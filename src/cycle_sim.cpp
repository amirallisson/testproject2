#include <iostream>
#include <iomanip>
#include <fstream>
#include <string.h>
#include <errno.h>
#include <stdint.h>
#include <algorithm>
#include <math.h>
#include <vector>
#include "RegisterInfo.h"
#include "EndianHelpers.h"
#include "CacheConfig.h"
#include "MemoryStore.h"
#include "DriverFunctions.h"
#include<set>

// Group Members: Amir Mokhammed-Ali, George Toumbas

#define END 0xfeedfeed
#define EXCEPTION_ADDR 0x8000

static MemoryStore* mem;

// Global State variable

// Cache Stuff variables
using byte_t = uint8_t;


// Datapath Variables
#define NOINC_PC 1
#define OVERFLOW 2
#define ILLEGAL_INST 3
#define NUM_REGS 32


// Enums
// Registers
enum REG_IDS
{
    REG_ZERO,
    REG_AT,
    REG_V0,
    REG_V1,
    REG_A0,
    REG_A1,
    REG_A2,
    REG_A3,
    REG_T0,
    REG_T1,
    REG_T2,
    REG_T3,
    REG_T4,
    REG_T5,
    REG_T6,
    REG_T7,
    REG_S0,
    REG_S1,
    REG_S2,
    REG_S3,
    REG_S4,
    REG_S5,
    REG_S6,
    REG_S7,
    REG_T8,
    REG_T9,
    REG_K0,
    REG_K1,
    REG_GP,
    REG_SP,

    REG_FP,
    REG_RA,
};

enum OP_IDS{
    //R-type opcodes...
    OP_ZERO = 0,
    //I-type opcodes...
    OP_ADDI = 0x8,
    OP_ADDIU = 0x9,
    OP_ANDI = 0xc,
    OP_BEQ = 0x4,
    OP_BNE = 0x5,
    OP_LBU = 0x24,
    OP_LHU = 0x25,
    OP_LL = 0x30,
    OP_LUI = 0xf,
    OP_LW = 0x23,
    OP_ORI = 0xd,
    OP_SLTI = 0xa,
    OP_SLTIU = 0xb,
    OP_SB = 0x28,
    OP_SH = 0x29,
    OP_SW = 0x2b,
    //J-type opcodes...
    OP_J = 0x2,
    OP_JAL = 0x3
};

enum FUN_IDS{
    FUN_ADD = 0x20,
    FUN_ADDU = 0x21,
    FUN_AND = 0x24,
    FUN_JR = 0x08,
    FUN_NOR = 0x27,
    FUN_OR = 0x25,
    FUN_SLT = 0x2a,
    FUN_SLTU = 0x2b,
    FUN_SLL = 0x00,
    FUN_SRL = 0x02,
    FUN_SUB = 0x22,
    FUN_SUBU = 0x23
};

enum HAZARD_TYPE{
    NONE, MEM_HAZ, WB_HAZ, WRITE_STORE_HAZ, BRANCH_EX_HAZ, BRANCH_MEM_HAZ, BRANCH_LOAD_MEM_HAZ, BRANCH_WB_HAZ
};

std::set<int> VALID_OP = {OP_ZERO, OP_ADDI,  OP_ADDIU, OP_ANDI,  OP_BEQ, OP_BNE, OP_LBU, OP_LHU, OP_LL, OP_LUI, 
                        OP_LW, OP_ORI, OP_SLTI, OP_SLTIU, OP_SB, OP_SH, OP_SW, OP_J, OP_JAL};
std::set<int> I_TYPE_NO_LS = {OP_ADDI,  OP_ADDIU, OP_ANDI,  OP_BEQ, OP_BNE, OP_ORI, OP_SLTI, OP_SLTIU, OP_LUI};
std::set<int> LOAD_OP = {OP_LL, OP_LW, OP_LHU, OP_LBU};
std::set<int> STORE_OP = {OP_SB, OP_SH, OP_SW};
std::set<int> JB_OP = {OP_BEQ, OP_BNE, OP_J, OP_JAL};

// -----------------------------------------------------------

// Utility Structs 
struct CONTROL 
{
    bool regDst;
    bool ALUOp1;
    bool ALUOp2;
    bool ALUSrc;
    bool branch;
    bool memRead;
    bool memWrite;
    bool regWrite;
    bool memToReg;
};
auto CONTROL_RTYPE = CONTROL{true, true, true, false, false, false, false, true, false};
auto CONTROL_LOAD = CONTROL{false, false, false, true, false, true, false, true, true};
auto CONTROL_STORE = CONTROL{false, false, false, true, false, false, true, false, false};
auto CONTROL_ITYPE = CONTROL{false, true, false, false, false, false, false, true, false};
auto CONTROL_NOP = CONTROL{false, false, false, false, false, false, false, false, false};


// Decoded instruction struct
struct DecodedInst{ 
    uint32_t instr;
    uint32_t op;
    uint32_t rs;
    uint32_t rt;
    uint32_t rd;
    uint32_t shamt;
    uint32_t funct;
    uint32_t imm;
    uint32_t signExtIm;
    uint32_t zeroExtImm;
    uint32_t addr;
};

uint32_t instructBits(uint32_t instruct, int start, int end)
{
    int run = start - end + 1;
    uint32_t mask = (1 << run) - 1;
    uint32_t clipped = instruct >> end;
    return clipped & mask;
}

uint32_t signExt(uint16_t smol)
{
    uint32_t x = smol;
    uint32_t extension = 0xffff0000;
    return (smol & 0x8000) ? x ^ extension : x;
}

// Function to decode instruction
void decodeInst(uint32_t inst, DecodedInst & decodedInst){
        decodedInst.instr = inst;
        decodedInst.op = instructBits(inst, 31, 26);
        decodedInst.rs = instructBits(inst, 25, 21);
        decodedInst.rt = instructBits(inst, 20, 16);
        decodedInst.rd = instructBits(inst, 15, 11);
        decodedInst.shamt = instructBits(inst, 10, 6);
        decodedInst.funct = instructBits(inst, 5, 0);
        decodedInst.imm = instructBits(inst, 15, 0);
        decodedInst.signExtIm = signExt(decodedInst.imm);
        decodedInst.zeroExtImm = decodedInst.imm;
        decodedInst.addr = instructBits(inst, 25, 0) << 2;
}
/*-----------------------------
 * -----Pipeline Stages--------
 ----------------------------*/
struct IF_ID_STAGE{
    uint32_t instr;
    uint32_t npc;
    bool block;
};

struct ID_EX_STAGE{
    DecodedInst decodedInst;
    uint32_t npc;
    uint32_t readData1;
    uint32_t readData2;
    CONTROL ctrl;
    bool block;
};    

struct EX_MEM_STAGE{
    DecodedInst decodedInst;
    uint32_t npc; 
    uint32_t aluResult;
    uint32_t setMemValue;
    CONTROL ctrl;
    bool block;
};

struct MEM_WB_STAGE{
    DecodedInst decodedInst;
    uint32_t aluResult;
    uint32_t npc;
    uint32_t data; 
    CONTROL ctrl;
};

// --------------------------------------------------------------------------------------------------------------


// Cache --------------------------------------------------

enum CACHE_RET {
    HIT, MISS
};

struct Block {
	uint32_t tag;
	uint32_t lastUsed;
	bool valid;
	bool dirty;
	std::vector<byte_t> data;	
};


class Cache {
private:
	CacheConfig cfg;	
	MemoryStore* mem;
	uint32_t n, entries, tag_bits, index_bits, offset_bits, use_counter, hits, miss;
	std::vector<std::vector<Block>> cache;

	uint32_t getTag(uint32_t addr) {
		return addr >> (32 - tag_bits);
	}

	uint32_t getIndex(uint32_t addr) {
		return (addr << (tag_bits)) >> (32 - index_bits);
	}

	uint32_t getOffset(uint32_t addr) {
		return (addr << (32 - offset_bits)) >> (32 - offset_bits);
	}

    uint32_t evict(uint32_t addr) {
		uint32_t index, offset;
        index = getIndex(addr);
        offset = getOffset(addr);
		uint32_t ret = 0, last = UINT32_MAX;

        // find a free spot or evict LRU cacheline
		for (uint32_t i = 0; i < n; ++i) {
            // if invalid, break
			if (!cache[index][i].valid) {	
				ret = i;
				break;
			} 
            // update lru
			if (cache[index][i].lastUsed < last) {
				ret = i;
				last = cache[index][i].lastUsed;
			}
		}

		// write-back for the evicted block	
        cache[index][ret].valid = false;
        uint32_t evict_addr = (cache[index][ret].tag << (index_bits + offset_bits)) + (index << offset_bits);
		if (cache[index][ret].dirty) {
			for (uint32_t i = 0; i < cfg.blockSize; ++i) {
				mem->setMemValue(evict_addr + i, cache[index][ret].data[i], BYTE_SIZE);
			}
		}

		return ret;
	}

public:
	Cache(const CacheConfig& cfg, MemoryStore* mem): cfg(cfg),  mem(mem) {
		n = (cfg.type == DIRECT_MAPPED) ? 1 : 2;
		entries = cfg.cacheSize / (cfg.blockSize * n);
		cache.resize(entries);
		offset_bits = log2(cfg.blockSize);
		index_bits = log2(entries);
		tag_bits = 32 - offset_bits - index_bits;
		use_counter = hits = miss = 0;
		for (uint32_t i = 0; i < entries; ++i) {
			for (uint32_t j = 0; j < n; ++j) {
				cache[i].push_back(Block{0, 0, false, false, std::vector<byte_t>(cfg.blockSize)});
			}
		}
	}

	int getCacheValue(uint32_t addr, uint32_t& value, MemEntrySize size) {
        uint32_t tag, index, offset;
        tag = getTag(addr);
        index = getIndex(addr);
        offset = getOffset(addr);

        // go to cache[index] and find correspoding tag
        value = 0;
        uint32_t whereToPut;
        bool hit = false;
        for (int i = 0; i < n; ++i) {
            // if hit: 1) update lru counter 2) record the value 3) return HIT
            if (cache[index][i].tag == tag && cache[index][i].valid) {
                cache[index][i].lastUsed = ++use_counter;      
                hit = true;
                ++hits;
                whereToPut = i;
            }
        }
        // if miss: 1) find free spot or evict 2) bring data from memory 3) update block values 4) return MISS
        if (!hit) {
            whereToPut = evict(addr);
            cache[index][whereToPut].tag = tag;
            cache[index][whereToPut].lastUsed = ++use_counter;
            cache[index][whereToPut].valid = true;
            cache[index][whereToPut].dirty = false;
            for (uint32_t i = 0; i < cfg.blockSize; ++i) {
                uint32_t res;
                mem->getMemValue(addr - offset + i, res, BYTE_SIZE);
                cache[index][whereToPut].data[i] = res;
            }
            ++miss;
        }

        // read and return
        for (int j = 0; j < size; ++j) {
                value <<= 8;
                value += cache[index][whereToPut].data[offset + j]; // [0]...[offset+0][offset+1][offset+2][offset+3]...[block_size - 1]
        }
        return (hit) ? CACHE_RET::HIT : CACHE_RET::MISS;
    }

	int setCacheValue(uint32_t addr, uint32_t value, MemEntrySize size) {
        uint32_t tag, index, offset;
        tag = getTag(addr);
        index = getIndex(addr);
        offset = getOffset(addr);
        bool hit = false;
        uint32_t whereToPut;
        for (int i = 0; i < n; ++i) {
            // if hit: 1) update use_counter 2) set value 3) set dirty 4) return HIT
            if (cache[index][i].tag == tag && cache[index][i].valid) {
                hit = true;
                cache[index][i].lastUsed = ++use_counter;      
                cache[index][i].dirty = true;
                ++hits;
                whereToPut = i;
            }
        }

        // if miss: 1) find free spot or evict 2) bring from memory 3) update block values 4) set 5) return MISS

        if (!hit) {
            whereToPut = evict(addr);
            cache[index][whereToPut].tag = tag;
            cache[index][whereToPut].lastUsed = ++use_counter;
            cache[index][whereToPut].valid = true;
            cache[index][whereToPut].dirty = true;
            for (uint32_t i = 0; i < cfg.blockSize; ++i) {
                uint32_t res;
                mem->getMemValue(addr - offset + i, res, BYTE_SIZE);
                cache[index][whereToPut].data[i] = res;
            }
            ++miss;
        }

        // set and return
        for (int j = 0; j < size; ++j) {
            byte_t byte_val = ((value << (32 - 8 * size + 8 * j)) >> 24); // V = V_1V_2V_3V_4          
            cache[index][whereToPut].data[offset + j] = byte_val;         // [0]...[offset+0] = V1 [offset+1] = V2 [offset+2] = V3 [offset+3] = V4...[block_size - 1]

        }
    
        return (hit) ? CACHE_RET::HIT : CACHE_RET::MISS;
    }

    void drain() {
        for (int i = 0; i < entries; ++i) {
            for (int j = 0; j < n; ++j) {
                if(!cache[i][j].valid || !cache[i][j].dirty) {
                    continue;
                }
                uint32_t addr = (cache[i][j].tag << (index_bits + offset_bits)) + (i << offset_bits);
                for (int k = 0; k < cfg.blockSize; ++k) {
                    mem->setMemValue(addr + k, cache[i][j].data[k], BYTE_SIZE);
                }
            }
        }
    }

	uint32_t Hits() {
		return hits;
	}
	uint32_t Misses() {
		return miss;
	}
    uint32_t Penalty() {
        return cfg.missLatency;
    }
};

// ---------------------------------------------------


// Datapath Structs ----------------------------------------------------

struct FORWARD_UNIT; // do not delete or compilation error
struct BRANCH_FORWARD_UNIT;
struct HAZARD_UNIT;  // do not delete or compilation error
struct EXECUTOR;  // do not delete or compilation error

struct STATE
{
    uint32_t pc, branch_pc;
    uint32_t cycles;
    uint32_t regs[NUM_REGS];
    int if_wait_cycles, mem_wait_cycles;
    IF_ID_STAGE if_id_stage;
    ID_EX_STAGE id_ex_stage;
    EX_MEM_STAGE ex_mem_stage;
    MEM_WB_STAGE mem_wb_stage;
    PipeState pipe_state;
    SimulationStats sim_stats;
    FORWARD_UNIT* fwd;
    BRANCH_FORWARD_UNIT* branch_fwd;  
    HAZARD_UNIT*  hzd;
    EXECUTOR* exec;
    Cache *i_cache, *d_cache;
    bool stall;
    bool exception;
    bool end_at_id;
    bool end_program;
};


struct FORWARD_UNIT 
{
    HAZARD_TYPE fwd1 = HAZARD_TYPE::NONE;
    HAZARD_TYPE fwd2 = HAZARD_TYPE::NONE;
    HAZARD_TYPE fwdWriteStore = HAZARD_TYPE::NONE;
    uint32_t mem_value, wb_value;

    void checkFwd(STATE& state) 
    {
        fwd1 = fwd2 = fwdWriteStore = HAZARD_TYPE::NONE;
        checkMEM(state);
        checkWB(state);
        checkWriteStore(state);
    }
private:

    void checkMEM(STATE& state) // example: add $t1, ... -> add $t2, $t1, $t0 -> forward from ex_mem to id_ex 
    {
        uint32_t where = (state.ex_mem_stage.ctrl.regDst) ? state.ex_mem_stage.decodedInst.rd : state.ex_mem_stage.decodedInst.rt;
        if (!state.ex_mem_stage.ctrl.regWrite || where == 0) {
            return;
        }
        fwd1 = (where == state.id_ex_stage.decodedInst.rs) ? (HAZARD_TYPE::MEM_HAZ) : (HAZARD_TYPE::NONE);
        fwd2 = (where == state.id_ex_stage.decodedInst.rt) ? (HAZARD_TYPE::MEM_HAZ) : (HAZARD_TYPE::NONE);
    }
    
    void checkWB(STATE& state) // example: add $t1, ... -> nop -> add $t2, $t1, $t0 -> forward from mem_wb to id_ex 
    {
        uint32_t where = (state.mem_wb_stage.ctrl.regDst) ? state.mem_wb_stage.decodedInst.rd : state.mem_wb_stage.decodedInst.rt;
        if (!state.mem_wb_stage.ctrl.regWrite || where == 0) {
            return;
        }
        // check that there is no such op between this and in id_ex
        fwd1 = ((where == state.id_ex_stage.decodedInst.rs) && (fwd1 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::WB_HAZ : fwd1;
        fwd2 = ((where == state.id_ex_stage.decodedInst.rt) && (fwd2 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::WB_HAZ : fwd2;
    }


    void checkWriteStore(STATE& state) { // example: lw $t0, addr -> sw $t0, addr -> forward from mem/wb to ex/mem 
        uint32_t where = (state.mem_wb_stage.ctrl.regDst) ? state.mem_wb_stage.decodedInst.rd : state.mem_wb_stage.decodedInst.rt;
        if (!state.ex_mem_stage.ctrl.memWrite || !state.mem_wb_stage.ctrl.regWrite || where == 0) {
            fwdWriteStore = HAZARD_TYPE::NONE;
            return;
        }
        fwdWriteStore = (where == state.ex_mem_stage.decodedInst.rt) ? HAZARD_TYPE::WRITE_STORE_HAZ : HAZARD_TYPE::NONE;
    }

};


struct BRANCH_FORWARD_UNIT {
    HAZARD_TYPE fwd1 = HAZARD_TYPE::NONE;
    HAZARD_TYPE fwd2 = HAZARD_TYPE::NONE;
    uint32_t mem_value, wb_value;

    void checkFwd(STATE& state) 
    {
        DecodedInst di;
        decodeInst(state.if_id_stage.instr, di);
        fwd1 = fwd2 = HAZARD_TYPE::NONE;
        if (di.op != OP_BEQ && di.op != OP_BNE){
            return;
        }
        checkEX(state, di);
        checkMEM(state, di);
        checkLOADMEM(state, di);
        checkWB(state, di);
    }

private:
    void checkEX(STATE& state, DecodedInst& decodedInst) // example: add $t1, ... -> beq $t1, $t0 -> stall and then forward from ex/mem to if/id
    {
        uint32_t where = (state.id_ex_stage.ctrl.regDst) ? state.id_ex_stage.decodedInst.rd : state.id_ex_stage.decodedInst.rt;
        if (!state.id_ex_stage.ctrl.regWrite || where == 0) {
            return;
        }
        fwd1 = (where == decodedInst.rs) ? HAZARD_TYPE::BRANCH_EX_HAZ : HAZARD_TYPE::NONE;
        fwd2 = (where == decodedInst.rt) ? HAZARD_TYPE::BRANCH_EX_HAZ : HAZARD_TYPE::NONE;  
    }

    void checkLOADMEM(STATE& state, DecodedInst& decodedInst) // example: load $t1, addr -> nop ->  beq $t1, $t0 -> stalls and then forward from ex/mem to if/id
    {   
        uint32_t where = (state.ex_mem_stage.ctrl.regDst) ? state.ex_mem_stage.decodedInst.rd : state.ex_mem_stage.decodedInst.rt;
        if (!state.ex_mem_stage.ctrl.memRead || !state.ex_mem_stage.ctrl.regWrite || where == 0) {
            return;
        }
        // check that there is no such op between this and branch
        fwd1 = ((where == decodedInst.rs) && (fwd1 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_LOAD_MEM_HAZ : fwd1;
        fwd2 = ((where == decodedInst.rt) && (fwd2 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_LOAD_MEM_HAZ : fwd2;   
    }

    void checkMEM(STATE &state, DecodedInst& decodedInst) { // example: add $t1, ... -> nop -> beq $t1, $t0 -> forward form ex/mem to if/id
        uint32_t where = (state.ex_mem_stage.ctrl.regDst) ? state.ex_mem_stage.decodedInst.rd : state.ex_mem_stage.decodedInst.rt;
        if (state.ex_mem_stage.ctrl.memRead || !state.ex_mem_stage.ctrl.regWrite || where == 0) {
            return;
        }
        // check that there is no such op between this and branch
        fwd1 = ((where == decodedInst.rs) && (fwd1 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_MEM_HAZ : fwd1;
        fwd2 = ((where == decodedInst.rt) && (fwd2 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_MEM_HAZ : fwd2;   
      
    }
    void checkWB(STATE &state, DecodedInst& decodedInst) { // example: add $t1, ... -> nop -> beq $t1, $t0 -> forward form ex/mem to if/id
        uint32_t where = (state.mem_wb_stage.ctrl.regDst) ? state.mem_wb_stage.decodedInst.rd : state.mem_wb_stage.decodedInst.rt;
        if (!state.ex_mem_stage.ctrl.regWrite || where == 0) {
            return;
        }
        // check that there is no such op between this and branch
        fwd1 = ((where == decodedInst.rs) && (fwd1 == HAZARD_TYPE::NONE) && (fwd1 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_WB_HAZ : fwd1;
        fwd2 = ((where == decodedInst.rt) && (fwd2 == HAZARD_TYPE::NONE) && (fwd2 == HAZARD_TYPE::NONE)) ? HAZARD_TYPE::BRANCH_WB_HAZ : fwd2;   
      
    }
};


struct HAZARD_UNIT 
{
    bool jump;

    void checkHazard(STATE& state, DecodedInst& decodedInst) {
        state.stall = false;
        if (state.id_ex_stage.ctrl.memRead) {    // check load_use if op = MemRead
            checkLoadUse(state);
        } else {                // check jump or branch: op = J, JAL, BEQ, BNE
            checkBranch(state, decodedInst);
        }
    }


private:
    void checkLoadUse(STATE& state) 
    {
        uint32_t if_id_reg1 = instructBits(state.if_id_stage.instr, 25, 21);
        uint32_t if_id_reg2 = instructBits(state.if_id_stage.instr, 20, 16);
        if (state.id_ex_stage.ctrl.memRead && ((state.id_ex_stage.decodedInst.rt == if_id_reg1) ||
            (state.id_ex_stage.decodedInst.rt == if_id_reg2))) {
                state.stall = true;
        } else {
            state.stall = false;
        }
    }

    // done during the id stage
    void checkBranch(STATE& state, DecodedInst& decodedInst) 
    {
        uint32_t readReg1 = state.regs[decodedInst.rs];
        uint32_t readReg2 = state.regs[decodedInst.rt];
        uint32_t old_pc = state.if_id_stage.npc;
        uint32_t op = decodedInst.op;

        if (!JB_OP.count(op)) {
            return;
        }

        // do forwarding if op = BEQ or BNE
        if (op == OP_BNE || op == OP_BEQ) {
            switch (state.branch_fwd -> fwd1) {
                case BRANCH_EX_HAZ:         // cant be load, because loaduse would handle this. 1 stall and fwd
                    state.stall = true;
                    return;
                case BRANCH_MEM_HAZ:        // no stalls, fwd
                    readReg1 = state.branch_fwd -> mem_value;
                    break;
                case BRANCH_LOAD_MEM_HAZ:   // 1 stall and fwd
                    state.stall = true;
                    return;
                case BRANCH_WB_HAZ:         // no stall, fwd 
                    readReg1 = state.branch_fwd -> wb_value;
                    break;
                default:
                    readReg1 = state.regs[decodedInst.rs];
            }
            // do forwarding
            switch (state.branch_fwd -> fwd2) {
                case BRANCH_EX_HAZ:
                    state.stall = true;
                    return;
                case BRANCH_MEM_HAZ:
                    readReg2 = state.branch_fwd -> mem_value;
                    break;
                case BRANCH_LOAD_MEM_HAZ:
                    state.stall = true;
                    return;
                case BRANCH_WB_HAZ:
                    readReg2 = state.branch_fwd -> wb_value;
                    break;
                default:
                    readReg2 = state.regs[decodedInst.rt];
            }
        }

        switch (op) {
            case OP_BEQ:
                jump = (readReg1 == readReg2);
                state.branch_pc = old_pc + (decodedInst.signExtIm << 2);
                return;
            case OP_BNE:
                jump = (readReg1 != readReg2);
                state.branch_pc = old_pc + (decodedInst.signExtIm << 2);
                return;
            case OP_JAL:
                // state.regs[REG_RA] = old_pc + 4; // not +8 because PC is incremented in the IF()
                // fall through
            case OP_J:
                jump = true;
                state.branch_pc = (old_pc & 0xf0000000) | (decodedInst.addr); 
                return;
        }
    }
};

struct EXECUTOR 
{
    uint8_t getSign(uint32_t value)
    {
        return (value >> 31) & 0x1;
    }

    int doAddSub(uint32_t& aluResult, uint32_t s1, uint32_t s2, bool isAdd, bool checkOverflow)
    {
        bool overflow = false;
        uint32_t result = 0;

        // Not sure why she was casting this before
        if (isAdd){result = s1 + s2;}
        else{result = s1 - s2;}

        if (checkOverflow)
        {
                if (isAdd)
                {
                    overflow = getSign(s1) == getSign(s2) && getSign(s2) != getSign(result);
                }
                else
                {
                    overflow = getSign(s1) != getSign(s2) && getSign(s2) == getSign(result);
                }
        }

        if (overflow)
        {
                // Inform the caller that overflow occurred so it can take appropriate action.
                return OVERFLOW;
        }

        // Otherwise update state and return success.
        aluResult = result;

        return 0;
    }

    void executeR(STATE& state){

        // Do I need to do anything with control signals here?
        
        uint32_t funct = state.id_ex_stage.decodedInst.funct;
        uint32_t rd = state.id_ex_stage.decodedInst.rd; // register number
        uint32_t rs = state.id_ex_stage.decodedInst.rs; // register number
        uint32_t rt = state.id_ex_stage.decodedInst.rt; // register number

        uint32_t rs_value = state.id_ex_stage.readData1;    // Amir
        uint32_t rt_value = state.id_ex_stage.readData2;    // Amir

        uint32_t shamt = state.id_ex_stage.decodedInst.shamt;
        // Perform ALU operation and store in EX/MEM aluResult
        uint32_t aluResult;
        int ret = 0;
        switch (funct){
            case FUN_ADD:
                ret = doAddSub(aluResult, rs_value, rt_value, true, true);
                break;
            case FUN_ADDU:
                ret = doAddSub(aluResult, rs_value, rt_value, true, false);
                break;
            case FUN_AND:
                aluResult = rs_value & rt_value;
                break;
            case FUN_JR:
                //FIXME Should we be updating the PC here?
                state.ex_mem_stage.npc = rs_value;
                break;
            case FUN_NOR:
                aluResult = ~(rs_value | rt_value);
                break;
            case FUN_OR:
                aluResult = rs_value | rt_value;
                break;
            case FUN_SLT:
                if ((rs_value >> 31) != (rt_value >> 31)) { // Different signs
                    aluResult = (rs_value >> 31) ? 1 : 0; 
                } else {
                    aluResult = (rs_value < rt_value) ? 1 : 0;
                }
                break;
            case FUN_SLTU:
                aluResult = (rs_value < rt_value) ? 1 : 0;
                break;
            case FUN_SLL:
                aluResult = rt_value << shamt;
                break;
            case FUN_SRL:
                aluResult = rt_value >> shamt;
                break;
            case FUN_SUB:
                ret = doAddSub(aluResult, rs_value, rt_value, false, true);
                break;
            case FUN_SUBU:
                ret = doAddSub(aluResult, rs_value, rt_value, false, false);
                break;
                // TODO jump to exception address=
        }
        if (ret == OVERFLOW) {
            state.exception = true;
            return;
        }
        if (!state.ex_mem_stage.block){
            state.ex_mem_stage.aluResult = aluResult;
        }
    }

    void executeI(STATE& state) {
        uint32_t op = state.id_ex_stage.decodedInst.op;
        uint32_t rt = state.id_ex_stage.decodedInst.rt; // register number
        uint32_t rs = state.id_ex_stage.decodedInst.rs; // register number

        uint32_t rs_value = state.id_ex_stage.readData1;    // Amir
        uint32_t rt_value = state.id_ex_stage.readData2;    // Amir

        uint32_t imm = state.id_ex_stage.decodedInst.imm;
        uint32_t seImm = state.id_ex_stage.decodedInst.signExtIm;
        uint32_t zeImm = imm;
        uint32_t aluResult;
        uint32_t addr = rs_value + seImm;

        int ret = 0;
        uint32_t oldPC = state.id_ex_stage.npc;

        switch(op){
            case OP_ADDI:
                ret = doAddSub(aluResult, rs_value, seImm, true, true);
                break;
            case OP_ADDIU:
                ret = doAddSub(aluResult, rs_value, seImm, true, false);
                break;
            case OP_ANDI:
                aluResult = rs_value & zeImm;
                break;
            case OP_BEQ:
                /*if (rs == rt){
                    state.ex_mem_stage.npc = 4 + (seImm << 2);
                }*/
                break;
            case OP_BNE:
                /*if (rs != rt){
                    state.ex_mem_stage.npc = 4 + (seImm << 2);
                }*/
                break;
            case OP_LBU:
                aluResult = addr;
                break;
            case OP_LHU:
                // Double check
                aluResult = addr;
                break;
            case OP_LUI:
                aluResult = (imm << 16);
                break;
            case OP_LW:
                aluResult = addr;
                break;
            case OP_ORI:
                aluResult = rs_value | zeImm;
                break;
            case OP_SLTI:
                if ((rs_value >> 31) != (seImm >> 31)) { // Different signs
                    aluResult = (rs_value >> 31) ? 1 : 0; 
                } else {
                    aluResult = (rs_value < seImm) ? 1 : 0;
                }
                break;
            case OP_SLTIU:
                aluResult = (rs_value < seImm) ? 1 : 0;
                break;
            case OP_SB:
                aluResult = addr;
                break;
            case OP_SW:
                aluResult = addr;
                break;
            case OP_SH:
                aluResult = addr;
                break;
        }

        if (ret == OVERFLOW) {
            state.exception = true;
            return;
        }
        if (!state.ex_mem_stage.block){
            state.ex_mem_stage.aluResult = aluResult;
        }
    }

};


// ----------------------------------------------------------------------------------


STATE state;

extern void dumpRegisterStateInternal(RegisterInfo & reg, std::ostream & reg_out);

// Print State
void printState(std::ostream & out, bool printReg)
{
    out << "\nState at beginning of cycle " << state.sim_stats.totalCycles << ":" << std::endl;
    out << "PC: " << std::hex << state.pc << std::endl;
    out << "IF/ID: " << std::hex << state.if_id_stage.instr << std::endl;
    out << "ID/EX: " << std::hex << state.id_ex_stage.decodedInst.instr << std::endl;
    out << "EX/MEM: " << std::hex << state.ex_mem_stage.decodedInst.instr << std::endl;
    out << "MEM/WB: " << std::hex << state.mem_wb_stage.decodedInst.instr << std::endl;
   // out << "WB: " << std::hex << state.wb_stage.decodedInst.instr << std::endl;

    if(printReg){
        out << "Registers:" << std::endl;
        for(int i = 0; i < NUM_REGS; i++){
            out << "$" << std::dec << i << ": " << std::hex << state.regs[i] << std::endl;
        }
    }
}


// *------------------------------------------------------------*
// Control 
// *------------------------------------------------------------*


void updateControl(DecodedInst & decIns, CONTROL& ctrl){
    // End of program check
    if (decIns.instr == 0xfeedfeed) {
        ctrl = CONTROL_NOP;
        return;
    }

    if (VALID_OP.count(decIns.op) == 0) { // ILLEGAL_INST
        state.exception = true;
        return;
    }

    if (decIns.op == OP_ZERO) {
        ctrl = CONTROL_RTYPE;
        return;
    }
    if (LOAD_OP.count(decIns.op) > 0) {
        ctrl = CONTROL_LOAD;
        return;
    }
    if (STORE_OP.count(decIns.op) > 0) {
        ctrl = CONTROL_STORE;
        return;
    }
    if (I_TYPE_NO_LS.count(decIns.op) > 0) {
        ctrl = CONTROL_ITYPE;
        return;
    }
    ctrl = CONTROL_NOP;
}

// Mem helper
int doLoad(STATE& state, uint32_t addr, MemEntrySize size, uint32_t& data)
{
    uint32_t value = 0;
    int ret = 0;
    ret = state.d_cache->getCacheValue(addr, value, size);

    switch (size)
    {
    case BYTE_SIZE:
            data = value & 0xFF;
            break;
    case HALF_SIZE:
            data = value & 0xFFFF;
            break;
    case WORD_SIZE:
            data = value;
            break;
    default:
            std::cerr << "Invalid size passed, cannot read/write memory" << std::endl;
            return -EINVAL;
    }

    return ret;
}

// *------------------------------------------------------------*
// Function for each stage
// *------------------------------------------------------------*
void IF(){
    uint32_t instr = 0;
    state.pipe_state.ifInstr = instr;

    if (state.stall){
        return;
    }
    
    // decrement wait_cycles and return if still have to wait
    if ((state.if_wait_cycles = std::max(state.if_wait_cycles - 1, 0)) > 0) {   // still blocked
        return;
    }
    
    // fetch instruction if 0xfeedfeed has not been reached 
    if (!state.end_at_id){
        auto hit = state.i_cache->getCacheValue(state.pc, instr, WORD_SIZE);
        if (hit != CACHE_RET::HIT && (state.i_cache -> Penalty() > 0)) {  // miss -> set penalty cycles
            state.if_wait_cycles = state.i_cache -> Penalty();
            return;
        }
    }
    // update pipe state
    state.pipe_state.ifInstr = instr;
  
    if (!state.if_id_stage.block) {         // if next stage not blocked, then move forward
        state.if_id_stage.instr = instr;
        state.if_id_stage.npc = state.pc + 4;
        state.pc = (state.hzd -> jump || state.exception) ? state.branch_pc : state.pc + 4;
    }
    
}


void ID(){
    uint32_t instr = state.if_id_stage.instr;

    // Update pipestate
    state.pipe_state.idInstr = instr;

    if (instr == 0xfeedfeed) {
        state.end_at_id = true;
    }
    DecodedInst decodedInst;
    CONTROL ctrl;

    decodeInst(instr, decodedInst);
    updateControl(decodedInst, ctrl);

    if (state.exception) {
        state.branch_pc = EXCEPTION_ADDR;
        return;
    }
    if (!state.end_at_id) {
        state.hzd -> jump = false;  // erase previously written value 
        state.hzd -> checkHazard(state, decodedInst);
    }


    if (!state.id_ex_stage.block){

        if (state.stall || (JB_OP.count(decodedInst.op) > 0 && decodedInst.op != OP_JAL)){
            state.id_ex_stage = ID_EX_STAGE{};
            return;
        }

        state.id_ex_stage.decodedInst = decodedInst;
        state.id_ex_stage.npc = state.if_id_stage.npc;
        state.id_ex_stage.readData1 = state.regs[decodedInst.rs];
        state.id_ex_stage.readData2 = state.regs[decodedInst.rt];
        state.id_ex_stage.ctrl = ctrl;
        state.if_id_stage = IF_ID_STAGE{};
    }
}

void EX()
{
    uint32_t readData1, readData2; 

    // Update pipestate
    state.pipe_state.exInstr = state.id_ex_stage.decodedInst.instr;

    // set readReg1
    switch (state.fwd -> fwd1) {
        case HAZARD_TYPE::MEM_HAZ:  // example: add $t1, ... (in MEM now)-> add $t0, $t1, $t1 (in EX now): 
            state.id_ex_stage.readData1 = state.fwd->mem_value;
            break;
        
        case HAZARD_TYPE::WB_HAZ: // example: add $t1, ... (in WB now)-> nop -> add $t0, $t1, $t1 (in EX now): 
            state.id_ex_stage.readData1 = state.fwd->wb_value;
            break;

        case HAZARD_TYPE::NONE:
            break;
    }
    // set readReg2
    switch (state.fwd -> fwd2) {
        case HAZARD_TYPE::MEM_HAZ:
            state.id_ex_stage.readData2 =  state.fwd->mem_value;
            break;
        
        case HAZARD_TYPE::WB_HAZ:
            state.id_ex_stage.readData2 = state.fwd->wb_value;
            break;

        case HAZARD_TYPE::NONE:
            break;
    }

    uint32_t op = state.id_ex_stage.decodedInst.op;

    // DO ALU Operations
    if (state.id_ex_stage.decodedInst.instr != 0xfeedfeed) {
        if (op == OP_ZERO) {
            state.exec -> executeR(state);
        } else if (I_TYPE_NO_LS.count(op) != 0 || LOAD_OP.count(op) != 0  || STORE_OP.count(op) != 0) {
            state.exec -> executeI(state);
        } // branch and jump finished by this time
    }

    if (state.exception) {                  // flush everything
        state.branch_pc = EXCEPTION_ADDR; 
        state.ex_mem_stage = EX_MEM_STAGE{};
        state.id_ex_stage = ID_EX_STAGE{};
        state.if_id_stage = IF_ID_STAGE{};
        return;
    } 
    if (!state.ex_mem_stage.block){
        state.ex_mem_stage.decodedInst = state.id_ex_stage.decodedInst;
        state.ex_mem_stage.npc = state.id_ex_stage.npc;
        state.ex_mem_stage.ctrl = state.id_ex_stage.ctrl;
        state.ex_mem_stage.setMemValue = state.id_ex_stage.readData2;
        state.id_ex_stage = ID_EX_STAGE{};
    }
}


void MEM(){ 

    // forward values
    state.fwd->mem_value = state.ex_mem_stage.aluResult;
    state.branch_fwd->mem_value = state.ex_mem_stage.aluResult;
    // Update pipestate
    state.pipe_state.memInstr = state.ex_mem_stage.decodedInst.instr;

    // decrement wait_cycles and check if have to wait more
    if ((state.mem_wait_cycles = std::max(state.mem_wait_cycles - 1, 0)) > 0){ // still blocked
        return;
    }

    state.if_id_stage.block = false;
    state.id_ex_stage.block = false;
    state.ex_mem_stage.block = false;
    

    uint32_t op = state.ex_mem_stage.decodedInst.op;
    uint32_t rt = state.ex_mem_stage.decodedInst.rt;
    uint32_t addr = state.ex_mem_stage.aluResult;
    uint32_t imm = state.ex_mem_stage.decodedInst.imm;
    uint32_t setValue;
    uint32_t data;
    int ret = CACHE_RET::HIT;



    // sw $t0, addr: t0 may be forwarded by the instruction in WB
    switch (state.fwd -> fwdWriteStore) {
        case HAZARD_TYPE::WRITE_STORE_HAZ:
            setValue = state.fwd -> wb_value;
            break;
        case HAZARD_TYPE::NONE:
            setValue = state.ex_mem_stage.setMemValue;
    }
    
    if (state.ex_mem_stage.decodedInst.instr != 0xfeedfeed) {
        switch(op){
            // Storing
            case OP_SW:
                ret = state.d_cache->setCacheValue(addr, setValue, WORD_SIZE); 
                break;
            case OP_SH:
                ret = state.d_cache->setCacheValue(addr, instructBits(setValue, 31, 16), HALF_SIZE); 
                break;
            case OP_SB:
                ret = state.d_cache->setCacheValue(addr, instructBits(setValue, 31, 24), BYTE_SIZE);
                break;
            // Loading
            case OP_LW:
                ret = doLoad(state, addr, WORD_SIZE, data);
                break;
            case OP_LHU:
                ret = doLoad(state, addr, HALF_SIZE, data);
                break;
            case OP_LBU:
                ret = doLoad(state, addr, BYTE_SIZE, data);
                break;
            // Default
            default:
                data = state.ex_mem_stage.aluResult;
        }
    }

    if (ret != CACHE_RET::HIT && (state.d_cache -> Penalty() > 0)) {    // if miss -> block all storages before this one
        state.mem_wait_cycles = state.d_cache->Penalty();
        state.ex_mem_stage.block = true;
        state.id_ex_stage.block = true;
        state.if_id_stage.block = true;
        return;
    }
    
    state.mem_wb_stage.decodedInst = state.ex_mem_stage.decodedInst;
    state.mem_wb_stage.aluResult = state.ex_mem_stage.aluResult;
    state.mem_wb_stage.data = data;
    state.mem_wb_stage.ctrl = state.ex_mem_stage.ctrl;
    state.mem_wb_stage.npc = state.ex_mem_stage.npc;

    state.ex_mem_stage = EX_MEM_STAGE{};
}


void WB(){
    // Update pipestate
    state.pipe_state.wbInstr = state.mem_wb_stage.decodedInst.instr;

    // Check for 0xfeefeed
    if (state.mem_wb_stage.decodedInst.instr == 0xfeedfeed) {
        state.pipe_state.wbInstr = 0;
        state.end_program = true;
        return;
    }

    uint32_t writeData = (state.mem_wb_stage.ctrl.memToReg) ? state.mem_wb_stage.data : state.mem_wb_stage.aluResult;
    uint32_t where = (state.mem_wb_stage.ctrl.regDst) ? state.mem_wb_stage.decodedInst.rd : state.mem_wb_stage.decodedInst.rt;
    uint32_t op = state.mem_wb_stage.decodedInst.op;
    if (state.mem_wb_stage.ctrl.regWrite) {
        state.regs[where] = writeData;
        // forward values 
        state.fwd->wb_value = writeData;        
        state.branch_fwd->wb_value = writeData; 
    }

    // JAL write reg
    if (op == OP_JAL){
        state.regs[REG_RA] = state.mem_wb_stage.npc + 4;
    }

}



int initSimulator(CacheConfig &icConfig, CacheConfig &dcConfig, MemoryStore *mainMem){
    // Init simulator 
    state = {};
    state.exec = new EXECUTOR{};
    state.hzd = new HAZARD_UNIT{};
    state.fwd = new FORWARD_UNIT{};
    state.branch_fwd = new BRANCH_FORWARD_UNIT{};
    mem = mainMem;

    // Init Cache
    state.i_cache = new Cache(icConfig, mainMem);
    state.d_cache = new Cache(dcConfig, mainMem);

    // Set regs to zero 
    for(int i = 0; i < 32; i++){ state.regs[i] = 0;}

    return 1;
}

int runCycles(uint32_t cycles){
    uint32_t startingCycle = state.sim_stats.totalCycles;
    bool finEarly = false;
    while (state.sim_stats.totalCycles < (cycles + startingCycle)){
        state.fwd->checkFwd(state);
        state.branch_fwd->checkFwd(state);

        WB();
        MEM();
        EX();
        ID();
        IF();
        state.sim_stats.totalCycles++;
        if(state.end_program){
            finEarly = true;
            break;
        }
    }
    // printState(std::cout, true);

    dumpMemoryState(mem);
    state.pipe_state.cycle = state.sim_stats.totalCycles - 1;
    dumpPipeState(state.pipe_state);

    if (finEarly) {
        return 1;
    }
    return 0;
}

int runTillHalt(){
    // uint32_t DrainIters = 5; {
    while(!state.end_program){
        // printState(std::cout, false);
        state.fwd->checkFwd(state);
        state.branch_fwd->checkFwd(state);
        WB();
        MEM();
        EX();
        ID();
        IF();
        state.sim_stats.totalCycles++;
    } 

    // printState(std::cout, true);

    dumpMemoryState(mem);
    state.pipe_state.cycle = state.sim_stats.totalCycles-1;
    dumpPipeState(state.pipe_state);

}

int finalizeSimulator(){
    // Write back dirty cache values, does not need to be cycle accurate
    state.d_cache->drain();
    state.sim_stats.icHits = state.i_cache->Hits();
    state.sim_stats.icMisses = state.i_cache->Misses();
    state.sim_stats.dcHits = state.d_cache->Hits();
    state.sim_stats.dcMisses = state.d_cache->Misses();


    //Dump RegisterInfo
    RegisterInfo regInfo = {};
    regInfo.at = state.regs[REG_AT];
    for (int i = 0; i < V_REG_SIZE; i++){
        regInfo.v[i] = state.regs[REG_V0 + i];
    }
    for (int i = 0; i < A_REG_SIZE; i++){
        regInfo.a[i] = state.regs[REG_A0 + i];
    }
    for (int i = 0; i < T_REG_SIZE-2; i++){
        regInfo.t[i] = state.regs[REG_T0 + i];
    }
    for (int i = 0; i < S_REG_SIZE; i++){
        regInfo.s[i] = state.regs[REG_S0 + i];
    }
    regInfo.t[8]= state.regs[REG_T8];
    regInfo.t[9] = state.regs[REG_T9];
    for (int i = 0; i < K_REG_SIZE; i++){
        regInfo.k[i] = state.regs[REG_K0 + i];
    }
    regInfo.gp = state.regs[REG_GP];
    regInfo.sp = state.regs[REG_SP];
    regInfo.fp = state.regs[REG_FP];
    regInfo.ra = state.regs[REG_RA];

    printSimStats(state.sim_stats);
    dumpRegisterState(regInfo);
    dumpMemoryState(mem);

    return 0;

}
