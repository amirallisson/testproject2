#pragma once
#include "CacheConfig.h"
#include "MemoryStore.h"
#include <math.h>
#include <vector>


using byte_t = uint8_t;

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
		if (cache[index][ret].dirty) {
			for (uint32_t i = 0; i < cfg.blockSize; ++i) {
				mem->setMemValue(addr - offset + i, cache[index][ret].data[i], BYTE_SIZE);
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
                res = cache[index][whereToPut].data[i];
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
        offset = getOffset(offset);
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
