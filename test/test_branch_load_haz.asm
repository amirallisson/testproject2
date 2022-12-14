.set noreorder    # example: add $t1, ... -> beq $t1, $t0 -> stall and then forward from ex/mem to if/id
addi $t1, $t1, 12     # t1 = c
addi $t0, $t0, next + 4
lw $t0, 0($t0)
beq $t0, $t1, 12     # true
addi $t2, $t2, 16   # delay: #t2 = 10
addi $t9, $t9, 16   # ..
addi $t4, $t4, 16   # ..
addi $t5, $t5, 16   # t5 = 16
next:
.word 0xfeedfeed
.word 0xc