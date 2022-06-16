.data
    a: .word 11
.globl __start


.text

__start:
    la t1, a
    lw a0, 0(t1)

################################################################################ 
  # Write your main function here. 
  # The input n is in a0. 
  # You should store the result T(n) into t0.
  # Round down the result of division.
  
  # HW1_1 
  # T(n) = 2T(3n/4) + 0.875n - 137, n >= 10
  # T(n) = 2T(n-1), 1 <= n < 10
  # T(0) = 7
  
  # EX. addi t0, a0, 1
################################################################################

  # no t0(x5), a0(x10)
    addi t1, x0, 1
    addi t2, x0, 2
    addi t3, x0, 3
    addi t4, x0, 7
    addi t5, x0, 10             # intergers
    #addi sp, x0, 2000
    add s1, a0, x0              # s1 = n (input)
    jal x1, recursive           # x1 save the jump link
    add t0, x0, s2
    beq x0, x0, result
    
recursive:
    addi sp, sp, -8             # make space in stack 
    sw x1, 0(sp)
    sw s1, 4(sp)
    bge s1, t5, ge10
    bge s1, t1, ge1
    addi s2, x0, 7
    lw x1, 0(sp)
    lw s1, 4(sp)
    addi sp, sp, 8
    jalr x0, 0(x1)

ge10:
    mul s1, s1, t3
    srli s1, s1, 2              # n = [3n/4]
    jal x1, recursive
    lw x1, 0(sp)
    lw s1, 4(sp)
    addi sp, sp, 8
    mul s2, s2, t2
    mul t6, s1, t4              # t6 = n * 7
    srli t6, t6, 3              # t6 = t6 / 8
    add s2, s2, t6              # s2 += 0.875n
    addi s2, s2, -137           # s2 -= 137
    
    jalr x0, 0(x1)
ge1:
    addi s1, s1, -1
    jal x1, recursive
    mul s2, s2, t2
    lw x1, 0(sp)
    addi sp, sp, 8
    jalr x0, 0(x1)

result:
    la t1, a
    sw t0, 4(t1)
  # Ends the program with status code 0
    addi a0,x0,10
    ecall    