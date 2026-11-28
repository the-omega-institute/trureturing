# Integer Qutrit Polar-Overlap Witness

## Abstract

An integer qutrit witness refutes the universal half-time polar overlap lower bound.

The kernel-checked source uses the integer Hermitian matrices A = [[2,6,-1],[6,4,1],[-1,1,1]] and B = [[-9,-6,1],[-6,-3,-1],[1,-1,8]]. The Taylor recurrence stores X^n and n! times the truncated exponential sum. For Y = B - 9I, the exact integer floor certificate at degree 100 gives the displayed entry bounds for K = exp(A) exp(Y). The row-sum norm bounds are ||A|| <= 11 and ||Y|| <= 25, and the degree-101 tails are at most 10^-18. After the scalar shift, exp(-18) exp(A+B) exp(A) exp(B) is bounded in trace norm by 801763/1638400 < 1/2, while exp(-18) Tr exp(2(A+B)) = 1 + exp(-16) + exp(-32) > 1. Hence ||exp(A+B) exp(A) exp(B)||_1 < Tr exp(2(A+B)). The Lean declaration integer_certificate supplies the floor table, and rational_certificate supplies the rational bounds.

**Theorem 1.1 (Strict integer qutrit witness).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.polar_optimized_overlap_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.polar_optimized_overlap_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A = Aᴴ and B = Bᴴ, and the certified exponential estimates prove the strict reverse of the proposed polar-optimized half-time inequality.

The closed claim quantifies over every pair H and J of Hermitian 3 by 3 complex matrices and asserts Tr exp(H+J) <= ||exp((H+J)/2) exp(H/2) exp(J/2)||_1. The source instantiates it at H = 2A and J = 2B. The scalar half-time factors reduce definitionally to exp(A+B), exp(A), and exp(B), so the strict witness is a literal kernel proof of Not of that universal claim.

**Theorem 1.2 (The universal half-time polar claim is false).**

Lean statement: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed claim is universally quantified. Its negation follows from the two concrete Hermitian witness matrices and the strict inequality.

The faithful physical realization uses two classical flag blocks. For arbitrary Hermitian H and J, put M = exp(H), N = Tr exp(J), Q = exp(J)/N, P = I/3, D1 = epsilon M, and D2 = I - epsilon M for 0 < epsilon < 1/||M||. The joint reference has blocks D_i/3. The joint alternative has X1 = X2 = Q/2, and the channel is the partial trace over the flag. With Omega_i = exp(log D_i + log Q), K_i = sqrt(Omega_i) sqrt(D_i) sqrt(Q), Z = sum_i Tr Omega_i, root fidelity is (sum_i ||K_i||_1)/sqrt(Z), and the real overlap uses sum_i Re Tr K_i. The first flag is exactly Omega1 = (epsilon/N) exp(H+J) and K1 = (epsilon/N) exp((H+J)/2) exp(H/2) exp(J/2).

For the explicit weight epsilon = 2^(-100), let f_i = ||K_i||_1 - Tr Omega_i. The matrix certificate gives f_1 < -epsilon exp(18)/(2N). Schatten Hölder gives f_2 <= (Tr D2 Q - Tr Omega2)/2. Scalar spectral Jensen in an eigenbasis of Q gives Tr Omega2 >= 1 + Tr Q log D2. The scalar inequality log(1-x) >= -x-x² on [0,1/2] then gives f_2 <= epsilon² ||M||²/2. The row-sum bounds ||A|| <= 11 and ||B|| <= 16 imply ||M|| <= exp(22) and N <= 3 exp(32). Using exp(1) < 3 and 3^5 < 2^8 gives epsilon exp(22) < 1/2 and epsilon exp(44) < exp(-14)/3. Thus f_1 + f_2 < 0 and the actual two-flag root fidelity is smaller than sqrt(Z). This source comparison uses the physical partial trace and the joint states with marginals P = I/3 and Q.

The Lean theorem proves the finite matrix overlap inequality. The physical embedding above is a mathematical derivation. For the same reference and Q, take alternative blocks epsilon Q and (1-epsilon)Q. The entropy loss is epsilon Tr Q (exp(H)-I-H) + O(epsilon²) with strictly positive leading coefficient. The actual recovery residual is O(epsilon) in trace norm, so the squared residual divided by the loss tends to zero on that path.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.polar_optimized_overlap_lt`
- Truth anchor: `D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
