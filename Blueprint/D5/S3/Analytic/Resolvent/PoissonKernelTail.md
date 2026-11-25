# Positive kernels and reciprocal-square tails

## Abstract

A positive Poisson-kernel envelope controls reciprocal-square tails of arbitrary height families.

**Theorem 1.1 (Continuity at every real width).**

Lean statement: `D5/S3/Analytic/Resolvent/PoissonKernelTail.cauchyKernel_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/PoissonKernelTail.cauchyKernel_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shared Cauchy kernel is cauchyKernel(w,x)=w/(w^2+x^2), continuous in x for every real w. The Poisson kernel is its translate cauchyKernel(u,t-g). The Gamma integral comparison uses the same kernel and continuity theorem.

Let the index type be arbitrary and fix T>32. On abs(g)>T, let the real weights be nonnegative, and impose 0<=u on the real kernel widths only where w>0. The kernel at height g and evaluation point x is u/(u^2+(x-g)^2). For each sign s=1 or s=-1, each t>=T-16 and each finite J with s*g_i>T for every i in J, assume the weighted kernel sum at x=s*t is at most (log(q*(t+3))+1)/2. There is no countability, local finiteness, or reflection assumption.

Write C=2*arctan(8), M_i=2*arctan(16/u_i), massRatio(u_i)=M_i/C, c(q)=1 if q=0 and c(q)=2 otherwise, and B=(log(q*(T-13))+c(q))/(C*(T-32)). Define E(q,x)=(log(q*(x+3))+c(q))/(x-16). For a finite J and a sign s, let K_s(J) consist of the i in J with T<s*g_i and 0<w_i, and put b_s(J)=T-16+sum over K_s(J) of abs(s*g_i). The finiteCorrection for that side is D_s(J)=E(q,b_s(J))/(2*C).

**Theorem 1.2 (Exact mass bound for nonnegative widths on one side).**

Lean statement: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_mass_side_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_mass_side_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix s=1 or s=-1 and assume only this sign's kernel envelope. Require w_i>=0 where s*g_i>T, and u_i>=0 there only where w_i>0. For every finite J, the mass-weighted subsum is at most B/2-D_s(J)<B/2. The mass-weighted family is summable and its total is at most B/2. There is no upper width bound. At u_i=0 both the kernel and massRatio(u_i) are zero, using real division by zero. The ordinary side estimate applies this theorem before comparing ordinary and mass-weighted terms.

**Theorem 1.3 (One side with local assumptions).**

Lean statement: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_side_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_side_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix s=1 or s=-1. Nonnegative weights are required only where s*g>T, and 0<u<=2 only on that side where w>0. Assume the kernel envelope only for this sign. For every finite J, the sum over K_s(J) of (M_i/C)*(w_i/g_i^2) is at most B/2-D_s(J)<B/2. The sum over J of massRatio(u_i)*positiveTerm(s*g,T,w,i) is exactly this filtered sum, since all omitted terms vanish and (s*g_i)^2=g_i^2. The ordinary reciprocal-square subsum is at most the mass-weighted subsum because M_i/C>=1 for 0<u_i<=2. Both the ordinary and mass-weighted families are summable, with each total at most B/2. No assumption is imposed on the opposite side. The two-sided result applies this estimate to each of the disjoint height signs.

**Theorem 1.4 (Uniform finite bounds and both infinite height tails).**

Lean statement: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite J, its mass-weighted sum on abs(g)>T is at most B-(D_1(J)+D_{-1}(J))<B. The mass-weighted family is summable and its total is at most B. For each sign the mass-weighted finite subsum is at most B/2-D_s(J)<B/2; that side family is summable with total at most B/2. These conclusions require only nonnegative widths at positive-weight tail indices. If additionally 0<u_i<=2 at those indices, every ordinary finite subsum is at most its mass-weighted subsum, the ordinary full tail is summable with total at most B, and each ordinary side is summable with total at most B/2. The weights are retained without pairing positive and negative heights.

The positive-kernel integral method has an explicit finite-interval form. The mass in the window [g-16,g+16] is 2*arctan(16/u), and the weighted window comparison retains this exact mass for every u>=0, without an upper width bound. For 0<u<=2 this mass is at least C=2*arctan(8)>pi-1/4. On that window the weight 1/(t-16)^2 is at least 1/g^2 for g>T. For K_s(J), write S for the sum of abs(s*g_i). The endpoint b_s(J) contains all their windows: abs(s*g_i)<=S and T>32 give s*g_i+16<=S+16<T-16+S. The envelope gives E(q,b_s(J))>0. It also makes the logarithmic integrand nonnegative, so its endpoint budget is nonincreasing by the integral budget inequality. Thus a smaller endpoint retains a larger correction. For q!=0 the derivative of -(log(q*(t+3))+2)/(t-16) dominates the logarithmic envelope divided by (t-16)^2; its value at the upper endpoint is strictly negative. For q=0 the reciprocal-square power integral gives the endpoint difference 1/(a-16)-1/(b-16). In both cases the integral is at most E(q,a)-E(q,b). Dividing by C retains every factor M_i/C and D_s(J)>0. No term-dependent mass is replaced by its uniform lower bound. The uniform bound gives summability, without interchanging an infinite sum and an integral.

The real parameter q is unrestricted. For q!=0 the logarithm is differentiated away from zero, with log(q*x)=log(abs(q)*x) for x>0; for q=0 Lean's real logarithm has value zero and the power integral supplies the smaller constant c(0)=1. The envelope itself supplies the required nonnegativity. The cutoff T>32 keeps t-16 positive throughout the integration interval. The upper width bound is used only in deriving the ordinary bounds from the exact mass-weighted bounds via 16/u>=8. Zero-weight terms are removed before integration. Nonnegative weights permit restriction of sums and passage to infinite sums. No sign or width constraint is imposed on abs(g)<=T. Taking u=2-beta and w equal to a natural multiplicity recovers the zero-family estimate for 0<=beta<=1; the proof also allows 0<=beta<2. Optimizing the window or the width range is a separate estimate.

## References

- Truth anchor: `D5/S3/Analytic/Resolvent/PoissonKernelTail.cauchyKernel_continuous`
- Truth anchor: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_mass_side_bound`
- Truth anchor: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_side_bound`
- Truth anchor: `D5/S3/Analytic/Resolvent/PoissonKernelTail.reciprocalSquare_tail_bound`
- Dependency: [D5/S3/Analytic/Boundary/HorizontalLogPotential](../Boundary/HorizontalLogPotential.md)
