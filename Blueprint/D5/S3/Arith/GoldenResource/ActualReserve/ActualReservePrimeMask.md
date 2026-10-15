# Actual Unrestricted Prime Mask Reserve

## Abstract

An arbitrary finite actual prime mask lower-bounds the same unrestricted reserve and the complete integer gap.

Fix a real x > 1 and lambda_x = 1/(x log x). The actual objective is J_x(n) = log(sigma(n)/n) - lambda_x log n for every n >= 1. M(x) is the supremum over all those integers, including the unit. With the inclusive harmonic reference F(x) = P(x) - lambda_x psi(x), Res(x) = F(x) - M(x) and d_x(n) = M(x) - J_x(n). Both use precisely the same objective, price, integer and unrestricted pressure.

S is any finite set of actual primes such that p^2 >= 2x and p+1 <= x. The endpoints are weak and S may be empty. Write B(S) = sum_S [1/p - log(1+1/p)] and C(S) = sum_S 1/[2p(p+1)]. Put U = T_x union n.primeFactors, A = sum_S [u_p(1) - u_p(n.factorization p)], and K = sum_(U minus S) [H_p(v_p) - u_p(n.factorization p)]. Primes of n beyond the reference support remain in K.

**Theorem 1.1 (Exact gap with both remainder sums).**

$$\forall x\in \mathbb{R},S\in Finset\left(N\right),n\in \mathbb{N},x> 1\land PrimeMask\left(x, S\right)\land n\ge 1\Rightarrow {F\left(x\right)-J\left(x, n\right)=B\left(S\right)+A\left(x, S, n\right)+K\left(x, S, n\right)}\land 0\le A\left(x, S, n\right)\land 0\le K\left(x, S, n\right)\land C\left(S\right)\le B\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask.actual_reference_gap_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite reference maximum supplies H_p(v_p) >= u_p(a) for every exponent. On S the inclusive reference exponent is one. The actual first marginal is strictly above lambda_x and the second strictly below it, even at the weak endpoints. The original generic strict-threshold maximum in GoldenResource5040PriceInterval therefore gives u_p(a) <= u_p(1), without assuming p divides n.

The original local_eq_layer_sum in GoldenResourceSupremum is exposed in place and identifies u_p(1) = log(1+1/p) - lambda_x log p. The existing golden_resource_objective_sum_on factors the actual objective on U. Subtracting the two exact finite sums and splitting S from its complement yields F-J = B+A+K. Both remainder sums are nonnegative. PrefixDeficitKernel.result at exponent one and ratio 1/p supplies C <= B inside this live composition.

At n=1 all actual exponents are zero; A retains u_p(1)-u_p(0). An empty mask leaves the full nonnegative complement. At p^k=x the last reference gain is zero, so omitting or including that layer gives the same F.

**Theorem 1.2 (The same actual reserve and integer defect).**

$$\forall x\in \mathbb{R},S\in Finset\left(N\right),n\in \mathbb{N},x> 1\land PrimeMask\left(x, S\right)\land n\ge 1\Rightarrow C\left(S\right)\le B\left(S\right)\le Res\left(x\right)\land 0\le d\left(x, n\right)\land F\left(x\right)-J\left(x, n\right)=Res\left(x\right)+d\left(x, n\right)\land B\left(S\right)\le Res\left(x\right)+d\left(x, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask.actual_reserve_prime_mask` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GoldenFutureExtensionMaximum.golden_future_extension_maximum_attained at base one and positive lambda_x supplies an actual integer attaining the unrestricted greatest objective value. Apply the preceding uniform inequality to that integer to obtain Res >= B >= C. The greatest-element property also yields d_x(n) >= 0 for every positive n. The exact sigma identity identifies J_x(n). Its gap is Res+d and is bounded below by B. No least/largest optimizer choice is substituted. All actual equality-price choices have the same pressure value; the existing supremum owner supplies that invariance.

The existing results also give a strict pointwise consequence for every real x > 2: Res(x) > 0 and F(x)-J_x(n) > 0 for every n >= 1. This application uses the complete prime union U, which contains the actual prime 2 even when 2 does not divide n. If its exponent is zero, strict increase of x log x gives 1/2-lambda_x log 2 > 0; reference_objective_maximal bounds this first harmonic gain by the inclusive reference maximum. If its exponent is positive, ReferencePrefixDominance.log_geom_prefix_lt_harmonic_prefix makes its actual local objective strictly smaller than the same-exponent harmonic objective, and reference_objective_maximal again bounds the latter by the reference maximum. HarmonicReference.actual_local_le_reference_maximum makes every other local gap nonnegative. The two complete finite factorizations therefore give a strictly positive gap for every actual integer.

Pointwise strict gaps alone do not give a strict gap above an arbitrary supremum. Here golden_future_extension_maximum_attained supplies an actual integer attaining precisely M(x); applying the strict integer gap to that integer proves Res(x) > 0. The endpoint x=2 is excluded. This is a reuse of existing declarations, with no new mathematical declaration or literature-priority claim. It provides neither a common positive constant as x grows nor a quantitative asymptotic lower bound, and it does not control the signed Ipsi term.

This implements the original section 87 finite reserve mechanism. Original section 93.2 already gives the stronger two-candidate producer on sqrt(x)<p<=x-1: the local reserve is min(1/p-log(1+1/p), 1/p-log(1+1/p+1/p^2)+lambda_x log p), with actual exponent one or two and all ties. Its prose bound 0<=Res-B2<=5 x^(-2/3)+2/x holds for every real x>1. Under unconditional PNT its scaled reserve tends to 2(sqrt(2)-1). Those stronger ordinary results are reused context, with no new finite start or Lean acceptance claimed here.

For the full Robin target at E=log n the signed identity remains Delta(n)=Ipsi(E)+Res(E)+d_E(n). A reserve lower bound does not control the signed Ipsi term. The existing section 491 calculation gives Ipsi(log5041)+Res(log5041)<-1/200, using the actual candidate integer 2520 only to lower-bound M; it does not assert an optimizer. Deleting d globally would therefore lose a necessary contribution. A faithful same-source signed estimate retaining d for all n>5040 remains unpaid. The full RH/Robin/5040 goal is active and unproved. The later Chebyshev/dyadic budget and unbounded PNT formalization are separate from this finite step.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask.actual_reference_gap_decomposition`
- Truth anchor: `D5/S3/Arith/GoldenResource/ActualReserve/ActualReservePrimeMask.actual_reserve_prime_mask`
- Dependency: [D5/S3/Arith/GoldenFutureExtensionMaximum](../../GoldenFutureExtensionMaximum.md)
- Dependency: [D5/S3/Arith/GoldenResource/ActualReserve/HarmonicReference](HarmonicReference.md)
- Dependency: [D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone](../FirstLayerMarginalAntitone.md)
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourceSupremum](../GoldenResourceSupremum.md)
- Dependency: [D5/S3/Arith/GoldenResource5040PriceInterval](../../GoldenResource5040PriceInterval.md)
