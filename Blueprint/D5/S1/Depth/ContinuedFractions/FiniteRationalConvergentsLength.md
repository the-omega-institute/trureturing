# Logarithmic rational convergent length

## Abstract

Logarithmic length of the rational Euclidean convergent list

For a rational x, let T(x) be the reciprocal of its fractional part and let den(x) be its positive denominator in lowest terms. The list convergents x includes the integer head. It has one entry at an integer and otherwise has one more entry than convergents T(x). These conventions include zero and negative rationals.

**Theorem 1.1 (Logarithmic length bound).**

$$\forall x \in \mathit{Rat},\; \operatorname{length}\left(\operatorname{convergents}\left(x\right)\right) \le 2 \cdot \operatorname{natLog}\left(2, \operatorname{den}\left(x\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergentsLength.convergents_length_log` (`✓ std3`). ∎

*Citation.* aicyberg (2026). *Finite-register phase estimation and spectral Shor order finding*. URL: <https://github.com/solanaqubits/leanbook/tree/9b742770a2a5dbcf30cf9abc44e711194e957a00>.

*Commentary.*

Here natLog(2,d) denotes Lean's Nat.log 2 d, the integer floor of the base-two logarithm for positive d. There are no extra hypotheses on x. Its canonical denominator is always positive; an integer has denominator one and its singleton list meets the bound with equality.

Strong induction on den(x) separates the integer case, the case where T(x) is an integer, and the case where two recursive steps remain. In the last case the denominator identity for a fractional part gives den(T(T(x))) + den(T(x)) <= den(x). Since den(T(T(x))) < den(T(x)), twice den(T(T(x))) is at most den(x). Monotonicity of the natural logarithm and its multiplication-by-two identity pay for the two list entries removed before the induction hypothesis is applied. The fractional-part argument works for negative x as well.

For natural y,Q,N with Q>0, the existing candidates y Q N filters convergents ((y:Rat)/Q) by denominator less than N. Filtering cannot increase length. The existing reduced_den theorem, with s=y, r=Q, gives den((y:Rat)/Q)=Q/gcd(y,Q)<=Q. Apply the displayed theorem at x=(y:Rat)/Q, then Nat.log_mono_right, to obtain length(candidates y Q N)<=2*Nat.log 2 Q+1. No restriction y<Q is needed for this counting consequence. With Q=2^n, positivity of 2^n and Nat.log_pow give length(candidates y (2^n) N)<=2*n+1 for every natural y,n,N, including n=0.

The quantity bounded is the number of list entries, or Euclidean stages. The repeated maps in the list definition have separate work costs. This estimate supplies no bit-operation or gate bound, observable selector, factoring or success-probability theorem, or hardware estimate. The original statements and proofs are due to aicyberg in the cited source.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/FiniteRationalConvergentsLength.convergents_length_log`
- Dependency: [D5/S1/Depth/ContinuedFractions/FiniteRationalConvergents](FiniteRationalConvergents.md)
