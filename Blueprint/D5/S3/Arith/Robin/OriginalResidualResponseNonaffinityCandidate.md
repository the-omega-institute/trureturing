# Affine Defect of the Original Mobius Floor Response

## Abstract

The original finite Mobius floor response has a quantitative pointwise defect from every affine vector on its complete original integer block.

All logarithms are natural. For natural N>=3 and natural d, use the unchanged OriginalResidualFiniteTransfer.coefficient c(N,d)=mu(d)*log(N/d)/log(N), with real division inside the logarithm. The Mobius function is the actual ArithmeticFunction.moebius at every original index. Put C(N)=sum_(1<=d<=N)c(N,d)/d. The unchanged OriginalResidualFiniteTransfer.response is R(N,m)=1+C(N)*m-sum_(1<=d<=N)c(N,d)*floor(m/d). The floors are natural division, then cast to the reals; the constant, linear term and every original Mobius row remain. The complete block is S(N)={m in N:N<=m<2N}.

**Theorem 1.1 (An original prime/composite four-point gap).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_four_point_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_four_point_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3 there are distinct internal prime/composite base indices p,c with N<p,c<2N such that every real affine error E(m)=R(N,m)-alpha-beta*m/N satisfies 1-log(2)/log(N)<=E(c)-E(c-1)-E(p)+E(p-1). The four slots may overlap. This supplier is consumed by the quantitative defect and the collision-aware lower energy of the actual original response adjoint.

**Theorem 1.2 (A definite pointwise defect for every affine comparison).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_affine_defect_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_affine_defect_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3 and every pair of real numbers alpha,beta, there exists a natural m in S(N) such that (1-log(2)/log(N))/4 <= abs(R(N,m)-alpha-beta*(m/N)). The coordinates are exactly (1,m/N). The real alpha,beta are arbitrary. The witness is required only to belong to S(N); no extra separation premise is used.

The actual literal-floor increment of R is C(N) minus the truncated coefficient sum over divisors of the increment index. For N<t<2N, every proper divisor is below N, so the full divisor identity ArithmeticFunction.sum_moebius_mul_log_eq supplies the truncated sum without discarding any original row. Bertrand's interval prime supplier Nat.exists_prime_lt_and_le_two_mul gives an internal prime p, where this sum equals 1. An internal even composite c has sum at most log(2)/log(N). Hence the increment at c minus the increment at p is at least delta=1-log(2)/log(N).

For E(m)=R(N,m)-alpha-beta*m/N, subtracting the affine function changes both increments by the same beta/N. Therefore delta <= E(c)-E(c-1)-E(p)+E(p-1). All four slots belong to S(N). If each absolute error were strictly below delta/4, their four-term combination would be strictly below delta, a contradiction. Slots may overlap; no four-distinct-points assumption is used.

**Theorem 1.3 (The complete original response is not affine).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_not_affine_on_original_block`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_not_affine_on_original_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=3, there do not exist real alpha,beta such that R(N,m)=alpha+beta*(m/N) for every natural m in S(N). The original proof compares the same internal prime and even-composite increments. An affine vector would make both increments equal beta/N, whereas log(2)<log(N) makes the supplied gap strictly positive.

These are finite statements about the exact original response. They give no prescribed Robin endpoint pair, signed interval realization, infinite compensation, strict Robin inequality for every integer above 5040, or proof of RH. The classical divisor and prime-existence suppliers are reused; no literature novelty claim is made for this repository derivation.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_affine_defect_lower_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_four_point_gap`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualResponseNonaffinityCandidate.response_not_affine_on_original_block`
- Dependency: [D5/S3/Arith/Robin/OriginalResidualFiniteTransfer](OriginalResidualFiniteTransfer.md)
