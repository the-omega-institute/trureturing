# The path Rodrigues coefficient LCM and the Mangoldt remainder

## Abstract

The path Rodrigues coefficient LCM and the Mangoldt remainder

**Theorem 1.1 (The exact factorial complement).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_eq_factorial_div_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_eq_factorial_div_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural r ≥ 2 and s ≥ 0, put x = s + 1. Let L(r,x) be the LCM of the coefficient contents C(r − 1,s,k) for integers 0 ≤ k ≤ s. In the natural numbers, L(r,x) is (s!)^r divided by tailLCM(rx − 1,r − 1). The tail is the product over r ≤ k ≤ rx − 1 of the prefix LCMs at the integer quotients floor((rx − 1)/k).

Each coefficient content and its complementary path moment multiply to (s!)^r. The gcd of those moments is the tail product. The tail times each content divides (s!)^r, giving one divisibility. In the other direction, (s!)^r divides each moment times the LCM and therefore divides their gcd, which is the tail times the LCM.

**Theorem 1.2 (The signed ceiling correction).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.T_eq_U_add_ceilingError`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.T_eq_U_add_ceilingError` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r ≥ 2 and integer x > 0, the logarithm of the tail is the sum over 1 ≤ q ≤ x of Λ(q) times (ceil(rx/q) − r). The count comes from the integers k ≥ r with qk ≤ rx − 1. Dividing by r gives x times the sum of Λ(q)/q, minus ψ(x), plus E(r,x)/r. Here E(r,x) is the sum of Λ(q) times (ceil(rx/q) − rx/q) over the same q.

Write γ for Euler's constant and T(r,x) for log((x − 1)!) − x log x + (1 + γ)x − log L(r,x)/r. The complete Mangoldt remainder U satisfies T(r,x) = U(x) + E(r,x)/r. The ceiling error lies between 0 and ψ(x). At r = x ≥ 2 the difference T(x,x) − U(x) therefore lies between 0 and log 4 + 4.

**Theorem 1.3 (The two-sided diagonal inequality).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.diagonal_gamma_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.diagonal_gamma_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer x ≥ 2, put G(x) = γx − log L(x,x)/x. Then G(x) + 1 − log x − (log 4 + 4) ≤ U(x) ≤ G(x) + 1. Left and right unit-cell sums for log bound the factorial term between γx + 1 − log x and γx + 1. Combining these bounds with the signed ceiling correction gives the two inequalities.

**Theorem 1.4 (Transfer from real windows to all integers in a block).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_gamma_blocks_of_pointwise_windows`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_gamma_blocks_of_pointwise_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose that for every real δ > 0 and every real R there is a Y ≥ max(R,1) with U(t) ≤ t^(1/2+δ) for every real t in [Y,Y^(3/2)]. Then for every real ε > 0 and natural A there is a natural k ≥ max(A,2) such that γx² − x^(3/2+ε) ≤ log L(x,x) for every integer x in [k^12,k^16].

Choose δ = ε/2 and a sufficiently late real window to absorb the additive logarithm and constant in the lower bound for U. The quartic block placement fits the entire interval [k^12,k^16] in that window.

**Theorem 1.5 (The cofinal gamma-block criterion for RH).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.rh_iff_cofinal_contentLCM_gamma_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.rh_iff_cofinal_contentLCM_gamma_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis holds exactly when for every ε > 0 and natural A there is a natural k ≥ max(A,2) with γx² − x^(3/2+ε) ≤ log L(x,x) at every integer x in [k^12,k^16]. Under RH the pointwise Mangoldt window criterion supplies the real windows for the transfer.

Conversely, sample at x = n^4 for each k³ ≤ n ≤ k⁴. The upper inequality for U converts the gamma bound with ε = κ/2 into U(n^4) ≤ (n^4)^(1/2+κ) on sufficiently late blocks for every κ > 0. The quartic integer criterion then gives RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.T_eq_U_add_ceilingError`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_eq_factorial_div_tail`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.contentLCM_gamma_blocks_of_pointwise_windows`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.diagonal_gamma_threshold`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge.rh_iff_cofinal_contentLCM_gamma_blocks`
- Dependency: [D5/S3/Arith/FactorialRatio/PathRodriguesGcd](../../../Arith/FactorialRatio/PathRodriguesGcd.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtPointwiseWindows](MangoldtPointwiseWindows.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSampling](QuarticSampling.md)
