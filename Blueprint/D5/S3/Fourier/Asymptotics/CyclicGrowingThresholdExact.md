# Exact support at a rear threshold

## Abstract

The exact finite score resolves every adjacent support decision at a leading rear threshold.

Fix parity e in {0,1}, index l≥0, a critical-scale sequence n⁵h(n)²→K, adjacent rear offset sets S=S_l and T=S_(l+1), and shared boundary radius R=l+1+e/2. Let p_S and p_T be the signed weights computed from the two three-moment fits.

**Theorem 1.1 (The two boundary scores have a positive determinant ratio).**

$$\operatorname{Det}\left(\operatorname{MomentMatrix}\left(S\right)\right) \cdot \operatorname{SignedValue}\left(S, R\right) = \operatorname{Det}\left(\operatorname{MomentMatrix}\left(T\right)\right) \cdot \operatorname{SignedValue}\left(T, R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact.adjacent_fit_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The larger window adds two distinct sites with offsets ±R. Their features coincide, so the assembled matrix changes by a rank-one outer product with multiplicity two. Subtract the exact fitted equations with common moment target and apply the matrix determinant lemma to identify the score ratio. Both determinants are eventually positive, since each tends to 16 times its window cardinality divided by 45. The identity also holds at a zero score.

**Theorem 1.2 (The finite score determines the exact support).**

$$\left(0 < \operatorname{SignedValue}\left(S, R\right) \Rightarrow k = l + 1\right) \land \left(\operatorname{SignedValue}\left(S, R\right) \le 0 \Rightarrow k = l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact.eventual_support_at_leading_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume positive integer periods q(n) of eventual parity e, h(n)=2π/q(n), and Q=3K/20=T_e(l+1). For every sufficiently large n choose k=l+1 if p_S(R)>0, and k=l if p_S(R)≤0. This allows k to vary with n. The other rear endpoints and the front endpoints have strict leading signs.

The finite optimizer certificate applies with a nonpositive omitted boundary, so equality of the score selects the smaller positive support. The fitted law is feasible with both exact cosine moment floors, is the unique minimum and has the squared-distance energy inequality. The support is the growing front and the selected rear window, for arbitrary approach rates to the leading critical scale.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact.adjacent_fit_score`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicGrowingThresholdExact.eventual_support_at_leading_threshold`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder](CyclicGrowingRearSecondOrder.md)
