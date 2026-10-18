# Entropy Direction Bounds

## Abstract

A logarithmic divided-difference bound and the entropy derivative of a finite three-point convolution.

**Theorem 1.1 (The logarithmic slope bound).**

$$0<B<A<1 \Rightarrow \frac{-\operatorname{log}\left(A B\right)}{1-A B}\le\frac{\operatorname{log}\left(A\right)-\operatorname{log}\left(B\right)}{A-B}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.log_divided_difference_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<B<A<1, the secant slope of log is at least −log(AB)/(1−AB). This divided-difference estimate is the bound A1 for the binary-entropy part of the pairwise comparison. Its proof uses log x≤x−1 to control the derivative of log x(1+x)/(1−x).

**Theorem 1.2 (The intermediate slope dominates the logarithm).**

$$0<B<A<1 \Rightarrow -\operatorname{log}\left(A B\right)<\frac{-\operatorname{log}\left(A B\right)}{1-A B}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.neg_log_product_lt_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same range, 0<AB<1 and −log(AB)>0, so division by 1−AB strictly increases −log(AB). This connects the convolution estimate to the divided-difference estimate.

**Definition 1.3 (A three-point convolution direction).**

$$\operatorname{threePointMass}\left(r, v0, v1, v2, t, k\right) = (v0+t)\operatorname{r0}\left(k\right)+(v1-2t)\operatorname{r1}\left(k\right)+(v2+t)\operatorname{r2}\left(k\right)$$

*Formalization.* `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.threePointMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r : Fin n → ℝ, r₀,r₁,r₂ denote its zero-extended shifts by zero, one and two. The output is indexed by Fin(n+2). The real parameter t perturbs the weights in the direction (1,−2,1), preserving their sum.

**Theorem 1.4 (Entropy derivative and upper bound).**

$$\operatorname{HasDerivAt}\left(H, d, 0\right)\land d\le-\operatorname{log}\left(v0 v2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.three_point_entropy_direction_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume r is nonnegative with total mass one, v₀,v₁,v₂ are positive and sum to one. Let Q=threePointMass r v₀ v₁ v₂ 0 and H(t)=Σₖ −Qₜ(k) log Qₜ(k). Then H has derivative d=Σⱼ r j[2 log Q(j+1)−log Q(j)−log Q(j+2)] at zero, and d≤−log(v₀v₂). The indices are the three canonical Fin embeddings. The middle embedding is injective, allowing its mass sum to be bounded by the total output mass. The estimate log x≤x−1 controls the middle term, and Q(j)≥v₀r j and Q(j+2)≥v₂r j control the outer terms. Zero entries of r are permitted. If an output mass vanishes, all three contributing shifted masses vanish and that entropy summand is identically zero in t; no derivative of −x log x at zero is assumed.

## References

- Truth anchor: `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.log_divided_difference_lower`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.neg_log_product_lt_div`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.threePointMass`
- Truth anchor: `D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.three_point_entropy_direction_bound`
- Dependency: [D5/S3/Quantum/Schatten/PowerMajorization](../../Quantum/Schatten/PowerMajorization.md)
