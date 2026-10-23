# Geometric mean lower bound

## Abstract

The matrix geometric mean dominates a quantitative arithmetic correction.

**Definition 1.1 (Geometric mean).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean`

*Formalization.* `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For finite complex square matrices P and Q, set geometricMean(P,Q) to the existing inverse-base mean gmInv(P inverse,Q). For positive definite inputs this is P^(1/2)(P^(-1/2) Q P^(-1/2))^(1/2)P^(1/2). The total definition also assigns zero whenever either input is zero; these are the singular cases needed by the block inequality.

**Theorem 1.2 (Positive Riccati solution).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every dimension and positive definite P,Q, their geometric mean G is positive definite and satisfies G P inverse G=Q. This uses the existing Riccati theorem at base P inverse and supplies positivity and the identity used below.

**Theorem 1.3 (Harmonic lower bound).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every positive definite P,Q, the inverse of (P inverse+Q inverse)/2 is at most their geometric mean G in Loewner order. The Riccati equation gives G inverse P G inverse=Q inverse. The positive quadratic form (G inverse−P inverse) P (G inverse−P inverse) equals P inverse+Q inverse−2G inverse. Inverse order then gives the asserted comparison without a commutation assumption.

**Theorem 1.4 (Exact arithmetic correction).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For H=(P+Q)/2 and K=(P−Q)/2 with P,Q positive definite, the harmonic mean is exactly H−K H inverse K. The intermediate expression P H inverse Q has inverse Q inverse H P inverse=(P inverse+Q inverse)/2. Expanding P=H+K and Q=H−K preserves the order of all matrix factors.

**Theorem 1.5 (Quantitative lower bound).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every dimension, positive definite P,Q and real c,d with c>0, put H=(P+Q)/2 and K=(P−Q)/2. If cI≤H and K²≤dI, then H−(d/c)I≤geometricMean(P,Q). Inverse order yields H inverse≤I/c; conjugation by Hermitian K and the square bound give K H inverse K≤(d/c)I. The exact harmonic correction and harmonic lower bound complete the argument. Taking d to be the squared operator norm of K recovers the corresponding operator norm estimate.

**Theorem 1.6 (Independent positive scaling).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every positive definite P,Q and positive real r,s, geometricMean(rP,sQ)=sqrt(rs) geometricMean(P,Q). The scaled matrix is positive definite and satisfies the scaled Riccati equation, so uniqueness identifies the two means. This identity restores arbitrary diagonal traces after normalization.

**Theorem 1.7 (Zero second input).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every complex square matrix P, geometricMean(P,0)=0. This includes every dimension and supplies the zero-block branch.

**Theorem 1.8 (Zero first input).**

Lean statement: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2016). *A singular value inequality related to a linear map*. DOI: [10.13001/1081-3810.3108](https://doi.org/10.13001/1081-3810.3108). URL: <https://arxiv.org/abs/1609.08231>.

*Commentary.*

For every complex square matrix Q, geometricMean(0,Q)=0. This includes every dimension and supplies the other zero-block branch.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.arithmetic_sub_le_geometricMean`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_riccati`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_smul`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_left`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.geometricMean_zero_right`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_eq_arithmetic_correction`
- Truth anchor: `D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound.harmonic_le_geometricMean`
- Dependency: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization](../AlternativeMeanLinearization.md)
- Dependency: [D5/S3/Quantum/Matrix/CayleyResolvent](../CayleyResolvent.md)
