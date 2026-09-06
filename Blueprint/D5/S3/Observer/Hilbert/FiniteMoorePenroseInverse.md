# Finite Moore-Penrose Inverse

## Abstract

The constructed finite Moore-Penrose inverse obeys all four equations and is unique.

For every RCLike scalar field k and finite-dimensional inner-product spaces E and F over k, A is a linear map E to F. MP(A) is the finite sum of rank-one maps formed from a right singular basis, weighted by inverse squared singular values; a zero singular value contributes zero. Products below are compositions, and star is the adjoint.

**Theorem 1.1 (Four derived Penrose equations).**

$$\forall A:E\to_{k}F, A\operatorname{MP}(A)A = A \land \operatorname{MP}(A)A\operatorname{MP}(A) = \operatorname{MP}(A) \land (A\operatorname{MP}(A))^{*} = A\operatorname{MP}(A) \land (\operatorname{MP}(A)A)^{*} = \operatorname{MP}(A)A$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse` (`✓ std3`). ∎

*Citation.* R. Penrose (1955). *A generalized inverse for matrices*. DOI: [10.1017/S0305004100030401](https://doi.org/10.1017/S0305004100030401).

*Commentary.*

All four conditions are proved from the spectral construction. They are not hypotheses of the constructed inverse. This is an attributed source port of the Kitware formal owner at commit 20461e477e1ae464d6abac1dade3188c29109b8c, with pinned-Lean compatibility edits and the complete upstream license retained.

**Theorem 1.2 (Uniqueness).**

$$\forall A:E\to_{k}F, B:F\to_{k}E, (ABA = A \land BAB = B \land (AB)^{*} = AB \land (BA)^{*} = BA) \Rightarrow B = \operatorname{MP}(A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.eq_moorePenroseInverse_of_isMoorePenroseInverse` (`✓ std3`). ∎

*Citation.* R. Penrose (1955). *A generalized inverse for matrices*. DOI: [10.1017/S0305004100030401](https://doi.org/10.1017/S0305004100030401).

*Commentary.*

Any inverse satisfying the four displayed conditions equals the constructed inverse. The downstream finite-synthesis bridge uses this to identify the ordinary inverse in the invertible case.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.eq_moorePenroseInverse_of_isMoorePenroseInverse`
- Truth anchor: `D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse.isMoorePenroseInverse_moorePenroseInverse`
