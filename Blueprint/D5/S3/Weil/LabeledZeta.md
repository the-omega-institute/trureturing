# Labeled Zeta Vectors

## Abstract

A labeled Dirichlet vector remains nonzero at every spectral parameter.

<a id="describe-labeled-zeta-vector-never-vanishes"></a>

**Theorem 1.1 (The labeled vector never vanishes).**

$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall s\in\mathbb{C},\ \operatorname{labeledZeta}(\ell,s)\neq 0$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero` (`✓ std3`). ∎

*Citation.* Hakan Hedenmalm, Peter Lindqvist, and Kristian Seip (1997). *A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1)*. DOI: [10.1215/S0012-7094-97-08601-4](https://doi.org/10.1215/S0012-7094-97-08601-4).

*Commentary.*

The coordinate product needs no summability claim. Its empty-ledger coordinate is one, so the kernel-checked function cannot equal the zero vector.

## References

- Truth anchor: `D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero`
