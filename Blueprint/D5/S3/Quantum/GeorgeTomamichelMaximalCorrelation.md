# The arithmetic and geometric endpoints

## Abstract

Geometric maximal correlation one forces arithmetic maximal correlation one.

**Definition 1.1 (Feasible Hermitian correlation values).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (J:\forall (c:\operatorname {Type}), ([\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)](\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to((\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to(\operatorname {Matrix}\left(c, c, \mathbb{C}\right))))), (\forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {correlationValues}\left(J, rho\right) = \{r:\mathbb{R}\mid\exists (X:\operatorname {Matrix}\left(a, a, \mathbb{C}\right)), (\exists (Y:\operatorname {Matrix}\left(b, b, \mathbb{C}\right)), ((\operatorname {Matrix.IsHermitian}\left(X\right)) \land ((\operatorname {Matrix.IsHermitian}\left(Y\right)) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right)\right)) \cdot (X)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right)\right)) \cdot (Y)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(X\right)) \cdot (\operatorname {J}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right), X\right))\right) = 1) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(Y\right)) \cdot (\operatorname {J}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right), Y\right))\right) = 1) \land (r = \Vert\operatorname {Matrix.trace}\left((\operatorname {Matrix.kroneckerMap}\left(\lambda x y \mapsto (x) \cdot (y), X, \operatorname {Matrix.conjTranspose}\left(Y\right)\right)) \cdot (rho)\right)\Vert))))))))\}))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Definition 24, equation (54), page 19: “where the maximization is over X ∈ Herm(A), Y ∈ Herm(B).” The displayed set consists of the feasible absolute traces with zero marginal expectation and unit quadratic norm. The index types are arbitrary finite types; the marginal matrices are the two finite partial sums.

**Definition 1.2 (Arithmetic maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muAM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto (\frac{1}{2}:\mathbb{C})\cdot((sigma) \cdot (Y) + (Y) \cdot (sigma)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The arithmetic mean gives the linear mean operator X ↦ (sigma X + X sigma)/2. The coefficient is the supremum of the feasible absolute correlations.

**Definition 1.3 (Geometric maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muGM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto ((\operatorname {CFC.sqrt}\left(sigma\right)) \cdot (Y)) \cdot (\operatorname {CFC.sqrt}\left(sigma\right)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The geometric mean gives X ↦ sqrt(sigma) X sqrt(sigma). The real supremum of an empty feasible set is zero.

**Definition 1.4 (The endpoint proposition).**

$$\operatorname {claim} = \forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Section VII, page 66: “Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?” Here rho is a positive semidefinite trace-one complex matrix on a product of finite index types. The displayed implication answers the question negatively, including states with singular marginals.

**Theorem 1.5 (Coincidence at maximal correlation one).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Compressing to the marginal supports preserves the geometric feasible values. At geometric correlation one, a centered fixed vector gives a nontrivial projection commuting with the marginal state. A partner projection has the same marginal and joint probability p, with 0 < p < 1. Centering both projections and dividing by sqrt(p(1-p)) gives arithmetic correlation one. The arithmetic Cauchy–Schwarz bound supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/FiniteCorrelationRecovery](FiniteCorrelationRecovery.md)
- Dependency: [D5/S3/Quantum/FixedPointProjection](FixedPointProjection.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](Matrix/CartesianVariance.md)
