# The arithmetic and geometric endpoints

## Abstract

Geometric maximal correlation one forces arithmetic maximal correlation one.

**Theorem 1.1 (pullPush).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , ( ( Matrix . conjTranspose ( ( U ) ) ) * ( ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) ) * ( U ) ) = X$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compression reverses an isometric matrix embedding.

**Theorem 1.2 (pushMul).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , \forall ( Y : Matrix c c \mathbb{C} ) , ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) * ( ( U ) * ( Y ) * ( Matrix . conjTranspose ( ( U ) ) ) ) = ( ( U ) * ( ( X * Y ) ) * ( Matrix . conjTranspose ( ( U ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushMul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugation by an isometry preserves multiplication.

**Theorem 1.3 (pushHermitian).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( X : Matrix c c \mathbb{C} ) , ( X . IsHermitian ) \to ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) . IsHermitian$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isometric embedding preserves Hermitian matrices.

**Theorem 1.4 (pushTrace).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( X : Matrix c c \mathbb{C} ) , ( ( ( U ) * ( X ) * ( Matrix . conjTranspose ( ( U ) ) ) ) ) . trace = X . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Isometric embedding preserves the trace.

**Theorem 1.5 (tracePair).**

$$\forall ( a : Type ) , \forall ( c : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype c ] [ DecidableEq c ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( S : Matrix c c \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , ( ( ( U ) * ( S ) * ( Matrix . conjTranspose ( ( U ) ) ) ) * X ) . trace = ( S * ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) . trace$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tracePair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedding and compression maps are adjoint for the trace pairing.

**Theorem 1.6 (tensorIso).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to ( ( Matrix . conjTranspose ( V ) ) * V = 1 ) \to ( Matrix . conjTranspose ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) * ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tensorIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Kronecker product of two isometries is an isometry.

**Theorem 1.7 (pullTensor).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , \forall ( X : Matrix a a \mathbb{C} ) , \forall ( Y : Matrix b b \mathbb{C} ) , ( ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) * ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( X ) ( Y ) ) ) ) * ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) = ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( ( ( Matrix . conjTranspose ( ( U ) ) ) * ( X ) * ( U ) ) ) ( ( ( Matrix . conjTranspose ( ( V ) ) ) * ( Y ) * ( V ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullTensor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compression by a product isometry acts separately on tensor factors.

**Theorem 1.8 (marginalAPush).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( V ) ) * V = 1 ) \to \forall ( rho : Matrix ( c \times d ) ( c \times d ) \mathbb{C} ) , partialTraceRight ( ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) * ( rho ) * ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) ) = ( ( U ) * ( ( partialTraceRight rho ) ) * ( Matrix . conjTranspose ( ( U ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalAPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the joint matrix by two local isometries embeds its left marginal by the left isometry.

**Theorem 1.9 (marginalBPush).**

$$\forall ( a : Type ) , \forall ( b : Type ) , \forall ( c : Type ) , \forall ( d : Type ) , [ Fintype a ] [ DecidableEq a ] [ Fintype b ] [ DecidableEq b ] [ Fintype c ] [ DecidableEq c ] [ Fintype d ] [ DecidableEq d ] \forall ( U : Matrix a c \mathbb{C} ) , \forall ( V : Matrix b d \mathbb{C} ) , ( ( Matrix . conjTranspose ( U ) ) * U = 1 ) \to \forall ( rho : Matrix ( c \times d ) ( c \times d ) \mathbb{C} ) , partialTraceLeft ( ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) * ( rho ) * ( Matrix . conjTranspose ( ( ( ( Matrix . kroneckerMap ( \lambda x y \mapsto x * y ) ( U ) ( V ) ) ) ) ) ) ) ) = ( ( V ) * ( ( partialTraceLeft rho ) ) * ( Matrix . conjTranspose ( ( V ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalBPush` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embedding the joint matrix by two local isometries embeds its right marginal by the right isometry.

**Definition 1.10 (Feasible Hermitian correlation values).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (J:\forall (c:\operatorname {Type}), ([\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)](\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to((\operatorname {Matrix}\left(c, c, \mathbb{C}\right))\to(\operatorname {Matrix}\left(c, c, \mathbb{C}\right))))), (\forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {correlationValues}\left(J, rho\right) = \{r:\mathbb{R}\mid\exists (X:\operatorname {Matrix}\left(a, a, \mathbb{C}\right)), (\exists (Y:\operatorname {Matrix}\left(b, b, \mathbb{C}\right)), ((\operatorname {Matrix.IsHermitian}\left(X\right)) \land ((\operatorname {Matrix.IsHermitian}\left(Y\right)) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right)\right)) \cdot (X)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.of}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right)\right)) \cdot (Y)\right) = 0) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(X\right)) \cdot (\operatorname {J}\left(\lambda i j \mapsto \sum k:b, \operatorname {rho}\left((i,k), (j,k)\right), X\right))\right) = 1) \land ((\operatorname {Matrix.trace}\left((\operatorname {Matrix.conjTranspose}\left(Y\right)) \cdot (\operatorname {J}\left(\lambda k l \mapsto \sum i:a, \operatorname {rho}\left((i,k), (i,l)\right), Y\right))\right) = 1) \land (r = \Vert\operatorname {Matrix.trace}\left((\operatorname {Matrix.kroneckerMap}\left(\lambda x y \mapsto (x) \cdot (y), X, \operatorname {Matrix.conjTranspose}\left(Y\right)\right)) \cdot (rho)\right)\Vert))))))))\}))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Definition 24, equation (54), page 19: “where the maximization is over X ∈ Herm(A), Y ∈ Herm(B).” The displayed set consists of the feasible absolute traces with zero marginal expectation and unit quadratic norm. The index types are arbitrary finite types; the marginal matrices are the two finite partial sums.

**Definition 1.11 (Arithmetic maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muAM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto (\frac{1}{2}:\mathbb{C})\cdot((sigma) \cdot (Y) + (Y) \cdot (sigma)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The arithmetic mean gives the linear mean operator X ↦ (sigma X + X sigma)/2. The coefficient is the supremum of the feasible absolute correlations.

**Definition 1.12 (Geometric maximal correlation).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), (\operatorname {muGM}\left(rho\right) = \operatorname {sSup}\left(\operatorname {correlationValues}\left(\lambda (c:\operatorname {Type}) [\operatorname {Fintype}\left(c\right)] [\operatorname {DecidableEq}\left(c\right)] (sigma Y:\operatorname {Matrix}\left(c, c, \mathbb{C}\right)) \mapsto ((\operatorname {CFC.sqrt}\left(sigma\right)) \cdot (Y)) \cdot (\operatorname {CFC.sqrt}\left(sigma\right)), rho\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM` (`✓ std3`).

*Citation.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

The geometric mean gives X ↦ sqrt(sigma) X sqrt(sigma). The real supremum of an empty feasible set is zero.

**Definition 1.13 (The endpoint proposition).**

$$\operatorname {claim} = \forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Formalization.* `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Section VII, page 66: “Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?” Here rho is a positive semidefinite trace-one complex matrix on a product of finite index types. The displayed implication answers the question negatively, including states with singular marginals.

**Theorem 1.14 (Coincidence at maximal correlation one).**

$$\forall (a:\operatorname {Type}), (\forall (b:\operatorname {Type}), ([\operatorname {Fintype}\left(a\right)] [\operatorname {DecidableEq}\left(a\right)] [\operatorname {Fintype}\left(b\right)] [\operatorname {DecidableEq}\left(b\right)] \forall (rho:\operatorname {Matrix}\left((a)\times(b), (a)\times(b), \mathbb{C}\right)), ((\operatorname {Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname {Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\operatorname {muGM}\left(rho\right) = 1) \Rightarrow (\operatorname {muAM}\left(rho\right) = 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result` (`✓ std3`). ∎

*Resolves.* `Problems/george-tomamichel-2025-am-gm-maximal-correlation` (proved) by `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"george-tomamichel-2025-am-gm-maximal-correlation","declaration_gid":"D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ian George and Marco Tomamichel (2025). *A Unified Approach to Quantum Contraction and Correlation Coefficients*. DOI: [10.48550/arXiv.2505.15281](https://doi.org/10.48550/arXiv.2505.15281). URL: <https://arxiv.org/abs/2505.15281v3>.

*Commentary.*

Compressing to the marginal supports preserves the geometric feasible values. At geometric correlation one, a centered fixed vector gives a nontrivial projection commuting with the marginal state. A partner projection has the same marginal and joint probability p, with 0 < p < 1. Centering both projections and dividing by sqrt(p(1-p)) gives arithmetic correlation one. The arithmetic Cauchy–Schwarz bound supplies the matching upper bound.

## References

- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.claim`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.correlationValues`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalAPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.marginalBPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muAM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.muGM`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullPush`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pullTensor`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushHermitian`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushMul`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.pushTrace`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.result`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tensorIso`
- Truth anchor: `D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation.tracePair`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](Divergence/SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/FixedPointProjection](FixedPointProjection.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](QuantumChannels/TwoPositiveTransitionTrace.md)
