# Positive definite similarity need not give diagonal majorization

## Abstract

A positive definite similarity in dimension seven defeats diagonal majorization.

**Definition 1.1 (Majorization by a doubly stochastic matrix).**

$$\forall (n: \mathbb{N}), \forall (y: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \forall (x: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \operatorname{Majorizes}\left(y, x\right) = (\exists (S: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (S \in \operatorname{doublyStochastic}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)) \land (x = \operatorname{Matrix.mulVec}\left(S, y\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.Majorizes` (`✓ std3`).

*Citation.* Jeffrey Uhlmann (2023). *Partial Proof of a Conjecture with Implications for Spectral Majorization*. DOI: [10.46571/JCI.2023.2.4](https://doi.org/10.46571/JCI.2023.2.4). URL: <https://arxiv.org/abs/2309.01302v1>.

*Commentary.*

Section 3, page 5: "An alternative definition is that x ≺ y if and only if" x = Sy (3.2), "where S is a doubly-stochastic matrix, i.e., nonnegative with every row and column sum equal to unity." Majorizes y x means x ≺ y. The vectors are real and indexed by Fin n; doublyStochastic supplies the nonnegativity and both unit-sum conditions.

**Definition 1.2 (The unrestricted diagonal-spectrum assertion).**

$$claim = (\forall (n: \mathbb{N}), \forall (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (\operatorname{Matrix.PosDef}\left(P\right)) \Rightarrow (\forall (d: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \operatorname{Majorizes}\left((fun (i: \operatorname{Fin}\left(n\right)) \mapsto (P \cdot \operatorname{Matrix.diagonal}\left(d\right) \cdot P^{-1})\left(i, i\right)), d\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.claim` (`✓ std3`).

*Citation.* Jeffrey Uhlmann (2023). *Partial Proof of a Conjecture with Implications for Spectral Majorization*. DOI: [10.46571/JCI.2023.2.4](https://doi.org/10.46571/JCI.2023.2.4). URL: <https://arxiv.org/abs/2309.01302v1>.

*Commentary.*

Section 4, page 7: "However, the fact that such a construction does not generally exist for n > 6 does not necessarily imply that the diagonal-spectrum majorization relationship does not hold in general." "Empirical investigation may be able to provide sufficient evidence to justify a conjecture or, alternatively, empirical and/or analytical efforts may identify counterexamples that constrain such generalizations" The formula expresses the unrestricted assertion considered there: n ranges over all natural numbers, P is real symmetric positive definite, and Matrix.diagonal d is any real diagonal matrix. The entries of d are the spectrum of its similarity by P. No upper bound on n is imposed.

**Theorem 1.3 (A seven-dimensional refutation).**

$$\neg(\forall (n: \mathbb{N}), \forall (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), (\operatorname{Matrix.PosDef}\left(P\right)) \Rightarrow (\forall (d: \operatorname{Fin}\left(n\right) \to \mathbb{R}), \operatorname{Majorizes}\left((fun (i: \operatorname{Fin}\left(n\right)) \mapsto (P \cdot \operatorname{Matrix.diagonal}\left(d\right) \cdot P^{-1})\left(i, i\right)), d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/uhlmann-2023-diagonal-majorization-question` (refuted) by `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"uhlmann-2023-diagonal-majorization-question","declaration_gid":"D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jeffrey Uhlmann (2023). *Partial Proof of a Conjecture with Implications for Spectral Majorization*. DOI: [10.46571/JCI.2023.2.4](https://doi.org/10.46571/JCI.2023.2.4). URL: <https://arxiv.org/abs/2309.01302v1>.

*Commentary.*

In blocks of sizes 1, 1 and 5, take P = [[10,1,2eᵀ],[1,10,2eᵀ],[2e,2e,10I]], where e has five entries equal to one, and take d = (1,20,2,2,2,2,2). For coordinates (x,y,z), the quadratic form is 10∑ᵢ(zᵢ+(x+y)/5)²+(7/2)(x+y)²+(9/2)(x−y)². It is positive for every nonzero vector: its vanishing would force x+y=x−y=0 and then every zᵢ=0. The inverse has hub block [[8/63,1/63],[1/63,8/63]], hub-to-leaf entries −1/35, and leaf block I/10+(2/175)eeᵀ. Exact multiplication gives diag(P·Matrix.diagonal(d)·P⁻¹) = (64/63,1565/63,36/35,36/35,36/35,36/35,36/35). Every entry is at least 64/63. Every row of a doubly stochastic matrix forms a convex combination, so its product with this vector has every entry at least 64/63. It cannot have first entry 1. This contradicts the displayed unrestricted assertion. The source's results with their dimensional restriction and its constructions from factors satisfying the majorization property keep their stated scopes.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.Majorizes`
- Truth anchor: `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/UhlmannDiagonalMajorizationRefutation.result`
