# The bracelet matrices form a monoid

## Abstract

Bracelet matrices contain the identity and are closed under ordinary multiplication in every finite dimension.

For each natural number d, matrices have real entries and both indices range over Fin d. The predicate IsBracelet is the existing interface from CirculantBraceletNonUnistochastic. It includes entrywise nonnegativity, unit row and column sums, and the column and row bracelet inequalities for distinct indices. The theorem keeps that predicate unchanged.

**Theorem 1.1 (Identity and product closure).**

$$\forall (d: \mathbb{N}), (\operatorname{CirculantBraceletNonUnistochastic.IsBracelet}\left((1: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{R}\right))\right)) \land (\forall (A: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{R}\right)), \forall (B: Matrix\left(Fin\left(d\right), Fin\left(d\right), \mathbb{R}\right)), (\operatorname{CirculantBraceletNonUnistochastic.IsBracelet}\left(A\right)) \Rightarrow ((\operatorname{CirculantBraceletNonUnistochastic.IsBracelet}\left(B\right)) \Rightarrow (\operatorname{CirculantBraceletNonUnistochastic.IsBracelet}\left((A) \cdot (B)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.bracelet_monoid` (`✓ std3`). ∎

*Resolves.* `Problems/rajchel-korzekwa-puchala-zyczkowski-2021-bracelet-monoid` (proved) by `D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.bracelet_monoid`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rajchel-korzekwa-puchala-zyczkowski-2021-bracelet-monoid","declaration_gid":"D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.bracelet_monoid","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

This is the all-finite-dimensional form of Conjecture 9. The identity clauses use disjoint supports in distinct rows and columns. For products, the column family is transported through a rectangular preservation lemma. A pair of nonnegative input weights is lifted to orthogonal complex amplitudes by a polygon construction. The weighted Lagrange identity records the output overlap as the Euclidean norm of one weighted inner-product coordinate and ordered minor coordinates. Unit column sums cancel the inner-product coordinates, the input bracelet bounds control the minors, and the Euclidean triangle inequality gives the output inequality. Applying the same argument to transposed factors supplies the row family.

The statement includes d = 0 because Fin d is allowed to be empty. In that dimension the distinct-index families are vacuous. No positivity, field, rectangular, or complex matrix conclusion is added to the real square-matrix interface.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/Unistochastic/BraceletMonoid.bracelet_monoid`
- Dependency: [D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic](../CirculantBraceletNonUnistochastic.md)
