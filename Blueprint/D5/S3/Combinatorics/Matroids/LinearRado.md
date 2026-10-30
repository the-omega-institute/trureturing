# Linear representative selection

## Abstract

Dimension inequalities yield spanning representatives and nonzero matrix minors.

**Theorem 1.1 (spanning_representatives).**

$$\forall (F: Type), [Field\left(F\right)] \forall (W: Type), [AddCommGroup\left(W\right)] [Module\left(F, W\right)] [FiniteDimensional\left(F, W\right)] \forall (k: \mathbb{N}), \forall (L: Fin\left(k\right) \to Submodule\left(F, W\right)), (\operatorname{Module}.\operatorname{finrank}\left(F, W\right) \le k) \Rightarrow ((\forall (J: Finset\left(Fin\left(k\right)\right)), \operatorname{Module}.\operatorname{finrank}\left(F, W\right) + \operatorname{Finset}.\operatorname{card}\left(J\right) \le k + \operatorname{Module}.\operatorname{finrank}\left(F, iSup\left((i: Subtype\left((j: Fin\left(k\right) \mapsto j \in J)\right) \mapsto L\left(val\left(i\right)\right))\right)\right)) \Rightarrow (\exists (l: Fin\left(k\right) \to W), (\forall (i: Fin\left(k\right)), l\left(i\right) \in L\left(i\right)) \land (\operatorname{Submodule}.\operatorname{span}\left(F, \operatorname{Set}.\operatorname{range}\left(l\right)\right) = \operatorname{Top}.\operatorname{top})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LinearRado.spanning_representatives` (`✓ std3`). ∎

*Citation.* Richard Rado (1942). *A theorem on independence relations*. DOI: [10.1093/qmath/os-13.1.83](https://doi.org/10.1093/qmath/os-13.1.83). URL: <https://doi.org/10.1093/qmath/os-13.1.83>.

*Commentary.*

The linear form of Rado's theorem selects one vector from each subspace. Its deficit version gives a spanning family: add an auxiliary space of dimension k − Module.finrank F W, choose independent representatives there, and project to W. The finite-set proof separates a proper set with equality in the dimension inequality; otherwise it passes to the quotient by a line.

**Theorem 1.2 (exists_nonsingular_rows).**

$$\forall (F: Type), [Field\left(F\right)] \forall (k: \mathbb{N}), \forall (t: \mathbb{N}), \forall (M: Matrix\left(Fin\left(k\right), Fin\left(t\right), F\right)), (\operatorname{Submodule}.\operatorname{span}\left(F, \operatorname{Set}.\operatorname{range}\left(\operatorname{Matrix}.\operatorname{row}\left(M\right)\right)\right) = \operatorname{Top}.\operatorname{top}) \Rightarrow (\exists (f: Fin\left(t\right) \to Fin\left(k\right)), (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \land (\operatorname{Matrix}.\operatorname{det}\left(\operatorname{Matrix}.\operatorname{submatrix}\left(M, f, id\right)\right) \ne 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LinearRado.exists_nonsingular_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite family spanning a coordinate space contains a basis. Selecting its row indices gives a square submatrix with nonzero determinant.

**Theorem 1.3 (independent_support_matching).**

$$\forall (K: Type), [Field\left(K\right)] \forall (i: Type), \forall (j: Type), [Fintype\left(i\right)] [Fintype\left(j\right)] \forall (v: i \to \left(j \to K\right)), (LinearIndependent\left(K, v\right)) \Rightarrow (\exists (f: i \to j), (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \land (\forall (a: i), v\left(a, f\left(a\right)\right) \ne 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LinearRado.independent_support_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A linearly independent family of coordinate vectors has an injective selection of nonzero coordinates. A nonsingular maximal minor has a nonzero term in its determinant expansion, and the corresponding permutation supplies the selection.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/LinearRado.exists_nonsingular_rows`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LinearRado.independent_support_matching`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LinearRado.spanning_representatives`
