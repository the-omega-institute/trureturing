# Rado's independent-transversal criterion

## Abstract

Rank inequalities characterize independent representatives of a finite indexed family.

**Theorem 1.1 (Independent representatives and subfamily rank).**

$$\forall (I: Type_{u}), \forall (E: Type_{v}), [Finite\left(I\right)] [Finite\left(E\right)] \forall (M: Matroid\left(E\right)), \forall (A: I \to Set\left(E\right)), (\exists (f: I \to E), (\operatorname{Function}.\operatorname{Injective}\left(f\right)) \land ((\forall (i: I), f\left(i\right) \in A\left(i\right)) \land (\operatorname{Matroid}.\operatorname{Indep}\left(M, \operatorname{Set}.\operatorname{range}\left(f\right)\right)))) \Leftrightarrow (\forall (J: Finset\left(I\right)), \operatorname{Nat}.\operatorname{cast}\left(\operatorname{Finset}.\operatorname{card}\left(J\right)\right) \le \operatorname{Matroid}.\operatorname{eRk}\left(M, \operatorname{Set}.\operatorname{iUnion}\left((i: I \mapsto \operatorname{Set}.\operatorname{iUnion}\left((h: i \in J \mapsto A\left(i\right))\right))\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Rado.rado_independent_transversal` (`✓ std3`). ∎

*Citation.* Richard Rado (1942). *A theorem on independence relations*. DOI: [10.1093/qmath/os-13.1.83](https://doi.org/10.1093/qmath/os-13.1.83). URL: <https://doi.org/10.1093/qmath/os-13.1.83>.

*Commentary.*

Let I : Type u and E : Type v be finite types in independent universes. For any native matroid M on E and any family A : I -> Set E, an independent transversal is one function f : I -> E that is injective, satisfies f i in A i for every i, and has M-independent range. Such a function exists if and only if, for every finite subfamily J : Finset I, the cardinality of J, coerced to ENat, is at most the rank of the union of A i over i in J. The same M and A occur on both sides of the equivalence.

The ground M.E is arbitrary, and the sets A i need not lie in it. Independence forces the selected representatives into the ground. The assumptions are only Finite I and Finite E; Fintype and decidable equality are chosen internally. Empty index and carrier types, loops and rank zero are included. No nonemptiness, full-ground, positive-rank, field or representability premise is required.

Necessity restricts the selected independent range to each subfamily. Injectivity identifies its cardinality with that subfamily's cardinality, and rank monotonicity gives the inequality. Sufficiency uses strong induction on the family size. A nonempty proper tight subfamily supplies a basis of its union; contract its representatives, solve the complementary family, and glue the two independent selections. If every nonempty proper subfamily has strict slack, choose a nonloop for one index, contract it, solve the remaining indices, and adjoin that representative. The empty family starts the induction.

Contraction uses the native identity (M / C).eRk Y + M.eRk C = M.eRk (Y union C). For an independent C its rank equals its cardinality. Finite ENat cancellation gives the two rank estimates needed in the tight and strict branches. Independence after contraction keeps the new representatives disjoint from C, so the glued function is injective and its whole range is independent.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Rado.rado_independent_transversal`
- Dependency: [D5/S3/Combinatorics/Matroids/FiniteIntersection](FiniteIntersection.md)
