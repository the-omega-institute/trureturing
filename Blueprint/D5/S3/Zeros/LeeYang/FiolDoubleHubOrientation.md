# Double-hub orientation

## Abstract

The physical double-hub family: orientation.

For any finite endpoint maps, reverse a chosen set of arrows and replace k_e by n_e-k_e on precisely those edges. This is an involution of the complete admissible split set. It preserves every vertex mass and the full factorial weight. Reindexing the complete sum proves arrow reversal invariance; an individual unsummed split is not asserted invariant.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Definition 1.1 (polynomial).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines polynomial for the physical double-hub family.

**Theorem 1.2 (polynomial reverse).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial_reverse`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexes the full weighted source by that split involution. Exact source statement: theorem polynomial_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]     (s t : E → V) (n : E → ℕ) (f : E → Bool) :     polynomial (reverseSrc s t f) (reverseTgt s t f) n=polynomial s t n.

**Theorem 1.3 (actual arrow sum invariance).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.actual_arrow_sum_invariance`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.actual_arrow_sum_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connects the full reversed physical source with the original independent source. Exact source statement: theorem actual_arrow_sum_invariance (m : ℕ) (n : Edge m → ℕ)     (f : Edge m → Bool) :     polynomial (reverseSrc (src : Edge m → Vertex m) tgt f)       (reverseTgt src tgt f) n=allVertexSource n.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.actual_arrow_sum_invariance`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial_reverse`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous](FiolDoubleHubHomogeneous.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
