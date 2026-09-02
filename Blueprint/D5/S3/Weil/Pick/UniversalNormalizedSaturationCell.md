# Universal Normalized Saturation Cell

## Abstract

Every normalized unit-phase contact gives one universal two-point Pick cell.

**Theorem 1.1 (The normalized cell is independent of its source data).**

$$\forall S \in \operatorname{Real}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \left(\left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right) \to \left(\operatorname{Circle}\left(\right) \to \left(\operatorname{UnitDisc}\left(\right) \to \operatorname{Complex}\left(\right)\right)\right)\right)\right)\right), A \in \operatorname{Real}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \left(\left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right) \to \left(\operatorname{Circle}\left(\right) \to \operatorname{UnitDisc}\left(\right)\right)\right)\right)\right),\; \left(\left(\forall h \in \operatorname{Real}\left(\right), d \in \operatorname{Real}\left(\right), m \in \operatorname{Nat}\left(\right), Xi \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), u \in \operatorname{Circle}\left(\right),\; S\left(h, d, m, Xi, u, 0\right) = 0\right) \land \left(\forall h \in \operatorname{Real}\left(\right), d \in \operatorname{Real}\left(\right), m \in \operatorname{Nat}\left(\right), Xi \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), u \in \operatorname{Circle}\left(\right),\; S\left(h, d, m, Xi, u, A\left(h, d, m, Xi, u\right)\right) = u\right)\right) \Rightarrow \left(\forall h \in \operatorname{Real}\left(\right), d \in \operatorname{Real}\left(\right), m \in \operatorname{Nat}\left(\right), Xi \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), u \in \operatorname{Circle}\left(\right),\; \operatorname{let}(s := S\left(h, d, m, Xi, u\right), a := A\left(h, d, m, Xi, u\right), K := (z, w \mapsto \frac{1 - s\left(z\right) \times \overline{s\left(w\right)}}{1 - z \times \overline{w}}), p := \operatorname{vector}\left(0, a\right), R := (i, j \mapsto \operatorname{K}\left(\operatorname{p}\left(i\right), \operatorname{p}\left(j\right)\right)))\;R = \operatorname{matrix}\left(1, 1, 1, 0\right) \land \left(\neg \operatorname{PosSemidef}\left(R\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/UniversalNormalizedSaturationCell.universal_normalized_saturation_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The candidate and contact-point families are indexed by zero height, offline distance, multiplicity, completed function, and unit contact phase. This makes every stated independence parameter visible in the theorem.

For every index tuple, the candidate is zero at the origin and takes the selected phase at its selected interior point. The displayed Pick kernel and two-point relation are the source constructions.

The relation is always the matrix with rows (1,1) and (1,0), and it is not positive semidefinite.

## References

- Truth anchor: `D5/S3/Weil/Pick/UniversalNormalizedSaturationCell.universal_normalized_saturation_cell`
- Dependency: [D5/S3/Weil/Pick/MinimalRelationalVisibility](MinimalRelationalVisibility.md)
