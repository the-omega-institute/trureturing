# Actual-Carrier Weighted Quadratic for Separable Records

## Abstract

The actual separable right-maximum series satisfies the source weighted quadratic.

**Theorem 1.1 (The actual quadratic with singleton and proper-cut terms).**

$$J = z + z \cdot (1 + \operatorname{C}\left(q\right)) \cdot J + \operatorname{C}\left(q\right) \cdot (1 + \operatorname{C}\left(q\right)) \cdot J^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J is the positive bivariate series whose outer coefficient marks the strict right-maximum count and whose inner coefficient marks length. q is the positive-length counting series of the literal permutations of Fin n avoiding 2413 and 3142. z is the singleton term, and C is the constant-series embedding into the outer PowerSeries.

The proof uses the frozen minimum-cut enumeration on the actual carrier. It restricts the block record laws to exact record fibers, combines the opposite-sign transport with the actual Schröder cardinalities, and derives I0(1+q)=q from the scalar Schröder equation. The proper-cut series then satisfies R=C(q)J and the all-avoider series satisfies U=(1+C(q))J, yielding the displayed quadratic.

The result is the source-faithful actual-carrier bridge needed before coefficient extraction. It does not by itself prove the arbitrary-index binomial T_r identity, the all-index declining comparisons, the three peak or the complete four-distribution CKZ conclusion. Registration remains paused and no external-problem resolution is claimed here.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/RecordAllIndex.actual_weighted_quadratic`
- Dependency: [D5/S1/Words/Patterns/Separable/RecordFirstDecline](RecordFirstDecline.md)
- Dependency: [D5/S1/Words/Patterns/Separable/RecordNewtonPositivity](RecordNewtonPositivity.md)
