# Best displacements

## Abstract

Adjacent rotation cuts are best displacements.

**Theorem 1.1 (Every gap is a best displacement).**

$$\forall \operatorname{alpha}: \operatorname{Real}, \forall \operatorname{N}: \operatorname{Nat}, [\operatorname{Fact} (\operatorname{Irrational} \operatorname{alpha})], [\operatorname{NeZero} \operatorname{N}], (1<\operatorname{N})\Rightarrow\forall \operatorname{r}: \operatorname{Fin} \operatorname{N}, \operatorname{let} \operatorname{a}:\operatorname{Real}:=\operatorname{rotationCut} \operatorname{alpha} \operatorname{N} \operatorname{r.castSucc}; \operatorname{let} \operatorname{ell}:\operatorname{Real}:=\operatorname{rotationCut} \operatorname{alpha} \operatorname{N} \operatorname{r.succ}-\operatorname{a}; \exists \operatorname{d}:\operatorname{Nat}, 0<\operatorname{d} \land ((\operatorname{ell}=\operatorname{forwardDisplacement} \operatorname{alpha} \operatorname{d} \land \forall \operatorname{k}: \operatorname{Nat}, (0<\operatorname{k})\Rightarrow(\operatorname{k}<\operatorname{d})\Rightarrow\operatorname{ell}\leq\operatorname{forwardDisplacement} \operatorname{alpha} \operatorname{k}) \lor (\operatorname{ell}=\operatorname{backwardDisplacement} \operatorname{alpha} \operatorname{d} \land \forall \operatorname{k}: \operatorname{Nat}, (0<\operatorname{k})\Rightarrow(\operatorname{k}<\operatorname{d})\Rightarrow\operatorname{ell}\leq\operatorname{backwardDisplacement} \operatorname{alpha} \operatorname{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturn.rotation_gap_best_displacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an irrational rotation with at least two cuts, each adjacent gap is a forward or backward displacement no larger than the displacements with smaller positive indices.

**Theorem 1.2 (The golden mechanical slope).**

$$\operatorname{goldenMechanicalSlope}=\operatorname{Real.goldenRatio}-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturn.golden_mechanical_slope_eq_goldenRatio_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden mechanical slope is the golden ratio minus one.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturn.golden_mechanical_slope_eq_goldenRatio_sub_one`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturn.rotation_gap_best_displacement`
- Dependency: [D5/S1/Recurrence/RotationOrbitGapsPartition](../../Recurrence/RotationOrbitGapsPartition.md)
- Dependency: [D5/S1/Words/GoldenMechanicalWord](../GoldenMechanicalWord.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore](GoldenArcFirstReturnCore.md)
