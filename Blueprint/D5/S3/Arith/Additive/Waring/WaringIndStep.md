# Bounding a phase fiber by an integral

## Abstract

Bounding a phase fiber by an integral

**Theorem 1.1 (Bounding a phase fiber by an integral).**

Lean statement: `D5/S3/Arith/Additive/Waring/WaringIndStep.BCount_le_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/Waring/WaringIndStep.BCount_le_integral` (`✓ std3`). ∎

*Citation.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

For every natural number s, including zero, the cardinality of any phase fiber is bounded by the unit-interval integral of the displacement norm to the power 2s.

**Theorem 1.2 (Grouping by phase).**

Lean statement: `D5/S3/Arith/Additive/Waring/WaringIndStep.normSq_pow_T_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/Waring/WaringIndStep.normSq_pow_T_fiber` (`✓ std3`). ∎

*Citation.* The Waring formalization authors (2026). *Waring's theorem in Lean 4*. URL: <https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765>.

*Commentary.*

For every natural number s, the s-th power of the squared norm of a displacement sum expands over phase fibers weighted by their cardinalities.

## References

- Truth anchor: `D5/S3/Arith/Additive/Waring/WaringIndStep.BCount_le_integral`
- Truth anchor: `D5/S3/Arith/Additive/Waring/WaringIndStep.normSq_pow_T_fiber`
- Dependency: [D5/S3/Arith/Additive/Waring/WaringCoeffBound](WaringCoeffBound.md)
- Dependency: [D5/S3/Arith/Additive/Waring/WaringHolder](WaringHolder.md)
- Dependency: [D5/S3/Arith/Additive/Waring/WaringLemma7](WaringLemma7.md)
- Dependency: [D5/S3/Arith/Additive/Waring/WaringWeylInq](WaringWeylInq.md)
