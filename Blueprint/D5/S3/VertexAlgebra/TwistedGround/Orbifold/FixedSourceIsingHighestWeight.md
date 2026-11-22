# Null coefficients on odd Ising highest-weight vectors

## Abstract

Null coefficients on odd Ising highest-weight vectors

Take a charge a with ⟨a, a⟩ = 4 and a parameter s with s² = 1. Given hu : IsUnit D.G.det, let x in the actual odd sector paritySpace D hu (-1) satisfy L(0)x = h · x and L(n)x = 0 for every positive integer n. The null coefficient recursion uses fixed lattice descendants and the action of their fields on the odd sector.

**Theorem 1.1 (Fourth null coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_fourth_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_fourth_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient four acts on x by 6(2h − 1)(16h − 1) times L(−1)x.

**Theorem 1.2 (Third null coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_third_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_third_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient three acts on x by 3(64h + 7)L(−1)²x + 24h(8h − 17)L(−2)x.

**Theorem 1.3 (First-descendant constraint).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_null_constraint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_null_constraint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing of the fourth null coefficient makes 6(2h − 1)(16h − 1)L(−1)x zero.

**Theorem 1.4 (Weight zero).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_zero_level_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_zero_level_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first descendant L(−1)x vanishes at weight zero.

**Theorem 1.5 (Weight one half).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_half_level_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_half_level_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At weight one half the third null coefficient gives L(−2)x = (3/4)L(−1)²x.

**Theorem 1.6 (Weight one sixteenth).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_sixteenth_level_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_sixteenth_level_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At weight one sixteenth the third null coefficient gives L(−2)x = (4/3)L(−1)²x.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_half_level_two`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_null_constraint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_sixteenth_level_two`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.highest_weight_zero_level_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_fourth_mode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.nullState_third_mode`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsing](FixedSourceIsing.md)
