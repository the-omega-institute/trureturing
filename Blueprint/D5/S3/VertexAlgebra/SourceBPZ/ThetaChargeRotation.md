# Charge Rotation and Dihedral Invariants

## Abstract

Charge rotations and lattice reflection give an exact dihedral invariant-dimension formula.

An additive charge map ell to ZMod 3 and a unit-valued phase define charge rotations on every energy grade. Lattice theta conjugates each rotation to its inverse, giving an action of the six-element dihedral group. No surjectivity of ell is assumed.

**Theorem 1.1 (Residue-sector dimension).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeResidue_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeResidue_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive-definite lattice, the dimension of charge residue r at integer energy n is the number of energy-fiber basis labels with ell(charge) = r.

**Theorem 1.2 (Reflection reverses charge residue).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeTheta_mem_gradeChargeResidue_neg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeTheta_mem_gradeChargeResidue_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every energy grade of a positive-definite lattice, theta maps residue r into residue -r.

**Theorem 1.3 (Rotation trace sum).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeRotation_trace_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeRotation_trace_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nontrivial phase and a positive-definite lattice, the sum of the three rotation traces is three times the number N0 of neutral-residue energy-fiber labels.

**Theorem 1.4 (Reflection characters).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the three dihedral reflections has character equal to the trace T of theta on the full energy grade. This identity requires neither positive definiteness nor a nontrivial phase.

**Theorem 1.5 (Exact character average).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_average_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_average_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive-definite lattice and a nontrivial phase, one sixth of the sum of the six dihedral characters is (N0 + T)/2. The trace T is on the full energy grade.

**Theorem 1.6 (Exact invariant dimension).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_invariants_finrank_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_invariants_finrank_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the complex dimension of the dihedral invariant submodule is (N0 + T)/2. This is a finite-grade representation-theoretic consequence; no analytic convergence or literature novelty is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_average_sharp`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_character_reflection`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeDihedral_invariants_finrank_sharp`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeResidue_finrank`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeChargeRotation_trace_sum`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/ThetaChargeRotation.gradeTheta_mem_gradeChargeResidue_neg`
