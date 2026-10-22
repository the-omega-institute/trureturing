/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual original BRST cohomology carries bilinear integer modes and parity projections. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstStateField
import D5.S3.VertexAlgebra.LatticeBcGhostNeutralCohomology
import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import Mathlib.LinearAlgebra.Quotient.Bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologyModes

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeBcGhostBrstCharge (State Q)
open LatticeBcGhostNeutralCohomology
  (OriginalCycles OriginalBoundaries OriginalCohomology original_image_in_cycles)
open LatticeBcGhostTensorStateField (stateField parityPart homogeneous)
open scoped VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem parityPart_Q_even (vector : State D) :
    parityPart 0 (Q D H vector) = Q D H (parityPart 1 vector) := by
  have split : Q D H (parityPart 0 vector) + Q D H (parityPart 1 vector) =
      Q D H vector := by
    rw [← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
  have firstFixed : parityPart 1 (Q D H (parityPart 0 vector)) =
      Q D H (parityPart 0 vector) :=
    (LatticeBcGhostTensorStateField.homogeneous_fixed 1 _).mp
      (LatticeBcGhostBrstStateField.Q_mem D H 0 _
        (LatticeBcGhostTensorStateField.parityPart_mem 0 vector))
  have secondFixed : parityPart 0 (Q D H (parityPart 1 vector)) =
      Q D H (parityPart 1 vector) :=
    (LatticeBcGhostTensorStateField.homogeneous_fixed 0 _).mp
      (LatticeBcGhostBrstStateField.Q_mem D H 1 _
        (LatticeBcGhostTensorStateField.parityPart_mem 1 vector))
  have vanish : parityPart 0 (Q D H (parityPart 0 vector)) = 0 := by
    rw [← firstFixed]
    exact LatticeBcGhostTensorStateField.parityPart_orthogonal 0 1 (by norm_num) _
  rw [← split, map_add, vanish, secondFixed, zero_add]

theorem parityPart_Q_odd (vector : State D) :
    parityPart 1 (Q D H vector) = Q D H (parityPart 0 vector) := by
  have split : Q D H (parityPart 0 vector) + Q D H (parityPart 1 vector) =
      Q D H vector := by
    rw [← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
  have firstFixed : parityPart 1 (Q D H (parityPart 0 vector)) =
      Q D H (parityPart 0 vector) :=
    (LatticeBcGhostTensorStateField.homogeneous_fixed 1 _).mp
      (LatticeBcGhostBrstStateField.Q_mem D H 0 _
        (LatticeBcGhostTensorStateField.parityPart_mem 0 vector))
  have secondFixed : parityPart 0 (Q D H (parityPart 1 vector)) =
      Q D H (parityPart 1 vector) :=
    (LatticeBcGhostTensorStateField.homogeneous_fixed 0 _).mp
      (LatticeBcGhostBrstStateField.Q_mem D H 1 _
        (LatticeBcGhostTensorStateField.parityPart_mem 1 vector))
  have vanish : parityPart 1 (Q D H (parityPart 1 vector)) = 0 := by
    rw [← secondFixed]
    exact LatticeBcGhostTensorStateField.parityPart_orthogonal 1 0 (by norm_num) _
  rw [← split, map_add, firstFixed, vanish, add_zero]

theorem parityPart_periodic (first second : ℕ) (same : first % 2 = second % 2) :
    (parityPart first : Module.End ℂ (State D)) = parityPart second := by
  simp only [LatticeBcGhostTensorStateField.parityPart,
    BcGhostSuperGenerators.parityPart, same]

theorem Q_parityPart (parity : ℕ) (vector : State D) :
    Q D H (parityPart parity vector) = parityPart (parity + 1) (Q D H vector) := by
  rcases Nat.mod_two_eq_zero_or_one parity with even | odd
  · rw [parityPart_periodic D parity 0 (by simpa using even),
      parityPart_periodic D (parity + 1) 1 (by omega)]
    exact (parityPart_Q_odd D H vector).symm
  · rw [parityPart_periodic D parity 1 (by simpa using odd),
      parityPart_periodic D (parity + 1) 0 (by omega)]
    exact (parityPart_Q_even D H vector).symm

def cycleParity (parity : ℕ) : Module.End ℂ (OriginalCycles D H) :=
  ((parityPart parity).comp (OriginalCycles D H).subtype).codRestrict
    (OriginalCycles D H) (fun vector => by
      change Q D H (parityPart parity vector.val) = 0
      rw [Q_parityPart D H, show Q D H vector.val = 0 from vector.property, map_zero])

theorem cycleParity_boundary (parity : ℕ) (vector : OriginalCycles D H)
    (boundary : vector ∈ OriginalBoundaries D H) :
    cycleParity D H parity vector ∈ OriginalBoundaries D H := by
  obtain ⟨preimage, equality⟩ := boundary
  change ∃ preimage, Q D H preimage = parityPart parity vector.val
  refine ⟨parityPart (parity + 1) preimage, ?_⟩
  rw [Q_parityPart D H, parityPart_periodic D (parity + 1 + 1) parity (by omega), equality]
  rfl

def parity (grade : ℕ) : Module.End ℂ (OriginalCohomology D H) :=
  (OriginalBoundaries D H).mapQ (OriginalBoundaries D H) (cycleParity D H grade)
    (cycleParity_boundary D H grade)

theorem parity_mk (grade : ℕ) (vector : OriginalCycles D H) :
    parity D H grade ((OriginalBoundaries D H).mkQ vector) =
      (OriginalBoundaries D H).mkQ (cycleParity D H grade vector) := rfl

theorem parity_decomposition (vector : OriginalCohomology D H) :
    parity D H 0 vector + parity D H 1 vector = vector := by
  refine Quotient.inductionOn vector ?_
  intro representative
  change (OriginalBoundaries D H).mkQ (cycleParity D H 0 representative) +
    (OriginalBoundaries D H).mkQ (cycleParity D H 1 representative) =
      (OriginalBoundaries D H).mkQ representative
  rw [← map_add]
  congr 1
  apply Subtype.ext
  exact LatticeBcGhostTensorStateField.parity_decomposition representative.val

theorem mode_closed (left right : OriginalCycles D H) (mode : ℤ) :
    ((stateField D left.val)[[mode]]) right.val ∈ OriginalCycles D H := by
  change Q D H (((stateField D left.val)[[mode]]) right.val) = 0
  rw [LatticeBcGhostBrstStateField.Q_derivation_mixed,
    show Q D H left.val = 0 from left.property,
    show Q D H right.val = 0 from right.property]
  simp

def cycleMode (mode : ℤ) :
    OriginalCycles D H →ₗ[ℂ] OriginalCycles D H →ₗ[ℂ] OriginalCycles D H where
  toFun left :=
    (((stateField D left.val)[[mode]]).comp (OriginalCycles D H).subtype).codRestrict
      (OriginalCycles D H) (fun right => mode_closed D H left right mode)
  map_add' first second := by
    apply LinearMap.ext
    intro right
    apply Subtype.ext
    simp [map_add]
  map_smul' scalar left := by
    apply LinearMap.ext
    intro right
    apply Subtype.ext
    simp [map_smul]

theorem cycleMode_boundary_left (mode : ℤ) (left right : OriginalCycles D H)
    (boundary : left ∈ OriginalBoundaries D H) :
    cycleMode D H mode left right ∈ OriginalBoundaries D H := by
  obtain ⟨preimage, equality⟩ := boundary
  change ∃ preimage, Q D H preimage = ((stateField D left.val)[[mode]]) right.val
  refine ⟨((stateField D preimage)[[mode]]) right.val, ?_⟩
  rw [LatticeBcGhostBrstStateField.Q_derivation_mixed, equality,
    show Q D H right.val = 0 from right.property]
  simp

theorem cycleMode_boundary_right (mode : ℤ) (left right : OriginalCycles D H)
    (boundary : right ∈ OriginalBoundaries D H) :
    cycleMode D H mode left right ∈ OriginalBoundaries D H := by
  obtain ⟨preimage, equality⟩ := boundary
  change ∃ preimage, Q D H preimage = ((stateField D left.val)[[mode]]) right.val
  refine ⟨((stateField D (parityPart 0 left.val))[[mode]]) preimage -
    ((stateField D (parityPart 1 left.val))[[mode]]) preimage, ?_⟩
  have evenClosed : Q D H (parityPart 0 left.val) = 0 := (cycleParity D H 0 left).property
  have oddClosed : Q D H (parityPart 1 left.val) = 0 := (cycleParity D H 1 left).property
  rw [map_sub, LatticeBcGhostBrstStateField.Q_derivation D H 0 _ preimage
      (LatticeBcGhostTensorStateField.parityPart_mem 0 left.val),
    LatticeBcGhostBrstStateField.Q_derivation D H 1 _ preimage
      (LatticeBcGhostTensorStateField.parityPart_mem 1 left.val), evenClosed, oddClosed]
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, zero_add,
    SuperFieldProducts.koszul, pow_zero, pow_one, Nat.mul_zero, Nat.mul_one,
    one_smul, neg_one_smul, sub_neg_eq_add, equality]
  change ((stateField D (parityPart 0 left.val))[[mode]]) right.val +
    ((stateField D (parityPart 1 left.val))[[mode]]) right.val =
      ((stateField D left.val)[[mode]]) right.val
  have fieldSplit : stateField D left.val = stateField D (parityPart 0 left.val) +
      stateField D (parityPart 1 left.val) := by
    rw [← map_add, LatticeBcGhostTensorStateField.parity_decomposition]
  rw [fieldSplit]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply]

def quotientCycleMode (mode : ℤ) :
    OriginalCycles D H →ₗ[ℂ] OriginalCycles D H →ₗ[ℂ] OriginalCohomology D H :=
  (cycleMode D H mode).compr₂ (OriginalBoundaries D H).mkQ

def product (mode : ℤ) :
    OriginalCohomology D H →ₗ[ℂ] OriginalCohomology D H →ₗ[ℂ] OriginalCohomology D H :=
  (quotientCycleMode D H mode).liftQ₂ (OriginalBoundaries D H) (OriginalBoundaries D H)
    (by
      intro left boundary
      apply LinearMap.ext
      intro right
      change (OriginalBoundaries D H).mkQ (cycleMode D H mode left right) = 0
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact cycleMode_boundary_left D H mode left right boundary)
    (by
      intro right boundary
      apply LinearMap.ext
      intro left
      change (OriginalBoundaries D H).mkQ (cycleMode D H mode left right) = 0
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact cycleMode_boundary_right D H mode left right boundary)

theorem product_mk (mode : ℤ) (left right : OriginalCycles D H) :
    product D H mode ((OriginalBoundaries D H).mkQ left)
      ((OriginalBoundaries D H).mkQ right) =
        (OriginalBoundaries D H).mkQ (cycleMode D H mode left right) := rfl

def boundaryCycle
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (critical : D.rank = 26) : State D →ₗ[ℂ] OriginalCycles D H :=
  (Q D H).codRestrict (OriginalCycles D H) (fun vector =>
    original_image_in_cycles D H hHG hGH critical ⟨vector, rfl⟩)

theorem boundaryCycle_class_zero
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (critical : D.rank = 26) (vector : State D) :
    (OriginalBoundaries D H).mkQ (boundaryCycle D H hHG hGH critical vector) = 0 := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  exact ⟨vector, rfl⟩

theorem product_lower_truncation (left right : OriginalCohomology D H) :
    ∃ bound : ℤ, ∀ mode : ℤ, bound < mode → product D H mode left right = 0 := by
  obtain ⟨first, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨second, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  refine ⟨VertexOperatorTensorProduct.upper (stateField D first.val) second.val, ?_⟩
  intro mode above
  rw [product_mk]
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  change ∃ preimage, Q D H preimage = ((stateField D first.val)[[mode]]) second.val
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact (VertexOperatorTensorProduct.mode_zero_above (stateField D first.val) second.val mode above).symm

#print axioms product
#print axioms Q_parityPart
#print axioms product_lower_truncation

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologyModes
