import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.Fermat.CharacterPointCount
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

/-! # Cardinality observation audit for the affine Fermat point count -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.CharacterSums.Fermat.CharacterPointCount

open _root_.D5.S3.CharacterSums.Fermat.CharacterPointCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

/-- The observation is the cardinality of the actual subtype, over every carrier. -/
abbrev countSignature : Signature where
  Params := Type u
  State X := Set X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev countActual : Realization countSignature :=
  realize countSignature (fun _ _ S => (Nat.card S : ℂ)) (fun e => nomatch e)

abbrev countShifted : Realization countSignature :=
  realize countSignature (fun _ _ S => (Nat.card S : ℂ) + 1) (fun e => nomatch e)

abbrev affineArena : Arena where
  signature := countSignature.{u}
  Law obs := ∀ {F : Type u} [Field F] [Fintype F] (χ : MulChar F ℂ) {d : ℕ},
    0 < d → orderOf χ = d →
      obs.readout () (F × F) {xy | xy.1 ^ d + xy.2 ^ d = 1} =
        (Fintype.card F : ℂ) +
          ∑ i ∈ Ico 1 d, ∑ j ∈ Ico 1 d, jacobiSum (χ ^ i) (χ ^ j)

private theorem affine_shifted_law : ¬ affineArena.{u}.Law countShifted := by
  intro h
  let F := ULift.{u} (ZMod 2)
  have ha := affine_point_count (F := F) (1 : MulChar F ℂ) (d := 1)
    (by decide) (by simp)
  have hb := h (F := F) (1 : MulChar F ℂ) (d := 1) (by decide) (by simp)
  change (Nat.card (affinePoints F 1) : ℂ) + 1 = _ at hb
  have he : (Nat.card (affinePoints F 1) : ℂ) + 1 =
      (Nat.card (affinePoints F 1) : ℂ) + 0 := by
    rw [add_zero]
    exact hb.trans ha.symm
  exact one_ne_zero (add_left_cancel he)

def affineEvidence : Registration affineArena.{u} (type_of% (@affine_point_count.{u})) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨affine_point_count, countShifted, affine_shifted_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countShifted, ?_, rfl, affine_shifted_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, ∅, Set.univ, ?_⟩
    simp [countActual, realize, Nat.card_eq_fintype_card]

/-- The source selection is intentionally unresolved: the cardinality is taken
of a computed subtype, and no faithful source-observation path is asserted here. -/
def affine_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@affine_point_count.{u}) (Realization countSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.CharacterSums.Fermat.CharacterPointCount.affine_unit
  realizationName := `Reg.D5.S3.CharacterSums.Fermat.CharacterPointCount.affineEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨affineArena.{u}⟩
  objectArena := .source ⟨affineArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source affineArena.{u} ⟨affineEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature.{u}
    (fun _ _ S => (Nat.card S : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.Fermat.CharacterPointCount
