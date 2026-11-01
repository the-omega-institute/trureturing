import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.BargmannImaginaryMaximizers
import Reg.Support.DependentFamily

/-! Source-bound audit of the latitude inner-product identity. -/

namespace Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot

open _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe conjugation of the first complex latitude parameter. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => star z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z w : ℂ,
    star (latitude t z) ⬝ᵥ latitude t w =
      ((1 - t : ℝ) : ℂ) + (t : ℂ) * R.readout () () z * w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) (by norm_num) 1 1
  rw [latitude_dot 1 (by norm_num) (by norm_num) 1 1] at hbad
  norm_num [rejected, realize] at hbad

def source_registration : Registration arena
    (∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z w : ℂ,
      star (latitude t z) ⬝ᵥ latitude t w =
        ((1 - t : ℝ) : ℂ) + (t : ℂ) * star z * w) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨latitude_dot, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change star (0 : ℂ) ≠ star 1
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot)
    (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot.star
  realizationName :=
    `Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => star z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BargmannImaginaryMaximizers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot
