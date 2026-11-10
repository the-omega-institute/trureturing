import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.TwoDeletionRunEntropyBounds
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the binary logarithm's strict rational bounds. -/

namespace Reg.D5.S3.Entropy.TwoDeletionRunEntropyBounds

open _root_.D5.S3.Entropy.TwoDeletionRunEntropyBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.logb 2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Vary the lower-bound logarithm coordinate while retaining both original clauses. -/
abbrev arena : Arena where
  signature := signature
  Law r := (3 : ℝ) / 2 < r.readout () () 3 ∧ Real.logb 2 3 < 5 / 3

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.1
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.logb 2 1 ≠ Real.logb 2 2
  norm_num [Real.logb_self_eq_one]

def source_registration : Registration arena (type_of% logb_three_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨logb_three_bounds, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Entropy.TwoDeletionRunEntropyBounds.logb_three_bounds)
      (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Entropy.TwoDeletionRunEntropyBounds.logb_three_bounds_unit
  realizationName := `Reg.D5.S3.Entropy.TwoDeletionRunEntropyBounds.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.logb 2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Entropy.TwoDeletionRunEntropyBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

set_option pp.proofs false in
#print _root_.D5.S3.Entropy.TwoDeletionRunEntropyBounds.logb_three_bounds

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Entropy.TwoDeletionRunEntropyBounds
