import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ReciprocalGammaTuran.Defs
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs
open _root_.D5.S3.Analytic.ReciprocalGammaTuran.Defs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => rgamma x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (-(n : ℝ)) = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, rgamma, Real.Gamma_zero, Real.Gamma_one]
def family : Registration arena (type_of% @rgamma_neg_nat) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rgamma_neg_nat, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rgamma_neg_nat) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs.Poles.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => rgamma x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Defs
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
namespace UnitSequence
attribute [local instance] Classical.propDecidable
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ g => decide (AdmissibleSeq g)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := R.readout () () (fun _ => 1) = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  cases h
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hz : ¬ AdmissibleSeq (fun _ => 0) := by
    intro hgood
    obtain ⟨n, hn⟩ := hgood.1
    exact hn rfl
  simp [actual, realize, hz, admissible_one] at he

def family : Registration arena (type_of% @admissible_one) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using admissible_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@admissible_one) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs.UnitSequence.unit
  realizationName := `Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs.UnitSequence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g => decide (AdmissibleSeq g)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ReciprocalGammaTuran.Defs
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end UnitSequence
end
end Reg.D5.S3.Analytic.ReciprocalGammaTuran.Defs
