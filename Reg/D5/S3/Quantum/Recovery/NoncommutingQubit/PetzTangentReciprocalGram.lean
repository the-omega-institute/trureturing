import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the marginal-dependent coefficient in the paired parity estimate. -/

namespace Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzTangentReciprocalGram
open MeasureTheory Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Replace only the multiplier and keep both original parity integrals and all hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (g β δ : ℝ) (a b c d : ℂ)
    (_hg : 0 < g) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hgb : g^2+β^2 ≤ 1),
    Complex.normSq ((g : ℂ)*(a+b)+(β : ℂ)*(c+d)) ≤ R.readout () () δ *
      ((∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*evenComplexEnergy δ a b t) +
        (∫ t in Ioi (0:ℝ), Real.sqrt (1+t)*oddComplexEnergy g δ c d t))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law 1 0 1 1 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at h

def source_registration : Registration arena (type_of% @paired_parity_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨paired_parity_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (1/2 : ℝ), ?_⟩
    change parityMultiplier 1 ≠ parityMultiplier (1/2)
    norm_num [parityMultiplier]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentReciprocalGram.paired_parity_bound)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ δ => parityMultiplier δ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram
