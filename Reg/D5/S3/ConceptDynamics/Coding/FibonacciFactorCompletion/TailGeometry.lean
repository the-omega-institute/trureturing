import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
noncomputable section

abbrev suffixSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : List Label, ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def suffixActual : Realization suffixSignature :=
  realize suffixSignature (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e)

def suffixRejected : Realization suffixSignature :=
  realize suffixSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev suffixArena : Arena.{0,0,0,0,0} where
  signature := suffixSignature
  Law r := ∀ (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (z : ℝ) (hz : InSupport e z) (p : ℕ), InSupport .G0 (r.readout () ⟨w, z⟩ p)

/-- The legal one-letter word and supported zero also admit states beyond its length. -/
theorem suffix_rejected_law : ¬ suffixArena.Law suffixRejected := by
  intro h
  have supported : InSupport .G0 0 := by
    constructor
    · norm_num
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le
  have hh := h .G0 .G0 [Label.L2] rfl 0 supported 2
  have hlo := hh.1
  norm_num [suffixRejected, realize] at hlo

def suffixRegistration : Registration suffixArena (type_of% @suffix_supported) where
  actual := suffixActual
  bridge := Iff.rfl
  variation := ⟨@suffix_supported, suffixRejected, suffix_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    suffixArena.Law suffixActual suffixRejected suffix_rejected_law
  dependence := by
    intro i
    refine ⟨⟨[Label.L2], 0⟩, 0, 1, ?_⟩
    norm_num [suffixActual, realize, compose, branch, shift]

def suffix_supported_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffix_supported)
      (type_of% (realize.{0,0,0,0,0} suffixSignature
        (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffix_supported_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry.suffixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨suffixArena⟩
  objectArena := .source ⟨suffixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source suffixArena ⟨suffixRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} suffixSignature
    (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms suffixRegistration
#print axioms suffix_supported_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
