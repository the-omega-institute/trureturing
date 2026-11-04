import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the labelled bubble count as a function of energy. -/

namespace Reg.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
open _root_.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the labelled bubble count as the integer energy varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℤ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ L E => bubbleCount L E) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete counting claim, with its bubble-count occurrence replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ L : ℕ, 5 ≤ L → ∀ E : ℤ,
    (R.readout () L E : ℤ) = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        ((L * (L - 4 * n - 1).choose (n - 1) / n : ℕ) : ℤ) *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            (n.choose (((n : ℤ) + E) / 2).toNat : ℤ) else 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 5 (by decide) 1
  norm_num [rejected, realize, Finset.sum_Icc_succ_top] at he

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨5, 1, 2, ?_⟩
  change bubbleCount 5 1 ≠ bubbleCount 5 2
  have hOne := result 5 (by decide) 1
  have hTwo := result 5 (by decide) 2
  norm_num [Finset.sum_Icc_succ_top] at hOne hTwo
  intro he
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) he
  omega

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L E => bubbleCount L E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
    definition := some {
      owner := `D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
      name := `D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
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
end Reg.D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
