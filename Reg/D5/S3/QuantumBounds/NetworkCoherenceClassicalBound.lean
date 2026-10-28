import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp classical network coherence bound. -/

namespace Reg.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound

open _root_.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
open _root_.D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)
open _root_.D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy (windowLaw)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Parameters retain the dimension, mixture weight, and both product laws. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ _ : ℝ, Σ _ : Fin n → Bool → ℝ, Fin n → Bool → ℝ
  State t := Fin t.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ t a => classicalMixture t.1 t.2.1 t.2.2.1 t.2.2.2 a)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The observation replaces the mixture within the complete sharp-bound statement. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 2 ≤ n →
    IsGreatest {c : ℝ | ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ p q : Fin n → Bool → ℝ,
      (∀ i, Probability (p i)) ∧ (∀ i, Probability (q i)) ∧
        c = coherenceMerit n (r.readout () ⟨n, γ, p, q⟩)} (1 / 4)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨γ, hγ, p, q, hp, hq, heq⟩ := (h 2 (by norm_num)).1
  norm_num [rejected, realize, coherenceMerit] at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1, (fun _ b => if b then 0 else 1),
    (fun _ b => if b then 0 else 1)⟩, (fun _ => false), (fun _ => true), ?_⟩
  norm_num [actual, realize, classicalMixture, windowLaw]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound.unit
  realizationName :=
    `Reg.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ t a => classicalMixture t.1 t.2.1 t.2.2.1 t.2.2.2 a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
    definition := some {
      owner := `D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
      name := `D5.S3.QuantumBounds.NetworkCoherenceClassicalBound.claim
      path := #[] }
    coordinates := #[0, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
