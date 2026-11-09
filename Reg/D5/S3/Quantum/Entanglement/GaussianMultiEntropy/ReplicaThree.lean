import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
import Reg.Support.SingleDependentReadout

/-! Source-bound audit attempts for the integral-defined order-three family. -/

namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree

open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropyAsymptotic
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p a => GM3 3 p.1 p.2.1 p.2.2 a) (fun e => nomatch e)

def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, 1, 2, ?_⟩
  have h := (GM3_three_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    (show (1 : ℝ) ∈ Set.Ici 1 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 1 by norm_num) (by norm_num)
  exact ne_of_gt h

abbrev closedArena : Arena where
  signature := signature
  Law R := ∀ (A B C : ℕ) (a : ℝ), 0 < A → 0 < B → 0 < C → 1 ≤ a →
    R.readout () ⟨A, B, C⟩ a =
      Real.log ((1 + kappa (A + B + C) a * pairSum A B C) ^ 2 /
        (cut (kappa (A + B + C) a) A B C *
          cut (kappa (A + B + C) a) B A C *
          cut (kappa (A + B + C) a) C A B)) / 12

private theorem closed_rejected : ¬ closedArena.Law oneReadout := by
  intro h
  have he := h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [oneReadout, realize, cut, kappa] at he

def closedFamily : Registration closedArena (type_of% @GM3_three_closed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨GM3_three_closed, oneReadout, closed_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    closedArena.Law actual oneReadout closed_rejected
  dependence := actual_dependence

abbrev behaviorArena : Arena where
  signature := signature
  Law R := ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
    GM3 3 A B C 1 = 0 ∧
      StrictAntiOn (R.readout () ⟨A, B, C⟩) (Set.Ici 1) ∧
        ∀ a : ℝ, 1 < a → GM3 3 A B C a < 0

private theorem behavior_rejected : ¬ behaviorArena.Law zeroReadout := by
  intro h
  have he := (h 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    (show (1 : ℝ) ∈ Set.Ici 1 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 1 by norm_num) (by norm_num)
  norm_num [zeroReadout, realize] at he

def behaviorFamily : Registration behaviorArena (type_of% @GM3_three_behavior) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨GM3_three_behavior, zeroReadout, behavior_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    behaviorArena.Law actual zeroReadout behavior_rejected
  dependence := actual_dependence

def closedAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@GM3_three_closed) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.closedUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.closedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨closedArena⟩
  objectArena := .source ⟨closedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closedArena ⟨closedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => GM3 3 p.1 p.2.1 p.2.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def behaviorAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@GM3_three_behavior) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.behaviorUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.behaviorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨behaviorArena⟩
  objectArena := .source ⟨behaviorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source behaviorArena ⟨behaviorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => GM3 3 p.1 p.2.1 p.2.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms closedAudit
#print axioms behaviorAudit

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree
