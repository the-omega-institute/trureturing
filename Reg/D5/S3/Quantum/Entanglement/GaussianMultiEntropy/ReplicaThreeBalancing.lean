import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
import Reg.Support.SingleDependentReadout

/-! Faithful source-bound audit of strict pair mixing, including its equality clause. -/

namespace Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing

open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar
open _root_.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p k =>
    value k ((1 - p.2.2.2) * p.1 + p.2.2.2 * p.2.1)
      (p.2.2.2 * p.1 + (1 - p.2.2.2) * p.2.1) p.2.2.1) (fun e => nomatch e)

def oneReadout : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1, 0⟩, 1, 2, ?_⟩
  have h := (parameter_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)).2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ici 0 by norm_num) (by norm_num)
  simpa [actual, realize] using ne_of_gt h

abbrev mixingArena : Arena where
  signature := signature
  Law R := ∀ k x y z t : ℝ, 0 < k → 0 < x → 0 < y → 0 < z → 0 ≤ t → t ≤ 1 →
    R.readout () ⟨x, y, z, t⟩ k ≤ value k x y z ∧
      (value k ((1 - t) * x + t * y) (t * x + (1 - t) * y) z = value k x y z ↔
        t = 0 ∨ t = 1 ∨ x = y)

private theorem mixing_rejected : ¬ mixingArena.Law oneReadout := by
  intro h
  have he := (h 1 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).1
  have hn := value_neg 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change 1 ≤ value 1 1 1 1 at he
  linarith

def mixingFamily : Registration mixingArena (type_of% @pair_mixing) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pair_mixing, oneReadout, mixing_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    mixingArena.Law actual oneReadout mixing_rejected
  dependence := actual_dependence

def mixingAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_mixing) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing.mixingUnit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing.mixingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨mixingArena⟩
  objectArena := .source ⟨mixingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mixingArena ⟨mixingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k =>
    value k ((1 - p.2.2.2) * p.1 + p.2.2.2 * p.2.1)
      (p.2.2.2 * p.1 + (1 - p.2.2.2) * p.2.1) p.2.2.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
    definition := none
    coordinates := #[1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms mixingAudit

end
end Reg.D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing
