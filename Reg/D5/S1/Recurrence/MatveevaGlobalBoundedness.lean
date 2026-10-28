import D5.S1.Recurrence.MatveevaGlobalBoundedness
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S1.Recurrence.MatveevaGlobalBoundedness
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.MatveevaGlobalBoundedness
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℚ, Σ _ : ℚ, Σ _ : ℚ, Σ _ : ℚ, Σ _ : ℚ, ℕ → ℚ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p n => ((n : ℚ) + p.2.2.1) * p.2.2.2.2.2 n +
    (p.1 * (n : ℚ) + p.2.2.2.1) * p.2.2.2.2.2 (n - 1) +
    (p.2.1 * (n : ℚ) + p.2.2.2.2.1) * p.2.2.2.2.2 (n - 2))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ¬ (∀ a1 a2 b0 b1 b2 : ℚ,
    a1 ≠ 0 → a2 ≠ 0 →
    (∀ n : ℕ, 2 ≤ n → b0 ≠ -(n : ℚ)) →
    ∀ s : ℕ → ℚ,
      (∀ n : ℕ, 2 ≤ n → r.readout () ⟨a1,a2,b0,b1,b2,s⟩ n = 0) →
      a1 * a2 * b0 + a1 * b2 - 2 * a2 * b1 ≠ 0 → ¬ globallyBounded s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro a1 a2 b0 b1 b2 ha1 ha2 hb0 s hs hE
  have htwo := hs 2 (by decide)
  norm_num [rejected, realize] at htwo

def evidence : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,1,0,0,0,fun _ => 1⟩,0,1,?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S1.Recurrence.MatveevaGlobalBoundedness.result)
    (Realization signature) Type Unit := {
  unitName := `D5.S1.Recurrence.MatveevaGlobalBoundedness.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.MatveevaGlobalBoundedness.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p n => ((n : ℚ) + p.2.2.1) * p.2.2.2.2.2 n +
      (p.1 * (n : ℚ) + p.2.2.2.1) * p.2.2.2.2.2 (n - 1) +
      (p.2.1 * (n : ℚ) + p.2.2.2.2.1) * p.2.2.2.2.2 (n - 2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S1.Recurrence.MatveevaGlobalBoundedness
    definition := some {
      owner := `D5.S1.Recurrence.MatveevaGlobalBoundedness
      name := `D5.S1.Recurrence.MatveevaGlobalBoundedness.claim
      path := #["arg"] }
    coordinates := #[0,1,2,3,4,8]
    readouts := #[{
      path := #["arg","body","body","body","body","body","body","body","body","body","domain","body","body","fn","arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms audit
end
end Reg.D5.S1.Recurrence.MatveevaGlobalBoundedness
