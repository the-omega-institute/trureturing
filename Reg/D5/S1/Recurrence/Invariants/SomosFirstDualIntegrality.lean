import D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The observation is the candidate orbit in the source exchange predicate. -/

namespace Reg.D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality

open _root_.D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit TrivSqZeroExt

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, Fin 4 → ℤ
  State _ := ℕ → DualNumber ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → DualNumber ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : ℕ) (c : Fin 4 → ℤ) (_hp : 0 < p) (_hq : 0 < q),
    ∃ A : ℕ → DualNumber ℚ,
      IsOrbit p q c (R.readout () ⟨p, q, c⟩ A) ∧
      (∀ X, IsOrbit p q c X → X = A) ∧
      (∀ n, 0 < (A n).fst) ∧
      ((∀ n, ∃ b : ℤ, (b : ℚ) = (A n).snd) ↔ p = 1) ∧
      (∀ B, IsRealOrbit p q c B ↔ B = fun n => realCast (A n)) ∧
      ((∀ n, ∃ b : ℤ, (b : ℝ) = (realCast (A n)).snd) ↔ p = 1) ∧
      Function.Injective realCast

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, _⟩ := h 1 1 (fun _ => 0) (by decide) (by decide)
  have he := congrArg (fst (R := ℚ) (M := ℚ)) (hA.1 ⟨0, by decide⟩)
  norm_num [rejected, realize] at he

def family : Registration arena (type_of% result) where
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
    refine ⟨⟨1, 1, fun _ => 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    intro he
    have h := congrArg (fun f : ℕ → DualNumber ℚ => (f 0).fst) he
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Invariants.SomosFirstDualIntegrality
