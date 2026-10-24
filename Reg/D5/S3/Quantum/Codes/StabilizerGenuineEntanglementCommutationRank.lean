import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
import Reg.Support.DependentFamily

/-! Source-bound audit of the commutation-rank lower-bound threshold. -/

namespace Reg.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

open _root_.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the required rank threshold as the field characteristic varies. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N p => (N - 1 + (p - 2)) / (p - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain every original parameter, stabilizer hypothesis and entanglement hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (N p k : ℕ), 1 ≤ N → ∀ hp : Nat.Prime p,
    ∀ G : Fin k → PauliWord N p,
      @IsStabilizer N p k ⟨hp.ne_zero⟩ G →
      @genuinelyEntangled N p k ⟨hp.ne_zero⟩ G →
      r.readout () N p ≤ Module.finrank (ZMod p) (@commutationSpace N p k ⟨hp⟩ G)

private def emptyGenerators : Fin 0 → PauliWord 1 2 := Fin.elim0

private theorem empty_stabilizer : IsStabilizer emptyGenerators := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro A hA c hc
    have hbot : generatedOperators emptyGenerators = ⊥ := by
      simp [generatedOperators, emptyGenerators, Set.range_eq_empty]
    have hAone : A = 1 := by simpa [hbot] using hA
    have he := congrArg (fun M : Matrix (Fin 1 → ZMod 2) (Fin 1 → ZMod 2) ℂ =>
      M (fun _ => 0) (fun _ => 0)) (hAone.symm.trans hc)
    simpa using he.symm

private theorem empty_entanglement : genuinelyEntangled emptyGenerators := by
  intro ψ _ _ Q hQ hQc
  obtain ⟨a, ha⟩ := hQ
  obtain ⟨b, hb⟩ := hQc
  have hab : a = b := Subsingleton.elim _ _
  exact (hb (hab ▸ ha)).elim

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 2 0 (by norm_num) Nat.prime_two emptyGenerators
    empty_stabilizer empty_entanglement
  have hz : @commutationSpace 1 2 0 ⟨Nat.prime_two⟩ emptyGenerators = ⊥ := by
    simp [commutationSpace, Set.range_eq_empty]
  change 1 ≤ Module.finrank (ZMod 2) _ at hbad
  rw [hz, finrank_bot] at hbad
  omega

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 2, 3, ?_⟩
  change (3 - 1 + (2 - 2)) / (2 - 1) ≠ (3 - 1 + (3 - 2)) / (3 - 1)
  norm_num

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
      (@_root_.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ N p => (N - 1 + (p - 2)) / (p - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
    definition := some {
      owner := `D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
      name := `D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank
