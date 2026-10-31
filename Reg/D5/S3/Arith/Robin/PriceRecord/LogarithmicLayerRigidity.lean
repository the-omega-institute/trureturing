import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
import Reg.Support.DependentFamily

/-! Source-bound audit of prime capacity in shrinking relative windows. -/

open _root_.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The observation selects only the threshold in `T ≤ x`. All cardinalities,
prime predicates, interval endpoints, and the positive threshold stay literal. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ x : ℝ,
    R.readout () () T ≤ x → ∀ N : ℕ, N ≤ ⌈C * Real.log x ^ 3⌉₊ →
    ∃ D U : Finset ℕ, D.card = N ∧ U.card = N ∧
      (∀ p ∈ D, p.Prime ∧ x * (1 - 1 / Real.log x ^ 3) < (p : ℝ) ∧
        (p : ℝ) ≤ x) ∧
      (∀ q ∈ U, q.Prime ∧ x < (q : ℝ) ∧
        (q : ℝ) ≤ x * (1 + 1 / Real.log x ^ 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := 2 / Real.log (2 : ℝ) ^ 3
  have hC : 0 < C := div_pos (by norm_num) (pow_pos hlog 3)
  obtain ⟨T, _, hT⟩ := h C hC
  have hN : 2 ≤ ⌈C * Real.log (2 : ℝ) ^ 3⌉₊ := by
    have heq : C * Real.log (2 : ℝ) ^ 3 = 2 := by
      dsimp [C]
      field_simp
    rw [heq]
    norm_num
  obtain ⟨D, U, hDcard, _, hD, _⟩ := hT 2 (by change (0 : ℝ) ≤ 2; norm_num) 2 hN
  have hsub : D ⊆ {2} := by
    intro p hp
    have hp0 := (hD p hp).1.two_le
    have hp1 : p ≤ 2 := by exact_mod_cast (hD p hp).2.2
    simpa only [Finset.mem_singleton] using (show p = 2 by omega)
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_singleton, hDcard] at hcard
  omega

def family : Registration arena (type_of% @shrinking_prime_windows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shrinking_prime_windows, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@shrinking_prime_windows) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.shrinking_prime_windows.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
