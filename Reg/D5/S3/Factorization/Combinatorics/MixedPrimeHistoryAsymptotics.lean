import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
import Reg.Support.SingleDependentReadout

noncomputable section
namespace Reg.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
open _root_.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
open _root_.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private theorem one_weight_positive : 0 < weightedCount 1 1 := by
  obtain ⟨ρ, C, R, K, l, u, hρ, _, _, _, _, hl, _, _, _, _, hb⟩ := result 1 (by norm_num)
  exact (div_pos hl (pow_pos hρ 1)).trans_le (hb 1 le_rfl).1

namespace GlobalBound
abbrev signature : Signature where
  Params := ℝ × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => weightedCount p.1 n * p.2 ^ n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (n : ℝ)) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law O := ∀ (t r : ℝ), 0 < t → 0 < r → r < 1 → t * primeSeries r < 1 →
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, O.readout () (t, r) n ≤ B
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, C, R, K, l, u, hρ, hρR, hR, _, _, _, _, hroot, _⟩ := result 1 (by norm_num)
  have hP : primeSeries ρ = 1 := by simpa using hroot
  obtain ⟨B, _, hB⟩ := h (1 / 2) ρ (by norm_num) hρ (hρR.trans hR) (by rw [hP]; norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact (not_le_of_gt hn) (hB n)
def family : Registration arena (type_of% subcritical_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨subcritical_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj; exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨((1, 1) : ℝ × ℝ), (0 : ℕ), (1 : ℕ), ?_⟩
    change weightedCount 1 0 * (1 : ℝ) ^ 0 ≠ weightedCount 1 1 * (1 : ℝ) ^ 1
    have hz : weightedCount 1 0 = 0 := by simp [weightedCount]
    intro he
    have hbad : (0 : ℝ) = weightedCount 1 1 := by
      calc
        _ = weightedCount 1 0 * (1 : ℝ) ^ 0 := by rw [hz]; ring
        _ = weightedCount 1 1 * (1 : ℝ) ^ 1 := he
        _ = _ := by ring
    exact one_weight_positive.ne hbad

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@subcritical_bound) (Realization signature) Unit Unit where
  unitName := `MixedPrimeHistoryAsymptotics.subcritical_bound.__information_unit
  realizationName := `Reg.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics.GlobalBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => weightedCount p.1 n * p.2 ^ n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
    definition := none
    coordinates := #[0, 1]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
      "arg", "body", "arg", "body", "fn", "arg"], stateBinder := 7, functionOperand := false,
                    stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GlobalBound

namespace Asymptotic
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t n => weightedCount t n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)
/-- The complete source is retained; the lower bound's endpoint weight is the observation. -/
def arena : Arena where
  signature := signature
  Law O := ∀ (t : ℝ), 0 < t →
    ∃ ρ C R K cLow cHigh : ℝ, 0 < ρ ∧ ρ < R ∧ R < 1 ∧ 0 < C ∧ 0 < K ∧
      0 < cLow ∧ cLow ≤ cHigh ∧ t * primeSeries ρ = 1 ∧
      (∀ σ : ℝ, 0 < σ → σ < 1 → t * primeSeries σ = 1 → σ = ρ) ∧
      (∀ n : ℕ, |weightedCount t n - C / ρ ^ n| ≤ K / R ^ n) ∧
      ∀ n : ℕ, 1 ≤ n → cLow / ρ ^ n ≤ O.readout () t n ∧
        weightedCount t n ≤ cHigh / ρ ^ n
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ, C, R, K, l, u, hρ, _, _, _, _, hl, _, _, _, _, hb⟩ := h 1 (by norm_num)
  exact (not_le_of_gt (div_pos hl (pow_pos hρ 1))) (hb 1 le_rfl).1
def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj; exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (0 : ℕ), (1 : ℕ), ?_⟩
    change weightedCount 1 0 ≠ weightedCount 1 1
    have hz : weightedCount 1 0 = 0 := by simp [weightedCount]
    simpa only [hz, pow_zero, pow_one, mul_one] using one_weight_positive.ne

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `MixedPrimeHistoryAsymptotics.result.__information_unit
  realizationName := `Reg.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics.Asymptotic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ t n => weightedCount t n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg", "body", "arg", "body",
      "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg",
      "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "body",
      "fn", "arg", "arg"], stateBinder := 8, functionOperand := false,
                    stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Asymptotic
end Reg.D5.S3.Factorization.Combinatorics.MixedPrimeHistoryAsymptotics
