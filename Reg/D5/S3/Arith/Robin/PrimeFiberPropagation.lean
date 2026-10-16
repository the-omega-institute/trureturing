import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PrimeFiberPropagation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.PrimeFiberPropagation

open _root_.D5.S3.Arith.Robin.PrimeFiberPropagation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- One role: the normalized divisor sum read at a natural number. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Each arena varies exactly the divisor-ratio occurrence in the conclusion; every other
occurrence keeps its actual value. -/
abbrev edgeArena : Arena where
  signature := signature
  Law R := ∀ {n m : ℕ}, 1 < n → 0 < m → RobinAt n → EdgeTest n m →
    R.readout () () (n * m) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * m : ℕ) : ℝ))

abbrev fibreArena : Arena where
  signature := signature
  Law R := ∀ {n q : ℕ}, q.Prime → 3 ≤ Real.log n → EdgeTest n q → ∀ k : ℕ,
    (R.readout () () (n * q ^ k * q) / divisorRatio (n * q ^ k) - 1) *
        Real.log (Real.log ((n * q ^ k : ℕ) : ℝ)) ≤
      Real.log (1 + Real.log (q : ℝ) / Real.log ((n * q ^ k : ℕ) : ℝ))

abbrev robinFibreArena : Arena where
  signature := signature
  Law R := ∀ {n q : ℕ}, q.Prime → 3 ≤ Real.log n → RobinAt n → EdgeTest n q → ∀ k : ℕ,
    R.readout () () (n * q ^ k) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * q ^ k : ℕ) : ℝ))

abbrev replaceArena : Arena where
  signature := signature
  Law R := ∀ {p q a m : ℕ}, p.Prime → q.Prime → p ≤ q → ¬ p ∣ m → ¬ q ∣ m →
    RobinAt (p ^ a * m) →
      R.readout () () (q ^ a * m) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((q ^ a * m : ℕ) : ℝ))

def actual : Realization signature :=
  realize signature (fun _ _ n => divisorRatio n) (fun e => nomatch e)

/-- The constant readout `100` replaces the divisor ratio at the selected occurrence. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 100) (fun e => nomatch e)

private theorem log_two_bounds : 0.69 < Real.log 2 ∧ Real.log 2 < 0.7 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> linarith

private theorem log_pow_two (k : ℕ) : Real.log ((2 ^ k : ℕ) : ℝ) = k * Real.log 2 := by
  push_cast
  rw [Real.log_pow]

private theorem exp_gamma_bounds :
    1 ≤ Real.exp Real.eulerMascheroniConstant ∧ Real.exp Real.eulerMascheroniConstant < 3 := by
  have h0 := Real.one_half_lt_eulerMascheroniConstant
  have h1 := Real.eulerMascheroniConstant_lt_two_thirds
  constructor
  · exact Real.one_le_exp (by linarith)
  · calc Real.exp Real.eulerMascheroniConstant < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
      _ < 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith

/-- `2 < log log 2^k < k` for `k ≥ 20`. -/
private theorem loglog_pow_two {k : ℕ} (hk : 20 ≤ k) :
    2 < Real.log (Real.log ((2 ^ k : ℕ) : ℝ)) ∧
      Real.log (Real.log ((2 ^ k : ℕ) : ℝ)) < k := by
  rw [log_pow_two]
  have hb := log_two_bounds
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) * Real.log 2 := by nlinarith
  constructor
  · rw [Real.lt_log_iff_exp_lt hpos]
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]
    have h1 := Real.exp_pos 1
    norm_num at he
    nlinarith
  · have := Real.log_le_sub_one_of_pos hpos
    nlinarith

private theorem sigma_pow_two (a : ℕ) :
    (ArithmeticFunction.sigma 1 (2 ^ a) : ℝ) = 2 ^ (a + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  push_cast
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

private theorem divisorRatio_pow_two (a : ℕ) :
    divisorRatio (2 ^ a) = 2 - 1 / 2 ^ a := by
  unfold divisorRatio
  rw [sigma_pow_two]
  push_cast
  field_simp
  ring

private theorem log20 : 3 ≤ Real.log ((2 ^ 20 : ℕ) : ℝ) := by
  rw [log_pow_two]
  have := log_two_bounds
  push_cast
  linarith

private theorem robin20 : RobinAt (2 ^ 20) := by
  unfold RobinAt
  rw [divisorRatio_pow_two]
  have hl := (loglog_pow_two (k := 20) le_rfl).1
  have hg := exp_gamma_bounds
  have hp : (0 : ℝ) < 1 / 2 ^ 20 := by positivity
  have hm := mul_le_mul hg.1 hl.le (by norm_num) (by linarith)
  norm_num at hm ⊢
  linarith

private theorem edge20 : EdgeTest (2 ^ 20) 2 := by
  unfold EdgeTest
  have hmul : (2 ^ 20 * 2 : ℕ) = 2 ^ 21 := by norm_num
  rw [hmul, divisorRatio_pow_two, divisorRatio_pow_two]
  have hl := loglog_pow_two (k := 20) le_rfl
  have hlog := log_pow_two 20
  have hb := log_two_bounds
  have hx : Real.log ((2 : ℕ) : ℝ) / Real.log ((2 ^ 20 : ℕ) : ℝ) = 1 / 20 := by
    rw [hlog]
    push_cast
    field_simp
  rw [hx]
  have hr := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 20)
  have hc : (2 - 1 / 2 ^ 21 : ℝ) / (2 - 1 / 2 ^ 20) - 1 = 1 / (2 ^ 22 - 2) := by
    field_simp
    ring
  rw [hc]
  push_cast at hl
  have hpos : (0 : ℝ) < 1 / (2 ^ 22 - 2) := by norm_num
  norm_num at hr ⊢
  nlinarith

theorem edge_rejected_law : ¬ edgeArena.Law rejected := by
  intro h
  have hbad := h (n := 2 ^ 20) (m := 2) (by norm_num) (by norm_num) robin20 edge20
  change (100 : ℝ) < Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log ((2 ^ 20 * 2 : ℕ) : ℝ)) at hbad
  rw [show (2 ^ 20 * 2 : ℕ) = 2 ^ 21 by norm_num] at hbad
  have hl := (loglog_pow_two (k := 21) (by norm_num)).2
  have hl0 := (loglog_pow_two (k := 21) (by norm_num)).1
  have hg := exp_gamma_bounds
  have hm := mul_lt_mul'' hg.2 hl (by linarith) (by linarith)
  norm_num at hm hbad
  linarith

theorem fibre_rejected_law : ¬ fibreArena.Law rejected := by
  intro h
  have hbad := h (n := 2 ^ 20) (q := 2) Nat.prime_two log20 edge20 0
  change ((100 : ℝ) / divisorRatio (2 ^ 20 * 2 ^ 0) - 1) *
      Real.log (Real.log ((2 ^ 20 * 2 ^ 0 : ℕ) : ℝ)) ≤
    Real.log (1 + Real.log ((2 : ℕ) : ℝ) / Real.log ((2 ^ 20 * 2 ^ 0 : ℕ) : ℝ)) at hbad
  rw [show (2 ^ 20 * 2 ^ 0 : ℕ) = 2 ^ 20 by norm_num, divisorRatio_pow_two] at hbad
  have hl := (loglog_pow_two (k := 20) le_rfl).1
  have hlog := log_pow_two 20
  have hb := log_two_bounds
  have hx : Real.log ((2 : ℕ) : ℝ) / Real.log ((2 ^ 20 : ℕ) : ℝ) = 1 / 20 := by
    rw [hlog]
    push_cast
    field_simp
  rw [hx] at hbad
  have hr : Real.log (1 + 1 / 20) ≤ 1 / 20 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 1 / 20)
    linarith
  have hq : (49 : ℝ) ≤ 100 / (2 - 1 / 2 ^ 20) - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num)]
    norm_num
  have hm := mul_le_mul hq hl.le (by norm_num) (by linarith)
  linarith

theorem robin_fibre_rejected_law : ¬ robinFibreArena.Law rejected := by
  intro h
  have hbad := h (n := 2 ^ 20) (q := 2) Nat.prime_two log20 robin20 edge20 0
  change (100 : ℝ) < Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log ((2 ^ 20 * 2 ^ 0 : ℕ) : ℝ)) at hbad
  rw [show (2 ^ 20 * 2 ^ 0 : ℕ) = 2 ^ 20 by norm_num] at hbad
  have hl := (loglog_pow_two (k := 20) le_rfl).2
  have hl0 := (loglog_pow_two (k := 20) le_rfl).1
  have hg := exp_gamma_bounds
  have hm := mul_lt_mul'' hg.2 hl (by linarith) (by linarith)
  norm_num at hm hbad
  linarith

theorem replace_rejected_law : ¬ replaceArena.Law rejected := by
  intro h
  have hR : RobinAt (2 ^ 20 * 1) := by simpa using robin20
  have hbad := h (p := 2) (q := 3) (a := 20) (m := 1) Nat.prime_two Nat.prime_three
    (by norm_num) (by norm_num) (by norm_num) hR
  change (100 : ℝ) < Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log ((3 ^ 20 * 1 : ℕ) : ℝ)) at hbad
  have hg := exp_gamma_bounds
  have h3 : Real.log ((3 ^ 20 * 1 : ℕ) : ℝ) = 20 * Real.log 3 := by
    rw [show ((3 ^ 20 * 1 : ℕ) : ℝ) = (3 : ℝ) ^ 20 by push_cast; ring, Real.log_pow]
    norm_num
  have hl3 : Real.log 3 < 1.4 := by
    have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4' : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := log_two_bounds
    linarith
  have hl3' : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpos : 0 < 20 * Real.log 3 := by positivity
  have hll : Real.log (Real.log ((3 ^ 20 * 1 : ℕ) : ℝ)) < 28 := by
    rw [h3]
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hl31 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have hm := mul_lt_mul'' hg.2 hll (by linarith) (by
    rw [h3]
    exact Real.log_nonneg (by linarith))
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change divisorRatio 1 ≠ divisorRatio 2
  have h1 := divisorRatio_pow_two 0
  have h2 := divisorRatio_pow_two 1
  norm_num at h1 h2
  rw [h1, h2]
  norm_num

def edgeRegistration : Registration edgeArena
    (∀ {n m : ℕ}, 1 < n → 0 < m → RobinAt n → EdgeTest n m →
      divisorRatio (n * m) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * m : ℕ) : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robinAt_mul_of_edgeTest, rejected, edge_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), edge_rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def fibreRegistration : Registration fibreArena
    (∀ {n q : ℕ}, q.Prime → 3 ≤ Real.log n → EdgeTest n q → ∀ k : ℕ,
      (divisorRatio (n * q ^ k * q) / divisorRatio (n * q ^ k) - 1) *
          Real.log (Real.log ((n * q ^ k : ℕ) : ℝ)) ≤
        Real.log (1 + Real.log (q : ℝ) / Real.log ((n * q ^ k : ℕ) : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@edgeTest_mul_prime_pow, rejected, fibre_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), fibre_rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def robinFibreRegistration : Registration robinFibreArena
    (∀ {n q : ℕ}, q.Prime → 3 ≤ Real.log n → RobinAt n → EdgeTest n q → ∀ k : ℕ,
      divisorRatio (n * q ^ k) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((n * q ^ k : ℕ) : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robinAt_mul_prime_pow, rejected, robin_fibre_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), robin_fibre_rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def replaceRegistration : Registration replaceArena
    (∀ {p q a m : ℕ}, p.Prime → q.Prime → p ≤ q → ¬ p ∣ m → ¬ q ∣ m →
      RobinAt (p ^ a * m) →
        divisorRatio (q ^ a * m) <
          Real.exp Real.eulerMascheroniConstant * Real.log (Real.log ((q ^ a * m : ℕ) : ℝ))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@robinAt_prime_replace, rejected, replace_rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), replace_rejected_law⟩, fun i => nomatch i⟩
  dependence := actual_dependence

def edgeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robinAt_mul_of_edgeTest)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PrimeFiberPropagation.robinAt_mul_of_edgeTest.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeFiberPropagation.edgeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨edgeArena⟩
  objectArena := .source ⟨edgeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source edgeArena ⟨edgeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PrimeFiberPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fibreAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@edgeTest_mul_prime_pow)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PrimeFiberPropagation.edgeTest_mul_prime_pow.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeFiberPropagation.fibreRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨fibreArena⟩
  objectArena := .source ⟨fibreArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fibreArena ⟨fibreRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PrimeFiberPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def robinFibreAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robinAt_mul_prime_pow)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PrimeFiberPropagation.robinAt_mul_prime_pow.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeFiberPropagation.robinFibreRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨robinFibreArena⟩
  objectArena := .source ⟨robinFibreArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source robinFibreArena ⟨robinFibreRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PrimeFiberPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def replaceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@robinAt_prime_replace)
    (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PrimeFiberPropagation.robinAt_prime_replace.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeFiberPropagation.replaceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨replaceArena⟩
  objectArena := .source ⟨replaceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source replaceArena ⟨replaceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => divisorRatio n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PrimeFiberPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms replaceRegistration
#print axioms edgeRegistration
#print axioms fibreRegistration
#print axioms robinFibreRegistration

abbrev positivityArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, n ≠ 0 → 0 < R.readout () () n

def positivityRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem positivity_rejected_law : ¬ positivityArena.Law positivityRejected := by
  intro h
  have hbad := h (n := 1) (by norm_num)
  norm_num [positivityRejected, realize] at hbad

def positivityFamily : Registration positivityArena (type_of% (@divisorRatio_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@divisorRatio_pos, positivityRejected, positivity_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨positivityRejected, ?_, rfl, positivity_rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def positivityAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@divisorRatio_pos)
    (type_of% (realize signature (fun _ _ n => divisorRatio n) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.Robin.PrimeFiberPropagation.divisorRatio_pos.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PrimeFiberPropagation.positivityFamily
  realizationSource := none
  generated := false
  arena := .source ⟨positivityArena⟩
  objectArena := .source ⟨positivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positivityArena ⟨positivityFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => divisorRatio n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PrimeFiberPropagation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms positivityFamily

end

end Reg.D5.S3.Arith.Robin.PrimeFiberPropagation
