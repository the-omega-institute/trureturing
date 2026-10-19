/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedReturnCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded positive return lists are counted by their actual weighted middle words. -/

import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.OfMap
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion

/-- The half length of an execution word. -/
def halfWeight : List CuLetter → ℕ
  | [] => 0
  | .c :: w => 10 + halfWeight w
  | .u :: w => 3 + halfWeight w

/-- A finite enumeration of all words of the specified half length. -/
def middleWords (n : ℕ) : Finset (List CuLetter) :=
  (if n = 0 then {[]} else ∅) ∪
    ((if 3 ≤ n then (middleWords (n-3)).image (List.cons .u) else ∅) ∪
     (if 10 ≤ n then (middleWords (n-10)).image (List.cons .c) else ∅))
termination_by n

/-- The actual nonempty positive-return fiber, with no cap on either exponent. -/
def ReturnFiber (n : ℕ) := {xs : List Return // xs ≠ [] ∧ listWeight xs = 2*n}

noncomputable def returnCount (n : ℕ) : ℕ := Nat.card (ReturnFiber n)

private theorem weight_twice (w : List CuLetter) : wordWeight w = 2*halfWeight w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [wordWeight, halfWeight, ih] <;> omega

private theorem half_append (w v : List CuLetter) :
    halfWeight (w ++ v) = halfWeight w + halfWeight v := by
  induction w with
  | nil => simp [halfWeight]
  | cons a w ih => cases a <;> simp [halfWeight, ih, Nat.add_assoc]

private theorem middle_membership (n : ℕ) (w : List CuLetter) :
    w ∈ middleWords n ↔ halfWeight w = n := by
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rw [middleWords]
    by_cases hzero : n = 0
    · subst n
      simp only [if_pos rfl, if_neg (by omega : ¬3 ≤ 0), if_neg (by omega : ¬10 ≤ 0),
        Finset.union_empty, Finset.mem_singleton]
      cases w with
      | nil => simp [halfWeight]
      | cons a w => cases a <;> simp [halfWeight]
    · by_cases hthree : 3 ≤ n
      · by_cases hten : 10 ≤ n
        · simp only [if_neg hzero, if_pos hthree, if_pos hten, Finset.empty_union,
            Finset.mem_union, Finset.mem_image]
          cases w with
          | nil => simp [halfWeight, hzero, eq_comm]
          | cons a w =>
            cases a <;> simp [ih (n-3) (by omega), ih (n-10) (by omega), halfWeight] <;> omega
        · simp only [if_neg hzero, if_pos hthree, if_neg hten, Finset.empty_union,
            Finset.union_empty, Finset.mem_image]
          cases w with
          | nil => simp [halfWeight, hzero, eq_comm]
          | cons a w =>
            cases a <;> simp [ih (n-3) (by omega), halfWeight] <;> omega
      · simp only [if_neg hzero, if_neg hthree, if_neg (by omega : ¬10 ≤ n),
          Finset.union_empty, Finset.notMem_empty, false_iff]
        cases w with
        | nil => simpa [halfWeight, eq_comm] using hzero
        | cons a w => cases a <;> simp only [halfWeight] <;> omega

private theorem middle_card (n : ℕ) :
    Nat.card {w : List CuLetter // halfWeight w = n} = (middleWords n).card := by
  classical
  let e : {w : List CuLetter // halfWeight w = n} ≃ {w // w ∈ middleWords n} :=
    { toFun := fun w => ⟨w.val, (middle_membership n w.val).mpr w.property⟩
      invFun := fun w => ⟨w.val, (middle_membership n w.val).mp w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr e

private theorem execution_endpoints (xs : List Return) (hne : xs ≠ []) :
    ∃ w : List CuLetter, executionWord xs = .c :: (w ++ [.u]) := by
  have first : ∃ v, executionWord xs = .c :: v := by
    cases xs with
    | nil => contradiction
    | cons a xs =>
      obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero a.r_pos.ne'
      exact ⟨List.replicate r .c ++ List.replicate a.m .u ++ executionWord xs,
        by simp [executionWord, hr, List.replicate_succ, List.append_assoc]⟩
  have endNonempty (a : Return) (rest : List Return) :
      (executionWord (a :: rest)).getLast? = some CuLetter.u := by
    induction rest generalizing a with
    | nil => simp [executionWord, List.getLast?_replicate, a.m_pos.ne']
    | cons b rest ih =>
      simp only [executionWord, List.getLast?_append] at ih ⊢
      rw [ih]
      rfl
  have last : (executionWord xs).getLast? = some CuLetter.u := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact endNonempty a xs
  obtain ⟨v, hv⟩ := first
  cases v with
  | nil => simp [hv] at last
  | cons a v =>
    have hl : (a :: v).getLast? = some CuLetter.u := by simpa [hv] using last
    exact ⟨(a :: v).dropLast, by rw [hv, List.dropLast_append_getLast? _ hl]⟩

private theorem parse_endpoints (w : List CuLetter) :
    ∃ xs : List Return, xs ≠ [] ∧ executionWord xs = .c :: (w ++ [.u]) := by
  obtain ⟨⟨a, xs⟩, h, _⟩ := finite_run_decomposition (.c :: (w ++ [.u]))
    (Or.inr (by change (([CuLetter.c] ++ w) ++ [CuLetter.u]).getLast? = _; rw [List.getLast?_append]; rfl))
  have az : a = 0 := by
    cases a with
    | zero => rfl
    | succ a =>
      have he := congrArg (fun v : List CuLetter => v.head?) h
      simp [List.replicate_succ] at he
  have he : executionWord xs = .c :: (w ++ [.u]) := by simpa [az] using h.symm
  refine ⟨xs, ?_, he⟩
  intro hz
  simp [hz, executionWord] at he

private noncomputable def endpointEquiv (n : ℕ) :
    {w : List CuLetter // 13 + halfWeight w = n} ≃ ReturnFiber n := by
  classical
  let f : {w : List CuLetter // 13 + halfWeight w = n} → ReturnFiber n := fun w =>
    ⟨(parse_endpoints w.val).choose, (parse_endpoints w.val).choose_spec.1, by
      have he := (parse_endpoints w.val).choose_spec.2
      have hw := complete_execution_word_parser.2.2.2.1 (parse_endpoints w.val).choose
      rw [he, weight_twice, halfWeight, half_append] at hw
      simp only [halfWeight] at hw
      omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro w v h
    apply Subtype.ext
    have he := congrArg (fun x : ReturnFiber n => executionWord x.val) h
    change executionWord (parse_endpoints w.val).choose =
      executionWord (parse_endpoints v.val).choose at he
    rw [(parse_endpoints w.val).choose_spec.2, (parse_endpoints v.val).choose_spec.2] at he
    exact List.append_cancel_right (List.cons.inj he).2
  · intro xs
    obtain ⟨w, hw⟩ := execution_endpoints xs.val xs.property.1
    have hn : 13 + halfWeight w = n := by
      have he := complete_execution_word_parser.2.2.2.1 xs.val
      rw [hw, weight_twice, halfWeight, half_append] at he
      simp only [halfWeight] at he
      have := xs.property.2
      omega
    refine ⟨⟨w, hn⟩, ?_⟩
    apply Subtype.ext
    apply complete_execution_word_parser.2.2.1
    exact (parse_endpoints w).choose_spec.2.trans hw.symm

/-- The genuine list count equals the finite middle-word count, with the forced
endpoints contributing half length thirteen. Every fiber is finite. -/
theorem actual_count_middle (n : ℕ) :
    Finite (ReturnFiber n) ∧
      returnCount n = if 13 ≤ n then (middleWords (n-13)).card else 0 := by
  classical
  by_cases hn : 13 ≤ n
  · let e : {w : List CuLetter // halfWeight w = n-13} ≃
        {w : List CuLetter // 13 + halfWeight w = n} :=
      Equiv.subtypeEquivRight (fun w => by omega)
    letI : Fintype {w : List CuLetter // w ∈ middleWords (n-13)} := Finset.Subtype.fintype _
    letI : Finite {w : List CuLetter // halfWeight w = n-13} := by
      apply Finite.of_equiv {w : List CuLetter // w ∈ middleWords (n-13)}
      exact { toFun := fun w => ⟨w.val, (middle_membership _ _).mp w.property⟩
              invFun := fun w => ⟨w.val, (middle_membership _ _).mpr w.property⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
    letI : Finite (ReturnFiber n) := Finite.of_equiv _ (e.trans (endpointEquiv n))
    refine ⟨inferInstance, ?_⟩
    rw [returnCount, if_pos hn, ← Nat.card_congr (e.trans (endpointEquiv n)), middle_card]
  · have empty : IsEmpty {w : List CuLetter // 13 + halfWeight w = n} :=
      ⟨fun w => by have := w.property; omega⟩
    letI := empty
    letI : IsEmpty (ReturnFiber n) := ⟨fun x => isEmptyElim ((endpointEquiv n).symm x)⟩
    exact ⟨inferInstance, by simp [returnCount, hn]⟩

private theorem middle_recurrence (n : ℕ) :
    (middleWords n).card = (if 3 ≤ n then (middleWords (n-3)).card else 0) +
      (if 10 ≤ n then (middleWords (n-10)).card else 0) + (if n = 0 then 1 else 0) := by
  classical
  let Z : Finset (List CuLetter) := if n = 0 then {[]} else ∅
  let U : Finset (List CuLetter) := if 3 ≤ n then (middleWords (n-3)).image (List.cons .u) else ∅
  let C : Finset (List CuLetter) := if 10 ≤ n then (middleWords (n-10)).image (List.cons .c) else ∅
  have uc : Disjoint U C := by
    apply Finset.disjoint_left.mpr
    intro w hu hc
    dsimp [U, C] at hu hc
    split_ifs at hu hc <;> simp_all
    obtain ⟨v, hv, he⟩ := hu
    obtain ⟨t, ht, he'⟩ := hc
    have impossible := he.trans he'.symm
    cases impossible
  have zrest : Disjoint Z (U ∪ C) := by
    apply Finset.disjoint_left.mpr
    intro w hz hw
    dsimp [Z, U, C] at hz hw
    split_ifs at hz hw <;> simp_all
  rw [middleWords]
  change (Z ∪ (U ∪ C)).card = _
  rw [Finset.card_union_of_disjoint zrest, Finset.card_union_of_disjoint uc]
  dsimp [Z, U, C]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_empty,
    Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)]
  omega

/-- Deleting the first middle letter gives a disjoint partition of the actual
list fiber. Guards supply the zero extension without truncated-index artifacts. -/
theorem actual_count_recurrence (n : ℕ) :
    returnCount n = (if 3 ≤ n then returnCount (n-3) else 0) +
      (if 10 ≤ n then returnCount (n-10) else 0) + (if n = 13 then 1 else 0) := by
  rw [(actual_count_middle n).2, (actual_count_middle (n-3)).2,
    (actual_count_middle (n-10)).2]
  by_cases hn : 13 ≤ n
  · rw [if_pos hn, middle_recurrence]
    have e3 : n-13-3 = n-3-13 := by omega
    have e10 : n-13-10 = n-10-13 := by omega
    rw [e3, e10]
    split_ifs <;> omega
  · split_ifs <;> omega

private theorem half_support (w : List CuLetter) :
    ∃ a b : ℕ, halfWeight w = 3*a + 10*b := by
  induction w with
  | nil => exact ⟨0, 0, rfl⟩
  | cons l w ih =>
    obtain ⟨a, b, h⟩ := ih
    cases l
    · exact ⟨a, b+1, by simp only [halfWeight, h]; omega⟩
    · exact ⟨a+1, b, by simp only [halfWeight, h]; omega⟩

private theorem half_replicate (l : CuLetter) (k : ℕ) :
    halfWeight (List.replicate k l) = k * halfWeight [l] := by
  induction k with
  | zero => simp [halfWeight]
  | succ k ih => cases l <;> simp [List.replicate_succ, halfWeight, ih] <;> omega

/-- The exact support is the translated semigroup generated by three and ten. -/
theorem actual_count_support (n : ℕ) :
    0 < returnCount n ↔ ∃ a b : ℕ, n = 13 + 3*a + 10*b := by
  rw [(actual_count_middle n).2]
  by_cases hn : 13 ≤ n
  · rw [if_pos hn, Finset.card_pos]
    constructor
    · rintro ⟨w, hw⟩
      have h := (middle_membership (n-13) w).mp hw
      obtain ⟨a, b, hab⟩ := half_support w
      exact ⟨a, b, by omega⟩
    · rintro ⟨a, b, hab⟩
      refine ⟨List.replicate a .u ++ List.replicate b .c, ?_⟩
      apply (middle_membership (n-13) _).mpr
      rw [half_append, half_replicate, half_replicate]
      simp only [halfWeight]
      omega
  · simp only [if_neg hn, Nat.lt_irrefl, false_iff]
    rintro ⟨a, b, h⟩
    omega

/-- The scaled counts stay inside one positive window for every later index.
The upper estimate also holds before the positive window. -/
theorem actual_count_window (x : ℝ) (hx : 0 < x) (hunit : x < 1)
    (hroot : x^3 + x^10 = 1) :
    (∀ n : ℕ, (returnCount n : ℝ) * x^n ≤ x^13) ∧
    (∀ n : ℕ, 31 ≤ n → x^40 ≤ (returnCount n : ℝ) * x^n) := by
  have positive (n : ℕ) (hn : 31 ≤ n) : 0 < returnCount n := by
    apply (actual_count_support n).mpr
    have rem : (n-13)%3 < 3 := Nat.mod_lt _ (by omega)
    have division := Nat.mod_add_div (n-13) 3
    interval_cases hr : (n-13)%3
    · exact ⟨(n-13)/3, 0, by omega⟩
    · exact ⟨((n-13)/3)-3, 1, by omega⟩
    · exact ⟨((n-13)/3)-6, 2, by omega⟩
  have scaled (n : ℕ) (hn : 14 ≤ n) :
      (returnCount n : ℝ)*x^n =
        x^3*((returnCount (n-3) : ℝ)*x^(n-3)) +
        x^10*((returnCount (n-10) : ℝ)*x^(n-10)) := by
    have recurrence := actual_count_recurrence n
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)] at recurrence
    rw [recurrence]
    push_cast
    have e3 : x^n = x^3*x^(n-3) := by rw [←pow_add]; congr 1; omega
    have e10 : x^n = x^10*x^(n-10) := by rw [←pow_add]; congr 1; omega
    calc
      ((returnCount (n-3) : ℝ) + (returnCount (n-10) : ℝ) + 0)*x^n =
          (returnCount (n-3) : ℝ)*x^n + (returnCount (n-10) : ℝ)*x^n := by ring
      _ = _ := by
        congr 1
        · rw [e3]; ring
        · rw [e10]; ring
  constructor
  · intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : 14 ≤ n
      · rw [scaled n hn]
        have h3 := mul_le_mul_of_nonneg_left (ih (n-3) (by omega)) (pow_nonneg hx.le 3)
        have h10 := mul_le_mul_of_nonneg_left (ih (n-10) (by omega)) (pow_nonneg hx.le 10)
        calc
          _ ≤ x^3*x^13+x^10*x^13 := add_le_add h3 h10
          _ = (x^3+x^10)*x^13 := by ring
          _ = x^13 := by rw [hroot, one_mul]
      · have e := (actual_count_middle n).2
        by_cases he : n = 13
        · subst n
          norm_num only at e
          have seed : (middleWords 0).card = 1 := by rw [middleWords]; decide
          simp only [ite_true, seed] at e
          rw [e]
          simp
        · rw [if_neg (by omega)] at e
          rw [e]
          simp only [Nat.cast_zero, zero_mul]
          exact (pow_pos hx 13).le
  · intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hlarge : 41 ≤ n
      · rw [scaled n (by omega)]
        have h3 := mul_le_mul_of_nonneg_left (ih (n-3) (by omega) (by omega)) (pow_nonneg hx.le 3)
        have h10 := mul_le_mul_of_nonneg_left (ih (n-10) (by omega) (by omega)) (pow_nonneg hx.le 10)
        calc
          x^40 = (x^3+x^10)*x^40 := by rw [hroot, one_mul]
          _ = x^3*x^40+x^10*x^40 := by ring
          _ ≤ _ := add_le_add h3 h10
      · have hcount : (1 : ℝ) ≤ (returnCount n : ℝ) := by exact_mod_cast positive n hn
        have hpower : x^40 ≤ x^n := pow_le_pow_of_le_one hx.le hunit.le (by omega)
        exact hpower.trans (by simpa using mul_le_mul_of_nonneg_right hcount (pow_nonneg hx.le n))

private theorem critical_root_exists : ∃ x : ℝ, 0 < x ∧ x < 1 ∧ x^3+x^10 = 1 := by
  have continuous : ContinuousOn (fun x : ℝ => x^3+x^10) (Set.Icc 0 1) := by fun_prop
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) continuous
    (show (1 : ℝ) ∈ Set.Icc ((0 : ℝ)^3+0^10) ((1 : ℝ)^3+1^10) by norm_num)
  have hp : 0 < x := by
    by_contra h
    have hz : x = 0 := by linarith [hx.1]
    simp [hz] at he
  have hlt : x < 1 := by
    by_contra h
    have hz : x = 1 := by linarith [hx.2]
    norm_num [hz] at he
  exact ⟨x, hp, hlt, he⟩

/-- The critical half-length radius. -/
noncomputable def criticalX : ℝ := critical_root_exists.choose

/-- The per-original-window exponent of the actual return count. -/
noncomputable def alphaInfinity : ℝ := -Real.logb 2 criticalX / 2

private theorem critical_spec :
    0 < criticalX ∧ criticalX < 1 ∧ criticalX^3+criticalX^10 = 1 :=
  critical_root_exists.choose_spec

/-- Explicit logarithmic bounds on the actual count, with the complete positive
window controlling the constant loss. The exponent is strictly positive. -/
theorem actual_count_log_bounds :
    0 < alphaInfinity ∧ ∀ n : ℕ, 31 ≤ n →
      0 < (returnCount n : ℝ) ∧
      2*alphaInfinity*(n : ℝ)-80*alphaInfinity ≤ Real.logb 2 (returnCount n : ℝ) ∧
      Real.logb 2 (returnCount n : ℝ) ≤ 2*alphaInfinity*(n : ℝ)-26*alphaInfinity := by
  obtain ⟨hp, hlt, hr⟩ := critical_spec
  have window := actual_count_window criticalX hp hlt hr
  have hnlog : Real.logb 2 criticalX < 0 := Real.logb_neg (by norm_num) hp hlt
  refine ⟨by dsimp [alphaInfinity]; linarith, ?_⟩
  intro n hn
  have fl := window.2 n hn
  have fu := window.1 n
  have fp : 0 < (returnCount n : ℝ) := by
    have prod := (pow_pos hp 40).trans_le fl
    exact pos_of_mul_pos_left prod (pow_nonneg hp.le n)
  have lower := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (pow_pos hp 40) fl
  have upper := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (mul_pos fp (pow_pos hp n)) fu
  rw [Real.logb_mul fp.ne' (pow_pos hp n).ne', Real.logb_pow, Real.logb_pow] at lower upper
  refine ⟨fp, ?_⟩
  dsimp [alphaInfinity]
  norm_num at lower upper
  constructor <;> nlinarith

/-- The logarithmic error is bounded, and the exact count has the stated
rate along the even original-length lattice. -/
theorem actual_even_rate :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => Real.logb 2 (returnCount n : ℝ)-2*alphaInfinity*(n : ℝ))
      (fun _ : ℕ => (1 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => Real.logb 2 (returnCount n : ℝ) / (2*(n : ℝ)))
      Filter.atTop (nhds alphaInfinity) := by
  have apos := actual_count_log_bounds.1
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨80*alphaInfinity, Filter.eventually_atTop.mpr ⟨31, ?_⟩⟩
    intro n hn
    have hb := (actual_count_log_bounds.2 n hn).2
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2]
  · have lower : Filter.Tendsto (fun n : ℕ => alphaInfinity-40*alphaInfinity/(n : ℝ))
        Filter.atTop (nhds alphaInfinity) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (40*alphaInfinity))
    have upper : Filter.Tendsto (fun n : ℕ => alphaInfinity-13*alphaInfinity/(n : ℝ))
        Filter.atTop (nhds alphaInfinity) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (13*alphaInfinity))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
    · apply Filter.eventually_atTop.mpr
      refine ⟨31, ?_⟩
      intro n hn
      have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have lowerBound := (actual_count_log_bounds.2 n hn).2.1
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) np)).mpr
      have expansion : (alphaInfinity-40*alphaInfinity/(n : ℝ))*(2*(n : ℝ)) =
          2*alphaInfinity*(n : ℝ)-80*alphaInfinity := by field_simp; ring
      rw [expansion]
      exact lowerBound
    · apply Filter.eventually_atTop.mpr
      refine ⟨31, ?_⟩
      intro n hn
      have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have upperBound := (actual_count_log_bounds.2 n hn).2.2
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) np)).mpr
      have expansion : (alphaInfinity-13*alphaInfinity/(n : ℝ))*(2*(n : ℝ)) =
          2*alphaInfinity*(n : ℝ)-26*alphaInfinity := by field_simp; ring
      rw [expansion]
      exact upperBound

end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedReturnCount
