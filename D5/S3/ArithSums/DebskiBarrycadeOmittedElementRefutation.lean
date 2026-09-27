/- GID: D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.Lattice.Nat, mathlib/module/Mathlib.Algebra.BigOperators.Intervals, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum.BigOperators]
   utility: none
   digest: arXiv 2609.18476 Conjecture 2 (2) refuted at i = 3. -/

/-
proof_shape: result: content
escape_witness: result: form (1) - private row_zero, row_one, row_two_tail, row_two_base (closed forms and base evaluations of the first three greedy rows, on the live path)
admission_basis: open-problem-resolution (issue #8675)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.BigOperators

open scoped BigOperators
open Set

namespace D5.S3.ArithSums.DebskiBarrycadeOmittedElementRefutation

/-- `S_mu`: the set of partial sums `a_1, a_1 + a_2, ...` of an infinite sequence of
positive integers. Rows are zero-indexed: `row r k` is the `(k+1)`-st entry of row `r+1`. -/
def partialSums (mu : ℕ → ℕ) : Set ℕ :=
  {s | ∃ k, s = ∑ i ∈ Finset.range (k + 1), mu i}

/-- The greedy N-quasi-barrycade row: the least positive unused prefix entry whose
new partial sum is absent from all earlier rows. The infimum is the paper's
"smallest" operation; general nonemptiness is not formalized here. -/
noncomputable def row : ℕ → ℕ → ℕ
  | r, k => sInf {a | 0 < a ∧ (∀ i : Fin k, row r i ≠ a) ∧
      (∑ i : Fin k, row r i) + a ∉
        ⋃ j : {j // j < r}, partialSums (fun n => row j.1 n)}
termination_by r k => (r, k)
decreasing_by
  · exact Prod.Lex.right _ i.isLt
  · exact Prod.Lex.left _ _ j.2
  · exact Prod.Lex.right _ i.2

example (r k : ℕ) : row r k = sInf {a | 0 < a ∧ (∀ i < k, row r i ≠ a) ∧
    (∑ i ∈ Finset.range k, row r i) + a ∉
      ⋃ j : {j // j < r}, partialSums (fun n => row j.1 n)} := by
  rw [row.eq_1]
  simp only [Fin.sum_univ_eq_sum_range, Fin.forall_iff]

private lemma row_zero (k : ℕ) : row 0 k = k + 1 := by
  have sInf_eq_of_mem_of_lt_not_mem {s : Set ℕ} {n : ℕ}
      (hn : n ∈ s) (hmin : ∀ m < n, m ∉ s) : sInf s = n := by
    apply Nat.le_antisymm (Nat.sInf_le hn)
    by_contra h
    have hslt : sInf s < n := by omega
    exact hmin (sInf s) hslt (Nat.sInf_mem ⟨n, hn⟩)
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [row.eq_1]
      simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
      apply sInf_eq_of_mem_of_lt_not_mem
      · refine ⟨by omega, ?_, ?_⟩
        · intro i hi heq
          rw [ih i hi] at heq
          omega
        · simp
      · intro a ha hmem
        rcases hmem with ⟨hapos, hunused, _⟩
        have hi : a - 1 < k := by omega
        have haeq : a - 1 + 1 = a := by omega
        exact hunused (a - 1) hi (by simp [ih (a - 1) hi, haeq])

private lemma row_one (k : ℕ) : row 1 k = k + 2 := by
  let triangle : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, (i + 1)
  have triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
    simp [triangle, Finset.sum_range_succ]
  have triangle_strictMono : StrictMono triangle := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [triangle_succ]
    omega
  have mem_zero (x : ℕ) : x ∈ partialSums (row 0) ↔ ∃ q, x = triangle (q + 1) := by
    simp only [partialSums, Set.mem_ofPred_eq, row_zero, triangle]
  have no_zero_between {x q : ℕ} (hlo : triangle (q + 1) < x)
      (hhi : x < triangle (q + 2)) : x ∉ partialSums (row 0) := by
    rw [mem_zero]
    rintro ⟨n, rfl⟩
    by_cases hn : n ≤ q
    · have hmono := triangle_strictMono.monotone (Nat.add_le_add_right hn 1)
      omega
    · have hqn : q + 2 ≤ n + 1 := by omega
      have hmono := triangle_strictMono.monotone hqn
      omega
  have union_one (x : ℕ) :
      x ∈ ⋃ j : {j // j < 1}, partialSums (fun n => row j.1 n) ↔
        x ∈ partialSums (row 0) := by
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨j, hj⟩
      have hj0 : j.1 = 0 := by omega
      simpa [hj0] using hj
    · intro hx
      rw [Set.mem_iUnion]
      exact ⟨⟨0, by omega⟩, hx⟩
  have sInf_eq_of_mem_of_lt_not_mem {s : Set ℕ} {n : ℕ}
      (hn : n ∈ s) (hmin : ∀ m < n, m ∉ s) : sInf s = n := by
    apply Nat.le_antisymm (Nat.sInf_le hn)
    by_contra h
    have hslt : sInf s < n := by omega
    exact hmin (sInf s) hslt (Nat.sInf_mem ⟨n, hn⟩)
  have sum_shift_two (q : ℕ) :
      (∑ i ∈ Finset.range q, (i + 2)) + 1 = triangle (q + 1) := by
    induction q with
    | zero => simp [triangle]
    | succ q ih =>
        rw [Finset.sum_range_succ]
        rw [show q + 1 + 1 = (q + 1) + 1 by omega, triangle_succ]
        omega
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hsum : (∑ i ∈ Finset.range k, row 1 i) + 1 = triangle (k + 1) := by
        calc
          (∑ i ∈ Finset.range k, row 1 i) + 1 =
              (∑ i ∈ Finset.range k, (i + 2)) + 1 := by
                congr 1
                apply Finset.sum_congr rfl
                intro i hi
                rw [ih i (Finset.mem_range.mp hi)]
          _ = triangle (k + 1) := sum_shift_two k
      rw [row.eq_1]
      simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
      apply sInf_eq_of_mem_of_lt_not_mem
      · refine ⟨by omega, ?_, ?_⟩
        · intro i hi heq
          rw [ih i hi] at heq
          omega
        · rw [union_one]
          apply no_zero_between (q := k)
          · omega
          · rw [show k + 2 = (k + 1) + 1 by omega, triangle_succ]
            omega
      · intro a ha hmem
        rcases hmem with ⟨hapos, hunused, hallowed⟩
        by_cases haone : a = 1
        · apply hallowed
          rw [union_one, mem_zero]
          exact ⟨k, by omega⟩
        · have hi : a - 2 < k := by omega
          have haeq : a - 2 + 2 = a := by omega
          exact hunused (a - 2) hi (by simp [ih (a - 2) hi, haeq])

private lemma row_two_tail (k : ℕ) : row 2 (k + 3) = k + 5 := by
  let triangle : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, (i + 1)
  have triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
    simp [triangle, Finset.sum_range_succ]
  have triangle_strictMono : StrictMono triangle := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [triangle_succ]
    omega
  have mem_zero (x : ℕ) : x ∈ partialSums (row 0) ↔ ∃ q, x = triangle (q + 1) := by
    simp only [partialSums, Set.mem_ofPred_eq, row_zero, triangle]
  have sum_shift_two (q : ℕ) :
      (∑ i ∈ Finset.range q, (i + 2)) + 1 = triangle (q + 1) := by
    induction q with
    | zero => simp [triangle]
    | succ q ih =>
        rw [Finset.sum_range_succ]
        rw [show q + 1 + 1 = (q + 1) + 1 by omega, triangle_succ]
        omega
  have row_one_partial (q : ℕ) :
      (∑ i ∈ Finset.range (q + 1), row 1 i) + 1 = triangle (q + 2) := by
    calc
      _ = (∑ i ∈ Finset.range (q + 1), (i + 2)) + 1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [row_one]
      _ = triangle (q + 1 + 1) := sum_shift_two (q + 1)
      _ = triangle (q + 2) := by congr 1
  have mem_one (x : ℕ) : x ∈ partialSums (row 1) ↔
      ∃ q, x + 1 = triangle (q + 2) := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, row_one_partial q⟩
    · rintro ⟨q, hq⟩
      have hs := row_one_partial q
      exact ⟨q, by omega⟩
  have no_zero_between {x q : ℕ} (hlo : triangle (q + 1) < x)
      (hhi : x < triangle (q + 2)) : x ∉ partialSums (row 0) := by
    rw [mem_zero]
    rintro ⟨n, rfl⟩
    by_cases hn : n ≤ q
    · have hmono := triangle_strictMono.monotone (Nat.add_le_add_right hn 1)
      omega
    · have hqn : q + 2 ≤ n + 1 := by omega
      have hmono := triangle_strictMono.monotone hqn
      omega
  have no_one_between {x q : ℕ} (hlo : triangle (q + 1) < x + 1)
      (hhi : x + 1 < triangle (q + 2)) : x ∉ partialSums (row 1) := by
    rw [mem_one]
    rintro ⟨n, hn⟩
    by_cases hnk : n + 2 ≤ q + 1
    · have hmono := triangle_strictMono.monotone hnk
      omega
    · have hqn : q + 2 ≤ n + 2 := by omega
      have hmono := triangle_strictMono.monotone hqn
      omega
  have union_two (x : ℕ) :
      x ∈ ⋃ j : {j // j < 2}, partialSums (fun n => row j.1 n) ↔
        x ∈ partialSums (row 0) ∨ x ∈ partialSums (row 1) := by
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨j, hj⟩
      have hjv : j.1 = 0 ∨ j.1 = 1 := by omega
      rcases hjv with hzero | hone
      · left; simpa [hzero] using hj
      · right; simpa [hone] using hj
    · intro hx
      rw [Set.mem_iUnion]
      rcases hx with hzero | hone
      · exact ⟨⟨0, by omega⟩, hzero⟩
      · exact ⟨⟨1, by omega⟩, hone⟩
  have sInf_eq_of_mem_of_lt_not_mem {s : Set ℕ} {n : ℕ}
      (hn : n ∈ s) (hmin : ∀ m < n, m ∉ s) : sInf s = n := by
    apply Nat.le_antisymm (Nat.sInf_le hn)
    by_contra h
    have hslt : sInf s < n := by omega
    exact hmin (sInf s) hslt (Nat.sInf_mem ⟨n, hn⟩)
  have hzero : row 2 0 = 4 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, by simp, ?_⟩
      rw [union_two]
      push Not
      constructor
      · apply no_zero_between (q := 1) <;> norm_num [triangle]
      · apply no_one_between (q := 1) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, hallowed⟩
      interval_cases a
      · apply hallowed; rw [union_two, mem_zero]; left; exact ⟨0, by norm_num [triangle]⟩
      · apply hallowed; rw [union_two, mem_one]; right; exact ⟨0, by norm_num [triangle]⟩
      · apply hallowed; rw [union_two, mem_zero]; left; exact ⟨1, by norm_num [triangle]⟩
  have hone : row 2 1 = 3 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        rw [hzero]
        omega
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two]
        push Not
        constructor
        · apply no_zero_between (q := 2) <;> norm_num [triangle]
        · apply no_one_between (q := 2) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, hallowed⟩
      interval_cases a
      · apply hallowed
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two, mem_one]
        right; exact ⟨1, by norm_num [triangle]⟩
      · apply hallowed
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two, mem_zero]
        left; exact ⟨2, by norm_num [triangle]⟩
  have htwo : row 2 2 = 1 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        interval_cases i
        · rw [hzero]; omega
        · rw [hone]; omega
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero, hone]
        rw [union_two]
        push Not
        constructor
        · apply no_zero_between (q := 2) <;> norm_num [triangle]
        · apply no_one_between (q := 2) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, _⟩
      omega
  let rowTwoForm : ℕ → ℕ
    | 0 => 4
    | 1 => 3
    | 2 => 1
    | q + 3 => q + 5
  have rowTwoForm_sum (q : ℕ) (hq : 3 ≤ q) :
      (∑ i ∈ Finset.range q, rowTwoForm i) + 2 = triangle (q + 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
    induction t with
    | zero => norm_num [rowTwoForm, triangle]
    | succ t ih =>
        rw [Finset.sum_range_succ]
        rw [show Nat.succ t + 3 + 1 = (t + 3 + 1) + 1 by omega, triangle_succ]
        rw [show rowTwoForm (t + 3) = t + 5 by rfl]
        have ih' : (∑ i ∈ Finset.range (t + 3), rowTwoForm i) + 2 =
            triangle (t + 4) := by simpa [show t + 3 + 1 = t + 4 by omega] using ih (by omega)
        omega
  have row_two_step (q : ℕ) (hq : 3 ≤ q)
      (hrows : ∀ i < q, row 2 i = rowTwoForm i) : row 2 q = q + 2 := by
    have hsum : (∑ i ∈ Finset.range q, row 2 i) + 2 = triangle (q + 1) := by
      calc
        _ = (∑ i ∈ Finset.range q, rowTwoForm i) + 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [hrows i (Finset.mem_range.mp hi)]
        _ = triangle (q + 1) := rowTwoForm_sum q hq
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, ?_, ?_⟩
      · intro i hi heq
        rw [hrows i hi] at heq
        rcases i with _ | _ | _ | i <;> simp [rowTwoForm] at heq <;> omega
      · rw [union_two]
        push Not
        constructor
        · apply no_zero_between (q := q)
          · omega
          · rw [show q + 2 = (q + 1) + 1 by omega, triangle_succ]
            omega
        · apply no_one_between (q := q)
          · omega
          · rw [show q + 2 = (q + 1) + 1 by omega, triangle_succ]
            omega
    · intro a ha hmem
      rcases hmem with ⟨hapos, hunused, hallowed⟩
      by_cases ha2 : a = 2
      · apply hallowed
        rw [union_two, mem_zero]
        left; exact ⟨q, by omega⟩
      · have hused : ∃ i < q, row 2 i = a := by
          by_cases ha1 : a = 1
          · exact ⟨2, by omega, by simpa [ha1] using htwo⟩
          by_cases ha3 : a = 3
          · exact ⟨1, by omega, by simpa [ha3] using hone⟩
          by_cases ha4 : a = 4
          · exact ⟨0, by omega, by simpa [ha4] using hzero⟩
          have ha5 : 5 ≤ a := by omega
          refine ⟨a - 2, by omega, ?_⟩
          rw [hrows (a - 2) (by omega)]
          obtain ⟨t, rfl⟩ : ∃ t, a = t + 5 := ⟨a - 5, by omega⟩
          simp [rowTwoForm]
        exact hunused hused.choose hused.choose_spec.1 hused.choose_spec.2
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hrows : ∀ i < k + 3, row 2 i = rowTwoForm i := by
        intro i hi
        rcases i with _ | _ | _ | i
        · simpa [rowTwoForm] using hzero
        · simpa [rowTwoForm] using hone
        · simpa [rowTwoForm] using htwo
        · have hik : i < k := by omega
          simpa [rowTwoForm] using ih i hik
      have hstep := row_two_step (k + 3) (by omega) hrows
      omega

private theorem row_two_base : row 2 0 = 4 ∧ row 2 1 = 3 ∧ row 2 2 = 1 := by
  let triangle : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, (i + 1)
  have triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
    simp [triangle, Finset.sum_range_succ]
  have triangle_strictMono : StrictMono triangle := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [triangle_succ]
    omega
  have mem_zero (x : ℕ) : x ∈ partialSums (row 0) ↔ ∃ q, x = triangle (q + 1) := by
    simp only [partialSums, Set.mem_ofPred_eq, row_zero, triangle]
  have sum_shift_two (q : ℕ) :
      (∑ i ∈ Finset.range q, (i + 2)) + 1 = triangle (q + 1) := by
    induction q with
    | zero => simp [triangle]
    | succ q ih =>
        rw [Finset.sum_range_succ]
        rw [show q + 1 + 1 = (q + 1) + 1 by omega, triangle_succ]
        omega
  have row_one_partial (q : ℕ) :
      (∑ i ∈ Finset.range (q + 1), row 1 i) + 1 = triangle (q + 2) := by
    calc
      _ = (∑ i ∈ Finset.range (q + 1), (i + 2)) + 1 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [row_one]
      _ = triangle (q + 1 + 1) := sum_shift_two (q + 1)
      _ = triangle (q + 2) := by congr 1
  have mem_one (x : ℕ) : x ∈ partialSums (row 1) ↔
      ∃ q, x + 1 = triangle (q + 2) := by
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, row_one_partial q⟩
    · rintro ⟨q, hq⟩
      have hs := row_one_partial q
      exact ⟨q, by omega⟩
  have no_zero_between {x q : ℕ} (hlo : triangle (q + 1) < x)
      (hhi : x < triangle (q + 2)) : x ∉ partialSums (row 0) := by
    rw [mem_zero]
    rintro ⟨n, rfl⟩
    by_cases hn : n ≤ q
    · have hmono := triangle_strictMono.monotone (Nat.add_le_add_right hn 1)
      omega
    · have hqn : q + 2 ≤ n + 1 := by omega
      have hmono := triangle_strictMono.monotone hqn
      omega
  have no_one_between {x q : ℕ} (hlo : triangle (q + 1) < x + 1)
      (hhi : x + 1 < triangle (q + 2)) : x ∉ partialSums (row 1) := by
    rw [mem_one]
    rintro ⟨n, hn⟩
    by_cases hnk : n + 2 ≤ q + 1
    · have hmono := triangle_strictMono.monotone hnk
      omega
    · have hqn : q + 2 ≤ n + 2 := by omega
      have hmono := triangle_strictMono.monotone hqn
      omega
  have union_two (x : ℕ) :
      x ∈ ⋃ j : {j // j < 2}, partialSums (fun n => row j.1 n) ↔
        x ∈ partialSums (row 0) ∨ x ∈ partialSums (row 1) := by
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨j, hj⟩
      have hjv : j.1 = 0 ∨ j.1 = 1 := by omega
      rcases hjv with hzero | hone
      · left; simpa [hzero] using hj
      · right; simpa [hone] using hj
    · intro hx
      rw [Set.mem_iUnion]
      rcases hx with hzero | hone
      · exact ⟨⟨0, by omega⟩, hzero⟩
      · exact ⟨⟨1, by omega⟩, hone⟩
  have sInf_eq_of_mem_of_lt_not_mem {s : Set ℕ} {n : ℕ}
      (hn : n ∈ s) (hmin : ∀ m < n, m ∉ s) : sInf s = n := by
    apply Nat.le_antisymm (Nat.sInf_le hn)
    by_contra h
    have hslt : sInf s < n := by omega
    exact hmin (sInf s) hslt (Nat.sInf_mem ⟨n, hn⟩)
  have hzero : row 2 0 = 4 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, by simp, ?_⟩
      rw [union_two]
      push Not
      constructor
      · apply no_zero_between (q := 1) <;> norm_num [triangle]
      · apply no_one_between (q := 1) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, hallowed⟩
      interval_cases a
      · apply hallowed; rw [union_two, mem_zero]; left; exact ⟨0, by norm_num [triangle]⟩
      · apply hallowed; rw [union_two, mem_one]; right; exact ⟨0, by norm_num [triangle]⟩
      · apply hallowed; rw [union_two, mem_zero]; left; exact ⟨1, by norm_num [triangle]⟩
  have hone : row 2 1 = 3 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        rw [hzero]
        omega
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two]
        push Not
        constructor
        · apply no_zero_between (q := 2) <;> norm_num [triangle]
        · apply no_one_between (q := 2) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, hallowed⟩
      interval_cases a
      · apply hallowed
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two, mem_one]
        right; exact ⟨1, by norm_num [triangle]⟩
      · apply hallowed
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero]
        rw [union_two, mem_zero]
        left; exact ⟨2, by norm_num [triangle]⟩
  have htwo : row 2 2 = 1 := by
    rw [row.eq_1]
    simp only [Fin.forall_iff, Fin.sum_univ_eq_sum_range]
    apply sInf_eq_of_mem_of_lt_not_mem
    · refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        interval_cases i
        · rw [hzero]; omega
        · rw [hone]; omega
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hzero, hone]
        rw [union_two]
        push Not
        constructor
        · apply no_zero_between (q := 2) <;> norm_num [triangle]
        · apply no_one_between (q := 2) <;> norm_num [triangle]
    · intro a ha hmem
      rcases hmem with ⟨hapos, _, _⟩
      omega
  exact ⟨hzero, hone, htwo⟩

/-- The literal printed Conjecture 2 (2), with `i >= 3`, in the paper's indexing. -/
def claim : Prop := ∀ i : ℕ, 3 ≤ i → ∀ n : ℕ,
  IsLeast {m : ℕ | 0 < m ∧ ∀ k, row (i - 1) k ≠ m} n → row (i - 1) 0 = n + 1

example : row 0 0 = 1 := by simpa using row_zero 0
example : row 1 0 = 2 := by simpa using row_one 0
example : row 2 0 = 4 := by exact row_two_base.1
example : row 2 1 = 3 := by exact row_two_base.2.1
example : row 2 2 = 1 := by exact row_two_base.2.2
example : row 2 3 = 5 := by simpa using row_two_tail 0

theorem result : ¬ claim := by
  intro hclaim
  have hbase := row_two_base
  have hne : ∀ k, row 2 k ≠ 2 := by
    intro k
    rcases k with _ | _ | _ | k
    · rw [hbase.1]
      omega
    · rw [hbase.2.1]
      omega
    · rw [hbase.2.2]
      omega
    · rw [row_two_tail]
      omega
  have hleast : IsLeast {m : ℕ | 0 < m ∧ ∀ k, row 2 k ≠ m} 2 := by
    constructor
    · exact ⟨by omega, hne⟩
    · intro m hm
      rcases hm with ⟨hmpos, hmomit⟩
      by_contra hnot
      have hmone : m = 1 := by omega
      exact hmomit 2 (by simpa [hmone] using hbase.2.2)
  have hbad := hclaim 3 (by omega) 2 (by simpa using hleast)
  rw [hbase.1] at hbad
  norm_num at hbad

end D5.S3.ArithSums.DebskiBarrycadeOmittedElementRefutation
