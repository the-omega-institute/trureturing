/- GID: D5/S3/Quantum/Thermal/ExactPartitionCounting
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/ExactPartitionCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit CNF penalties, local commuting projections, and exact rational counting recovery. -/

import Mathlib

/-!
The energy is constructed from the syntax of a CNF, not from a supplied count.
Clauses may repeat and may be empty. The rational partition uses inverse
 temperature log 2 and penalty n+1. The computational claims here are exact
finite identities and an explicit common denominator, not a Turing-machine
running-time theorem or a hardness theorem for approximate free energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Thermal.ExactPartitionCounting

open scoped BigOperators

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev Literal (n : ℕ) := Fin n × Bool
abbrev Clause (n : ℕ) := List (Literal n)
abbrev CNF (n : ℕ) := List (Clause n)

def evalClause {n : ℕ} (x : Assignment n) : Clause n → Bool
  | [] => false
  | l :: c => (x l.1 == l.2) || evalClause x c

def violations {n : ℕ} : CNF n → Assignment n → ℕ
  | [], _ => 0
  | c :: f, x => (if evalClause x c then 0 else 1) + violations f x

theorem violations_eq_zero_iff {n : ℕ} (f : CNF n) (x : Assignment n) :
    violations f x = 0 ↔ f.all (evalClause x) = true := by
  induction f with
  | nil => simp [violations]
  | cons c f ih =>
      cases hc : evalClause x c <;> simp [violations, hc, ih]

theorem violations_le_length {n : ℕ} (f : CNF n) (x : Assignment n) :
    violations f x ≤ f.length := by
  induction f with
  | nil => simp [violations]
  | cons c f ih =>
      cases hc : evalClause x c <;> simp only [violations, hc, List.length_cons] <;>
        simp_all <;> omega

def satisfyingCount {n : ℕ} (f : CNF n) : ℕ :=
  (Finset.univ.filter (fun x : Assignment n => f.all (evalClause x) = true)).card

def zeroCount {ι : Type*} [Fintype ι] (v : ι → ℕ) : ℕ :=
  (Finset.univ.filter (fun x => v x = 0)).card

theorem zeroCount_violations {n : ℕ} (f : CNF n) :
    zeroCount (violations f) = satisfyingCount f := by
  classical
  unfold zeroCount satisfyingCount
  congr 1
  ext x
  simp [violations_eq_zero_iff]

noncomputable def partition {ι : Type*} [Fintype ι] (v : ι → ℕ) (q : ℚ) : ℚ :=
  ∑ x, q ^ v x

noncomputable def tail {ι : Type*} [Fintype ι] (v : ι → ℕ) (q : ℚ) : ℚ :=
  ∑ x, if v x = 0 then 0 else q ^ v x

theorem partition_split {ι : Type*} [Fintype ι] (v : ι → ℕ) (q : ℚ) :
    partition v q = (zeroCount v : ℚ) + tail v q := by
  classical
  have hc : (∑ x, if v x = 0 then (1 : ℚ) else 0) = (zeroCount v : ℚ) := by
    simp [zeroCount]
  calc
    partition v q = ∑ x, ((if v x = 0 then (1 : ℚ) else 0) +
        (if v x = 0 then 0 else q ^ v x)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : v x = 0 <;> simp [hx]
    _ = (∑ x, if v x = 0 then (1 : ℚ) else 0) + tail v q := by
      simp only [tail, Finset.sum_add_distrib]
    _ = (zeroCount v : ℚ) + tail v q := by rw [hc]

private theorem small_pow_le_one {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    q ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc
        q ^ k * q ≤ 1 * 1 := mul_le_mul ih hq1 hq0 (by norm_num)
        _ = 1 := by norm_num

private theorem positive_power_le {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {k : ℕ} (hk : k ≠ 0) : q ^ k ≤ q := by
  cases k with
  | zero => exact (hk rfl).elim
  | succ k =>
      rw [pow_succ]
      simpa using mul_le_mul_of_nonneg_right (small_pow_le_one hq0 hq1 k) hq0

theorem tail_nonneg {ι : Type*} [Fintype ι] (v : ι → ℕ) {q : ℚ} (hq : 0 ≤ q) :
    0 ≤ tail v q := by
  classical
  apply Finset.sum_nonneg
  intro x _
  by_cases hx : v x = 0 <;> simp [hx, pow_nonneg hq]

theorem tail_le_card_mul {ι : Type*} [Fintype ι] (v : ι → ℕ)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    tail v q ≤ (Fintype.card ι : ℚ) * q := by
  classical
  calc
    tail v q ≤ ∑ _x : ι, q := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : v x = 0
      · simpa [hx] using hq0
      · simpa [hx] using positive_power_le hq0 hq1 hx
    _ = (Fintype.card ι : ℚ) * q := by simp

theorem floor_partition {ι : Type*} [Fintype ι] (v : ι → ℕ)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (Fintype.card ι : ℚ) * q < 1) :
    Int.floor (partition v q) = (zeroCount v : ℤ) := by
  have h0 := tail_nonneg v hq0
  have h1 := tail_le_card_mul v hq0 hq1
  have hs := partition_split v q
  apply Int.floor_eq_iff.mpr
  constructor
  · have h : (zeroCount v : ℚ) ≤ partition v q := by linarith
    simpa using h
  · have h : partition v q < (zeroCount v : ℚ) + 1 := by linarith
    simpa using h

def weight (n : ℕ) : ℚ := 1 / (2 : ℚ) ^ (n + 1)

private theorem one_le_two_pow (k : ℕ) : (1 : ℚ) ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; linarith

theorem weight_pos (n : ℕ) : 0 < weight n := by unfold weight; positivity

theorem weight_le_one (n : ℕ) : weight n ≤ 1 := by
  unfold weight
  exact (div_le_one (by positivity)).mpr (one_le_two_pow (n + 1))

theorem assignment_card_weight (n : ℕ) :
    (Fintype.card (Assignment n) : ℚ) * weight n = 1 / 2 := by
  have hp : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [Assignment, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, weight, pow_succ]
  field_simp [hp] <;> ring

noncomputable def hiddenPartition {n : ℕ} (f : CNF n) : ℚ :=
  partition (violations f) (weight n)

/-- Sum over the actual additional two-level system, with energies 0 and 1. -/
noncomputable def visibleHiddenPartition {n : ℕ} (f : CNF n) : ℚ :=
  ∑ b : Bool, (if b then (1 / 2 : ℚ) else 1) * hiddenPartition f

theorem visible_factor {n : ℕ} (f : CNF n) :
    visibleHiddenPartition f = (3 / 2 : ℚ) * hiddenPartition f := by
  simp [visibleHiddenPartition, Fintype.sum_bool] <;> ring

/-- Exact one-query recovery, valid also for unsatisfiable and empty formulas. -/
theorem exact_cnf_counting_recovery {n : ℕ} (f : CNF n) :
    Int.floor ((2 / 3 : ℚ) * visibleHiddenPartition f) = (satisfyingCount f : ℤ) := by
  have hs : (Fintype.card (Assignment n) : ℚ) * weight n < 1 := by
    rw [assignment_card_weight]
    norm_num
  have hf := floor_partition (violations f) (le_of_lt (weight_pos n))
    (weight_le_one n) hs
  rw [zeroCount_violations] at hf
  have hz : (2 / 3 : ℚ) * visibleHiddenPartition f = hiddenPartition f := by
    rw [visible_factor]
    ring
  rw [hz]
  exact hf

def clauseSupport {n : ℕ} (c : Clause n) : Finset (Fin n) :=
  (c.map Prod.fst).toFinset

theorem evalClause_congr {n : ℕ} (c : Clause n) (x y : Assignment n)
    (h : ∀ l ∈ c, x l.1 = y l.1) : evalClause x c = evalClause y c := by
  revert h
  induction c with
  | nil => intro _; rfl
  | cons l c ih =>
      intro h
      have hl := h l (by simp)
      have ht : ∀ a ∈ c, x a.1 = y a.1 := by
        intro a ha
        exact h a (by simp [ha])
      simp only [evalClause, hl, ih ht]

/-- A clause reads no variables outside its explicit support. -/
theorem clause_three_local {n : ℕ} (c : Clause n) (hc : c.length ≤ 3) :
    (clauseSupport c).card ≤ 3 ∧
    ∀ x y : Assignment n,
      (∀ i ∈ clauseSupport c, x i = y i) → evalClause x c = evalClause y c := by
  constructor
  · exact (List.toFinset_card_le (c.map Prod.fst)).trans (by simpa using hc)
  · intro x y h
    apply evalClause_congr c x y
    intro l hl
    apply h l.1
    simp only [clauseSupport, List.mem_toFinset]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩

noncomputable def clauseProjector {n : ℕ} (c : Clause n) :
    Matrix (Assignment n) (Assignment n) ℚ :=
  Matrix.diagonal (fun x => if evalClause x c then 0 else 1)

theorem clauseProjector_idempotent {n : ℕ} (c : Clause n) :
    clauseProjector c * clauseProjector c = clauseProjector c := by
  classical
  unfold clauseProjector
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  cases h : evalClause x c <;> simp [h]

theorem clauseProjectors_commute {n : ℕ} (c d : Clause n) :
    clauseProjector c * clauseProjector d = clauseProjector d * clauseProjector c := by
  classical
  unfold clauseProjector
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

/-- Natural numerator of the partition at the explicit common denominator. -/
noncomputable def partitionNumerator {n : ℕ} (f : CNF n) : ℕ :=
  ∑ x : Assignment n, (2 ^ (n + 1)) ^ (f.length - violations f x)

theorem common_denominator {n : ℕ} (f : CNF n) :
    ((2 ^ (n + 1)) ^ f.length : ℚ) * hiddenPartition f =
      (partitionNumerator f : ℚ) := by
  classical
  have hb : (2 : ℚ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  unfold hiddenPartition partition partitionNumerator weight
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  have hk := violations_le_length f x
  calc
    ((2 : ℚ) ^ (n + 1)) ^ f.length * (1 / 2 ^ (n + 1)) ^ violations f x =
        (((2 : ℚ) ^ (n + 1)) ^ (f.length - violations f x) *
          ((2 : ℚ) ^ (n + 1)) ^ violations f x) *
            (((2 : ℚ) ^ (n + 1)) ^ violations f x)⁻¹ := by
      rw [← pow_add, Nat.sub_add_cancel hk, one_div, inv_pow]
    _ = ((2 : ℚ) ^ (n + 1)) ^ (f.length - violations f x) := by
      rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb), mul_one]


/-- The rational weight is the Boltzmann weight at the fixed positive
inverse temperature log 2, not a new definition of the exponential. -/
theorem boltzmann_weight {n : ℕ} (f : CNF n) (x : Assignment n) :
    Real.exp (-Real.log 2 * (((n + 1) * violations f x : ℕ) : ℝ)) =
      (((weight n) ^ violations f x : ℚ) : ℝ) := by
  have he : -Real.log 2 * (((n + 1) * violations f x : ℕ) : ℝ) =
      -((((n + 1) * violations f x : ℕ) : ℝ) * Real.log 2) := by ring
  rw [he, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  unfold weight
  push_cast
  rw [one_div, inv_pow, pow_mul]

/-- The diagonal energy is the sum of the individual Boolean penalties. -/
theorem penalty_sum {n : ℕ} (f : CNF n) (x : Assignment n) :
    (violations f x : ℚ) =
      (f.map (fun c => if evalClause x c then (0 : ℚ) else 1)).sum := by
  induction f with
  | nil => simp [violations]
  | cons c f ih =>
      cases hc : evalClause x c <;> simp [violations, hc, ih]

#print axioms exact_cnf_counting_recovery
#print axioms clause_three_local
#print axioms clauseProjector_idempotent
#print axioms clauseProjectors_commute
#print axioms common_denominator
#print axioms boltzmann_weight
#print axioms penalty_sum

end D5.S3.Quantum.Thermal.ExactPartitionCounting
