/- GID: D5/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/SharedThresholdResponseCoupling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One finite rational disturbance simultaneously attains every two-world Boolean Frechet cell bound across arbitrary finite mediator values. -/

import D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw
import Mathlib.Algebra.BigOperators.Fin

/- The shared threshold is an attaining choice of within-mechanism dependence.
   It is not an assumption imposed on all outcome laws. Both interventions read
   one complete outcome table. The denominator is arbitrary and positive, so
   the construction works at every finite rational grid, without approximation.
   Consumer: PartialMediatorTransportReduction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.SharedThresholdResponseCoupling

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw

/-- The same finite uniform disturbance is used for all response coordinates. -/
def uniformThresholdLaw (denominator : ℕ) (positive : 0 < denominator) :
    FiniteResponseLaw (Fin denominator) where
  mass := fun _ => 1 / (denominator : ℚ)
  nonnegative := fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)
  total := by
    have nz : (denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt positive)
    simp [Finset.sum_const, nsmul_eq_mul, nz]

/-- Probability of a prefix in the finite uniform disturbance. -/
theorem uniformThreshold_prefix (N K : ℕ) (hN : 0 < N) (hK : K ≤ N) :
    linearObjective (fun u : Fin N => if u.val < K then 1 else 0)
      (uniformThresholdLaw N hN).mass = (K : ℚ) / N := by
  have filtered : (Finset.range N).filter (fun i => i < K) = Finset.range K := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold linearObjective uniformThresholdLaw
  simp only [ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < K then (1 : ℚ) / N else 0)]
  rw [← Finset.sum_filter, filtered]
  simp [nsmul_eq_mul, div_eq_mul_inv]

private theorem uniformThreshold_both (N A B : ℕ) (hN : 0 < N)
    (hA : A ≤ N) (hB : B ≤ N) :
    linearObjective (fun u : Fin N => if u.val < A ∧ u.val < B then 1 else 0)
      (uniformThresholdLaw N hN).mass = min ((A : ℚ) / N) ((B : ℚ) / N) := by
  have event : (fun u : Fin N => if u.val < A ∧ u.val < B then (1 : ℚ) else 0) =
      (fun u => if u.val < min A B then 1 else 0) := by
    funext u
    simp only [lt_min_iff]
  rw [event, uniformThreshold_prefix N (min A B) hN ((min_le_left _ _).trans hA)]
  have hn : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  rcases le_total A B with h | h
  · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right (by exact_mod_cast h) hn)]
  · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right (by exact_mod_cast h) hn)]

private theorem uniformThreshold_between (N A B : ℕ) (hN : 0 < N)
    (hA : A ≤ N) (hB : B ≤ N) :
    linearObjective (fun u : Fin N => if ¬u.val < A ∧ u.val < B then 1 else 0)
      (uniformThresholdLaw N hN).mass = max 0 ((B : ℚ) / N - (A : ℚ) / N) := by
  have event : (fun u : Fin N => if ¬u.val < A ∧ u.val < B then (1 : ℚ) else 0) =
      (fun u => (if u.val < B then 1 else 0) -
        (if u.val < A ∧ u.val < B then 1 else 0)) := by
    funext u
    by_cases ha : u.val < A <;> by_cases hb : u.val < B <;> simp [ha, hb]
  rw [event]
  have split : linearObjective
      (fun u : Fin N => (if u.val < B then 1 else 0) -
        (if u.val < A ∧ u.val < B then 1 else 0)) (uniformThresholdLaw N hN).mass =
      linearObjective (fun u : Fin N => if u.val < B then 1 else 0)
          (uniformThresholdLaw N hN).mass -
        linearObjective (fun u : Fin N => if u.val < A ∧ u.val < B then 1 else 0)
          (uniformThresholdLaw N hN).mass := by
    simp only [linearObjective, sub_mul, Finset.sum_sub_distrib]
  rw [split, uniformThreshold_prefix N B hN hB, uniformThreshold_both N A B hN hA hB]
  by_cases h : (A : ℚ) / N ≤ (B : ℚ) / N
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), sub_self,
      max_eq_left (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]

variable {Mediator : Type*} [Fintype Mediator] [DecidableEq Mediator]

/-- Actual outcome success probability at treatment a and mediator m. -/
def outcomeSuccess (law : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (a : Bool) (m : Mediator) : ℚ :=
  linearObjective (fun table => if table (a, m) then 1 else 0) law.mass

/-- Cross-world benefit conditional on a complete mediator response pair. -/
def outcomeBenefitCell (law : FiniteResponseLaw ((Bool × Mediator) → Bool))
    (m0 m1 : Mediator) : ℚ :=
  linearObjective (fun table => if table (false, m0) = false ∧ table (true, m1) = true
    then 1 else 0) law.mass

/-- Upper witness flips the control threshold; lower witness uses aligned
actual-success thresholds. Neither construction splits the two worlds' noise. -/
noncomputable def thresholdOutcomeLaw (N : ℕ) (hN : 0 < N)
    (count : Bool × Mediator → ℕ) (upper : Bool) :
    FiniteResponseLaw ((Bool × Mediator) → Bool) :=
  pushforwardResponseLaw (uniformThresholdLaw N hN) (fun u index =>
    if upper && !index.1 then !decide (u.val < N - count index)
    else decide (u.val < count index))

/-- Both attaining outcome mechanisms reproduce every prescribed success row. -/
theorem thresholdOutcomeLaw_success (N : ℕ) (hN : 0 < N)
    (count : Bool × Mediator → ℕ) (bounded : ∀ index, count index ≤ N)
    (upper a : Bool) (m : Mediator) :
    outcomeSuccess (thresholdOutcomeLaw N hN count upper) a m = (count (a, m) : ℚ) / N := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold outcomeSuccess thresholdOutcomeLaw
  rw [pushforward_linearObjective]
  cases upper <;> cases a
  · simpa using uniformThreshold_prefix N (count (false, m)) hN (bounded _)
  · simpa using uniformThreshold_prefix N (count (true, m)) hN (bounded _)
  · have event : (fun u : Fin N => if (!decide (u.val < N - count (false, m))) then
          (1 : ℚ) else 0) =
        (fun u => 1 - (if u.val < N - count (false, m) then 1 else 0)) := by
      funext u
      by_cases h : u.val < N - count (false, m) <;> simp [h]
    change linearObjective (fun u : Fin N => if (!decide (u.val < N - count (false, m)))
      then (1 : ℚ) else 0) (uniformThresholdLaw N hN).mass = _
    rw [event]
    have split : linearObjective
        (fun u : Fin N => 1 - (if u.val < N - count (false, m) then 1 else 0))
          (uniformThresholdLaw N hN).mass =
        1 - linearObjective (fun u : Fin N => if u.val < N - count (false, m) then 1 else 0)
          (uniformThresholdLaw N hN).mass := by
      simp only [linearObjective, sub_mul, one_mul, Finset.sum_sub_distrib,
        (uniformThresholdLaw N hN).total]
    rw [split, uniformThreshold_prefix N (N - count (false, m)) hN (Nat.sub_le _ _),
      Nat.cast_sub (bounded _)]
    field_simp [hn] <;> ring
  · simpa using uniformThreshold_prefix N (count (true, m)) hN (bounded _)

/-- A single upper witness attains all m0,m1 upper cells simultaneously. -/
theorem thresholdOutcomeLaw_upper_cells (N : ℕ) (hN : 0 < N)
    (count : Bool × Mediator → ℕ) (bounded : ∀ index, count index ≤ N)
    (m0 m1 : Mediator) :
    outcomeBenefitCell (thresholdOutcomeLaw N hN count true) m0 m1 =
      min (1 - (count (false, m0) : ℚ) / N) ((count (true, m1) : ℚ) / N) := by
  unfold outcomeBenefitCell thresholdOutcomeLaw
  rw [pushforward_linearObjective]
  have h := uniformThreshold_both N (N - count (false, m0)) (count (true, m1)) hN
    (Nat.sub_le _ _) (bounded _)
  have complement : ((N - count (false, m0) : ℕ) : ℚ) / N =
      1 - (count (false, m0) : ℚ) / N := by
    rw [Nat.cast_sub (bounded _)]
    have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp [hn] <;> ring
  rw [complement] at h
  simpa using h

/-- A different single witness attains all lower cells simultaneously. -/
theorem thresholdOutcomeLaw_lower_cells (N : ℕ) (hN : 0 < N)
    (count : Bool × Mediator → ℕ) (bounded : ∀ index, count index ≤ N)
    (m0 m1 : Mediator) :
    outcomeBenefitCell (thresholdOutcomeLaw N hN count false) m0 m1 =
      max 0 ((count (true, m1) : ℚ) / N - (count (false, m0) : ℚ) / N) := by
  unfold outcomeBenefitCell thresholdOutcomeLaw
  rw [pushforward_linearObjective]
  simpa using uniformThreshold_between N (count (false, m0)) (count (true, m1))
    hN (bounded _) (bounded _)

/-- Every admitted outcome law obeys the same cell bounds. -/
theorem outcomeBenefitCell_bounds
    (law : FiniteResponseLaw ((Bool × Mediator) → Bool)) (m0 m1 : Mediator) :
    max 0 (outcomeSuccess law true m1 - outcomeSuccess law false m0) ≤
        outcomeBenefitCell law m0 m1 ∧
      outcomeBenefitCell law m0 m1 ≤
        min (1 - outcomeSuccess law false m0) (outcomeSuccess law true m1) := by
  have pointwise (table : (Bool × Mediator) → Bool) :
      (0 : ℚ) ≤ (if table (false, m0) = false ∧ table (true, m1) = true then 1 else 0) ∧
      (if table (true, m1) then (1 : ℚ) else 0) - (if table (false, m0) then 1 else 0) ≤
        (if table (false, m0) = false ∧ table (true, m1) = true then 1 else 0) ∧
      (if table (false, m0) = false ∧ table (true, m1) = true then (1 : ℚ) else 0) ≤
        1 - (if table (false, m0) then 1 else 0) ∧
      (if table (false, m0) = false ∧ table (true, m1) = true then (1 : ℚ) else 0) ≤
        (if table (true, m1) then 1 else 0) := by
    cases h0 : table (false, m0) <;> cases h1 : table (true, m1) <;> norm_num
  have h0 := Finset.sum_nonneg (fun table (_ : table ∈ (Finset.univ :
      Finset ((Bool × Mediator) → Bool))) => mul_nonneg (pointwise table).1 (law.nonnegative table))
  have h1 := Finset.sum_le_sum (fun table (_ : table ∈ (Finset.univ :
      Finset ((Bool × Mediator) → Bool))) =>
        mul_le_mul_of_nonneg_right (pointwise table).2.1 (law.nonnegative table))
  have h2 := Finset.sum_le_sum (fun table (_ : table ∈ (Finset.univ :
      Finset ((Bool × Mediator) → Bool))) =>
        mul_le_mul_of_nonneg_right (pointwise table).2.2.1 (law.nonnegative table))
  have h3 := Finset.sum_le_sum (fun table (_ : table ∈ (Finset.univ :
      Finset ((Bool × Mediator) → Bool))) =>
        mul_le_mul_of_nonneg_right (pointwise table).2.2.2 (law.nonnegative table))
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib, law.total] at h1 h2
  exact ⟨max_le h0 h1, le_min h2 h3⟩

private theorem rational_common_grid {Index : Type*} [Fintype Index]
    (probability : Index → ℚ) (valid : ∀ i, 0 ≤ probability i ∧ probability i ≤ 1) :
    ∃ N : ℕ, ∃ count : Index → ℕ,
      0 < N ∧ (∀ i, count i ≤ N) ∧ ∀ i, probability i = (count i : ℚ) / N := by
  classical
  let numerator : Index → ℕ := fun i => (probability i).num.toNat
  let denominator : Index → ℕ := fun i => (probability i).den
  have den_pos (i : Index) : 0 < denominator i := Rat.den_pos _
  have representation (i : Index) : probability i = (numerator i : ℚ) / denominator i := by
    have num_int : (numerator i : ℤ) = (probability i).num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.mpr (valid i).1)
    have num_rat : (numerator i : ℚ) = ((probability i).num : ℚ) := by
      exact_mod_cast num_int
    rw [num_rat]
    exact (Rat.num_div_den _).symm
  have numerator_le (i : Index) : numerator i ≤ denominator i := by
    have dp : (0 : ℚ) < denominator i := by exact_mod_cast den_pos i
    have bound : (numerator i : ℚ) / denominator i ≤ 1 := by
      rw [← representation i]
      exact (valid i).2
    have h := (div_le_iff₀ dp).mp bound
    have h' : (numerator i : ℚ) ≤ denominator i := by simpa only [one_mul] using h
    exact_mod_cast h'
  let N := ∏ i, denominator i
  have Npos : 0 < N := Finset.prod_pos (fun i _ => den_pos i)
  have divides (i : Index) : denominator i ∣ N :=
    Finset.dvd_prod_of_mem denominator (Finset.mem_univ i)
  have factorization (i : Index) : denominator i * (N / denominator i) = N :=
    Nat.mul_div_cancel' (divides i)
  refine ⟨N, (fun i => numerator i * (N / denominator i)), Npos, ?_, ?_⟩
  · intro i
    exact (Nat.mul_le_mul_right (N / denominator i) (numerator_le i)).trans_eq (factorization i)
  · intro i
    have dp : (denominator i : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (den_pos i))
    have np : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Npos)
    have factors : (denominator i : ℚ) * ((N / denominator i : ℕ) : ℚ) = N := by
      exact_mod_cast factorization i
    apply (eq_div_iff np).mpr
    rw [representation i]
    calc
      (numerator i : ℚ) / denominator i * N =
          (numerator i : ℚ) / denominator i *
            ((denominator i : ℚ) * ((N / denominator i : ℕ) : ℚ)) := by rw [factors]
      _ = (numerator i : ℚ) * ((N / denominator i : ℕ) : ℚ) := by field_simp [dp] <;> ring
      _ = ((numerator i * (N / denominator i) : ℕ) : ℚ) := by push_cast; rfl

/-- Every finite rational success kernel has two complete outcome mechanisms
that simultaneously attain all two-world lower and upper Frechet cells.
The same respective mechanism works for every pair of mediator values. -/
theorem simultaneous_frechet_outcome_laws
    (probability : Bool × Mediator → ℚ)
    (valid : ∀ index, 0 ≤ probability index ∧ probability index ≤ 1) :
    ∃ lower upper : FiniteResponseLaw ((Bool × Mediator) → Bool),
      (∀ a m, outcomeSuccess lower a m = probability (a, m)) ∧
      (∀ a m, outcomeSuccess upper a m = probability (a, m)) ∧
      (∀ m0 m1, outcomeBenefitCell lower m0 m1 =
        max 0 (probability (true, m1) - probability (false, m0))) ∧
      (∀ m0 m1, outcomeBenefitCell upper m0 m1 =
        min (1 - probability (false, m0)) (probability (true, m1))) := by
  obtain ⟨N, count, positive, bounded, represents⟩ := rational_common_grid probability valid
  refine ⟨thresholdOutcomeLaw N positive count false, thresholdOutcomeLaw N positive count true,
    ?_, ?_, ?_, ?_⟩
  · intro a m
    rw [thresholdOutcomeLaw_success N positive count bounded, represents]
  · intro a m
    rw [thresholdOutcomeLaw_success N positive count bounded, represents]
  · intro m0 m1
    rw [thresholdOutcomeLaw_lower_cells N positive count bounded, represents, represents]
  · intro m0 m1
    rw [thresholdOutcomeLaw_upper_cells N positive count bounded, represents, represents]

#print axioms simultaneous_frechet_outcome_laws
#print axioms thresholdOutcomeLaw_success
#print axioms thresholdOutcomeLaw_upper_cells
#print axioms thresholdOutcomeLaw_lower_cells

end D5.S3.ConceptDynamics.CausalMoments.SharedThresholdResponseCoupling
