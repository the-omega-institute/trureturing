/- GID: D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Factorial congruences control the local normalized divisor factors. -/

import D5.S3.Arith.RobinExponentSwap
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Asymptotics D5.S3.Arith.RobinExponentSwap
open scoped BigOperators Topology

namespace D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer

/-- All prime factors at most the factorial boundary, including factors equal to one. -/
noncomputable def smallWeight (m n : ℕ) : ℝ :=
  ∏ p ∈ Ioc 0 m with p.Prime, reciprocalGeomSum p (n.factorization p)

/-- The simultaneous error floor at the factorial boundary. -/
noncomputable def delta (m : ℕ) : ℝ :=
  ∏ p ∈ Ioc 0 m with p.Prime, (1 - ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1))

/-- The factorial congruence squeeze and its quantitative vanishing error. -/
theorem result :
    (∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => delta m - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹) := by
  have squeeze {m a b : ℕ} (_hm : 2 ≤ m)
      (ha : 0 < a) (hb : 0 < b) (hab : Nat.ModEq m.factorial a b) :
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹ := by
    classical
    have scalar (p : ℕ) (hp : p.Prime) :
        let q := (p : ℝ)⁻¹
        let t := m.factorial.factorization p
        1 - q ^ (t + 1) ≤ reciprocalGeomSum p (a.factorization p) /
          reciprocalGeomSum p (b.factorization p) ∧
        reciprocalGeomSum p (a.factorization p) / reciprocalGeomSum p (b.factorization p) ≤
          (1 - q ^ (t + 1))⁻¹ := by
      dsimp
      let q : ℝ := (p : ℝ)⁻¹
      let t := m.factorial.factorization p
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hq0 : 0 < q := inv_pos.mpr (by exact_mod_cast hp.pos)
      have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hp1
      have hpow (v : ℕ) : 0 < 1 - q ^ (v + 1) := by
        exact sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (by omega))
      have hformula (v : ℕ) : reciprocalGeomSum p v = (1 - q ^ (v + 1)) / (1 - q) := by
        dsimp [reciprocalGeomSum]
        rw [geom_sum_eq (ne_of_lt hq1)]
        change (q ^ (v + 1) - 1) / (q - 1) = _
        rw [← neg_sub (1 : ℝ) (q ^ (v + 1)), ← neg_sub (1 : ℝ) q, neg_div_neg_eq]
      have ratio : reciprocalGeomSum p (a.factorization p) /
          reciprocalGeomSum p (b.factorization p) =
          (1 - q ^ (a.factorization p + 1)) / (1 - q ^ (b.factorization p + 1)) := by
        rw [hformula, hformula, div_div_div_cancel_right₀ (sub_pos.mpr hq1).ne']
      have congrpow (k : ℕ) (hk : k ≤ t) :
          k ≤ a.factorization p ↔ k ≤ b.factorization p := by
        rw [← hp.pow_dvd_iff_le_factorization ha.ne',
          ← hp.pow_dvd_iff_le_factorization hb.ne']
        exact hab.dvd_iff ((hp.pow_dvd_iff_le_factorization m.factorial_ne_zero).mpr hk)
      have valuation : (a.factorization p = b.factorization p ∧ a.factorization p < t) ∨
          (t ≤ a.factorization p ∧ t ≤ b.factorization p) := by
        by_cases hta : t ≤ a.factorization p
        · exact Or.inr ⟨hta, (congrpow t le_rfl).mp hta⟩
        · have hat : a.factorization p < t := by omega
          have hablo := (congrpow (a.factorization p) (by omega)).mp le_rfl
          have habhi := mt (congrpow (a.factorization p + 1) (by omega)).mpr
            (by omega : ¬a.factorization p + 1 ≤ a.factorization p)
          exact Or.inl ⟨by omega, hat⟩
      rw [ratio]
      rcases valuation with ⟨heq, _⟩ | ⟨hta, htb⟩
      · rw [heq, div_self (hpow _).ne']
        exact ⟨sub_le_self _ (pow_nonneg hq0.le _),
          (one_le_inv₀ (hpow _)).mpr (sub_le_self _ (pow_nonneg hq0.le _))⟩
      · have hA : 1 - q ^ (t + 1) ≤ 1 - q ^ (a.factorization p + 1) := by
          exact sub_le_sub_left (pow_le_pow_of_le_one hq0.le hq1.le (by omega)) 1
        have hB : 1 - q ^ (t + 1) ≤ 1 - q ^ (b.factorization p + 1) := by
          exact sub_le_sub_left (pow_le_pow_of_le_one hq0.le hq1.le (by omega)) 1
        constructor
        · apply (le_div_iff₀ (hpow _)).mpr
          exact (mul_le_of_le_one_right (hpow _).le
            (sub_le_self _ (pow_nonneg hq0.le _))).trans hA
        · rw [inv_eq_one_div]
          apply (div_le_div_iff₀ (hpow _) (hpow _)).mpr
          rw [one_mul]
          exact (mul_le_of_le_one_left (hpow _).le
            (sub_le_self _ (pow_nonneg hq0.le _))).trans hB
    have factorpos (p : ℕ) (hp : p.Prime) (v : ℕ) : 0 < reciprocalGeomSum p v := by
      dsimp [reciprocalGeomSum]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < ((p : ℝ)⁻¹) ^ 0)
        (Finset.single_le_sum (fun i _ => pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
          (mem_range.mpr (by omega)))
    have deltapos (p : ℕ) (hp : p.Prime) :
        0 < 1 - ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      exact sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr (Nat.cast_nonneg _))
        (inv_lt_one_of_one_lt₀ hp1) (by omega))
    dsimp [smallWeight, delta]
    rw [← Finset.prod_div_distrib, ← Finset.prod_inv_distrib]
    constructor
    · exact Finset.prod_le_prod
        (fun p hp => (deltapos p (mem_filter.mp hp).2).le)
        (fun p hp => (scalar p (mem_filter.mp hp).2).1)
    · exact Finset.prod_le_prod
        (fun p hp => (div_pos (factorpos p (mem_filter.mp hp).2 _)
          (factorpos p (mem_filter.mp hp).2 _)).le)
        (fun p hp => (scalar p (mem_filter.mp hp).2).2)
  have tailbound {m : ℕ} (hm : 4 ≤ m) :
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹ ∧
      |delta m - 1| ≤ (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹ := by
    classical
    let f : ℕ → ℝ := fun p => ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)
    let s := (Ioc 0 m).filter Nat.Prime
    let k := ⌊Real.sqrt m⌋₊
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by positivity
    have hsqrt : 2 ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
    have hk1 : 1 ≤ k := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (by norm_num; linarith)
    have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkm : k ≤ m := by
      apply Nat.floor_le_of_le
      exact Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    have small (p : ℕ) (hp : p.Prime) : f p ≤ (m : ℝ)⁻¹ := by
      have hlog : Nat.log p m ≤ m.factorial.factorization p :=
        (hp.pow_dvd_iff_le_factorization m.factorial_ne_zero).mp
          (Nat.dvd_factorial (Nat.pow_pos hp.pos) (Nat.pow_log_le_self p (by omega)))
      have hlt : m < p ^ (m.factorial.factorization p + 1) :=
        Nat.lt_pow_of_log_lt hp.one_lt (by omega)
      have hltR : (m : ℝ) < (p : ℝ) ^ (m.factorial.factorization p + 1) := by
        exact_mod_cast hlt
      dsimp [f]
      rw [inv_pow]
      exact inv_anti₀ hm0 hltR.le
    have large (p : ℕ) (hp : p.Prime) (hpm : p ≤ m) :
        f p ≤ 1 / ((p : ℝ) * (p - 1)) := by
      have ht : 1 ≤ m.factorial.factorization p :=
        (hp.dvd_iff_one_le_factorization m.factorial_ne_zero).mp
          (Nat.dvd_factorial hp.pos hpm)
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hq : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp1.le
      calc
        f p ≤ ((p : ℝ)⁻¹) ^ 2 :=
          pow_le_pow_of_le_one (by positivity) hq (by omega)
        _ = ((p : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
        _ ≤ 1 / ((p : ℝ) * (p - 1)) := by
          rw [one_div]
          apply inv_anti₀ (mul_pos (by positivity) (by linarith))
          nlinarith
    have smallsum : (∑ p ∈ s.filter (fun p => p ≤ k), f p) ≤ (Real.sqrt m)⁻¹ := by
      calc
        _ ≤ ∑ p ∈ s.filter (fun p => p ≤ k), (m : ℝ)⁻¹ :=
          Finset.sum_le_sum (fun p hp => small p (mem_filter.mp (mem_filter.mp hp).1).2)
        _ ≤ ∑ p ∈ Ioc 0 k, (m : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (fun p hp => mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1,
              (mem_filter.mp hp).2⟩)
            (fun p _ _ => by positivity)
        _ = (k : ℝ) * (m : ℝ)⁻¹ := by simp
        _ ≤ Real.sqrt m * (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg _)) (by positivity)
        _ = (Real.sqrt m)⁻¹ := by
          have hsq := Real.sq_sqrt (Nat.cast_nonneg m)
          have hpos : 0 < Real.sqrt m := by linarith
          field_simp
          nlinarith
    have telescoping (j : ℕ) (hkj : k ≤ j) :
        (∑ p ∈ Ioc k j, 1 / ((p : ℝ) * (p - 1))) = (k : ℝ)⁻¹ - (j : ℝ)⁻¹ := by
      induction j, hkj using Nat.le_induction with
      | base => simp
      | succ j hkj ih =>
        rw [Finset.sum_Ioc_succ_top hkj, ih]
        have hj : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
        push_cast
        field_simp [ne_of_gt hj, ne_of_gt hkR]
        ring
    have largesum : (∑ p ∈ s.filter (fun p => ¬p ≤ k), f p) ≤ (Real.sqrt m - 1)⁻¹ := by
      calc
        _ ≤ ∑ p ∈ s.filter (fun p => ¬p ≤ k), 1 / ((p : ℝ) * (p - 1)) :=
          Finset.sum_le_sum (fun p hp => large p (mem_filter.mp (mem_filter.mp hp).1).2
            (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2)
        _ ≤ ∑ p ∈ Ioc k m, 1 / ((p : ℝ) * (p - 1)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (fun p hp => mem_Ioc.mpr ⟨by simpa using (mem_filter.mp hp).2,
              (mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).2⟩)
            (fun p hp _ => by
              have hp1 : 1 < p := lt_of_le_of_lt hk1 (mem_Ioc.mp hp).1
              have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
              exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (by linarith)))
        _ = (k : ℝ)⁻¹ - (m : ℝ)⁻¹ := telescoping m hkm
        _ ≤ (k : ℝ)⁻¹ := sub_le_self _ (by positivity)
        _ ≤ (Real.sqrt m - 1)⁻¹ := by
          apply inv_anti₀ (by linarith)
          have h := Nat.lt_floor_add_one (Real.sqrt m)
          dsimp [k] at *
          linarith
    have hsum : (∑ p ∈ s, f p) ≤ (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹ := by
      rw [← Finset.sum_filter_add_sum_filter_not s (fun p => p ≤ k)]
      exact add_le_add smallsum largesum
    refine ⟨hsum, ?_⟩
    have hf (p : ℕ) (hp : p ∈ s) : 0 ≤ f p ∧ f p ≤ 1 := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      exact ⟨by dsimp [f]; positivity,
        pow_le_one₀ (by positivity) ((inv_le_one₀ (by positivity)).mpr hp1.le)⟩
    have hupper : delta m ≤ 1 := Finset.prod_le_one
      (fun p hp => sub_nonneg.mpr (hf p hp).2)
      (fun p hp => sub_le_self _ (hf p hp).1)
    have hlower : 1 - (∑ p ∈ s, f p) ≤ delta m := by
      change 1 - (∑ p ∈ s, f p) ≤ ∏ p ∈ s, (1 - f p)
      rw [Finset.prod_one_sub_ordered]
      apply sub_le_sub_left
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_of_le_one_right (hf p hp).1
      exact Finset.prod_le_one
        (fun j hj => sub_nonneg.mpr (hf j (mem_filter.mp hj).1).2)
        (fun j hj => sub_le_self _ (hf j (mem_filter.mp hj).1).1)
    rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith
  -- The finite bounds give a constant Big-O envelope.
  refine ⟨fun m a b hm ha hb hab => squeeze hm ha hb hab,
    fun m hm => (tailbound hm).1, ?_⟩
  refine isBigO_iff.mpr ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
  have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt : 2 ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqrt0 : 0 < Real.sqrt m := by linarith
  have htail : (Real.sqrt m - 1)⁻¹ ≤ 2 * (Real.sqrt m)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by linarith) hsqrt0).mpr
    nlinarith
  have h := (tailbound hm).2
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt0)]
  linarith

#print axioms result

end D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
