/- GID: D5/S3/Arith/FibonacciAtomic/MertensBoundary
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/MertensBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power bounds for the seven-ten boundary and coprime Mertens sums. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Asymptotics

namespace D5.S3.Arith.FibonacciAtomic.MertensBoundary

/-- The Moebius summatory function restricted to integers coprime to the modulus. -/
noncomputable def coprimeMertens (R : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
    if n.Coprime R then (ArithmeticFunction.moebius n : ℝ) else 0

/-- The signed contribution on the real interval from X/10, excluded, to X/7, included. -/
noncomputable def boundary (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X / 10⌋₊ ⌊X / 7⌋₊,
    if n.Coprime 70 then (ArithmeticFunction.moebius n : ℝ) else 0

/-- For every positive exponent, the boundary and the coprime Mertens sum have
exactly the same power growth bound as the ordinary Mertens sum over real truncations. -/
theorem power_bounds_iff (a : ℝ) (ha : 0 < a) :
    (boundary =O[atTop] (fun X : ℝ => X ^ a) ↔
      coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a)) ∧
    (coprimeMertens 70 =O[atTop] (fun X : ℝ => X ^ a) ↔
      coprimeMertens 1 =O[atTop] (fun X : ℝ => X ^ a)) := by
  classical
  let Bound (f : ℝ → ℝ) : Prop :=
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → |f x| ≤ C * x ^ a
  have zero (R : ℕ) (x : ℝ) (hx : x < 1) : coprimeMertens R x = 0 := by
    simp [coprimeMertens, Nat.floor_eq_zero.mpr hx]
  have localBound (R : ℕ) (T : ℝ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ T → |coprimeMertens R x| ≤ B := by
    refine ⟨⌊T⌋₊, Nat.cast_nonneg _, ?_⟩
    intro x hx
    calc
      _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          |if n.Coprime R then (ArithmeticFunction.moebius n : ℝ) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        split_ifs
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        · norm_num
      _ = (⌊x⌋₊ : ℝ) := by simp
      _ ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast Nat.floor_mono hx
  have toBigO (f : ℝ → ℝ) (h : Bound f) : f =O[atTop] (fun x : ℝ => x ^ a) := by
    obtain ⟨C, _, hC⟩ := h
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le a)] using hC x hx
  have fromBigO (f : ℝ → ℝ) (hf0 : ∀ x : ℝ, x < 1 → f x = 0)
      (hloc : ∀ T : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ T → |f x| ≤ B)
      (h : f =O[atTop] (fun x : ℝ => x ^ a)) : Bound f := by
    obtain ⟨C, hC⟩ := isBigO_iff.mp h
    obtain ⟨T, hT⟩ := eventually_atTop.mp hC
    obtain ⟨B, hB, hbound⟩ := hloc T
    refine ⟨max |C| B, le_trans (abs_nonneg C) (le_max_left _ _), ?_⟩
    intro x hx
    by_cases hsmall : x < 1
    · rw [hf0 x hsmall, abs_zero]
      positivity
    by_cases htail : T ≤ x
    · have ht := hT x htail
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hx.le a)] at ht
      exact ht.trans (mul_le_mul_of_nonneg_right
        ((le_abs_self C).trans (le_max_left _ _)) (Real.rpow_nonneg hx.le a))
    · have hp : 1 ≤ x ^ a := Real.one_le_rpow (le_of_not_gt hsmall) ha.le
      calc
        |f x| ≤ B := hbound x (le_of_not_ge htail)
        _ ≤ max |C| B := le_max_right _ _
        _ ≤ max |C| B * x ^ a := le_mul_of_one_le_right
          (le_trans hB (le_max_right _ _)) hp
  have difference (X : ℝ) (hX : 0 ≤ X) :
      boundary X = coprimeMertens 70 (X / 7) - coprimeMertens 70 (X / 10) := by
    have h := Finset.sum_Ioc_consecutive
      (fun n => if n.Coprime 70 then (ArithmeticFunction.moebius n : ℝ) else 0)
      (Nat.zero_le ⌊X / 10⌋₊) (Nat.floor_mono (by linarith : X / 10 ≤ X / 7))
    dsimp [boundary, coprimeMertens]
    linarith
  have boundaryZero (x : ℝ) (hx : x < 1) : boundary x = 0 := by
    have h : x / 7 < 1 := by linarith
    simp [boundary, Nat.floor_eq_zero.mpr h]
  have boundaryLocal (T : ℝ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ T → |boundary x| ≤ B := by
    obtain ⟨B, hB, hb⟩ := localBound 70 (max T 0)
    refine ⟨2 * B, by positivity, ?_⟩
    intro x hx
    by_cases hsmall : x < 1
    · rw [boundaryZero x hsmall, abs_zero]; positivity
    have hx0 : 0 ≤ x := by linarith
    rw [difference x hx0]
    exact (abs_sub _ _).trans (by
      have h7 := hb (x / 7) (by have := le_max_left T 0; linarith)
      have h10 := hb (x / 10) (by have := le_max_left T 0; linarith)
      linarith)
  have contract (f : ℝ → ℝ) (hf0 : ∀ x : ℝ, x < 1 → f x = 0)
      (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
      (hd : Bound (fun x => f x - f (q * x))) : Bound f := by
    obtain ⟨C, hC, hd⟩ := hd
    have hr0 : 0 ≤ q ^ a := Real.rpow_nonneg hq0.le a
    have hr1 : q ^ a < 1 := Real.rpow_lt_one hq0.le hq1 ha
    refine ⟨C / (1 - q ^ a), div_nonneg hC (by linarith), ?_⟩
    intro x hx
    have ht : Tendsto (fun j : ℕ => q ^ j * x) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const x
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
    have telescoping : ∀ n : ℕ,
        (∑ j ∈ Finset.range n, (f (q ^ j * x) - f (q * (q ^ j * x)))) =
          f x - f (q ^ n * x) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        rw [show q * (q ^ n * x) = q ^ (n + 1) * x by ring]
        ring
    have hsum : f x = ∑ j ∈ Finset.range N,
        (f (q ^ j * x) - f (q * (q ^ j * x))) := by
      rw [telescoping, hf0 _ hN, sub_zero]
    rw [hsum]
    calc
      _ ≤ ∑ j ∈ Finset.range N, |f (q ^ j * x) - f (q * (q ^ j * x))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, C * (q ^ j * x) ^ a := by
        exact Finset.sum_le_sum fun j _ => hd _ (mul_pos (pow_pos hq0 j) hx)
      _ = C * x ^ a * ∑ j ∈ Finset.range N, (q ^ a) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Real.mul_rpow (pow_nonneg hq0.le j) hx.le, ← Real.rpow_pow_comm hq0.le]
        ring
      _ ≤ C * x ^ a * (1 / (1 - q ^ a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1)
      _ = C / (1 - q ^ a) * x ^ a := by ring
  have primeDifference (R p : ℕ) (hp : p.Prime) (hpR : p.Coprime R) (x : ℝ) :
      coprimeMertens R x = coprimeMertens (p * R) x -
        coprimeMertens (p * R) (x / p) := by
    let c (S n : ℕ) : ℝ := if n.Coprime S then (ArithmeticFunction.moebius n : ℝ) else 0
    have mult (m : ℕ) : c R (p * m) = - c (p * R) m := by
      by_cases hmR : m.Coprime R
      · by_cases hpm : p.Coprime m
        · have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hpm
          rw [ArithmeticFunction.moebius_apply_prime hp] at hmu
          have hleft : (p * m).Coprime R := Nat.coprime_mul_iff_left.mpr ⟨hpR, hmR⟩
          have hright : m.Coprime (p * R) := Nat.coprime_mul_iff_right.mpr ⟨hpm.symm, hmR⟩
          simp only [c, if_pos hleft, if_pos hright, hmu, Int.cast_neg, neg_one_mul]
        · have hsq : ¬ Squarefree (p * m) := fun h => hpm (Nat.coprime_of_squarefree_mul h)
          have hright : ¬ m.Coprime (p * R) := fun h =>
            hpm (Nat.coprime_mul_iff_right.mp h).1.symm
          simp [c, hright, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      · simp [c, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, hmR]
    have coefficient (n : ℕ) :
        c R n = c (p * R) n - (if p ∣ n then c (p * R) (n / p) else 0) := by
      by_cases hd : p ∣ n
      · obtain ⟨m, rfl⟩ := hd
        have hnot : ¬ (p * m).Coprime p := by
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          simp
        simpa [c, Nat.coprime_mul_iff_right, hnot, hp.ne_zero] using mult m
      · have hc : n.Coprime p := (hp.coprime_iff_not_dvd.mpr hd).symm
        have he : n.Coprime (p * R) ↔ n.Coprime R :=
          Nat.coprime_mul_iff_right.trans (and_iff_right hc)
        simp only [c, he, if_neg hd, sub_zero]
    have multiples (N : ℕ) :
        (∑ n ∈ Finset.Ioc 0 N, if p ∣ n then c (p * R) (n / p) else 0) =
          ∑ m ∈ Finset.Ioc 0 (N / p), c (p * R) m := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun n _ => n / p) ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) hp.pos,
          Nat.div_le_div_right hnN⟩
      · intro n hn m hm heq
        have hn' := (Finset.mem_filter.mp hn).2
        have hm' := (Finset.mem_filter.mp hm).2
        have := congrArg (fun k => p * k) heq
        simpa [Nat.mul_div_cancel' hn', Nat.mul_div_cancel' hm'] using this
      · intro m hm
        obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hm
        refine ⟨p * m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨
          Nat.mul_pos hp.pos hm0, ?_⟩, dvd_mul_right p m⟩, ?_⟩
        · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hmN
        · simp [hp.ne_zero]
      · intro n hn
        rfl
    simp only [coprimeMertens, Nat.floor_div_natCast]
    change (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c R n) =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, c (p * R) n) -
        ∑ n ∈ Finset.Ioc 0 (⌊x⌋₊ / p), c (p * R) n
    simp_rw [coefficient]
    rw [Finset.sum_sub_distrib, multiples]
  have primeTransfer (R p : ℕ) (hp : p.Prime) (hpR : p.Coprime R) :
      (coprimeMertens (p * R) =O[atTop] (fun X : ℝ => X ^ a)) ↔
        coprimeMertens R =O[atTop] (fun X : ℝ => X ^ a) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    constructor
    · intro h
      obtain ⟨C, hC, hm⟩ := fromBigO _ (zero (p * R)) (localBound (p * R)) h
      apply toBigO
      refine ⟨2 * C, by positivity, ?_⟩
      intro x hx
      rw [primeDifference R p hp hpR x]
      have hscale : (x / p) ^ a ≤ x ^ a := Real.rpow_le_rpow
        (by positivity) ((div_le_self hx.le (by linarith))) ha.le
      calc
        _ ≤ |coprimeMertens (p * R) x| + |coprimeMertens (p * R) (x / p)| := abs_sub _ _
        _ ≤ C * x ^ a + C * (x / p) ^ a := add_le_add (hm x hx) (hm _ (by positivity))
        _ ≤ C * x ^ a + C * x ^ a := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hscale hC)
        _ = 2 * C * x ^ a := by ring
    · intro h
      obtain ⟨C, hC, hm⟩ := fromBigO _ (zero R) (localBound R) h
      apply toBigO
      apply contract _ (zero (p * R)) (1 / p) (by positivity) ((div_lt_one hp0).mpr hp1)
      refine ⟨C, hC, ?_⟩
      intro x hx
      simpa only [one_div_mul_eq_div, ← primeDifference R p hp hpR x] using hm x hx
  constructor
  · constructor
    · intro h
      obtain ⟨C, hC, hb⟩ := fromBigO boundary boundaryZero boundaryLocal h
      apply toBigO
      apply contract (coprimeMertens 70) (zero 70) (7 / 10) (by norm_num) (by norm_num)
      refine ⟨C * 7 ^ a, by positivity, ?_⟩
      intro x hx
      have h := hb (7 * x) (by positivity)
      rw [difference _ (by positivity)] at h
      have e7 : 7 * x / 7 = x := by ring
      have e10 : 7 * x / 10 = (7 / 10) * x := by ring
      rw [e7, e10, Real.mul_rpow (by norm_num) hx.le] at h
      simpa [mul_assoc] using h
    · intro h
      obtain ⟨C, hC, hm⟩ := fromBigO (coprimeMertens 70) (zero 70) (localBound 70) h
      apply toBigO
      refine ⟨2 * C, by positivity, ?_⟩
      intro x hx
      rw [difference x hx.le]
      have h7 := hm (x / 7) (by positivity)
      have h10 := hm (x / 10) (by positivity)
      have hp7 : (x / 7) ^ a ≤ x ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
      have hp10 : (x / 10) ^ a ≤ x ^ a := Real.rpow_le_rpow (by positivity) (by linarith) ha.le
      calc
        _ ≤ |coprimeMertens 70 (x / 7)| + |coprimeMertens 70 (x / 10)| := abs_sub _ _
        _ ≤ C * (x / 7) ^ a + C * (x / 10) ^ a := add_le_add h7 h10
        _ ≤ C * x ^ a + C * x ^ a := add_le_add
          (mul_le_mul_of_nonneg_left hp7 hC) (mul_le_mul_of_nonneg_left hp10 hC)
        _ = 2 * C * x ^ a := by ring
  · have h2 := primeTransfer 1 2 (by decide) (by decide)
    have h5 := primeTransfer 2 5 (by decide) (by decide)
    have h7 := primeTransfer 10 7 (by decide) (by decide)
    norm_num only [Nat.mul_one, Nat.reduceMul] at h2 h5 h7
    exact h7.trans (h5.trans h2)

#print axioms power_bounds_iff

end D5.S3.Arith.FibonacciAtomic.MertensBoundary
