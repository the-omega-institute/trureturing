/- GID: D5/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman
   generality: G
   mirror-B: D5/B/S3/Arith/ExponentExchange/RoughPrimeRobinSuffixBellman
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Same-integer Robin suffix maxima with accumulated prefix and exact budget branches. -/

import D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Same-integer Robin scores on the existing finite suffix states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman

open D5.S3.Arith.RobinExponentSwap
open D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

/-- The denominator uses the actual prefix times the represented suffix integer. -/
def robinScore (C y i : ℕ) (t : List ℕ) : ℝ :=
  suffixWeight y i t / Real.log (Real.log ((C * suffixNumber y i t : ℕ) : ℝ))

/-- The finite semantic maximum of the same-integer Robin suffix score. -/
def robinV (C y i b h : ℕ) : ℝ :=
  if hb : 1 ≤ b then
    robinScore C y i (Classical.choose
      (Set.exists_max_image _ (robinScore C y i) (feasible_finite y i b h)
        ⟨[], by simp [Feasible, Ordered, suffixNumber, hb]⟩))
  else 0

/-- A branch updates the actual prefix and divides the remaining integer budget. -/
def robinBranchValues (C y i b h : ℕ) : Finset ℝ := by
  classical
  exact insert (1 / Real.log (Real.log (C : ℝ)))
    (((Finset.Icc 1 h).filter (fun a => prime y i ^ a ≤ b)).image
      (fun a => reciprocalGeomSum (prime y i) a *
        robinV (C * prime y i ^ a) y (i + 1) (b / prime y i ^ a) a))

private theorem score_cons (C y i a : ℕ) (t : List ℕ) :
    robinScore C y i (a :: t) = reciprocalGeomSum (prime y i) a *
      robinScore (C * prime y i ^ a) y (i + 1) t := by
  simp only [robinScore, suffixWeight, suffixNumber, Nat.mul_assoc]
  ring

private theorem maximum_spec (C y i b h : ℕ) (hb : 1 ≤ b) :
    ∃ t : List ℕ, Feasible y i b h t ∧ robinScore C y i t = robinV C y i b h ∧
      ∀ u : List ℕ, Feasible y i b h u → robinScore C y i u ≤ robinV C y i b h := by
  let ex := Set.exists_max_image _ (robinScore C y i) (feasible_finite y i b h)
    ⟨[], by simp [Feasible, Ordered, suffixNumber, hb]⟩
  have ht := Classical.choose_spec ex
  refine ⟨Classical.choose ex, ht.1, ?_, ?_⟩
  · simp only [robinV, dite_eq_left hb]
  · intro u hu
    simpa only [robinV, dite_eq_left hb] using ht.2 u hu

private theorem feasible_cons (y i b h a : ℕ) (t : List ℕ) :
    Feasible y i b h (a :: t) ↔ 1 ≤ a ∧ a ≤ h ∧ prime y i ^ a ≤ b ∧
      Feasible y (i + 1) (b / prime y i ^ a) a t := by
  have htpos := (suffix_prime_factors y (i + 1) t).1
  have hp : 0 < prime y i ^ a := pow_pos (Nat.prime_nth_prime _).pos _
  constructor
  · rintro ⟨⟨ha, hah, htail⟩, hbudget⟩
    refine ⟨ha, hah, ?_, htail, ?_⟩
    · simp only [suffixNumber] at hbudget
      nlinarith
    · simp only [suffixNumber] at hbudget
      exact (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hbudget)
  · rintro ⟨ha, hah, _, htail, hbudget⟩
    refine ⟨⟨ha, hah, htail⟩, ?_⟩
    simpa only [suffixNumber, Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).1 hbudget

/-- Exact nonlinear branches, all feasible upper bounds, an actual attaining
suffix, and strict budget descent. No sign assumption on a logarithm is needed
for this finite recurrence. -/
theorem robin_bellman_complete (C y i b h : ℕ) (hb : 1 ≤ b) :
    robinV C y i b h = (robinBranchValues C y i b h).max' (by
      classical
      exact ⟨_, Finset.mem_insert_self _ _⟩) ∧
    (∀ t : List ℕ, Feasible y i b h t → robinScore C y i t ≤ robinV C y i b h) ∧
    (∃ t : List ℕ, Feasible y i b h t ∧ robinScore C y i t = robinV C y i b h) ∧
    (∀ a : ℕ, 1 ≤ a → prime y i ^ a ≤ b → b / prime y i ^ a < b) := by
  classical
  obtain ⟨t, ht, htV, htupper⟩ := maximum_spec C y i b h hb
  let terminal : ℝ := 1 / Real.log (Real.log (C : ℝ))
  have hbase : terminal ∈ robinBranchValues C y i b h := Finset.mem_insert_self _ _
  have hG (a : ℕ) : 0 ≤ reciprocalGeomSum (prime y i) a := by
    unfold reciprocalGeomSum
    positivity
  have hbranch (a : ℕ) (ha : 1 ≤ a) (hah : a ≤ h) (hab : prime y i ^ a ≤ b) :
      reciprocalGeomSum (prime y i) a *
        robinV (C * prime y i ^ a) y (i + 1) (b / prime y i ^ a) a ∈
          robinBranchValues C y i b h := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha, hah⟩, hab⟩, rfl⟩
  have hbranch_le (a : ℕ) (ha : 1 ≤ a) (hah : a ≤ h) (hab : prime y i ^ a ≤ b) :
      reciprocalGeomSum (prime y i) a *
        robinV (C * prime y i ^ a) y (i + 1) (b / prime y i ^ a) a ≤
          robinV C y i b h := by
    have hc : 1 ≤ b / prime y i ^ a :=
      Nat.div_pos hab (pow_pos (Nat.prime_nth_prime _).pos _)
    obtain ⟨u, hu, huV, _⟩ := maximum_spec (C * prime y i ^ a) y (i + 1)
      (b / prime y i ^ a) a hc
    have hjoin := (feasible_cons y i b h a u).2 ⟨ha, hah, hab, hu⟩
    calc
      _ = robinScore C y i (a :: u) := by rw [score_cons, huV]
      _ ≤ robinV C y i b h := htupper _ hjoin
  have hmax_le : (robinBranchValues C y i b h).max' ⟨terminal, hbase⟩ ≤
      robinV C y i b h := by
    apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa [robinScore, suffixWeight, suffixNumber, terminal] using
        htupper [] (by simp [Feasible, Ordered, suffixNumber, hb])
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨haa, hab⟩ := Finset.mem_filter.mp ha
      obtain ⟨haa, hah⟩ := Finset.mem_Icc.mp haa
      exact hbranch_le a haa hah hab
  have hV_le : robinV C y i b h ≤
      (robinBranchValues C y i b h).max' ⟨terminal, hbase⟩ := by
    rw [← htV]
    cases t with
    | nil =>
        simpa [robinScore, suffixWeight, suffixNumber, terminal] using
          (Finset.le_max' (s := robinBranchValues C y i b h) terminal hbase)
    | cons a u =>
        obtain ⟨ha, hah, hab, hu⟩ := (feasible_cons y i b h a u).1 ht
        have hc : 1 ≤ b / prime y i ^ a :=
          Nat.div_pos hab (pow_pos (Nat.prime_nth_prime _).pos _)
        obtain ⟨_, _, _, huupper⟩ := maximum_spec (C * prime y i ^ a) y (i + 1)
          (b / prime y i ^ a) a hc
        rw [score_cons]
        exact (mul_le_mul_of_nonneg_left (huupper u hu) (hG a)).trans
          (Finset.le_max' (s := robinBranchValues C y i b h) _ (hbranch a ha hah hab))
  exact ⟨le_antisymm hV_le hmax_le, htupper, ⟨t, ht, htV⟩,
    (bellman_complete y i b h hb).2.2.2⟩

/-- Every rough integer in a finite budget is bounded by the same-integer root
maximum. The old sigma maximizer is used at the individual budget `n`, so its
representative is no larger than `n` and its Robin denominator cannot increase. -/
theorem rough_robin_bound {C y B n : ℕ} (hC : 3 ≤ C) (hy : 1 ≤ y)
    (hn : 1 ≤ n) (hnB : n ≤ B) (hrough : Rough y n) :
    ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
        Real.log (Real.log ((C * n : ℕ) : ℝ)) ≤
      robinV C y 0 B (rootCap y B) := by
  classical
  have hB : 1 ≤ B := hn.trans hnB
  obtain ⟨_, _, _, _, ⟨m, t, hm1, hmn, _, ht, htm, htU⟩, _⟩ :=
    rough_prime_suffix_complete y n hy hn
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ suffixWeight y 0 t := by
    rw [htU]
    simp only [U, dite_eq_left hn]
    apply Finset.le_max'
    exact Finset.mem_image.mpr
      ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, le_rfl⟩, hrough⟩, rfl⟩
  have order_mono (k l : ℕ) (u : List ℕ) (hu : Ordered k u) (hkl : k ≤ l) :
      Ordered l u := by
    cases u with
    | nil => trivial
    | cons a u => exact ⟨hu.1, hu.2.1.trans hkl, hu.2.2⟩
  have htB : Feasible y 0 B (rootCap y B) t :=
    ⟨order_mono _ _ t ht.1 (Nat.log_mono_right hnB), ht.2.trans hnB⟩
  have hCm : 3 ≤ C * m := hC.trans (Nat.le_mul_of_pos_right C hm1)
  have hCmpos : (0 : ℝ) < (C * m : ℕ) := by exact_mod_cast (by omega : 0 < C * m)
  have hlogm : 1 < Real.log ((C * m : ℕ) : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hCmpos).mpr
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hCm)
  have hdenpos : 0 < Real.log (Real.log ((C * m : ℕ) : ℝ)) := Real.log_pos hlogm
  have hden : Real.log (Real.log ((C * m : ℕ) : ℝ)) ≤
      Real.log (Real.log ((C * n : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) (Real.log_le_log hCmpos
      (by exact_mod_cast Nat.mul_le_mul_left C hmn))
  have hsig : 0 ≤ (ArithmeticFunction.sigma 1 n : ℝ) / n := by positivity
  calc
    _ ≤ ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
        Real.log (Real.log ((C * m : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hsig hdenpos hden
    _ ≤ suffixWeight y 0 t / Real.log (Real.log ((C * m : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right hratio hdenpos.le
    _ = robinScore C y 0 t := by rw [robinScore, htm]
    _ ≤ robinV C y 0 B (rootCap y B) :=
      (robin_bellman_complete C y 0 B (rootCap y B) hB).2.1 t htB

#print axioms robin_bellman_complete
#print axioms rough_robin_bound

end D5.S3.Arith.ExponentExchange.RoughPrimeRobinSuffixBellman
