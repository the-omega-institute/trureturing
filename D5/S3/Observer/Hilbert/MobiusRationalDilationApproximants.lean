/- GID: D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/MobiusRationalDilationApproximants
   mirror-E: none(waiver:universal-finite-error-identity)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: Rational Mobius dilations have exact finite squared error. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound

/-!
Finite explicit Möbius rational-dilation approximants.

The dictionary `phi (n/k)` uses literal rational parameters before coercion
into `ℝ`. The finite Möbius floor cancellation gives the half-open block
recurrence. Pairwise disjoint blocks have squared integral one, yielding
the exact squared error `1 / S N` on `Set.Ioo 0 1` for every `N ≥ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants

open Set
open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## Literal dictionary and finite coefficients -/

def muQ (k : ℕ) : ℚ := (ArithmeticFunction.moebius k : ℚ)

def muR (k : ℕ) : ℝ := (muQ k : ℝ)

/-- The literal atom `({αu} - u) / u`, with `α` a rational parameter. -/
def phi (α : ℚ) (u : ℝ) : ℝ :=
  (Int.fract ((α : ℝ) * u) - u) / u

/-- Rational Möbius coefficient `m_n = ∑_{1≤k≤n} μ(k)/k`, written with a
range so that the successor recurrence is supplied directly by
`Finset.sum_range_succ`. -/
def m (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n,
    muQ (j + 1) / ((j + 1 : ℕ) : ℚ)

private def M (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, muQ (j + 1)

private def A (n : ℕ) : ℚ := (n : ℚ) * m n - M n

/-! ## Pointwise functions -/

def H (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    muR (j + 1) * phi ((n : ℚ) / ((j + 1 : ℕ) : ℚ)) u

def floorMoebiusSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n,
    muR (j + 1) *
      (Int.floor
        ((((n : ℚ) / ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) * u) : ℝ)

def indicatorThreshold (n : ℕ) (u : ℝ) : ℝ :=
  if 1 ≤ (n : ℝ) * u then 1 else 0

/-- The half-open block `u⁻¹ 1_[1/(n+1),1/n)`. -/
def e (n : ℕ) (u : ℝ) : ℝ :=
  u⁻¹ * (Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))).indicator
    (fun _ : ℝ => (1 : ℝ)) u

def S (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, (m (j + 1)) ^ 2

def F (N : ℕ) (u : ℝ) : ℝ :=
  (S N : ℝ)⁻¹ *
    ∑ j ∈ Finset.range N,
      (m (j + 1) : ℝ) * (H (j + 2) u - H (j + 1) u)

/-! ## Source proofs of finite arithmetic and algebraic identities -/

private theorem m_one : m 1 = 1 := by
  simp [m, muQ]

private theorem m_succ (n : ℕ) :
    m (n + 1) = m n + muQ (n + 1) / ((n + 1 : ℕ) : ℚ) := by
  simp [m, Finset.sum_range_succ]

private theorem M_succ (n : ℕ) :
    M (n + 1) = M n + muQ (n + 1) := by
  simp [M, Finset.sum_range_succ]

private theorem A_succ_sub (n : ℕ) : A (n + 1) - A n = m n := by
  have hq : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  simp only [A, m_succ, M_succ, Nat.cast_add, Nat.cast_one]
  field_simp [hq]; ring

private theorem phi_floor_form (α : ℚ) {u : ℝ} (hu : u ≠ 0) :
    phi α u = (α : ℝ) - 1 -
      (Int.floor ((α : ℝ) * u) : ℝ) / u := by
  rw [phi, Int.fract]
  field_simp [hu]; ring

/-! ## Actual finite floor bridge

The next lemmas are the finite arithmetic bridge.  The only convolution
input is the canonical Möbius--zeta identity supplied by Mathlib; the
conversion from real floors to natural division and the cutoff reindexing
are proved here. -/

private theorem floor_mobius_nat_cutoff (x : ℝ) :
    (∑ k ∈ Finset.Ioc 0 (Nat.floor x),
      muR k * ((Nat.floor (x / (k : ℝ)) : ℕ) : ℝ)) =
      if 1 ≤ x then 1 else 0 := by
  by_cases hx : 1 ≤ x
  · simpa only [ite_eq_left hx, muR, muQ, Rat.cast_intCast] using
      D5.S3.Arith.MoebiusLogarithmic.floor_cancellation hx
  · have hfloor : Nat.floor x = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hx)
    simp [hfloor, hx]

private theorem floor_term_nat (n k : ℕ) {u : ℝ} (hk : 0 < k) (hu : 0 < u) :
    (Int.floor ((((n : ℚ) / ((k : ℕ) : ℚ) : ℚ) : ℝ) * u) : ℝ) =
      ((Nat.floor (((n : ℝ) * u) / (k : ℝ)) : ℕ) : ℝ) := by
  have hcast :
      ((((n : ℚ) / ((k : ℕ) : ℚ) : ℚ) : ℝ) * u) =
        ((n : ℝ) * u) / (k : ℝ) := by
    norm_num [Rat.cast_div, Rat.cast_natCast, div_eq_mul_inv]
    ring
  rw [hcast]
  have hx : 0 ≤ ((n : ℝ) * u) / (k : ℝ) := by positivity
  exact (natCast_floor_eq_intCast_floor hx).symm

private theorem sum_range_succ_to_Ioc (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, f (j + 1)) = ∑ k ∈ Finset.Ioc 0 n, f k := by
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ioc]
    omega
  · intro j hj k hk h
    omega
  · intro k hk
    simp only [Finset.mem_Ioc] at hk
    refine ⟨k - 1, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intro j hj
    rfl

theorem floor_moebius_bridge :
    ∀ {n : ℕ} {u : ℝ}, 0 < n → u ∈ Set.Ioo 0 1 →
      floorMoebiusSum n u = indicatorThreshold n u := by
  intro n u hn hu
  let x : ℝ := (n : ℝ) * u
  let q : ℕ := Nat.floor x
  have hx0 : 0 < x := by
    dsimp [x]
    exact mul_pos (by exact_mod_cast hn) hu.1
  have hxn : x < (n : ℝ) := by
    dsimp [x]
    exact (mul_lt_mul_of_pos_left hu.2 (by exact_mod_cast hn)).trans_eq
      (mul_one (n : ℝ))
  have hqle : q ≤ n := by
    dsimp [q]
    have hq_lt : Nat.floor x < n :=
      (Nat.floor_lt (le_of_lt hx0)).mpr hxn
    exact hq_lt.le
  have hfloor : floorMoebiusSum n u =
      ∑ j ∈ Finset.range n,
        muR (j + 1) * ((q / (j + 1) : ℕ) : ℝ) := by
    simp only [floorMoebiusSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [floor_term_nat (n := n) (k := j + 1) (by omega) hu.1]
    dsimp [x, q]
    rw [Nat.floor_div_natCast]
  rw [hfloor, sum_range_succ_to_Ioc (fun k => muR k * ((q / k : ℕ) : ℝ)) n]
  have hsub : Finset.Ioc 0 q ⊆ Finset.Ioc 0 n := by
    intro k hk
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1, (Finset.mem_Ioc.mp hk).2.trans hqle⟩
  have hzero : ∀ k ∈ Finset.Ioc 0 n, k ∉ Finset.Ioc 0 q →
      muR k * ((q / k : ℕ) : ℝ) = 0 := by
    intro k hk hkq
    have hqk : q < k := by
      exact lt_of_not_ge (fun h => hkq (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hk).1, h⟩))
    simp [Nat.div_eq_of_lt hqk]
  rw [← Finset.sum_subset hsub hzero]
  simpa only [indicatorThreshold, x, q, Nat.floor_div_natCast] using
    floor_mobius_nat_cutoff x

private def AReal (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    muR (j + 1) *
      ((((n : ℚ) / ((j + 1 : ℕ) : ℚ) : ℚ) : ℝ) - 1)

private theorem H_eq_AReal_sub_floor (n : ℕ) {u : ℝ} (hu : u ≠ 0) :
    H n u = AReal n - floorMoebiusSum n u / u := by
  classical
  simp only [H, AReal, floorMoebiusSum]
  simp_rw [phi_floor_form _ hu]
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-! The real and rational coefficient definitions are definitionally the same
finite sum after the rational casts are expanded. -/
private theorem a_realization : ∀ n : ℕ, AReal n = (A n : ℝ) := by
  intro n
  simp only [AReal, A, m, M, Rat.cast_sub, Rat.cast_mul, Rat.cast_sum,
    Rat.cast_div, Rat.cast_natCast, muR, muQ]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem H_eq_A_sub_indicator
    {n : ℕ} {u : ℝ} (hn : 0 < n) (hu : u ∈ Set.Ioo 0 1) :
    H n u = (A n : ℝ) - u⁻¹ * indicatorThreshold n u := by
  have hu0 : u ≠ 0 := ne_of_gt hu.1
  rw [H_eq_AReal_sub_floor n hu0, a_realization n, floor_moebius_bridge hn hu]
  field_simp [hu0]

private theorem indicatorThreshold_eq {n : ℕ} (hn : 0 < n) (u : ℝ) :
    indicatorThreshold n u = if 1 / (n : ℝ) ≤ u then 1 else 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiff : 1 ≤ (n : ℝ) * u ↔ 1 / (n : ℝ) ≤ u := by
    rw [div_le_iff₀ hnR]
    simp only [mul_comm]
  simp only [indicatorThreshold, hiff]

/-! The exact endpoint step is separated from the algebraic recurrence.  This
keeps `[1/(n+1),1/n)` explicit and makes the n=1 boundary visible. -/
private theorem indicator_step :
    ∀ {n : ℕ} {u : ℝ}, 1 ≤ n → u ∈ Set.Ioo 0 1 →
      indicatorThreshold (n + 1) u - indicatorThreshold n u =
        (Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))).indicator
          (fun _ : ℝ => (1 : ℝ)) u := by
  intro n u hn hu
  rw [indicatorThreshold_eq (n := n + 1) (by omega) u,
    indicatorThreshold_eq (n := n) (by omega) u]
  by_cases hlo : 1 / ((n + 1 : ℕ) : ℝ) ≤ u
  · by_cases hup : u < 1 / ((n : ℕ) : ℝ)
    · have hnnot : ¬1 / ((n : ℕ) : ℝ) ≤ u := not_le_of_gt hup
      simp only [Set.indicator, Set.mem_Ico, hlo, hup, hnnot,
        ite_true, ite_false, and_self, sub_zero]
    · have hnle : 1 / ((n : ℕ) : ℝ) ≤ u := le_of_not_gt hup
      simp only [Set.indicator, Set.mem_Ico, hlo, hup, hnle,
        ite_true, ite_false, and_false, sub_self]
  · have hnlower : ¬1 / ((n + 1 : ℕ) : ℝ) ≤ u := hlo
    have hupper : ¬1 / ((n : ℕ) : ℝ) ≤ u := by
      intro huper
      have hlt : 1 / ((n + 1 : ℕ) : ℝ) < 1 / ((n : ℕ) : ℝ) := by
        apply one_div_lt_one_div_of_lt
        · exact_mod_cast (show 0 < n by omega)
        · exact_mod_cast Nat.lt_succ_self n
      exact hnlower (hlt.le.trans huper)
    simp only [Set.indicator, Set.mem_Ico, hlo, hupper,
      ite_false, false_and, sub_self]

theorem h_step
    {n : ℕ} {u : ℝ}
    (hn : 1 ≤ n) (hu : u ∈ Set.Ioo 0 1) :
    H (n + 1) u - H n u = (m n : ℝ) - e n u := by
  have h1 := H_eq_A_sub_indicator (n := n + 1) (u := u)
    (by omega) hu
  have h0 := H_eq_A_sub_indicator (n := n) (u := u)
    (by omega) hu
  have hA' : ((A (n + 1) : ℚ) : ℝ) - (A n : ℝ) = (m n : ℝ) := by
    exact_mod_cast A_succ_sub n
  rw [h1, h0]
  calc
    _ = ((A (n + 1) : ℝ) - (A n : ℝ)) -
        u⁻¹ * (indicatorThreshold (n + 1) u - indicatorThreshold n u) := by ring
    _ = (m n : ℝ) - e n u := by rw [hA', indicator_step hn hu]; rfl

private theorem e_sq_indicator (n : ℕ) (u : ℝ) :
    (e n u) ^ 2 =
      (Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))).indicator
        (fun v : ℝ => v⁻¹ ^ 2) u := by
  by_cases hu : u ∈ Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))
  · simp only [e, Set.indicator_of_mem hu, mul_one]
  · simp only [e, Set.indicator_of_notMem hu, mul_zero, zero_pow (by omega : 2 ≠ 0)]

theorem block_integral {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in Set.Ioo (0 : ℝ) 1, (e n u) ^ 2) = 1 := by
  have hn0 : 0 < n := by omega
  let a : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  let b : ℝ := 1 / ((n : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast (Nat.le_succ n)
  have hb1 : b ≤ 1 := by
    dsimp [b]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n)]
    norm_num
    exact_mod_cast hn
  have hset : Set.Ico a b ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨ha.trans_le hu.1, hu.2.trans_le hb1⟩
  calc
    (∫ u in Set.Ioo (0 : ℝ) 1, (e n u) ^ 2) =
        ∫ u in Set.Ioo (0 : ℝ) 1,
          (Set.Ico a b).indicator (fun v : ℝ => v⁻¹ ^ 2) u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simpa [a, b] using e_sq_indicator n u
    _ = ∫ u in Set.Ioo (0 : ℝ) 1 ∩ Set.Ico a b, (fun v : ℝ => v⁻¹ ^ 2) u := by
      rw [setIntegral_indicator measurableSet_Ico]
    _ = ∫ u in Set.Ico a b, (fun v : ℝ => v⁻¹ ^ 2) u := by
      rw [inter_eq_right.mpr hset]
    _ = ∫ u in a..b, (fun v : ℝ => v⁻¹ ^ 2) u := by
      rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    _ = ∫ u in a..b, u ^ (-2 : ℤ) := by
      congr 1
      funext u
      simp [zpow_neg, zpow_ofNat]
    _ = (b ^ (-1 : ℤ) - a ^ (-1 : ℤ)) / (-1 : ℝ) := by
      convert _root_.integral_zpow (a := a) (b := b) (n := (-2 : ℤ))
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha (ha.trans_le hab)⟩) using 1 <;>
        norm_num
    _ = 1 := by
      dsimp [a, b]
      simp only [zpow_neg_one, one_div, inv_inv, Nat.cast_add, Nat.cast_one]
      ring

private theorem block_mul_eq_zero {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    ∀ u : ℝ, e m u * e n u = 0 := by
    intro u
    rcases lt_or_gt_of_ne hmn with hmn' | hnm'
    · by_cases hmset : u ∈ Set.Ico (1 / ((m + 1 : ℕ) : ℝ)) (1 / ((m : ℕ) : ℝ))
      · by_cases hnset : u ∈ Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))
        · have hnm : 1 / ((n : ℕ) : ℝ) ≤
              1 / ((m + 1 : ℕ) : ℝ) := by
            apply one_div_le_one_div_of_le
            · positivity
            · exact_mod_cast (Nat.succ_le_of_lt hmn')
          exfalso
          exact (not_lt_of_ge hnm) (lt_of_le_of_lt hmset.1 hnset.2)
        · simp only [e, Set.indicator_of_notMem hnset, mul_zero]
      · simp only [e, Set.indicator_of_notMem hmset, mul_zero, zero_mul]
    · by_cases hmset : u ∈ Set.Ico (1 / ((m + 1 : ℕ) : ℝ)) (1 / ((m : ℕ) : ℝ))
      · by_cases hnset : u ∈ Set.Ico (1 / ((n + 1 : ℕ) : ℝ)) (1 / ((n : ℕ) : ℝ))
        · have hmnle : 1 / ((m : ℕ) : ℝ) ≤
              1 / ((n + 1 : ℕ) : ℝ) := by
            apply one_div_le_one_div_of_le
            · positivity
            · exact_mod_cast (Nat.succ_le_of_lt hnm')
          exfalso
          exact (not_lt_of_ge hmnle) (lt_of_le_of_lt hnset.1 hmset.2)
        · simp only [e, Set.indicator_of_notMem hnset, mul_zero]
      · simp only [e, Set.indicator_of_notMem hmset, mul_zero, zero_mul]

theorem block_orthogonality {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    (∫ u in Set.Ioo (0 : ℝ) 1, e m u * e n u) = 0 := by
  simp_rw [block_mul_eq_zero hm hn hmn]
  simp

theorem s_pos {N : ℕ} (hN : 1 ≤ N) : 0 < (S N : ℝ) := by
  have hq : 0 < S N := by
    rw [S]
    apply Finset.sum_pos'
    · intro j hj
      exact sq_nonneg (m (j + 1))
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      simp [m_one]
  exact_mod_cast hq

private theorem block_sq_integrable {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun u : ℝ => (e n u) ^ 2) volume := by
  let a : ℝ := 1 / ((n + 1 : ℕ) : ℝ)
  let b : ℝ := 1 / ((n : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : ContinuousOn (fun u : ℝ => u⁻¹ ^ 2) (Icc a b) := by
    intro u hu
    exact ((continuousAt_id.inv₀ (ne_of_gt (ha.trans_le hu.1))).pow 2).continuousWithinAt
  have hi : IntegrableOn (fun u : ℝ => u⁻¹ ^ 2) (Set.Ico a b) volume :=
    hc.integrableOn_Icc.mono_set (fun u hu => ⟨hu.1, hu.2.le⟩)
  have hind := hi.integrable_indicator measurableSet_Ico
  have heq : (fun u : ℝ => (e n u) ^ 2) =
      (Set.Ico a b).indicator (fun u : ℝ => u⁻¹ ^ 2) := by
    funext u
    exact e_sq_indicator n u
  rw [heq]
  exact hind

private theorem error_pointwise {N : ℕ} {u : ℝ} (hN : 1 ≤ N) (hu : u ∈ Set.Ioo 0 1) :
    1 - F N u = (S N : ℝ)⁻¹ *
      ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) * e (j + 1) u := by
  have hS : (S N : ℝ) =
      ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 := by
    simp only [S, Rat.cast_sum, Rat.cast_pow]
  have hsum :
      (∑ j ∈ Finset.range N,
        (m (j + 1) : ℝ) * (H (j + 2) u - H (j + 1) u)) =
      (S N : ℝ) -
        ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) * e (j + 1) u := by
    rw [hS, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [h_step (n := j + 1) (by omega) hu]
    ring
  rw [F, hsum]
  have hS0 : (S N : ℝ) ≠ 0 := ne_of_gt (s_pos hN)
  field_simp [hS0]; ring

private theorem weighted_block_sum_sq (N : ℕ) (u : ℝ) :
    (∑ j ∈ Finset.range N, (m (j + 1) : ℝ) * e (j + 1) u) ^ 2 =
      ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · ring
  · intro j hj hji
    have hzero := block_mul_eq_zero (m := i + 1) (n := j + 1)
      (by omega) (by omega) (by omega) u
    calc
      _ = ((m (i + 1) : ℝ) * (m (j + 1) : ℝ)) *
        (e (i + 1) u * e (j + 1) u) := by ring
      _ = 0 := by rw [hzero]; simp
  · intro hnot
    exact (hnot hi).elim

theorem error_sq_integrable {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => (1 - F N u) ^ 2) (Set.Ioo (0 : ℝ) 1) volume := by
  have hint (j : ℕ) :
      Integrable (fun u : ℝ =>
        (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((block_sq_integrable (n := j + 1) (by omega)).const_mul _).integrableOn
  have hi := (integrable_finsetSum (Finset.range N) (fun j hj => hint j)).const_mul
    ((S N : ℝ)⁻¹ ^ 2)
  apply IntegrableOn.congr_fun hi ?_ measurableSet_Ioo
  intro u hu
  change (S N : ℝ)⁻¹ ^ 2 *
      ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2 =
      (1 - F N u) ^ 2
  rw [error_pointwise hN hu, mul_pow, weighted_block_sum_sq]

theorem finite_error {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Set.Ioo (0 : ℝ) 1, (1 - F N u) ^ 2) = (1 : ℝ) / (S N : ℝ) := by
  have hS : (S N : ℝ) =
      ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 := by
    simp only [S, Rat.cast_sum, Rat.cast_pow]
  have hint (j : ℕ) :
      Integrable (fun u : ℝ =>
        (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ((block_sq_integrable (n := j + 1) (by omega)).const_mul _).integrableOn
  calc
    (∫ u in Set.Ioo (0 : ℝ) 1, (1 - F N u) ^ 2) =
        ∫ u in Set.Ioo (0 : ℝ) 1, (S N : ℝ)⁻¹ ^ 2 *
          ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      change (1 - F N u) ^ 2 =
        (S N : ℝ)⁻¹ ^ 2 *
          ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2
      rw [error_pointwise hN hu, mul_pow, weighted_block_sum_sq]
    _ = (S N : ℝ)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range N,
          ∫ u in Set.Ioo (0 : ℝ) 1,
            (m (j + 1) : ℝ) ^ 2 * (e (j + 1) u) ^ 2 := by
      rw [integral_const_mul, integral_finsetSum (Finset.range N) (fun j hj => hint j)]
    _ = (S N : ℝ)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range N, (m (j + 1) : ℝ) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, block_integral (by omega), mul_one]
    _ = (1 : ℝ) / (S N : ℝ) := by
      rw [← hS]
      field_simp [ne_of_gt (s_pos hN)]

end D5.S3.Observer.Hilbert.MobiusRationalDilationApproximants
