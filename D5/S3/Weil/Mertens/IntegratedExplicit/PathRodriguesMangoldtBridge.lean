/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PathRodriguesMangoldtBridge
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: The path Rodrigues coefficient LCM gives a cofinal gamma threshold for RH. -/

import D5.S3.Arith.FactorialRatio.PathRodriguesGcd
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The path Rodrigues coefficient LCM and the complete Mangoldt remainder

At integer scale `x = s + 1`, the coefficient-content LCM complements
the exact path moment gcd inside `(s!)^r`. Counting the incidences in the
tail at `r*x - 1` gives a nonnegative weighted ceiling error.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge

open Finset Filter
open scoped Nat Topology
open D5.S3.Arith.FactorialRatio.PathRodriguesGcd (B C F B_mul_C C_ne_zero exact_path_rodrigues_gcd)
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd (tail_nonzero)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
  (rh_iff_pointwise_sqrt_windows)
open D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
  (exists_quartic_block_in_power_window rh_iff_quartic_integer_blocks)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass_lt_third)

/-- The LCM of the integral coefficient contents for all orders through `x - 1`. -/
def contentLCM (r x : ℕ) : ℕ := (range x).lcm (C (r - 1) (x - 1))

private theorem tail_mul_contentLCM {r : ℕ} (hr : 2 ≤ r) (s : ℕ) :
    tailLCM (r * (s + 1) - 1) (r - 1) * contentLCM r (s + 1) = (s !)^r := by
  let indices := range (s + 1)
  let A := tailLCM (r * (s + 1) - 1) (r - 1)
  let L := contentLCM r (s + 1)
  let P := (s !)^r
  change A * L = P
  have hL : L = indices.lcm (C (r - 1) s) := by
    simp only [L, contentLCM, indices, Nat.add_sub_cancel]
  have hB (k : ℕ) (hk : k ∈ indices) : B (r - 1) s k * C (r - 1) s k = P := by
    have hks : k ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simpa only [P, F, Nat.sub_add_cancel (show 1 ≤ r by omega)] using
      (B_mul_C (n := r - 1) hks)
  have hG : indices.gcd (B (r - 1) s) = A := exact_path_rodrigues_gcd hr s
  have hAB (k : ℕ) (hk : k ∈ indices) : A ∣ B (r - 1) s k := by
    rw [← hG]
    exact Finset.gcd_dvd hk
  have h0 : 0 ∈ indices := Finset.mem_range.mpr (Nat.zero_lt_succ s)
  have hAP : A ∣ P := by
    rw [← hB 0 h0]
    exact (hAB 0 h0).trans (dvd_mul_right _ _)
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_div_iff_mul_dvd hAP).mp
    rw [hL]
    apply Finset.lcm_dvd
    intro k hk
    apply (Nat.dvd_div_iff_mul_dvd hAP).mpr
    rw [← hB k hk]
    exact Nat.mul_dvd_mul (hAB k hk) (dvd_refl _)
  · have hgcd : P ∣ indices.gcd (fun k => B (r - 1) s k * L) := by
      apply Finset.dvd_gcd
      intro k hk
      rw [← hB k hk]
      have hkL : C (r - 1) s k ∣ L := by
        rw [hL]
        exact Finset.dvd_lcm hk
      exact Nat.mul_dvd_mul (dvd_refl _) hkL
    rwa [Finset.gcd_mul_right, normalize_eq, hG] at hgcd

/-- Exact coefficient-content LCM in the vertex-count coordinates. -/
theorem contentLCM_eq_factorial_div_tail {r : ℕ} (hr : 2 ≤ r) (s : ℕ) :
    contentLCM r (s + 1) = (s !)^r / tailLCM (r * (s + 1) - 1) (r - 1) := by
  let A := tailLCM (r * (s + 1) - 1) (r - 1)
  have hA : 0 < A := Nat.pos_of_ne_zero (tail_nonzero _ _)
  calc
    _ = (A * contentLCM r (s + 1)) / A := (Nat.mul_div_cancel_left _ hA).symm
    _ = _ := by rw [show A * contentLCM r (s + 1) = (s !)^r from tail_mul_contentLCM hr s]

private theorem ceil_natCast_div {m q : ℕ} (hm : 0 < m) (hq : 0 < q) :
    ⌈(m : ℝ) / (q : ℝ)⌉₊ = (m - 1) / q + 1 := by
  let d := (m - 1) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : d * q ≤ m - 1 := (Nat.le_div_iff_mul_le hq).mp (le_refl d)
  have hhi : m - 1 < (d + 1) * q := (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self d)
  have hlo' : d * q < m := by omega
  have hhi' : m ≤ (d + 1) * q := by omega
  change ⌈(m : ℝ) / (q : ℝ)⌉₊ = d + 1
  apply (Nat.ceil_eq_iff (Nat.succ_ne_zero d)).2
  rw [Nat.succ_sub_one]
  exact ⟨(lt_div_iff₀ hqR).2 (by exact_mod_cast hlo'),
    (div_le_iff₀ hqR).2 (by exact_mod_cast hhi')⟩

/-- Count the incidences `q*k ≤ H` in either order. The cutoff `x` covers
every possible `q` because `k ≥ M + 1`. -/
private theorem log_tailLCM_count (H M x : ℕ) (hx : H / (M + 1) ≤ x) :
    Real.log (tailLCM H M : ℝ) =
      ∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q * ((H / q - M : ℕ) : ℝ) := by
  unfold tailLCM
  rw [Nat.cast_prod, Real.log_prod (fun k _ => Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero _))]
  simp only [← Chebyshev.psi_eq_log_lcmUpto, Chebyshev.psi, Nat.floor_natCast]
  calc
    _ = ∑ k ∈ Ioc M H, ∑ q ∈ Ioc 0 x,
        if q ≤ H / k then ArithmeticFunction.vonMangoldt q else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkM : M + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_Ioc.mp hk).1
      have hcut : H / k ≤ x :=
        (Nat.div_le_div_left hkM (Nat.zero_lt_succ M)).trans hx
      rw [← Finset.sum_filter]
      have heq : (Ioc 0 x).filter (fun q => q ≤ H / k) = Ioc 0 (H / k) := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
      rw [heq]
    _ = ∑ q ∈ Ioc 0 x, ∑ k ∈ Ioc M H,
        if q ≤ H / k then ArithmeticFunction.vonMangoldt q else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq0 := (Finset.mem_Ioc.mp hq).1
      rw [← Finset.sum_filter]
      have heq : (Ioc M H).filter (fun k => q ≤ H / k) = Ioc M (H / q) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hkM, _⟩, hqk⟩
          have hk0 : 0 < k := (Nat.zero_le M).trans_lt hkM
          have hmul := (Nat.le_div_iff_mul_le hk0).mp hqk
          exact ⟨hkM, (Nat.le_div_iff_mul_le hq0).mpr (by simpa [mul_comm] using hmul)⟩
        · rintro ⟨hkM, hkq⟩
          have hk0 : 0 < k := (Nat.zero_le M).trans_lt hkM
          have hmul := (Nat.le_div_iff_mul_le hq0).mp hkq
          exact ⟨⟨hkM, hkq.trans (Nat.div_le_self _ _)⟩,
            (Nat.le_div_iff_mul_le hk0).mpr (by simpa [mul_comm] using hmul)⟩
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, mul_comm]

/-- At the shifted endpoint, the count is exactly `⌈rx/q⌉ - r`. -/
theorem log_tailLCM_eq_sum_vonMangoldt_ceil {r x : ℕ} (hr : 2 ≤ r) (hx : 0 < x) :
    Real.log (tailLCM (r * x - 1) (r - 1) : ℝ) =
      ∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q *
        ((⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ : ℝ) - (r : ℝ)) := by
  have hr0 : 0 < r := by omega
  have hr1 : 1 ≤ r := by omega
  have hcut : (r * x - 1) / ((r - 1) + 1) ≤ x := by
    rw [Nat.sub_add_cancel hr1]
    calc
      _ ≤ (r * x) / r := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = x := Nat.mul_div_cancel_left x hr0
  rw [log_tailLCM_count _ _ _ hcut]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hq0, hqx⟩ := Finset.mem_Ioc.mp hq
  have hceil : ⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ = (r * x - 1) / q + 1 := by
    simpa only [Nat.cast_mul] using ceil_natCast_div (Nat.mul_pos hr0 hx) hq0
  have hcount : (r * x - 1) / q - (r - 1) = ⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ - r := by
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqxR : (q : ℝ) ≤ x := by exact_mod_cast hqx
  have hlo : (r : ℝ) ≤ (r : ℝ) * (x : ℝ) / (q : ℝ) :=
    (le_div_iff₀ hqR).2 (mul_le_mul_of_nonneg_left hqxR (Nat.cast_nonneg r))
  have hrceil : r ≤ ⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ := by
    exact_mod_cast hlo.trans (Nat.le_ceil _)
  rw [hcount, Nat.cast_sub hrceil]

/-- The Mangoldt-weighted sum of the ceiling errors at the integer scale. -/
def ceilingError (r x : ℕ) : ℝ :=
  ∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q *
    ((⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ : ℝ) - (r : ℝ) * (x : ℝ) / (q : ℝ))

/-- The normalized tail logarithm equals the complete finite ramp plus the ceiling error. -/
theorem log_tailLCM_div_eq_mangoldt {r x : ℕ} (hr : 2 ≤ r) (hx : 0 < x) :
    Real.log (tailLCM (r * x - 1) (r - 1) : ℝ) / (r : ℝ) =
      (x : ℝ) * (∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
        Chebyshev.psi (x : ℝ) + ceilingError r x / (r : ℝ) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hsum :
      (∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q *
        ((⌈(r : ℝ) * (x : ℝ) / (q : ℝ)⌉₊ : ℝ) - (r : ℝ))) =
      (r : ℝ) * ((x : ℝ) *
        (∑ q ∈ Ioc 0 x, ArithmeticFunction.vonMangoldt q / (q : ℝ)) -
          Chebyshev.psi (x : ℝ)) + ceilingError r x := by
    rw [Chebyshev.psi, Nat.floor_natCast, ceilingError, mul_sub (r : ℝ), Finset.mul_sum _ _ (x : ℝ),
      Finset.mul_sum _ _ (r : ℝ), Finset.mul_sum _ _ (r : ℝ),
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [log_tailLCM_eq_sum_vonMangoldt_ceil hr hx, hsum, add_div, mul_div_cancel_left₀ _ hrR]

/-- Every individual ceiling error lies between zero and one. -/
theorem ceilingError_bounds (r x : ℕ) :
    0 ≤ ceilingError r x ∧ ceilingError r x ≤ Chebyshev.psi (x : ℝ) := by
  have hround (q : ℕ) :
      let y := (r : ℝ) * (x : ℝ) / (q : ℝ)
      0 ≤ (⌈y⌉₊ : ℝ) - y ∧ (⌈y⌉₊ : ℝ) - y ≤ 1 := by
    dsimp only
    refine ⟨sub_nonneg.mpr (Nat.le_ceil _), ?_⟩
    have hy : 0 ≤ (r : ℝ) * (x : ℝ) / (q : ℝ) := by positivity
    linarith only [Nat.ceil_lt_add_one hy]
  unfold ceilingError
  rw [Chebyshev.psi, Nat.floor_natCast]
  constructor
  · exact Finset.sum_nonneg fun q _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hround q).1
  · apply Finset.sum_le_sum
    intro q _
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hround q).2 ArithmeticFunction.vonMangoldt_nonneg

/-- The centered logarithm of the actual path coefficient-content LCM. -/
def T (r x : ℕ) : ℝ :=
  Real.log ((x - 1)! : ℝ) - (x : ℝ) * Real.log (x : ℝ) +
    (1 + Real.eulerMascheroniConstant) * (x : ℝ) - Real.log (contentLCM r x : ℝ) / (r : ℝ)

/-- The coefficient LCM gives the complete Mangoldt remainder with a positive-signed correction. -/
theorem T_eq_U_add_ceilingError {r x : ℕ} (hr : 2 ≤ r) (hx : 0 < x) :
    T r x = U (x : ℝ) + ceilingError r x / (r : ℝ) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hL : contentLCM r x ≠ 0 := by
    unfold contentLCM
    apply Finset.lcm_ne_zero_iff.mpr
    intro k hk
    have hkx := Finset.mem_range.mp hk
    exact C_ne_zero (by omega)
  have hprod : tailLCM (r * x - 1) (r - 1) * contentLCM r x = ((x - 1)!)^r := by
    simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt hx)] using tail_mul_contentLCM hr (x - 1)
  have hlog :
      Real.log (tailLCM (r * x - 1) (r - 1) : ℝ) + Real.log (contentLCM r x : ℝ) =
        (r : ℝ) * Real.log ((x - 1)! : ℝ) := by
    rw [← Real.log_mul (Nat.cast_ne_zero.mpr (tail_nonzero _ _)) (Nat.cast_ne_zero.mpr hL),
      ← Nat.cast_mul, hprod, Nat.cast_pow, Real.log_pow]
  have hratio : Real.log ((x - 1)! : ℝ) - Real.log (contentLCM r x : ℝ) / (r : ℝ) =
      Real.log (tailLCM (r * x - 1) (r - 1) : ℝ) / (r : ℝ) := by
    apply (eq_div_iff hrR).2
    rw [sub_mul, div_mul_cancel₀ _ hrR, mul_comm (Real.log ((x - 1)! : ℝ)), ← hlog]
    ring
  unfold T
  calc
    _ = (Real.log ((x - 1)! : ℝ) - Real.log (contentLCM r x : ℝ) / (r : ℝ)) -
        (x : ℝ) * Real.log (x : ℝ) + (1 + Real.eulerMascheroniConstant) * (x : ℝ) := by ring
    _ = _ := by
      rw [hratio, log_tailLCM_div_eq_mangoldt hr hx, U, Nat.floor_natCast]
      ring

/-- One-sided error bound at every positive integer, including `x = 1`. -/
theorem T_sub_U_bounds {r x : ℕ} (hr : 2 ≤ r) (hx : 0 < x) :
    0 ≤ T r x - U (x : ℝ) ∧
      T r x - U (x : ℝ) ≤ Chebyshev.psi (x : ℝ) / (r : ℝ) := by
  rw [T_eq_U_add_ceilingError hr hx, add_sub_cancel_left]
  have hrR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  obtain ⟨hlo, hhi⟩ := ceilingError_bounds r x
  exact ⟨div_nonneg hlo hrR, div_le_div_of_nonneg_right hhi hrR⟩

/-- Choosing the vertex count to equal the integer scale gives a uniform error. -/
theorem diagonal_sub_U_bounds {x : ℕ} (hx : 2 ≤ x) :
    0 ≤ T x x - U (x : ℝ) ∧ T x x - U (x : ℝ) ≤ Real.log 4 + 4 := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  obtain ⟨hlo, hhi⟩ := T_sub_U_bounds hx (show 0 < x by omega)
  exact ⟨hlo, hhi.trans ((div_le_iff₀ hxR).2 (Chebyshev.psi_le_const_mul_self hxR.le))⟩

/-- RH is equivalent to a fixed square-root bound for the centered coefficient
LCM on arbitrarily late blocks of consecutive integers. -/
theorem rh_iff_cofinal_contentLCM_blocks :
    RiemannHypothesis ↔ ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 → T x x ≤ 2 * Real.sqrt (x : ℝ) := by
  constructor
  · intro rh A
    let D : ℝ := Real.log 4 + 4
    have hD : 0 ≤ D := by
      dsimp [D]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hwindow := (rh_iff_pointwise_sqrt_windows (b := (3 : ℝ) / 2)
      (firstLiMass_lt_third.trans (by norm_num : (1 : ℝ) / 3 < 1))
      (by norm_num)).mp rh
    obtain ⟨Y, hY, hU⟩ := hwindow (max (((max A 5 : ℕ) : ℝ) ^ 12) (D ^ 2))
    have hY' : max (((max A 5 : ℕ) : ℝ) ^ 12) (D ^ 2) ≤ Y :=
      (le_max_left _ _).trans hY
    obtain ⟨k, hk, hsubset⟩ := exists_quartic_block_in_power_window A
      ((le_max_left _ _).trans hY')
    refine ⟨k, hk, ?_⟩
    intro x hlo hhi
    have hk2 : 2 ≤ k := (le_max_right A 2).trans hk
    have hkx : k ≤ x := (le_self_pow₀ (by omega : 1 ≤ k) (by decide : 12 ≠ 0)).trans hlo
    have hx2 : 2 ≤ x := hk2.trans hkx
    have hx : (x : ℝ) ∈ Set.Icc ((k : ℝ) ^ 12) ((k : ℝ) ^ 16) :=
      ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hxY := hsubset hx
    have hDs : D ≤ Real.sqrt (x : ℝ) :=
      (Real.le_sqrt hD (Nat.cast_nonneg x)).2 ((le_max_right _ _).trans (hY'.trans hxY.1))
    have hUx := hU (x : ℝ) hxY
    have hgap : T x x - U (x : ℝ) ≤ D := (diagonal_sub_U_bounds hx2).2
    linarith only [hUx, hgap, hDs]
  · intro blocks
    apply rh_iff_quartic_integer_blocks.mpr
    intro κ hκ A
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      ((tendsto_rpow_atTop hκ).eventually_ge_atTop (2 : ℝ))
    let A' := max A ⌈R⌉₊
    obtain ⟨k, hk, hT⟩ := blocks A'
    have hkA : A ≤ k := (le_max_left A ⌈R⌉₊).trans ((le_max_left A' 2).trans hk)
    have hk2 : 2 ≤ k := (le_max_right A' 2).trans hk
    refine ⟨k, max_le hkA hk2, ?_⟩
    intro n hlo hhi
    have hlo' : k ^ 12 ≤ n ^ 4 := calc
      _ = (k ^ 3) ^ 4 := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left hlo 4
    have hhi' : n ^ 4 ≤ k ^ 16 := calc
      _ ≤ (k ^ 4) ^ 4 := Nat.pow_le_pow_left hhi 4
      _ = _ := by rw [← pow_mul]
    have hkn : k ≤ n := (le_self_pow₀ (by omega : 1 ≤ k) (by decide : 3 ≠ 0)).trans hlo
    have hnx : n ≤ n ^ 4 := le_self_pow₀ (by omega : 1 ≤ n) (by decide : 4 ≠ 0)
    have hx2 : 2 ≤ n ^ 4 := hk2.trans (hkn.trans hnx)
    have hkR : R ≤ (k : ℝ) := (Nat.le_ceil R).trans
      (by exact_mod_cast (le_max_right A ⌈R⌉₊).trans ((le_max_left A' 2).trans hk))
    have hxR : R ≤ (n : ℝ) ^ 4 := hkR.trans (by exact_mod_cast hkn.trans hnx)
    have hx0 : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos (by exact_mod_cast (show 0 < n by omega)) 4
    have hU := sub_nonneg.mp (diagonal_sub_U_bounds hx2).1
    calc
      U ((n : ℝ) ^ 4) ≤ T (n ^ 4) (n ^ 4) := by simpa only [Nat.cast_pow] using hU
      _ ≤ 2 * Real.sqrt ((n : ℝ) ^ 4) := by simpa only [Nat.cast_pow] using hT (n ^ 4) hlo' hhi'
      _ ≤ ((n : ℝ) ^ 4) ^ κ * Real.sqrt ((n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right (hR _ hxR) (Real.sqrt_nonneg _)
      _ = ((n : ℝ) ^ 4) ^ (1 / 2 + κ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0, add_comm κ]

/-- The left and right unit-cell sums for `log` give the exact bounds on the
factorial part of the centered coefficient logarithm. -/
theorem log_factorial_gamma_bounds {x : ℕ} (hx : 1 ≤ x) :
    Real.eulerMascheroniConstant * (x : ℝ) + 1 - Real.log (x : ℝ) ≤
      Real.log ((x - 1)! : ℝ) - (x : ℝ) * Real.log (x : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (x : ℝ) ∧
    Real.log ((x - 1)! : ℝ) - (x : ℝ) * Real.log (x : ℝ) +
        (1 + Real.eulerMascheroniConstant) * (x : ℝ) ≤
      Real.eulerMascheroniConstant * (x : ℝ) + 1 := by
  have hMono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) (x : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn.mono
    intro t ht
    exact zero_lt_one.trans_le (by simpa only [Nat.cast_one] using ht.1)
  have hLeftIndex : Ico 1 x = Ioc 0 (x - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hLeft := hMono.sum_le_integral_Ico hx
  rw [hLeftIndex, Real.sum_log_eq_log_factorial, Nat.cast_one] at hLeft
  have hRightSum :
      (∑ n ∈ Ico 1 x, Real.log ((n + 1 : ℕ) : ℝ)) = Real.log (x ! : ℝ) := by
    rw [Finset.sum_Ico_add' (fun n : ℕ => Real.log (n : ℝ)) 1 x 1,
      Finset.Ico_add_one_add_one_eq_Ioc]
    have hsplit :
        (∑ n ∈ Ioc 1 x, Real.log (n : ℝ)) = ∑ n ∈ Icc 1 x, Real.log (n : ℝ) := by
      simpa only [Nat.cast_one, Real.log_one, zero_add] using
        (Finset.add_sum_Ioc_eq_sum_Icc (f := fun n : ℕ => Real.log (n : ℝ)) hx)
    rw [hsplit, show Icc 1 x = Ioc 0 x by
      simpa only [zero_add] using (Finset.Icc_add_one_left_eq_Ioc (0 : ℕ) x),
      Real.sum_log_eq_log_factorial]
  have hRight := hMono.integral_le_sum_Ico hx
  rw [hRightSum, Nat.cast_one] at hRight
  have hIntegral :
      (∫ t in (1 : ℝ)..(x : ℝ), Real.log t) = (x : ℝ) * Real.log (x : ℝ) - x + 1 := by
    rw [integral_log, Real.log_one, mul_zero, sub_zero]
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hFact :
      Real.log (x ! : ℝ) = Real.log (x : ℝ) + Real.log ((x - 1)! : ℝ) := by
    have hnat : x ! = x * (x - 1)! := by
      simpa only [Nat.sub_add_cancel hx] using Nat.factorial_succ (x - 1)
    rw [hnat, Nat.cast_mul, Real.log_mul hx0 (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  rw [hIntegral] at hLeft hRight
  rw [hFact] at hRight
  exact ⟨by linarith only [hRight], by linarith only [hLeft]⟩

/-- The diagonal coefficient logarithm locates the principal Mangoldt remainder
between two thresholds at distance `log x + log 4 + 4`. -/
theorem diagonal_gamma_threshold {x : ℕ} (hx : 2 ≤ x) :
    Real.eulerMascheroniConstant * (x : ℝ) - Real.log (contentLCM x x : ℝ) / (x : ℝ) +
      1 - Real.log (x : ℝ) - (Real.log 4 + 4) ≤ U (x : ℝ) ∧
    U (x : ℝ) ≤
      Real.eulerMascheroniConstant * (x : ℝ) - Real.log (contentLCM x x : ℝ) / (x : ℝ) + 1 := by
  obtain ⟨hFactLo, hFactHi⟩ := log_factorial_gamma_bounds (show 1 ≤ x by omega)
  obtain ⟨hErrLo, hErrHi⟩ := diagonal_sub_U_bounds hx
  unfold T at hErrLo hErrHi
  exact ⟨by linarith only [hFactLo, hErrHi], by linarith only [hFactHi, hErrLo]⟩

private theorem eventually_power_add_log_le {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, x ^ ((1 : ℝ) / 2 + ε / 2) + Real.log x + D ≤
      x ^ ((1 : ℝ) / 2 + ε) := by
  have ha : 0 < (1 : ℝ) / 2 + ε / 2 := by linarith only [hε]
  have hLog := (isLittleO_log_rpow_atTop ha).eventuallyLE
  have hConst := (tendsto_rpow_atTop ha).eventually_ge_atTop D
  have hPower := (tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop (3 : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hLog, hConst, hPower] with x hx hLogX hDX hPowerX
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hNonneg : 0 ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := Real.rpow_nonneg hx0.le _
  have hLogX' : Real.log x ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    simpa only [Real.norm_of_nonneg (Real.log_nonneg hx), Real.norm_of_nonneg hNonneg] using hLogX
  calc
    _ ≤ 3 * x ^ ((1 : ℝ) / 2 + ε / 2) := by linarith only [hDX, hLogX']
    _ ≤ x ^ (ε / 2) * x ^ ((1 : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hPowerX hNonneg
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

private theorem scale_power_error {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    x ^ ((3 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2 + ε) * x := by
  rw [show (3 : ℝ) / 2 + ε = (1 : ℝ) / 2 + ε + 1 by ring, Real.rpow_add_one hx.ne']

/-- A cofinal principal Mangoldt upper bound on `[Y, Y^(3/2)]` gives the
coefficient lower bound on every integer in a cofinal block. The input is the
principal window after identifying its normalized remainder with `U`. -/
theorem contentLCM_gamma_blocks_of_pointwise_windows
    (windows : ∀ δ : ℝ, 0 < δ → ∀ R : ℝ, ∃ Y : ℝ, max R 1 ≤ Y ∧
      ∀ t ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)), U t ≤ t ^ ((1 : ℝ) / 2 + δ)) :
    ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 →
        Real.eulerMascheroniConstant * (x : ℝ) ^ 2 - (x : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
          Real.log (contentLCM x x : ℝ) := by
  intro ε hε A
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_power_add_log_le hε (Real.log 4 + 4))
  let B : ℝ := ((max A 5 : ℕ) : ℝ) ^ 12
  obtain ⟨Y, hY, hWindow⟩ := windows (ε / 2) (half_pos hε) (max B R)
  have hBRY : max B R ≤ Y := (le_max_left _ _).trans hY
  obtain ⟨k, hk, hSubset⟩ := exists_quartic_block_in_power_window A
    (show B ≤ Y from (le_max_left B R).trans hBRY)
  refine ⟨k, hk, ?_⟩
  intro x hlo hhi
  have hk2 : 2 ≤ k := (le_max_right A 2).trans hk
  have hkx : k ≤ x := (le_self_pow₀ (by omega : 1 ≤ k) (by decide : 12 ≠ 0)).trans hlo
  have hx2 : 2 ≤ x := hk2.trans hkx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxWindow : (x : ℝ) ∈ Set.Icc Y (Y ^ ((3 : ℝ) / 2)) :=
    hSubset ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hxR : R ≤ (x : ℝ) := (le_max_right B R).trans (hBRY.trans hxWindow.1)
  have hQuotient :
      Real.eulerMascheroniConstant * (x : ℝ) - (x : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        Real.log (contentLCM x x : ℝ) / (x : ℝ) := by
    linarith only [(diagonal_gamma_threshold hx2).1, hWindow (x : ℝ) hxWindow, hR (x : ℝ) hxR]
  calc
    _ = (Real.eulerMascheroniConstant * (x : ℝ) - (x : ℝ) ^ ((1 : ℝ) / 2 + ε)) * (x : ℝ) := by
      rw [scale_power_error hx0 ε]
      ring
    _ ≤ _ := (le_div_iff₀ hx0).mp hQuotient

/-- RH is equivalent to the coefficient-content LCM gamma threshold with
arbitrarily small power loss on cofinal blocks of consecutive integers. -/
theorem rh_iff_cofinal_contentLCM_gamma_blocks :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ x : ℕ, k ^ 12 ≤ x → x ≤ k ^ 16 →
        Real.eulerMascheroniConstant * (x : ℝ) ^ 2 - (x : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤
          Real.log (contentLCM x x : ℝ) := by
  constructor
  · intro rh
    apply contentLCM_gamma_blocks_of_pointwise_windows
    intro δ hδ R
    have hWindow := (MangoldtPointwiseWindows.rh_iff_pointwise_power_windows
      (b := (3 : ℝ) / 2) (by norm_num)).mp rh δ hδ
    exact (frequently_atTop.mp hWindow) (max R 1)
  · intro blocks
    apply rh_iff_quartic_integer_blocks.mpr
    intro κ hκ A
    obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_power_add_log_le hκ 1)
    let A' := max A ⌈R⌉₊
    obtain ⟨k, hk, hBlock⟩ := blocks (κ / 2) (half_pos hκ) A'
    have hkA' : A' ≤ k := (le_max_left A' 2).trans hk
    have hkA : A ≤ k := (le_max_left A ⌈R⌉₊).trans hkA'
    have hk2 : 2 ≤ k := (le_max_right A' 2).trans hk
    have hceil : ⌈R⌉₊ ≤ k := (le_max_right A ⌈R⌉₊).trans hkA'
    refine ⟨k, max_le hkA hk2, ?_⟩
    intro n hlo hhi
    let x : ℕ := n ^ 4
    have hlo' : k ^ 12 ≤ x := calc
      _ = (k ^ 3) ^ 4 := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_left hlo 4
    have hhi' : x ≤ k ^ 16 := calc
      _ ≤ (k ^ 4) ^ 4 := Nat.pow_le_pow_left hhi 4
      _ = _ := by rw [← pow_mul]
    have hkx : k ≤ x := (le_self_pow₀ (by omega : 1 ≤ k) (by decide : 12 ≠ 0)).trans hlo'
    have hx2 : 2 ≤ x := hk2.trans hkx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hxR : R ≤ (x : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hceil.trans hkx)
    have hLCM := hBlock x hlo' hhi'
    have hQuotient :
        Real.eulerMascheroniConstant * (x : ℝ) - (x : ℝ) ^ ((1 : ℝ) / 2 + κ / 2) ≤
          Real.log (contentLCM x x : ℝ) / (x : ℝ) := by
      apply (le_div_iff₀ hx0).mpr
      calc
        _ = Real.eulerMascheroniConstant * (x : ℝ) ^ 2 - (x : ℝ) ^ ((3 : ℝ) / 2 + κ / 2) := by
          rw [scale_power_error hx0 (κ / 2)]
          ring
        _ ≤ _ := hLCM
    have hLog : 0 ≤ Real.log (x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    have hU : U (x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2 + κ) := by
      linarith only [(diagonal_gamma_threshold hx2).2, hQuotient, hR (x : ℝ) hxR, hLog]
    simpa only [x, Nat.cast_pow] using hU

end D5.S3.Weil.Mertens.IntegratedExplicit.PathRodriguesMangoldtBridge
