/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompactQuarticBridge
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Exact tail LCM and compact factorial gcd bounds for quartic RH tests. -/

import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import D5.S3.Arith.FactorialRatio.QuarticCompactLog
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

/-! Fourth-power RH tests using exact finite LCM and factorial products. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge

open Finset Filter Real
open scoped Topology Nat
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

private theorem log_tailLCM_eq_sum_psi (H M : ℕ) :
    Real.log (tailLCM H M : ℝ) =
      ∑ k ∈ Ioc M H, Chebyshev.psi ((H / k : ℕ) : ℝ) := by
  unfold tailLCM
  rw [Nat.cast_prod, Real.log_prod (fun k _ => Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero _))]
  exact Finset.sum_congr rfl fun k _ => (Chebyshev.psi_eq_log_lcmUpto (H / k)).symm

/-- Count the incidences a*k ≤ M*N, with 0 < a and M < k, in either order. -/
theorem log_tailLCM_eq_sum_vonMangoldt (N M : ℕ) (hM : 0 < M) :
    Real.log (tailLCM (M * N) M : ℝ) =
      ∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a * ((M * N / a - M : ℕ) : ℝ) := by
  let H := M * N
  change Real.log (tailLCM H M : ℝ) = _
  rw [log_tailLCM_eq_sum_psi]
  simp only [Chebyshev.psi, Nat.floor_natCast]
  calc
    _ = ∑ k ∈ Ioc M H, ∑ a ∈ Ioc 0 N,
        if a ≤ H / k then ArithmeticFunction.vonMangoldt a else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkM := (Finset.mem_Ioc.mp hk).1
      have hkn : H / k ≤ N := calc
        _ ≤ H / M := Nat.div_le_div_left hkM.le hM
        _ = N := by dsimp [H]; exact Nat.mul_div_cancel_left N hM
      rw [← Finset.sum_filter]
      have heq : (Ioc 0 N).filter (fun a => a ≤ H / k) = Ioc 0 (H / k) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
      rw [heq]
    _ = ∑ a ∈ Ioc 0 N, ∑ k ∈ Ioc M H,
        if a ≤ H / k then ArithmeticFunction.vonMangoldt a else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha0 := (Finset.mem_Ioc.mp ha).1
      rw [← Finset.sum_filter]
      have heq : (Ioc M H).filter (fun k => a ≤ H / k) = Ioc M (H / a) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hkM, _⟩, hak⟩
          have hk0 : 0 < k := (Nat.zero_le M).trans_lt hkM
          have hm := (Nat.le_div_iff_mul_le hk0).mp hak
          exact ⟨hkM, (Nat.le_div_iff_mul_le ha0).mpr (by simpa [mul_comm] using hm)⟩
        · rintro ⟨hkM, hka⟩
          have hk0 : 0 < k := (Nat.zero_le M).trans_lt hkM
          have hm := (Nat.le_div_iff_mul_le ha0).mp hka
          exact ⟨⟨hkM, hka.trans (Nat.div_le_self _ _)⟩,
            (Nat.le_div_iff_mul_le hk0).mpr (by simpa [mul_comm] using hm)⟩
      rw [heq, Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      dsimp [H]
      ring

/-- The normalized, centered logarithm of the finite tail of prefix LCMs. -/
def D (N M : ℕ) : ℝ :=
  Real.log (tailLCM (M * N) M : ℝ) / (M : ℝ) -
    (N : ℝ) * Real.log N + (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- Exact cancellation leaves a weighted floor error. -/
private theorem U_sub_D_eq_floor_error (N M : ℕ) (hM : 0 < M) :
    U (N : ℝ) - D N M =
      (∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a *
        ((M : ℝ) * (N : ℝ) / (a : ℝ) - ((M * N / a : ℕ) : ℝ))) / (M : ℝ) := by
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hsub : (∑ a ∈ Ioc 0 N,
      ArithmeticFunction.vonMangoldt a * ((M * N / a - M : ℕ) : ℝ)) =
      (∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a * ((M * N / a : ℕ) : ℝ)) -
        (M : ℝ) * (∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨ha0, haN⟩ := Finset.mem_Ioc.mp ha
    have hma : M ≤ M * N / a :=
      (Nat.le_div_iff_mul_le ha0).mpr (Nat.mul_le_mul_left M haN)
    rw [Nat.cast_sub hma]
    ring
  have herror : (∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a *
        ((M : ℝ) * (N : ℝ) / (a : ℝ) - ((M * N / a : ℕ) : ℝ))) =
      (M : ℝ) * ((N : ℝ) *
        (∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a / (a : ℝ))) -
        ∑ a ∈ Ioc 0 N, ArithmeticFunction.vonMangoldt a * ((M * N / a : ℕ) : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [D, log_tailLCM_eq_sum_vonMangoldt N M hM, hsub, U, Chebyshev.psi,
    Nat.floor_natCast, herror]
  field_simp [hm]; ring

/-- One-sided error bound for every natural N and every positive M. -/
theorem U_sub_D_bounds (N M : ℕ) (hM : 0 < M) :
    0 ≤ U (N : ℝ) - D N M ∧
      U (N : ℝ) - D N M ≤ Chebyshev.psi (N : ℝ) / (M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hfloor (a : ℕ) :
      0 ≤ (M : ℝ) * (N : ℝ) / (a : ℝ) - ((M * N / a : ℕ) : ℝ) ∧
        (M : ℝ) * (N : ℝ) / (a : ℝ) - ((M * N / a : ℕ) : ℝ) ≤ 1 := by
    have hlo : ((M * N / a : ℕ) : ℝ) ≤ (M : ℝ) * (N : ℝ) / (a : ℝ) := by
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le : ((M * N / a : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) / (a : ℝ))
    have hhi : (M : ℝ) * (N : ℝ) / (a : ℝ) < ((M * N / a : ℕ) : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (((M * N : ℕ) : ℝ) / (a : ℝ))
      rw [Nat.floor_div_natCast, Nat.floor_natCast, Nat.cast_mul] at h
      exact h
    exact ⟨by linarith, by linarith⟩
  rw [U_sub_D_eq_floor_error N M hM, Chebyshev.psi, Nat.floor_natCast]
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun a _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hfloor a).1) hm.le
  · apply div_le_div_of_nonneg_right _ hm.le
    apply Finset.sum_le_sum
    intro a _
    calc
      _ ≤ ArithmeticFunction.vonMangoldt a * 1 :=
        mul_le_mul_of_nonneg_left (hfloor a).2 ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := mul_one _

private theorem quartic_U_sub_D_bounds (n : ℕ) (hn : 0 < n) :
    0 ≤ U ((n : ℝ)^4) - D (n^4) (n^2) ∧
      U ((n : ℝ)^4) - D (n^4) (n^2) ≤ (Real.log 4 + 4) * (n : ℝ)^2 := by
  have h := U_sub_D_bounds (n^4) (n^2) (pow_pos hn 2)
  push_cast at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (pow_pos hn0 2)).2
  calc
    _ ≤ (Real.log 4 + 4) * (n : ℝ)^4 :=
      Chebyshev.psi_le_const_mul_self (by positivity)
    _ = _ := by ring

/-- Any fixed constant is eventually below a positive power of the quartic scale. -/
private theorem eventually_quartic_rpow_ge (p C : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, C ≤ ((n : ℝ)^4)^p := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hp).eventually_ge_atTop C)
  filter_upwards [eventually_ge_atTop (max ⌈T⌉₊ 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right ⌈T⌉₊ 1).trans hn
  have hnT : T ≤ (n : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left ⌈T⌉₊ 1).trans hn)
  exact hT _ (hnT.trans (le_self_pow₀ hn1 (by decide : 4 ≠ 0)))

/-- A uniform logarithmic error loses an arbitrarily small quartic exponent. -/
private theorem eventually_quartic_log_error_le (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 * (1 + Real.log n) ≤ ((n : ℝ)^4)^(1/2 + δ) := by
  have hp : 0 < 2 * δ := by positivity
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(2 * δ)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (C * (1 + 1 / (2 * δ))),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hx0 : (0 : ℝ) < n := zero_lt_one.trans_le hx1
  have hxpow := Real.one_le_rpow hx1 hp.le
  have hlog := Real.log_le_rpow_div hx0.le hp
  have hc : C * (1 + Real.log n) ≤ (n : ℝ)^(2*δ) * (n : ℝ)^(2*δ) := calc
    _ ≤ C * ((n : ℝ)^(2*δ) + (n : ℝ)^(2*δ)/(2*δ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hxpow hlog) hC
    _ = C * (1 + 1/(2*δ)) * (n : ℝ)^(2*δ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (by positivity)
  calc
    _ = (n : ℝ)^2 * (C * (1 + Real.log n)) := by ring
    _ ≤ (n : ℝ)^2 * ((n : ℝ)^(2*δ) * (n : ℝ)^(2*δ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = ((n : ℝ)^4)^(1/2 + δ) := by
      rw [← Real.rpow_add hx0 (2*δ) (2*δ), ← Real.rpow_natCast (n : ℝ) 2,
        ← Real.rpow_add hx0, ← Real.rpow_natCast (n : ℝ) 4, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring

/-- The block quantifiers are preserved under an eventual one-sided power error. -/
private theorem transfer_blocks {f g : ℕ → ℝ}
    (herr : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      g n ≤ f n + ((n : ℝ)^4)^(1/2+δ))
    (hf : ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 → f n ≤ ((n : ℝ)^4)^(1/2+κ)) :
    ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 → g n ≤ ((n : ℝ)^4)^(1/2+κ) := by
  intro κ hκ A
  obtain ⟨B, hB⟩ := eventually_atTop.mp (herr (κ/2) (half_pos hκ))
  obtain ⟨E, hE⟩ := eventually_atTop.mp (eventually_quartic_rpow_ge (κ/2) 2 (half_pos hκ))
  obtain ⟨k, hk, hkbound⟩ := hf (κ/2) (half_pos hκ) (max A (max B E))
  have hk1 : 1 ≤ k := by omega
  have hkA : A ≤ k := (le_max_left A (max B E)).trans ((le_max_left _ 2).trans hk)
  have hkBE : max B E ≤ k := (le_max_right A _).trans ((le_max_left _ 2).trans hk)
  refine ⟨k, max_le hkA ((le_max_right _ 2).trans hk), ?_⟩
  intro n hlo hhi
  have hkn : k ≤ n := (le_self_pow₀ hk1 (by decide : 3 ≠ 0)).trans hlo
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hk1.trans hkn
  have hx0 : 0 < (n : ℝ)^4 := by positivity
  have hscale := hE n ((le_max_right B E).trans (hkBE.trans hkn))
  have hb := hkbound n hlo hhi
  have hg := hB n ((le_max_left B E).trans (hkBE.trans hkn))
  calc
    g n ≤ 2 * ((n : ℝ)^4)^(1/2+κ/2) := by linarith
    _ ≤ ((n : ℝ)^4)^(κ/2) * ((n : ℝ)^4)^(1/2+κ/2) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = ((n : ℝ)^4)^(1/2+κ) := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- Stability of the existing RH criterion under a quantitative O(n² log n) error. -/
private theorem rh_iff_quartic_blocks_of_log_error (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (herr : ∀ᶠ n : ℕ in atTop,
      |f n - U ((n : ℝ) ^ 4)| ≤ C * (n : ℝ) ^ 2 * (1 + Real.log n)) :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 → f n ≤ ((n : ℝ)^4)^(1/2+κ) := by
  rw [rh_iff_quartic_integer_blocks]
  have habs (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop,
      |f n - U ((n : ℝ) ^ 4)| ≤ ((n : ℝ)^4)^(1/2+δ) :=
    (herr.and (eventually_quartic_log_error_le C δ hC hδ)).mono fun _ h => h.1.trans h.2
  constructor
  · intro hf
    apply transfer_blocks (f := fun n => U ((n : ℝ)^4)) (g := f) _ hf
    intro δ hδ
    filter_upwards [habs δ hδ] with n hn
    linarith [le_abs_self (f n - U ((n : ℝ)^4))]
  · intro hf
    apply transfer_blocks (f := f) (g := fun n => U ((n : ℝ)^4)) _ hf
    intro δ hδ
    filter_upwards [habs δ hδ] with n hn
    linarith [neg_le_abs (f n - U ((n : ℝ)^4))]

theorem rh_iff_tailLCM_quartic_integer_blocks :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 → D (n^4) (n^2) ≤ ((n : ℝ)^4)^(1/2+κ) := by
  have hC : 0 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  apply rh_iff_quartic_blocks_of_log_error (fun n => D (n^4) (n^2)) _ hC
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h := quartic_U_sub_D_bounds n (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn1
  rw [abs_of_nonpos (by linarith only [h.1])]
  calc
    _ ≤ (Real.log 4 + 4) * (n : ℝ)^2 := by linarith only [h.2]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)

/-- An eventual quadratic sample bound with an arbitrary fixed real constant
already implies RH. The forward implication even permits C = 1. -/
theorem rh_iff_eventually_tailLCM_quartic_constant :
    RiemannHypothesis ↔ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      D (n^4) (n^2) ≤ C * (n : ℝ)^2 := by
  constructor
  · intro rh
    refine ⟨1, ?_⟩
    filter_upwards [rh_iff_eventually_quartic_samples.mp rh,
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have h := quartic_U_sub_D_bounds n (by omega)
    linarith only [hn, h.1]
  · rintro ⟨C, hC⟩
    apply rh_iff_tailLCM_quartic_integer_blocks.mpr
    intro κ hκ A
    obtain ⟨B, hB⟩ := eventually_atTop.mp hC
    obtain ⟨E, hE⟩ := eventually_atTop.mp (eventually_quartic_rpow_ge κ C hκ)
    let k := max (max A 2) (max B E)
    have hk : max A 2 ≤ k := le_max_left _ _
    have hk1 : 1 ≤ k := by omega
    refine ⟨k, hk, ?_⟩
    intro n hlo _
    have hkn : k ≤ n := (le_self_pow₀ hk1 (by decide : 3 ≠ 0)).trans hlo
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hBE : max B E ≤ n := (le_max_right _ _).trans hkn
    have hsqrt : ((n : ℝ)^4)^(1/2 : ℝ) = (n : ℝ)^2 := by
      rw [← Real.rpow_natCast (n : ℝ) 4, ← Real.rpow_mul hn0.le]
      norm_num
    calc
      _ ≤ C * (n : ℝ)^2 := hB n ((le_max_left _ _).trans hBE)
      _ ≤ ((n : ℝ)^4)^κ * (n : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (hE n ((le_max_right _ _).trans hBE)) (by positivity)
      _ = ((n : ℝ)^4)^(1/2+κ) := by rw [← hsqrt, ← Real.rpow_add (pow_pos hn0 4)]; congr 1; ring

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass)

/-- The established sharp RH envelope permits every fixed C above firstLiMass. -/
theorem rh_iff_eventually_tailLCM_quartic_of_mass_lt (C : ℝ) (hC : firstLiMass < C) :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, D (n^4) (n^2) ≤ C * (n : ℝ)^2 := by
  constructor
  · intro rh
    have he := (RHSharpActualEnvelope.actual_G_control rh).1 (C-firstLiMass)
      (sub_pos.mpr hC)
    have hlim : Tendsto (fun n : ℕ => 4 * Real.log (n : ℝ)) atTop atTop :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    filter_upwards [hlim.eventually he, eventually_ge_atTop (1 : ℕ)] with n h hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h4 : Real.exp (4 * Real.log (n : ℝ)) = (n : ℝ)^4 := by
      simpa [Real.exp_log hn0] using Real.exp_nat_mul (Real.log (n : ℝ)) 4
    have h2 : Real.exp (-(4 * Real.log (n : ℝ))/2) = ((n : ℝ)^2)⁻¹ := by
      rw [show -(4 * Real.log (n : ℝ))/2 = -(2 * Real.log (n : ℝ)) by ring, Real.exp_neg]
      congr 1
      simpa [Real.exp_log hn0] using Real.exp_nat_mul (Real.log (n : ℝ)) 2
    change |Real.exp (-(4 * Real.log (n : ℝ))/2) *
      U (Real.exp (4 * Real.log (n : ℝ)))| < _ at h
    rw [h4, h2] at h
    have hlt : U ((n : ℝ)^4) / (n : ℝ)^2 < C := by
      rw [div_eq_inv_mul]
      linarith [le_abs_self (((n : ℝ)^2)⁻¹ * U ((n : ℝ)^4))]
    have hU := (div_lt_iff₀ (pow_pos hn0 2)).mp hlt
    have hf := (quartic_U_sub_D_bounds n (by omega)).1
    linarith only [hU, hf]
  · intro h
    exact rh_iff_eventually_tailLCM_quartic_constant.mpr ⟨C, h⟩

/-- At the quartic scales the degree is already divisible by the number of parts. -/
private theorem quartic_degree (M : ℕ) (hM : 1 ≤ M) :
    (M + 1) * (M * (M - 1)) + M = M * M^2 := by
  have hmul : (M + 1) * (M - 1) + (M + 1) = (M + 1) * M := by
    calc
      _ = (M + 1) * (M - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hM]
  have heq : (M + 1) * M = M*M + M := by ring
  have hd : (M + 1) * (M - 1) + 1 = M*M := by omega
  calc
    _ = M * ((M + 1) * (M - 1) + 1) := by ring
    _ = _ := by rw [hd]; ring

/-- The actual finite gcd of factorial ratios at the quartic sample. -/
def quarticFactorialGcd (n : ℕ) : ℕ :=
  selbergGcd (n^2 + 1) (n^2 * (n^2 - 1))

/-- The defining family uses at most n² factorial-ratio integers. -/
theorem quarticFactorialGcd_family_size (n : ℕ) (hn : 0 < n) :
    (range (n^2 * (n^2 - 1) / (n^2 + 1) + 1)).card ≤ n^2 := by
  let M := n^2
  have hM : 0 < M := pow_pos hn 2
  change (range (M * (M - 1) / (M + 1) + 1)).card ≤ M
  have hlt : M * (M - 1) < M * (M + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hM
  have hdiv : M * (M - 1) / (M + 1) < M :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < M + 1)).mpr hlt
  simpa only [Finset.card_range] using (show M * (M - 1) / (M + 1) + 1 ≤ M by omega)

/-- Degree padding has factor 1 at H = n⁶, M = n². -/
private theorem quarticFactorialGcd_divisibility (n : ℕ) (hn : 0 < n) :
    tailLCM (n^2 * n^4) (n^2) ∣ quarticFactorialGcd n ∧
      quarticFactorialGcd n ∣ tailLCM (n^2 * n^4) (n^2) * (2 * (n^2 + 1)^2)! := by
  let M := n^2
  have hM : 1 ≤ M := Nat.succ_le_of_lt (pow_pos hn 2)
  have hr : 2 ≤ M + 1 := by omega
  have hs : M * (M - 1) < (M + 1)^2 := by
    calc
      _ ≤ M * M := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ < (M + 1)^2 := by nlinarith
  have hdeg : (M + 1) * (M * (M - 1)) + (M + 1) - 1 = M * n^4 := by
    have h := quartic_degree M hM
    have hN : M^2 = n^4 := by dsimp [M]; ring
    rw [hN] at h
    omega
  have h := compact_factorial_gcd (M + 1) (M * (M - 1)) hr hs
  rw [hdeg, Nat.add_sub_cancel] at h
  exact h

/-- The difference of logs is controlled by divisibility and an explicit factorial. -/
private theorem log_gap_of_dvd {A G B : ℕ} (hA : 0 < A)
    (hAG : A ∣ G) (hGB : G ∣ A * B !) :
    0 ≤ Real.log (G : ℝ) - Real.log (A : ℝ) ∧
      Real.log (G : ℝ) - Real.log (A : ℝ) ≤ (B : ℝ) * Real.log B := by
  have hAB : 0 < A * B ! := Nat.mul_pos hA (Nat.factorial_pos B)
  have hG : 0 < G := Nat.pos_of_dvd_of_pos hGB hAB
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have hB' : (0 : ℝ) < B ! := by exact_mod_cast Nat.factorial_pos B
  have hlo : Real.log (A : ℝ) ≤ Real.log (G : ℝ) :=
    Real.log_le_log hA' (by exact_mod_cast Nat.le_of_dvd hG hAG)
  have hhi : Real.log (G : ℝ) ≤ Real.log ((A : ℝ) * (B ! : ℕ)) :=
    Real.log_le_log hG' (by exact_mod_cast Nat.le_of_dvd hAB hGB)
  rw [Real.log_mul hA'.ne' hB'.ne'] at hhi
  have hfac : Real.log (B ! : ℕ) ≤ (B : ℝ) * Real.log B := calc
    _ ≤ Real.log ((B : ℝ)^B) :=
      Real.log_le_log hB' (by exact_mod_cast B.factorial_le_pow)
    _ = _ := Real.log_pow _ _
  exact ⟨by linarith, by linarith⟩

/-- Center the logarithm of the compact, explicit gcd by the same real terms. -/
def compactD (n : ℕ) : ℝ :=
  Real.log (quarticFactorialGcd n : ℝ) / (n : ℝ)^2 -
    (n : ℝ)^4 * Real.log ((n : ℝ)^4) +
      (1 + Real.eulerMascheroniConstant) * (n : ℝ)^4

private theorem compactD_sub_D_eq_log_gap (n : ℕ) :
    compactD n - D (n^4) (n^2) =
      (Real.log (quarticFactorialGcd n : ℝ) -
        Real.log (tailLCM (n^2 * n^4) (n^2) : ℝ)) / (n : ℝ)^2 := by
  unfold compactD D
  push_cast
  rw [sub_div]
  ring

private theorem compactD_sub_D_bounds (n : ℕ) (hn : 0 < n) :
    0 ≤ compactD n - D (n^4) (n^2) ∧
      compactD n - D (n^4) (n^2) ≤
        ((2 : ℝ) * ((n : ℝ)^2 + 1)^2) *
          Real.log (2 * ((n : ℝ)^2 + 1)^2) / (n : ℝ)^2 := by
  have hA : 0 < tailLCM (n^2 * n^4) (n^2) := by
    unfold tailLCM
    exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => Nat.lcmUpto_ne_zero _)
  have hdvd := quarticFactorialGcd_divisibility n hn
  have hlog := log_gap_of_dvd hA hdvd.1 hdvd.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [compactD_sub_D_eq_log_gap]
  push_cast at hlog
  exact ⟨div_nonneg hlog.1 (by positivity),
    div_le_div_of_nonneg_right hlog.2 (by positivity)⟩

/-- Explicit O(n² log n) budget, using only factorial ≤ B^B. -/
private theorem compactD_sub_D_le (n : ℕ) (hn : 2 ≤ n) :
    compactD n - D (n^4) (n^2) ≤ 56 * (n : ℝ)^2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  let B : ℝ := 2 * ((n : ℝ)^2 + 1)^2
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB : B ≤ 8*(n : ℝ)^4 := by
    dsimp [B]
    have hn_sq : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ hn1
    calc
      _ ≤ 2 * (2 * (n : ℝ)^2)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith : (n : ℝ)^2 + 1 ≤ 2*(n : ℝ)^2) 2)
          (by norm_num)
      _ = _ := by ring
  have hlog : Real.log B ≤ 7 * Real.log n := calc
    _ ≤ Real.log (8 * (n : ℝ)^4) := Real.log_le_log hB0 hB
    _ = 3 * Real.log 2 + 4 * Real.log n := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 4 hn0.ne'), Real.log_pow,
        show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      norm_num
    _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0:ℝ) < 2) hn2]
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hprod : B * Real.log B ≤ 8 * (n : ℝ)^4 * (7 * Real.log n) := calc
    _ ≤ B * (7 * Real.log n) := mul_le_mul_of_nonneg_left hlog hB0.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hB (by positivity)
  apply (compactD_sub_D_bounds n (by omega)).2.trans
  change B * Real.log B / (n : ℝ)^2 ≤ _
  apply (div_le_iff₀ (pow_pos hn0 2)).mpr
  calc
    _ ≤ 8 * (n : ℝ)^4 * (7 * Real.log n) := hprod
    _ = _ := by ring

/-- A two-sided quantitative bridge from the compact integer object to U. -/
theorem compactD_U_bounds (n : ℕ) (hn : 2 ≤ n) :
    -(Real.log 4 + 4) * (n : ℝ)^2 ≤ compactD n - U ((n : ℝ)^4) ∧
      compactD n - U ((n : ℝ)^4) ≤ 56 * (n : ℝ)^2 * Real.log n := by
  have hfloor := quartic_U_sub_D_bounds n (by omega)
  have hcompact := compactD_sub_D_bounds n (by omega)
  have hlog := compactD_sub_D_le n hn
  exact ⟨by linarith only [hfloor.2, hcompact.1], by linarith only [hfloor.1, hlog]⟩

/-- RH tested using the actual gcd of at most n² explicit factorial-ratio integers. -/
theorem rh_iff_compact_factorial_gcd_quartic_integer_blocks :
    RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 →
        Real.log (((range (n^2 * (n^2-1) / (n^2+1) + 1)).gcd
          (selbergFactorial (n^2+1) (n^2 * (n^2-1))) : ℕ) : ℝ) / (n : ℝ)^2 -
          (n : ℝ)^4 * Real.log ((n : ℝ)^4) +
            (1 + Real.eulerMascheroniConstant) * (n : ℝ)^4 ≤
          ((n : ℝ)^4)^(1/2+κ) := by
  change RiemannHypothesis ↔ ∀ κ : ℝ, 0 < κ → ∀ A : ℕ, ∃ k ≥ max A 2,
      ∀ n : ℕ, k^3 ≤ n → n ≤ k^4 → compactD n ≤ ((n : ℝ)^4)^(1/2+κ)
  have hC : 0 ≤ Real.log 4 + 4 := by linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  apply rh_iff_quartic_blocks_of_log_error compactD (Real.log 4 + 4 + 56) (by linarith)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have h := compactD_U_bounds n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog := Real.log_nonneg hn1
  have hs : 0 ≤ (n : ℝ)^2 := by positivity
  have hfloor : (Real.log 4 + 4) * (n : ℝ)^2 ≤
      (Real.log 4 + 4 + 56) * (n : ℝ) ^ 2 * (1 + Real.log n) := calc
    _ ≤ (Real.log 4 + 4 + 56) * (n : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)
  have hfactorial : 56 * (n : ℝ)^2 * Real.log n ≤
      (Real.log 4 + 4 + 56) * (n : ℝ) ^ 2 * (1 + Real.log n) := calc
    _ ≤ (Real.log 4 + 4 + 56) * (n : ℝ)^2 * Real.log n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs) hlog
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  exact abs_le.mpr ⟨by linarith only [h.1, hfloor], h.2.trans hfactorial⟩

/-- The exact compact quartic bridge at the square-root scale. -/
theorem compactD_U_quadratic_bounds (n : ℕ) (hn : 3 ≤ n) :
    -(Real.log 4 + 4) * (n : ℝ)^2 ≤ compactD n - U ((n : ℝ)^4) ∧
      compactD n - U ((n : ℝ)^4) ≤ 18 * (Real.log 4 + 4) * (n : ℝ)^2 := by
  let M := n^2
  have hM4 : 4 ≤ M := (show 4 ≤ (3 : ℕ)^2 by decide).trans (Nat.pow_le_pow_left hn 2)
  have hMr : 8 ≤ M + 1 := by
    have h := Nat.pow_le_pow_left hn 2
    change (3 : ℕ)^2 ≤ M at h
    omega
  have hM1 : 1 ≤ M := by omega
  have hsub : M + 1 - 2 = M - 1 := by omega
  have hdeg : (M + 1) * (M * (M - 1)) + M = M * n^4 := by
    rw [quartic_degree M hM1]
    congr 1
    dsimp [M]
    ring
  have hgap := quartic_compact_log_gap (M + 1) hMr
  dsimp only at hgap
  rw [Nat.add_sub_cancel, hsub, hdeg] at hgap
  change 0 ≤ Real.log (quarticFactorialGcd n : ℝ) -
      Real.log (tailLCM (n^2 * n^4) (n^2) : ℝ) ∧
    Real.log (quarticFactorialGcd n : ℝ) -
      Real.log (tailLCM (n^2 * n^4) (n^2) : ℝ) ≤
      11 * (Real.log 4 + 4) * ((M + 1 : ℕ) : ℝ)^2 at hgap
  have hC : 0 ≤ Real.log 4 + 4 := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hM4R : (4 : ℝ) ≤ M := by exact_mod_cast hM4
  have hMpos : (0 : ℝ) < M := by linarith
  have hMeq : (M : ℝ) = (n : ℝ)^2 := by simp [M]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 11 * ((M + 1 : ℕ) : ℝ)^2 ≤ 18 * (M : ℝ)^2 := calc
    _ ≤ 11 * ((5 / 4 : ℝ) * M)^2 := by
      rw [Nat.cast_add, Nat.cast_one]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) 2) (by norm_num)
    _ ≤ _ := by nlinarith only [sq_nonneg (M : ℝ)]
  have hcompact :
      0 ≤ compactD n - D (n^4) (n^2) ∧
      compactD n - D (n^4) (n^2) ≤ 18 * (Real.log 4 + 4) * (n : ℝ)^2 := by
    rw [compactD_sub_D_eq_log_gap]
    refine ⟨div_nonneg hgap.1 (by positivity), (div_le_iff₀ (pow_pos hnpos 2)).mpr ?_⟩
    calc
      _ ≤ 11 * (Real.log 4 + 4) * ((M + 1 : ℕ) : ℝ)^2 := hgap.2
      _ ≤ 18 * (Real.log 4 + 4) * (M : ℝ)^2 := by
        simpa only [mul_left_comm (Real.log 4 + 4), mul_assoc] using
          mul_le_mul_of_nonneg_left hsq hC
      _ = _ := by rw [hMeq]; ring
  have hfloor := quartic_U_sub_D_bounds n (by omega)
  exact ⟨by linarith only [hcompact.1, hfloor.2], by linarith only [hcompact.2, hfloor.1]⟩

/-- RH is equivalent to an eventual bound for the explicit compact factorial gcd
with a prescribed constant at the square-root scale. -/
theorem rh_iff_eventually_compact_factorial_gcd :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop,
      compactD n ≤ (1 + 18 * (Real.log 4 + 4)) * (n : ℝ)^2 := by
  constructor
  · intro rh
    filter_upwards [rh_iff_eventually_quartic_samples.mp rh,
      eventually_ge_atTop (3 : ℕ)] with n hU hn
    have h := (compactD_U_quadratic_bounds n hn).2
    linarith only [hU, h, show (1 + 18 * (Real.log 4 + 4)) * (n : ℝ)^2 =
        (n : ℝ)^2 + 18 * (Real.log 4 + 4) * (n : ℝ)^2 by ring]
  · intro he
    apply rh_iff_eventually_tailLCM_quartic_constant.mpr
    refine ⟨1 + 18 * (Real.log 4 + 4), ?_⟩
    filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact (sub_nonneg.mp (compactD_sub_D_bounds n (by omega)).1).trans hn

end D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
