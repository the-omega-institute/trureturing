/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The leading odd-cutoff signed residual and the sharpness of the zero order exponent. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusWindow
import Mathlib.Data.Nat.Prime.Infinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real ArithmeticFunction Finset MeasureTheory
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (spectralPrimitive windowDiscrepancy)


/-- The signed prime-window residual with the strict spectral cutoff. -/
def signedWindowResidual (m : ℕ) (a B : ℝ) : ℝ :=
  windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
    spectralPrimitive (phaseOrbit (Real.log a)) -
    (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) -
    (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2*n < m+1),
      -(μ n : ℝ) * (rootPrimitive (n : ℝ) B-rootPrimitive (n : ℝ) a))

private theorem residual_succ_of_odd {m : ℕ} (hm : 2 ≤ m) (hodd : Odd (m+1)) (a B : ℝ) :
    signedWindowResidual (m+1) a B =
      signedWindowResidual m a B - arithmeticPrimitive (m+1) a B := by
  have hroots :
      (Finset.Icc 2 (m+1)).filter (fun n => 2*n < (m+1)+1) =
        (Finset.Icc 2 m).filter (fun n => 2*n < m+1) := by
    obtain ⟨k, hk⟩ := hodd
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have harith : Finset.Icc 3 (m+1) = insert (m+1) (Finset.Icc 3 m) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [signedWindowResidual, signedWindowResidual, hroots, harith,
    Finset.sum_insert (by simp)]
  ring

theorem power_gap_of_rate_increase {s δ a B : ℝ} (hs : 0 < s)
    (hδ : 0 ≤ δ) (ha : 0 < a) (hab : a ≤ B) :
    powerGap (s+δ) a B ≤ ((s+δ)/s) * a^(-δ) * powerGap s a B := by
  have hB := ha.trans_le hab
  have hlog := Real.log_le_log ha hab
  have hr : 0 < s+δ := add_pos_of_pos_of_nonneg hs hδ
  have hp (x v : ℝ) (hx : 0 < x) : Real.exp (-v*Real.log x) = x^(-v) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hm : (∫ u in Real.log a..Real.log B, Real.exp (-(s+δ)*u)) ≤
      ∫ u in Real.log a..Real.log B, a^(-δ)*Real.exp (-s*u) := by
    apply intervalIntegral.integral_mono_on hlog
    · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-(s+δ)*u)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u : ℝ => a^(-δ)*Real.exp (-s*u)).intervalIntegrable _ _
    · intro u hu
      rw [← hp a δ ha, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hu.1)])
  rw [intervalIntegral.integral_const_mul, exp_decay_integral hr, exp_decay_integral hs,
    hp a (s+δ) ha, hp B (s+δ) hB, hp a s ha, hp B s hB] at hm
  unfold powerGap
  exact ((div_le_iff₀ hr).mp hm).trans_eq (by ring)

/-- The first omitted arithmetic term gives the leading response at odd cutoff. -/
theorem signed_window_odd_cutoff_expansion (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → Odd (m+1) → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
        let q := m+1
        let s := orderRate m
        let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
        let W := K*((q : ℝ)*(1+Real.log (q : ℝ))^2)
        |signedWindowResidual m a B + (μ q : ℝ) * (((m : ℝ)+1)/((m : ℝ)*s)) *
          powerGap s a B| ≤ W * powerGap (s+δ) a B ∧
        W * powerGap (s+δ) a B ≤ W*((s+δ)/s)*a^(-δ)*powerGap s a B := by
  obtain ⟨a₀, K, ha₀, hK, hb⟩ := prime_window_mobius_of_rh hRH
  refine ⟨a₀, K, ha₀, hK, fun m hm hodd a B ha hAB => ?_⟩
  dsimp only
  let q := m+1
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq3 : (3 : ℝ) ≤ q := by
    exact_mod_cast (show 3 ≤ q by dsimp [q]; omega)
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hs : 0 < s := by
    have hi := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) < (m : ℝ)+1 by linarith)
    dsimp [s, orderRate]
    norm_num at hi
    linarith
  have hδ : 0 ≤ δ := by
    exact sub_nonneg.mpr (inv_anti₀ (by positivity : (0 : ℝ) < (m : ℝ)+1)
      (by linarith : (m : ℝ)+1 ≤ (m : ℝ)+2))
  have hr : orderRate q = s+δ := by
    dsimp [orderRate, s, δ]
    rw [hq', show (m : ℝ)+1+1 = (m : ℝ)+2 by ring]
    ring
  have ha' : 0 < a := by linarith
  have harith : arithmeticPrimitive q a B =
      -(μ q : ℝ) * ((q : ℝ)/((m : ℝ)*s)) * powerGap s a B := by
    have hrate : arithmeticRate q = s := by simp only [arithmeticRate, hq', s, orderRate]
    have hcoe : 2*(q : ℝ)^2/(((q : ℝ)-1)*((q : ℝ)-2)) = (q : ℝ)/((m : ℝ)*s) := by
      rw [hq']
      dsimp only [s, orderRate]
      have h₁ : (m : ℝ) ≠ 0 := by linarith
      have h₂ : (m : ℝ)+1 ≠ 0 := by linarith
      have h₃ : (m : ℝ)+1-1 ≠ 0 := by linarith
      have h₄ : (m : ℝ)+1-2 ≠ 0 := by linarith
      field_simp
      ring
    rw [arithmeticPrimitive, hrate, hcoe]
  have hres : signedWindowResidual m a B +
      (μ q : ℝ) * (((m : ℝ)+1)/((m : ℝ)*s)) * powerGap s a B =
        signedWindowResidual q a B := by
    rw [residual_succ_of_odd hm hodd, harith, hq']
    ring
  rw [hres]
  have hn : 2 ≤ q := by dsimp [q]; omega
  have hsigned : |signedWindowResidual q a B| ≤
      K*((q : ℝ)*(1+Real.log (q : ℝ))^2)*powerGap (orderRate q) a B := by
    have ar (n : ℕ) : -(arithmeticRate n) = (n : ℝ)⁻¹-1/2 := by unfold arithmeticRate; ring
    have or : -(orderRate q) = ((q : ℝ)+1)⁻¹-1/2 := by unfold orderRate; ring
    simpa only [signedWindowResidual, arithmeticPrimitive, powerGap, ar, or]
      using hb q hn a B ha hAB
  rw [hr] at hsigned
  refine ⟨hsigned, ?_⟩
  exact (mul_le_mul_of_nonneg_left (power_gap_of_rate_increase hs hδ ha' hAB)
    (by positivity : 0 ≤ K*((q : ℝ)*(1+Real.log (q : ℝ))^2))).trans_eq (by ring)

open Filter Topology

/-- Unbounded prime cutoffs exclude a uniform negative power, even on very late windows. -/
theorem signed_window_no_negative_order_exponent (hRH : RiemannHypothesis)
    {γ : ℝ} (hγ : 0 < γ) (K : ℝ) (lowerStart : ℕ → ℝ) (N : ℕ) :
    ∃ M : ℕ, max 2 N ≤ M ∧ ∀ m : ℕ, M ≤ m → (m+1).Prime →
      ∃ S : ℝ, max 2 (lowerStart m) ≤ S ∧ ∀ a B : ℝ, S ≤ a → a < B →
        K * (m : ℝ)^(-γ) * powerGap (orderRate m) a B < signedWindowResidual m a B := by
  have hmSmall : ∀ᶠ x : ℝ in atTop, K*x^(-γ) < 1 := by
    have h : Tendsto (fun x : ℝ => K*x^(-γ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℝ => K) atTop (𝓝 K) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul (tendsto_rpow_neg_atTop hγ)
    exact h.eventually_lt_const zero_lt_one
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hmSmall
  obtain ⟨M, hM⟩ := exists_nat_ge T
  let M₀ := max (max 2 N) M
  refine ⟨M₀, le_max_left _ _, fun m hm hprime => ?_⟩
  have hm₂ : 2 ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmM : M ≤ m := (le_max_right _ _).trans hm
  have hT' : T ≤ (m : ℝ) := hM.trans (by exact_mod_cast hmM)
  have hmBound := hT (m : ℝ) hT'
  have hodd : Odd (m+1) := hprime.odd_of_ne_two (by omega)
  obtain ⟨a₀, J, ha₀, hJ, hexpansion⟩ := signed_window_odd_cutoff_expansion hRH
  let s := orderRate m
  let δ := ((m : ℝ)+1)⁻¹-((m : ℝ)+2)⁻¹
  let W := J*(((m+1 : ℕ) : ℝ)*(1+Real.log ((m+1 : ℕ) : ℝ))^2)
  let C := W*((s+δ)/s)
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hs : 0 < s := by
    have hi := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) < (m : ℝ)+1 by linarith)
    dsimp [s, orderRate]
    norm_num at hi
    linarith
  have hs' : s < 1/2 := by
    dsimp only [s, orderRate]
    exact sub_lt_self _ (by positivity)
  have hδ : 0 < δ := sub_pos.mpr (inv_strictAnti₀ (by positivity) (by linarith))
  have hsmall : ∀ᶠ x : ℝ in atTop, C*x^(-δ) < 1 := by
    have h : Tendsto (fun x : ℝ => C*x^(-δ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℝ => C) atTop (𝓝 C) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul (tendsto_rpow_neg_atTop hδ)
    exact h.eventually_lt_const zero_lt_one
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hsmall
  let lower := max S (max a₀ (max 2 (lowerStart m)))
  refine ⟨lower, ?_, fun a B haLower hab => ?_⟩
  · dsimp only [lower]
    exact (le_max_right a₀ _).trans (le_max_right S _)
  have ha : a₀ ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans haLower)
  have ha' : 0 < a := by linarith
  have hgap : 0 < powerGap s a B := by
    exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg ha' hab (neg_neg_of_pos hs))
  have hδbound : C*a^(-δ) < 1 := hS a ((le_max_left _ _).trans haLower)
  have hcoe : 2 < ((m : ℝ)+1)/((m : ℝ)*s) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    have hms := mul_lt_mul_of_pos_left hs' (show (0 : ℝ) < m by linarith)
    linarith only [hms]
  have hb := hexpansion m hm₂ hodd a B ha hab.le
  have he := hb.1.trans hb.2
  rw [ArithmeticFunction.moebius_apply_prime hprime] at he
  norm_num only [Int.cast_neg, Int.cast_one, neg_one_mul] at he
  change |signedWindowResidual m a B + -(((m : ℝ)+1)/((m : ℝ)*s)) * powerGap s a B| ≤
    C*a^(-δ)*powerGap s a B at he
  have hlo := (abs_le.mp he).1
  have hprod := mul_lt_mul_of_pos_right hcoe hgap
  have hδprod := mul_lt_mul_of_pos_right hδbound hgap
  have hmb := mul_lt_mul_of_pos_right hmBound hgap
  linarith only [hlo, hprod, hδprod, hmb]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
