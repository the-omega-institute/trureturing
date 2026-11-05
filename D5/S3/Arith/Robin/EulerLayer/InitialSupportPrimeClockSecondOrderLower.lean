/- GID: D5/S3/Arith/Robin/EulerLayer/InitialSupportPrimeClockSecondOrderLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayer/InitialSupportPrimeClockSecondOrderLower
   mirror-E: none(waiver:source-only-uncompiled)
   anchors: []
   utility: none
   digest: Uniform scalar near/far transfer to the actual largest-prime clock.

   SOURCE ONLY: UNCOMPILED / UNACCEPTED. No compiler was run for this source.
-/

import D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower
import D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import D5.S3.Arith.Robin.LogarithmBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower

open Finset Filter Asymptotics
open scoped Topology BigOperators Chebyshev
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail

noncomputable section

private def D (t : ℝ) : ℝ := Real.sqrt t * Real.log t
private def A : ℝ := 2 * Real.sqrt 2
private def c : ℝ := Real.log 2
private def B : ℝ := Real.sqrt 2 * (2 + c)
private def H (L : ℝ) : ℝ := A - B / (L - c) - 3200 / (L - c)^3
private def r (L : ℝ) : ℝ := 1 / ((1 + 1 / L^3) * (1 + 1 / L^4))

private def lowerX (X : ℝ) : ℝ :=
  A - B / Real.log X +
    Real.sqrt 2 * (8 + 4 * c + 3 * c^2 / 4) / (Real.log X)^2 -
      3200 / (Real.log X)^3

private theorem c_bounds : 0 < c ∧ c ≤ 1 := by
  constructor
  · exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [c]
    linarith

private theorem A_pos : 0 < A := by unfold A; positivity
private theorem B_nonneg : 0 ≤ B := by
  unfold B
  exact mul_nonneg (Real.sqrt_nonneg _) (by linarith [c_bounds.1])

/-- Only the already public factorization identity is used here. -/
private theorem support_clock_lower {m P : ℕ} (hm : 0 < m)
    (hsupport : m.primeFactors = Nat.primesLE P) :
    Chebyshev.theta (P : ℝ) ≤ Real.log (m : ℝ) := by
  have hsplit := D5.S3.Arith.Robin.EulerLayerInventoryGrowth.log_factorization_split hm
  have hQ : 0 ≤ ∑ p ∈ m.primeFactors,
      ((m.factorization p - 1 : ℕ) : ℝ) * Real.log p := by
    exact Finset.sum_nonneg (fun p hp =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
  rw [Chebyshev.theta_eq_sum_primesLE_log, ← hsupport]
  linarith

/-- A single theta threshold, including the finite lower half-window. -/
private theorem theta_window_eventually :
    ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 2 ≤ Real.log p ∧ p / 2 ≤ Chebyshev.theta p ∧
        Chebyshev.theta p ≤ p * (1 + 1 / (2 * (Real.log p)^3)) := by
  have herror : ∀ᶠ p : ℝ in atTop,
      |Chebyshev.theta p - p| ≤ p / (Real.log p)^8 := by
    filter_upwards [
      D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity.theta_error_eight.eventuallyLE,
      eventually_gt_atTop (1 : ℝ)] with p hp hp1
    simpa only [Real.norm_eq_abs, abs_of_pos
      (div_pos (by linarith : 0 < p) (pow_pos (Real.log_pos hp1) 8))] using hp
  filter_upwards [herror, Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with p herr hL2 hp1
  have hp : 0 < p := by linarith
  have hL : 0 < Real.log p := by linarith
  have h8 : (2 : ℝ) ≤ (Real.log p)^8 := by
    calc
      _ ≤ (2 : ℝ)^8 := by norm_num
      _ ≤ (Real.log p)^8 := by gcongr
  have h5 : (2 : ℝ) ≤ (Real.log p)^5 := by
    calc
      _ ≤ (2 : ℝ)^5 := by norm_num
      _ ≤ (Real.log p)^5 := by gcongr
  have h83 : 2 * (Real.log p)^3 ≤ (Real.log p)^8 := by
    calc
      _ ≤ (Real.log p)^5 * (Real.log p)^3 :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = _ := by ring
  have hhalf : p / (Real.log p)^8 ≤ p / 2 :=
    div_le_div_of_nonneg_left hp.le (by norm_num) h8
  have hsmall : p / (Real.log p)^8 ≤ p / (2 * (Real.log p)^3) :=
    div_le_div_of_nonneg_left hp.le (by positivity) h83
  have habs := abs_le.mp herr
  have hlower : p / 2 ≤ Chebyshev.theta p := by linarith [habs.1]
  have heq : p / (2 * (Real.log p)^3) = p * (1 / (2 * (Real.log p)^3)) := by ring
  rw [heq] at hsmall
  have hupper : Chebyshev.theta p ≤ p * (1 + 1 / (2 * (Real.log p)^3)) := by
    nlinarith only [habs.2, hsmall]
  exact ⟨hp1, hL2, hlower, hupper⟩

/-- Scalar rational functions in z=1/L; their denominators are 1 at z=0. -/
private def R (z : ℝ) : ℝ := 1 / ((1 + z^3) * (1 + z^4))
private def Q (z : ℝ) : ℝ := 1 / (1 - c * z)
private def G (z : ℝ) : ℝ :=
  -A * (z^2 + z^3 + z^6) * R z -
    B * (R z * Q z - 1) - 3200 * R z * z^2 * (Q z)^3

private theorem scalar_identity {L : ℝ} (hL : 0 < L) (hY : 0 < L - c) :
    L * (r L * H L - A) + B = G (L⁻¹) := by
  have h3 : 1 + L⁻¹ ^ 3 ≠ 0 := by positivity
  have h4 : 1 + L⁻¹ ^ 4 ≠ 0 := by positivity
  have h3a : 1 + 1 / L^3 ≠ 0 := by positivity
  have h4a : 1 + 1 / L^4 ≠ 0 := by positivity
  have hq : 1 - c * L⁻¹ ≠ 0 := by
    have heq : 1 - c * L⁻¹ = (L - c) / L := by field_simp [hL.ne']; ring
    rw [heq]
    exact (div_pos hY hL).ne'
  unfold r H G R Q
  field_simp [hL.ne', hY.ne', h3, h4, h3a, h4a, hq]
  <;> ring

/-- This limit is on a scalar real L only, before any integer m is introduced. -/
private theorem scalar_limits :
    Tendsto H atTop (𝓝 A) ∧
      Tendsto (fun L : ℝ => L * (r L * H L - A) + B) atTop (𝓝 0) := by
  have hY : Tendsto (fun L : ℝ => L - c) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (Filter.tendsto_atTop_add_const_right atTop (-c)
        (tendsto_id : Tendsto (fun L : Real => L) atTop atTop))
  have hH : Tendsto H atTop (𝓝 A) := by
    have h1 := hY.const_div_atTop B
    have h3 := ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hY)
      .const_div_atTop (3200 : ℝ)
    simpa [H] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atTop (𝓝 A)).sub h1).sub h3
  have hG : ContinuousAt G 0 := by
    unfold G R Q
    fun_prop (disch := norm_num)
  have hzero : G 0 = 0 := by norm_num [G, R, Q]
  have hlim : Tendsto (fun L : ℝ => G (L⁻¹)) atTop (𝓝 0) := by
    rw [← hzero]
    exact hG.tendsto.comp tendsto_inv_atTop_zero
  apply And.intro hH
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (max 0 c)] with L hL
  exact (scalar_identity (lt_of_le_of_lt (le_max_left _ _) hL)
    (by linarith [le_max_right (0 : ℝ) c])).symm

private theorem D_pos {t : ℝ} (ht : 1 < t) : 0 < D t := by
  exact mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos ht)

private theorem D_mono {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : D s ≤ D t := by
  exact mul_le_mul (Real.sqrt_le_sqrt hst)
    (Real.log_le_log (by linarith) hst) (Real.log_pos hs).le (Real.sqrt_nonneg t)

private theorem loglog_mono {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    Real.log (Real.log s) ≤ Real.log (Real.log t) := by
  exact Real.log_le_log (Real.log_pos hs) (Real.log_le_log (by linarith) hst)

/-- The near denominator grows by at most a*(1+L^(-4)). -/
private theorem D_near_upper {p : ℝ} (hp : 1 < p) (hL : 0 < Real.log p) :
    D (p * (1 + 1 / (Real.log p)^3)) ≤
      D p * ((1 + 1 / (Real.log p)^3) * (1 + 1 / (Real.log p)^4)) := by
  let L := Real.log p
  let a := 1 + 1 / L^3
  have hp0 : 0 < p := by linarith
  have hL0 : 0 < L := hL
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact le_add_of_nonneg_right (by positivity)
  have ha : 0 < a := by linarith
  have hpa : 1 < p * a :=
    hp.trans_le (by simpa using mul_le_mul_of_nonneg_left ha1 hp0.le)
  have hs : Real.sqrt a ≤ a := Real.sqrt_le_self_iff.mpr (Or.inr ha1)
  have hl : Real.log a ≤ 1 / L^3 := by
    have hh := Real.log_le_sub_one_of_pos ha
    dsimp [a] at hh
    linarith
  have hr : Real.sqrt (p * a) ≤ Real.sqrt p * a := by
    rw [Real.sqrt_mul hp0.le]
    exact mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg p)
  have hlog : Real.log (p * a) ≤ L + 1 / L^3 := by
    rw [Real.log_mul hp0.ne' ha.ne']
    exact add_le_add_left hl L
  change D (p * a) ≤ D p * (a * (1 + 1 / L^4))
  calc
    D (p * a) ≤ (Real.sqrt p * a) * (L + 1 / L^3) :=
      mul_le_mul hr hlog (Real.log_pos hpa).le (by positivity)
    _ = D p * (a * (1 + 1 / L^4)) := by
      unfold D
      change (Real.sqrt p * a) * (L + 1 / L^3) =
        (Real.sqrt p * L) * (a * (1 + 1 / L^4))
      field_simp [hL0.ne']
      <;> ring

/-- Dropping only the positive third-order term gives the scalar envelope H. -/
private theorem lowerX_envelope {p X : ℝ} (hp : 0 < p)
    (hL : 2 ≤ Real.log p) (hhalf : p / 2 ≤ X) : H (Real.log p) ≤ lowerX X := by
  have hY : 0 < Real.log p - c := by linarith [c_bounds.2]
  have hX : 0 < X := (div_pos hp (by norm_num)).trans_le hhalf
  have hlog : Real.log p - c ≤ Real.log X := by
    have hh := Real.log_le_log (div_pos hp (by norm_num)) hhalf
    rw [Real.log_div hp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    exact hh
  have hB := div_le_div_of_nonneg_left B_nonneg hY hlog
  have hpow : (Real.log p - c)^3 ≤ (Real.log X)^3 := by gcongr
  have h3200 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3200)
    (pow_pos hY 3) hpow
  have hc := c_bounds.1.le
  have hthird : 0 ≤ Real.sqrt 2 * (8 + 4 * c + 3 * c^2 / 4) / (Real.log X)^2 := by
    positivity
  unfold H lowerX
  linarith

/-- Uniform near transfer: the threshold is chosen before m and P. -/
private theorem near_clock_transfer {ε X₀ : ℝ} (hε : 0 < ε)
    (hbound : ∀ m P : ℕ, 0 < m → m.primeFactors = Nat.primesLE P →
      1 < Chebyshev.theta (P : ℝ) → X₀ ≤ Real.log (m : ℝ) →
      lowerX (Real.log (m : ℝ)) ≤ D (Real.log (m : ℝ)) *
        (tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (Chebyshev.theta (P : ℝ))))) :
    ∃ T : ℝ, ∀ m P : ℕ, 0 < m → m.primeFactors = Nat.primesLE P →
      1 < Chebyshev.theta (P : ℝ) → T ≤ (P : ℝ) →
      1 < (P : ℝ) → 2 ≤ Real.log (P : ℝ) →
      (P : ℝ) / 2 ≤ Chebyshev.theta (P : ℝ) → X₀ ≤ Real.log (m : ℝ) →
      Real.log (m : ℝ) ≤ (P : ℝ) * (1 + 1 / (Real.log (P : ℝ))^3) →
      -ε < Real.log (P : ℝ) * (D (P : ℝ) *
        (tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (Chebyshev.theta (P : ℝ)))) - A) + B := by
  have hH := (scalar_limits.1.comp Real.tendsto_log_atTop).eventually
    (lt_mem_nhds A_pos)
  have hF := (scalar_limits.2.comp Real.tendsto_log_atTop).eventually
    (lt_mem_nhds (by linarith : -ε < (0 : ℝ)))
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hH.and hF)
  apply Exists.intro T
  intro m P hm hs ht hTP hp1 hL2 hhalf hX₀ hnear
  let p : ℝ := P
  let X := Real.log (m : ℝ)
  let L := Real.log p
  let C := tail m + Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta p))
  have hp : 0 < p := by dsimp [p]; linarith
  have hL : 0 < L := by dsimp [L, p]; linarith
  have hXθ : Chebyshev.theta p ≤ X := support_clock_lower hm hs
  have hX1 : 1 < X := ht.trans_le hXθ
  have hhalfX : p / 2 ≤ X := hhalf.trans hXθ
  have hHC : H L ≤ D X * C :=
    (lowerX_envelope hp hL2 hhalfX).trans (hbound m P hm hs ht hX₀)
  have hC : 0 ≤ C := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (D_pos hX1).le (le_of_not_ge hn)
    linarith [(hT p hTP).1]
  let k := (1 + 1 / L^3) * (1 + 1 / L^4)
  have hk : 0 < k := by dsimp [k]; positivity
  have hD : D X ≤ D p * k :=
    (D_mono hX1 hnear).trans (D_near_upper hp1 hL)
  have hscaled : H L ≤ (D p * C) * k := by
    have hh := hHC.trans (mul_le_mul_of_nonneg_right hD hC)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  have htransfer : r L * H L ≤ D p * C := by
    change (1 / k) * H L ≤ D p * C
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hk).mpr hscaled
  have hfinal := (hT p hTP).2
  change -ε < L * (D p * C - A) + B
  have hh := mul_le_mul_of_nonneg_left htransfer hL.le
  change -ε < L * (r L * H L - A) + B at hfinal
  linarith only [hfinal, hh]

/-- The actual Mathlib power/log growth supplier, specialized to sqrt(p). -/
private theorem far_growth :
    Tendsto (fun p : ℝ => Real.sqrt p / (8 * (Real.log p)^3)) atTop atTop := by
  have hsmall : Tendsto (fun p : ℝ => (Real.log p)^3 / Real.sqrt p) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow] using
      (_root_.isLittleO_log_rpow_rpow_atTop (3 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h8 : Tendsto (fun p : ℝ => 8 * ((Real.log p)^3 / Real.sqrt p))
      atTop (𝓝 0) := by simpa using hsmall.const_mul 8
  have hpos : ∀ᶠ p : ℝ in atTop, 0 < 8 * ((Real.log p)^3 / Real.sqrt p) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
    exact mul_pos (by norm_num) (div_pos (pow_pos (Real.log_pos hp) 3)
      (Real.sqrt_pos.mpr (by linarith)))
  have hright : Tendsto (fun p : ℝ => 8 * ((Real.log p)^3 / Real.sqrt p))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h8, hpos⟩
  have hh := hright.inv_tendsto_nhdsGT_zero
  apply hh.congr'
  exact Eventually.of_forall (fun p => by
    change (8 * ((Real.log p)^3 / Real.sqrt p))⁻¹ =
      Real.sqrt p / (8 * (Real.log p)^3)
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring)

/-- Uniform far transfer, with the P in the tangent numerator cancelled. -/
private theorem far_clock_transfer {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ m P : ℕ, 1 < Chebyshev.theta (P : ℝ) → T ≤ (P : ℝ) →
      1 < (P : ℝ) → 2 ≤ Real.log (P : ℝ) →
      Chebyshev.theta (P : ℝ) ≤ (P : ℝ) * (1 + 1 / (2 * (Real.log (P : ℝ))^3)) →
      (P : ℝ) * (1 + 1 / (Real.log (P : ℝ))^3) < Real.log (m : ℝ) →
      0 ≤ tail m →
      -ε < Real.log (P : ℝ) * (D (P : ℝ) *
        (tail m + Real.log (Real.log (Real.log (m : ℝ))) -
          Real.log (Real.log (Chebyshev.theta (P : ℝ)))) - A) + B := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (far_growth.eventually_gt_atTop A)
  apply Exists.intro T
  intro m P ht hTP hp1 hL2 htheta hfar htail
  let p : ℝ := P
  let L := Real.log p
  let a := 1 + 1 / L^3
  let b := 1 + 1 / (2 * L^3)
  let X := Real.log (m : ℝ)
  let C := tail m + Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta p))
  have hp : 0 < p := by dsimp [p]; linarith
  have hL : 0 < L := by dsimp [L, p]; linarith
  have hL1 : 1 ≤ L := by dsimp [L, p]; linarith
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact le_add_of_nonneg_right (by positivity)
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact le_add_of_nonneg_right (by positivity)
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hab : b < a := by
    have hd : 0 < 1 / L^3 := by positivity
    have heq : 1 / (2 * L^3) = (1 / L^3) / 2 := by
      field_simp [hL.ne']
      <;> ring
    dsimp [a, b]
    rw [heq]
    linarith
  have hpa : 1 < p * a :=
    hp1.trans_le (by simpa using mul_le_mul_of_nonneg_left ha1 hp.le)
  have hpb : 1 < p * b :=
    hp1.trans_le (by simpa using mul_le_mul_of_nonneg_left hb1 hp.le)
  have hba : p * b < p * a := mul_lt_mul_of_pos_left hab hp
  have hXa : p * a < X := hfar
  have htlog := loglog_mono ht htheta
  have hXlog := loglog_mono hpa hXa.le
  have htangent := D5.S3.Arith.Robin.RestrictedDivisorStrictInventory.loglog_tangent
    hpa hpb (ne_of_gt hba)
  -- Exact tangent numerator: p*b-p*a = -(a-b)*p. The factor p cancels.
  have htangent' : (a - b) / (a * Real.log (p * a)) <
      Real.log (Real.log (p * a)) - Real.log (Real.log (p * b)) := by
    have hid : -( (p * b - p * a) *
        D5.S3.Arith.Robin.ActualRobinClockCovariance.g (p * a)) =
        (a - b) / (a * Real.log (p * a)) := by
      unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
      field_simp [hp.ne', ha.ne', (Real.log_pos hpa).ne']
      <;> ring
    linarith
  have hC : (a - b) / (a * Real.log (p * a)) < C := by
    dsimp [C]
    linarith
  have hL3 : 1 ≤ L^3 := by
    calc
      _ = (1 : ℝ)^3 := by norm_num
      _ ≤ L^3 := by gcongr
  have hdelta : 1 / L^3 ≤ 1 := (div_le_one (pow_pos hL 3)).mpr hL3
  have ha2 : a ≤ 2 := by dsimp [a]; linarith
  have hloga : Real.log a ≤ 1 / L^3 := by
    have hh := Real.log_le_sub_one_of_pos ha
    dsimp [a] at hh
    linarith
  have hlogpa : Real.log (p * a) ≤ 2 * L := by
    rw [Real.log_mul hp.ne' ha.ne']
    change L + Real.log a ≤ 2 * L
    linarith
  have hden : a * Real.log (p * a) ≤ 4 * L := by
    nlinarith [mul_le_mul ha2 hlogpa (Real.log_pos hpa).le (by norm_num : (0 : ℝ) ≤ 2)]
  have hdiff : a - b = 1 / (2 * L^3) := by
    dsimp [a, b]
    field_simp [hL.ne']
    <;> ring
  have hcoarse : 1 / (8 * L^4) ≤ (a - b) / (a * Real.log (p * a)) := by
    rw [hdiff]
    calc
      _ = (1 / (2 * L^3)) / (4 * L) := by field_simp [hL.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (mul_pos ha (Real.log_pos hpa)) hden
  have hDC : Real.sqrt p / (8 * L^3) < D p * C := by
    have hh := mul_lt_mul_of_pos_left (hcoarse.trans_lt hC) (D_pos hp1)
    have heq : D p * (1 / (8 * L^4)) = Real.sqrt p / (8 * L^3) := by
      unfold D
      change Real.sqrt p * L * (1 / (8 * L^4)) = Real.sqrt p / (8 * L^3)
      field_simp [hL.ne']
      <;> ring
    rwa [heq] at hh
  have hlarge : A < D p * C := (hT p hTP).trans hDC
  have hpositive : 0 < L * (D p * C - A) := mul_pos hL (sub_pos.mpr hlarge)
  change -ε < L * (D p * C - A) + B
  linarith [B_nonneg]

/-- One P-threshold before all positive initial-prime-support integers. -/
theorem initial_support_prime_clock_second_order_lower :
    ∀ ε : ℝ, 0 < ε →
      ∃ P₀ : ℝ, 1 < P₀ ∧
        ∀ m P : ℕ, 0 < m →
          P = largestPrime m →
          m.primeFactors = Nat.primesLE P →
          1 < Chebyshev.theta (P : ℝ) →
          P₀ ≤ (P : ℝ) →
          Real.log (P : ℝ) *
              (Real.sqrt (P : ℝ) * Real.log (P : ℝ) *
                  (OriginalEndpointPrimeTail.tail m +
                    Real.log (Real.log (Real.log (m : ℝ))) -
                    Real.log (Real.log (Chebyshev.theta (P : ℝ)))) -
                2 * Real.sqrt 2) +
              Real.sqrt 2 * (2 + Real.log 2) > -ε := by
  intro ε hε
  obtain ⟨X₀, hX₀, hbound⟩ :=
    D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower
      .uniform_min_tail_robin_second_order_lower
  obtain ⟨Tθ, hTθ⟩ := eventually_atTop.mp theta_window_eventually
  obtain ⟨Tnear, hTnear⟩ := near_clock_transfer hε (X₀ := X₀) (by
    intro m P hm hs ht hX
    simpa [lowerX, A, B, c, D] using hbound m P hm hs ht hX)
  obtain ⟨Tfar, hTfar⟩ := far_clock_transfer hε
  let P₀ := max (max Tθ (max Tnear Tfar)) (max 2 (2 * X₀))
  have hP₀ : 1 < P₀ := by
    have hh : (2 : ℝ) ≤ P₀ :=
      (le_max_left 2 (2 * X₀)).trans (le_max_right _ _)
    linarith
  apply Exists.intro P₀
  apply And.intro hP₀
  intro m P hm hPexact hsupport htheta hP₀P
  have hPT : max Tθ (max Tnear Tfar) ≤ (P : ℝ) :=
    (le_max_left _ _).trans hP₀P
  have hPθ : Tθ ≤ (P : ℝ) := (le_max_left _ _).trans hPT
  have hPnear : Tnear ≤ (P : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hPT)
  have hPfar : Tfar ≤ (P : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hPT)
  obtain ⟨hp1, hL2, hhalf, hupp⟩ := hTθ (P : ℝ) hPθ
  have hXθ := support_clock_lower hm hsupport
  have h2X₀ : 2 * X₀ ≤ (P : ℝ) :=
    (le_max_right 2 (2 * X₀)).trans ((le_max_right _ _).trans hP₀P)
  have hX₀m : X₀ ≤ Real.log (m : ℝ) := by
    have hX₀half : X₀ ≤ (P : ℝ) / 2 := by linarith
    exact hX₀half.trans (hhalf.trans hXθ)
  change -ε < Real.log (P : ℝ) * (D (P : ℝ) *
    (tail m + Real.log (Real.log (Real.log (m : ℝ))) -
      Real.log (Real.log (Chebyshev.theta (P : ℝ)))) - A) + B
  by_cases hnear : Real.log (m : ℝ) ≤ (P : ℝ) * (1 + 1 / (Real.log (P : ℝ))^3)
  · exact hTnear m P hm hsupport htheta hPnear hp1 hL2 hhalf hX₀m hnear
  · have hsupportQ : m.primeFactors = Nat.primesLE (largestPrime m) := by
      simpa only [hPexact] using hsupport
    have htail : 0 ≤ tail m := (tail_robin_data hm hsupportQ).1
    exact hTfar m P htheta hPfar hp1 hL2 hupp (lt_of_not_ge hnear) htail

end
end D5.S3.Arith.Robin.EulerLayer.InitialSupportPrimeClockSecondOrderLower
