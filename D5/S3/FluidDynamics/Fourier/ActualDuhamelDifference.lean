/- GID: D5/S3/FluidDynamics/Fourier/ActualDuhamelDifference
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/ActualDuhamelDifference
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: none
   digest: Two actual full-frequency Duhamel paths obey a closed-interval difference estimate. -/

import Mathlib
import D5.S3.FluidDynamics.Fourier.ActualTensorDuhamel

open scoped ENNReal BigOperators
open Set MeasureTheory
open D5.S3.FluidDynamics.Fourier.WeightedTensorConvolution
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.ActualDuhamelDifference

set_option maxHeartbeats 4000000 in
-- Four full-lattice paths and three Bochner coefficient identities are elaborated together.
/-- The actual bilinear row-divergence heat paths have a difference controlled by
the differences of both input paths, on the original closed time interval. -/
theorem actual_duhamel_difference (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    let K := ℤ × ℤ
    let V := EuclideanSpace ℂ (Fin 2)
    let TV := EuclideanSpace ℂ (Fin 2 × Fin 2)
    let H := lp (fun _ : K => V) 2
    let G := lp (fun _ : K => TV) 2
    let ρ : K → ℝ := fun k => (k.1 : ℝ)^2 + (k.2 : ℝ)^2
    let κ : K → V := fun k => WithLp.toLp 2 (fun i => (![k.1, k.2] i : ℂ))
    let P := fun k => (ℂ ∙ κ k)ᗮ.starProjection
    ∀ (x y z w : ℝ → H), ContinuousOn x (Icc 0 τ) →
      ContinuousOn y (Icc 0 τ) → ContinuousOn z (Icc 0 τ) →
      ContinuousOn w (Icc 0 τ) →
      ∀ (Mx My Mz Mw Dx Dy : ℝ),
        0 ≤ Mx → 0 ≤ My → 0 ≤ Mz → 0 ≤ Mw → 0 ≤ Dx → 0 ≤ Dy →
        (∀ t ∈ Icc 0 τ, ‖x t‖ ≤ Mx) →
        (∀ t ∈ Icc 0 τ, ‖y t‖ ≤ My) →
        (∀ t ∈ Icc 0 τ, ‖z t‖ ≤ Mz) →
        (∀ t ∈ Icc 0 τ, ‖w t‖ ≤ Mw) →
        (∀ t ∈ Icc 0 τ, ‖x t - z t‖ ≤ Dx) →
        (∀ t ∈ Icc 0 τ, ‖y t - w t‖ ≤ Dy) →
    ∃ Dxy Dzw : ℝ → H, Continuous Dxy ∧ Continuous Dzw ∧
      Dxy 0 = 0 ∧ Dzw 0 = 0 ∧
      (∀ t ∈ Icc 0 τ, ‖Dxy t‖ ≤ 32 * Mx * My * Real.sqrt (t / ν)) ∧
      (∀ t ∈ Icc 0 τ, ‖Dzw t‖ ≤ 32 * Mz * Mw * Real.sqrt (t / ν)) ∧
      (∀ t ∈ Icc 0 τ, ∀ k : K,
        Dxy t k = ∫ s in (0 : ℝ)..t,
          Real.exp (-ν * (t-s) * ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j *
                (weight k • convolution
                  (fun l => (weight l)⁻¹ • x s l)
                  (fun l => (weight l)⁻¹ • y s l) k) (i,j))))) ∧
      (∀ t ∈ Icc 0 τ, ∀ k : K,
        Dzw t k = ∫ s in (0 : ℝ)..t,
          Real.exp (-ν * (t-s) * ρ k) •
            (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
              ∑ j : Fin 2, κ k j *
                (weight k • convolution
                  (fun l => (weight l)⁻¹ • z s l)
                  (fun l => (weight l)⁻¹ • w s l) k) (i,j))))) ∧
      ∀ t ∈ Icc 0 τ,
        ‖Dxy t - Dzw t‖ ≤
          32 * (Dx * My + Mz * Dy) * Real.sqrt (t / ν) := by
  classical
  intro K V TV H G ρ κ P x y z w hx hy hz hw
    Mx My Mz Mw Dx Dy hMx hMy hMz hMw hDx hDy hxb hyb hzb hwb hdiffx hdiffy
  obtain ⟨qxy, hqxyc, hqxyb, hqxyk, -, hqxycmp, -, Dxy, hDxyc, hDxy0,
      hDxyb, -, -, hDxyk⟩ :=
    D5.S3.FluidDynamics.Fourier.ActualTensorDuhamel.continuous_weighted_tensor_duhamel
      ν τ hν hτ x y hx hy Mx My hMx hMy hxb hyb
  obtain ⟨qzw, hqzwc, hqzwb, hqzwk, -, -, -, Dzw, hDzwc, hDzw0,
      hDzwb, -, -, hDzwk⟩ :=
    D5.S3.FluidDynamics.Fourier.ActualTensorDuhamel.continuous_weighted_tensor_duhamel
      ν τ hν hτ z w hz hw Mz Mw hMz hMw hzb hwb
  let C : ℝ := 16 * Dx * My + 16 * Mz * Dy
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hqdiff (t : ℝ) (ht : t ∈ Icc 0 τ) :
      ‖qxy t - qzw t‖ ≤ C := by
    have h := hqxycmp t ht (z t) (w t) (qzw t) (hqzwk t ht)
    calc
      ‖qxy t - qzw t‖ ≤
          16 * ‖x t - z t‖ * ‖y t‖ + 16 * ‖z t‖ * ‖y t - w t‖ := h
      _ ≤ C := by
        dsimp [C]
        have ha : 16 * ‖x t - z t‖ * ‖y t‖ ≤ 16 * Dx * My :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hdiffx t ht) (by norm_num))
            (hyb t ht) (norm_nonneg _) (mul_nonneg (by norm_num) hDx)
        have hb : 16 * ‖z t‖ * ‖y t - w t‖ ≤ 16 * Mz * Dy :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hzb t ht) (by norm_num))
            (hdiffy t ht) (norm_nonneg _) (mul_nonneg (by norm_num) hMz)
        linarith
  let qc : C(Icc (0:ℝ) τ, G) :=
    ⟨fun t => qxy t - qzw t,
      continuousOn_iff_continuous_domRestrict.mp (hqxyc.sub hqzwc)⟩
  let qe : ℝ → G := fun t => qc (projIcc 0 τ hτ.le t)
  have hqe : Continuous qe := qc.continuous.comp continuous_projIcc
  have hqeb (t : ℝ) : ‖qe t‖ ≤ C :=
    hqdiff (projIcc 0 τ hτ.le t).1 (projIcc 0 τ hτ.le t).2
  obtain ⟨Ddiff, hDdiffc, hDdiff0, hDdiffb, hDdiffk⟩ :=
    D5.S3.FluidDynamics.Fourier.BochnerRowHeatPath.bochner_row_heat_path
      ν τ hν hτ qe hqe C hC hqeb
  have hqxy_ext : Continuous (fun s : ℝ =>
      (⟨fun t : Icc (0:ℝ) τ => qxy t,
        continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G))
        (projIcc 0 τ hτ.le s)) :=
    (⟨fun t : Icc (0:ℝ) τ => qxy t,
      continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G)).continuous.comp
        continuous_projIcc
  have hqzw_ext : Continuous (fun s : ℝ =>
      (⟨fun t : Icc (0:ℝ) τ => qzw t,
        continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G))
        (projIcc 0 τ hτ.le s)) :=
    (⟨fun t : Icc (0:ℝ) τ => qzw t,
      continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G)).continuous.comp
        continuous_projIcc
  let qxe : ℝ → G := fun s =>
    (⟨fun t : Icc (0:ℝ) τ => qxy t,
      continuousOn_iff_continuous_domRestrict.mp hqxyc⟩ : C(Icc 0 τ,G))
      (projIcc 0 τ hτ.le s)
  let qze : ℝ → G := fun s =>
    (⟨fun t : Icc (0:ℝ) τ => qzw t,
      continuousOn_iff_continuous_domRestrict.mp hqzwc⟩ : C(Icc 0 τ,G))
      (projIcc 0 τ hτ.le s)
  have hqxe_eq (s : ℝ) (hs : s ∈ Icc 0 τ) : qxe s = qxy s := by
    dsimp [qxe]; rw [projIcc_of_mem _ hs]; rfl
  have hqze_eq (s : ℝ) (hs : s ∈ Icc 0 τ) : qze s = qzw s := by
    dsimp [qze]; rw [projIcc_of_mem _ hs]; rfl
  have hqe_sub (s : ℝ) : qe s = qxe s - qze s := by
    dsimp [qe, qxe, qze, qc]
    rfl
  have hrow_cont (q : ℝ → G) (hq : Continuous q) (k : K) :
      Continuous (fun s : ℝ => (WithLp.toLp 2 (fun i : Fin 2 =>
        ∑ j : Fin 2, κ k j * q s k (i,j)) : V)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul
      ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 2 × Fin 2 => ℂ) (i,j)).continuous.comp
        ((lp.evalCLM ℝ (fun _ : K => TV) 2 k).continuous.comp hq))
  have hkernel_cont (q : ℝ → G) (hq : Continuous q) (t : ℝ) (k : K) :
      Continuous (fun s : ℝ => Real.exp (-ν * (t-s) * ρ k) •
        (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ k j * q s k (i,j))))) := by
    exact (Real.continuous_exp.comp (by fun_prop)).smul
      ((continuous_const : Continuous (fun _ : ℝ => (Complex.I : ℂ))).smul
        ((P k).continuous.comp (hrow_cont q hq k)))
  have hD_eq (t : ℝ) (ht : t ∈ Icc 0 τ) : Dxy t - Dzw t = Ddiff t := by
    apply lp.ext
    funext k
    let f : (ℝ → G) → ℝ → V := fun q s =>
      Real.exp (-ν * (t-s) * ρ k) •
        (Complex.I • P k (WithLp.toLp 2 (fun i : Fin 2 =>
          ∑ j : Fin 2, κ k j * q s k (i,j))))
    have hfi : IntervalIntegrable (f qxe) volume 0 t :=
      (hkernel_cont qxe hqxy_ext t k).intervalIntegrable 0 t
    have hfj : IntervalIntegrable (f qze) volume 0 t :=
      (hkernel_cont qze hqzw_ext t k).intervalIntegrable 0 t
    have hfx : Dxy t k = ∫ s in (0:ℝ)..t, f qxe s := by
      rw [hDxyk t ht k]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 τ := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      dsimp [f]
      rw [hqxe_eq s hs', hqxyk s hs' k]
      rfl
    have hfz : Dzw t k = ∫ s in (0:ℝ)..t, f qze s := by
      rw [hDzwk t ht k]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 τ := by
        rw [uIcc_of_le ht.1] at hs
        exact ⟨hs.1, hs.2.trans ht.2⟩
      dsimp [f]
      rw [hqze_eq s hs', hqzwk s hs' k]
      rfl
    rw [lp.coeFn_sub, Pi.sub_apply, hfx, hfz, hDdiffk t ht k,
      ← intervalIntegral.integral_sub hfi hfj]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [f]
    have hcoord : qe s k = qxe s k - qze s k := by
      rw [hqe_sub]
      rfl
    rw [hcoord]
    let row : G → V := fun q => WithLp.toLp 2 (fun i : Fin 2 =>
      ∑ j : Fin 2, κ k j * q k (i,j))
    have hrow : row (qxe s) - row (qze s) = row (qxe s - qze s) := by
      ext i
      change (∑ j : Fin 2, κ k j * qxe s k (i,j)) -
          (∑ j : Fin 2, κ k j * qze s k (i,j)) =
          ∑ j : Fin 2, κ k j * (qxe s k (i,j) - qze s k (i,j))
      simp only [mul_sub, Finset.sum_sub_distrib]
    change Real.exp (-ν * (t-s) * ρ k) • (Complex.I • P k (row (qxe s))) -
        Real.exp (-ν * (t-s) * ρ k) • (Complex.I • P k (row (qze s))) =
        Real.exp (-ν * (t-s) * ρ k) •
          (Complex.I • P k (row (qxe s - qze s)))
    rw [← smul_sub, ← smul_sub, ← map_sub, hrow]
  refine ⟨Dxy, Dzw, hDxyc, hDzwc, hDxy0, hDzw0,
    hDxyb, hDzwb, hDxyk, hDzwk, ?_⟩
  intro t ht
  rw [hD_eq t ht]
  have h := hDdiffb t ht
  calc
    ‖Ddiff t‖ ≤ 2 * C * Real.sqrt (t / ν) := h
    _ = 32 * (Dx * My + Mz * Dy) * Real.sqrt (t / ν) := by
      dsimp [C]
      ring

#print axioms actual_duhamel_difference

end D5.S3.FluidDynamics.Fourier.ActualDuhamelDifference
