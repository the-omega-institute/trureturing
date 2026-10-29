/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary formal inverse coefficients of the actual depth-normalized composition. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators NNReal ENNReal

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionReciprocalSeries

/-- The ordinary formal inverse, with the source power and all positive parameters. -/
def ordinarySeries (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) : PowerSeries ℝ :=
  ((PowerSeries.mk (CompositionDisk.coefficient head tail)) ^ (ell : ℕ))⁻¹

/-- Ordinary coefficients: there is no exponential-generating factorial. -/
def ordinaryCoefficient (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (ordinarySeries head tail ell)

/-- The actual normalized analytic reciprocal, including its removable value at zero. -/
def reciprocal (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (z : ℂ) : ℂ :=
  (CompositionZeroFreeCollar.normalizedContinuation head tail z ^ (ell : ℕ))⁻¹

private def Represents (f : ℂ → ℂ) (p : PowerSeries ℂ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ PowerSeries.coeff n p)) 0

private theorem represents_unique {f : ℂ → ℂ} {p q : PowerSeries ℂ}
    (hp : Represents f p) (hq : Represents f q) : p = q := by
  have h := hp.eq_formalMultilinearSeries hq
  ext n
  simpa using congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ ↦ s.coeff n) h

private theorem represents_one : Represents (fun _ : ℂ ↦ 1) 1 := by
  apply hasFPowerSeriesAt_iff.mpr
  apply Eventually.of_forall
  intro z
  convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)) using 1
  funext n
  by_cases hn : n = 0 <;>
    simp [FormalMultilinearSeries.coeff_ofScalars, PowerSeries.coeff_one, hn]


private theorem represents_mul {f g : ℂ → ℂ} {p q : PowerSeries ℂ}
    (hp : Represents f p) (hq : Represents g q) :
    Represents (fun z ↦ f z * g z) (p * q) := by
  apply hasFPowerSeriesAt_iff.mpr
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  filter_upwards [Metric.eball_mem_nhds (0 : ℂ) hr.r_pos,
    Metric.eball_mem_nhds (0 : ℂ) hs.r_pos] with z hz hzs
  have hzrad := Metric.eball_subset_eball hr.r_le hz
  have hzsrad := Metric.eball_subset_eball hs.r_le hzs
  have habs := (FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ PowerSeries.coeff n p)).summable_norm_apply hzrad
  have hbabs := (FormalMultilinearSeries.ofScalars ℂ
    (fun n ↦ PowerSeries.coeff n q)).summable_norm_apply hzsrad
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at habs hbabs
  have hm := hasSum_sum_range_mul_of_summable_norm habs hbabs
  have hfp := hr.hasSum hz
  have hgq := hs.hasSum hzs
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at hfp hgq
  rw [hfp.tsum_eq, hgq.tsum_eq] at hm
  convert hm using 1
  · funext n
    simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      PowerSeries.coeff_mul, Finset.mul_sum]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : z ^ n = z ^ k * z ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hk']
    rw [hpow]
    ring
  · simp only [zero_add]


private theorem represents_pow {f : ℂ → ℂ} {p : PowerSeries ℂ}
    (hp : Represents f p) (n : ℕ) : Represents (fun z ↦ f z ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using represents_one
  | succ n ih => simpa [pow_succ] using represents_mul ih hp

private theorem analytic_represents {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ p : PowerSeries ℂ, Represents f p := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨PowerSeries.mk p.coeff, ?_⟩
  have heq : FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ PowerSeries.coeff n (PowerSeries.mk p.coeff)) = p := by
    funext n
    ext
    simp [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simpa only [Represents, heq] using hp

private theorem actual_series (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    HasFPowerSeriesAt (reciprocal head tail ell)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ (ordinaryCoefficient head tail ell n : ℂ))) 0 := by
  obtain ⟨hag, han, R0, hR0, hne⟩ := CompositionZeroFreeCollar.result head tail
  have h0omega : (0 : ℂ) ∈ CompositionContinuation.omega := by
    simp [CompositionContinuation.omega, Complex.mem_slitPlane_iff]
  have hrec : AnalyticAt ℂ (reciprocal head tail ell) 0 :=
    ((han 0 h0omega).pow (ell : ℕ)).inv
      (pow_ne_zero _ (hne 0 h0omega (by simpa using lt_trans zero_lt_one hR0)))
  obtain ⟨p, hp⟩ := analytic_represents hrec
  let f : PowerSeries ℝ := PowerSeries.mk (CompositionDisk.coefficient head tail)
  let fc : PowerSeries ℂ := PowerSeries.map Complex.ofRealHom f
  have hf : Represents (CompositionDisk.normalized head tail) fc := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hs := ((CompositionDisk.source_series head tail).2.2.1 z hz').of_norm.hasSum
    simpa [fc, f, CompositionDisk.normalized, mul_comm] using hs
  have hprod := represents_mul hp (represents_pow hf (ell : ℕ))
  have hpone : Represents (fun _ : ℂ ↦ 1) (p * fc ^ (ell : ℕ)) := by
    apply hprod.congr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    dsimp [reciprocal]
    rw [hag z hz']
    exact inv_mul_cancel₀ (pow_ne_zero _ ((CompositionZeroFree.result head tail).2.2.1 z hz'))
  have hpeq : p * fc ^ (ell : ℕ) = 1 := represents_unique hpone represents_one
  have hfzero : PowerSeries.constantCoeff (f ^ (ell : ℕ)) ≠ 0 := by
    simp only [map_pow, f, PowerSeries.constantCoeff_mk]
    exact pow_ne_zero _ ((CompositionDisk.source_series head tail).1 0).ne'
  have hqeq : PowerSeries.map Complex.ofRealHom (ordinarySeries head tail ell) *
      fc ^ (ell : ℕ) = 1 := by
    have h := congrArg (PowerSeries.map Complex.ofRealHom)
      (PowerSeries.inv_mul_cancel (f ^ (ell : ℕ)) hfzero)
    simpa [ordinarySeries, f, fc] using h
  have hfczero : PowerSeries.constantCoeff (fc ^ (ell : ℕ)) ≠ 0 := by
    rw [map_pow]
    apply pow_ne_zero
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [fc, f, PowerSeries.coeff_map, PowerSeries.coeff_mk, Complex.ofRealHom_eq_coe]
    exact Complex.ofReal_ne_zero.mpr ((CompositionDisk.source_series head tail).1 0).ne' 
  have hpq : p = PowerSeries.map Complex.ofRealHom (ordinarySeries head tail ell) := by
    have hunit := (PowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr hfczero))
    exact hunit.mul_right_cancel (hpeq.trans hqeq.symm)
  rw [hpq] at hp
  simpa only [Represents, PowerSeries.coeff_map, Complex.ofRealHom_eq_coe,
    ordinaryCoefficient] using hp

private theorem coefficient_circle (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (n : ℕ) :
    (ordinaryCoefficient head tail ell n : ℂ) = (2 * Real.pi * I : ℂ)⁻¹ *
      circleIntegral (fun z ↦ reciprocal head tail ell z / z ^ (n + 1)) 0 (1 / 2) := by
  obtain ⟨hag, han, R0, hR0, hne⟩ := CompositionZeroFreeCollar.result head tail
  have hdiff : DifferentiableOn ℂ (reciprocal head tail ell)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    have hn : ‖z‖ < 1 := by
      have h := Metric.mem_closedBall.mp hz
      simp only [dist_zero_right] at h
      linarith
    have hzomega : z ∈ CompositionContinuation.omega := by
      simpa [CompositionContinuation.omega, sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hn)
    exact (((han z hzomega).pow (ell : ℕ)).inv
      (pow_ne_zero _ (hne z hzomega (hn.trans hR0)))).differentiableAt.differentiableWithinAt
  have hc := hdiff.hasFPowerSeriesOnBall
    (R := (NNReal.mk (1 / 2) (by norm_num))) (by norm_num [← NNReal.coe_pos])
  have heq := (actual_series head tail ell).eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p n (fun _ ↦ 1)) heq
  rw [cauchyPowerSeries_apply] at h
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, div_eq_mul_inv, pow_succ,
    mul_comm, mul_left_comm, mul_assoc] using h

end D5.S3.AnalyticClosure.Polylogarithm.CompositionReciprocalSeries
