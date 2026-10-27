/- GID: D5/S3/AnalyticClosure/PrimeSpectrumHeatL2
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A geometric prime majorant quantitatively bounds the heat trace and L2 coefficient norm. -/

import Mathlib
import D5.S3.AnalyticClosure.PrimeSpectrumBoundaryDivergent

namespace D5.S3.AnalyticClosure.PrimeSpectrumHeatL2

open D5.S3.AnalyticClosure.PrimeSpectrumBoundaryDivergent
open D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

/-- The logarithmic length of a prime-by-natural spectrum. -/
def primeSpectrum (beta : Nat → ℝ) : Nat.Primes × Nat → ℝ :=
  fun pk => beta (pk.2 + 1) * Real.log (pk.1 : ℝ)

/-- Linear exponent growth controls the whole real heat trace by a prime sum
and one explicit geometric factor. -/
theorem prime_spectrum_heat_trace_geometric_bound (beta : Nat → ℝ) (b0 σ : ℝ)
    (h0 : 0 < b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (hσ : 1 / b0 < σ) :
    (∑' pk : Nat.Primes × Nat, Real.exp (-σ * primeSpectrum beta pk)) ≤
      (∑' p : Nat.Primes, (p : ℝ) ^ (-σ * b0)) /
        (1 - (2 : ℝ) ^ (-σ)) := by
  have hcritical : 1 < σ * b0 := (div_lt_iff₀ h0).mp hσ
  have hσpos : 0 < σ := lt_trans (by positivity : 0 < 1 / b0) hσ
  let q : ℝ := (2 : ℝ) ^ (-σ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ * b0)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hgeom : Summable (fun k : Nat => q ^ k) :=
    summable_geometric_of_lt_one hq0 hq1
  have hmajor : Summable (fun pk : Nat.Primes × Nat =>
      (pk.1 : ℝ) ^ (-σ * b0) * q ^ pk.2) := by
    apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
    refine ⟨fun p => hgeom.mul_left ((p : ℝ) ^ (-σ * b0)), ?_⟩
    simpa only [tsum_mul_left] using hbase.mul_right (∑' k : Nat, q ^ k)
  have hpoint (pk : Nat.Primes × Nat) :
      Real.exp (-σ * primeSpectrum beta pk) ≤
        (pk.1 : ℝ) ^ (-σ * b0) * q ^ pk.2 := by
    have hp : 0 < (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.pos
    have hp2 : (2 : ℝ) ≤ (pk.1 : ℝ) := by exact_mod_cast pk.1.prop.two_le
    have hlogp : 0 ≤ Real.log (pk.1 : ℝ) := Real.log_nonneg (by linarith)
    have hlog : Real.log 2 ≤ Real.log (pk.1 : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    have hklog := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg pk.2 : (0 : ℝ) ≤ pk.2)
    have hlength : b0 * Real.log (pk.1 : ℝ) +
        (pk.2 : ℝ) * Real.log 2 ≤ primeSpectrum beta pk := by
      calc
        _ ≤ (b0 + (pk.2 : ℝ)) * Real.log (pk.1 : ℝ) := by nlinarith
        _ ≤ primeSpectrum beta pk :=
          mul_le_mul_of_nonneg_right (h2 pk.2) hlogp
    calc
      Real.exp (-σ * primeSpectrum beta pk) ≤
          Real.exp (-σ * (b0 * Real.log (pk.1 : ℝ) +
            (pk.2 : ℝ) * Real.log 2)) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hlength (neg_nonpos.mpr hσpos.le))
      _ = (pk.1 : ℝ) ^ (-σ * b0) * q ^ pk.2 := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
          ← Real.exp_add]
        congr 1
        ring
  have hsum : Summable (fun pk : Nat.Primes × Nat =>
      Real.exp (-σ * primeSpectrum beta pk)) :=
    hmajor.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hpoint
  calc
    _ ≤ ∑' pk : Nat.Primes × Nat,
        (pk.1 : ℝ) ^ (-σ * b0) * q ^ pk.2 := hsum.tsum_le_tsum hpoint hmajor
    _ = (∑' p : Nat.Primes, (p : ℝ) ^ (-σ * b0)) *
        (∑' k : Nat, q ^ k) := (hbase.tsum_mul_tsum hgeom hmajor).symm
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- The exact L2 domain, consumed by the quantitative norm bound below. -/
theorem prime_spectrum_heat_l2_iff (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1)) (s : ℂ) :
    Memℓp (heatCoefficient (primeSpectrum beta) s) 2 ↔
      1 / (2 * b0) < s.re := by
  have h := heat_coefficient_mem_iff_of_boundary_divergent
    (primeSpectrum beta) (1 / b0)
    (prime_spectrum_boundary_divergent beta b0 h0 h1 h2) s
  have hhalf : (1 / b0) / 2 = 1 / (2 * b0) := by field_simp [ne_of_gt h0]
  rwa [hhalf] at h

/-- In the exact L2 domain, a quantitative norm bound independent of the vertical parameter. -/
theorem prime_spectrum_heat_l2_norm_bound (beta : Nat → ℝ) (b0 : ℝ)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : ℝ) ≤ beta (k + 1))
    (σ t : ℝ) (hσ : 1 / (2 * b0) < σ) :
    let x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
      ⟨heatCoefficient (primeSpectrum beta) ((σ : ℂ) + Complex.I * (t : ℂ)),
        (prime_spectrum_heat_l2_iff beta b0 h0 h1 h2 _).2 (by simpa using hσ)⟩
    ‖x‖ ^ 2 ≤ (∑' p : Nat.Primes, (p : ℝ) ^ (-(2 * σ) * b0)) /
      (1 - (2 : ℝ) ^ (-(2 * σ))) := by
  let x : lp (fun _ : Nat.Primes × Nat => ℂ) 2 :=
    ⟨heatCoefficient (primeSpectrum beta) ((σ : ℂ) + Complex.I * (t : ℂ)),
      (prime_spectrum_heat_l2_iff beta b0 h0 h1 h2 _).2 (by simpa using hσ)⟩
  have htwice : 1 / b0 < 2 * σ := by
    have hhalf : (1 / b0) / 2 = 1 / (2 * b0) := by field_simp [ne_of_gt h0]
    rw [← hhalf] at hσ
    linarith
  have hcoord (a : Nat.Primes × Nat) :
      ‖x a‖ ^ (2 : ℝ) = Real.exp (-(2 * σ) * primeSpectrum beta a) := by
    change ‖heatCoefficient (primeSpectrum beta) ((σ : ℂ) + Complex.I * (t : ℂ)) a‖ ^
      (2 : ℝ) = _
    rw [heatCoefficient_norm, Real.rpow_two, pow_two, ← Real.exp_add]
    congr 1
    simp
    ring
  change ‖x‖ ^ 2 ≤ _
  calc
    ‖x‖ ^ 2 = ‖x‖ ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ = ∑' a : Nat.Primes × Nat, ‖x a‖ ^ (2 : ℝ) :=
      lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) x
    _ = ∑' a : Nat.Primes × Nat, Real.exp (-(2 * σ) * primeSpectrum beta a) :=
      tsum_congr hcoord
    _ ≤ _ := prime_spectrum_heat_trace_geometric_bound beta b0 (2 * σ) h0 h2 htwice

#print axioms prime_spectrum_heat_trace_geometric_bound
#print axioms prime_spectrum_heat_l2_norm_bound

end

end D5.S3.AnalyticClosure.PrimeSpectrumHeatL2
