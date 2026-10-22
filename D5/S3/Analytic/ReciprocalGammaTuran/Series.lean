/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Exact formal Cauchy coefficients and their boundary specialization. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Defs
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section
open scoped BigOperators
open Finset
open D5.S3.Analytic.ReciprocalGammaTuran.Defs

namespace D5.S3.Analytic.ReciprocalGammaTuran.Series

/-- The formal series for an arbitrary coefficient sequence. -/
def formalSeries (g : ℕ → ℝ) (b : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => g n * rgamma ((n : ℝ) + b))

/-- The formal boundary Turanian. -/
def boundarySeries (t : ℝ) : PowerSeries ℝ :=
  formalSeries (fun _ => 1) 0 ^ 2 -
    formalSeries (fun _ => 1) (-t) * formalSeries (fun _ => 1) t

/-- Boundary coefficients in the ordinary power basis. -/
def d (t : ℝ) (m : ℕ) : ℝ := PowerSeries.coeff m (boundarySeries t)

/-- The pinned finite sum is exactly the coefficient of the formal products. -/
theorem coeff_mul (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) :
    PowerSeries.coeff m
      (formalSeries g (μ + α) * formalSeries g (μ + β) -
        formalSeries g μ * formalSeries g (μ + α + β)) = turanCoeff g μ α β m := by
  simp only [map_sub, PowerSeries.coeff_mul, formalSeries, PowerSeries.coeff_mk,
    ← Finset.sum_sub_distrib, turanCoeff]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    (g i * rgamma (i + (μ + α)) * (g j * rgamma (j + (μ + β)))) -
    (g i * rgamma (i + μ) * (g j * rgamma (j + (μ + α + β))))) m]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  simp only [add_assoc]
  ring

/-- The boundary specialization identifies the pinned coefficients with `d`. -/
theorem turanCoeff_one_boundary (t : ℝ) (m : ℕ) :
    turanCoeff (fun _ => 1) (-t) t t m = d t m := by
  have h := coeff_mul (fun _ => (1 : ℝ)) (-t) t t m
  simpa [d, boundarySeries, pow_two] using h.symm


end D5.S3.Analytic.ReciprocalGammaTuran.Series
