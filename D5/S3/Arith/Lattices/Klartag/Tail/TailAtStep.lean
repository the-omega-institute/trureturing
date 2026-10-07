/- GID: D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/TailAtStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ContactIntegrated
import D5.S3.Arith.Lattices.Klartag.Walk.ChainInputDom
import D5.S3.Arith.Lattices.Klartag.Completion.ParamsAdopted2

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA
open scoped ENNReal NNReal

/-- Klartag's tail argument is `yOf`: with `M₀ = a₀ − (α·r)⁻²` (eq. 61 at the scaled radius) and
`q = 1`, the argument of `Φ` in `padded_tail_of_increments` is `yOf a₀ t (α·r)`. -/
theorem tail_arg_eq (a₀ t u : ℝ) :
    (a₀ - (u ^ 2)⁻¹) / (Real.sqrt t * 1) = yOf a₀ t u := by
  unfold yOf; rw [mul_one]

/-- An `ℝ≥0∞` tail bound read as a real one. -/
theorem measureReal_le_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {s : Set Ω} {b : ℝ} (hb : 0 ≤ b)
    (h : μ s ≤ ENNReal.ofReal b) : μ.real s ≤ b := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hb] at this

theorem riemann_lower_le {f : ℝ → ℝ} {hstep : ℝ} {N : ℕ} (hh : 0 < hstep)
    (hf0 : ∀ t, 0 ≤ f t)
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → f s ≤ f t)
    (hint : ∀ b : ℝ, IntegrableOn f (Ioc (0 : ℝ) b)) :
    ∑ k ∈ Finset.range N, hstep * (if k = 0 then 0 else f ((k : ℝ) * hstep))
      ≤ ∫ t in Ioc (0 : ℝ) ((N : ℝ) * hstep), f t := by
  have hIOC : ∀ k : ℕ, IntegrableOn f (Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep)) := by
    intro k
    exact (hint (((k : ℝ) + 1) * hstep)).mono_set
      (Ioc_subset_Ioc_left (by positivity))
  have hadj : ∀ k ∈ Finset.range N,
      hstep * (if k = 0 then 0 else f ((k : ℝ) * hstep))
        ≤ ∫ t in Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep), f t := by
    intro k _
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, mul_zero]
      exact setIntegral_nonneg measurableSet_Ioc (fun t _ => hf0 t)
    · rw [if_neg hk]
      have hkpos : (0 : ℝ) < (k : ℝ) * hstep := by
        have hk1 : (0 : ℝ) < (k : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        positivity
      have hconstint : IntegrableOn (fun _ : ℝ => f ((k : ℝ) * hstep))
          (Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep)) :=
        integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc])
          aestronglyMeasurable_const (M := ‖f ((k : ℝ) * hstep)‖) (fun _ _ => le_rfl)
      have hle := setIntegral_mono_on hconstint (hIOC k) measurableSet_Ioc
        (fun t ht => hmono _ _ hkpos ht.1.le)
      rwa [setIntegral_const, measureReal_def, Real.volume_Ioc,
        show ((k : ℝ) + 1) * hstep - (k : ℝ) * hstep = hstep by ring,
        ENNReal.toReal_ofReal hh.le, smul_eq_mul] at hle
  refine le_trans (Finset.sum_le_sum hadj) (le_of_eq ?_)
  have hcast : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * hstep = ((k : ℝ) + 1) * hstep := by
    intro k; push_cast; ring
  have hII : ∀ k : ℕ, IntervalIntegrable f volume ((k : ℝ) * hstep) (((k : ℕ) + 1 : ℕ) * hstep) := by
    intro k
    rw [hcast k, intervalIntegrable_iff_integrableOn_Ioc_of_le (by nlinarith)]
    exact hIOC k
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) * hstep) (f := f) (μ := volume) (n := N)
    (fun k _ => hII k)
  have hrw : ∀ k : ℕ, (∫ t in ((k : ℝ) * hstep)..(((k + 1 : ℕ) : ℝ) * hstep), f t)
      = ∫ t in Ioc ((k : ℝ) * hstep) (((k : ℝ) + 1) * hstep), f t := by
    intro k
    rw [hcast k, intervalIntegral.integral_of_le (by nlinarith)]
  simp_rw [hrw] at hsum
  rw [hsum, Nat.cast_zero, zero_mul, intervalIntegral.integral_of_le (by positivity)]

theorem adopted_horizon {n : ℕ} (hn : 3 ≤ n) :
    (ParamsAdopted2.numStepsAdopted2 n : ℝ) * ParamsAdopted2.stepSizeAdopted2 n
      = ChainDrift.horizon n :=
  ParamsAdopted2.numStepsAdopted2_mul_stepSizeAdopted2 hn

theorem horizon_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ChainDrift.horizon n := by
  have hlog : (1 : ℝ) ≤ Real.log n := ChainDrift.log_pos_of_three hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [ChainDrift.horizon]
  exact div_pos (by linarith) (by positivity)

theorem adopted_stepSize_pos {n : ℕ} (hn : 3 ≤ n) : 0 < ParamsAdopted2.stepSizeAdopted2 n := by
  rw [ParamsAdopted2.stepSizeAdopted2, ChainDrift.stepSize]
  exact div_pos (horizon_pos hn) (ChainDrift.numSteps_pos hn)

/-- **`Params.dom` against `c · profile`.**  `dom_of_tail` rescaled; `c ≥ 0` is all that is used. -/
theorem dom_of_tail2 {n : ℕ} (hn : 0 < n) {a₀ α W T c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (w : (Fin n → ℤ) → ℝ≥0∞) (supp : Finset (Fin n → ℤ))
    (htail : ∀ y ∈ supp, w y ≤ ENNReal.ofReal
      (c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t ‖toE n y‖)) :
    ∀ y ∈ supp, ∀ x ∈ cube (toE n y),
      w y ≤ ENNReal.ofReal (c * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) := by
  intro y hy x hx
  have hbase : Antitone (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t r) :=
    antitone_integral (fun t ht => profileAt_antitone hα ht.1)
      (fun r => integrableOn_profile_time (r + Real.sqrt n / 2))
  have hanti : Antitone (fun r : ℝ => c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t r) :=
    fun _ _ h => mul_le_mul_of_nonneg_left (hbase h) hc
  have hwide := dom_of_antitone hn hanti supp y hy x hx
  have heq : (c * ∫ t in Ioc (0 : ℝ) T, profileAt a₀ α W n t (‖x‖ - Real.sqrt n / 2))
      = c * ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖ := by
    simp [profileAt, sub_add_cancel]
  rw [heq] at hwide
  exact le_trans (htail y hy) hwide

end D5.S3.Arith.Lattices.Klartag
