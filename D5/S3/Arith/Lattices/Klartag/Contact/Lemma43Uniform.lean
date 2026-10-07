/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43Final
import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound8

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Gaussian
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

/-- `t ↦ PhiC (yOf a₀ t u)` is monotone: `yOf` is `c/√t`, which decreases in `t` when `c ≥ 0`
(and `PhiC` is antitone), while for `c < 0` both values are negative and `PhiC` is `1/2` at both. -/
theorem PhiC_yOf_mono {a₀ u t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') :
    PhiC (yOf a₀ t u) ≤ PhiC (yOf a₀ t' u) := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs' : Real.sqrt t ≤ Real.sqrt t' := Real.sqrt_le_sqrt htt
  have hs'0 : (0 : ℝ) < Real.sqrt t' := lt_of_lt_of_le hs hs'
  by_cases h : 0 ≤ a₀ - (u ^ 2)⁻¹
  · refine PhiC_antitone ?_
    unfold yOf
    gcongr
  · have h' : a₀ - (u ^ 2)⁻¹ < 0 := not_le.1 h
    rw [PhiC_of_nonpos (le_of_lt (by unfold yOf; exact div_neg_of_neg_of_pos h' hs)),
      PhiC_of_nonpos (le_of_lt (by unfold yOf; exact div_neg_of_neg_of_pos h' hs'0))]

/-- **The profile is monotone in `t`.**  This is what the small-`t` branch runs on. -/
theorem profile_mono_time {a₀ α W : ℝ} {n : ℕ} {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (r : ℝ) :
    profile a₀ α W n t r ≤ profile a₀ α W n t' r := by
  unfold profile
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact PhiC_yOf_mono ht htt

/-- `radiusOf` at `y = 0` is `t`-free: this is why Lemma 4.3's inner-ball term is a constant. -/
theorem radiusOf_zero_eq {a₀ α δ t : ℝ} : radiusOf a₀ α δ t 0 = (Real.sqrt a₀)⁻¹ / α + δ := by
  unfold radiusOf subst; norm_num

/-- **`radiusOf` inverts `yOf`.**  This is the reparameterisation. -/
theorem radiusOf_yOf {a₀ α δ v t : ℝ} (ht : 0 < t) (hv : 0 < v) :
    radiusOf a₀ α δ t (yOf a₀ t v) = v / α + δ := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  have key : a₀ - Real.sqrt t * yOf a₀ t v = (v ^ 2)⁻¹ := by
    unfold yOf; field_simp; ring
  unfold radiusOf subst
  rw [key, Real.sqrt_inv, Real.sqrt_sq hv.le, inv_inv]

theorem yOf_mul_sqrt {a₀ v t : ℝ} (ht : 0 < t) :
    yOf a₀ t v * Real.sqrt t = a₀ - (v ^ 2)⁻¹ := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold yOf; field_simp

theorem subst_sq_inv {a₀ s Y : ℝ} (hu : 0 < a₀ - s * Y) :
    ((subst a₀ s Y) ^ 2)⁻¹ = a₀ - s * Y := by
  rw [subst, inv_pow, Real.sq_sqrt hu.le, inv_inv]

theorem sqrtT_eq {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : T = 16 * Real.log n / (n : ℝ) ^ 2) :
    Real.sqrt T = 4 * Real.sqrt (Real.log n) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := drift_eq hn hT
  field_simp at h ⊢
  linarith

/-- `radiusOf a₀ α (√n/2) t 0`, written `t`-free. -/
noncomputable def rhoC (a₀ α : ℝ) (n : ℕ) : ℝ := (Real.sqrt a₀)⁻¹ / α + Real.sqrt n / 2

/-- `pieces_at_params`' constant: `K = e⁶ + e³(2/√(2π) + 2) + 2e³`. -/
noncomputable def Kc : ℝ :=
  Real.exp 6 + Real.exp 3 * (2 / Real.sqrt (2 * π) + 2) + 2 * Real.exp 3

theorem rhoC_nonneg {a₀ α : ℝ} {n : ℕ} (hα : 0 < α) : 0 ≤ rhoC a₀ α n := by
  unfold rhoC; positivity

theorem profile_zero_int {a₀ α W T : ℝ} {n : ℕ} {r : ℝ} (hr : W < r) :
    (∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) = 0 := by
  simp [profile_zero_of_gt hr]

theorem stronglyMeasurable_int {a₀ α W T : ℝ} {n : ℕ} :
    StronglyMeasurable (fun r : ℝ => ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t r) :=
  ((measurable_profile_uncurry (a₀ := a₀) (α := α) (W := W) (n := n)).comp
    measurable_swap).stronglyMeasurable.integral_prod_right'

/-- **`Params.integrable`, discharged.** -/
theorem integrable_radial_euclidean {a₀ α W T : ℝ} {n : ℕ} (hT : 0 ≤ T) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) := by
  have hsm : StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) :=
    stronglyMeasurable_int.comp_measurable (continuous_norm.measurable)
  have hbnd : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖‖ ≤ 1 / 2 * T := by
    intro x
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) T)
      (C := 1 / 2) (f := fun t => profile a₀ α W n t ‖x‖)
      (by simp [Real.volume_Ioc]) (fun t _ => norm_profile_le t ‖x‖)
    simpa [Real.volume_Ioc, max_eq_left hT] using h
  have h1 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) (Metric.closedBall 0 W) :=
    integrableOn_of_bounded' measurableSet_closedBall
      (measure_closedBall_lt_top).ne hsm.aestronglyMeasurable (M := 1 / 2 * T)
      (fun x _ => hbnd x)
  have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ t in Ioc (0 : ℝ) T, profile a₀ α W n t ‖x‖) (Metric.closedBall 0 W)ᶜ := by
    refine (integrableOn_zero (μ := volume)
      (s := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) W)ᶜ)).congr_fun ?_
      measurableSet_closedBall.compl
    intro x hx
    exact (profile_zero_int
      (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx)).symm
  rw [← integrableOn_univ, ← union_compl_self (Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) W)]
  exact h1.union h2

/-- Klartag's `a₀ = (1 − 1/n)⁻²`, p. 21 eq. (61). -/
noncomputable def a0C (n : ℕ) : ℝ := (1 - 1 / (n : ℝ))⁻¹ ^ 2

theorem horizon_eq (n : ℕ) : ChainDrift.horizon n = 16 * Real.log n / (n : ℝ) ^ 2 := rfl

theorem a0C_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ a0C n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (0 : ℝ) < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hinv : (1 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) h1]; simp
  unfold a0C; nlinarith

theorem a0C_le_four {n : ℕ} (hn : 2 ≤ n) : a0C n ≤ 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
    linarith
  have hinv : (1 - 1 / (n : ℝ))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hinv0 : (0 : ℝ) ≤ (1 - 1 / (n : ℝ))⁻¹ := by positivity
  unfold a0C; nlinarith

end D5.S3.Arith.Lattices.Klartag
