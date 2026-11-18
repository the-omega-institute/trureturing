/- GID: D5/S3/Analytic/Measure/NatFloorL2
   generality: G
   mirror-B: D5/B/S3/Analytic/Measure/NatFloorL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-summable sequences give natural-floor step functions in half-line L2. -/

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
Square summability of a sequence implies L² membership of its natural-floor
step function on `(1, ∞)`.  The proof uses the unit cells
`[n + 1, n + 2)` covering `[1, ∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Measure.NatFloorL2

open Set MeasureTheory
open scoped ENNReal

/-- A square-summable positive-index sequence defines an L² natural-floor
step function on the real half-line `(1, ∞)`.  No condition on `a 0` is needed. -/
theorem memLp_nat_floor_of_summable_sq (a : ℕ → ℝ)
    (ha : Summable (fun n : ℕ => (a (n + 1)) ^ 2)) :
    MemLp (fun x : ℝ => a (Nat.floor x)) 2
      (volume.restrict (Ioi (1 : ℝ))) := by
  let s : ℕ → Set ℝ := fun n =>
    Ico ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 1)
  have hfloor (n : ℕ) (x : ℝ) (hx : x ∈ s n) :
      Nat.floor x = n + 1 :=
    Nat.floor_eq_on_Ico (n + 1) x hx
  have hcover : (⋃ n : ℕ, s n) = Ici (1 : ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      change ((n + 1 : ℕ) : ℝ) ≤ x ∧
        x < ((n + 1 : ℕ) : ℝ) + 1 at hn
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ n + 1 by omega)
      exact hn1.trans hn.1
    · intro hx
      have hx1 : (1 : ℝ) ≤ x := hx
      have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
      have hfpos : 0 < Nat.floor x := Nat.floor_pos.mpr hx1
      have hsucc : Nat.floor x - 1 + 1 = Nat.floor x := by omega
      refine mem_iUnion.mpr ⟨Nat.floor x - 1, ?_⟩
      change ((Nat.floor x - 1 + 1 : ℕ) : ℝ) ≤ x ∧
        x < ((Nat.floor x - 1 + 1 : ℕ) : ℝ) + 1
      rw [hsucc]
      exact ⟨Nat.floor_le hx0, Nat.lt_floor_add_one x⟩
  have hcell (n : ℕ) :
      IntegrableOn (fun x : ℝ => (a (Nat.floor x)) ^ 2) (s n) volume := by
    have hc : IntegrableOn (fun _ : ℝ => (a (n + 1)) ^ 2) (s n) volume :=
      integrableOn_const (by simp [s])
    refine hc.congr_fun ?_ measurableSet_Ico
    intro x hx
    change (a (n + 1)) ^ 2 = (a (Nat.floor x)) ^ 2
    rw [hfloor n x hx]
  have hnorm (n : ℕ) :
      (∫ x in s n, ‖(a (Nat.floor x)) ^ 2‖) = (a (n + 1)) ^ 2 := by
    calc
      (∫ x in s n, ‖(a (Nat.floor x)) ^ 2‖) =
          ∫ _ in s n, (a (n + 1)) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change ‖(a (Nat.floor x)) ^ 2‖ = (a (n + 1)) ^ 2
        rw [hfloor n x hx, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg (a (n + 1)))]
      _ = (a (n + 1)) ^ 2 := by
        rw [setIntegral_const]
        simp [s, Real.volume_real_Ico]
  have hnorm_sum :
      Summable (fun n : ℕ => ∫ x in s n, ‖(a (Nat.floor x)) ^ 2‖) := by
    simpa only [hnorm] using ha
  have hsq_union :
      IntegrableOn (fun x : ℝ => (a (Nat.floor x)) ^ 2)
        (⋃ n : ℕ, s n) volume :=
    integrableOn_iUnion_of_summable_integral_norm hcell hnorm_sum
  have hsq_Ici :
      IntegrableOn (fun x : ℝ => (a (Nat.floor x)) ^ 2) (Ici (1 : ℝ)) volume := by
    rw [← hcover]
    exact hsq_union
  have hsq_Ioi :
      IntegrableOn (fun x : ℝ => (a (Nat.floor x)) ^ 2) (Ioi (1 : ℝ)) volume :=
    hsq_Ici.mono_set Ioi_subset_Ici_self
  have hm : Measurable (fun x : ℝ => a (Nat.floor x)) :=
    (measurable_of_countable a).comp Nat.measurable_floor
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq_Ioi

end D5.S3.Analytic.Measure.NatFloorL2
