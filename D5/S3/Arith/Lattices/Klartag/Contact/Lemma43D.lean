/- GID: D5/S3/Arith/Lattices/Klartag/Contact/Lemma43D
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Contact/Lemma43D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contact profile counts and accumulated projection dimension. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.Lemma43C
import D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Real
open D5.S3.Arith.Lattices.Klartag.Construction.Section5
open D5.S3.Arith.Lattices.Klartag.Construction.Tiling
open scoped ENNReal NNReal

section Projection

open D5.S3.Arith.Lattices.Klartag.Walk.ChainDataInst

end Projection

section Markov

end Markov

section Integrability

/-- Bounded and measurable on a finite-measure set is integrable there. -/
theorem integrableOn_of_bounded' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (hsm : MeasurableSet s) (hs : μ s ≠ ⊤) (hm : AEStronglyMeasurable f μ) {M : ℝ}
    (hb : ∀ x ∈ s, ‖f x‖ ≤ M) : IntegrableOn f s μ := by
  refine Measure.integrableOn_of_bounded (s_finite := hs) (f_mble := hm) (M := M) ?_
  filter_upwards [self_mem_ae_restrict hsm] with x hx
  exact hb x hx

/-- **`hgt`, discharged.**  The fixed-radius slice `t ↦ g t r` is integrable on `(0,T]` because it
is bounded and `(0,T]` has finite measure.  `Φ ≤ 1/2` supplies the bound. -/
theorem integrableOn_t_of_bounded {T : ℝ} {g : ℝ → ℝ → ℝ} {M : ℝ}
    (hm : ∀ r : ℝ, AEStronglyMeasurable (fun t : ℝ => g t r) volume)
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, ∀ r : ℝ, ‖g t r‖ ≤ M) (r : ℝ) :
    IntegrableOn (fun t : ℝ => g t r) (Ioc (0 : ℝ) T) :=
  integrableOn_of_bounded' measurableSet_Ioc (by simp [Real.volume_Ioc]) (hm r)
    (fun t ht => hb t ht r)

/-- **Extending integrability from a bounded window to `(0,∞)`.**  A profile supported in
`(0, L]` is integrable on `Ioi 0` as soon as it is integrable on the window.  This is what turns
the fixed-window bound into `RadialWeightData.radial_bound`'s `Ioi 0` statement. -/
theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : IntegrableOn f (Ioc (0 : ℝ) L)) (hzero : ∀ y : ℝ, L < y → f y = 0) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
  have htail : IntegrableOn f (Ioi L) := by
    have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi L) volume := integrableOn_zero
    refine h0.congr_fun ?_ measurableSet_Ioi
    intro y hy
    exact (hzero y hy).symm
  rw [hsplit]
  exact hf.union htail

end Integrability

end D5.S3.Arith.Lattices.Klartag
