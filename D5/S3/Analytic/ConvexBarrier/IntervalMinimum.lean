/- GID: D5/S3/Analytic/ConvexBarrier/IntervalMinimum
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/IntervalMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
An open bounded interval is not compact. Endpoint blowup, rather than a
compact-fiber hypothesis, makes each of its finite sublevel sets compact.
This supplies the attainment step used by Zhang--Fu--Dai, arXiv:2611.06404v1,
Theorem 3.5. Uncompiled proof source.
-/

open Set Filter
open scoped Topology

namespace D5.S3.Analytic.ConvexBarrier

/-- Sequential endpoint blowup suffices: this is the form supplied by
`IsLHSCB.boundary_blowup`, with no extra limit premise. -/
theorem interval_sublevel_isCompact {a b : ℝ} {H : ℝ → ℝ}
    (hH : ContinuousOn H (Ioo a b))
    (ha : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 a) → Tendsto (H ∘ v) atTop atTop)
    (hb : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 b) → Tendsto (H ∘ v) atTop atTop)
    (M : ℝ) : IsCompact {z : ℝ | z ∈ Ioo a b ∧ H z ≤ M} := by
  apply isCompact_Icc.of_isClosed_subset
  · apply isSeqClosed_iff_isClosed.mp
    intro v x hv hlim
    have hvI : ∀ n, v n ∈ Ioo a b := fun n => (hv n).1
    have hvM : ∀ n, H (v n) ≤ M := fun n => (hv n).2
    have hx : x ∈ Icc a b := isClosed_Icc.mem_of_tendsto hlim
      (Eventually.of_forall fun n => ⟨(hvI n).1.le,(hvI n).2.le⟩)
    have hxa : x ≠ a := by
      intro he
      have hd := ha v hvI (by simpa [he] using hlim)
      obtain ⟨n,hn⟩ := (hd.eventually (eventually_ge_atTop (M+1))).exists
      have := hvM n
      change M+1 ≤ H (v n) at hn
      linarith
    have hxb : x ≠ b := by
      intro he
      have hd := hb v hvI (by simpa [he] using hlim)
      obtain ⟨n,hn⟩ := (hd.eventually (eventually_ge_atTop (M+1))).exists
      have := hvM n
      change M+1 ≤ H (v n) at hn
      linarith
    have hxI : x ∈ Ioo a b :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),lt_of_le_of_ne hx.2 hxb⟩
    refine ⟨hxI,?_⟩
    exact le_of_tendsto ((hH.continuousAt (isOpen_Ioo.mem_nhds hxI)).tendsto.comp hlim)
      (Eventually.of_forall hvM)
  · exact fun _ h => ⟨h.1.1.le,h.1.2.le⟩

theorem interval_exists_isMinOn {a b z₀ : ℝ} {H : ℝ → ℝ}
    (hz₀ : z₀ ∈ Ioo a b) (hH : ContinuousOn H (Ioo a b))
    (ha : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 a) → Tendsto (H ∘ v) atTop atTop)
    (hb : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 b) → Tendsto (H ∘ v) atTop atTop) :
    ∃ z ∈ Ioo a b, IsMinOn H (Ioo a b) z := by
  let S : Set ℝ := {z | z ∈ Ioo a b ∧ H z ≤ H z₀}
  have hS : IsCompact S := interval_sublevel_isCompact hH ha hb (H z₀)
  have h₀ : z₀ ∈ S := ⟨hz₀,le_rfl⟩
  obtain ⟨z,hz,hm⟩ := hS.exists_isMinOn ⟨z₀,h₀⟩ (hH.mono fun _ h => h.1)
  refine ⟨z,hz.1,?_⟩
  intro y hy
  by_cases hle : H y ≤ H z₀
  · exact hm ⟨hy,hle⟩
  · exact (hm h₀).trans (lt_of_not_ge hle).le

theorem interval_exists_unique_min {a b z₀ : ℝ} {H : ℝ → ℝ}
    (hz₀ : z₀ ∈ Ioo a b) (hH : ContinuousOn H (Ioo a b))
    (hpos : ∀ z ∈ Ioo a b, 0 < (deriv^[2] H) z)
    (ha : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 a) → Tendsto (H ∘ v) atTop atTop)
    (hb : ∀ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a b) →
      Tendsto v atTop (𝓝 b) → Tendsto (H ∘ v) atTop atTop) :
    ∃! z : ℝ, z ∈ Ioo a b ∧ IsMinOn H (Ioo a b) z := by
  obtain ⟨z,hz,hm⟩ := interval_exists_isMinOn hz₀ hH ha hb
  have hsc : StrictConvexOn ℝ (Ioo a b) H :=
    strictConvexOn_of_deriv2_pos (convex_Ioo a b) hH
      (by simpa [interior_Ioo] using hpos)
  exact ⟨z,⟨hz,hm⟩,fun y hy => hsc.eq_of_isMinOn hy.2 hm hy.1 hz⟩

theorem interval_min_stationary {a b z : ℝ} {H : ℝ → ℝ}
    (hz : z ∈ Ioo a b) (hm : IsMinOn H (Ioo a b) z) : deriv H z = 0 :=
  (hm.isLocalMin (isOpen_Ioo.mem_nhds hz)).deriv_eq_zero

end D5.S3.Analytic.ConvexBarrier
