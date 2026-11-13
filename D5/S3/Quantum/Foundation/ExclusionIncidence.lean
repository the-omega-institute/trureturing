/- GID: D5/S3/Quantum/Foundation/ExclusionIncidence
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionIncidence
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Topology.Sequences]
   utility: none
   digest: Compact original effects control limits of entire original exclusion fibers. -/

import D5.S3.Quantum.Foundation.ContinuousFrameSum
import Mathlib.Topology.Sequences

/-! The original-domain upper association needed by IX118.3. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.ExclusionIncidence

open Set Filter Topology
open CircuitBalancedConfirmation FacetZeroGluing ContinuousFrameSum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A pure limiting label retains every limit of actual mixed exclusion states.
The effect interval and base compactness are derived on the original normed space. -/
theorem exclusion_upper_limit {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {p : pure C u} {pn : ℕ → pure C u} {y : V} {yn : ℕ → V}
    (hp : Tendsto pn atTop (𝓝 p)) (hy : Tendsto yn atTop (𝓝 y))
    (hyn : ∀ n, yn n ∈ exclusion C u (pn n)) : y ∈ exclusion C u p := by
  let f (n : ℕ) : V →L[ℝ] ℝ := ((hyn n).2.choose).toContinuousLinearMap
  have hf (n : ℕ) : confirms C u (pn n) (f n).toLinearMap :=
    (hyn n).2.choose_spec.1
  have hz (n : ℕ) : f n (yn n) = 0 := (hyn n).2.choose_spec.2
  obtain ⟨e, he, φ, hφ, hfe⟩ :=
    (effects_compact hs hg).tendsto_subseq (fun n => (hf n).1)
  have hpp : Tendsto (fun n => (pn (φ n) : V)) atTop (𝓝 (p : V)) :=
    (continuous_subtype_val.tendsto p |>.comp hp).comp hφ.tendsto_atTop
  have hyy : Tendsto (fun n => yn (φ n)) atTop (𝓝 y) := hy.comp hφ.tendsto_atTop
  have hev : Continuous (fun t : (V →L[ℝ] ℝ) × V => t.1 t.2) := by fun_prop
  have hep : e p = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto (e, (p : V))).comp (hfe.prodMk_nhds hpp))
    have hconst : (fun n => f (φ n) (pn (φ n))) = fun _ : ℕ => (1 : ℝ) :=
      funext (fun n => (hf (φ n)).2)
    rw [hconst]
    exact tendsto_const_nhds
  have hey : e y = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto (e, y)).comp (hfe.prodMk_nhds hyy))
    have hconst : (fun n => f (φ n) (yn (φ n))) = fun _ : ℕ => (0 : ℝ) :=
      funext (fun n => hz (φ n))
    rw [hconst]
    exact tendsto_const_nhds
  exact ⟨(base_compact hc hs).isClosed.mem_of_tendsto hy
    (Eventually.of_forall fun n => (hyn n).1), e.toLinearMap, ⟨he, hep⟩, hey⟩

/-- Uniform upper approximation of each entire nearby exclusion fiber, in the
original norm. No ball, faithful-label or closed-pure-carrier hypothesis is used. -/
theorem exclusion_upper_eventually {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    {p : pure C u} {pn : ℕ → pure C u}
    (hp : Tendsto pn atTop (𝓝 p)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ y ∈ exclusion C u (pn n),
      ∃ z ∈ exclusion C u p, dist y z < ε := by
  classical
  by_contra h
  have hb : ∃ᶠ n in atTop, ∃ y ∈ exclusion C u (pn n),
      ∀ z ∈ exclusion C u p, ε ≤ dist y z := by
    simpa only [not_forall, not_exists, not_and, not_lt] using not_eventually.mp h
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hb
  choose y hy hfar using hbad
  obtain ⟨z, _, ψ, hψ, hyz⟩ :=
    (base_compact hc hs).tendsto_subseq (fun n => (hy n).1)
  have hz : z ∈ exclusion C u p := exclusion_upper_limit hc hs hg
    (hp.comp (hφ.comp hψ).tendsto_atTop) hyz (fun n => hy (ψ n))
  have hnear : ∀ᶠ n in atTop, dist (y (ψ n)) z < ε :=
    (Metric.tendsto_nhds.mp hyz) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (ψ n) z hz).not_gt hn

#print axioms exclusion_upper_limit
#print axioms exclusion_upper_eventually

end D5.S3.Quantum.Foundation.ExclusionIncidence
