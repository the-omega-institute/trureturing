/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSLocalObservationGraph
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSLocalObservationGraph
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Analytic]
   utility: none
   digest: An analytic observation is a graph in any invertible tangent projection. -/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! A chosen tangent projection gives common graph coordinates for comparison
of regular observation branches. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSLocalObservationGraph

open Set Filter Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An invertible derivative of the tangential component gives an analytic
graph through the observation point. -/
theorem exists_analytic_graph (T : E → E) (N : E → ℝ) (x : E)
    (hT : AnalyticAt ℝ T x) (hN : AnalyticAt ℝ N x) (L : E ≃L[ℝ] E)
    (hD : HasFDerivAt T (L : E →L[ℝ] E) x) :
    ∃ (e : OpenPartialHomeomorph E E) (U : Set E) (g : E → ℝ),
      (e : E → E) = T ∧ x ∈ e.source ∧ IsOpen U ∧ T x ∈ U ∧ U ⊆ e.target ∧
      AnalyticAt ℝ e.symm (T x) ∧ AnalyticOnNhd ℝ g U ∧
      ∀ y ∈ U, (T (e.symm y), N (e.symm y)) = (y, g y) := by
  have hD' := hT.hasStrictFDerivAt
  rw [hD.fderiv] at hD'
  let e := hD'.toOpenPartialHomeomorph T
  have he : (e : E → E) = T := rfl
  have hx : x ∈ e.source := hD'.mem_toOpenPartialHomeomorph_source
  have ht : T x ∈ e.target := hD'.image_mem_toOpenPartialHomeomorph_target
  have hi : AnalyticAt ℝ e.symm (T x) :=
    e.analyticAt_symm' hx (by rwa [he]) (i := L) (by rw [he, hD.fderiv])
  have hei : e.symm (T x) = x := e.left_inv hx
  have hg : AnalyticAt ℝ (N ∘ e.symm) (T x) :=
    hN.comp_of_eq hi hei
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp
    (hg.eventually_analyticAt.and (e.open_target.mem_nhds ht))
  refine ⟨e, U, N ∘ e.symm, he, hx, hUopen, hxU, fun y hy => (hU y hy).2, hi,
    fun y hy => (hU y hy).1, ?_⟩
  intro y hy
  exact Prod.ext (e.right_inv (hU y hy).2) rfl

/-- A correction of order `ε` in source coordinates changes an observation
with zero strict derivative by a term of smaller order. -/
theorem normal_change_littleO {N : E → ℝ} {x : E}
    (hN : HasStrictFDerivAt N (0 : E →L[ℝ] ℝ) x)
    {α : Type*} {l : Filter α} {a b : α → E} {ε : α → ℝ}
    (ha : Tendsto a l (𝓝 x)) (hb : Tendsto b l (𝓝 x))
    (hab : (fun t => a t - b t) =O[l] ε) :
    (fun t => N (a t) - N (b t)) =o[l] ε := by
  have hpair : Tendsto (fun t => (a t, b t)) l (𝓝 (x, x)) := ha.prodMk_nhds hb
  have h := (hN.isLittleO.comp_tendsto hpair)
  exact (by simpa only [Function.comp_def, zero_apply, sub_zero] using h :
    (fun t => N (a t) - N (b t)) =o[l] (fun t => a t - b t)).trans_isBigO hab

/-- If a source path solves the tangential equation to order three, the
normal graph and the source path have the same cubic expansion whenever
the normal differential vanishes. -/
theorem normal_graph_remainder {N : E → ℝ} {x : E} (e : OpenPartialHomeomorph E E)
    (hx : x ∈ e.source) (hi : AnalyticAt ℝ e.symm (e x))
    (hN : HasStrictFDerivAt N (0 : E →L[ℝ] ℝ) x)
    {α : Type*} {l : Filter α} {a y : α → E} {ε : α → ℝ}
    (ha : Tendsto a l (𝓝 x)) (hy : Tendsto y l (𝓝 (e x)))
    (h : (fun t => e (a t) - y t) =O[l] ε) :
    (fun t => N (e.symm (y t)) - N (a t)) =o[l] ε := by
  have hea : Tendsto (fun t => e (a t)) l (𝓝 (e x)) :=
    (e.continuousAt hx).tendsto.comp ha
  have hpair : Tendsto (fun t => (e (a t), y t)) l (𝓝 (e x, e x)) :=
    hea.prodMk_nhds hy
  have hs : ∀ᶠ t in l, a t ∈ e.source := ha (e.open_source.mem_nhds hx)
  have hr : (fun t => a t - e.symm (y t)) =O[l] ε :=
    ((hi.hasStrictFDerivAt.isBigO_sub.comp_tendsto hpair).trans h).congr'
      (hs.mono fun t ht => by simp only [Function.comp_apply, e.left_inv ht]) EventuallyEq.rfl
  have hb : Tendsto (fun t => e.symm (y t)) l (𝓝 x) := by
    rw [← e.left_inv hx]
    exact hi.continuousAt.tendsto.comp hy
  exact (normal_change_littleO hN ha hb hr).neg_left.congr_left fun t => neg_sub _ _

end D5.S3.Quantum.TensorNetworks.PeriodicMPSLocalObservationGraph
