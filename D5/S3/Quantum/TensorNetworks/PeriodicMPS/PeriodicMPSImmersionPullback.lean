/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSImmersionPullback
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSImmersionPullback
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph]
   utility: none
   digest: Pullback through an immersion preserves countable differentiable covers. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Bases

/-! A linear left inverse of the differential gives a locally invertible
projection, so the inverse image can be covered using differentiable maps
with the same domains as those covering the original set. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSImmersionPullback

open Set Filter Function
open scoped Topology

universe u

variable {E : Type u} {Y H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [SecondCountableTopology E]

private theorem inverse_neighborhood {f : E → Y} {x : E} (ha : AnalyticAt ℝ f x)
    (hinj : Injective (fderiv ℝ f x)) :
    ∃ (g : Y → E) (U : Set E) (V : Set Y), U ∈ 𝓝 x ∧
      DifferentiableOn ℝ g V ∧ MapsTo f U V ∧ ∀ y ∈ U, g (f y) = y := by
  let D := fderiv ℝ f x
  let P : Y →L[ℝ] E := D.toLinearMap.leftInverse.toContinuousLinearMap
  have he : P.comp D = ContinuousLinearMap.id ℝ E := by
    ext z
    exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hinj) z
  let T := P ∘ f
  have hT : AnalyticAt ℝ T x := (P.analyticAt (f x)).comp ha
  have hD : HasFDerivAt T ((ContinuousLinearEquiv.refl ℝ E) : E →L[ℝ] E) x := by
    apply (P.hasFDerivAt.comp x ha.hasStrictFDerivAt.hasFDerivAt).congr_fderiv
    exact he
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨e, W, _, hTe, hx, hW, hTx, hsub, hi, _, _⟩ :=
    PeriodicMPSLocalObservationGraph.exists_analytic_graph T (fun _ => 0) x hT
      analyticAt_const (ContinuousLinearEquiv.refl ℝ E) hD
  let Z : Set E := W ∩ {y | AnalyticAt ℝ e.symm y}
  have hZ : Z ∈ 𝓝 (T x) := inter_mem (hW.mem_nhds hTx) hi.eventually_analyticAt
  let U := e.source ∩ T ⁻¹' Z
  let V := P ⁻¹' Z
  refine ⟨e.symm ∘ P, U, V,
    inter_mem (e.open_source.mem_nhds hx) (hT.continuousAt hZ), ?_,
    fun y hy => hy.2, ?_⟩
  · intro y hy
    exact ((hy.2 : AnalyticAt ℝ e.symm (P y)).differentiableAt.comp y
      P.differentiableAt).differentiableWithinAt
  · intro y hy
    change e.symm (T y) = y
    rw [← hTe]
    exact e.left_inv hy.1

/-- Locally immersive points mapping into a countable differentiable cover
are contained in a cover with the same parameter space. -/
theorem cover_regular_preimage {f : E → Y} (A : Set E)
    (hA : ∀ x ∈ A, AnalyticAt ℝ f x ∧ Injective (fderiv ℝ f x))
    {ι : Type u} [Countable ι] (D : ι → Set H) (g : ι → H → Y)
    (hg : ∀ i, DifferentiableOn ℝ (g i) (D i)) (hc : f '' A ⊆ ⋃ i, g i '' D i) :
    ∃ (κ : Type u) (_ : Countable κ) (W : κ → Set H) (q : κ → H → E),
      (∀ i, DifferentiableOn ℝ (q i) (W i)) ∧ A ⊆ ⋃ i, q i '' W i := by
  classical
  have hlocal (x : E) (hx : x ∈ A) := inverse_neighborhood (hA x hx).1 (hA x hx).2
  choose inv U V hU hI hmaps he using hlocal
  let chosen (x : E) : Set E := if hx : x ∈ A then U x hx else ∅
  have hchosen (x : E) (hx : x ∈ A) : chosen x ∈ 𝓝[A] x :=
    nhdsWithin_le_nhds (by simpa [chosen, hx] using hU x hx)
  obtain ⟨C, hC, hh, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hchosen
  haveI : Countable C := hh.to_subtype
  let W (j : C × ι) := D j.2 ∩ g j.2 ⁻¹' V j.1 (hC j.1.property)
  let q (j : C × ι) := inv j.1 (hC j.1.property) ∘ g j.2
  refine ⟨C × ι, inferInstance, W, q, ?_, ?_⟩
  · intro j
    exact (hI j.1 (hC j.1.property)).comp ((hg j.2).mono inter_subset_left) inter_subset_right
  · intro x hx
    obtain ⟨c, hcC, hxc⟩ := mem_iUnion₂.mp (hcov hx)
    have hsv : x ∈ U c (hC hcC) := by simpa [chosen, hC hcC] using hxc
    obtain ⟨i, w, hw, hwx⟩ := mem_iUnion.mp (hc ⟨x, hx, rfl⟩)
    refine mem_iUnion.mpr ⟨(⟨c, hcC⟩, i), w, ⟨hw, ?_⟩, ?_⟩
    · change g i w ∈ V c (hC hcC)
      rw [hwx]
      exact hmaps c (hC hcC) hsv
    · change inv c (hC hcC) (g i w) = x
      rw [hwx]
      exact he c (hC hcC) x hsv

end D5.S3.Quantum.TensorNetworks.PeriodicMPSImmersionPullback
