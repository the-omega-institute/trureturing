import CFMPActualFlatGraph269Transient
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Topology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff NNReal

namespace CFMPConvexFlatPrimitive270Transient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded continuous covector, closed on one convex open side and zero on
the other closed convex side, has a C1 primitive across their interface.
The convex contact set, rather than a preassigned matching primitive, forces
the boundary values to differ by a single constant. -/
theorem exists_primitive_across_flat_side
    (s t U : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (ht : Convex ℝ t) (htc : IsClosed t)
    (hcontact : (closure s ∩ t).Nonempty)
    (hU : IsOpen U) (hcover : U ⊆ closure s ∪ t)
    (A : E → E →L[ℝ] ℝ) (dA : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ContinuousOn A (closure s ∪ t))
    (hder : ∀ x ∈ s, HasFDerivAt A (dA x) x)
    (hsym : ∀ x ∈ s, ∀ v w : E, dA x v w = dA x w v)
    (C : ℝ≥0) (hbound : ∀ x ∈ s, ‖A x‖₊ ≤ C)
    (hzero : ∀ x ∈ t, A x = 0) :
    ∃ F : E → ℝ,
      ContDiffOn ℝ 1 F U ∧
      (∀ x ∈ U, HasFDerivAt F (A x) x) ∧ Set.EqOn F 0 t := by
  classical
  obtain ⟨f, hf⟩ := hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun x hx => (hder x hx).hasFDerivWithinAt)
    (fun x hx v _ w _ => hsym x hx v w)
  have hfLip : LipschitzOnWith C f s :=
    hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le hf hbound
  obtain ⟨g, hgLip, hfg⟩ := hfLip.extend_real
  have hgder (x : E) (hx : x ∈ s) : HasFDerivAt g (A x) x := by
    apply ((hf x hx).hasFDerivAt (hso.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hso.mem_nhds hx] with y hy
    exact (hfg hy).symm
  have hgfder : Set.EqOn (fderiv ℝ g) A s := fun x hx => (hgder x hx).fderiv
  have hgclosure (x : E) (hx : x ∈ closure s) :
      HasFDerivWithinAt g (A x) (closure s) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hgder y hy).differentiableAt.differentiableWithinAt)
      hs hso (fun y _ => hgLip.continuous.continuousAt.continuousWithinAt)
    have hlim : Tendsto A (𝓝[s] x) (𝓝 (A x)) :=
      (hA x (Or.inl hx)).mono (fun y hy => Or.inl (subset_closure hy))
    exact (tendsto_congr' hgfder.eventuallyEq_nhdsWithin).2 hlim
  obtain ⟨z, hz⟩ := hcontact
  have hconst (x : E) (hx : x ∈ closure s ∩ t) : g x = g z := by
    have hder0 (y : E) (hy : y ∈ closure s ∩ t) :
        HasFDerivWithinAt g (0 : E →L[ℝ] ℝ) (closure s ∩ t) y := by
      have hd : HasFDerivWithinAt g (A y) (closure s ∩ t) y :=
        (hgclosure y hy.1).mono inter_subset_left
      simpa only [hzero y hy.2] using hd
    have hnorm : ‖g x - g z‖ ≤ 0 := by
      simpa only [norm_zero, zero_mul] using
        (hs.closure.inter ht).norm_image_sub_le_of_norm_hasFDerivWithin_le
          (C := (0 : ℝ)) hder0 (fun y _ => by simp) hz hx
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  let F : E → ℝ := (closure s).piecewise (fun x => g x - g z) 0
  have hFS : Set.EqOn F (fun x => g x - g z) (closure s) := by
    intro x hx
    simp only [F, Set.piecewise_eq_of_mem (closure s) (fun x => g x - g z) 0 hx]
  have hFT : Set.EqOn F 0 t := by
    intro x hx
    by_cases hxs : x ∈ closure s
    · simp only [hFS hxs, hconst x ⟨hxs,hx⟩, sub_self, Pi.zero_apply]
    · simp only [F, Set.piecewise_eq_of_notMem (closure s) (fun x => g x - g z) 0 hxs]
  have hfull (x : E) (hx : x ∈ U) : HasFDerivAt F (A x) x := by
    have hS : HasFDerivWithinAt F (A x) (closure s) x := by
      by_cases hxs : x ∈ closure s
      · exact ((hgclosure x hxs).sub_const (g z)).congr' hFS hxs
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [closure_closure] using hxs)
    have hT : HasFDerivWithinAt F (A x) t x := by
      by_cases hxt : x ∈ t
      · rw [hzero x hxt]
        exact (hasFDerivWithinAt_const (0 : ℝ) x t).congr' hFT hxt
      · exact HasFDerivWithinAt.of_notMem_closure (by simpa only [htc.closure_eq] using hxt)
    exact (hS.union hT).hasFDerivAt (mem_of_superset (hU.mem_nhds hx) hcover)
  refine ⟨F, ?_, hfull, hFT⟩
  have hc : ContDiffOn ℝ (0 + 1) F U :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n := 0) hU.uniqueDiffOn).2
      ⟨by simp, A, contDiffOn_zero.mpr (hA.mono hcover),
        fun x hx => (hfull x hx).hasFDerivWithinAt⟩
  simpa only [zero_add] using hc

end CFMPConvexFlatPrimitive270Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPConvexFlatPrimitive270Transient.exists_primitive_across_flat_side
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP270 constructed flat-interface primitive absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP270 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP270 CHECKED {name} axioms={axioms}"
