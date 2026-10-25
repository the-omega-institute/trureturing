import CFMPLocalExactRectangle277Transient
import Mathlib.Analysis.Calculus.Deriv.AffineMap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open CFMPLocalExactRectangle277Transient (Plane square rectangle_integral_eq)

namespace CFMPLocalExactConvex278Transient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local exactness of a continuous covector gives the triangle identity on
a convex set, by pulling back to a finitely subdivided parameter square. -/
theorem triangle_integral_of_local_exactness
    (s : Set E) (hs : Convex ℝ s) (A : E → E →L[ℝ] ℝ)
    (hA : ContinuousOn A s)
    (hlocal : ∀ z ∈ s, ∃ V : Set E,
      z ∈ V ∧ IsOpen V ∧ ∃ G : E → ℝ,
        ∀ w ∈ V, HasFDerivAt G (A w) w)
    (a b c : E) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (∫ᶜ x in Path.segment a b, A x) + (∫ᶜ x in Path.segment b c, A x) =
      ∫ᶜ x in Path.segment a c, A x := by
  let ψ : Plane → E := fun z => AffineMap.lineMap a (AffineMap.lineMap b c z.1) z.2
  have hψ : ContDiff ℝ ∞ ψ := by
    dsimp only [ψ,AffineMap.lineMap_apply]
    simp only [vadd_eq_add, vsub_eq_sub]
    fun_prop
  have hdψ (z : Plane) : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
    (hψ.differentiable (by simp) z).hasFDerivAt
  have hψs : MapsTo ψ square s := by
    intro z hz
    exact hs.lineMap_mem ha (hs.lineMap_mem hb hc hz.1) hz.2
  let B : Plane → Plane →L[ℝ] ℝ := fun z =>
    (A (ψ z)).comp (fderiv ℝ ψ z)
  have hB : ContinuousOn B square := by
    have hder : Continuous (fun z => fderiv ℝ ψ z) :=
      continuous_iff_continuousAt.mpr (fun z =>
        (hψ.contDiffAt (x := z)).continuousAt_fderiv (by simp))
    exact (hA.comp hψ.continuous.continuousOn hψs).clm_comp hder.continuousOn
  have hBlocal : ∀ z ∈ square, ∃ V : Set Plane,
      z ∈ V ∧ IsOpen V ∧ ∃ G : Plane → ℝ,
        ∀ w ∈ V, HasFDerivAt G (B w) w := by
    intro z hz
    obtain ⟨V,h0,hV,G,hG⟩ := hlocal (ψ z) (hψs hz)
    exact ⟨ψ ⁻¹' V,h0,hV.preimage hψ.continuous,G ∘ ψ,
      fun w hw => (hG (ψ w) hw).comp w (hdψ w)⟩
  have hbottom (x : ℝ) : fderiv ℝ ψ (x,0) (1,0) = 0 := by
    have hd := (hdψ (x,0)).comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x (0 : ℝ)))
    simp only [Function.comp_def,ψ,AffineMap.lineMap_apply_zero] at hd
    exact hd.unique (hasDerivAt_const x a)
  have htop (x : ℝ) : fderiv ℝ ψ (x,1) (1,0) = c - b := by
    have hd := (hdψ (x,1)).comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x (1 : ℝ)))
    simp only [Function.comp_def,ψ,AffineMap.lineMap_apply_one] at hd
    exact hd.unique AffineMap.hasDerivAt_lineMap
  have hleft (y : ℝ) : fderiv ℝ ψ (0,y) (0,1) = b - a := by
    have hd := (hdψ (0,y)).comp_hasDerivAt y
      ((hasDerivAt_const y (0 : ℝ)).prodMk (hasDerivAt_id y))
    simp only [Function.comp_def,ψ,AffineMap.lineMap_apply_zero] at hd
    exact hd.unique AffineMap.hasDerivAt_lineMap
  have hright (y : ℝ) : fderiv ℝ ψ (1,y) (0,1) = c - a := by
    have hd := (hdψ (1,y)).comp_hasDerivAt y
      ((hasDerivAt_const y (1 : ℝ)).prodMk (hasDerivAt_id y))
    simp only [Function.comp_def,ψ,AffineMap.lineMap_apply_one] at hd
    exact hd.unique AffineMap.hasDerivAt_lineMap
  have hrect := rectangle_integral_eq B hB hBlocal
  simp only [B,ContinuousLinearMap.comp_apply,hbottom,htop,hleft,hright,
    map_zero,ψ,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,
    intervalIntegral.integral_zero,zero_add] at hrect
  rw [curveIntegral_segment,curveIntegral_segment,curveIntegral_segment]
  linarith

/-- On an open convex domain, the actual segment-integral primitive is C1
whenever the continuous covector is locally exact. The derivative need not
exist for the covector itself at any interface. -/
theorem segment_primitive_C1_of_local_exactness
    (s : Set E) (hs : Convex ℝ s) (hso : IsOpen s)
    (A : E → E →L[ℝ] ℝ) (hA : ContinuousOn A s)
    (hlocal : ∀ z ∈ s, ∃ V : Set E,
      z ∈ V ∧ IsOpen V ∧ ∃ G : E → ℝ,
        ∀ w ∈ V, HasFDerivAt G (A w) w)
    (a : E) (ha : a ∈ s) :
    ContDiffOn ℝ 1 (fun b => ∫ᶜ x in Path.segment a b, A x) s ∧
      ∀ b ∈ s, HasFDerivAt (fun c => ∫ᶜ x in Path.segment a c, A x) (A b) b := by
  have hD (b : E) (hb : b ∈ s) :
      HasFDerivAt (fun c => ∫ᶜ x in Path.segment a c, A x) (A b) b := by
    have hd := (HasFDerivWithinAt.curveIntegral_segment_source hs hA hb).const_add
      (∫ᶜ x in Path.segment a b, A x)
    have hwithin : HasFDerivWithinAt
        (fun c => ∫ᶜ x in Path.segment a c, A x) (A b) s b :=
      hd.congr' (fun c hc =>
        (triangle_integral_of_local_exactness s hs A hA hlocal a b c ha hb hc).symm) hb
    exact hwithin.hasFDerivAt (hso.mem_nhds hb)
  refine ⟨?_,hD⟩
  have hC1 : ContDiffOn ℝ (0 + 1) (fun b => ∫ᶜ x in Path.segment a b, A x) s :=
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hso.uniqueDiffOn).2
      ⟨by simp,A,contDiffOn_zero.mpr hA,
        fun b hb => (hD b hb).hasFDerivWithinAt⟩
  simpa only [zero_add] using hC1

end CFMPLocalExactConvex278Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPLocalExactConvex278Transient.triangle_integral_of_local_exactness,
      ``CFMPLocalExactConvex278Transient.segment_primitive_C1_of_local_exactness] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP278 continuous locally exact convex primitive absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP278 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP278 CHECKED {name} axioms={axioms}"
