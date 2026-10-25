import D5.S3.Geometry.Hyperideal.CFMPSimplexFullFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalReferenceFluxReadout435Transient
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Temporary exact coordinate transfer of the reference-simplex FTC formula. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators ContDiff
open CFMPFrameMotion435Transient
open CFMPSimplexDirection435Transient
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPOriginalReferenceFluxReadout435Transient

namespace CFMPReferenceSimplexDivergence435Transient

def simplex : Set (Fin 3 → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1}

def split3 : (Fin 3 → ℝ) ≃ᵐ (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

def pack3 (z : ℝ × (ℝ × ℝ)) : Fin 3 → ℝ := ![z.1,z.2.1,z.2.2]
def pack2 (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1,z.2]

theorem split3_preserving : MeasurePreserving split3 := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

theorem simplex_integral (g : (Fin 3 → ℝ) → ℝ) :
    (∫ u in simplex, g u) = ∫ z in tetrahedron 1, g (pack3 z) := by
  have heq : simplex = split3 ⁻¹' tetrahedron 1 := by
    ext u
    change ((∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1) ↔
      (0 ≤ u 0 ∧ 0 ≤ u 1 ∧ 0 ≤ u 2 ∧ u 0+u 1+u 2 ≤ 1)
    simp [Fin.forall_fin_succ,Fin.sum_univ_three,and_assoc]
  have hinv (u : Fin 3 → ℝ) : pack3 (split3 u) = u := by
    ext i
    fin_cases i <;> rfl
  have hp := (split3_preserving.restrict_preimage
    (tetrahedron_compact 1).measurableSet).integral_comp split3.measurableEmbedding
      (fun z => g (pack3 z))
  simpa only [← heq,hinv] using hp

theorem triangle_integral (g : (Fin 2 → ℝ) → ℝ) :
    (∫ q in parameterTriangle, g q) = ∫ z in triangle 1, g (pack2 z) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have heq : parameterTriangle = e ⁻¹' triangle 1 := by rfl
  have hinv (q : Fin 2 → ℝ) : pack2 (e q) = q := by
    ext i
    fin_cases i <;> rfl
  have hp := ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).restrict_preimage
    (triangle_compact 1).measurableSet).integral_comp e.measurableEmbedding
      (fun z => g (pack2 z))
  change (∫ q in e ⁻¹' triangle 1, g (pack2 (e q))) =
    ∫ z in triangle 1, g (pack2 z) at hp
  rw [← heq] at hp
  simpa only [hinv] using hp

theorem simplex_full_flux (F : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hF : ∀ u ∈ simplex, ContDiffAt ℝ 1 F u) :
    (∫ u in simplex, divergence F u) =
      ∫ q in parameterTriangle,
        (∑ i : Fin 3, F ![1-q 0-q 1,q 0,q 1] i) -
          (∑ i : Fin 3, F (referenceInternalFace i q) i) := by
  let P : Fin 3 → (ℝ × (ℝ × ℝ)) → ℝ := fun i z => F (pack3 z) i
  let D : Fin 3 → (ℝ × (ℝ × ℝ)) → ℝ :=
    fun i z => ((fderiv ℝ F (pack3 z)) (basis i)) i
  have hpack : Continuous pack3 := by unfold pack3; fun_prop
  have hmem (z : ℝ × (ℝ × ℝ)) (hz : z ∈ tetrahedron 1) : pack3 z ∈ simplex := by
    change (∀ i, 0 ≤ pack3 z i) ∧ (∑ i, pack3 z i) ≤ 1
    rcases hz with ⟨hx,hy,hz,hs⟩
    constructor
    · intro i
      fin_cases i
      · simpa [pack3] using hx
      · simpa [pack3] using hy
      · simpa [pack3] using hz
    · simpa [pack3,Fin.sum_univ_three] using hs
  have hP (i : Fin 3) : ContinuousOn (P i) (tetrahedron 1) := by
    intro z hz
    exact ((continuousAt_apply i _).comp
      ((hF _ (hmem z hz)).continuousAt.comp hpack.continuousAt)).continuousWithinAt
  have hD (i : Fin 3) : ContinuousOn (D i) (tetrahedron 1) := by
    intro z hz
    have h := ((hF _ (hmem z hz)).continuousAt_fderiv (by norm_num)).comp
      hpack.continuousAt
    exact ((continuousAt_apply i _).comp
      (h.clm_apply continuousAt_const)).continuousWithinAt
  have hd (u : Fin 3 → ℝ) (hu : u ∈ simplex) (i : Fin 3) :
      deriv (fun s : ℝ => F (u+s • basis i) i) 0 =
        ((fderiv ℝ F u) (basis i)) i := by
    have hline : HasDerivAt (fun s : ℝ => u+s • basis i) (basis i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basis i)).const_add u
    have hF0 : HasFDerivAt F (fderiv ℝ F u) (u+(0 : ℝ) • basis i) := by
      simpa only [zero_smul,add_zero] using (hF u hu).differentiableAt_one.hasFDerivAt
    have hh := hF0.comp_hasDerivAt 0 hline
    have hcoord : HasDerivAt (fun s : ℝ => F (u+s • basis i) i)
        (((fderiv ℝ F u) (basis i)) i) 0 := by
      simpa only [Function.comp_def] using hasDerivAt_pi.mp hh i
    exact hcoord.deriv
  have hslice (i : Fin 3) (c : ℝ → ℝ × (ℝ × ℝ)) (s : ℝ)
      (hm : c s ∈ tetrahedron 1)
      (hc : HasDerivAt (fun r => pack3 (c r)) (basis i) s) :
      HasDerivAt (fun r => P i (c r)) (D i (c s)) s := by
    have h := ((hF _ (hmem _ hm)).differentiableAt_one.hasFDerivAt).comp_hasDerivAt s hc
    exact hasDerivAt_pi.mp h i
  have hx : ∀ yz ∈ triangle 1, ∀ x ∈ Ioo (0 : ℝ) (1-yz.1-yz.2),
      HasDerivAt (fun r => P 0 (r,yz)) (D 0 (x,yz)) x := by
    intro yz hyz x hx
    apply hslice 0 (fun r => (r,yz)) x
    · exact ⟨hx.1.le,hyz.1,hyz.2.1,by linarith [hx.2]⟩
    · apply hasDerivAt_pi.mpr
      intro j
      fin_cases j
      · convert! (config := { preTransparency := .all, postTransparency := .all })
          (hasDerivAt_id x) using 1 <;> simp [pack3,basis]
      · simpa [pack3,basis] using (hasDerivAt_const x yz.1)
      · simpa [pack3,basis] using (hasDerivAt_const x yz.2)
  have hy : ∀ yz ∈ triangle 1, ∀ x ∈ Ioo (0 : ℝ) (1-yz.1-yz.2),
      HasDerivAt (fun r => P 1 (yz.1,(r,yz.2))) (D 1 (yz.1,(x,yz.2))) x := by
    intro yz hyz x hx
    apply hslice 1 (fun r => (yz.1,(r,yz.2))) x
    · exact ⟨hyz.1,hx.1.le,hyz.2.1,by linarith [hx.2]⟩
    · apply hasDerivAt_pi.mpr
      intro j
      fin_cases j
      · simpa [pack3,basis] using (hasDerivAt_const x yz.1)
      · convert! (config := { preTransparency := .all, postTransparency := .all })
          (hasDerivAt_id x) using 1 <;> simp [pack3,basis]
      · simpa [pack3,basis] using (hasDerivAt_const x yz.2)
  have hz : ∀ yz ∈ triangle 1, ∀ x ∈ Ioo (0 : ℝ) (1-yz.1-yz.2),
      HasDerivAt (fun r => P 2 (yz.1,(yz.2,r))) (D 2 (yz.1,(yz.2,x))) x := by
    intro yz hyz x hx
    apply hslice 2 (fun r => (yz.1,(yz.2,r))) x
    · exact ⟨hyz.1,hyz.2.1,hx.1.le,by linarith [hx.2]⟩
    · apply hasDerivAt_pi.mpr
      intro j
      fin_cases j
      · simpa [pack3,basis] using (hasDerivAt_const x yz.1)
      · simpa [pack3,basis] using (hasDerivAt_const x yz.2)
      · convert! (config := { preTransparency := .all, postTransparency := .all })
          (hasDerivAt_id x) using 1 <;> simp [pack3,basis]
  have hfull := tetrahedron_full_flux (1 : ℝ) (by norm_num)
    (P 0) (P 1) (P 2) (D 0) (D 1) (D 2)
    (hP 0) (hP 1) (hP 2) (hD 0) (hD 1) (hD 2) hx hy hz
  rw [simplex_integral,triangle_integral]
  calc
    _ = ∫ z in tetrahedron 1, D 0 z+D 1 z+D 2 z := by
      apply setIntegral_congr_fun (tetrahedron_compact 1).measurableSet
      intro z hz
      simp only [divergence,Fin.sum_univ_three]
      rw [hd _ (hmem z hz) 0,hd _ (hmem z hz) 1,hd _ (hmem z hz) 2]
    _ = _ := hfull.trans (by
      apply integral_congr_ae
      filter_upwards with z
      simp [P,pack3,pack2,referenceInternalFace,Fin.sum_univ_three]
      ring)

end CFMPReferenceSimplexDivergence435Transient
