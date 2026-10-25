import D5.S3.Geometry.Hyperideal.CFMPAffineDensityTransport435Transient
import D5.S3.Geometry.Hyperideal.CFMPFrameContinuity435Transient
import D5.S3.Geometry.Hyperideal.CFMPStaticAffinePiola435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody (lorentz)

namespace CFMPFrameAffineTransport435Transient
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

theorem joint_density_differentiable
    (P : ℝ → M4) (D : M4) (t : ℝ) (x : V)
    (hP : HasDerivAt P D t) (hd : (P t).det ≠ 0) (hq : q (P t) x ≠ 0) :
    DifferentiableAt ℝ (fun z : ℝ × V => density (P z.1) z.2) (t,x) := by
  have ha := (frame_absolute_det_derivative P D t hP hd).differentiableAt
  have ha' : DifferentiableAt ℝ (fun z : ℝ × V => |(P z.1).det|) (t,x) :=
    by
      have hh := ha.comp (t,x)
        (differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : ℝ × V → ℝ) (t,x))
      simpa -implicitDefEqProofs only [Function.comp_def] using hh
  have hp (i j : Fin 4) :
      DifferentiableAt ℝ (fun z : ℝ × V => P z.1 i j) (t,x) := by
    have hh := (differentiableAt_pi.mp (differentiableAt_pi.mp hP.differentiableAt i) j).comp
      (t,x) (differentiableAt_fst : DifferentiableAt ℝ (Prod.fst : ℝ × V → ℝ) (t,x))
    simpa -implicitDefEqProofs only [Function.comp_def] using hh
  have hl (i : Fin 4) :
      DifferentiableAt ℝ (fun z : ℝ × V => lift z.2 i) (t,x) := by
    fin_cases i <;> simp [lift] <;> fun_prop
  have hu (j : Fin 4) :
      DifferentiableAt ℝ (fun z : ℝ × V => ambient (P z.1) z.2 j) (t,x) := by
    simpa -implicitDefEqProofs only
      [ambient,Matrix.vecMul,dotProduct,Fin.sum_univ_four,Pi.add_def,Pi.mul_def] using
      DifferentiableAt.sum (u := (Finset.univ : Finset (Fin 4)))
        (fun i _ => (hl i).mul (hp i j))
  have hq' : DifferentiableAt ℝ (fun z : ℝ × V => q (P z.1) z.2) (t,x) := by
    simp only [q,lorentz,Fin.sum_univ_four]
    fun_prop
  have hh := ha'.mul ((hq'.pow 2).inv (pow_ne_zero 2 hq))
  simpa -implicitDefEqProofs only
    [density,Pi.mul_def,Pi.inv_apply,Pi.pow_apply,div_eq_mul_inv] using hh

theorem field_differentiable (K : M4) (x : V) :
    DifferentiableAt ℝ (field K) x := by
  apply differentiableAt_pi.mpr
  intro i
  simp [field,alpha,lift,rowSum,Fin.sum_univ_four]
  fun_prop

theorem spatial_density_differentiable (P : ℝ → M4) (D : M4) (t : ℝ) (x : V)
    (hP : HasDerivAt P D t) (hd : (P t).det ≠ 0) (hq : q (P t) x ≠ 0) :
    DifferentiableAt ℝ (density (P t)) x := by
  have hi : DifferentiableAt ℝ (fun z : V => ((t : ℝ),z)) x := by fun_prop
  simpa [Function.comp_def] using
    (joint_density_differentiable P D t x hP hd hq).comp x hi

theorem divergence_add (F G : V → V) (x : V)
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun z => F z + G z) x = divergence F x + divergence G x := by
  unfold divergence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hl : DifferentiableAt ℝ (fun r : ℝ => x+r • basis i) 0 := by fun_prop
  have hf : DifferentiableAt ℝ (fun r : ℝ => F (x+r • basis i) i) 0 := by
    have hF0 : DifferentiableAt ℝ (fun z => F z i) (x+(0 : ℝ) • basis i) := by
      simpa only [zero_smul,add_zero] using differentiableAt_pi.mp hF i
    have hh := hF0.comp 0 hl
    simpa -implicitDefEqProofs only [Function.comp_def] using hh
  have hg : DifferentiableAt ℝ (fun r : ℝ => G (x+r • basis i) i) 0 := by
    have hG0 : DifferentiableAt ℝ (fun z => G z i) (x+(0 : ℝ) • basis i) := by
      simpa only [zero_smul,add_zero] using differentiableAt_pi.mp hG i
    have hh := hG0.comp 0 hl
    simpa -implicitDefEqProofs only [Function.comp_def] using hh
  exact deriv_add hf hg

def totalFlux (P : M4) (K : M4) (B E : M3) (o v : V) (u : V) : V :=
  (|B.det| * density P (o+B.mulVec u)) •
    B⁻¹.mulVec (v+E.mulVec u+field K (o+B.mulVec u))

theorem frame_affine_transport
    (P : ℝ → M4) (D : M4) (o : ℝ → V) (B : ℝ → M3)
    (v u : V) (E : M3) (t : ℝ)
    (hP : HasDerivAt P D t) (ho : HasDerivAt o v t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (E i j) t)
    (hdP : (P t).det ≠ 0) (hdB : (B t).det ≠ 0)
    (hq : q (P t) (o t+(B t).mulVec u) ≠ 0) :
    HasDerivAt
      (fun s => |(B s).det| * density (P s) (o s+(B s).mulVec u))
      (divergence (totalFlux (P t) (D*(P t)⁻¹) (B t) E (o t) v) u) t := by
  let x := o t+(B t).mulVec u
  let rho : ℝ → V → ℝ := fun s z => density (P s) z
  let L := fderiv ℝ (fun z : ℝ × V => rho z.1 z.2) (t,x)
  have hr : HasFDerivAt (fun z : ℝ × V => rho z.1 z.2) L (t,x) :=
    (joint_density_differentiable P D t x hP hdP hq).hasFDerivAt
  have hs := spatial_density_differentiable P D t x hP hdP hq
  let K := D*(P t)⁻¹
  let H : V → V := fun z => density (P t) z • field K z
  have hH : DifferentiableAt ℝ H x := hs.smul (field_differentiable K x)
  have ht : L (1,0) = divergence H x := by
    have hi : HasDerivAt (fun s : ℝ => (s,x)) (1,(0 : V)) t := by
      simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have htime : HasDerivAt (fun s => density (P s) x) (L (1,0)) t := by
      simpa [rho,Function.comp_def] using hr.comp_hasDerivAt t hi
    exact htime.unique (frame_density_continuity P D x t hP hdP hq)
  have ha := CFMPAffineDensityTransport435Transient.actual_transport_with_time_density
    o B rho v u E t L ho hB hdB hr
  have hp := CFMPStaticAffinePiola435Transient.static_affine_piola
    (B t) (o t) u H (fderiv ℝ H x) hdB hH.hasFDerivAt
  rw [ht] at ha
  -- The remaining assembly identifies the sum of the two reference fields.
  let F := CFMPAffineDensityTransport435Transient.referenceFlux (B t) E (o t) v (rho t)
  let G := CFMPStaticAffinePiola435Transient.pullFlux (B t) (o t) H
  have hG : DifferentiableAt ℝ G u :=
    (CFMPStaticAffinePiola435Transient.pullFlux_hasFDerivAt
      (B t) (o t) u H _ hH.hasFDerivAt).differentiableAt
  have hF : DifferentiableAt ℝ F u := by
    have hx : DifferentiableAt ℝ (fun z : V => o t+(B t).mulVec z) u := by
      exact ((B t).mulVecLin.toContinuousLinearMap.differentiableAt).const_add (o t)
    have hv : DifferentiableAt ℝ (fun z : V => (B t)⁻¹.mulVec (v+E.mulVec z)) u := by
      have he : DifferentiableAt ℝ (fun z : V => v+E.mulVec z) u :=
        E.mulVecLin.toContinuousLinearMap.differentiableAt.const_add v
      exact ((B t)⁻¹).mulVecLin.toContinuousLinearMap.differentiableAt.comp u he
    exact ((hs.comp u hx).const_mul |(B t).det|).smul hv
  have he : totalFlux (P t) K (B t) E (o t) v = fun z => F z+G z := by
    funext z
    simp [totalFlux,F,G,H,rho,CFMPAffineDensityTransport435Transient.referenceFlux,
      CFMPStaticAffinePiola435Transient.pullFlux,Matrix.mulVec_add,smul_add,
      Matrix.mulVec_smul,smul_smul] <;> module
  rw [he,divergence_add F G u hF hG,hp]
  simpa [CFMPAffineDensityTransport435Transient.coordinateDivergence,
    CFMPAffineDensityTransport435Transient.basisVector,divergence,basis,F,x,rho,
    CFMPAffineDensityTransport435Transient.affinePoint,add_comm] using ha

#print axioms frame_affine_transport
end CFMPFrameAffineTransport435Transient
