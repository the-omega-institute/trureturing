import D5.S3.Geometry.Hyperideal.CFMPFrameMotion435Transient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace CFMPAffineDensityTransport435Transient

abbrev M := Matrix (Fin 3) (Fin 3) ℝ

theorem actual_absolute_det_derivative (B : ℝ → M) (D : M) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun s => B s i j) (D i j) t)
    (hB : (B t).det ≠ 0) :
    HasDerivAt (fun s => |(B s).det|)
      (|(B t).det| * ((B t)⁻¹ * D).trace) t := by
  have hb : HasDerivAt B D t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h i j
  have hd := CFMPFrameMotion435Transient.frame_absolute_det_derivative B D t hb hB
  rw [Matrix.trace_mul_comm D (B t)⁻¹] at hd
  exact hd


abbrev V := Fin 3 → ℝ

def affinePoint (o : ℝ → V) (B : ℝ → M) (t : ℝ) (u : V) : V :=
  o t + (B t).mulVec u

theorem actual_affine_velocity (o : ℝ → V) (B : ℝ → M)
    (o' u : V) (D : M) (t : ℝ)
    (ho : HasDerivAt o o' t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (D i j) t) :
    HasDerivAt (fun s => affinePoint o B s u) (o' + D.mulVec u) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have hm := (((hB i 0).mul_const (u 0)).add
    ((hB i 1).mul_const (u 1))).add ((hB i 2).mul_const (u 2))
  simpa -implicitDefEqProofs
    [affinePoint, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
     Pi.add_def, Pi.mul_def, Function.comp_def] using
    (hasDerivAt_pi.mp ho i).add hm

theorem joint_density_split (L : (ℝ × V) →L[ℝ] ℝ) (v : V) :
    L (1,v) = L (1,0) + L (0,v) := by
  have he : ((1 : ℝ),v) = (1,0) + (0,v) := by ext <;> simp
  rw [he, map_add]

theorem actual_weighted_density_derivative
    (o : ℝ → V) (B : ℝ → M) (ρ : ℝ → V → ℝ)
    (o' u : V) (D : M) (t : ℝ) (L : (ℝ × V) →L[ℝ] ℝ)
    (ho : HasDerivAt o o' t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (D i j) t)
    (hd : (B t).det ≠ 0)
    (hρ : HasFDerivAt (fun z : ℝ × V => ρ z.1 z.2) L
      (t,affinePoint o B t u)) :
    HasDerivAt (fun s => |(B s).det| * ρ s (affinePoint o B s u))
      (|(B t).det| *
        (((B t)⁻¹ * D).trace * ρ t (affinePoint o B t u) +
          L (1,0) + L (0,o' + D.mulVec u))) t := by
  have hp := (hasDerivAt_id t).prodMk
    (actual_affine_velocity o B o' u D t ho hB)
  have hr := hρ.comp_hasDerivAt t hp
  have hw := (actual_absolute_det_derivative B D t hB hd).mul hr
  simp only [Function.comp_def, id_eq, Pi.mul_def] at hw
  rw [joint_density_split L (o' + D.mulVec u)] at hw
  convert hw using 1 <;> ring


def basisVector (i : Fin 3) : V := Pi.single i 1

def coordinateDivergence (F : V → V) (u : V) : ℝ :=
  ∑ i : Fin 3, deriv (fun s : ℝ => F (u + s • basisVector i) i) 0

def referenceFlux (B D : M) (o v : V) (ρ : V → ℝ) (u : V) : V :=
  (|B.det| * ρ (o + B.mulVec u)) • (B⁻¹).mulVec (v + D.mulVec u)

theorem linear_covector_columns (L : V →L[ℝ] ℝ) (B : M) (q : V) :
    (∑ i : Fin 3, L (B.col i) * q i) = L (B.mulVec q) := by
  have he : B.mulVec q = q 0 • B.col 0 + q 1 • B.col 1 + q 2 • B.col 2 := by
    ext k
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.col_apply]
    ring
  rw [he]
  simp [Fin.sum_univ_three,map_add,map_smul,smul_eq_mul]
  ring

theorem fixed_matrix_curve (B : M) (u : V) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => B.mulVec (u + s • basisVector i)) (B.col i) 0 := by
  have hu : HasDerivAt (fun s : ℝ => u + s • basisVector i) (basisVector i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVector i)).const_add u
  have hb := B.mulVecLin.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  simpa -implicitDefEqProofs
    [basisVector, Matrix.mulVec_single_one, Function.comp_def] using hb

theorem affine_velocity_curve (C D : M) (v u : V) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => C.mulVec (v + D.mulVec (u + s • basisVector i)))
      ((C * D).col i) 0 := by
  have hv := (fixed_matrix_curve D u i).const_add v
  have hc := C.mulVecLin.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  have hc' : HasDerivAt
      (fun s : ℝ => C.mulVec (v + D.mulVec (u + s • basisVector i)))
      (C.mulVec (D.col i)) 0 := by
    simpa -implicitDefEqProofs [Function.comp_def] using hc
  have he : (C * D).col i = C.mulVec (D.col i) := by
    ext k
    simp [Matrix.mul_apply, Matrix.col_apply, Matrix.mulVec, dotProduct]
  rw [← he] at hc'
  exact hc'

theorem referenceFlux_coordinate_derivative (B D : M) (o v u : V)
    (ρ : V → ℝ) (L : V →L[ℝ] ℝ)
    (hρ : HasFDerivAt ρ L (o + B.mulVec u)) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => referenceFlux B D o v ρ (u + s • basisVector i) i)
      (|B.det| * (L (B.col i) * ((B⁻¹).mulVec (v + D.mulVec u)) i +
        ρ (o + B.mulVec u) * (B⁻¹ * D) i i)) 0 := by
  have hp := (fixed_matrix_curve B u i).const_add o
  have hρ0 : HasFDerivAt ρ L (o + B.mulVec (u+(0 : ℝ) • basisVector i)) := by
    simpa only [zero_smul,add_zero] using hρ
  have hr := hρ0.comp_hasDerivAt 0 hp
  have hq := hasDerivAt_pi.mp (affine_velocity_curve B⁻¹ D v u i) i
  have hf := (hr.const_mul |B.det|).mul hq
  convert hf using 1
  · funext s
    simp [referenceFlux,Pi.smul_apply,smul_eq_mul]
  · simp [Matrix.col_apply]
    ring

theorem referenceFlux_divergence (B D : M) (o v u : V)
    (ρ : V → ℝ) (L : V →L[ℝ] ℝ) (hB : B.det ≠ 0)
    (hρ : HasFDerivAt ρ L (o + B.mulVec u)) :
    coordinateDivergence (referenceFlux B D o v ρ) u =
      |B.det| * (ρ (o + B.mulVec u) * (B⁻¹ * D).trace + L (v + D.mulVec u)) := by
  unfold coordinateDivergence
  simp_rw [(referenceFlux_coordinate_derivative B D o v u ρ L hρ _).deriv]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    ← Finset.mul_sum,linear_covector_columns]
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),
    Matrix.one_mulVec]
  simp only [Matrix.trace,Matrix.diag_apply]
  ring

theorem actual_transport_with_time_density
    (o : ℝ → V) (B : ℝ → M) (ρ : ℝ → V → ℝ)
    (o' u : V) (D : M) (t : ℝ) (L : (ℝ × V) →L[ℝ] ℝ)
    (ho : HasDerivAt o o' t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (D i j) t)
    (hd : (B t).det ≠ 0)
    (hρ : HasFDerivAt (fun z : ℝ × V => ρ z.1 z.2) L
      (t,affinePoint o B t u)) :
    HasDerivAt (fun s => |(B s).det| * ρ s (affinePoint o B s u))
      (|(B t).det| * L (1,0) +
        coordinateDivergence (referenceFlux (B t) D (o t) o' (ρ t)) u) t := by
  let Ls : V →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inr ℝ ℝ V)
  have hs : HasFDerivAt (ρ t) Ls (affinePoint o B t u) := by
    have hi : HasFDerivAt (fun x : V => (t,x))
        (ContinuousLinearMap.inr ℝ ℝ V) (affinePoint o B t u) := by
      simpa using
        (((ContinuousLinearMap.inr ℝ ℝ V).hasFDerivAt
          (x := affinePoint o B t u)).const_add ((t : ℝ),(0 : V)))
    simpa [Ls,Function.comp_def] using hρ.comp (affinePoint o B t u) hi
  have hp := referenceFlux_divergence (B t) D (o t) o' u (ρ t) Ls hd hs
  rw [hp]
  convert actual_weighted_density_derivative o B ρ o' u D t L ho hB hd hρ using 1
  simp [Ls,affinePoint,ContinuousLinearMap.comp_apply]
  ring

end CFMPAffineDensityTransport435Transient
