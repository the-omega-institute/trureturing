import D5.S3.Geometry.Hyperideal.CFMPFrameMotion435Transient

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open CFMPFrameMotion435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody (lorentz)

namespace CFMPFrameContinuity435Transient

def tangent (v : V) : W := ![v 0,v 1,v 2,-v 0-v 1-v 2]
def ambient (M : M4) (x : V) : W := Matrix.vecMul (lift x) M
def q (M : M4) (x : V) : ℝ := -lorentz (ambient M x) (ambient M x)
def qDirection (M : M4) (x v : V) : ℝ :=
  -2 * lorentz (ambient M x) (Matrix.vecMul (tangent v) M)
def qTime (M D : M4) (x : V) : ℝ :=
  -2 * lorentz (ambient M x) (Matrix.vecMul (lift x) D)
def density (M : M4) (x : V) : ℝ := |M.det| / (q M x)^2

theorem lorentz_right_linear (u v w : W) (a b : ℝ) :
    lorentz u (a • v + b • w) = a * lorentz u v + b * lorentz u w := by
  simp [lorentz, Fin.sum_univ_four]
  ring

theorem lorentz_curve (f : ℝ → W) (v : W) (t : ℝ)
    (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => -lorentz (f s) (f s)) (-2 * lorentz (f t) v) t := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
    (fun i _ => ((hasDerivAt_pi.mp hf i).const_mul
      (![(1 : ℝ),1,1,-1] i)).mul (hasDerivAt_pi.mp hf i))
  convert h.neg using 1
  · rfl
  · simp [lorentz, Fin.sum_univ_four]
    ring

theorem ambient_time (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) :
    HasDerivAt (fun s => ambient (M s) x) (Matrix.vecMul (lift x) D) t := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa [ambient, Matrix.vecMul, dotProduct] using
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
      (fun i _ => (hasDerivAt_pi.mp (hasDerivAt_pi.mp hM i) j).const_mul (lift x i))

theorem quadratic_time (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) :
    HasDerivAt (fun s => q (M s) x) (qTime (M t) D x) t :=
  lorentz_curve _ _ _ (ambient_time M D x t hM)

theorem lift_line (x v : V) (s : ℝ) :
    lift (x + s • v) = lift x + s • tangent v := by
  ext i
  fin_cases i <;> simp [lift, tangent] <;> ring

theorem ambient_line (M : M4) (x v : V) :
    HasDerivAt (fun s : ℝ => ambient M (x + s • v))
      (Matrix.vecMul (tangent v) M) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const
    (Matrix.vecMul (tangent v) M)).const_add (ambient M x)
  simp only [one_smul] at h
  convert h using 1
  funext s
  simp [ambient, lift_line, Matrix.add_vecMul, Matrix.smul_vecMul]

theorem quadratic_line (M : M4) (x v : V) :
    HasDerivAt (fun s : ℝ => q M (x + s • v)) (qDirection M x v) 0 := by
  have h := lorentz_curve _ _ _ (ambient_line M x v)
  simpa [q, qDirection] using h

theorem field_tangent (K : M4) (x : V) :
    tangent (field K x) = Matrix.vecMul (lift x) K - alpha K x • lift x := by
  ext i
  fin_cases i <;>
    simp [tangent, field, Matrix.vecMul, dotProduct, alpha, rowSum, lift,
      Fin.sum_univ_four] <;> ring

theorem quadratic_frame_balance (M D K : M4) (x : V) (hK : K * M = D) :
    qDirection M x (field K x) = qTime M D x - 2 * alpha K x * q M x := by
  have hvec : Matrix.vecMul (tangent (field K x)) M =
      Matrix.vecMul (lift x) D - alpha K x • ambient M x := by
    rw [field_tangent, Matrix.sub_vecMul, Matrix.smul_vecMul,
      Matrix.vecMul_vecMul, hK]
    rfl
  rw [qDirection, hvec]
  have hh : lorentz (ambient M x)
      (Matrix.vecMul (lift x) D - alpha K x • ambient M x) =
      lorentz (ambient M x) (Matrix.vecMul (lift x) D) -
        alpha K x * lorentz (ambient M x) (ambient M x) := by
    simpa [sub_eq_add_neg] using
      lorentz_right_linear (ambient M x) (Matrix.vecMul (lift x) D)
        (ambient M x) 1 (-alpha K x)
  rw [hh]
  simp only [qTime, q]
  ring

theorem quadratic_direction_components (M : M4) (x v : V) :
    qDirection M x v = ∑ i, v i * qDirection M x (basis i) := by
  have ht : tangent v =
      v 0 • tangent (basis 0) + v 1 • tangent (basis 1) + v 2 • tangent (basis 2) := by
    ext i
    fin_cases i <;> simp [tangent, basis, Pi.single_apply] <;> ring
  rw [qDirection, ht]
  simp only [Matrix.add_vecMul, Matrix.smul_vecMul]
  have h1 := lorentz_right_linear (ambient M x)
    (Matrix.vecMul (tangent (basis 0)) M) (Matrix.vecMul (tangent (basis 1)) M)
    (v 0) (v 1)
  have h2 := lorentz_right_linear (ambient M x)
    (v 0 • Matrix.vecMul (tangent (basis 0)) M +
      v 1 • Matrix.vecMul (tangent (basis 1)) M)
    (Matrix.vecMul (tangent (basis 2)) M) 1 (v 2)
  simp only [one_smul, one_mul] at h2
  rw [h2, h1]
  simp [Fin.sum_univ_three, qDirection]
  ring

theorem density_line (M : M4) (x v : V) (hq : q M x ≠ 0) :
    HasDerivAt (fun s : ℝ => density M (x + s • v))
      (-2 * |M.det| / (q M x)^3 * qDirection M x v) 0 := by
  have h := (hasDerivAt_const (0 : ℝ) |M.det|).div
    ((quadratic_line M x v).pow 2) (pow_ne_zero 2 (by simpa using hq))
  convert h using 1
  · rfl
  · simp
    field_simp [hq] <;> ring

theorem density_field_divergence (M K : M4) (x : V) (hq : q M x ≠ 0) :
    divergence (fun z => density M z • field K z) x =
      density M x * (K.trace - 4 * alpha K x) -
        2 * |M.det| / (q M x)^3 * qDirection M x (field K x) := by
  have hi (i : Fin 3) :
      deriv (fun s : ℝ => density M (x + s • basis i) *
        field K (x + s • basis i) i) 0 =
      (-2 * |M.det| / (q M x)^3 * qDirection M x (basis i)) * field K x i +
        density M x * (K i.castSucc i.castSucc - K 3 i.castSucc -
          (rowSum K i.castSucc - rowSum K 3) * x i - alpha K x) := by
    simpa -implicitDefEqProofs only [Pi.mul_def, zero_smul, add_zero] using
      ((density_line M x (basis i) hq).mul (field_coordinate_derivative K x i)).deriv
  unfold divergence
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  have hs := projective_divergence K x
  unfold divergence at hs
  simp_rw [(field_coordinate_derivative K x _).deriv] at hs
  rw [← Finset.mul_sum, hs]
  rw [quadratic_direction_components M x (field K x)]
  simp only [Fin.sum_univ_three]
  ring

theorem frame_density_continuity (M : ℝ → M4) (D : M4) (x : V) (t : ℝ)
    (hM : HasDerivAt M D t) (hd : (M t).det ≠ 0) (hq : q (M t) x ≠ 0) :
    HasDerivAt (fun s => density (M s) x)
      (divergence (fun z => density (M t) z • field (D * (M t)⁻¹) z) x) t := by
  let K := D * (M t)⁻¹
  have hK : K * M t = D := by
    dsimp [K]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.mul_one]
  have h := (frame_absolute_det_derivative M D t hM hd).div
    ((quadratic_time M D x t hM).pow 2) (pow_ne_zero 2 hq)
  convert h using 1
  · rfl
  · rw [density_field_divergence _ _ _ hq,
      quadratic_frame_balance (M t) D K x hK]
    simp only [density, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    dsimp only [K]
    field_simp [hq]
    ring

#print axioms frame_density_continuity
end CFMPFrameContinuity435Transient
