import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import OmegaBuild.Commands

/-! The exact pointwise resolvent remainder for the inner hot-region entropy.
The scalar logarithm representation is applied to the matrix cubic before
subtracting its degree-three part. The square-root normalization is expressed
by the exact inverse-congruence premise, so no commutation of the perturbation
with the reference is required. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerResolvent

open D5.S3.Quantum.Divergence.ResolventFunctionalRigidity (cfc_shift_inverse)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The integrand of the spectral logarithm formula for `Y^3 log Y`.
It is well defined even when `Y` has zero eigenvalues, for positive `l`. -/
def cubicLogIntegrand (l : ℝ) (Y : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => x^3 * ((1+l)⁻¹ - (x+l)⁻¹)) Y

/-- Polynomial division of the shifted cubic, using the actual matrix resolvent. -/
theorem cubicLogIntegrand_eq (Y : Matrix n n ℂ) (hY : Y.PosSemidef)
    (l : ℝ) (hl : 0 < l) :
    cubicLogIntegrand l Y = (1+l)⁻¹ • Y^3 - Y^2 + l • Y - l^2 • 1 +
      l^3 • (Y + l • (1 : Matrix n n ℂ))⁻¹ := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Y) :=
    Y.finite_real_spectrum.continuousOn f
  have hh := hY.isHermitian.isSelfAdjoint
  have he : cubicLogIntegrand l Y = cfc (fun x : ℝ =>
      (1+l)⁻¹ * x^3 - x^2 + l*x - l^2 + l^3*(x+l)⁻¹) Y := by
    unfold cubicLogIntegrand
    apply cfc_congr
    intro x hx
    rw [hY.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have hn := hY.eigenvalues_nonneg i
    have h1 : 1+l ≠ 0 := by positivity
    have h2 : hY.isHermitian.eigenvalues i + l ≠ 0 := by positivity
    field_simp [h1, h2] <;> ring
  rw [he, cfc_add Y _ _ (hc _) (hc _), cfc_sub _ _ Y (hc _) (hc _),
    cfc_add Y _ _ (hc _) (hc _), cfc_sub _ _ Y (hc _) (hc _),
    cfc_const_mul _ _ _ (hc _), cfc_pow_id (R := ℝ) Y 3 hh,
    cfc_pow_id (R := ℝ) Y 2 hh, cfc_const_mul_id _ Y hh,
    cfc_const _ Y hh, Algebra.algebraMap_eq_smul_one,
    cfc_const_mul _ _ _ (hc _), cfc_shift_inverse Y hY l hl]

/-- The shifted inverse after subtracting its noncommuting degree-three
expansion. `W` is the inverse square root of the unperturbed shifted matrix
in the application, and `Z = W*U*W`. The premise explicitly identifies
its inverse congruence; `B` and `U` need not commute. -/
theorem shifted_inverse_fourth (B U W : Matrix n n ℂ) (l : ℝ)
    (hl : 0 < l) (hY : (B+U).PosSemidef)
    (hW : W * (B + l • 1) * W = 1) :
    let Z := W * U * W
    (B+U + l • 1)⁻¹ =
      W * (1-Z+Z^2-Z^3) * W + W * (Z^4 * (1+Z)⁻¹) * W := by
  let T : Matrix n n ℂ := B + l • 1
  let Y : Matrix n n ℂ := B+U + l • 1
  let Z := W * U * W
  change W*T*W = 1 at hW
  change Y⁻¹ = W*(1-Z+Z^2-Z^3)*W + W*(Z^4*(1+Z)⁻¹)*W
  have hYeq : Y = T+U := by dsimp [Y,T]; abel
  have hWright : T*W*W = 1 := by
    have h : W*(T*W) = 1 := by simpa only [mul_assoc] using hW
    simpa only [mul_assoc] using (mul_eq_one_comm.mp h : (T*W)*W = 1)
  have hWunit : IsUnit W := (Matrix.isUnit_iff_isUnit_det W).mpr
    (Matrix.isUnit_det_of_left_inverse hW)
  have hYpos : Y.PosDef := Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hl)
  have hcong : W*Y*W = 1+Z := by
    rw [hYeq, mul_add, add_mul, hW]
  have hJunit : IsUnit (1+Z) := by
    rw [← hcong]
    exact (hWunit.mul hYpos.isUnit).mul hWunit
  have hJ : (1+Z)*(1+Z)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv (1+Z) ((Matrix.isUnit_iff_isUnit_det (1+Z)).mp hJunit)
  have hres : Y⁻¹ = W*(1+Z)⁻¹*W := by
    apply Matrix.inv_eq_right_inv
    calc
      Y*(W*(1+Z)⁻¹*W) = (T*W*W)*Y*W*(1+Z)⁻¹*W := by rw [hWright, one_mul] <;> noncomm_ring
      _ = T*W*(W*Y*W)*(1+Z)⁻¹*W := by noncomm_ring
      _ = T*W*(1+Z)*(1+Z)⁻¹*W := by rw [hcong]
      _ = T*W*((1+Z)*(1+Z)⁻¹)*W := by noncomm_ring
      _ = 1 := by rw [hJ, mul_one, hWright]
  have hp : (1-Z+Z^2-Z^3)*(1+Z)+Z^4 = 1 := by noncomm_ring
  have hgeo : (1+Z)⁻¹ = 1-Z+Z^2-Z^3 + Z^4*(1+Z)⁻¹ := by
    calc
      _ = ((1-Z+Z^2-Z^3)*(1+Z)+Z^4)*(1+Z)⁻¹ := by rw [hp, one_mul]
      _ = _ := by rw [add_mul, mul_assoc (1-Z+Z^2-Z^3), hJ, mul_one]
  calc
    Y⁻¹ = W*(1+Z)⁻¹*W := hres
    _ = W*((1-Z+Z^2-Z^3)+Z^4*(1+Z)⁻¹)*W :=
      congrArg (fun J : Matrix n n ℂ => W*J*W) hgeo
    _ = _ := by rw [mul_add, add_mul]

/-- The exact integrand remainder after degree three in the displacement `U`.
The trace is ordinary complex trace. A normalized trace is obtained by division
by the dimension. Substituting `U=S*A*S` and `W=(B+lI)^(-1/2)` gives
`Z=Q_l^(1/2)*A*Q_l^(1/2)` from the inner-region proof. -/
theorem cubic_log_integrand_trace_fourth (B U W : Matrix n n ℂ) (l : ℝ)
    (hl : 0 < l) (hY : (B+U).PosSemidef)
    (hW : W * (B + l • 1) * W = 1) :
    let Y := B+U
    let Z := W*U*W
    let polynomial := (1+l)⁻¹ • Y^3 - Y^2 + l • Y - l^2 • 1 +
      l^3 • (W*(1-Z+Z^2-Z^3)*W)
    (cubicLogIntegrand l Y).trace - polynomial.trace =
      l^3 • ((B + l • 1)⁻¹ * (Z^4*(1+Z)⁻¹)).trace := by
  have hP : (B + l • (1 : Matrix n n ℂ))⁻¹ = W^2 := by
    apply Matrix.inv_eq_right_inv
    have h : W*((B + l • (1 : Matrix n n ℂ))*W) = 1 := by
      simpa only [mul_assoc] using hW
    simpa only [pow_two, mul_assoc] using (mul_eq_one_comm.mp h)
  dsimp only
  rw [hP]
  rw [cubicLogIntegrand_eq _ hY _ hl, shifted_inverse_fourth B U W l hl hY hW]
  simp only [smul_add, Matrix.trace_add, Matrix.trace_smul, add_assoc]
  have ht (A : Matrix n n ℂ) : (W*A*W).trace = (W^2*A).trace := by
    rw [Matrix.trace_mul_cycle, pow_two]
  simp only [ht]
  abel

/-- The inverse-congruence premise is always realized by the spectral
inverse square root of a PSD reference at a positive shift. -/
theorem shift_inverse_sqrt_congruence (B : Matrix n n ℂ) (hB : B.PosSemidef)
    (l : ℝ) (hl : 0 < l) :
    let W := cfc (fun x : ℝ => Real.sqrt ((x+l)⁻¹)) B
    W*(B+l • 1)*W = 1 := by
  let f : ℝ → ℝ := fun x => Real.sqrt ((x+l)⁻¹)
  let g : ℝ → ℝ := fun x => x+l
  have hc (h : ℝ → ℝ) : ContinuousOn h (spectrum ℝ B) :=
    B.finite_real_spectrum.continuousOn h
  have hh := hB.isHermitian.isSelfAdjoint
  have hg : cfc g B = B + l • (1 : Matrix n n ℂ) := by
    dsimp only [g]
    rw [cfc_add_const l (fun x : ℝ => x) B (hc _) hh,
      cfc_id' ℝ B hh, Algebra.algebraMap_eq_smul_one]
  change cfc f B * (B+l • 1) * cfc f B = 1
  rw [← hg, ← cfc_mul f g B (hc _) (hc _),
    ← cfc_mul (fun x => f x*g x) f B (hc _) (hc _), ← cfc_const_one ℝ B hh]
  apply cfc_congr
  intro x hx
  rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have hp : 0 < hB.isHermitian.eigenvalues i + l :=
    add_pos_of_nonneg_of_pos (hB.eigenvalues_nonneg i) hl
  change Real.sqrt ((hB.isHermitian.eigenvalues i+l)⁻¹) *
    (hB.isHermitian.eigenvalues i+l) *
    Real.sqrt ((hB.isHermitian.eigenvalues i+l)⁻¹) = 1
  rw [mul_right_comm, Real.mul_self_sqrt (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']

#print axioms cubic_log_integrand_trace_fourth
#print axioms shift_inverse_sqrt_congruence

end D5.S3.Quantum.Semigroups.WuCubicHotInnerResolvent
