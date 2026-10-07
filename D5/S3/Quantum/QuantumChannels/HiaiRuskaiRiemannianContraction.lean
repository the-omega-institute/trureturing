/- GID: D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact qubit CQ contraction coefficients for dual WY, geometric and BKM metrics. -/

/-
proof_shape: result: bind-only; all private lemmas are consumed bind-only auxiliaries.
escape_witness: none
admission_basis: open-problem-resolution (#13774; Proved)
Consumed private theorem helpers (proof_shape: bind-only):
  trace_conj_eigenbasis; consumers: hs_conj_eigenbasis, metric_eigenbasis | hs_conj_eigenbasis; consumers: hs_omega_im_zero, hs_resolvent_real
  schur_hs_real; consumers: hs_resolvent_real, metric_eigenbasis | hs_omega_im_zero; consumers: metric_eigenbasis
  metric_eigenbasis; consumers: metric_congr_positive, metric_extreme_resolvent, metric_kernel_integral, metric_kernel_mixture, metric_pos, metric_weight_integrable | resolvent_equation; consumers: extreme_metric_pauli
  resolvent_equation_unique; consumers: extreme_metric_pauli | hs_resolvent_real; consumers: metric_extreme_resolvent
  extreme_schur_coefficient; consumers: metric_extreme_resolvent | metric_extreme_resolvent; consumers: extreme_metric_pauli
  Pauli.xi_pos; consumers: Pauli.candidate_equation, Pauli.candidate_quadratic, extreme_metric_pinching | Pauli.action_coeffs; consumers: Pauli.candidate_equation
  Pauli.quadratic_coeffs; consumers: Pauli.candidate_quadratic | Pauli.candidate_equation; consumers: extreme_metric_pauli
  Pauli.candidate_quadratic; consumers: extreme_metric_pauli | extreme_metric_pauli; consumers: extreme_center_input, extreme_center_output, extreme_metric_pinching, extreme_output_pauli_bound, integral_pauli_bounds
  Pinching.cauchy_three; consumers: extreme_metric_pinching | Pinching.bures_pinching_bound; consumers: extreme_metric_pinching
  extreme_metric_pinching; consumers: dualWY_pauli_bounds, integral_pauli_bounds | phi_rho_pauli; consumers: dualWY_center_values, dualWY_pauli_bounds, extreme_center_output, extreme_output_pauli_bound, integral_center_values, integral_pauli_bounds
  phi_tangent_pauli; consumers: extreme_center_output, extreme_output_pauli_bound, integral_pauli_bounds | Pauli.diag_im_zero; consumers: Pauli.hermitian_trace_coordinates
  Pauli.hermitian_trace_coordinates; consumers: Pauli.density_coordinates, Pauli.tangent_coordinates | Pauli.density_coordinates; consumers: matrix_contraction_from_pauli
  Pauli.tangent_coordinates; consumers: matrix_contraction_from_pauli | Pauli.rho_hermitian; consumers: Pauli.rho_posDef
  Pauli.rho_det; consumers: Pauli.rho_radius_lt | Pauli.rho_radius_lt; consumers: matrix_contraction_from_pauli
  Pauli.rho_posDef; consumers: center_density, dualWY_center_values, dualWY_pauli_bounds, extreme_center_input, extreme_center_output, extreme_output_pauli_bound, integral_center_values, integral_pauli_bounds | Reduced.reduced_extreme_bound; consumers: Scalar.output_Q_bound
  Reduced.reduced_at_zero; consumers: extreme_center_output | Reduced.extreme_parameter_range; consumers: Scalar.output_Q_bound, Scalar.output_Q_identity
  Scalar.X_pos; consumers: Scalar.output_Q_identity, Scalar.reduced_Q | Scalar.output_radius_lt; consumers: Scalar.output_Q_identity, dualWY_pauli_bounds, extreme_center_output, extreme_output_pauli_bound, integral_pauli_bounds
  Scalar.reduced_Q; consumers: extreme_center_input | Scalar.output_Q_identity; consumers: Scalar.output_Q_bound, extreme_center_output
  Scalar.output_Q_bound; consumers: extreme_output_pauli_bound, integral_pauli_bounds | center_density; consumers: centerDensity, dualWY_center_values, integral_center_values
  sigma1_tangent; consumers: eta_eq_of_metric_bound | sigma1_as_pauli; consumers: extreme_center_input, extreme_center_output
  extreme_center_input; consumers: dualWY_center_values, integral_center_values | extreme_center_output; consumers: dualWY_center_values, integral_center_values
  metric_kernel_integral; consumers: integral_center_values, integral_pauli_bounds | metric_kernel_mixture; consumers: metric_dualWY_mixture
  Kernels.geometric_smooth_mass; consumers: geometric_center_values, geometric_pauli_bounds | Kernels.geometric_integral; consumers: Coefficient.geometric_coefficient_integral, geometric_center_values, geometric_pauli_bounds
  Kernels.dual_wy_is_half_mixture; consumers: metric_dualWY_mixture | Kernels.continuousOn_bkmDensity; consumers: Kernels.bkm_integrable, Kernels.bkm_integral, Kernels.bkm_mass, bkm_pauli_bounds
  Kernels.bkm_mass; consumers: Kernels.bkm_integral, bkm_center_values, bkm_pauli_bounds | Kernels.bkm_integral; consumers: Coefficient.bkm_coefficient_integral, bkm_center_values, bkm_pauli_bounds
  Kernels.geometric_integrable; consumers: geometric_center_values, geometric_pauli_bounds | Kernels.continuousOn_extreme; consumers: Kernels.bkm_integrable
  Kernels.bkm_integrable; consumers: bkm_center_values, bkm_pauli_bounds | metric_congr_positive; consumers: metric_dualWY_mixture
  metric_dualWY_mixture; consumers: dualWY_center_values, dualWY_pauli_bounds | metric_weight_integrable; consumers: integral_pauli_bounds
  Coefficient.c_as_kernel; consumers: Coefficient.bkm_coefficient_integral, Coefficient.geometric_coefficient_integral, coefficient_weight_integrable | Coefficient.geometric_closed; consumers: Coefficient.geometric_coefficient_integral
  Coefficient.bkm_closed; consumers: Coefficient.bkm_coefficient_integral, bkm_contraction | Coefficient.geometric_coefficient_integral; consumers: geometric_center_values, geometric_pauli_bounds
  Coefficient.bkm_coefficient_integral; consumers: bkm_center_values, bkm_pauli_bounds | integral_pauli_bounds; consumers: bkm_pauli_bounds, geometric_pauli_bounds
  coefficient_weight_integrable; consumers: bkm_pauli_bounds, geometric_pauli_bounds | geometric_weight_integrable; consumers: geometric_pauli_bounds
  geometric_pauli_bounds; consumers: dualWY_pauli_bounds, geometric_contraction | bkm_pauli_bounds; consumers: bkm_contraction
  integral_center_values; consumers: bkm_center_values, geometric_center_values | metric_pos; consumers: eta_eq_of_metric_bound
  geometric_positive; consumers: result | dualWY_positive; consumers: result
  bkm_positive; consumers: bkm_contraction, result | dual_coefficient_closed; consumers: dualWY_center_values, dualWY_pauli_bounds
  extreme_output_pauli_bound; consumers: dualWY_pauli_bounds | dualWY_pauli_bounds; consumers: dualWY_contraction
  matrix_contraction_from_pauli; consumers: bkm_contraction, dualWY_contraction, geometric_contraction | geometric_contraction; consumers: result
  dualWY_contraction; consumers: result | bkm_contraction; consumers: result
  geometric_center_values; consumers: dualWY_center_values, result | bkm_center_values; consumers: result
  dualWY_center_values; consumers: result | eta_eq_of_metric_bound; consumers: result
Consumed private definitions:
  kExtreme; consumers: Coefficient.bkm_coefficient_integral, Coefficient.c_as_kernel, Coefficient.geometric_coefficient_integral, Kernels.bkm_integrable, Kernels.bkm_integral, Kernels.continuousOn_extreme, Kernels.dual_wy_is_half_mixture, Kernels.geometric_integrable, Kernels.geometric_integral, coefficient_weight_integrable, dualWY_center_values, dualWY_pauli_bounds, extreme_center_input, extreme_center_output, extreme_metric_pauli, extreme_metric_pinching, extreme_output_pauli_bound, extreme_schur_coefficient, integral_center_values, integral_pauli_bounds, metric_dualWY_mixture, metric_extreme_resolvent | resolvent; consumers: extreme_metric_pauli, hs_resolvent_real, metric_extreme_resolvent, resolvent_equation
  Pauli.spin; consumers: Pauli.action_coeffs, Pauli.candidate_equation, Pauli.coeffCandidate, Pauli.density_coordinates, Pauli.hermitian_trace_coordinates, Pauli.quadratic_coeffs, Pauli.tangent_coordinates | Pauli.delta; consumers: Pauli.candidate, Pauli.candidate_equation, Pauli.candidate_quadratic, Pauli.xi_pos, extreme_center_input, extreme_center_output, extreme_metric_pauli, extreme_metric_pinching, extreme_output_pauli_bound, integral_pauli_bounds
  Pauli.xi; consumers: Pauli.candidate, Pauli.candidate_equation, Pauli.candidate_quadratic, Pauli.xi_pos, Scalar.Q, Scalar.X_pos, Scalar.output_Q_identity, Scalar.reduced_Q, extreme_center_input, extreme_center_output, extreme_metric_pauli, extreme_metric_pinching, extreme_output_pauli_bound, integral_pauli_bounds | Pauli.coeffCandidate; consumers: Pauli.action_coeffs, Pauli.candidate, Pauli.candidate_equation, Pauli.candidate_quadratic, Pauli.quadratic_coeffs
  Pauli.candidate; consumers: Pauli.candidate_equation, Pauli.candidate_quadratic, extreme_metric_pauli | Reduced.reducedRatio; consumers: Reduced.reduced_at_zero, Reduced.reduced_extreme_bound, Scalar.output_Q_bound, Scalar.output_Q_identity, extreme_center_output
  Scalar.Q; consumers: Scalar.output_Q_bound, Scalar.output_Q_identity, Scalar.reduced_Q, extreme_center_input, extreme_center_output, extreme_output_pauli_bound, integral_pauli_bounds | centerDensity; consumers: eta_eq_of_metric_bound
  Kernels.geometricSmoothWeight; consumers: Coefficient.geometric_coefficient_integral, Kernels.geometric_integrable, Kernels.geometric_integral, Kernels.geometric_smooth_mass, geometric_center_values, geometric_pauli_bounds, geometric_weight_integrable | Kernels.bkmDensity; consumers: Coefficient.bkm_coefficient_integral, Kernels.bkm_integrable, Kernels.bkm_integral, Kernels.bkm_mass, Kernels.continuousOn_bkmDensity, bkm_center_values, bkm_pauli_bounds
  Coefficient.c; consumers: Coefficient.bkm_coefficient_integral, Coefficient.c_as_kernel, Coefficient.geometric_coefficient_integral, bkm_pauli_bounds, coefficient_weight_integrable, dualWY_pauli_bounds, extreme_output_pauli_bound, geometric_pauli_bounds, integral_center_values, integral_pauli_bounds
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Information.ActualPureQubitGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
open Matrix MeasureTheory
open scoped ComplexOrder Interval
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)
namespace D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
def omegaHermitian (k : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let U : Matrix (Fin 2) (Fin 2) ℂ := h.eigenvectorUnitary
  let lam := h.eigenvalues
  let Y := Uᴴ * X * U
  let Z : Matrix (Fin 2) (Fin 2) ℂ := fun i j => ((k (lam i / lam j) / lam j : ℝ) : ℂ) * Y i j
  U * Z * Uᴴ
def omega (k : ℝ → ℝ) (rho X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if h : rho.IsHermitian then omegaHermitian k rho h X else 0
def phi (alpha tau : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let w0 := Matrix.trace X / 2
  let w1 := Matrix.trace (qubitX * X) / 2
  w0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) + ((alpha : ℂ) * w1) • qubitX + ((tau : ℂ) * w0) • qubitZ
def metric (k : ℝ → ℝ) (rho A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (Matrix.trace (Aᴴ * omega k rho A)).re
def ratio (k : ℝ → ℝ) (alpha tau : ℝ) (rho A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  metric k (phi alpha tau rho) (phi alpha tau A) / metric k rho A
def eta (k : ℝ → ℝ) (alpha tau : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}, ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
    (A.IsHermitian ∧ Matrix.trace A = 0) ∧ A ≠ 0 ∧ z = ratio k alpha tau rho.val A}
private def kExtreme (s x : ℝ) : ℝ :=
  (1+s)/2 * (1/(x+s) + 1/(1+s*x))
def kDualWY (x : ℝ) : ℝ := (1 + Real.sqrt x)^2 / (4*x)
def admissible (alpha tau : ℝ) : Prop :=
  0 ≤ alpha ∧ 0 < |tau| ∧ |tau| < 1 ∧ alpha^2 + tau^2 ≤ 1
def claim : Prop := ∀ alpha tau : ℝ, admissible alpha tau →
  eta kDualWY alpha tau = alpha^2 * (1 + Real.sqrt (1-tau^2)) / (2*(1-tau^2)) ∧
  eta (fun x : ℝ => Real.rpow x (-1/2)) alpha tau = alpha^2 / Real.sqrt (1-tau^2) ∧
  eta (dslope Real.log 1) alpha tau = alpha^2 * Real.log ((1+tau)/(1-tau)) / (2*tau)
/-- proof_shape: bind-only; consumers: hs_conj_eigenbasis, hs_omega_im_zero, metric_eigenbasis. -/
private lemma trace_conj_eigenbasis (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix.trace ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) X) = Matrix.trace X := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle,
    ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self h.eigenvectorUnitary, Matrix.one_mul]
/-- proof_shape: bind-only; consumers: hs_omega_im_zero, hs_resolvent_real. -/
private lemma hs_conj_eigenbasis (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (A B : Matrix (Fin 2) (Fin 2) ℂ) : (fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) A) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) B) = (fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) A B := by
  dsimp only
  rw [← Matrix.star_eq_conjTranspose, ← map_star, ← map_mul, trace_conj_eigenbasis, Matrix.star_eq_conjTranspose]
private lemma schur_hs_real (Y : Matrix (Fin 2) (Fin 2) ℂ) (W : Fin 2 → Fin 2 → ℝ) : ((fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) Y (fun i j => (W i j : ℂ)*Y i j)).re = ∑ i, ∑ j, W i j * Complex.normSq (Y i j) := by
  unfold Matrix.trace; simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; simp [Complex.mul_re,Complex.mul_im,Complex.normSq_apply]; ring
private lemma hs_omega_im_zero (k : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (h : rho.IsHermitian) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.trace (Aᴴ * omega k rho A)).im = 0 := by
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  let W := fun i j => k (h.eigenvalues i/h.eigenvalues j)/h.eigenvalues j
  have hA : A = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Y :=
    (StarAlgEquiv.apply_symm_apply _ A).symm
  have hO : omega k rho A = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ)
      h.eigenvectorUnitary) (fun i j => (W i j : ℂ)*Y i j) := by
    rw [omega, dif_pos h]
    rfl
  rw [hO, hA]
  change ((fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) _ _).im = 0
  rw [hs_conj_eigenbasis]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  simp [Complex.mul_re, Complex.mul_im]
  ring
private lemma metric_eigenbasis (k : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (A : Matrix (Fin 2) (Fin 2) ℂ) : metric k rho A = ∑ i, ∑ j, (k (h.eigenvalues i/h.eigenvalues j)/h.eigenvalues j) * Complex.normSq ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A i j) := by
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  let W := fun i j => k (h.eigenvalues i/h.eigenvalues j)/h.eigenvalues j
  have hA : A = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Y := (StarAlgEquiv.apply_symm_apply _ A).symm
  have hO : omega k rho A = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) (fun i j => (W i j : ℂ)*Y i j) := by
    rw [omega,dif_pos h]
    rfl
  have hcomplex : Matrix.trace (Aᴴ * omega k rho A) =
      ((∑ i, ∑ j, W i j * Complex.normSq (Y i j) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [hO, hA, ← Matrix.star_eq_conjTranspose, ← map_star, ← map_mul,
        trace_conj_eigenbasis]
      exact schur_hs_real Y W
    · simpa only [Complex.ofReal_im] using hs_omega_im_zero k rho h A
  have htrace : ((metric k rho A : ℝ) : ℂ) = Matrix.trace (Aᴴ * omega k rho A) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (hs_omega_im_zero k rho h A).symm
  exact Complex.ofReal_injective (htrace.trans hcomplex)
private def resolvent (s : ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) (fun i j => (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm X i j / ((h.eigenvalues i+s*h.eigenvalues j : ℝ) : ℂ))
private lemma resolvent_equation (s : ℝ) (hs : 0 ≤ s) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (h : rho.IsHermitian) (X : Matrix (Fin 2) (Fin 2) ℂ) : rho*resolvent s rho h X+(s : ℂ) • (resolvent s rho h X*rho) = X := by
  have hRho : (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm rho = Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) := by
    simpa [Unitary.conjStarAlgAut_symm, Function.comp_def] using h.conjStarAlgAut_star_eigenvectorUnitary
  apply EquivLike.injective (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm
  simp only [map_add, map_smul, map_mul, resolvent, StarAlgEquiv.symm_apply_apply, hRho]
  ext i j
  have hi : 0 < h.eigenvalues i := hp.eigenvalues_pos i
  have hj : 0 < h.eigenvalues j := hp.eigenvalues_pos j
  have hd : h.eigenvalues i+s*h.eigenvalues j ≠ 0 := ne_of_gt (by positivity)
  have hc : ((h.eigenvalues i+s*h.eigenvalues j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,smul_eq_mul]; push_cast at hc ⊢
  calc
    (h.eigenvalues i : ℂ)*((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm X i j/((h.eigenvalues i : ℂ)+(s : ℂ)*(h.eigenvalues j : ℂ))) +
        (s : ℂ)*(((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm X i j/((h.eigenvalues i : ℂ)+(s : ℂ)*(h.eigenvalues j : ℂ)))*(h.eigenvalues j : ℂ)) =
      (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm X i j * (((h.eigenvalues i : ℂ)+(s : ℂ)*(h.eigenvalues j : ℂ))*
        ((h.eigenvalues i : ℂ)+(s : ℂ)*(h.eigenvalues j : ℂ))⁻¹) := by ring
    _ = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm X i j := by rw [mul_inv_cancel₀ hc]; simp
private lemma resolvent_equation_unique (s : ℝ) (hs : 0 ≤ s) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (h : rho.IsHermitian) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (he : rho*X+(s : ℂ) • (X*rho) = rho*Y+(s : ℂ) • (Y*rho)) : X=Y := by
  have hRho : (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm rho = Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) := by
    simpa [Unitary.conjStarAlgAut_symm, Function.comp_def] using h.conjStarAlgAut_star_eigenvectorUnitary
  apply EquivLike.injective (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm
  ext i j
  have hij := congrArg (fun Z => (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm Z i j) he
  simp only [map_add, map_smul, map_mul, hRho, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, smul_eq_mul] at hij
  have hi : 0 < h.eigenvalues i := hp.eigenvalues_pos i
  have hj : 0 < h.eigenvalues j := hp.eigenvalues_pos j
  have hd : h.eigenvalues i+s*h.eigenvalues j ≠ 0 := ne_of_gt (by positivity)
  have hc : ((h.eigenvalues i : ℂ)+(s : ℂ)*(h.eigenvalues j : ℂ)) ≠ 0 := by exact_mod_cast hd
  apply mul_left_cancel₀ hc
  linear_combination hij
private lemma hs_resolvent_real (s : ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (A : Matrix (Fin 2) (Fin 2) ℂ) : ((fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) A (resolvent s rho h A)).re = ∑ i, ∑ j, Complex.normSq ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A i j)/(h.eigenvalues i+s*h.eigenvalues j) := by
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  let W := fun i j => 1/(h.eigenvalues i+s*h.eigenvalues j)
  let Z : Matrix (Fin 2) (Fin 2) ℂ := fun i j => (W i j : ℂ)*Y i j
  have hRes : resolvent s rho h A = (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Z := by
    unfold resolvent
    congr 1
    ext i j; simp [Z,W,Y,div_eq_mul_inv,mul_comm]
  have hPair : (fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) A ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Z)=(fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) Y Z := by
    calc
      (fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) A ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Z)=(fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Y) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) Z) := by rw [StarAlgEquiv.apply_symm_apply]
      _ = (fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) Y Z := hs_conj_eigenbasis rho h Y Z
  rw [hRes,hPair]
  simpa [Z,W,Y,div_eq_mul_inv,mul_comm] using schur_hs_real Y W
private lemma extreme_schur_coefficient (s a b : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hb : 0 < b) : kExtreme s (a/b)/b = (1+s)/2*(1/(a+s*b)+1/(b+s*a)) := by
  have hd1 : a+s*b ≠ 0 := ne_of_gt (by positivity)
  have hd2 : b+s*a ≠ 0 := ne_of_gt (by positivity)
  have hd3 : a/b+s ≠ 0 := ne_of_gt (by positivity)
  have hd4 : 1+s*(a/b) ≠ 0 := ne_of_gt (by positivity)
  unfold kExtreme; field_simp [ha.ne',hb.ne',hd1,hd2,hd3,hd4]
  <;> ring
private lemma metric_extreme_resolvent (s : ℝ) (hs : 0 ≤ s) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (h : rho.IsHermitian) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) : metric (kExtreme s) rho A = (1+s)*((fun A B : Matrix (Fin 2) (Fin 2) ℂ => Matrix.trace (Aᴴ * B)) A (resolvent s rho h A)).re := by
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  have hY : Y.IsHermitian := by
    change ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A)ᴴ=(Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A; rw [← Matrix.star_eq_conjTranspose, ← map_star, Matrix.star_eq_conjTranspose, hA.eq]
  have hnorm : Complex.normSq ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A 0 1)=Complex.normSq ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A 1 0) := by
    change Complex.normSq (Y 0 1)=Complex.normSq (Y 1 0); rw [← hY.apply 0 1]; simp
  have hcoef : ∀ i j : Fin 2, kExtreme s (h.eigenvalues i/h.eigenvalues j)/h.eigenvalues j = (1+s)/2*(1/(h.eigenvalues i+s*h.eigenvalues j)+1/(h.eigenvalues j+s*h.eigenvalues i)) := by
    intro i j; exact extreme_schur_coefficient s _ _ hs (hp.eigenvalues_pos i) (hp.eigenvalues_pos j)
  rw [metric_eigenbasis _ rho h A,hs_resolvent_real]; simp only [Fin.sum_univ_two]; rw [hcoef 0 0,hcoef 0 1,hcoef 1 0,hcoef 1 1,hnorm]; ring
namespace Pauli
private def spin (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![z,x-Complex.I*y;x+Complex.I*y,-z]
private def delta (w1 w2 w3 : ℝ) : ℝ := 1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])
private def xi (s w1 w2 w3 : ℝ) : ℝ := (1+s)^2-(1-s)^2*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])
private def coeffCandidate (b p q r w1 w2 w3 y1 y2 y3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (b : ℂ) • (1:(Matrix (Fin 2) (Fin 2) ℂ)) + spin
    ((p*y1+q*w1 : ℝ)+Complex.I*(r*(w2*y3-w3*y2) : ℝ))
    ((p*y2+q*w2 : ℝ)+Complex.I*(r*(w3*y1-w1*y3) : ℝ))
    ((p*y3+q*w3 : ℝ)+Complex.I*(r*(w1*y2-w2*y1) : ℝ))
private def candidate (s w1 w2 w3 y1 y2 y3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  coeffCandidate
    (-2*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])/((1+s)*delta w1 w2 w3))
    (2*(1+s)/xi s w1 w2 w3)
    (8*s*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])/(xi s w1 w2 w3*(1+s)*delta w1 w2 w3))
    (-2*(1-s)/xi s w1 w2 w3) w1 w2 w3 y1 y2 y3
private lemma xi_pos (s w1 w2 w3 : ℝ) (hs : 0 ≤ s) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 0 < xi s w1 w2 w3 := by
  have hR : 0 ≤ (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; positivity
  have hd : 0 < delta w1 w2 w3 := by unfold delta; linarith
  have hp : 0 < (1+s)^2 := sq_pos_of_pos (by linarith)
  have heq : xi s w1 w2 w3 = (1+s)^2*delta w1 w2 w3+4*s*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by
    unfold xi delta; ring
  rw [heq]
  positivity
private lemma action_coeffs (s b p q r w1 w2 w3 y1 y2 y3 : ℝ) : (blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))*coeffCandidate b p q r w1 w2 w3 y1 y2 y3 + (s : ℂ) • (coeffCandidate b p q r w1 w2 w3 y1 y2 y3*(blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) = coeffCandidate ((1+s)*(b+p*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])+q*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))/2) (((1+s)*p+(1-s)*r*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))/2) (((1+s)*(q+b)-(1-s)*r*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))/2) (((1+s)*r+(1-s)*p)/2) w1 w2 w3 y1 y2 y3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochMatrix,coeffCandidate,spin,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two, Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,pow_two] <;> ring
private lemma quadratic_coeffs (b p q r w1 w2 w3 y1 y2 y3 : ℝ) : (Matrix.trace ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))*coeffCandidate b p q r w1 w2 w3 y1 y2 y3)).re = 2*p*(y1^2+y2^2+y3^2)+2*q*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]) := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fin.sum_univ_two]; simp [blochMatrix,coeffCandidate,spin,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Complex.mul_re,Complex.mul_im,pow_two]; ring
private theorem candidate_equation (s w1 w2 w3 y1 y2 y3 : ℝ) (hs : 0 ≤ s) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : (blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))*candidate s w1 w2 w3 y1 y2 y3 + (s : ℂ) • (candidate s w1 w2 w3 y1 y2 y3*(blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) = (blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])) := by
  have hd : delta w1 w2 w3 ≠ 0 := ne_of_gt (by unfold delta; linarith)
  have hxi : xi s w1 w2 w3 ≠ 0 := (xi_pos s w1 w2 w3 hs hw).ne'
  have hsp : 1+s ≠ 0 := ne_of_gt (by linarith)
  let b := -2*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])/((1+s)*delta w1 w2 w3)
  let p := 2*(1+s)/xi s w1 w2 w3
  let q := 8*s*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])/(xi s w1 w2 w3*(1+s)*delta w1 w2 w3)
  let r := -2*(1-s)/xi s w1 w2 w3
  have h0 : b+p*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])+q*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) = 0 := by
    dsimp [b,p,q]; field_simp [hd,hxi,hsp]
    <;> simp only [xi,delta] <;> ring
  have h1 : (1+s)*p+(1-s)*r*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) = 2 := by
    dsimp [p,r]; field_simp [hxi]
    <;> simp only [xi] <;> ring
  have h2 : (1+s)*(q+b)-(1-s)*r*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]) = 0 := by
    dsimp [b,q,r]; field_simp [hd,hxi,hsp]
    <;> simp only [xi,delta] <;> ring
  have h3 : (1+s)*r+(1-s)*p = 0 := by dsimp [r,p]; ring
  change (blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))*coeffCandidate b p q r w1 w2 w3 y1 y2 y3 +
    (s : ℂ) • (coeffCandidate b p q r w1 w2 w3 y1 y2 y3*(blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) = _
  rw [action_coeffs,h0,h1,h2,h3]; ext i j
  fin_cases i <;> fin_cases j <;> simp [coeffCandidate,blochMatrix,spin] <;> ring
private theorem candidate_quadratic (s w1 w2 w3 y1 y2 y3 : ℝ) (hs : 0 ≤ s) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : (1+s)*(Matrix.trace ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))*candidate s w1 w2 w3 y1 y2 y3)).re = 4*(1+s)^2/xi s w1 w2 w3*(y1^2+y2^2+y3^2) + 16*s/(xi s w1 w2 w3*delta w1 w2 w3)*((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2 := by
  have hd : delta w1 w2 w3 ≠ 0 := ne_of_gt (by unfold delta; linarith)
  have hxi : xi s w1 w2 w3 ≠ 0 := (xi_pos s w1 w2 w3 hs hw).ne'
  have hsp : 1+s ≠ 0 := ne_of_gt (by linarith)
  unfold candidate; rw [quadratic_coeffs]; field_simp [hd,hxi,hsp]
  <;> ring
end Pauli
private lemma extreme_metric_pauli (s w1 w2 w3 y1 y2 y3 : ℝ) (hs : 0 ≤ s) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : metric (kExtreme s) ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) = 4*(1+s)^2/Pauli.xi s w1 w2 w3*(y1^2+y2^2+y3^2) + 16*s/(Pauli.xi s w1 w2 w3*Pauli.delta w1 w2 w3)* ((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2 := by
  have hA : ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))).IsHermitian := by
    apply Matrix.IsHermitian.ext; intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [blochMatrix,Pauli.spin,Complex.mul_re,Complex.mul_im]
  have he : resolvent s ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) hp.isHermitian ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) = Pauli.candidate s w1 w2 w3 y1 y2 y3 := by
    apply resolvent_equation_unique s hs _ hp hp.isHermitian; rw [resolvent_equation s hs _ hp hp.isHermitian, Pauli.candidate_equation s w1 w2 w3 y1 y2 y3 hs hw]
  rw [metric_extreme_resolvent s hs _ hp hp.isHermitian _ hA,he]; simp only [hA.eq]; exact Pauli.candidate_quadratic s w1 w2 w3 y1 y2 y3 hs hw
namespace Pinching
private theorem cauchy_three (w1 w2 w3 y1 y2 y3 : ℝ) : ((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2 ≤ (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) * (dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3]) := by
  simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 3)) (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]
private theorem bures_pinching_bound (w1 w2 w3 y1 y2 y3 : ℝ) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : y1^2/(1-w1^2) ≤ (dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3]) + ((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2/(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])) := by
  let d := 1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])
  let c := 1-w1^2
  have hd : 0 < d := by dsimp [d]; linarith
  have hc : 0 < c := by dsimp [c]; simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hw; nlinarith [sq_nonneg w2, sq_nonneg w3]
  let z2 := c*y2+w1*y1*w2
  let z3 := c*y3+w1*y1*w3
  have hs : 0 ≤ d*(z2^2+z3^2)+(w2*z2+w3*z3)^2 := by positivity
  have hid : c*(c*(d*((dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3]))+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2)-d*y1^2) = d*(z2^2+z3^2)+(w2*z2+w3*z3)^2 := by
    simp only [c,d,z2,z3,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; ring
  have hquad : d*y1^2 ≤ c*(d*(dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2) := by
    apply sub_nonneg.mp
    have hmul : 0 ≤ c*(c*(d*(dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2)-d*y1^2) := by
      rw [hid]; exact hs
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul) hc
  calc
    y1^2/(1-w1^2) ≤ (d*(dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2)/d := by
      apply (div_le_div_iff₀ hc hd).mpr; nlinarith only [hquad]
    _ = (dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2/(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])) := by
      change (d*(dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2)/d =
        (dotProduct (![y1, y2, y3] : Fin 3 → ℝ) ![y1, y2, y3])+((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2/d
      field_simp [hd.ne']
      <;> ring
end Pinching
private lemma extreme_metric_pinching (s w1 w2 w3 y1 y2 y3 : ℝ) (hs : 0 ≤ s) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 4*y1^2/(1-w1^2) ≤ metric (kExtreme s) ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) := by
  let R := (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])
  let Y := y1^2+y2^2+y3^2
  let D := (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3])
  let d := Pauli.delta w1 w2 w3
  let X := Pauli.xi s w1 w2 w3
  have hd : 0 < d := by dsimp [d,Pauli.delta]; linarith
  have hX : 0 < X := Pauli.xi_pos s w1 w2 w3 hs hw
  have hcs : D^2 ≤ R*Y := by
    simpa [D,R,Y,add_assoc,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using
      Pinching.cauchy_three w1 w2 w3 y1 y2 y3
  have hgap : 0 ≤ (1-s)^2/X*(R*Y-D^2) := mul_nonneg (div_nonneg (sq_nonneg _) hX.le) (sub_nonneg.mpr hcs)
  have hId : (1+s)^2/X*Y+4*s/(X*d)*D^2 - (Y+D^2/d) = (1-s)^2/X*(R*Y-D^2) := by
    field_simp [hd.ne',hX.ne']; dsimp [X,d,R,Pauli.xi,Pauli.delta]; ring
  have hB : y1^2/(1-w1^2) ≤ Y+D^2/d := by
    simpa [Y,D,d,add_assoc,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Pauli.delta,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using
      Pinching.bures_pinching_bound w1 w2 w3 y1 y2 y3 hw
  rw [extreme_metric_pauli s w1 w2 w3 y1 y2 y3 hs hp hw]; change 4*y1^2/(1-w1^2) ≤ 4*(1+s)^2/X*Y+16*s/(X*d)*D^2; rw [← hId] at hgap
  have hnorm : 4*y1^2/(1-w1^2) = 4*(y1^2/(1-w1^2)) := by ring
  rw [hnorm]
  calc
    4*(y1^2/(1-w1^2)) ≤ 4*(Y+D^2/d) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ ≤ 4*((1+s)^2/X*Y+4*s/(X*d)*D^2) :=
      mul_le_mul_of_nonneg_left (sub_nonneg.mp hgap) (by norm_num)
    _ = 4*(1+s)^2/X*Y+16*s/(X*d)*D^2 := by ring
private lemma phi_rho_pauli (alpha tau w1 w2 w3 : ℝ) : phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))=(blochMatrix 1 (WithLp.toLp 2 ![(alpha*w1),0,tau])) := by
  unfold phi; simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fin.sum_univ_two]; ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qubitX,qubitZ,blochMatrix,Complex.mul_re,Complex.mul_im] <;> ring <;> simp
private lemma phi_tangent_pauli (alpha tau y1 y2 y3 : ℝ) : phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))=(blochMatrix 0 (WithLp.toLp 2 ![2*(alpha*y1),2*0,2*0])) := by
  unfold phi; simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Fin.sum_univ_two]; ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [qubitX,qubitZ,blochMatrix,Complex.mul_re,Complex.mul_im] <;> ring <;> simp
namespace Pauli
private lemma diag_im_zero (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian) (i : Fin 2) : (A i i).im = 0 := by
  have hi := congrArg Complex.im (h.apply i i)
  change -(A i i).im = (A i i).im at hi; linarith
private lemma hermitian_trace_coordinates (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian) : A = ((Matrix.trace A).re/2 : ℂ) • (1:(Matrix (Fin 2) (Fin 2) ℂ)) + spin (A 0 1).re (-(A 0 1).im) ((A 0 0).re-(Matrix.trace A).re/2) := by
  have hd0 := diag_im_zero A h 0
  have hd1 := diag_im_zero A h 1
  have hr01 := congrArg Complex.re (h.apply 1 0)
  have hi01 := congrArg Complex.im (h.apply 1 0)
  change (A 0 1).re = (A 1 0).re at hr01; change -(A 0 1).im = (A 1 0).im at hi01; ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [spin,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im] <;>
    linarith
private lemma density_coordinates (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian) (ht : Matrix.trace A=1) : A=(blochMatrix 1 (WithLp.toLp 2 ![(2*(A 0 1).re),(-2*(A 0 1).im),(2*(A 0 0).re-1)])) := by
  conv_lhs => rw [hermitian_trace_coordinates A h,ht]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochMatrix,spin,Complex.mul_re,Complex.mul_im] <;> ring
private lemma tangent_coordinates (A : Matrix (Fin 2) (Fin 2) ℂ) (h : A.IsHermitian) (ht : Matrix.trace A=0) :
    A=blochMatrix 0 (WithLp.toLp 2 ![2*(A 0 1).re,2*(-(A 0 1).im),2*(A 0 0).re]) := by
  conv_lhs => rw [hermitian_trace_coordinates A h,ht]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochMatrix,spin,Complex.mul_re,Complex.mul_im] <;> ring
private lemma rho_hermitian (w1 w2 w3 : ℝ) : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).IsHermitian := by
  apply Matrix.IsHermitian.ext; intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochMatrix,spin,Complex.mul_re,Complex.mul_im]
private lemma rho_det (w1 w2 w3 : ℝ) : Matrix.det ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) = ((1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))/4 : ℝ) := by
  apply Complex.ext <;>
    simp [Matrix.det_fin_two,blochMatrix,spin,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Complex.mul_re,Complex.mul_im,pow_two] <;> ring
private lemma rho_radius_lt (w1 w2 w3 : ℝ) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1 := by
  have hd := hp.det_pos
  rw [rho_det] at hd
  have hr : 0 < (1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))/4 := by exact_mod_cast hd
  linarith
private lemma rho_posDef (w1 w2 w3 : ℝ) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef := by
  have hR : w3^2 < 1 := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hw; nlinarith [sq_nonneg w1,sq_nonneg w2]
  have ha : 0 < 1+w3 := by nlinarith [sq_nonneg (1+w3)]
  have hd : 0 < 1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by linarith
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (rho_hermitian w1 w2 w3); intro z hz
  let N := Complex.normSq (((1+w3 : ℝ) : ℂ)*z 0+(w1-Complex.I*w2)*z 1)
  have hId : (dotProduct (star z) (Matrix.mulVec ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) z)).re*(2*(1+w3)) = N+(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))*Complex.normSq (z 1) := by
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_two,Fin.sum_univ_three]; simp [blochMatrix,spin,N,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]; ring
  have hIm : (dotProduct (star z) (Matrix.mulVec ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) z)).im = 0 := by
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_two,Fin.sum_univ_three]; simp [blochMatrix,spin,Complex.mul_re,Complex.mul_im]; ring
  have hN : 0 ≤ N := Complex.normSq_nonneg _
  have hQ : 0 < N+(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))*Complex.normSq (z 1) := by
    by_cases h1 : z 1=0
    · have h0 : z 0 ≠ 0 := by
        intro h0; apply hz; ext i
        fin_cases i <;> simp [h0,h1]
      have hNpos : 0 < N := by
        apply Complex.normSq_pos.mpr; dsimp [N]; simp only [h1,mul_zero,add_zero]; exact mul_ne_zero (by exact_mod_cast ha.ne') h0
      simpa [h1] using hNpos
    · have hpos := mul_pos hd (Complex.normSq_pos.mpr h1)
      linarith
  apply Complex.pos_iff.mpr
  constructor
  · have hprod : 0 < (dotProduct (star z) (Matrix.mulVec ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) z)).re*(2*(1+w3)) := by
      rw [hId]; exact hQ
    exact (mul_pos_iff_of_pos_right (by positivity : 0 < 2*(1+w3))).mp hprod
  · exact hIm.symm
end Pauli
namespace Reduced
private def reducedRatio (a b q u : ℝ) : ℝ :=
  a * ((1-u)/(1-b-a*u)) * ((1-b-q*a*u)/(1-q*b-q*a*u))
private theorem reduced_extreme_bound (a b q u : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b < 1) (hab : a+b ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hu : 0 ≤ u) (hu1 : u < 1) : reducedRatio a b q u ≤ a / (1-q*b) := by
  have hd : 0 < 1-b := by linarith
  have hu' : 0 < 1-u := by linarith
  have hgap : 0 ≤ (1-b-a)*u := mul_nonneg (by linarith) hu
  have hD : 0 < 1-b-a*u := by nlinarith [mul_pos hd hu']
  have hau : 0 ≤ a*u := mul_nonneg ha hu
  have hqau : q*a*u ≤ a*u := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-q) hau]
  have hR : 0 < 1-b-q*a*u := by linarith
  have hqb : q*b ≤ b := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-q) hb]
  have hC : 0 < 1-q*b := by linarith
  have hE : 0 < 1-q*b-q*a*u := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-q) hb]
  have hfirst : (1-u)/(1-b-a*u) ≤ 1/(1-b) := by
    apply (div_le_div_iff₀ hD hd).mpr; nlinarith
  have hprod : 0 ≤ (q*a*u)*(b*(1-q)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hq ha) hu) (mul_nonneg hb (by linarith))
  have hsecond : (1-b-q*a*u)/(1-q*b-q*a*u) ≤ (1-b)/(1-q*b) := by
    apply (div_le_div_iff₀ hE hC).mpr; nlinarith
  unfold reducedRatio
  calc
    a * ((1-u)/(1-b-a*u)) * ((1-b-q*a*u)/(1-q*b-q*a*u)) ≤
        a * (1/(1-b)) * ((1-b-q*a*u)/(1-q*b-q*a*u)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfirst ha)
        (div_nonneg hR.le hE.le)
    _ ≤ a * (1/(1-b)) * ((1-b)/(1-q*b)) :=
      mul_le_mul_of_nonneg_left hsecond (mul_nonneg ha (div_nonneg zero_le_one hd.le))
    _ = a/(1-q*b) := by field_simp
private theorem reduced_at_zero (a b q : ℝ) (hb : b < 1) : reducedRatio a b q 0 = a/(1-q*b) := by
  unfold reducedRatio
  have hd : 1-b ≠ 0 := by linarith
  simp only [mul_zero, sub_zero, zero_mul]; field_simp [hd]
private theorem extreme_parameter_range (s : ℝ) (hs : 0 ≤ s) : 0 ≤ ((1-s)/(1+s))^2 ∧ ((1-s)/(1+s))^2 ≤ 1 := by
  constructor
  · positivity
  · rw [div_pow]
    have hp : 0 < (1+s)^2 := sq_pos_of_pos (by linarith)
    apply (div_le_one hp).mpr; nlinarith
end Reduced
namespace Scalar
private def Q (s w1 w2 w3 y1 y2 y3 : ℝ) :=
  4*(1+s)^2/Pauli.xi s w1 w2 w3*(y1^2+y2^2+y3^2)+
    16*s/(Pauli.xi s w1 w2 w3*(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3])))*((dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![y1, y2, y3]))^2
private lemma X_pos (s w1 w2 w3 : ℝ) (hs : 0 ≤ s) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 0 < Pauli.xi s w1 w2 w3 := by
  have hR : 0 ≤ (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; positivity
  have hd : 0 < 1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by linarith
  have heq : Pauli.xi s w1 w2 w3 = (1+s)^2*(1-(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]))+4*s*(dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) := by unfold Pauli.xi; ring
  rw [heq]
  have hsp : 0 < (1+s)^2 := sq_pos_of_pos (by linarith)
  positivity
private lemma output_radius_lt (alpha tau w : ℝ) (ht : tau^2 < 1) (hab : alpha^2+tau^2 ≤ 1) (hw : w^2 < 1) : (dotProduct (![(alpha*w), 0, tau] : Fin 3 → ℝ) ![(alpha*w), 0, tau]) < 1 := by
  have hgap : 0 ≤ (1-tau^2-alpha^2)*w^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hp : 0 < (1-tau^2)*(1-w^2) := mul_pos (by linarith) (by linarith)
  simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; nlinarith
private lemma reduced_Q (s w y : ℝ) (hs : 0 ≤ s) (hw : w^2 < 1) : Q s w 0 0 y 0 0 = 4*y^2/(1-w^2) := by
  have hd : 1-w^2 ≠ 0 := ne_of_gt (by linarith)
  have hX : Pauli.xi s w 0 0 ≠ 0 := (X_pos s w 0 0 hs (by simpa [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using hw)).ne'
  unfold Q; simp only [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; simp only [zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero]
  have hdR : 1-(dotProduct (![w, 0, 0] : Fin 3 → ℝ) ![w, 0, 0]) ≠ 0 := by simpa [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using hd
  field_simp [hd,hdR,hX]; simp only [Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,zero_pow (by decide : 2 ≠ 0),add_zero]; field_simp [hd]; ring
private lemma output_Q_identity (alpha tau s w y : ℝ) (hs : 0 ≤ s) (ht : tau^2 < 1) (hab : alpha^2+tau^2 ≤ 1) (hw : w^2 < 1) : Q s (alpha*w) 0 tau (alpha*y) 0 0 = Reduced.reducedRatio (alpha^2) (tau^2) (((1-s)/(1+s))^2) (w^2) * (4*y^2/(1-w^2)) := by
  let q := ((1-s)/(1+s))^2
  have hq0 : 0 ≤ q := (Reduced.extreme_parameter_range s hs).1
  have hq1 : q ≤ 1 := (Reduced.extreme_parameter_range s hs).2
  have hr := output_radius_lt alpha tau w ht hab hw
  have hD : 0 < 1-tau^2-alpha^2*w^2 := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hr; nlinarith
  have hDq : 0 < 1-q*tau^2-q*alpha^2*w^2 := by
    have hqm : q*(tau^2+alpha^2*w^2) ≤ tau^2+alpha^2*w^2 := by
      apply mul_le_of_le_one_left (by positivity) hq1
    nlinarith only [hD,hqm]
  have hX := X_pos s (alpha*w) 0 tau hs hr
  have hc : 1-w^2 ≠ 0 := ne_of_gt (by linarith)
  have hsp : 1+s ≠ 0 := ne_of_gt (by linarith)
  change Q s (alpha*w) 0 tau (alpha*y) 0 0 =
    Reduced.reducedRatio (alpha^2) (tau^2) q (w^2) * (4*y^2/(1-w^2))
  have hdout : 1-(dotProduct (![(alpha*w), 0, tau] : Fin 3 → ℝ) ![(alpha*w), 0, tau]) ≠ 0 := ne_of_gt (by linarith)
  have hqDen : 1-q*tau^2-q*alpha^2*w^2 = Pauli.xi s (alpha*w) 0 tau/(1+s)^2 := by
    simp only [q,Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]; field_simp [hsp]; ring
  have hqNum : 1-tau^2-q*alpha^2*w^2 = ((1+s)^2*(1-tau^2-alpha^2*w^2)+4*s*alpha^2*w^2)/(1+s)^2 := by
    dsimp [q]; field_simp [hsp]; ring
  unfold Q Reduced.reducedRatio; rw [hqDen,hqNum]; field_simp [hc,hD.ne',hX.ne',hdout,hsp]; simp only [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero]; ring
private lemma output_Q_bound (alpha tau s w y : ℝ) (hs : 0 ≤ s) (ht : tau^2 < 1) (hab : alpha^2+tau^2 ≤ 1) (hw : w^2 < 1) : Q s (alpha*w) 0 tau (alpha*y) 0 0 ≤ (alpha^2/(1-((1-s)/(1+s))^2*tau^2))*(4*y^2/(1-w^2)) := by
  rw [output_Q_identity alpha tau s w y hs ht hab hw]; exact mul_le_mul_of_nonneg_right
    (Reduced.reduced_extreme_bound (alpha^2) (tau^2) _ (w^2)
      (sq_nonneg _) (sq_nonneg _) ht hab (Reduced.extreme_parameter_range s hs).1
      (Reduced.extreme_parameter_range s hs).2 (sq_nonneg _) hw)
    (div_nonneg (by positivity) (by linarith))
end Scalar
private lemma center_density : (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])).PosDef ∧ Matrix.trace (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))=1 := by
  constructor
  · apply Pauli.rho_posDef
    norm_num [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two]
  · norm_num [blochMatrix,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two] <;> ring
private def centerDensity : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1} := ⟨(blochMatrix 1 (WithLp.toLp 2 ![0,0,0])),center_density⟩
private lemma sigma1_tangent : (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.IsHermitian ∧ Matrix.trace A = 0) qubitX ∧ qubitX ≠ 0 := by
  constructor
  · constructor
    · simpa only [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using qubit_weyl_star.2.1
    · norm_num [qubitX,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two]
  · intro hz
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hz
    norm_num [qubitX] at h01
private lemma sigma1_as_pauli : qubitX=(blochMatrix 0 (WithLp.toLp 2 ![2*1,2*0,2*0])) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitX,blochMatrix,Pauli.spin]
private lemma extreme_center_input (s : ℝ) (hs : 0 ≤ s) : metric (kExtreme s) (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4 := by
  rw [sigma1_as_pauli,extreme_metric_pauli s 0 0 0 1 0 0 hs (Pauli.rho_posDef 0 0 0 (by norm_num [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two])) (by norm_num [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two])]
  have h := Scalar.reduced_Q s 0 1 hs (by norm_num)
  simpa [Scalar.Q,Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Pauli.delta] using h
private lemma extreme_center_output (alpha tau s : ℝ) (hAdm : admissible alpha tau) (hs : 0 ≤ s) : metric (kExtreme s) (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX) = 4*(alpha^2/(1-((1-s)/(1+s))^2*tau^2)) := by
  obtain ⟨ha,ht0,ht1,hab⟩ := hAdm
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau]
  have hw : (dotProduct (![(alpha*0), 0, tau] : Fin 3 → ℝ) ![(alpha*0), 0, tau]) < 1 := Scalar.output_radius_lt alpha tau 0 ht hab (by norm_num)
  rw [sigma1_as_pauli,phi_rho_pauli,phi_tangent_pauli, extreme_metric_pauli s (alpha*0) 0 tau (alpha*1) 0 0 hs (Pauli.rho_posDef _ _ _ hw) hw]
  have h := Scalar.output_Q_identity alpha tau s 0 1 hs ht hab (by norm_num)
  simp only [zero_pow (by decide : 2 ≠ 0)] at h; rw [Reduced.reduced_at_zero _ _ _ ht] at h
  simpa [Scalar.Q,Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Pauli.delta,mul_comm] using h
private lemma metric_kernel_integral (K : ℝ → (ℝ → ℝ)) (k : ℝ → ℝ) (f : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (A : Matrix (Fin 2) (Fin 2) ℂ) (hrep : ∀ x : ℝ, 0 < x → (∫ t in (0:ℝ)..1, f t*K t x)=k x) (hi : ∀ x : ℝ, 0 < x → IntervalIntegrable (fun t => f t*K t x) volume 0 1) : (∫ t in (0:ℝ)..1, f t*metric (K t) rho A) = metric k rho A := by
  let h := hp.isHermitian
  let lam := h.eigenvalues
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  have hratio : ∀ i j : Fin 2, 0 < lam i/lam j := fun i j => div_pos (hp.eigenvalues_pos i) (hp.eigenvalues_pos j)
  have hentry : ∀ i j : Fin 2, IntervalIntegrable (fun t => f t*(K t (lam i/lam j)/lam j*Complex.normSq (Y i j))) volume 0 1 := by
    intro i j
    have he := (hi _ (hratio i j)).mul_const (Complex.normSq (Y i j)/lam j)
    convert he using 1
    funext t; ring
  have hpoint : ∀ t : ℝ, f t*metric (K t) rho A = ∑ i : Fin 2, ∑ j : Fin 2, f t*(K t (lam i/lam j)/lam j*Complex.normSq (Y i j)) := by
    intro t; rw [metric_eigenbasis _ rho h A]; simp only [Finset.mul_sum]
    rfl
  have hentryIntegral : ∀ i j : Fin 2, (∫ t in (0:ℝ)..1, f t*(K t (lam i/lam j)/lam j*Complex.normSq (Y i j))) = k (lam i/lam j)/lam j*Complex.normSq (Y i j) := by
    intro i j
    have hf : (fun t : ℝ => f t*(K t (lam i/lam j)/lam j*Complex.normSq (Y i j))) = (fun t : ℝ => (f t*K t (lam i/lam j))*(Complex.normSq (Y i j)/lam j)) := by
      funext t; ring
    rw [hf,intervalIntegral.integral_mul_const,hrep _ (hratio i j)]; ring
  simp_rw [hpoint]
  simp only [Fin.sum_univ_two]; rw [intervalIntegral.integral_add ((hentry 0 0).add (hentry 0 1)) ((hentry 1 0).add (hentry 1 1)), intervalIntegral.integral_add (hentry 0 0) (hentry 0 1), intervalIntegral.integral_add (hentry 1 0) (hentry 1 1)]
  simp_rw [hentryIntegral]
  rw [metric_eigenbasis _ rho h A]; simp only [Fin.sum_univ_two]
  rfl
private lemma metric_kernel_mixture (k1 k2 : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (h : rho.IsHermitian) (A : Matrix (Fin 2) (Fin 2) ℂ) : metric (fun x => (k1 x+k2 x)/2) rho A = (metric k1 rho A+metric k2 rho A)/2 := by
  rw [metric_eigenbasis _ rho h A,metric_eigenbasis _ rho h A,metric_eigenbasis _ rho h A]; simp only [Fin.sum_univ_two]; ring
namespace Kernels
private def geometricSmoothWeight (t : ℝ) : ℝ := 4/(Real.pi*(1+t^2))
private def bkmDensity (s : ℝ) : ℝ := 2/(1+s)^2
private theorem geometric_smooth_mass : (∫ t in (0:ℝ)..1, geometricSmoothWeight t) = 1 := by
  unfold geometricSmoothWeight
  have hfn : (fun t : ℝ => 4/(Real.pi*(1+t^2))) = (fun t : ℝ => (4/Real.pi)*(1/(1+t^2))) := by
    funext t
    have h1 : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [h1,Real.pi_ne_zero]
    <;> ring
  rw [hfn, intervalIntegral.integral_const_mul, integral_one_div_one_add_sq]; simp [Real.arctan_one]
private theorem geometric_integral (x : ℝ) (hx : 0 < x) : (∫ t in (0:ℝ)..1, geometricSmoothWeight t*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme (t^2) x) = (fun x : ℝ => Real.rpow x (-1/2)) x := by
  let r := Real.sqrt x
  have hr : 0 < r := Real.sqrt_pos.mpr hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hfirst : (∫ t in (0:ℝ)..1, 1/(x+t^2)) = Real.arctan (1/r)/r := by
    have hfn : (fun t : ℝ => 1/(x+t^2)) = (fun t : ℝ => (r^2+t^2)⁻¹) := by
      funext t; rw [hr2,one_div]
    rw [hfn, integral_inv_sq_add_sq hr.ne']; simp; ring
  have hsecond : (∫ t in (0:ℝ)..1, 1/(1+x*t^2)) = Real.arctan r/r := by
    have hfn : (fun t : ℝ => 1/(1+x*t^2)) = (fun t : ℝ => (1/x)*((1/r)^2+t^2)⁻¹) := by
      funext t
      have hn : 1+x*t^2 ≠ 0 := ne_of_gt (by positivity)
      rw [← hr2]; field_simp [hr.ne']
      <;> ring
    rw [hfn, intervalIntegral.integral_const_mul, integral_inv_sq_add_sq (by positivity : (1/r : ℝ) ≠ 0)]; simp; rw [← hr2]; field_simp [hr.ne']
    <;> ring
  have hi1 : IntervalIntegrable (fun t : ℝ => 1/(x+t^2)) volume 0 1 := by
    apply Continuous.intervalIntegrable; exact continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (by positivity))
  have hi2 : IntervalIntegrable (fun t : ℝ => 1/(1+x*t^2)) volume 0 1 := by
    apply Continuous.intervalIntegrable; exact continuous_const.div (continuous_const.add (continuous_const.mul (continuous_id.pow 2))) (fun t => ne_of_gt (by positivity))
  have hfn : (fun t : ℝ => geometricSmoothWeight t*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme (t^2) x) = (fun t : ℝ => (2/Real.pi)*(1/(x+t^2)+1/(1+x*t^2))) := by
    funext t; unfold geometricSmoothWeight D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme
    have h1 : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [h1, Real.pi_ne_zero]
    <;> ring
  rw [hfn, intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2, hfirst, hsecond]
  change 2/Real.pi * (Real.arctan (1/r)/r + Real.arctan r/r) = x ^ (-1/2 : ℝ)
  rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_inv, ← one_div]; change 2/Real.pi * (Real.arctan (1/r)/r + Real.arctan r/r) = 1/r; rw [one_div, Real.arctan_inv_of_pos hr]; field_simp [Real.pi_ne_zero,hr.ne']
  <;> ring
private theorem dual_wy_is_half_mixture (x : ℝ) (hx : 0 < x) : D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kDualWY x = (D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme 0 x+(fun x : ℝ => Real.rpow x (-1/2)) x)/2 := by
  unfold D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kDualWY D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme
  change (1 + Real.sqrt x)^2 / (4*x) = ((1+0)/2 * (1/(x+0) + 1/(1+0*x)) + x ^ (-1/2 : ℝ))/2
  rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_inv, ← one_div]
  have hs : (Real.sqrt x)^2 = x := Real.sq_sqrt hx.le
  have hp : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  simp only [zero_add,add_zero,zero_mul,mul_zero,one_mul,mul_one]
  have hgeom : 1/Real.sqrt x = Real.sqrt x/x := by
    apply (div_eq_div_iff hp hx.ne').mpr; nlinarith only [hs]
  rw [hgeom]; field_simp [hx.ne']; nlinarith only [hs]
private lemma continuousOn_bkmDensity : ContinuousOn bkmDensity (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]; unfold bkmDensity; apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2); intro s hs
  have hp : 0 < 1+s := by linarith [hs.1]
  exact pow_ne_zero 2 hp.ne'
private theorem bkm_mass : (∫ s in (0:ℝ)..1, bkmDensity s) = 1 := by
  let F := fun s : ℝ => -2/(1+s)
  have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F (bkmDensity s) s := by
    intro s hs; rw [Set.uIcc_of_le zero_le_one] at hs
    have hne : 1+s ≠ 0 := ne_of_gt (by linarith [hs.1])
    have h := (((hasDerivAt_const s (1:ℝ)).add (hasDerivAt_id s)).inv hne).const_mul (-2)
    simpa [F,bkmDensity,div_eq_mul_inv] using h
  calc
    (∫ s in (0:ℝ)..1, bkmDensity s) = F 1-F 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv continuousOn_bkmDensity.intervalIntegrable
    _ = 1 := by norm_num [F]
private theorem bkm_integral (x : ℝ) (hx : 0 < x) : (∫ s in (0:ℝ)..1, bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) = (dslope Real.log 1) x := by
  by_cases hx1 : x=1
  · subst x
    have hcongr : (∫ s in (0:ℝ)..1, bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s 1) = (∫ s in (0:ℝ)..1, bkmDensity s) := by
      apply intervalIntegral.integral_congr; intro s hs; rw [Set.uIcc_of_le zero_le_one] at hs
      have hne : 1+s ≠ 0 := ne_of_gt (by linarith [hs.1])
      have hk : D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s 1 = 1 := by
        unfold D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme; field_simp [hne]
        <;> ring
      change bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s 1 = bkmDensity s; rw [hk,mul_one]
    rw [hcongr,bkm_mass]; simp [dslope_same, Real.deriv_log]
  · let F := fun s : ℝ => (Real.log (1+x*s)-Real.log (x+s))/(x-1)
    have hderiv : ∀ s ∈ Set.uIcc (0:ℝ) 1, HasDerivAt F (bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) s := by
      intro s hs; rw [Set.uIcc_of_le zero_le_one] at hs
      have hs0 : 0 ≤ s := hs.1
      have hxs : x+s ≠ 0 := ne_of_gt (by positivity)
      have hsx : 1+x*s ≠ 0 := ne_of_gt (by positivity)
      have h1s : 1+s ≠ 0 := ne_of_gt (by positivity)
      have hxm : x-1 ≠ 0 := sub_ne_zero.mpr hx1
      have h := ((((hasDerivAt_const s (1:ℝ)).add ((hasDerivAt_id s).const_mul x)).log hsx).sub
        (((hasDerivAt_const s x).add (hasDerivAt_id s)).log hxs)).div_const (x-1)
      have hF : HasDerivAt F ((x/(1+x*s)-1/(x+s))/(x-1)) s := by
        simpa only [F,Pi.add_apply,Pi.sub_apply,id_eq,zero_add,mul_one] using h
      have heq : ((x/(1+x*s)-1/(x+s))/(x-1)) = bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x := by
        unfold bkmDensity D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme
        have hsx' : 1+s*x ≠ 0 := by simpa [mul_comm] using hsx
        field_simp [hxs,hsx,hsx',h1s,hxm]
        <;> ring
      rw [heq] at hF; exact hF
    have hcK : ContinuousOn (fun s : ℝ => D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) (Set.uIcc (0:ℝ) 1) := by
      rw [Set.uIcc_of_le zero_le_one]; unfold D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme; apply ((continuousOn_const.add continuousOn_id).div_const (2:ℝ)).mul; apply ContinuousOn.add
      · apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
        intro s hs; change x+s ≠ 0; exact ne_of_gt (by linarith [hs.1])
      · apply continuousOn_const.div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
        intro s hs
        have hs0 : 0 ≤ s := hs.1
        change 1+s*x ≠ 0; exact ne_of_gt (by positivity)
    calc
      (∫ s in (0:ℝ)..1, bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) = F 1-F 0 :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (continuousOn_bkmDensity.mul hcK).intervalIntegrable
      _ = (dslope Real.log 1) x := by
        simp [F,dslope,Function.update_apply,Real.deriv_log,slope_def_field,hx1,add_comm]
        <;> ring
private lemma geometric_integrable (x : ℝ) (hx : 0 < x) : IntervalIntegrable (fun t => geometricSmoothWeight t*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme (t^2) x) volume 0 1 := by
  apply Continuous.intervalIntegrable; unfold geometricSmoothWeight D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme; apply Continuous.mul
  · exact continuous_const.div (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))
      (fun t => mul_ne_zero Real.pi_ne_zero (ne_of_gt (by positivity)))
  · apply ((continuous_const.add (continuous_id.pow 2)).div_const (2:ℝ)).mul
    apply Continuous.add
    · exact continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun t => ne_of_gt (by positivity))
    · exact continuous_const.div (continuous_const.add ((continuous_id.pow 2).mul continuous_const)) (fun t => ne_of_gt (by positivity))
private lemma continuousOn_extreme (x : ℝ) (hx : 0 < x) : ContinuousOn (fun s => D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]; unfold D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme; apply ((continuousOn_const.add continuousOn_id).div_const (2:ℝ)).mul; apply ContinuousOn.add
  · apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro s hs; change x+s ≠ 0; exact ne_of_gt (by linarith [hs.1])
  · apply continuousOn_const.div (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    change 1+s*x ≠ 0; exact ne_of_gt (by positivity)
private lemma bkm_integrable (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable (fun s => bkmDensity s*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s x) volume 0 1 :=
  (continuousOn_bkmDensity.mul (continuousOn_extreme x hx)).intervalIntegrable
end Kernels
private lemma metric_congr_positive (k1 k2 : ℝ → ℝ) (he : ∀ x, 0 < x → k1 x=k2 x) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (A : Matrix (Fin 2) (Fin 2) ℂ) : metric k1 rho A=metric k2 rho A := by
  rw [metric_eigenbasis _ rho hp.isHermitian A,metric_eigenbasis _ rho hp.isHermitian A]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; rw [he _ (div_pos (hp.eigenvalues_pos i) (hp.eigenvalues_pos j))]
private lemma metric_dualWY_mixture (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (A : Matrix (Fin 2) (Fin 2) ℂ) : metric kDualWY rho A=(metric (kExtreme 0) rho A+metric (fun x : ℝ => Real.rpow x (-1/2)) rho A)/2 := by
  calc
    metric kDualWY rho A=metric (fun x => (kExtreme 0 x+(fun x : ℝ => Real.rpow x (-1/2)) x)/2) rho A :=
      metric_congr_positive _ _ Kernels.dual_wy_is_half_mixture rho hp A
    _ = _ := metric_kernel_mixture _ _ rho hp.isHermitian A
private lemma metric_weight_integrable (K : ℝ → (ℝ → ℝ)) (f : ℝ → ℝ) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (A : Matrix (Fin 2) (Fin 2) ℂ) (hi : ∀ x : ℝ, 0 < x → IntervalIntegrable (fun t => f t*K t x) volume 0 1) : IntervalIntegrable (fun t => f t*metric (K t) rho A) volume 0 1 := by
  let h := hp.isHermitian
  let lam := h.eigenvalues
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  let e := fun i j t => f t*(K t (lam i/lam j)/lam j*Complex.normSq (Y i j))
  have he : ∀ i j : Fin 2, IntervalIntegrable (e i j) volume 0 1 := by
    intro i j
    have hr : 0 < lam i/lam j := div_pos (hp.eigenvalues_pos i) (hp.eigenvalues_pos j)
    have hprod := (hi _ hr).mul_const (Complex.normSq (Y i j)/lam j)
    convert hprod using 1
    funext t; dsimp [e]; ring
  have heq : (fun t => f t*metric (K t) rho A) = (fun t => (e 0 0 t+e 0 1 t)+(e 1 0 t+e 1 1 t)) := by
    funext t; rw [metric_eigenbasis _ rho h A]; simp only [Fin.sum_univ_two]; dsimp [e,Y,lam]; ring
  rw [heq]; exact ((he 0 0).add (he 0 1)).add ((he 1 0).add (he 1 1))
namespace Coefficient
private def c (alpha tau s : ℝ) := alpha^2/(1-((1-s)/(1+s))^2*tau^2)
private lemma c_as_kernel (alpha tau s : ℝ) (ht : |tau| < 1) (hs : 0 ≤ s) : c alpha tau s = alpha^2*D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s ((1-tau)/(1+tau))/(1+tau) := by
  obtain ⟨htn,htp⟩ := abs_lt.mp ht
  have hp : 0 < 1+tau := by linarith
  have hm : 0 < 1-tau := by linarith
  have hs1 : 0 < 1+s := by linarith
  have hr : 0 < (1-tau)/(1+tau) := div_pos hm hp
  have hq0 : 0 ≤ ((1-s)/(1+s))^2 := sq_nonneg _
  have hq1 : ((1-s)/(1+s))^2 ≤ 1 := by
    rw [div_pow]; apply (div_le_one (sq_pos_of_pos hs1)).mpr; nlinarith
  have ht2 : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau]
  have hq : 0 < 1-((1-s)/(1+s))^2*tau^2 := by
    have he := mul_le_of_le_one_left (sq_nonneg tau) hq1
    linarith
  have hd1 : (1-tau)/(1+tau)+s ≠ 0 := ne_of_gt (by positivity)
  have hd2 : 1+s*((1-tau)/(1+tau)) ≠ 0 := ne_of_gt (by positivity)
  let d1 := 1-tau+s*(1+tau)
  let d2 := 1+tau+s*(1-tau)
  have hd1p : 0 < d1 := by dsimp [d1]; positivity
  have hd2p : 0 < d2 := by dsimp [d2]; positivity
  have h1 : (1-tau)/(1+tau)+s=d1/(1+tau) := by dsimp [d1]; field_simp [hp.ne'] <;> ring
  have h2 : 1+s*((1-tau)/(1+tau))=d2/(1+tau) := by dsimp [d2]; field_simp [hp.ne'] <;> ring
  have hden : 1-((1-s)/(1+s))^2*tau^2=d1*d2/(1+s)^2 := by
    dsimp [d1,d2]; field_simp [hs1.ne']; ring
  unfold c D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme; rw [hden,h1,h2]; field_simp [hp.ne',hs1.ne',hd1p.ne',hd2p.ne']; dsimp [d1,d2]; ring
private lemma geometric_closed (alpha tau : ℝ) (ht : |tau| < 1) : alpha^2*(fun x : ℝ => Real.rpow x (-1/2)) ((1-tau)/(1+tau))/(1+tau)=alpha^2/Real.sqrt (1-tau^2) := by
  obtain ⟨htn,htp⟩ := abs_lt.mp ht
  have hp : 0 < 1+tau := by linarith
  have hm : 0 < 1-tau := by linarith
  have hr : 0 < (1-tau)/(1+tau) := div_pos hm hp
  have hd : 0 < 1-tau^2 := by nlinarith [sq_abs tau,abs_nonneg tau]
  have he : Real.sqrt ((1-tau)/(1+tau))*(1+tau)=Real.sqrt (1-tau^2) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp; rw [mul_pow,Real.sq_sqrt hr.le,Real.sq_sqrt hd.le]; field_simp [hp.ne']; ring
  change alpha^2 * (((1-tau)/(1+tau)) ^ (-1/2 : ℝ)) / (1+tau) = alpha^2 / Real.sqrt (1-tau^2)
  rw [show (-1/2 : ℝ) = -(1/2) by ring, Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_inv, ← one_div]; rw [← he]; field_simp [hp.ne',(Real.sqrt_pos.mpr hr).ne'] <;> ring
private lemma bkm_closed (alpha tau : ℝ) (ht : |tau| < 1) (ht0 : tau ≠ 0) : alpha^2*(dslope Real.log 1) ((1-tau)/(1+tau))/(1+tau)= alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau) := by
  obtain ⟨htn,htp⟩ := abs_lt.mp ht
  have hp : 0 < 1+tau := by linarith
  have hm : 0 < 1-tau := by linarith
  have hr1 : (1-tau)/(1+tau) ≠ 1 := by
    intro he
    have he' := (div_eq_one_iff_eq hp.ne').mp he
    apply ht0; linarith
  have hxm : (1-tau)/(1+tau)-1 ≠ 0 := sub_ne_zero.mpr hr1
  have hinv : (1-tau)/(1+tau)=((1+tau)/(1-tau))⁻¹ := by simp [div_eq_mul_inv,mul_comm]
  simp only [dslope, Function.update_apply, Real.deriv_log, inv_one, slope_def_field, Real.log_one, sub_zero]; rw [if_neg hr1,hinv,Real.log_inv]; field_simp [hp.ne',hm.ne',ht0,hxm] <;> ring_nf <;> field_simp [ht0] <;> ring
private lemma geometric_coefficient_integral (alpha tau : ℝ) (ht : |tau| < 1) : (∫ t in (0:ℝ)..1, Kernels.geometricSmoothWeight t*c alpha tau (t^2))= alpha^2/Real.sqrt (1-tau^2) := by
  have hrep : (fun t : ℝ => Kernels.geometricSmoothWeight t*c alpha tau (t^2)) = (fun t => (alpha^2/(1+tau))*(Kernels.geometricSmoothWeight t* D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme (t^2) ((1-tau)/(1+tau)))) := by
    funext t; rw [c_as_kernel alpha tau (t^2) ht (sq_nonneg _)]; ring
  rw [hrep,intervalIntegral.integral_const_mul,Kernels.geometric_integral]
  · have h := geometric_closed alpha tau ht
    convert h using 1 <;> ring
  · exact div_pos (by linarith [(abs_lt.mp ht).2]) (by linarith [(abs_lt.mp ht).1])
private lemma bkm_coefficient_integral (alpha tau : ℝ) (ht : |tau| < 1) (ht0 : tau ≠ 0) : (∫ s in (0:ℝ)..1, Kernels.bkmDensity s*c alpha tau s)= alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau) := by
  have hrep : (∫ s in (0:ℝ)..1, Kernels.bkmDensity s*c alpha tau s)= (∫ s in (0:ℝ)..1, (alpha^2/(1+tau))*(Kernels.bkmDensity s* D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction.kExtreme s ((1-tau)/(1+tau)))) := by
    apply intervalIntegral.integral_congr; intro s hs; rw [Set.uIcc_of_le zero_le_one] at hs; change Kernels.bkmDensity s*c alpha tau s = _; rw [c_as_kernel alpha tau s ht hs.1]; ring
  rw [hrep,intervalIntegral.integral_const_mul,Kernels.bkm_integral]
  · have h := bkm_closed alpha tau ht ht0
    convert h using 1 <;> ring
  · exact div_pos (by linarith [(abs_lt.mp ht).2]) (by linarith [(abs_lt.mp ht).1])
end Coefficient
private lemma integral_pauli_bounds (alpha tau : ℝ) (hAdm : admissible alpha tau) (p f : ℝ → ℝ) (k : ℝ → ℝ) (C : ℝ) (hp0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ p t) (hf0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ f t) (hfi : IntervalIntegrable f volume 0 1) (hfm : (∫ t in (0:ℝ)..1, f t)=1) (hrep : ∀ x, 0 < x → (∫ t in (0:ℝ)..1, f t*kExtreme (p t) x)=k x) (hi : ∀ x, 0 < x → IntervalIntegrable (fun t => f t*kExtreme (p t) x) volume 0 1) (hci : IntervalIntegrable (fun t => f t*Coefficient.c alpha tau (p t)) volume 0 1) (hcm : (∫ t in (0:ℝ)..1, f t*Coefficient.c alpha tau (p t))=C) (w1 w2 w3 y1 y2 y3 : ℝ) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 4*y1^2/(1-w1^2) ≤ metric k ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) ∧ metric k (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ C*(4*y1^2/(1-w1^2)) := by
  let Rho := (blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))
  let A := (blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))
  let d := 4*y1^2/(1-w1^2)
  obtain ⟨ha,ht0,ht1,hab⟩ := hAdm
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau]
  have hw1 : w1^2 < 1 := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hw; nlinarith [sq_nonneg w2,sq_nonneg w3]
  have hOut : (dotProduct (![(alpha*w1), 0, tau] : Fin 3 → ℝ) ![(alpha*w1), 0, tau]) < 1 := Scalar.output_radius_lt alpha tau w1 ht hab hw1
  have hOutp : (phi alpha tau Rho).PosDef := by
    dsimp [Rho]; rw [phi_rho_pauli]; exact Pauli.rho_posDef _ _ _ hOut
  have hin := metric_weight_integrable (fun t => kExtreme (p t)) f Rho hp A hi
  have hout := metric_weight_integrable (fun t => kExtreme (p t)) f _ hOutp (phi alpha tau A) hi
  have hInRep := metric_kernel_integral (fun t => kExtreme (p t)) k f Rho hp A hrep hi
  have hOutRep := metric_kernel_integral (fun t => kExtreme (p t)) k f _ hOutp (phi alpha tau A) hrep hi
  have hdInt : (∫ t in (0:ℝ)..1, f t*d)=d := by rw [intervalIntegral.integral_mul_const,hfm,one_mul]
  have hcInt : (∫ t in (0:ℝ)..1, (f t*Coefficient.c alpha tau (p t))*d)=C*d := by
    rw [intervalIntegral.integral_mul_const,hcm]
  constructor
  · have hbound := intervalIntegral.integral_mono_on zero_le_one (hfi.mul_const d) hin (fun t hT =>
        mul_le_mul_of_nonneg_left
          (extreme_metric_pinching (p t) w1 w2 w3 y1 y2 y3 (hp0 t hT) hp hw) (hf0 t hT))
    rwa [hdInt,hInRep] at hbound
  · have hpoint : ∀ t ∈ Set.Icc (0:ℝ) 1,
        f t*metric (kExtreme (p t)) (phi alpha tau Rho) (phi alpha tau A) ≤
          (f t*Coefficient.c alpha tau (p t))*d := by
      intro t hT
      have hb := Scalar.output_Q_bound alpha tau (p t) w1 y1 (hp0 t hT) ht hab hw1
      have hmet : metric (kExtreme (p t)) (phi alpha tau Rho) (phi alpha tau A) ≤ Coefficient.c alpha tau (p t)*d := by
        dsimp [Rho,A]; rw [phi_rho_pauli,phi_tangent_pauli,extreme_metric_pauli (p t) (alpha*w1) 0 tau (alpha*y1) 0 0 (hp0 t hT) (Pauli.rho_posDef _ _ _ hOut) hOut]
        simpa only [Coefficient.c,d,Scalar.Q,Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two, Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Pauli.delta] using hb
      have hh := mul_le_mul_of_nonneg_left hmet (hf0 t hT)
      simpa only [mul_assoc] using hh
    have hbound := intervalIntegral.integral_mono_on zero_le_one hout (hci.mul_const d) hpoint
    rwa [hOutRep,hcInt] at hbound
private lemma coefficient_weight_integrable (alpha tau : ℝ) (ht : |tau| < 1) (p f : ℝ → ℝ) (hp0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ p t) (hi : ∀ x, 0 < x → IntervalIntegrable (fun t => f t*kExtreme (p t) x) volume 0 1) : IntervalIntegrable (fun t => f t*Coefficient.c alpha tau (p t)) volume 0 1 := by
  let x := (1-tau)/(1+tau)
  have hx : 0 < x := div_pos (by linarith [(abs_lt.mp ht).2]) (by linarith [(abs_lt.mp ht).1])
  have hK := (hi x hx).const_mul (alpha^2/(1+tau))
  have heq : Set.EqOn (fun t => (alpha^2/(1+tau))*(f t*kExtreme (p t) x)) (fun t => f t*Coefficient.c alpha tau (p t)) (Set.uIoc (0:ℝ) 1) := by
    intro t hT; rw [Set.uIoc_of_le zero_le_one] at hT; change (alpha^2/(1+tau))*(f t*kExtreme (p t) x)=f t*Coefficient.c alpha tau (p t); rw [Coefficient.c_as_kernel alpha tau (p t) ht (hp0 t ⟨hT.1.le,hT.2⟩)]; change (alpha^2/(1+tau))*(f t*kExtreme (p t) ((1-tau)/(1+tau)))=
      f t*(alpha^2*kExtreme (p t) ((1-tau)/(1+tau))/(1+tau))
    ring
  exact (intervalIntegrable_congr heq).mp hK
private lemma geometric_weight_integrable : IntervalIntegrable Kernels.geometricSmoothWeight volume 0 1 := by
  apply Continuous.intervalIntegrable; unfold Kernels.geometricSmoothWeight; exact continuous_const.div (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))
    (fun t => mul_ne_zero Real.pi_ne_zero (ne_of_gt (by positivity)))
private lemma geometric_pauli_bounds (alpha tau : ℝ) (hAdm : admissible alpha tau) (w1 w2 w3 y1 y2 y3 : ℝ) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 4*y1^2/(1-w1^2) ≤ metric (fun x : ℝ => Real.rpow x (-1/2)) ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) ∧ metric (fun x : ℝ => Real.rpow x (-1/2)) (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ (alpha^2/Real.sqrt (1-tau^2))*(4*y1^2/(1-w1^2)) := by
  have hci := coefficient_weight_integrable alpha tau hAdm.2.2.1 (fun t => t^2)
    Kernels.geometricSmoothWeight (fun t _ => sq_nonneg t) Kernels.geometric_integrable
  exact integral_pauli_bounds alpha tau hAdm (fun t => t^2) Kernels.geometricSmoothWeight
    (fun x : ℝ => Real.rpow x (-1/2)) (alpha^2/Real.sqrt (1-tau^2)) (fun t _ => sq_nonneg t)
    (fun t _ => by unfold Kernels.geometricSmoothWeight; positivity)
    geometric_weight_integrable Kernels.geometric_smooth_mass Kernels.geometric_integral
    Kernels.geometric_integrable hci (Coefficient.geometric_coefficient_integral alpha tau hAdm.2.2.1)
    w1 w2 w3 y1 y2 y3 hp hw
private lemma bkm_pauli_bounds (alpha tau : ℝ) (hAdm : admissible alpha tau) (w1 w2 w3 y1 y2 y3 : ℝ) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 4*y1^2/(1-w1^2) ≤ metric (dslope Real.log 1) ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) ∧ metric (dslope Real.log 1) (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ (alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau))*(4*y1^2/(1-w1^2)) := by
  have ht0 : tau ≠ 0 := fun hz => by simpa [hz] using hAdm.2.1
  have hci := coefficient_weight_integrable alpha tau hAdm.2.2.1 id
    Kernels.bkmDensity (fun t hT => hT.1) Kernels.bkm_integrable
  exact integral_pauli_bounds alpha tau hAdm id Kernels.bkmDensity (dslope Real.log 1)
    (alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau)) (fun t hT => hT.1)
    (fun t _ => by unfold Kernels.bkmDensity; positivity)
    Kernels.continuousOn_bkmDensity.intervalIntegrable Kernels.bkm_mass Kernels.bkm_integral
    Kernels.bkm_integrable hci (Coefficient.bkm_coefficient_integral alpha tau hAdm.2.2.1 ht0)
    w1 w2 w3 y1 y2 y3 hp hw
private lemma integral_center_values (alpha tau : ℝ) (hAdm : admissible alpha tau) (p f : ℝ → ℝ) (k : ℝ → ℝ) (C : ℝ) (hp0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ p t) (hfm : (∫ t in (0:ℝ)..1, f t)=1) (hrep : ∀ x, 0 < x → (∫ t in (0:ℝ)..1, f t*kExtreme (p t) x)=k x) (hi : ∀ x, 0 < x → IntervalIntegrable (fun t => f t*kExtreme (p t) x) volume 0 1) (hcm : (∫ t in (0:ℝ)..1, f t*Coefficient.c alpha tau (p t))=C) : metric k (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4 ∧ metric k (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)=4*C := by
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau,hAdm.2.2.1]
  have hpout : (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))).PosDef := by
    rw [phi_rho_pauli]; apply Pauli.rho_posDef
    simpa [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using ht
  have hIn := metric_kernel_integral (fun t => kExtreme (p t)) k f _ center_density.1 qubitX hrep hi
  have hOut := metric_kernel_integral (fun t => kExtreme (p t)) k f _ hpout (phi alpha tau qubitX) hrep hi
  constructor
  · rw [← hIn]
    have heq : (∫ t in (0:ℝ)..1, f t*metric (kExtreme (p t)) (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX)= (∫ t in (0:ℝ)..1, f t*4) := by
      apply intervalIntegral.integral_congr; intro t hT; rw [Set.uIcc_of_le zero_le_one] at hT; change f t*metric (kExtreme (p t)) (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=f t*4; rw [extreme_center_input (p t) (hp0 t hT)]
    rw [heq,intervalIntegral.integral_mul_const,hfm]; norm_num
  · rw [← hOut]
    have heq : (∫ t in (0:ℝ)..1, f t*metric (kExtreme (p t)) (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX))= (∫ t in (0:ℝ)..1, 4*(f t*Coefficient.c alpha tau (p t))) := by
      apply intervalIntegral.integral_congr; intro t hT; rw [Set.uIcc_of_le zero_le_one] at hT; change f t*metric (kExtreme (p t)) (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)=_; rw [extreme_center_output alpha tau (p t) hAdm (hp0 t hT)]; unfold Coefficient.c; ring
    rw [heq,intervalIntegral.integral_const_mul,hcm]
private lemma metric_pos (k : ℝ → ℝ) (hk : ∀ x, 0 < x → 0 < k x) (rho : Matrix (Fin 2) (Fin 2) ℂ) (hp : rho.PosDef) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ≠ 0) : 0 < metric k rho A := by
  let h := hp.isHermitian
  let Y := (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A
  have hY : Y ≠ 0 := by
    intro hy; apply hA
    have he : (Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A=(Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm 0 := by simpa only [Y, map_zero] using hy
    calc
      A=(Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm A) := (StarAlgEquiv.apply_symm_apply _ A).symm
      _=(Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary) ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary).symm 0) := congrArg ((Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) h.eigenvectorUnitary)) he
      _=0 := StarAlgEquiv.apply_symm_apply _ 0
  obtain ⟨i,j,hij⟩ : ∃ i j : Fin 2, Y i j ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hY; ext i j; exact hn i j
  have hcoef : ∀ i j : Fin 2, 0 < k (h.eigenvalues i/h.eigenvalues j)/h.eigenvalues j := by
    intro i j; exact div_pos (hk _ (div_pos (hp.eigenvalues_pos i) (hp.eigenvalues_pos j))) (hp.eigenvalues_pos j)
  rw [metric_eigenbasis _ rho h A]; apply (Finset.sum_pos_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hcoef i j).le (Complex.normSq_nonneg _)))).mpr
  refine ⟨i,Finset.mem_univ i,?_⟩
  apply (Finset.sum_pos_iff_of_nonneg (fun j _ => mul_nonneg (hcoef i j).le (Complex.normSq_nonneg _))).mpr; exact ⟨j,Finset.mem_univ j,mul_pos (hcoef i j) (Complex.normSq_pos.mpr hij)⟩
private lemma geometric_positive (x : ℝ) (hx : 0 < x) : 0 < (fun x : ℝ => Real.rpow x (-1/2)) x := by
  exact Real.rpow_pos_of_pos hx _
private lemma dualWY_positive (x : ℝ) (hx : 0 < x) : 0 < kDualWY x := by
  unfold kDualWY
  have h1 : 0 < 1+Real.sqrt x := by positivity
  exact div_pos (sq_pos_of_pos h1) (by positivity)
private lemma bkm_positive (x : ℝ) (hx : 0 < x) : 0 < (dslope Real.log 1) x := by
  simp only [dslope, Function.update_apply, Real.deriv_log, inv_one, slope_def_field, Real.log_one, sub_zero]
  split_ifs with hx1
  · norm_num
  · rcases lt_or_gt_of_ne hx1 with hlt|hgt
    · exact div_pos_of_neg_of_neg (Real.log_neg hx hlt) (sub_neg.mpr hlt)
    · exact div_pos (Real.log_pos hgt) (sub_pos.mpr hgt)
private lemma dual_coefficient_closed (alpha tau : ℝ) (ht : |tau| < 1) : (alpha^2/(1-tau^2)+alpha^2/Real.sqrt (1-tau^2))/2= alpha^2*(1+Real.sqrt (1-tau^2))/(2*(1-tau^2)) := by
  have hd : 0 < 1-tau^2 := by nlinarith [sq_abs tau,abs_nonneg tau]
  have hr : 0 < Real.sqrt (1-tau^2) := Real.sqrt_pos.mpr hd
  have he : (Real.sqrt (1-tau^2))^2=1-tau^2 := Real.sq_sqrt hd.le
  have hdiv : 1/Real.sqrt (1-tau^2)=Real.sqrt (1-tau^2)/(1-tau^2) := by
    apply (div_eq_div_iff hr.ne' hd.ne').mpr; nlinarith only [he]
  have hA : alpha^2/Real.sqrt (1-tau^2)=alpha^2*(1/Real.sqrt (1-tau^2)) := by ring
  rw [hA,hdiv]; field_simp [hd.ne'] <;> ring
private lemma extreme_output_pauli_bound (alpha tau s w1 w2 w3 y1 y2 y3 : ℝ) (hAdm : admissible alpha tau) (hs : 0 ≤ s) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : metric (kExtreme s) (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ Coefficient.c alpha tau s*(4*y1^2/(1-w1^2)) := by
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau,hAdm.2.2.1]
  have hw1 : w1^2 < 1 := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hw; nlinarith [sq_nonneg w2,sq_nonneg w3]
  have hout : (dotProduct (![(alpha*w1), 0, tau] : Fin 3 → ℝ) ![(alpha*w1), 0, tau]) < 1 :=
    Scalar.output_radius_lt alpha tau w1 ht hAdm.2.2.2 hw1
  rw [phi_rho_pauli,phi_tangent_pauli,extreme_metric_pauli s (alpha*w1) 0 tau (alpha*y1) 0 0 hs (Pauli.rho_posDef _ _ _ hout) hout]
  simpa only [Coefficient.c,Scalar.Q,Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two, Pauli.xi,Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two,Pauli.delta] using
    Scalar.output_Q_bound alpha tau s w1 y1 hs ht hAdm.2.2.2 hw1
private lemma dualWY_pauli_bounds (alpha tau : ℝ) (hAdm : admissible alpha tau) (w1 w2 w3 y1 y2 y3 : ℝ) (hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef) (hw : (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1) : 4*y1^2/(1-w1^2) ≤ metric kDualWY ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3]))) ∧ metric kDualWY (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ (alpha^2*(1+Real.sqrt (1-tau^2))/(2*(1-tau^2)))*(4*y1^2/(1-w1^2)) := by
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau,hAdm.2.2.1]
  have hw1 : w1^2 < 1 := by simp [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] at hw; nlinarith [sq_nonneg w2,sq_nonneg w3]
  have hout : (dotProduct (![(alpha*w1), 0, tau] : Fin 3 → ℝ) ![(alpha*w1), 0, tau]) < 1 :=
    Scalar.output_radius_lt alpha tau w1 ht hAdm.2.2.2 hw1
  have hpout : (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))).PosDef := by
    rw [phi_rho_pauli]; exact Pauli.rho_posDef _ _ _ hout
  have hG := geometric_pauli_bounds alpha tau hAdm w1 w2 w3 y1 y2 y3 hp hw
  have hP := extreme_metric_pinching 0 w1 w2 w3 y1 y2 y3 (by norm_num) hp hw
  have hO := extreme_output_pauli_bound alpha tau 0 w1 w2 w3 y1 y2 y3 hAdm (by norm_num) hw
  have hC0 : Coefficient.c alpha tau 0=alpha^2/(1-tau^2) := by simp [Coefficient.c]
  rw [hC0] at hO
  constructor
  · rw [metric_dualWY_mixture _ hp]
    linarith only [hG.1,hP]
  · rw [metric_dualWY_mixture _ hpout,← dual_coefficient_closed alpha tau hAdm.2.2.1]
    calc
      _ ≤ ((alpha^2/(1-tau^2))*(4*y1^2/(1-w1^2))+
        (alpha^2/Real.sqrt (1-tau^2))*(4*y1^2/(1-w1^2)))/2 := by
          linarith only [hO,hG.2]
      _ = _ := by ring
private lemma matrix_contraction_from_pauli (k : ℝ → ℝ) (alpha tau C : ℝ) (h : ∀ w1 w2 w3 y1 y2 y3 : ℝ, ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef → (dotProduct (![w1, w2, w3] : Fin 3 → ℝ) ![w1, w2, w3]) < 1 → metric k (phi alpha tau ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])))) (phi alpha tau ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) ≤ C*metric k ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))) ((blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])))) (rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : (A.IsHermitian ∧ Matrix.trace A = 0)) : metric k (phi alpha tau rho.val) (phi alpha tau A) ≤ C*metric k rho.val A := by
  let w1 := 2*(rho.val 0 1).re
  let w2 := -2*(rho.val 0 1).im
  let w3 := 2*(rho.val 0 0).re-1
  let y1 := (A 0 1).re
  let y2 := -(A 0 1).im
  let y3 := (A 0 0).re
  have hr : rho.val=(blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3])) := Pauli.density_coordinates _ rho.property.1.isHermitian rho.property.2
  have hy : A=(blochMatrix 0 (WithLp.toLp 2 ![2*y1,2*y2,2*y3])) := Pauli.tangent_coordinates _ hA.1 hA.2
  have hp : ((blochMatrix 1 (WithLp.toLp 2 ![w1,w2,w3]))).PosDef := hr ▸ rho.property.1
  rw [hr,hy]; exact h w1 w2 w3 y1 y2 y3 hp (Pauli.rho_radius_lt w1 w2 w3 hp)
private lemma geometric_contraction (alpha tau : ℝ) (hAdm : admissible alpha tau) (rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : (A.IsHermitian ∧ Matrix.trace A = 0)) : metric (fun x : ℝ => Real.rpow x (-1/2)) (phi alpha tau rho.val) (phi alpha tau A) ≤ (alpha^2/Real.sqrt (1-tau^2))*metric (fun x : ℝ => Real.rpow x (-1/2)) rho.val A := by
  apply matrix_contraction_from_pauli
  · intro w1 w2 w3 y1 y2 y3 hp hw
    have hB := geometric_pauli_bounds alpha tau hAdm w1 w2 w3 y1 y2 y3 hp hw
    exact hB.2.trans (mul_le_mul_of_nonneg_left hB.1 (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)))
  · exact hA
private lemma dualWY_contraction (alpha tau : ℝ) (hAdm : admissible alpha tau) (rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : (A.IsHermitian ∧ Matrix.trace A = 0)) : metric kDualWY (phi alpha tau rho.val) (phi alpha tau A) ≤ (alpha^2*(1+Real.sqrt (1-tau^2))/(2*(1-tau^2)))*metric kDualWY rho.val A := by
  have hd : 0 < 1-tau^2 := by nlinarith [sq_abs tau,abs_nonneg tau,hAdm.2.2.1]
  apply matrix_contraction_from_pauli
  · intro w1 w2 w3 y1 y2 y3 hp hw
    have hB := dualWY_pauli_bounds alpha tau hAdm w1 w2 w3 y1 y2 y3 hp hw
    have hC : 0 ≤ alpha^2*(1+Real.sqrt (1-tau^2))/(2*(1-tau^2)) := by positivity
    exact hB.2.trans (mul_le_mul_of_nonneg_left hB.1 hC)
  · exact hA
private lemma bkm_contraction (alpha tau : ℝ) (hAdm : admissible alpha tau) (rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : (A.IsHermitian ∧ Matrix.trace A = 0)) : metric (dslope Real.log 1) (phi alpha tau rho.val) (phi alpha tau A) ≤ (alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau))*metric (dslope Real.log 1) rho.val A := by
  have ht0 : tau ≠ 0 := fun hz => by simpa [hz] using hAdm.2.1
  have hp : 0 < 1+tau := by linarith [(abs_lt.mp hAdm.2.2.1).1]
  have hm : 0 < 1-tau := by linarith [(abs_lt.mp hAdm.2.2.1).2]
  have hC : 0 ≤ alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau) := by
    rw [← Coefficient.bkm_closed alpha tau hAdm.2.2.1 ht0]; exact div_nonneg (mul_nonneg (sq_nonneg _) (bkm_positive _ (div_pos hm hp)).le) hp.le
  apply matrix_contraction_from_pauli
  · intro w1 w2 w3 y1 y2 y3 hp hw
    have hB := bkm_pauli_bounds alpha tau hAdm w1 w2 w3 y1 y2 y3 hp hw
    exact hB.2.trans (mul_le_mul_of_nonneg_left hB.1 hC)
  · exact hA
private lemma geometric_center_values (alpha tau : ℝ) (hAdm : admissible alpha tau) : metric (fun x : ℝ => Real.rpow x (-1/2)) (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4 ∧ metric (fun x : ℝ => Real.rpow x (-1/2)) (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)= 4*(alpha^2/Real.sqrt (1-tau^2)) := by
  exact integral_center_values alpha tau hAdm (fun t => t^2) Kernels.geometricSmoothWeight
    (fun x : ℝ => Real.rpow x (-1/2)) (alpha^2/Real.sqrt (1-tau^2)) (fun t _ => sq_nonneg t)
    Kernels.geometric_smooth_mass Kernels.geometric_integral Kernels.geometric_integrable
    (Coefficient.geometric_coefficient_integral alpha tau hAdm.2.2.1)
private lemma bkm_center_values (alpha tau : ℝ) (hAdm : admissible alpha tau) : metric (dslope Real.log 1) (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4 ∧ metric (dslope Real.log 1) (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)= 4*(alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau)) := by
  have ht0 : tau ≠ 0 := fun hz => by simpa [hz] using hAdm.2.1
  exact integral_center_values alpha tau hAdm id Kernels.bkmDensity (dslope Real.log 1)
    (alpha^2*Real.log ((1+tau)/(1-tau))/(2*tau)) (fun t hT => hT.1)
    Kernels.bkm_mass Kernels.bkm_integral Kernels.bkm_integrable
    (Coefficient.bkm_coefficient_integral alpha tau hAdm.2.2.1 ht0)
private lemma dualWY_center_values (alpha tau : ℝ) (hAdm : admissible alpha tau) : metric kDualWY (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4 ∧ metric kDualWY (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)= 4*(alpha^2*(1+Real.sqrt (1-tau^2))/(2*(1-tau^2))) := by
  have hG := geometric_center_values alpha tau hAdm
  have ht : tau^2 < 1 := by nlinarith [sq_abs tau,abs_nonneg tau,hAdm.2.2.1]
  have hpout : (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))).PosDef := by
    rw [phi_rho_pauli]; apply Pauli.rho_posDef
    simpa [Matrix.cons_dotProduct_cons, Matrix.dotProduct_of_isEmpty, add_zero, ← pow_two] using ht
  constructor
  · rw [metric_dualWY_mixture _ center_density.1,extreme_center_input 0 (by norm_num),hG.1]
    norm_num
  · rw [metric_dualWY_mixture _ hpout,extreme_center_output alpha tau 0 hAdm (by norm_num),hG.2,
      ← dual_coefficient_closed alpha tau hAdm.2.2.1]
    norm_num; ring
private lemma eta_eq_of_metric_bound (k : ℝ → ℝ) (alpha tau C : ℝ) (hk : ∀ x, 0 < x → 0 < k x) (hB : ∀ (rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}) (A : Matrix (Fin 2) (Fin 2) ℂ), (A.IsHermitian ∧ Matrix.trace A = 0) → metric k (phi alpha tau rho.val) (phi alpha tau A) ≤ C*metric k rho.val A) (hIn : metric k (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=4) (hOut : metric k (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)=4*C) : eta k alpha tau=C := by
  have hBound : ∀ z ∈ {z : ℝ | ∃ rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}, ∃ A : Matrix (Fin 2) (Fin 2) ℂ, (A.IsHermitian ∧ Matrix.trace A = 0) ∧ A ≠ 0 ∧ z=ratio k alpha tau rho.val A}, z ≤ C := by
    rintro z ⟨rho,A,hA,hn,rfl⟩
    unfold ratio; exact (div_le_iff₀ (metric_pos k hk rho.val rho.property.1 A hn)).mpr (hB rho A hA)
  have hAt : ratio k alpha tau centerDensity.val qubitX=C := by
    change metric k (phi alpha tau (blochMatrix 1 (WithLp.toLp 2 ![0,0,0]))) (phi alpha tau qubitX)/metric k (blochMatrix 1 (WithLp.toLp 2 ![0,0,0])) qubitX=C; rw [hIn,hOut]; ring
  have hMem : C ∈ {z : ℝ | ∃ rho : {rho : Matrix (Fin 2) (Fin 2) ℂ // rho.PosDef ∧ Matrix.trace rho = 1}, ∃ A : Matrix (Fin 2) (Fin 2) ℂ, (A.IsHermitian ∧ Matrix.trace A = 0) ∧ A ≠ 0 ∧ z=ratio k alpha tau rho.val A} :=
    ⟨centerDensity,qubitX,sigma1_tangent.1,sigma1_tangent.2,hAt.symm⟩
  unfold eta; apply le_antisymm
  · exact csSup_le ⟨C,hMem⟩ hBound
  · exact le_csSup ⟨C,hBound⟩ hMem
theorem result : ∀ alpha tau : ℝ, admissible alpha tau →
  eta kDualWY alpha tau = alpha^2 * (1 + Real.sqrt (1-tau^2)) / (2*(1-tau^2)) ∧
  eta (fun x : ℝ => Real.rpow x (-1/2)) alpha tau = alpha^2 / Real.sqrt (1-tau^2) ∧
  eta (dslope Real.log 1) alpha tau = alpha^2 * Real.log ((1+tau)/(1-tau)) / (2*tau) := by
  intro alpha tau hAdm
  have hG := geometric_center_values alpha tau hAdm
  have hD := dualWY_center_values alpha tau hAdm
  have hB := bkm_center_values alpha tau hAdm
  refine ⟨?_,?_,?_⟩
  · exact eta_eq_of_metric_bound kDualWY alpha tau _ dualWY_positive
      (dualWY_contraction alpha tau hAdm) hD.1 hD.2
  · exact eta_eq_of_metric_bound (fun x : ℝ => Real.rpow x (-1/2)) alpha tau _ geometric_positive
      (geometric_contraction alpha tau hAdm) hG.1 hG.2
  · exact eta_eq_of_metric_bound (dslope Real.log 1) alpha tau _ bkm_positive
      (bkm_contraction alpha tau hAdm) hB.1 hB.2
end D5.S3.Quantum.QuantumChannels.HiaiRuskaiRiemannianContraction
