/- GID: D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: The Jordan domain of a unital positive matrix map. -/

/-
proof_shape: positive_map_hermitian: bind-only; escape_witness=none
  consumers: invariant_state_fixed_of_trace_preserving, hermitian_jordan_domain, positive_inverse_square_preserving
proof_shape: kadison_finite_weights: bind-only; escape_witness=none
  consumers: kadison_hermitian
proof_shape: diagonal_single_sum: bind-only; escape_witness=none
  consumers: kadison_hermitian
proof_shape: kadison_hermitian: bind-only; escape_witness=none
  consumers: invariant_state_fixed_of_trace_preserving, kadison_equality_of_weighted_trace_zero, hermitian_jordan_domain, positive_inverse_square_preserving
proof_shape: faithful_weighted_trace_zero: bind-only; escape_witness=none
  consumers: kadison_equality_of_weighted_trace_zero
proof_shape: kadison_equality_of_weighted_trace_zero: content; escape_witness=kadison_equality_of_weighted_trace_zero
  consumers: fixed_hermitian_square
proof_shape: fixed_hermitian_square: content; escape_witness=fixed_hermitian_square
  consumers: fixed_jordan_domain
proof_shape: jordan_hermitian: bind-only; escape_witness=none
  consumers: hermitian_jordan_domain
proof_shape: quadratic_psd_linear_zero: bind-only; escape_witness=none
  consumers: hermitian_jordan_domain
proof_shape: hermitian_jordan_domain: content; escape_witness=hermitian_jordan_domain
  consumers: hermitian_jordan_domain_complex
proof_shape: jordan_add_right: bind-only; escape_witness=none
  consumers: hermitian_jordan_domain_complex, complex_jordan_extension_on_submodule
proof_shape: jordan_add_left: bind-only; escape_witness=none
  consumers: complex_jordan_extension, fixed_jordan_domain, complex_jordan_extension_on_submodule
proof_shape: jordan_smul_right: bind-only; escape_witness=none
  consumers: hermitian_jordan_domain_complex, complex_jordan_extension_on_submodule, forward_phase_implementation
proof_shape: jordan_smul_left: bind-only; escape_witness=none
  consumers: complex_jordan_extension, fixed_jordan_domain, complex_jordan_extension_on_submodule, forward_phase_implementation
proof_shape: hermitian_jordan_domain_complex: content; escape_witness=hermitian_jordan_domain_complex
  consumers: complex_jordan_extension, fixed_jordan_domain
proof_shape: complex_jordan_extension: content; escape_witness=complex_jordan_extension
  consumers: positive_inverse_complex_jordan
proof_shape: positive_map_star: bind-only; escape_witness=none
  consumers: fixed_jordan_domain, unital_positive_inverse_classification
proof_shape: fixed_jordan_domain: content; escape_witness=fixed_jordan_domain
  consumers: trace_preserving_of_projectors_fixed, fixed_jordan
proof_shape: fixed_jordan: content; escape_witness=fixed_jordan
  consumers: fixed_powers, fixed_edge, bouquet_fixed_point_rigidity
proof_shape: square_polarization: bind-only; escape_witness=none
  consumers: complex_jordan_extension_on_submodule
proof_shape: complex_jordan_extension_on_submodule: bind-only; escape_witness=none
  consumers: arbitrary_square_extension
proof_shape: arbitrary_square_extension: bind-only; escape_witness=none
  consumers: positive_inverse_projection_alignment
proof_shape: positive_map_monotone: bind-only; escape_witness=none
  consumers: positive_inverse_square_preserving
proof_shape: positive_inverse_square_preserving: content; escape_witness=positive_inverse_square_preserving
  consumers: positive_inverse_projection_alignment, positive_inverse_complex_jordan
proof_shape: positive_inverse_complex_jordan: content; escape_witness=positive_inverse_complex_jordan
  consumers: positive_inverse_projection_alignment, unital_positive_inverse_classification
escape_witness: hermitian_jordan_domain, positive_inverse_square_preserving
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
  declaration statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
  declaration statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import Mathlib.Analysis.Matrix.Order
import D5.S3.Quantum.Foundation.FiniteKrausChannel

noncomputable section
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
namespace D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n m : ℕ}

theorem positive_map_hermitian
    (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hPhi : ∀ X, X.PosSemidef → (Phi X).PosSemidef)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : (Phi H).IsHermitian := by
  let F : Matrix (Fin n) (Fin n) ℂ →ₚ[ℂ] Matrix (Fin m) (Fin m) ℂ :=
    PositiveLinearMap.mk₀ Phi (fun X h => (hPhi X h.posSemidef).nonneg)
  exact hH.isSelfAdjoint.map' F

theorem kadison_finite_weights
    {k : Type*} [Fintype k] (A : k → Matrix (Fin m) (Fin m) ℂ)
    (lambda : k → ℝ) (hA : ∀ i, (A i).PosSemidef) (h1 : ∑ i, A i = 1) :
    (∑ i, (lambda i : ℂ) • A i) * (∑ i, (lambda i : ℂ) • A i) ≤
      ∑ i, ((lambda i : ℂ)^2) • A i := by
  classical
  let K := ∑ i, (lambda i : ℂ) • A i
  have hK : K.IsHermitian := by
    exact isSelfAdjoint_sum _ (fun i _ => (hA i).isHermitian.smul (by simp [IsSelfAdjoint]))
  let B (i : k) := (lambda i : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - K
  have hB (i : k) : (B i).IsHermitian := by
    exact (isHermitian_one.smul (by simp [IsSelfAdjoint])).sub hK
  have hpos : (∑ i, B i * A i * B i).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i hi
    simpa only [(hB i).eq] using (hA i).conjTranspose_mul_mul_same (B i)
  have hterm (i : k) : B i * A i * B i =
      ((lambda i : ℂ)^2) • A i - (lambda i : ℂ) • (A i * K) -
        (lambda i : ℂ) • (K * A i) + K * A i * K := by
    dsimp [B]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    simp only [smul_sub, smul_smul, pow_two, Matrix.mul_assoc, ← Complex.ofReal_mul, Complex.coe_smul]
    abel
  have hid : (∑ i, B i * A i * B i) =
      (∑ i, ((lambda i : ℂ)^2) • A i) - K * K := by
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (∑ i, (lambda i : ℂ) • (A i * K)) = K * K by
      simp only [← smul_mul_assoc, ← Finset.sum_mul]; rfl]
    rw [show (∑ i, (lambda i : ℂ) • (K * A i)) = K * K by
      simp only [← mul_smul_comm, ← Finset.mul_sum]; rfl]
    rw [← Finset.sum_mul, ← Finset.mul_sum, h1, mul_one]
    abel
  exact Matrix.le_iff.mpr (hid ▸ hpos)

private theorem diagonal_single_sum (v : Fin n → ℂ) :
    (∑ i, v i • diagonal (Pi.single i (1 : ℂ))) = diagonal v := by
  classical
  ext j k
  by_cases h : j = k
  · subst k
    simp [Matrix.sum_apply, Matrix.smul_apply, diagonal, Pi.single_apply]
  · simp [Matrix.sum_apply, Matrix.smul_apply, diagonal, Pi.single_apply, h]

theorem kadison_hermitian
    (Phi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (hPhi : ∀ X, X.PosSemidef → (Phi X).PosSemidef) (h1 : Phi 1 = 1)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) :
    Phi H * Phi H ≤ Phi (H * H) := by
  classical
  let U := hH.eigenvectorUnitary
  let J := Unitary.conjStarAlgAut ℂ _ U
  let P (i : Fin n) := J (diagonal (Pi.single i (1 : ℂ)))
  have hP (i : Fin n) : (P i).PosSemidef := by
    have hd : (diagonal (Pi.single i (1 : ℂ))).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun j => by simp [Pi.single_apply]; split_ifs <;> norm_num)
    simpa only [P, J, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hd.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℂ)
  have sumP : ∑ i, P i = 1 := by
    dsimp only [P]
    rw [← map_sum]
    have hs : (∑ i : Fin n, diagonal (Pi.single i (1 : ℂ))) = 1 := by
      simpa using diagonal_single_sum (fun _ : Fin n => (1 : ℂ))
    rw [hs, map_one]
  have sumW (v : Fin n → ℂ) : ∑ i, v i • P i = J (diagonal v) := by
    simp only [P, ← map_smul, ← map_sum]
    rw [diagonal_single_sum]
  have sumH : (∑ i, (hH.eigenvalues i : ℂ) • P i) = H := by
    rw [sumW]
    exact hH.spectral_theorem.symm
  have sumH2 : (∑ i, ((hH.eigenvalues i : ℂ)^2) • P i) = H * H := by
    rw [sumW]
    conv_rhs => rw [hH.spectral_theorem]
    rw [← map_mul]
    simp [diagonal_mul_diagonal, pow_two, J, U]
  have w1 : (∑ i, Phi (P i)) = 1 := by rw [← map_sum, sumP, h1]
  have hw := kadison_finite_weights (fun i => Phi (P i)) hH.eigenvalues
    (fun i => hPhi (P i) (hP i)) w1
  have hm1 : (∑ i, (hH.eigenvalues i : ℂ) • Phi (P i)) = Phi H := by
    simp only [← map_smul, ← map_sum]
    rw [sumH]
  have hm2 : (∑ i, ((hH.eigenvalues i : ℂ)^2) • Phi (P i)) = Phi (H * H) := by
    simp only [← map_smul, ← map_sum]
    rw [sumH2]
  rwa [hm1, hm2] at hw
end


section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem faithful_weighted_trace_zero {S Z : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hZ : Z.PosSemidef) (hz : (S * Z).trace = 0) : Z = 0 := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hRR : R * R = S := by simpa [R, pow_two] using CFC.sq_sqrt S
  have hu : IsUnit R := (isUnit_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp (by simpa [pow_two, hRR] using hS.isUnit)
  have hp : (R * Z * R).PosSemidef := by
    simpa [hR.eq] using hZ.conjTranspose_mul_mul_same R
  have ht : (R * Z * R).trace = 0 := by rw [Matrix.trace_mul_cycle, hRR]; exact hz
  have h0 := hp.trace_eq_zero_iff.mp ht
  have h0' : R * (Z * R) = R * 0 := by simpa [Matrix.mul_assoc] using h0
  have h0'' : Z * R = 0 * R := by simpa using hu.mul_left_cancel h0'
  exact hu.mul_right_cancel h0''

private theorem kadison_equality_of_weighted_trace_zero
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S Y : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef) (hY : Y.IsHermitian)
    (htr : (S * (E (Y * Y) - E Y * E Y)).trace = 0) :
    E (Y * Y) = E Y * E Y := by
  have hp := Matrix.le_iff.mp (kadison_hermitian E hE h1 hY)
  exact sub_eq_zero.mp (faithful_weighted_trace_zero hS hp htr)

private theorem fixed_hermitian_square
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S Y : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ A, (S * E A).trace = (S * A).trace)
    (hY : Y.IsHermitian) (hfix : E Y = Y) : E (Y * Y) = Y * Y := by
  have ht : (S * (E (Y * Y) - E Y * E Y)).trace = 0 := by
    rw [hfix, mul_sub, trace_sub, hstate, sub_self]
  simpa [hfix] using kadison_equality_of_weighted_trace_zero E hE h1 hS hY ht
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def jordan (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A * B + B * A

private theorem jordan_hermitian {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (jordan A B).IsHermitian := by
  change (A * B + B * A)ᴴ = A * B + B * A
  simp only [conjTranspose_add, conjTranspose_mul, hA.eq, hB.eq, add_comm]

private theorem quadratic_psd_linear_zero {C D : Matrix (Fin n) (Fin n) ℂ} (hC : C.IsHermitian)
    (hp : ∀ t : ℝ, ((t : ℂ) • C + ((t : ℂ)^2) • D).PosSemidef) : C = 0 := by
  classical
  have hq (v : Fin n → ℂ) : (star v ⬝ᵥ C *ᵥ v).re = 0 := by
    have hd := discrim_le_zero (a := (star v ⬝ᵥ D *ᵥ v).re)
      (b := (star v ⬝ᵥ C *ᵥ v).re) (c := (0 : ℝ)) (fun t => by
        have h := (hp t).re_dotProduct_nonneg v
        simpa [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
          Complex.mul_re, pow_two, mul_assoc, mul_comm, mul_left_comm, add_comm] using h)
    simp only [discrim, mul_zero, sub_zero] at hd
    nlinarith [sq_nonneg (star v ⬝ᵥ C *ᵥ v).re]
  apply hC.eigenvalues_eq_zero_iff.mp
  funext i
  rw [hC.eigenvalues_eq]
  exact hq _

theorem hermitian_jordan_domain
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {H Y : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hY : Y.IsHermitian)
    (heq : E (H * H) = E H * E H) :
    E (jordan H Y) = jordan (E H) (E Y) := by
  let C := E (jordan H Y) - jordan (E H) (E Y)
  let D := E (Y * Y) - E Y * E Y
  have hC : C.IsHermitian :=
    (positive_map_hermitian E hE (jordan_hermitian hH hY)).sub
      (jordan_hermitian (positive_map_hermitian E hE hH) (positive_map_hermitian E hE hY))
  have hpoly (t : ℝ) :
      E ((H + (t : ℂ) • Y) * (H + (t : ℂ) • Y)) -
        E (H + (t : ℂ) • Y) * E (H + (t : ℂ) • Y) =
        (t : ℂ) • C + ((t : ℂ)^2) • D := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, map_add, map_smul, heq]
    dsimp [C, D, jordan]
    simp only [map_add, smul_add, smul_sub, pow_two]
    simp only [smul_smul, ← Complex.ofReal_mul, Complex.coe_smul]
    abel
  have hp (t : ℝ) := Matrix.le_iff.mp (kadison_hermitian E hE h1
    (hH.add (hY.smul (show IsSelfAdjoint (t : ℂ) from by simp [IsSelfAdjoint]))))
  have hz := quadratic_psd_linear_zero hC (fun t => hpoly t ▸ hp t)
  exact sub_eq_zero.mp hz
end

section
open Matrix
open scoped MatrixOrder ComplexOrder ComplexStarModule Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem jordan_add_right (A B C : Matrix (Fin n) (Fin n) ℂ) :
    jordan A (B + C) = jordan A B + jordan A C := by simp [jordan, mul_add, add_mul]; abel
private theorem jordan_add_left (A B C : Matrix (Fin n) (Fin n) ℂ) :
    jordan (A + B) C = jordan A C + jordan B C := by simp [jordan, mul_add, add_mul]; abel
theorem jordan_smul_right (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    jordan A (c • B) = c • jordan A B := by simp [jordan, mul_smul_comm, smul_mul_assoc, smul_add]
theorem jordan_smul_left (c : ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    jordan (c • A) B = c • jordan A B := by simp [jordan, mul_smul_comm, smul_mul_assoc, smul_add]

def JordanMD (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ B, E (jordan A B) = jordan (E A) (E B)

private theorem hermitian_jordan_domain_complex
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (heq : E (H * H) = E H * E H) : JordanMD E H := by
  intro Y
  have hr := hermitian_jordan_domain E hE h1 hH (ℜ Y).property heq
  have hi := hermitian_jordan_domain E hE h1 hH (ℑ Y).property heq
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart Y]
  conv_rhs => arg 2; rw [← realPart_add_I_smul_imaginaryPart Y]
  simp only [jordan_add_right, jordan_smul_right, map_add, map_smul, hr, hi]

private theorem complex_jordan_extension
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    (hsquare : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → E (H * H) = E H * E H)
    (A B : Matrix (Fin n) (Fin n) ℂ) : E (jordan A B) = jordan (E A) (E B) := by
  have hr := hermitian_jordan_domain_complex E hE h1 (ℜ A).property (hsquare _ (ℜ A).property) B
  have hi := hermitian_jordan_domain_complex E hE h1 (ℑ A).property (hsquare _ (ℑ A).property) B
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A]
  conv_rhs => arg 1; rw [← realPart_add_I_smul_imaginaryPart A]
  simp only [jordan_add_left, jordan_smul_left, map_add, map_smul, hr, hi]

theorem positive_map_star (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (A : Matrix (Fin n) (Fin n) ℂ) :
    E Aᴴ = (E A)ᴴ := by
  let F : Matrix (Fin n) (Fin n) ℂ →ₚ[ℂ] Matrix (Fin n) (Fin n) ℂ := PositiveLinearMap.mk₀ E (fun X h => (hE h.posSemidef).nonneg)
  exact map_star F A

theorem fixed_jordan_domain
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace) (hfix : E A = A) : JordanMD E A := by
  have hs : E Aᴴ = Aᴴ := by rw [positive_map_star E hE, hfix]
  have hr : E (ℜ A : Matrix (Fin n) (Fin n) ℂ) = (ℜ A : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [realPart_apply_coe, ← Complex.coe_smul, map_smul, map_add,
      Matrix.star_eq_conjTranspose, hfix, hs]
  have hi : E (ℑ A : Matrix (Fin n) (Fin n) ℂ) = (ℑ A : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [imaginaryPart_apply_coe, ← Complex.coe_smul, map_smul, map_sub,
      Matrix.star_eq_conjTranspose, hfix, hs]
  have hrd := hermitian_jordan_domain_complex E hE h1 (ℜ A).property
    (by rw [fixed_hermitian_square E hE h1 hS hstate (ℜ A).property hr, hr])
  have hid := hermitian_jordan_domain_complex E hE h1 (ℑ A).property
    (by rw [fixed_hermitian_square E hE h1 hS hstate (ℑ A).property hi, hi])
  intro B
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A]
  conv_rhs => arg 1; rw [← realPart_add_I_smul_imaginaryPart A]
  simp only [jordan_add_left, jordan_smul_left, map_add, map_smul, hrd B, hid B]

theorem fixed_jordan
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) (h1 : E 1 = 1)
    {S A B : Matrix (Fin n) (Fin n) ℂ} (hS : S.PosDef)
    (hstate : ∀ Y, (S * E Y).trace = (S * Y).trace)
    (hA : E A = A) (hB : E B = B) : E (jordan A B) = jordan A B := by
  rw [fixed_jordan_domain E hE h1 hS hstate hA B, hA, hB]
end

section
open Matrix
open scoped MatrixOrder ComplexOrder ComplexStarModule Matrix.Norms.L2Operator
variable {n : ℕ}


private theorem square_polarization
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : E (A * A) = E A * E A) (hB : E (B * B) = E B * E B)
    (hsum : E ((A + B) * (A + B)) = E (A + B) * E (A + B)) :
    E (jordan A B) = jordan (E A) (E B) := by
  simp only [add_mul, mul_add, map_add, hA, hB] at hsum
  dsimp [jordan]
  rw [map_add]
  have h := congrArg (fun Z => Z - E A * E A - E B * E B) hsum
  convert h using 1 <;> abel

private theorem complex_jordan_extension_on_submodule
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (D : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hstar : ∀ A ∈ D, Aᴴ ∈ D)
    (hsquare : ∀ A ∈ D, A.IsHermitian → E (A * A) = E A * E A)
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ D) (hB : B ∈ D) :
    E (jordan A B) = jordan (E A) (E B) := by
  have hr (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ D) : (ℜ Y : Matrix (Fin n) (Fin n) ℂ) ∈ D := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact D.smul_mem _ (D.add_mem hY (hstar Y hY))
  have hi (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ D) : (ℑ Y : Matrix (Fin n) (Fin n) ℂ) ∈ D := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact D.smul_mem _ (D.smul_mem _ (D.sub_mem hY (hstar Y hY)))
  have hj {H K : Matrix (Fin n) (Fin n) ℂ} (hH : H ∈ D) (hK : K ∈ D)
      (hh : H.IsHermitian) (hk : K.IsHermitian) :
      E (jordan H K) = jordan (E H) (E K) :=
    square_polarization E (hsquare H hH hh) (hsquare K hK hk)
      (hsquare (H+K) (D.add_mem hH hK) (hh.add hk))
  have hrr := hj (hr A hA) (hr B hB) (ℜ A).property (ℜ B).property
  have hri := hj (hr A hA) (hi B hB) (ℜ A).property (ℑ B).property
  have hir := hj (hi A hA) (hr B hB) (ℑ A).property (ℜ B).property
  have hii := hj (hi A hA) (hi B hB) (ℑ A).property (ℑ B).property
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart A, ← realPart_add_I_smul_imaginaryPart B]
  conv_rhs => arg 1; rw [← realPart_add_I_smul_imaginaryPart A]
  conv_rhs => arg 2; rw [← realPart_add_I_smul_imaginaryPart B]
  simp only [jordan_add_left, jordan_add_right, jordan_smul_left, jordan_smul_right,
    map_add, map_smul, hrr, hri, hir, hii]

theorem arbitrary_square_extension
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (D : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (hstar : ∀ A ∈ D, Aᴴ ∈ D)
    (hsquare : ∀ A ∈ D, A.IsHermitian → E (A * A) = E A * E A)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ D) : E (A * A) = E A * E A := by
  have h := complex_jordan_extension_on_submodule E D hstar hsquare hA hA
  simp only [jordan, ← two_smul ℂ, map_smul] at h
  exact (smul_right_inj (by norm_num : (2 : ℂ) ≠ 0)).mp h
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem positive_map_monotone (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hE : IsPositive E) : Monotone E := by
  intro A B h
  apply Matrix.le_iff.mpr
  rw [← map_sub]
  exact hE (Matrix.le_iff.mp h)

theorem positive_inverse_square_preserving
    (Phi Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hPhi : IsPositive Phi) (hPsi : IsPositive Psi)
    (hPhi1 : Phi 1 = 1) (hPsi1 : Psi 1 = 1)
    (hcomp : Psi.comp Phi = LinearMap.id)
    {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) : Phi (H * H) = Phi H * Phi H := by
  have hleft (Y : Matrix (Fin n) (Fin n) ℂ) : Psi (Phi Y) = Y := LinearMap.congr_fun hcomp Y
  have hinj : Function.Injective Phi := Function.LeftInverse.injective hleft
  have hsurj : Function.Surjective Phi := LinearMap.surjective_of_injective hinj
  have hright (Y : Matrix (Fin n) (Fin n) ℂ) : Phi (Psi Y) = Y := by
    obtain ⟨Z, rfl⟩ := hsurj Y
    rw [hleft]
  have hle := positive_map_monotone Psi hPsi (kadison_hermitian Phi hPhi hPhi1 hH)
  rw [hleft] at hle
  have hge := kadison_hermitian Psi hPsi hPsi1 (positive_map_hermitian Phi hPhi hH)
  rw [hleft] at hge
  have heq := le_antisymm hle hge
  have h := congrArg Phi heq
  rw [hright] at h
  exact h.symm

theorem positive_inverse_complex_jordan
    (Phi Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hPhi : IsPositive Phi) (hPsi : IsPositive Psi)
    (hPhi1 : Phi 1 = 1) (hPsi1 : Psi 1 = 1)
    (hcomp : Psi.comp Phi = LinearMap.id) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Phi (jordan A B) = jordan (Phi A) (Phi B) := by
  exact complex_jordan_extension Phi hPhi hPhi1
    (fun _ hH => positive_inverse_square_preserving Phi Psi hPhi hPsi hPhi1 hPsi1 hcomp hH) A B
end

end D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain
