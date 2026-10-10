/- GID: D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result; premises=D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy.bouquet_twoTriangle_values
   digest: Two triangle gains obstruct positive interconversion. -/

/-
proof_shape: unitalize_apply: bind-only; escape_witness=none
  consumers: unitalize_state, unitalize_transport
proof_shape: sandwich_positive: bind-only; escape_witness=none
  consumers: unitalize_positive
proof_shape: unitalize_positive: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: unitalize_state: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: unitalize_transport: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: sigmaHalf_hermitian: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: sigmaInvHalf_hermitian: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: sigmaHalf_square: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, bouquet_not_interconvertible
proof_shape: sigmaHalf_inverse: bind-only; escape_witness=none
  consumers: sigmaInvHalf_inverse, ptp_unitalized_inverse, sigmaHalf_likelihood_cancel, bouquet_not_interconvertible
proof_shape: sigmaInvHalf_inverse: bind-only; escape_witness=none
  consumers: ptp_unitalized_inverse, sigmaHalf_likelihood_cancel, bouquet_not_interconvertible
proof_shape: ptp_unitalized_inverse: content; escape_witness=ptp_unitalized_inverse
  consumers: bouquet_not_interconvertible
proof_shape: transpose_state_invariance: bind-only; escape_witness=none
  consumers: transpose_inner_state_matrix
proof_shape: inner_state_matrix: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: transpose_inner_state_matrix: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: sigma_weights_injective: bind-only; escape_witness=none
  consumers: sigma_unitary_diagonal
proof_shape: sigma_unitary_diagonal: bind-only; escape_witness=none
  consumers: two_triangle_holonomy_obstruction, bouquet_not_interconvertible
proof_shape: diagonal_cycleGain: bind-only; escape_witness=none
  consumers: diagonal_twoTriangleGain
proof_shape: diagonal_twoTriangleGain: bind-only; escape_witness=none
  consumers: two_triangle_holonomy_obstruction
proof_shape: bouquet_twoTriangle_values: bind-only; escape_witness=none
  consumers: two_triangle_holonomy_obstruction
proof_shape: two_triangle_holonomy_obstruction: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: commuting_sandwich_rearrange: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: sigmaHalf_likelihood_cancel: bind-only; escape_witness=none
  consumers: sigmaHalf_transpose_likelihood_cancel, bouquet_not_interconvertible
proof_shape: sigmaHalf_transpose: bind-only; escape_witness=none
  consumers: sigmaHalf_transpose_likelihood_cancel
proof_shape: sigmaHalf_transpose_likelihood_cancel: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: sigmaHalf_diagonal_commute: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: sigmaHalf_diagonal_star_commute: bind-only; escape_witness=none
  consumers: bouquet_not_interconvertible
proof_shape: bouquet_not_interconvertible: content; escape_witness=bouquet_not_interconvertible
  consumers: result
escape_witness: bouquet_not_interconvertible
admission_basis: escape-witness
The non-normalization step constructs the orthogonal projection frame and coherently phased unitary classifying the positive inverse pair; the explicit triangle gains then give a contradiction.
Direct frozen dependencies:
  D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unitalized
  D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound.unitalized_one
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
  declaration statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
  declaration statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseClassification
import D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound

noncomputable section
open D5.S3.QuantumChannels.RenyiSufficiency.LikelihoodSpectrum
open D5.S3.QuantumChannels.RenyiSufficiency.BouquetFixedPoint
open D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseClassification
open D5.S3.Quantum.QuantumChannels.ConditionalTwoPositiveSpectralBound (unitalized unitalized_one)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
namespace D5.S3.QuantumChannels.RenyiSufficiency.BouquetHolonomy

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem unitalize_apply (K L : Matrix (Fin n) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    unitalized T K L 1 Y = L * T (K * Y * K) * L := by
  simp only [unitalized, inv_one, one_smul, LinearMap.comp_apply,
    LinearMap.mulLeftRight_apply]

private theorem sandwich_positive {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : IsPositive (LinearMap.mulLeftRight ℂ (A, A)) := by
  intro Y hY
  change (A * Y * A).PosSemidef
  simpa only [hA.eq] using hY.conjTranspose_mul_mul_same A

private theorem unitalize_positive {K L : Matrix (Fin n) (Fin n) ℂ} (hK : K.IsHermitian) (hL : L.IsHermitian)
    {T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : IsPositive T) : IsPositive (unitalized T K L 1) := by
  intro Y hY
  simpa only [unitalized, inv_one, one_smul, LinearMap.comp_apply,
    LinearMap.mulLeftRight_apply] using sandwich_positive hL (hT (sandwich_positive hK hY))

private theorem unitalize_state {K L S : Matrix (Fin n) (Fin n) ℂ} (hKK : K * K = S) (hLK : L * K = 1)
    (hKL : K * L = 1) {T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ}
    (htrace : ∀ Y, (T Y).trace = Y.trace) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (S * unitalized T K L 1 Y).trace = (S * Y).trace := by
  have hLSL : L * S * L = 1 := by
    rw [← hKK]
    simp only [← mul_assoc, hLK, one_mul, hKL]
  rw [unitalize_apply]
  calc
    _ = ((S * L) * T (K * Y * K) * L).trace := by simp only [mul_assoc]
    _ = ((L * S * L) * T (K * Y * K)).trace := by rw [trace_mul_cycle]; simp only [mul_assoc]
    _ = (K * Y * K).trace := by rw [hLSL, one_mul, htrace]
    _ = (S * Y).trace := by rw [trace_mul_cycle, hKK]

private theorem unitalize_transport {K L A B : Matrix (Fin n) (Fin n) ℂ} (hKL : K * L = 1)
    (hLK : L * K = 1) {T : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ} (hT : T A = B) :
    unitalized T K L 1 (L * A * L) = L * B * L := by
  rw [unitalize_apply]
  have hc : K * (L * A * L) * K = A := by
    simp only [← mul_assoc, hKL, one_mul]
    simp only [mul_assoc, hLK, mul_one]
  rw [hc, hT]


private theorem sigmaHalf_hermitian : (matrixPower sigma (1/2)).IsHermitian := by
  simp only [sigma, matrixPower_diagonal]
  apply isHermitian_diagonal_of_self_adjoint
  ext i
  simp

private theorem sigmaInvHalf_hermitian : (matrixPower sigma (-1/2)).IsHermitian := by
  simp only [sigma, matrixPower_diagonal]
  apply isHermitian_diagonal_of_self_adjoint
  ext i
  simp

private theorem sigmaHalf_square : (matrixPower sigma (1/2)) * (matrixPower sigma (1/2)) = sigma := by
  simp only [sigma, matrixPower_diagonal, diagonal_mul_diagonal, ← Complex.ofReal_mul]
  congr 1
  funext i
  rw [← Real.rpow_add (by positivity)]
  norm_num

private theorem sigmaHalf_inverse : (matrixPower sigma (1/2)) * (matrixPower sigma (-1/2)) = 1 := by
  simp only [sigma, matrixPower_diagonal,
    diagonal_mul_diagonal, ← Complex.ofReal_mul]
  have he : (fun i : Fin 5 =>
      (((i.val+1 : ℕ) : ℝ)/15) ^ (1/2 : ℝ) *
      (((i.val+1 : ℕ) : ℝ)/15) ^ (-1/2 : ℝ)) = fun _ => 1 := by
    funext i
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hv (i : Fin 5) := congrFun he i
  simpa only [hv, Complex.ofReal_one, diagonal_one]

private theorem sigmaInvHalf_inverse : (matrixPower sigma (-1/2)) * (matrixPower sigma (1/2)) = 1 := by
  have hc : (matrixPower sigma (-1/2)) * (matrixPower sigma (1/2)) = (matrixPower sigma (1/2)) * (matrixPower sigma (-1/2)) := by
    simp only [sigma, matrixPower_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hc, sigmaHalf_inverse]

private theorem ptp_unitalized_inverse
    (T R : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hT : IsPTP T) (hR : IsPTP R)
    (hTs : T sigma = sigma) (hRs : R sigma = sigma)
    (hTr : T (rho false (1/1000)) = rho true (1/1000))
    (hRr : R (rho true (1/1000)) = rho false (1/1000)) :
    (unitalized R (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1).comp (unitalized T (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1) =
      LinearMap.id := by
  let Phi := unitalized T (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1
  let Psi := unitalized R (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1
  have hp : IsPositive Phi := unitalize_positive sigmaHalf_hermitian sigmaInvHalf_hermitian hT.1
  have hq : IsPositive Psi := unitalize_positive sigmaHalf_hermitian sigmaInvHalf_hermitian hR.1
  have hp1 : Phi 1 = 1 := by
    exact unitalized_one T (matrixPower sigma (1/2)) (matrixPower sigma (-1/2))
      sigma 1 (by norm_num) sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse
      (by simpa only [one_smul] using hTs)
  have hq1 : Psi 1 = 1 := by
    exact unitalized_one R (matrixPower sigma (1/2)) (matrixPower sigma (-1/2))
      sigma 1 (by norm_num) sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse
      (by simpa only [one_smul] using hRs)
  have hps : ∀ Y, (sigma * Phi Y).trace = (sigma * Y).trace :=
    unitalize_state sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse hT.2
  have hqs : ∀ Y, (sigma * Psi Y).trace = (sigma * Y).trace :=
    unitalize_state sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse hR.2
  have hpr : Phi (likelihood false) = likelihood true :=
    unitalize_transport sigmaHalf_inverse sigmaInvHalf_inverse hTr
  have hqr : Psi (likelihood true) = likelihood false :=
    unitalize_transport sigmaHalf_inverse sigmaInvHalf_inverse hRr
  apply bouquet_fixed_point_rigidity
  · intro Y hY; exact hq (hp hY)
  · change Psi (Phi 1) = 1
    rw [hp1, hq1]
  · intro Y
    change (sigma * Psi (Phi Y)).trace = (sigma * Y).trace
    rw [hqs, hps]
  · change Psi (Phi (likelihood false)) = likelihood false
    rw [hpr, hqr]
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem transpose_state_invariance (U : Matrix (Fin 5) (Fin 5) ℂ)
    (h : (Uᴴ * sigma * U).transpose = sigma) : Uᴴ * sigma * U = sigma := by
  have ht := congrArg Matrix.transpose h
  simpa only [transpose_transpose, sigma, diagonal_transpose] using ht

private theorem inner_state_matrix (U : Matrix.unitaryGroup (Fin 5) ℂ)
    (hstate : ∀ Y : Matrix (Fin 5) (Fin 5) ℂ,
      (sigma * ((U : Matrix (Fin 5) (Fin 5) ℂ) * Y * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ)).trace = (sigma * Y).trace) :
    (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ * sigma * U = sigma := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  calc
    _ = (sigma * ((U : Matrix (Fin 5) (Fin 5) ℂ) * Y * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ)).trace := by
      simp only [mul_assoc]
      rw [trace_mul_comm (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ]
      simp only [mul_assoc]
    _ = _ := hstate Y

private theorem transpose_inner_state_matrix (U : Matrix.unitaryGroup (Fin 5) ℂ)
    (hstate : ∀ Y : Matrix (Fin 5) (Fin 5) ℂ,
      (sigma * ((U : Matrix (Fin 5) (Fin 5) ℂ) * Y.transpose * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ)).trace = (sigma * Y).trace) :
    (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ * sigma * U = sigma := by
  apply transpose_state_invariance
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  calc
    _ = (((U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ * sigma * U) * Y.transpose).trace := by
      rw [← trace_transpose_mul _ Y.transpose, transpose_transpose]
    _ = (sigma * ((U : Matrix (Fin 5) (Fin 5) ℂ) * Y.transpose * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ)).trace := by
      simp only [mul_assoc]
      rw [trace_mul_comm (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ]
      simp only [mul_assoc]
    _ = _ := hstate Y

private theorem sigma_weights_injective :
    Function.Injective (fun i : Fin 5 => ((((i.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ)) := by
  intro i j h
  have hr := Complex.ofReal_injective h
  have he : (i.val : ℝ) = (j.val : ℝ) := by push_cast at hr; linarith
  exact Fin.ext (by exact_mod_cast he)

private theorem sigma_unitary_diagonal (U : Matrix.unitaryGroup (Fin 5) ℂ)
    (hS : (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ * sigma * U = sigma) :
    (U : Matrix (Fin 5) (Fin 5) ℂ) = diagonal (fun i => (U : Matrix (Fin 5) (Fin 5) ℂ) i i) := by
  have hu : (U : Matrix (Fin 5) (Fin 5) ℂ) * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ = 1 := Unitary.mul_star_self_of_mem U.prop
  have hc : sigma * (U : Matrix (Fin 5) (Fin 5) ℂ) = (U : Matrix (Fin 5) (Fin 5) ℂ) * sigma := by
    have hh := congrArg (fun A : Matrix (Fin 5) (Fin 5) ℂ => (U : Matrix (Fin 5) (Fin 5) ℂ) * A) hS
    simpa only [← mul_assoc, hu, one_mul] using hh
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrFun (congrFun hc i) j
    simp only [sigma, diagonal_mul, mul_diagonal] at he
    have hn := (fun he => hij (sigma_weights_injective he))
    have hz : (U : Matrix (Fin 5) (Fin 5) ℂ) i j = 0 := by
      have hp : (((((i.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ) -
          ((((j.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ)) * (U : Matrix (Fin 5) (Fin 5) ℂ) i j = 0 := by
        calc
          _ = (((((i.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ) * (U : Matrix (Fin 5) (Fin 5) ℂ) i j) -
            (U : Matrix (Fin 5) (Fin 5) ℂ) i j * ((((j.val+1 : ℕ) : ℝ)/15 : ℝ) : ℂ) := by ring
          _ = 0 := sub_eq_zero.mpr he
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hn)
    simpa [diagonal_apply, hij] using hz

private def cycleGain (Y : Matrix (Fin 5) (Fin 5) ℂ) (i j k : Fin 5) : ℂ := Y i j * Y j k * Y k i

private def twoTriangleGain (Y : Matrix (Fin 5) (Fin 5) ℂ) : ℂ := cycleGain Y 0 1 2 * cycleGain Y 0 3 4

private theorem diagonal_cycleGain (u : Fin 5 → ℂ) (hu : ∀ i, u i * star (u i) = 1)
    (Y : Matrix (Fin 5) (Fin 5) ℂ) (i j k : Fin 5) :
    cycleGain (diagonal u * Y * (diagonal u)ᴴ) i j k = cycleGain Y i j k := by
  simp only [cycleGain, diagonal_conjTranspose, diagonal_mul, mul_diagonal, Pi.star_apply]
  calc
    _ = (u i * star (u i)) * (u j * star (u j)) * (u k * star (u k)) *
      (Y i j * Y j k * Y k i) := by ring
    _ = _ := by rw [hu, hu, hu]; simp

private theorem diagonal_twoTriangleGain (U : Matrix.unitaryGroup (Fin 5) ℂ)
    (hd : (U : Matrix (Fin 5) (Fin 5) ℂ) = diagonal (fun i => (U : Matrix (Fin 5) (Fin 5) ℂ) i i)) (Y : Matrix (Fin 5) (Fin 5) ℂ) :
    twoTriangleGain ((U : Matrix (Fin 5) (Fin 5) ℂ) * Y * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ) = twoTriangleGain Y := by
  have hu : ∀ i, (U : Matrix (Fin 5) (Fin 5) ℂ) i i * star ((U : Matrix (Fin 5) (Fin 5) ℂ) i i) = 1 := by
    have hh : (U : Matrix (Fin 5) (Fin 5) ℂ) * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ = 1 := Unitary.mul_star_self_of_mem U.prop
    rw [hd, diagonal_conjTranspose, diagonal_mul_diagonal] at hh
    intro i
    have he := congrFun (congrFun hh i) i
    simpa using he
  rw [hd]
  exact congrArg₂ (· * ·) (diagonal_cycleGain _ hu Y 0 1 2)
    (diagonal_cycleGain _ hu Y 0 3 4)

private theorem bouquet_twoTriangle_values :
    twoTriangleGain (rho false (1/1000)) = -(1/5000 : ℂ)^6 ∧
    twoTriangleGain (rho true (1/1000)) = (1/5000 : ℂ)^6 ∧
    twoTriangleGain (rho false (1/1000)).transpose = -(1/5000 : ℂ)^6 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    norm_num [twoTriangleGain, cycleGain, rho, Matrix.transpose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem two_triangle_holonomy_obstruction (U : Matrix.unitaryGroup (Fin 5) ℂ)
    (hS : (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ * sigma * U = sigma) :
    rho true (1/1000) ≠ (U : Matrix (Fin 5) (Fin 5) ℂ) * rho false (1/1000) * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ ∧
    rho true (1/1000) ≠ (U : Matrix (Fin 5) (Fin 5) ℂ) * (rho false (1/1000)).transpose * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ := by
  have hd := sigma_unitary_diagonal U hS
  obtain ⟨hf, ht, hft⟩ := bouquet_twoTriangle_values
  constructor <;> intro he
  · have h := congrArg twoTriangleGain he
    rw [diagonal_twoTriangleGain U hd, hf, ht] at h
    have hr := congrArg Complex.re h
    norm_num at hr
  · have h := congrArg twoTriangleGain he
    rw [diagonal_twoTriangleGain U hd, hft, ht] at h
    have hr := congrArg Complex.re h
    norm_num at hr
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem commuting_sandwich_rearrange (K U V X : Matrix (Fin n) (Fin n) ℂ)
    (hKU : K * U = U * K) (hKV : K * V = V * K) :
    K * (U * X * V) * K = U * (K * X * K) * V := by
  calc
    _ = (K * U) * X * (V * K) := by noncomm_ring
    _ = (U * K) * X * (K * V) := by rw [hKU, ← hKV]
    _ = _ := by noncomm_ring

private theorem sigmaHalf_likelihood_cancel (minus : Bool) :
    (matrixPower sigma (1/2)) * likelihood minus * (matrixPower sigma (1/2)) = rho minus (1/1000) := by
  change (matrixPower sigma (1/2)) * ((matrixPower sigma (-1/2)) * rho minus (1/1000) * (matrixPower sigma (-1/2))) * (matrixPower sigma (1/2)) = _
  simp only [← mul_assoc, sigmaHalf_inverse, one_mul]
  simp only [mul_assoc, sigmaInvHalf_inverse, mul_one]

private theorem sigmaHalf_transpose : (matrixPower sigma (1/2)).transpose = (matrixPower sigma (1/2)) := by
  simp only [sigma, matrixPower_diagonal, diagonal_transpose]

private theorem sigmaHalf_transpose_likelihood_cancel (minus : Bool) :
    (matrixPower sigma (1/2)) * (likelihood minus).transpose * (matrixPower sigma (1/2)) =
      (rho minus (1/1000)).transpose := by
  have h := congrArg Matrix.transpose (sigmaHalf_likelihood_cancel minus)
  simpa only [transpose_mul, sigmaHalf_transpose, mul_assoc] using h

private theorem sigmaHalf_diagonal_commute {U : Matrix (Fin 5) (Fin 5) ℂ}
    (hU : U = diagonal (fun i => U i i)) : (matrixPower sigma (1/2)) * U = U * (matrixPower sigma (1/2)) := by
  rw [hU]
  simp only [sigma, matrixPower_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem sigmaHalf_diagonal_star_commute {U : Matrix (Fin 5) (Fin 5) ℂ}
    (hU : U = diagonal (fun i => U i i)) : (matrixPower sigma (1/2)) * Uᴴ = Uᴴ * (matrixPower sigma (1/2)) := by
  rw [hU, diagonal_conjTranspose]
  simp only [sigma, matrixPower_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem bouquet_not_interconvertible :
    ¬ Interconvertible (rho false (1/1000)) sigma (rho true (1/1000)) sigma := by
  rintro ⟨T, R, hT, hR, hTr, hTs, hRr, hRs⟩
  let Phi := unitalized T (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1
  let Psi := unitalized R (matrixPower sigma (1/2)) (matrixPower sigma (-1/2)) 1
  have hp : IsPositive Phi := unitalize_positive sigmaHalf_hermitian sigmaInvHalf_hermitian hT.1
  have hq : IsPositive Psi := unitalize_positive sigmaHalf_hermitian sigmaInvHalf_hermitian hR.1
  have hp1 : Phi 1 = 1 := by
    exact unitalized_one T (matrixPower sigma (1/2)) (matrixPower sigma (-1/2))
      sigma 1 (by norm_num) sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse
      (by simpa only [one_smul] using hTs)
  have hq1 : Psi 1 = 1 := by
    exact unitalized_one R (matrixPower sigma (1/2)) (matrixPower sigma (-1/2))
      sigma 1 (by norm_num) sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse
      (by simpa only [one_smul] using hRs)
  have hcomp : Psi.comp Phi = LinearMap.id := ptp_unitalized_inverse T R hT hR hTs hRs hTr hRr
  have hstate : ∀ Y, (sigma * Phi Y).trace = (sigma * Y).trace :=
    unitalize_state sigmaHalf_square sigmaInvHalf_inverse sigmaHalf_inverse hT.2
  have hpr : Phi (likelihood false) = likelihood true :=
    unitalize_transport sigmaHalf_inverse sigmaInvHalf_inverse hTr
  obtain ⟨U, hf | ht⟩ := unital_positive_inverse_classification Phi Psi hp hq hp1 hq1 hcomp
  · have hS := inner_state_matrix U (by
      intro Y
      simpa only [hf, Matrix.star_eq_conjTranspose] using hstate Y)
    have hd := sigma_unitary_diagonal U hS
    have hk := sigmaHalf_diagonal_commute hd
    have hks := sigmaHalf_diagonal_star_commute hd
    have he : likelihood true = (U : Matrix (Fin 5) (Fin 5) ℂ) * likelihood false * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ := by
      rw [← hpr, hf, Matrix.star_eq_conjTranspose]
    have hh := congrArg (fun Y : Matrix (Fin 5) (Fin 5) ℂ => (matrixPower sigma (1/2)) * Y * (matrixPower sigma (1/2))) he
    rw [sigmaHalf_likelihood_cancel,
      commuting_sandwich_rearrange _ _ _ _ hk hks, sigmaHalf_likelihood_cancel] at hh
    exact (two_triangle_holonomy_obstruction U hS).1 hh
  · have hS := transpose_inner_state_matrix U (by
      intro Y
      simpa only [ht, Matrix.star_eq_conjTranspose] using hstate Y)
    have hd := sigma_unitary_diagonal U hS
    have hk := sigmaHalf_diagonal_commute hd
    have hks := sigmaHalf_diagonal_star_commute hd
    have he : likelihood true = (U : Matrix (Fin 5) (Fin 5) ℂ) * (likelihood false).transpose * (U : Matrix (Fin 5) (Fin 5) ℂ)ᴴ := by
      rw [← hpr, ht, Matrix.star_eq_conjTranspose]
    have hh := congrArg (fun Y : Matrix (Fin 5) (Fin 5) ℂ => (matrixPower sigma (1/2)) * Y * (matrixPower sigma (1/2))) he
    rw [sigmaHalf_likelihood_cancel,
      commuting_sandwich_rearrange _ _ _ _ hk hks, sigmaHalf_transpose_likelihood_cancel] at hh
    exact (two_triangle_holonomy_obstruction U hS).2 hh
end

end D5.S3.QuantumChannels.RenyiSufficiency.BouquetHolonomy
