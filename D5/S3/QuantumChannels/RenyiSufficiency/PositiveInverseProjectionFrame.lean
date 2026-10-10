/- GID: D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Orthogonal projection families admit a unitary frame. -/

/-
proof_shape: projection_jordan_zero: bind-only; escape_witness=none
  consumers: positive_inverse_projection_alignment
proof_shape: nonzero_projection_vector: content; escape_witness=nonzero_projection_vector
  consumers: orthogonal_projection_frame
proof_shape: orthogonal_projection_frame: content; escape_witness=orthogonal_projection_frame
  consumers: positive_inverse_projection_alignment
proof_shape: positive_inverse_projection_alignment: content; escape_witness=positive_inverse_projection_alignment
  consumers: unital_positive_inverse_classification
escape_witness: orthogonal_projection_frame
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
  declaration statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain

noncomputable section
open D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
namespace D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseProjectionFrame

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {n : ℕ}

private theorem projection_jordan_zero {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P * P = P)
    (hj : jordan P Q = 0) : P * Q = 0 := by
  letI : IsAddTorsionFree (Matrix (Fin n) (Fin n) ℂ) := by
    constructor
    intro k hk A B hAB
    funext i j
    exact IsAddTorsionFree.nsmul_right_injective hk (congrFun (congrFun hAB i) j)
  apply IsIdempotentElem.mul_eq_zero_of_anticommute (a := P) (b := Q) hP
  simpa only [jordan] using hj

private theorem nonzero_projection_vector {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (h0 : P ≠ 0) :
    ∃ v : Fin n → ℂ, star v ⬝ᵥ v = 1 ∧ P *ᵥ v = v := by
  let J := Unitary.conjStarAlgAut ℂ _ hP.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => (hP.eigenvalues i : ℂ)
  have hPJ : P = J (diagonal d) := hP.spectral_theorem
  have hex : ∃ k, hP.eigenvalues k ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply h0
    rw [hPJ]
    have hd : diagonal d = 0 := by ext i j; simp [diagonal_apply, d, hn]
    rw [hd, map_zero]
  obtain ⟨k, hk⟩ := hex
  have hi : diagonal d * diagonal d = diagonal d := by
    apply J.injective
    rw [map_mul]
    change J (diagonal d) * J (diagonal d) = J (diagonal d)
    rw [← hPJ]
    exact hPP
  have hie := congrFun (congrFun hi k) k
  simp only [diagonal_mul_diagonal, diagonal_apply_eq, d, ← Complex.ofReal_mul] at hie
  have hr : hP.eigenvalues k * hP.eigenvalues k = hP.eigenvalues k := Complex.ofReal_injective hie
  have hk1 : hP.eigenvalues k = 1 :=
    (eq_zero_or_one_of_sq_eq_self (by simpa only [pow_two] using hr)).resolve_left hk
  refine ⟨⇑(hP.eigenvectorBasis k), ?_, ?_⟩
  · rw [dotProduct_comm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, ite_true] using
      (orthonormal_iff_ite.mp hP.eigenvectorBasis.orthonormal k k)
  · simpa only [hk1, one_smul] using hP.mulVec_eigenvectorBasis k

theorem orthogonal_projection_frame
    (P : Fin n → Matrix (Fin n) (Fin n) ℂ) (hherm : ∀ i, (P i).IsHermitian)
    (hnonzero : ∀ i, P i ≠ 0) (hproj : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ,
      ∀ i, P i = (U : Matrix (Fin n) (Fin n) ℂ) * single i i 1 * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  choose v hvnorm hvfix using fun i => nonzero_projection_vector (hherm i) (hproj i) (hnonzero i)
  have hkill (i j : Fin n) (hij : i ≠ j) : P i *ᵥ v j = 0 := by
    rw [← hvfix j, mulVec_mulVec, horth i j hij, zero_mulVec]
  have hon (i j : Fin n) : star (v i) ⬝ᵥ v j = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j; simpa using hvnorm i
    · rw [if_neg hij]
      calc
        _ = star (P i *ᵥ v i) ⬝ᵥ v j := by rw [hvfix]
        _ = star (v i) ⬝ᵥ (P i *ᵥ v j) := by rw [star_mulVec, (hherm i).eq, dotProduct_mulVec]
        _ = 0 := by rw [hkill i j hij, dotProduct_zero]
  let V : Matrix (Fin n) (Fin n) ℂ := fun i j => v j i
  have hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    change (star (v i) ⬝ᵥ v j) = _
    simpa only [Matrix.one_apply] using hon i j
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨V, hV⟩
  refine ⟨U, fun i => ?_⟩
  have hPU : P i * V = V * single i i 1 := by
    ext a b
    change (P i *ᵥ v b) a = _
    by_cases hib : i = b
    · subst b
      rw [hvfix]
      simp only [Matrix.mul_apply]
      simp [V, single, Matrix.of_apply]
    · rw [hkill i b hib]
      simp only [Matrix.mul_apply]
      simp [V, single, Matrix.of_apply, hib, Ne.symm hib]
  have hu : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
  change P i = V * single i i 1 * Vᴴ
  rw [← hPU, mul_assoc, hu, mul_one]

theorem positive_inverse_projection_alignment
    (Phi Psi : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) (hPhi : IsPositive Phi) (hPsi : IsPositive Psi)
    (hPhi1 : Phi 1 = 1) (hPsi1 : Psi 1 = 1)
    (hcomp : Psi.comp Phi = LinearMap.id) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ,
      ∀ i, Phi (single i i 1) = (U : Matrix (Fin n) (Fin n) ℂ) * single i i 1 * (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  have hj := positive_inverse_complex_jordan Phi Psi hPhi hPsi hPhi1 hPsi1 hcomp
  have hs (A : Matrix (Fin n) (Fin n) ℂ) : Phi (A * A) = Phi A * Phi A :=
    arbitrary_square_extension Phi ⊤ (fun _ _ => Submodule.mem_top)
      (fun H _ hH => positive_inverse_square_preserving Phi Psi hPhi hPsi hPhi1 hPsi1 hcomp hH)
      (Submodule.mem_top : A ∈ (⊤ : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)))
  have hp (i : Fin n) : single i i (1 : ℂ) * single i i 1 = single i i 1 := by simp
  have hpp (i : Fin n) : Phi (single i i 1) * Phi (single i i 1) = Phi (single i i 1) := by
    rw [← hs, hp]
  apply orthogonal_projection_frame (fun i => Phi (single i i 1))
  · intro i
    exact positive_map_hermitian Phi hPhi (by simp [IsHermitian])
  · intro i hz
    have he := LinearMap.congr_fun hcomp (single i i (1 : ℂ))
    change Psi (Phi (single i i 1)) = single i i 1 at he
    rw [hz, map_zero] at he
    have hc := congrFun (congrFun he i) i
    simpa using hc
  · exact hpp
  · intro i j hij
    apply projection_jordan_zero (hpp i)
    rw [← hj]
    have he : jordan (single i i (1 : ℂ)) (single j j 1) = 0 := by
      simp [jordan, Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
    rw [he, map_zero]
end

end D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseProjectionFrame
