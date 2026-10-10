/- GID: D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification
   mirror-E: none(waiver:kernel-checked-proof)
   anchors: []
   utility: none
   digest: Unital positive inverse maps are inner or transpose-inner. -/

/-
proof_shape: jordan_squares: bind-only; escape_witness=none
  consumers: peirce_single_orientation
proof_shape: peirce_two_plane: bind-only; escape_witness=none
  consumers: peirce_single_orientation
proof_shape: peirce_single_orientation: bind-only; escape_witness=none
  consumers: root_orientation_uniform, diagonal_jordan_classification
proof_shape: root_orientation_uniform: bind-only; escape_witness=none
  consumers: forward_phase_implementation
proof_shape: forward_phase_implementation: content; escape_witness=forward_phase_implementation
  consumers: diagonal_jordan_classification
proof_shape: diagonal_jordan_classification: content; escape_witness=diagonal_jordan_classification
  consumers: unital_positive_inverse_classification
proof_shape: unital_positive_inverse_classification: content; escape_witness=unital_positive_inverse_classification
  consumers: bouquet_not_interconvertible
escape_witness: unital_positive_inverse_classification
admission_basis: escape-witness
Direct frozen dependencies:
  D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsPositive
  declaration statement_id: sha256:f17d83cade270607ed26a249661ca93167b5a57d01906f355672261f7aaa0cb6
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14881
-/

import D5.S3.QuantumChannels.RenyiSufficiency.BouquetFixedPoint
import D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseProjectionFrame

noncomputable section
open D5.S3.QuantumChannels.RenyiSufficiency.PositiveMapJordanDomain
open D5.S3.QuantumChannels.RenyiSufficiency.BouquetFixedPoint
open D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseProjectionFrame
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap
namespace D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseClassification

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

private theorem jordan_squares (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B)) (A : Matrix (Fin 5) (Fin 5) ℂ) :
    E (A * A) = E A * E A := by
  have h := hJ A A
  simp only [jordan, ← two_smul ℂ, map_smul] at h
  exact (smul_right_inj (by norm_num : (2 : ℂ) ≠ 0)).mp h

private theorem peirce_two_plane (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B))
    (hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ))) (i j : Fin 5) (hij : i ≠ j) :
    E ((single i j (1 : ℂ))) = E ((single i j (1 : ℂ))) i j • (single i j (1 : ℂ)) + E ((single i j (1 : ℂ))) j i • (single j i (1 : ℂ)) := by
  have he : jordan ((single i i (1 : ℂ))) (jordan ((single j j (1 : ℂ))) ((single i j (1 : ℂ)))) = (single i j (1 : ℂ)) := by
    simp [jordan, mu_mul, hij, Ne.symm hij]
  have hh := congrArg E he
  rw [hJ, hJ, hd, hd] at hh
  rw [show (single i i (1 : ℂ)) = single i i 1 from rfl, show (single j j (1 : ℂ)) = single j j 1 from rfl,
    jordan_projector_edge i j hij] at hh
  exact hh.symm

private theorem peirce_single_orientation (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B))
    (hstar : ∀ A, E Aᴴ = (E A)ᴴ) (hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (i j : Fin 5) (hij : i ≠ j) :
    ∃ c : ℂ, c * star c = 1 ∧
      (E ((single i j (1 : ℂ))) = c • (single i j (1 : ℂ)) ∨ E ((single i j (1 : ℂ))) = c • (single j i (1 : ℂ))) := by
  let a := E ((single i j (1 : ℂ))) i j
  let b := E ((single i j (1 : ℂ))) j i
  have he : E ((single i j (1 : ℂ))) = a • (single i j (1 : ℂ)) + b • (single j i (1 : ℂ)) := peirce_two_plane E hJ hd i j hij
  have hrev : E ((single j i (1 : ℂ))) = star a • (single j i (1 : ℂ)) + star b • (single i j (1 : ℂ)) := by
    have h := hstar ((single i j (1 : ℂ)))
    have hm : ((single i j (1 : ℂ)))ᴴ = (single j i (1 : ℂ)) := by simp
    rw [hm, he] at h
    simpa only [conjTranspose_add, conjTranspose_smul, conjTranspose_single, star_one] using h
  have hzero : a * b = 0 := by
    have hs := jordan_squares E hJ ((single i j (1 : ℂ)))
    have hm : (single i j (1 : ℂ)) * (single i j (1 : ℂ)) = 0 := by simp [mu_mul, hij, Ne.symm hij]
    rw [hm, map_zero, he] at hs
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      mu_mul, if_pos rfl, if_neg hij, if_neg (Ne.symm hij), smul_zero, zero_add, add_zero] at hs
    have hc := congrFun (congrFun hs i) i
    simpa [Matrix.single, hij, Ne.symm hij, mul_comm] using hc.symm
  have hnorm : a * star a + b * star b = 1 := by
    have hj := hJ ((single i j (1 : ℂ))) ((single j i (1 : ℂ)))
    have hm : jordan ((single i j (1 : ℂ))) ((single j i (1 : ℂ))) = (single i i (1 : ℂ)) + (single j j (1 : ℂ)) := by simp [jordan, mu_mul]
    rw [hm, map_add, hd, hd, he, hrev] at hj
    simp only [jordan, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      mu_mul, if_pos rfl, if_neg hij, if_neg (Ne.symm hij), smul_zero, zero_add, add_zero] at hj
    have hc := congrFun (congrFun hj i) i
    simpa [Matrix.single, hij, Ne.symm hij, mul_comm] using hc.symm
  rcases mul_eq_zero.mp hzero with ha | hb
  · refine ⟨b, ?_, Or.inr ?_⟩
    · simpa [ha] using hnorm
    · simpa [ha] using he
  · refine ⟨a, ?_, Or.inl ?_⟩
    · simpa [hb] using hnorm
    · simpa [hb] using he

private theorem root_orientation_uniform (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B))
    (hstar : ∀ A, E Aᴴ = (E A)ᴴ) (hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (hinj : Function.Injective E) (c : ℂ) (hc : c * star c = 1)
    (h01 : E ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) = c • (single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) (k : Fin 5) (hk : k ≠ 0) :
    ∃ a : ℂ, a * star a = 1 ∧ E ((single (0 : Fin 5) k (1 : ℂ))) = a • (single (0 : Fin 5) k (1 : ℂ)) := by
  by_cases hk1 : k = 1
  · subst k; exact ⟨c, hc, h01⟩
  obtain ⟨a, ha, hf | hr⟩ := peirce_single_orientation E hJ hstar hd 0 k (Ne.symm hk)
  · exact ⟨a, ha, hf⟩
  · have hs : E ((single k (0 : Fin 5) (1 : ℂ))) = star a • (single (0 : Fin 5) k (1 : ℂ)) := by
      have ht := hstar ((single (0 : Fin 5) k (1 : ℂ)))
      simp only [conjTranspose_single, star_one] at ht
      rw [hr] at ht
      simpa only [conjTranspose_smul, conjTranspose_single, star_one] using ht
    have hj := hJ ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) ((single k (0 : Fin 5) (1 : ℂ)))
    have he : jordan ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) ((single k (0 : Fin 5) (1 : ℂ))) = (single k (1 : Fin 5) (1 : ℂ)) := by
      simp [jordan, mu_mul, hk1, Ne.symm hk1]
    have hz : jordan (c • (single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) (star a • (single (0 : Fin 5) k (1 : ℂ))) = 0 := by
      simp [jordan_smul_left, jordan_smul_right, jordan, mu_mul, hk, Ne.symm hk]
    rw [he, h01, hs, hz] at hj
    have hem : (single k (1 : Fin 5) (1 : ℂ)) = 0 := hinj (by simpa using hj)
    have hh := congrFun (congrFun hem k) 1
    simpa [Matrix.single] using hh
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

private theorem forward_phase_implementation (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B))
    (hstar : ∀ A, E Aᴴ = (E A)ᴴ) (hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (hinj : Function.Injective E) (c : ℂ) (hc : c * star c = 1)
    (h01 : E ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) = c • (single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) :
    ∃ D : Matrix.unitaryGroup (Fin 5) ℂ,
      ∀ Y, E Y = (D : Matrix (Fin 5) (Fin 5) ℂ) * Y * (D : Matrix (Fin 5) (Fin 5) ℂ)ᴴ := by
  have hex (k : Fin 5) : ∃ a : ℂ, a * star a = 1 ∧ E ((single (0 : Fin 5) k (1 : ℂ))) = a • (single (0 : Fin 5) k (1 : ℂ)) := by
    by_cases hk : k = 0
    · subst k
      exact ⟨1, by simp, by simpa using hd 0⟩
    · exact root_orientation_uniform E hJ hstar hd hinj c hc h01 k hk
  choose a hanorm hrow using hex
  have ha0 : a 0 = 1 := by
    have hh := hrow 0
    rw [hd] at hh
    have hh' := congrFun (congrFun hh 0) 0
    simpa [Matrix.single] using hh'.symm
  have hcol (i : Fin 5) : E ((single i (0 : Fin 5) (1 : ℂ))) = star (a i) • (single i (0 : Fin 5) (1 : ℂ)) := by
    have hh := hstar ((single (0 : Fin 5) i (1 : ℂ)))
    rw [show ((single (0 : Fin 5) i (1 : ℂ)))ᴴ = (single i (0 : Fin 5) (1 : ℂ)) by simp, hrow] at hh
    simpa only [conjTranspose_smul, conjTranspose_single, star_one] using hh
  have hunit (i : Fin 5) : star (a i) * a i = 1 := by rw [mul_comm]; exact hanorm i
  have hmu (i j : Fin 5) : E ((single i j (1 : ℂ))) = (star (a i) * a j) • (single i j (1 : ℂ)) := by
    by_cases hi : i = 0
    · subst i; simp only [ha0, star_one, one_mul]; exact hrow j
    by_cases hj : j = 0
    · subst j; simp only [ha0, mul_one]; exact hcol i
    by_cases hij : i = j
    · subst j; rw [hunit, one_smul]; exact hd i
    have hh := hJ ((single i (0 : Fin 5) (1 : ℂ))) ((single (0 : Fin 5) j (1 : ℂ)))
    have hm : jordan ((single i (0 : Fin 5) (1 : ℂ))) ((single (0 : Fin 5) j (1 : ℂ))) = (single i j (1 : ℂ)) := by
      simp [jordan, mu_mul, hij, Ne.symm hij]
    rw [hm, hcol, hrow, jordan_smul_left, jordan_smul_right, hm, smul_smul] at hh
    exact hh
  let u : Fin 5 → ℂ := fun i => star (a i)
  have hu (i : Fin 5) : u i * star (u i) = 1 := by
    simp only [u, star_star]; exact hunit i
  have hD : diagonal u ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    simpa only [Pi.star_apply, hu, diagonal_one]
  let D : Matrix.unitaryGroup (Fin 5) ℂ := ⟨diagonal u, hD⟩
  let J := Unitary.conjStarAlgAut ℂ _ D
  have hJmu (i j : Fin 5) : J ((single i j (1 : ℂ))) = (star (a i) * a j) • (single i j (1 : ℂ)) := by
    change diagonal u * (single i j (1 : ℂ)) * (diagonal u)ᴴ = _
    simp only [diagonal_conjTranspose, diagonal_mul, mul_diagonal]
    ext r s
    simp only [Matrix.smul_apply, smul_eq_mul, Pi.star_apply, u, star_star]
    by_cases hr : i = r <;> by_cases hs : j = s <;> simp [Matrix.single, hr, hs]
  have hmaps : E = J.toAlgEquiv.toLinearMap := by
    apply Matrix.ext_linearMap
    intro i j
    apply LinearMap.ext
    intro z
    change E (single i j z) = J (single i j z)
    have hz : single i j z = z • (single i j (1 : ℂ)) := by simp
    rw [hz, map_smul, map_smul, hmu, hJmu]
  refine ⟨D, fun Y => ?_⟩
  have hh := LinearMap.congr_fun hmaps Y
  change E Y = J Y at hh
  simpa only [J, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose] using hh

private theorem diagonal_jordan_classification (E : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ)
    (hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B))
    (hstar : ∀ A, E Aᴴ = (E A)ᴴ) (hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)))
    (hinj : Function.Injective E) :
    ∃ D : Matrix.unitaryGroup (Fin 5) ℂ,
      (∀ Y, E Y = (D : Matrix (Fin 5) (Fin 5) ℂ) * Y * (D : Matrix (Fin 5) (Fin 5) ℂ)ᴴ) ∨
      (∀ Y, E Y = (D : Matrix (Fin 5) (Fin 5) ℂ) * Y.transpose * (D : Matrix (Fin 5) (Fin 5) ℂ)ᴴ) := by
  obtain ⟨c, hc, hf | hr⟩ := peirce_single_orientation E hJ hstar hd 0 1 (by decide)
  · obtain ⟨D, hD⟩ := forward_phase_implementation E hJ hstar hd hinj c hc hf
    exact ⟨D, Or.inl hD⟩
  · let F := E.comp (Matrix.transposeLinearEquiv (Fin 5) (Fin 5) ℂ ℂ).toLinearMap
    have hF (Y : Matrix (Fin 5) (Fin 5) ℂ) : F Y = E Y.transpose := rfl
    have hjF (A B : Matrix (Fin 5) (Fin 5) ℂ) : F (jordan A B) = jordan (F A) (F B) := by
      simp only [hF]
      have ht : (jordan A B).transpose = jordan A.transpose B.transpose := by
        simp only [jordan, transpose_add, transpose_mul, add_comm]
      rw [ht, hJ]
    have hsF (A : Matrix (Fin 5) (Fin 5) ℂ) : F Aᴴ = (F A)ᴴ := by
      simp only [hF, transpose_conjTranspose, ← hstar, conjTranspose_transpose]
    have hdF (i : Fin 5) : F ((single i i (1 : ℂ))) = (single i i (1 : ℂ)) := by simp [hF, hd]
    have hiF : Function.Injective F := by
      intro A B he
      apply Matrix.transpose_injective
      exact hinj he
    have hf01 : F ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ))) = star c • (single (0 : Fin 5) (1 : Fin 5) (1 : ℂ)) := by
      have hh := hstar ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ)))
      rw [show ((single (0 : Fin 5) (1 : Fin 5) (1 : ℂ)))ᴴ = (single (1 : Fin 5) (0 : Fin 5) (1 : ℂ)) by simp, hr] at hh
      simpa only [hF, transpose_single, conjTranspose_smul, conjTranspose_single, star_one] using hh
    have hcs : star c * star (star c) = 1 := by simpa [mul_comm] using hc
    obtain ⟨D, hD⟩ := forward_phase_implementation F hjF hsF hdF hiF (star c) hcs hf01
    refine ⟨D, Or.inr (fun Y => ?_)⟩
    simpa only [hF, transpose_transpose] using hD Y.transpose
end

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

theorem unital_positive_inverse_classification
    (Phi Psi : Matrix (Fin 5) (Fin 5) ℂ →ₗ[ℂ] Matrix (Fin 5) (Fin 5) ℂ) (hPhi : IsPositive Phi) (hPsi : IsPositive Psi)
    (hPhi1 : Phi 1 = 1) (hPsi1 : Psi 1 = 1)
    (hcomp : Psi.comp Phi = LinearMap.id) :
    ∃ U : Matrix.unitaryGroup (Fin 5) ℂ,
      (∀ Y, Phi Y = (U : Matrix (Fin 5) (Fin 5) ℂ) * Y * star (U : Matrix (Fin 5) (Fin 5) ℂ)) ∨
      (∀ Y, Phi Y = (U : Matrix (Fin 5) (Fin 5) ℂ) * Y.transpose * star (U : Matrix (Fin 5) (Fin 5) ℂ)) := by
  obtain ⟨V, hV⟩ := positive_inverse_projection_alignment Phi Psi hPhi hPsi hPhi1 hPsi1 hcomp
  let J := Unitary.conjStarAlgAut ℂ _ V
  let E := J.symm.toAlgEquiv.toLinearMap.comp Phi
  have hE (Y : Matrix (Fin 5) (Fin 5) ℂ) : E Y = J.symm (Phi Y) := rfl
  have hJ : ∀ A B, E (jordan A B) = jordan (E A) (E B) := by
    intro A B
    rw [hE, positive_inverse_complex_jordan Phi Psi hPhi hPsi hPhi1 hPsi1 hcomp]
    simp only [jordan, map_add, map_mul, hE]
  have hstar : ∀ A, E Aᴴ = (E A)ᴴ := by
    intro A
    rw [hE, positive_map_star Phi hPhi]
    simp only [← Matrix.star_eq_conjTranspose, map_star, hE]
  have hd : ∀ i, E ((single i i (1 : ℂ))) = (single i i (1 : ℂ)) := by
    intro i
    rw [hE, hV]
    change J.symm (J ((single i i (1 : ℂ)))) = (single i i (1 : ℂ))
    exact J.symm_apply_apply _
  have hinj : Function.Injective E := by
    intro A B he
    have hp : Phi A = Phi B := J.symm.injective he
    have hA := LinearMap.congr_fun hcomp A
    have hB := LinearMap.congr_fun hcomp B
    change Psi (Phi A) = A at hA
    change Psi (Phi B) = B at hB
    rw [← hA, ← hB, hp]
  obtain ⟨D, hf | ht⟩ := diagonal_jordan_classification E hJ hstar hd hinj
  · refine ⟨V * D, Or.inl (fun Y => ?_)⟩
    calc
      Phi Y = J (E Y) := (J.apply_symm_apply _).symm
      _ = J (Unitary.conjStarAlgAut ℂ _ D Y) := by
        rw [hf]; rfl
      _ = _ := by
        rw [← Unitary.conjStarAlgAut_mul_apply, Unitary.conjStarAlgAut_apply]
  · refine ⟨V * D, Or.inr (fun Y => ?_)⟩
    calc
      Phi Y = J (E Y) := (J.apply_symm_apply _).symm
      _ = J (Unitary.conjStarAlgAut ℂ _ D Y.transpose) := by
        rw [ht]; rfl
      _ = _ := by
        rw [← Unitary.conjStarAlgAut_mul_apply, Unitary.conjStarAlgAut_apply]
end

end D5.S3.QuantumChannels.RenyiSufficiency.PositiveInverseClassification
