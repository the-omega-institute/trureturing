/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original width-three scalar-Gram theorem at the native threshold. -/

import D5.S3.Quantum.Algebra.CompressionKernel.NativeThreeKernelGeometry
import D5.S3.Quantum.Algebra.CompressionKernel.NativeTwoKernelBound
import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeCommonKernelBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The native kernel alternatives applied to the unchanged original tensor factors. -/

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound

open D5.S3.Quantum.Algebra.CommonCoefficientPlane
open D5.S3.Quantum.Algebra.NativeThreeKernelGeometry
open D5.S3.Quantum.Algebra.NativeCoefficientWhitening
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation
open D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

private theorem neutral_plane_bound {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) = 1)
    (hMGram : ∑ r, (M r)ᴴ * M r = 1)
    (L : Submodule ℂ (Fin 3 → ℂ))
    (hLdim : Module.finrank ℂ L = 2)
    (hplane : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      compression M T = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0) :
    2 * c ≤ d := by
  have hneutral := complex_block_neutral M N hF hMGram L (by
    intro T hT hcomp
    apply hplane T hT
    exact hcomp)
  let e : (Fin 3 → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
    (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).symm
  let Le : Submodule ℂ (EuclideanSpace ℂ (Fin 3)) := L.map e.toLinearMap
  have hLedim : Module.finrank ℂ Le = 2 := by
    rw [LinearEquiv.finrank_map_eq e, hLdim]
  let b : OrthonormalBasis (Fin 2) ℂ Le := hLedim ▸ stdOrthonormalBasis ℂ Le
  let V : Matrix (Fin 3) (Fin 2) ℂ := fun i a =>
    (WithLp.ofLp ((b a : Le) : EuclideanSpace ℂ (Fin 3))) i
  have hVgram : Vᴴ * V = 1 := by
    ext a q
    have hb := (orthonormal_iff_ite.mp b.orthonormal) a q
    simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      PiLp.inner_apply, dotProduct, Matrix.one_apply, mul_comm] using hb
  have hVplane : ∀ (l m : Fin c) (a q : Fin 2),
      ∑ r, ∑ s, star (V r a) *
        (((N r)ᴴ * N s) l m -
          (if r = s then if l = m then 1 else 0 else 0)) * V s q = 0 := by
    intro l m a q
    obtain ⟨u, hu, hueq⟩ := (b a).property
    obtain ⟨v, hv, hveq⟩ := (b q).property
    have hVa (r : Fin 3) : V r a = u r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hueq
      simpa [V, e] using hh.symm
    have hVq (r : Fin 3) : V r q = v r := by
      have hh := congrArg (fun z : EuclideanSpace ℂ (Fin 3) => WithLp.ofLp z r) hveq
      simpa [V, e] using hh.symm
    have hh := hneutral l m u hu v hv
    simpa [Matrix.mulVec, dotProduct, hVa, hVq, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hh
  let W : Matrix (Fin d) (Fin 3 × Fin c) ℂ := concatK N
  let P : Matrix (Fin 3 × Fin c) (Fin 3 × Fin c) ℂ := Wᴴ * W
  let C : Matrix (Fin 3 × Fin c) (Fin 2 × Fin c) ℂ :=
    Matrix.kronecker V (1 : Matrix (Fin c) (Fin c) ℂ)
  have hPentry (r s : Fin 3) (l m : Fin c) : P (r, l) (s, m) =
      ((N r)ᴴ * N s) l m := by
    rfl
  have hCPC : Cᴴ * P * C = 1 := by
    have hCentry (r : Fin 3) (i : Fin c) (a : Fin 2) (l : Fin c) :
        C (r, i) (a, l) = if i = l then V r a else 0 := by
      by_cases h : i = l <;> simp [C, Matrix.kronecker,
        Matrix.kroneckerMap_apply, h]
    ext ⟨a, l⟩ ⟨q, m⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.conjTranspose_apply]
    simp_rw [hCentry, hPentry]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.sum_mul]
    have hz := hVplane l m a q
    have hv : ∑ r, ∑ s, star (V r a) *
        ((if r = s then if l = m then 1 else 0 else 0)) * V s q =
        (if l = m then (Vᴴ * V) a q else 0) := by
      by_cases hlm : l = m
      · subst m
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      · simp [hlm]
    have hsum (r s : Fin 3) :
        ∑ i : Fin c, star (if i = l then V r a else 0) *
          ((N r)ᴴ * N s) i m * V s q =
          star (V r a) * ((N r)ᴴ * N s) l m * V s q := by
      classical
      rw [Finset.sum_eq_single l]
      · simp
      · intro b hb hbl
        simp [hbl]
      · simp
    simp_rw [hsum]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at hz
    rw [hv, hVgram] at hz
    rw [Finset.sum_comm]
    by_cases haq : a = q <;> by_cases hlm : l = m
    · simpa [Matrix.one_apply, Prod.mk.injEq, haq, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, haq, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, haq, hlm] using sub_eq_zero.mp hz
    · simpa [Matrix.one_apply, Prod.mk.injEq, haq, hlm] using sub_eq_zero.mp hz
  have hRank : (Cᴴ * P * C).rank ≤ d := by
    calc
      (Cᴴ * P * C).rank ≤ P.rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      _ ≤ W.rank := Matrix.rank_mul_le_right _ _
      _ ≤ d := by simpa using W.rank_le_card_height
  rw [hCPC, Matrix.rank_one] at hRank
  simpa only [Fintype.card_prod, Fintype.card_fin] using hRank

/-- Every original width-three scalar-Gram tensor at `a < b` obeys the right
dimension bound, including all minimal decomposition widths and zero cases. -/
theorem native_three_rectangular_bound {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hab : a < b)
    (hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ *
      (∑ r, Matrix.kronecker (M r) (N r)) =
        (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) :
    3 * c ≤ 2 * d := by
  classical
  by_cases hcz : c = 0
  · simp [hcz]
  have hc : 0 < c := Nat.pos_of_ne_zero hcz
  obtain ⟨k, hk, A, D, hA, hD, hsum, hgram⟩ :=
    normalized_minimal_decomposition M N lambda hlambda hF
  obtain ⟨B, hB, hBB, hPres, hMGram, hMLI⟩ :=
    exact_whitening A D hD hc hgram
  let M' := mix B A
  let N' := mix B.transpose⁻¹ D
  have hM' : LinearIndependent ℂ M' := hMLI hA
  have hMG : ∑ r, (M' r)ᴴ * M' r = 1 := hMGram
  have hFG : (∑ r, Matrix.kronecker (M' r) (N' r))ᴴ *
      (∑ r, Matrix.kronecker (M' r) (N' r)) = 1 := by
    simpa only [M', N', hPres] using hgram
  have hSG : (stackK M')ᴴ * stackK M' = 1 := by
    rw [stackK_gram]
    exact hMG
  have hSI := gram_identity_injective (stackK M') hSG
  have hdim := LinearMap.finrank_le_finrank_of_injective hSI
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
    Fintype.card_fin] at hdim
  interval_cases k
  · omega
  · omega
  · have htwo :=
      D5.S3.Quantum.Algebra.NativeTwoKernelBound.right_dimension_bound
        hab M' N' hM' hFG hMG
    omega
  · obtain ⟨v, hv, hkernel⟩ | ⟨L, hLdim, hplane⟩ :=
      native_three_compression_kernel_geometry a b hab M' hM'
        (by exact hSI)
    · exact NativeCommonKernelBound.original_gram_common_kernel_bound
        M' N' hab hFG hMG v hv hkernel
    · have hneutral := neutral_plane_bound M' N' hFG hMG L hLdim (by
        intro T hT hcomp
        apply hplane T hT
        exact hcomp)
      omega

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeThreeRectangularBound
