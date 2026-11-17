/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common coefficient kernel bounds three times the right input by twice its output. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound

/-! The original right Gram blocks yield a dimension bound from a common coefficient kernel. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeCommonKernelBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeRectangularBound
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
open D5.S3.Quantum.Algebra.NativeWidthAtMostThreeRefutation

private theorem tensor_factor {a b c d : ℕ}
    (Y : Matrix (Fin d) (Fin c) ℂ) (X : Matrix (Fin a) (Fin b) ℂ)
    (u : Fin c → ℂ) (x : Fin b → ℂ) :
    Y * Matrix.vecMulVec u x * X.transpose =
      Matrix.vecMulVec (Y *ᵥ u) (X *ᵥ x) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

private theorem matrix_not_injective_of_dimensions {a b : ℕ} (hab : a < b)
    (A : Matrix (Fin a) (Fin b) ℂ) : ¬ Function.Injective A.mulVecLin := by
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hab)
  exact fun hA => hker (LinearMap.ker_eq_bot.mpr hA)

private theorem complex_block_annihilated {a b c d : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (Y : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (hF : (∑ r, Matrix.kronecker (X r) (Y r))ᴴ *
      (∑ r, Matrix.kronecker (X r) (Y r)) = 1)
    (hXGram : ∑ r, (X r)ᴴ * X r = 1)
    (v : Fin 3 → ℂ)
    (hkernel : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression X T = 0 →
      T *ᵥ v = 0) (l m : Fin c) :
    (fun r s =>
      ((Y r)ᴴ * Y s) l m -
        (if r = s then if l = m then 1 else 0 else 0)) *ᵥ v = 0 := by
  let T : Matrix (Fin 3) (Fin 3) ℂ := fun r s =>
    ((Y r)ᴴ * Y s) l m - (if r = s then if l = m then 1 else 0 else 0)
  let Tr : Matrix (Fin 3) (Fin 3) ℂ := (realPart T : Matrix (Fin 3) (Fin 3) ℂ)
  let Ti : Matrix (Fin 3) (Fin 3) ℂ := (imaginaryPart T : Matrix (Fin 3) (Fin 3) ℂ)
  have hc : (stack X)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 :=
    block_compression X Y hF hXGram l m
  have hcstar : (stack X)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 := by
    have h := stackK_compression_conjTranspose X T
    change (stack X)ᴴ * Matrix.kronecker Tᴴ (1 : Matrix (Fin a) (Fin a) ℂ) * stack X =
      ((stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stack X)ᴴ at h
    rw [h, hc, Matrix.conjTranspose_zero]
  have hTr : Tr.IsHermitian := (realPart T).property.isHermitian
  have hTi : Ti.IsHermitian := (imaginaryPart T).property.isHermitian
  have hTr_formula : Tr = ((2 : ℝ)⁻¹ : ℂ) • (T + Tᴴ) := by
    dsimp [Tr]
    rw [realPart_apply_coe]
    ext i j
    simp [Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul]
    ring
  let z : ℂ := -Complex.I * ((2 : ℝ)⁻¹ : ℂ)
  have hTi_formula : Ti = z • (T - Tᴴ) := by
    dsimp [Ti]
    rw [imaginaryPart_apply_coe]
    ext i j
    simp [z, Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul, smul_smul]
    ring
  have hcTr : (stack X)ᴴ * Matrix.kronecker Tr
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 := by
    rw [hTr_formula]
    have h := stackK_compression_smul_add X ((2 : ℝ)⁻¹ : ℂ) ((2 : ℝ)⁻¹ : ℂ)
      T Tᴴ
    change (stack X)ᴴ * Matrix.kronecker (((2 : ℝ)⁻¹ : ℂ) • T +
        ((2 : ℝ)⁻¹ : ℂ) • Tᴴ) (1 : Matrix (Fin a) (Fin a) ℂ) * stack X =
      ((2 : ℝ)⁻¹ : ℂ) • ((stack X)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X) +
      ((2 : ℝ)⁻¹ : ℂ) • ((stack X)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X) at h
    rw [hc, hcstar] at h
    simpa only [smul_add, smul_zero, zero_add] using h
  have hcTi : (stack X)ᴴ * Matrix.kronecker Ti
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 := by
    rw [hTi_formula, sub_eq_add_neg, smul_add, smul_neg]
    have h := stackK_compression_smul_add X z (-z) T Tᴴ
    change (stack X)ᴴ * Matrix.kronecker (z • T + (-z) • Tᴴ)
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X =
      z • ((stack X)ᴴ * Matrix.kronecker T
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X) +
      (-z) • ((stack X)ᴴ * Matrix.kronecker Tᴴ
        (1 : Matrix (Fin a) (Fin a) ℂ) * stack X) at h
    rw [hc, hcstar] at h
    simpa only [smul_sub, sub_eq_add_neg, neg_smul, smul_zero, zero_add] using h
  have hTr0 : D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression X Tr = 0 := by
    change (stack X)ᴴ * Matrix.kronecker Tr
      (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0
    exact hcTr
  have hTi0 : D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression X Ti = 0 := by
    change (stack X)ᴴ * Matrix.kronecker Ti
      (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0
    exact hcTi
  have hTrv := hkernel Tr hTr hTr0
  have hTiv := hkernel Ti hTi hTi0
  have hdecomp : Tr + Complex.I • Ti = T := realPart_add_I_smul_imaginaryPart T
  change T *ᵥ v = 0
  rw [← hdecomp]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, hTrv, hTiv, smul_zero, add_zero]

theorem original_gram_common_kernel_bound {a b c d : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (Y : Fin 3 → Matrix (Fin d) (Fin c) ℂ)
    (hab : a < b)
    (hF : (∑ r, Matrix.kronecker (X r) (Y r))ᴴ *
      (∑ r, Matrix.kronecker (X r) (Y r)) = 1)
    (hXGram : ∑ r, (X r)ᴴ * X r = 1)
    (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (hkernel : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
      D5.S3.Quantum.Algebra.CommonCoefficientPlane.compression X T = 0 →
      T *ᵥ v = 0) :
    3 * c ≤ 2 * d := by
  classical
  have hR : ∀ l m : Fin c, (fun r s =>
      ((Y r)ᴴ * Y s) l m -
        (if r = s then if l = m then 1 else 0 else 0)) *ᵥ v = 0 := by
    intro l m
    exact complex_block_annihilated X Y hF hXGram v hkernel l m
  let Z : Matrix (Fin d) (Fin c) ℂ := ∑ s, v s • Y s
  have hYZ (r : Fin 3) : (Y r)ᴴ * Z = v r • (1 : Matrix (Fin c) (Fin c) ℂ) := by
    ext l m
    have hr := congrFun (hR l m) r
    change (∑ s, (((Y r)ᴴ * Y s) l m -
      (if r = s then if l = m then 1 else 0 else 0)) * v s) = 0 at hr
    have hsum : (∑ s, ((Y r)ᴴ * Y s) l m * v s) =
        (if l = m then v r else 0) := by
      have hdelta : (∑ s, (if r = s then if l = m then 1 else 0 else 0) * v s) =
          (if l = m then v r else 0) := by
        by_cases hlm : l = m <;> simp [hlm]
      have hr' := hr
      simp_rw [sub_mul] at hr'
      rw [Finset.sum_sub_distrib] at hr'
      have heq := sub_eq_zero.mp hr'
      simpa [hdelta] using heq
    have hmat : (Y r)ᴴ * Z =
        ∑ s, v s • ((Y r)ᴴ * Y s) := by
      change (Y r)ᴴ * (∑ s, v s • Y s) = _
      rw [Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Matrix.mul_smul]
    rw [hmat]
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      mul_comm] using hsum
  have hZ : Function.Injective Z.mulVecLin := by
    intro u w huw
    apply sub_eq_zero.mp
    have hu : Z *ᵥ (u - w) = 0 := by
      change Z.mulVecLin (u - w) = 0
      rw [map_sub, huw, sub_self]
    obtain ⟨r, hr⟩ : ∃ r : Fin 3, v r ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (funext h)
    have hmul : ((Y r)ᴴ * Z) *ᵥ (u - w) = 0 := by
      rw [← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    rw [hYZ r, Matrix.smul_mulVec, Matrix.one_mulVec] at hmul
    exact (smul_eq_zero.mp hmul).resolve_left hr
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  let J := {r : Fin 3 // r ≠ i}
  let W : J → Matrix (Fin d) (Fin c) ℂ := fun r =>
    Y r.1 - (star (v r.1 / v i)) • Y i
  have hWorth (r : J) : (W r)ᴴ * Z = 0 := by
    dsimp [W]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.sub_mul,
      Matrix.smul_mul, hYZ r.1, hYZ i]
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [Matrix.smul_apply, Matrix.one_apply, div_eq_mul_inv, hi]
    · simp [Matrix.smul_apply, Matrix.one_apply, hpq]
  have hWcommon : ∀ u : Fin c → ℂ,
      (∀ r : J, W r *ᵥ u = 0) → u = 0 := by
    intro u hu
    by_contra hu0
    let A : Matrix (Fin a) (Fin b) ℂ :=
      ∑ r : Fin 3, (star (v r / v i)) • X r
    have hnot := matrix_not_injective_of_dimensions hab A
    obtain ⟨x, y, hxyA, hxy⟩ := Function.not_injective_iff.mp hnot
    let x₀ := x - y
    have hx₀ : x₀ ≠ 0 := sub_ne_zero.mpr hxy
    have hAx₀ : A *ᵥ x₀ = 0 := by
      dsimp [x₀]
      change A.mulVecLin (x - y) = 0
      rw [map_sub, hxyA, sub_self]
    have hYrel (r : Fin 3) : Y r *ᵥ u =
        (star (v r / v i)) • (Y i *ᵥ u) := by
      by_cases hri : r = i
      · subst r
        simp [hi]
      · have hw := hu ⟨r, hri⟩
        have hw' : Y r *ᵥ u - (star (v r / v i)) • (Y i *ᵥ u) = 0 := by
          simpa [W, Matrix.sub_mulVec, Matrix.smul_mulVec] using hw
        exact sub_eq_zero.mp hw'
    have hFq : (∑ r, Matrix.kronecker (X r) (Y r)) *ᵥ
        Matrix.vec (Matrix.vecMulVec u x₀) = 0 := by
      have hterm (r : Fin 3) : Matrix.kronecker (X r) (Y r) *ᵥ
          Matrix.vec (Matrix.vecMulVec u x₀) =
          Matrix.vec (Matrix.vecMulVec (Y r *ᵥ u) (X r *ᵥ x₀)) := by
        simpa only [Matrix.kronecker] using
          (Matrix.kronecker_mulVec_vec (Y r) (Matrix.vecMulVec u x₀) (X r)).trans
            (congrArg Matrix.vec (tensor_factor (Y r) (X r) u x₀))
      rw [Matrix.sum_mulVec]
      simp_rw [hterm]
      ext ⟨q, p⟩
      simp only [Pi.zero_apply]
      rw [Finset.sum_apply]
      change (∑ r, (Y r *ᵥ u) p * (X r *ᵥ x₀) q) = 0
      calc
        (∑ r, (Y r *ᵥ u) p * (X r *ᵥ x₀) q) =
            ∑ r, ((star (v r / v i)) • (Y i *ᵥ u)) p *
              (X r *ᵥ x₀) q := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [hYrel r]
        _ = 0 := by
          calc
            (∑ r, ((star (v r / v i)) • (Y i *ᵥ u)) p *
                (X r *ᵥ x₀) q) =
                (∑ r, (star (v r / v i)) *
                  (X r *ᵥ x₀) q) * (Y i *ᵥ u) p := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro r hr
                    simp [mul_comm, mul_left_comm, mul_assoc]
            _ = 0 := by
              have hcoef : (∑ r, (star (v r / v i)) *
                  (X r *ᵥ x₀) q) = 0 := by
                have hcoef0 := congrFun hAx₀ q
                simp only [A, Matrix.mulVec, dotProduct, Matrix.sum_apply,
                  Matrix.smul_apply, smul_eq_mul] at hcoef0
                calc
                  (∑ r, (star (v r / v i)) * (X r *ᵥ x₀) q) =
                      ∑ r, ∑ j, (star (v r / v i)) * X r q j * x₀ j := by
                        apply Finset.sum_congr rfl
                        intro r hr
                        simp only [Matrix.mulVec, dotProduct]
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                  _ = ∑ j, ∑ r, (star (v r / v i)) * X r q j * x₀ j := by
                        rw [Finset.sum_comm]
                  _ = ∑ j, (∑ r, (star (v r / v i)) * X r q j) * x₀ j := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_mul]
                  _ = 0 := hcoef0
              rw [hcoef]
              simp
    have hFinj := gram_identity_injective
      (∑ r, Matrix.kronecker (X r) (Y r)) hF
    have hq : Matrix.vec (Matrix.vecMulVec u x₀) ≠ 0 := by
      intro hq
      have hmat : Matrix.vecMulVec u x₀ = 0 := Matrix.vec_eq_zero_iff.mp hq
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hu0
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hx₀
      have hu_eq : u = 0 := by
        funext p'
        have hentry := congrArg (fun M : Matrix (Fin c) (Fin b) ℂ => M p' q) hmat
        have hz : u p' * x₀ q = 0 := by
          simpa [Matrix.vecMulVec_apply] using hentry
        exact (mul_eq_zero.mp hz).resolve_right hq
      exact hu0 hu_eq
    apply hq
    apply hFinj
    change (∑ r, Matrix.kronecker (X r) (Y r)) *ᵥ
      Matrix.vec (Matrix.vecMulVec u x₀) =
      (∑ r, Matrix.kronecker (X r) (Y r)) *ᵥ 0
    rw [Matrix.mulVec_zero]
    exact hFq
  let K : Submodule ℂ (Fin d → ℂ) := LinearMap.ker (Zᴴ).mulVecLin
  have hKdim : finrank ℂ K + c = d := by
    have h := (Zᴴ).mulVecLin.finrank_range_add_finrank_ker
    have hZrank : Z.rank = c := by
      change finrank ℂ (LinearMap.range Z.mulVecLin) = c
      rw [LinearMap.finrank_range_of_inj hZ]
      simp
    have hrange : finrank ℂ (LinearMap.range (Zᴴ).mulVecLin) = c := by
      change (Zᴴ).rank = c
      rw [Matrix.rank_conjTranspose]
      exact hZrank
    rw [hrange] at h
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, add_comm] using h
  have hdim : c ≤ 2 * finrank ℂ K := by
    have hWorth' : ∀ r : J, Zᴴ * W r = 0 := by
      intro r
      have hh := congrArg Matrix.conjTranspose (hWorth r)
      simpa using hh
    let f : (Fin c → ℂ) →ₗ[ℂ] (J → K) :=
      LinearMap.pi (fun r => LinearMap.codRestrict K (W r).mulVecLin (by
        intro u
        change Zᴴ *ᵥ (W r *ᵥ u) = 0
        have hh := congrArg (fun A : Matrix (Fin c) (Fin c) ℂ => A *ᵥ u) (hWorth' r)
        simpa [Matrix.mulVec_mulVec] using hh))
    have hf : Function.Injective f := by
      intro u w huw
      apply sub_eq_zero.mp
      apply hWcommon (u - w)
      intro r
      dsimp [f] at huw
      have hr := congrFun huw r
      have heq : W r *ᵥ u = W r *ᵥ w := by
        simpa using congrArg Subtype.val hr
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr heq
    have hh := LinearMap.finrank_le_finrank_of_injective hf
    have hJcard : Fintype.card J = 2 := by simp [J]
    simpa [f, Module.finrank_pi_fintype, hJcard] using hh
  omega

end D5.S3.Quantum.TensorNetworks.BridgeGraph.NativeCommonKernelBound
