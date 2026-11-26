/- GID: D5/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiSupportedMoorePenrose
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite variational arithmetic inverse equals the supported Moore-Penrose form. -/

import D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse

/-! The range condition and the maximizing test for the arithmetic inverse.
The finite inverse is the existing `FiniteMoorePenroseInverse.moorePenroseInverse`.
The kernel-direction test and square completion follow the independent GPT Pro
derivation for the singular metric variational form.

proof_shape: content
admission_basis: escape-witness
escape_witness: boundedness of the complex quadratic tests forces membership in
the arithmetic range, where the Moore–Penrose preimage attains the supremum.
The actual channel maps each admissible test direction into this output range. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Quantum.Divergence.UmegakiSupportedMoorePenrose

open _root_.Matrix
open scoped InnerProduct CStarAlgebra ComplexOrder MatrixOrder
open HilbertSchmidtOperatorSpace
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension

universe u
variable {n R a b : Type u}
  [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The variational domain is the range of the arithmetic map. On this range
the Moore–Penrose preimage attains the variational supremum. -/
theorem variationalInverse_moorePenrose (Z V : Matrix n n ℂ) (t : ℝ)
    (hZ : Z.PosSemidef) (ht : t ∈ Set.Icc 0 1) :
    (BddAbove (inverseTestValues Z V t) ↔ matrixHS V ∈ (hsArithmeticMap Z t).toLinearMap.range) ∧
    (matrixHS V ∈ (hsArithmeticMap Z t).toLinearMap.range →
      variationalInverse Z V t =
        (inner ℂ (matrixHS V) (moorePenroseInverse (hsArithmeticMap Z t).toLinearMap
          (matrixHS V))).re) := by
  let A := (hsArithmeticMap Z t).toLinearMap
  let W := matrixHS V
  let Y₀ := moorePenroseInverse A W
  have hPositive := (arithmetic_positive Z t hZ ht).toLinearMap
  have hSym : A.IsSymmetric := hPositive.isSymmetric
  have hInner (X Y : Matrix n n ℂ) : inner ℂ (matrixHS X) (matrixHS Y) = (Xᴴ * Y).trace :=
    hsInner_matrix X Y
  have hTest (Y : HSOp (EuclideanSpace ℂ n)) :
      inverseTest Z V (matrixHS.symm Y) t =
        2 * (inner ℂ Y W).re - (inner ℂ Y (A Y)).re := by
    simp only [inverseTest, energy, ← hInner, arithmetic, ← arithmetic_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  have hRange (hFin : BddAbove (inverseTestValues Z V t)) : W ∈ A.range := by
    obtain ⟨C, hC⟩ := hFin
    have hOrth : W ∈ A.kerᗮ := by
      apply Submodule.mem_orthogonal_iff_re_inner_eq_zero.mpr
      intro K hK
      change (inner ℂ K W).re = 0
      by_contra hNonzero
      let s : ℝ := (|C| + 1) / (2 * (inner ℂ K W).re)
      have hBound : inverseTest Z V (matrixHS.symm ((s : ℂ) • K)) t ≤ C :=
        hC (Set.mem_insert_of_mem 0 (Set.mem_range_self (matrixHS.symm ((s : ℂ) • K))))
      rw [hTest, map_smul, LinearMap.mem_ker.mp hK, smul_zero, inner_zero_right, Complex.zero_re,
        sub_zero, inner_smul_left] at hBound
      change 2 * (star (s : ℂ) * inner ℂ K W).re ≤ C at hBound
      rw [show star (s : ℂ) = (s : ℂ) from Complex.conj_ofReal s, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hBound
      have hScale : 2 * (s * (inner ℂ K W).re) = |C| + 1 := by
        calc
          _ = s * (2 * (inner ℂ K W).re) := by ring
          _ = _ := div_mul_cancel₀ _ (mul_ne_zero (by norm_num) hNonzero)
      linarith only [hBound, hScale, le_abs_self C]
    rwa [LinearMap.orthogonal_ker, hSym.adjoint_eq] at hOrth
  have hMax (hW : W ∈ A.range) :
      IsGreatest (inverseTestValues Z V t) (inner ℂ W Y₀).re := by
    have hSolve : A Y₀ = W := by
      obtain ⟨K, hK⟩ := LinearMap.mem_range.mp hW
      dsimp only [Y₀]
      rw [← hK]
      exact congrArg (fun L : HSOp (EuclideanSpace ℂ n) →ₗ[ℂ] HSOp (EuclideanSpace ℂ n) => L K)
        (comp_moorePenroseInverse_comp A)
    have hSquare (Y : HSOp (EuclideanSpace ℂ n)) :
        inverseTest Z V (matrixHS.symm Y) t =
          (inner ℂ W Y₀).re - (inner ℂ (Y - Y₀) (A (Y - Y₀))).re := by
      have hCross : (inner ℂ Y₀ (A Y)).re = (inner ℂ Y W).re := by
        rw [← hSym Y₀ Y, hSolve]
        exact inner_re_symm (𝕜 := ℂ) W Y
      have hSelf : (inner ℂ Y₀ W).re = (inner ℂ W Y₀).re := inner_re_symm (𝕜 := ℂ) Y₀ W
      rw [hTest, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
        Complex.sub_re, Complex.sub_re, Complex.sub_re, hCross, hSolve, hSelf]
      ring
    have hAttain := hSquare Y₀
    simp only [sub_self, map_zero, inner_zero_right, Complex.zero_re, sub_zero] at hAttain
    refine ⟨hAttain ▸ Set.mem_insert_of_mem _ (Set.mem_range_self (matrixHS.symm Y₀)), ?_⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨X, rfl⟩
    · rw [← hSolve]
      exact hPositive.re_inner_nonneg_left _
    · have h := hSquare (matrixHS X)
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.trans_le (sub_le_self _ (hPositive.re_inner_nonneg_right _))
  exact ⟨⟨hRange, fun hW => ⟨_, (hMax hW).2⟩⟩,
    fun hW => (hMax hW).isLUB.csSup_eq ⟨_, (hMax hW).1⟩⟩

theorem variationalInverse_output_moorePenrose (N : QuantumChannel a b)
    (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ) (hZ : Z.PosSemidef)
    (hV : partialTraceRight V = 0) (ht : t ∈ Set.Icc 0 1)
    (hFin : BddAbove (inverseTestValues Z V t)) :
    matrixHS (amp N V) ∈ (hsArithmeticMap (amp N Z) t).toLinearMap.range ∧
    variationalInverse (amp N Z) (amp N V) t =
      (inner ℂ (matrixHS (amp N V)) (moorePenroseInverse (hsArithmeticMap (amp N Z) t).toLinearMap
        (matrixHS (amp N V)))).re := by
  have hOut := (variationalInverse_channel_contraction N Z V t hZ hV ht hFin).1
  have hPSD : (amp N Z).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (referenceAction_nonneg N (CStarMatrix.ofMatrix Z)
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hZ.nonneg)))
  have hMP := variationalInverse_moorePenrose (amp N Z) (amp N V) t hPSD ht
  exact ⟨hMP.1.mp hOut, hMP.2 (hMP.1.mp hOut)⟩

/-- The actual metric coefficient uses the supported Moore–Penrose form at
the output and the faithful inverse at the input. -/
theorem variationalMetricCoefficient_eq_sSup_moorePenrose (N : QuantumChannel a b)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    variationalMetricCoefficient N t = sSup (insert 0
      {x : ℝ | ∃ (R : Type u) (fR : Fintype R) (eR : DecidableEq R),
        letI := fR
        letI := eR
        ∃ Z V : Matrix (R × a) (R × a) ℂ, Z.PosDef ∧ partialTraceRight V = 0 ∧
          0 < q Z V t ∧ matrixHS (amp N V) ∈ (hsArithmeticMap (amp N Z) t).toLinearMap.range ∧
          x = (inner ℂ (matrixHS (amp N V))
            (moorePenroseInverse (hsArithmeticMap (amp N Z) t).toLinearMap
              (matrixHS (amp N V)))).re / q Z V t}) := by
  have hOutput (R : Type u) [Fintype R] [DecidableEq R]
      (Z V : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) (hV : partialTraceRight V = 0) :=
    variationalInverse_output_moorePenrose N Z V t hZ.posSemidef hV ht
      (variationalInverse_eq_q Z V t hZ ht).1
  unfold variationalMetricCoefficient
  refine congrArg (fun ratios : Set ℝ => sSup (insert 0 ratios)) ?_
  ext x
  constructor
  · rintro ⟨R, fR, eR, Z, V, hZ, hV, hq, rfl⟩
    let _ := fR
    let _ := eR
    obtain ⟨hRange, hEq⟩ := hOutput R Z V hZ hV
    exact ⟨R, fR, eR, Z, V, hZ, hV, hq, hRange, by rw [hEq]⟩
  · rintro ⟨R, fR, eR, Z, V, hZ, hV, hq, _, rfl⟩
    let _ := fR
    let _ := eR
    exact ⟨R, fR, eR, Z, V, hZ, hV, hq, by rw [(hOutput R Z V hZ hV).2]⟩

#print axioms variationalInverse_moorePenrose
#print axioms variationalInverse_output_moorePenrose
#print axioms variationalMetricCoefficient_eq_sSup_moorePenrose
end D5.S3.Quantum.Divergence.UmegakiSupportedMoorePenrose
