/- GID: D5/S3/Quantum/Subentropy/Subadditivity
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/Subadditivity
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Jensen]
   utility: none
   digest: Subentropy is subadditive for every finite bipartite density state. -/

import D5.S3.Quantum.Subentropy.EigenbasisBlocks
import D5.S3.Quantum.Subentropy.PinchingGap
import Mathlib.Analysis.Convex.Jensen

/-! The classical block weights are retained without dividing by zero probabilities. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker CStarAlgebra

namespace D5.S3.Quantum.Subentropy.Subadditivity
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.Quantum.Subentropy.ClassicalQuantumGram
open _root_.D5.S3.Quantum.Subentropy.PinchingGap
open _root_.D5.S3.Quantum.Subentropy.EigenbasisBlocks

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B] [DecidableEq B]

private theorem pinching_upper (G : Matrix (X × B) (X × B) ℂ)
    (hG : G.PosSemidef) (htr : G.trace = 1) (x₀ : X) (i₀ : X × B) :
    matrixSubentropy (blockPinch G) - matrixSubentropy G ≤
      matrixSubentropy (diagonal (fun x =>
        (((∑ b, G (x,b) (x,b)).re : ℝ) : ℂ))) := by
  let w := hG.isHermitian.eigenvalues
  let v : (X × B) → (X × B) → ℂ := fun j => ⇑(hG.isHermitian.eigenvectorBasis j)
  let R := fun j => Matrix.vecMulVec (v j) (star (v j))
  let r : (X × B) → X → ℝ := fun j x => ∑ b, Complex.normSq (v j (x,b))
  have hw := spectral_prob hG htr
  have hv (j : X × B) : ∑ i, star (v j i) * v j i = 1 := by
    change star (⇑(hG.isHermitian.eigenvectorBasis j)) ⬝ᵥ
      ⇑(hG.isHermitian.eigenvectorBasis j) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hG.isHermitian.eigenvectorBasis.orthonormal.1 j]
    norm_num
  have hdecomp : G = ∑ j, w j • R j := by
    ext a b
    conv_lhs => rw [hG.isHermitian.spectral_theorem,
      Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, w, v, R]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hstates (j : X × B) : (R j).PosSemidef ∧ (R j).trace = 1 := by
    refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
    change (∑ i, v j i * star (v j i)) = 1
    simpa only [mul_comm] using hv j
  have hr (j : X × B) : (∀ x, 0 ≤ r j x) ∧ ∑ x, r j x = 1 := by
    refine ⟨fun x => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _, ?_⟩
    have hC : ((∑ x, r j x : ℝ) : ℂ) = 1 := by
      simpa only [r, Complex.ofReal_sum, Fintype.sum_prod_type,
        Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using hv j
    exact_mod_cast hC
  have hD (j : X × B) :
      (diagonal (fun x => (r j x : ℂ))).PosSemidef ∧
        (diagonal (fun x => (r j x : ℂ))).trace = 1 := by
    refine ⟨Matrix.PosSemidef.diagonal (fun x => by
      simpa [Complex.le_def] using (hr j).1 x), ?_⟩
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, (hr j).2, Complex.ofReal_one]
  have hmass (x : X) : (∑ j, w j * r j x) = (∑ b, G (x,b) (x,b)).re := by
    rw [hdecomp]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      R, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum, r]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have hDsum : (∑ j, w j • diagonal (fun x => (r j x : ℂ))) =
      diagonal (fun x => (((∑ b, G (x,b) (x,b)).re : ℝ) : ℂ)) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
        Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, hmass]
    · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]
  have hc := (actual_pinching_gap_laws i₀).1.map_sum_le
    (t := Finset.univ) (w := w) (p := R)
    (fun j _ => hw.1 j) hw.2 (fun j _ => hstates j)
  have hd := ConcaveOn.le_map_sum (matrix_subentropy_concave x₀)
    (t := Finset.univ) (w := w) (p := fun j => diagonal (fun x => (r j x : ℂ)))
    (fun j _ => hw.1 j) hw.2 (fun j _ => hD j)
  change matrixSubentropy (blockPinch (∑ j, w j • R j)) -
    matrixSubentropy (∑ j, w j • R j) ≤
      ∑ j, w j * (matrixSubentropy (blockPinch (R j)) - matrixSubentropy (R j)) at hc
  rw [← hdecomp] at hc
  rw [hDsum] at hd
  calc
    _ ≤ ∑ j, w j * (matrixSubentropy (blockPinch (R j)) - matrixSubentropy (R j)) := hc
    _ = ∑ j, w j * matrixSubentropy (diagonal (fun x => (r j x : ℂ))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(pure_block_pinching (v j) (hv j)).1]
    _ ≤ _ := hd

private theorem cq_blocks_upper (Y : X → Matrix B B ℂ)
    (hY : ∀ x, (Y x).PosSemidef) (htr : (∑ x, Y x).trace = 1)
    (x₀ : X) (i₀ : X × B) :
    matrixSubentropy (fun i j : X × B => if i.1 = j.1 then Y i.1 i.2 j.2 else 0) ≤
      matrixSubentropy (∑ x, Y x) +
        matrixSubentropy (diagonal (fun x => ((Y x).trace.re : ℂ))) := by
  let V : Matrix B (X × B) ℂ := fun b i => CFC.sqrt (Y i.1) b i.2
  have hs (x : X) : (CFC.sqrt (Y x)).conjTranspose = CFC.sqrt (Y x) := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg (Y x)).isSelfAdjoint.star_eq
  have hsq (x : X) : CFC.sqrt (Y x) * CFC.sqrt (Y x) = Y x :=
    CFC.sqrt_mul_sqrt_self _ (hY x).nonneg
  have hrow : V * V.conjTranspose = ∑ x, Y x := by
    ext b d
    simp only [Matrix.mul_apply, V, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro x _
    change (CFC.sqrt (Y x) * (CFC.sqrt (Y x)).conjTranspose) b d = Y x b d
    rw [hs, hsq]
  have hp : blockPinch (V.conjTranspose * V) =
      (fun i j : X × B => if i.1 = j.1 then Y i.1 i.2 j.2 else 0) := by
    ext i j
    by_cases hij : i.1 = j.1
    · simp only [blockPinch, hij, ite_true]
      change ((CFC.sqrt (Y i.1)).conjTranspose * CFC.sqrt (Y j.1)) i.2 j.2 = _
      rw [← hij, hs, hsq]
    · simp [blockPinch, hij]
  have ht : (V.conjTranspose * V).trace = 1 := by
    rw [Matrix.trace_mul_comm, hrow, htr]
  have hm : (V.conjTranspose * V).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self V
  have hb := pinching_upper (V.conjTranspose * V) hm ht x₀ i₀
  have hmass (x : X) : (∑ b, (V.conjTranspose * V) (x,b) (x,b)).re =
      (Y x).trace.re := by
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    have h := congrArg (fun N : Matrix (X × B) (X × B) ℂ => N (x,b) (x,b)) hp
    simpa only [blockPinch, ite_true, Matrix.diag_apply] using h
  rw [hp, matrixSubentropy_rectangular_gram V, hrow] at hb
  simp_rw [hmass] at hb
  linarith

/-- Subentropy is subadditive for every finite bipartite density state. The right
partial trace retains the first system and the left partial trace retains the second. -/
theorem subentropy_subadditive (ρ : DensityState (X × B)) :
    subentropy ρ ≤ subentropy (marginalRight ρ) + subentropy (marginalLeft ρ) := by
  haveI : Nonempty (X × B) := by
    by_contra hn
    haveI : IsEmpty (X × B) := not_nonempty_iff.mp hn
    have ht := ρ.2.2
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.univ_eq_empty,
      Finset.sum_empty, zero_ne_one] using ht
  haveI : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty (X × B))).1⟩
  haveI : Nonempty B := ⟨(Classical.choice (inferInstance : Nonempty (X × B))).2⟩
  let M := CStarMatrix.ofMatrix.symm ρ.1
  have hM := density_posSemidef ρ
  let hR := (partialTraceRight_posSemidef hM).isHermitian
  let U : Matrix X X ℂ := hR.eigenvectorUnitary
  let K := localConjugate U M
  let Y := fun x : X => K.submatrix (fun b => (x,b)) (fun b => (x,b))
  have hb := eigenbasis_blocks M hM
  change K.PosSemidef ∧ K.trace = M.trace ∧
    (∀ x, (Y x).PosSemidef) ∧ (∑ x, Y x) = partialTraceLeft M ∧
    (∀ x, (Y x).trace = (hR.eigenvalues x : ℂ)) ∧
    blockPinch K = (fun i j => if i.1 = j.1 then Y i.1 i.2 j.2 else 0) at hb
  let x₀ : X := Classical.choice inferInstance
  let b₀ : B := Classical.choice inferInstance
  have hKt : K.trace = 1 := hb.2.1.trans ρ.2.2
  have hnonneg := (actual_pinching_gap_laws (x₀,b₀)).2 K hb.1 hKt
  have hYtr : (∑ x, Y x).trace = 1 := by
    rw [hb.2.2.2.1, trace_partialTraceLeft]
    exact ρ.2.2
  have hupper := cq_blocks_upper Y hb.2.2.1 hYtr x₀ (x₀,b₀)
  have hQK : matrixSubentropy K = matrixSubentropy M := by
    have hiso : (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ)).conjTranspose *
        (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ)) = 1 := by
      simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
      rw [show U * U.conjTranspose = 1 from Unitary.coe_mul_star_self hR.eigenvectorUnitary,
        Matrix.one_kronecker_one]
    simpa only [K, localConjugate, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] using
      matrixSubentropy_isometric_embedding M (U.conjTranspose ⊗ₖ (1 : Matrix B B ℂ)) hiso
  have hQA : matrixSubentropy (diagonal (fun x => (hR.eigenvalues x : ℂ))) =
      matrixSubentropy (partialTraceRight M) := by
    have hspectral : partialTraceRight M =
        U * diagonal (fun x => (hR.eigenvalues x : ℂ)) * U.conjTranspose := hR.spectral_theorem
    calc
      _ = matrixSubentropy (U * diagonal (fun x => (hR.eigenvalues x : ℂ)) *
          U.conjTranspose) := (matrixSubentropy_isometric_embedding _ U
            (Unitary.coe_star_mul_self hR.eigenvectorUnitary)).symm
      _ = _ := congrArg matrixSubentropy hspectral.symm
  have hweights : (fun x => ((Y x).trace.re : ℂ)) =
      fun x => (hR.eigenvalues x : ℂ) := by
    funext x
    rw [hb.2.2.2.2.1 x, Complex.ofReal_re]
  rw [← hb.2.2.2.2.2, hb.2.2.2.1, hweights, hQA] at hupper
  rw [hQK] at hnonneg
  change matrixSubentropy M ≤ matrixSubentropy (partialTraceRight M) +
    matrixSubentropy (partialTraceLeft M)
  linarith

end D5.S3.Quantum.Subentropy.Subadditivity
