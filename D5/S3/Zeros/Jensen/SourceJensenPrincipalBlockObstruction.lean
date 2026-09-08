/- GID: D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction
   mirror-E: none(waiver:universal-symbolic-obstruction)
   anchors: []
   utility: none
   digest: Fixed literal Jensen coefficients obstruct unchanged positive principal extensions. -/

import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import D5.S3.QuantumStates.ZeroWeightSupportFace
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourTraceExtension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.SourceJensenPrincipalBlockObstruction

open Polynomial MeasureTheory
open scoped ComplexOrder
open NormalizedJensenDegreeLowering SourceThetaMomentBounds
open D5.S3.QuantumStates.ZeroWeightSupportFace
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourTraceExtension

/-- The constant, fixed linear, vanished next, and leading source coefficients. -/
theorem source_jensen_coeff_edges (d : ℕ) (hd : 1 ≤ d) :
    (sourceJensenPolynomial d).coeff 0 = (sourceThetaCoefficient 0 : ℂ) ∧
    (sourceJensenPolynomial d).coeff 1 = (sourceThetaCoefficient 1 : ℂ) ∧
    (sourceJensenPolynomial d).coeff (d + 1) = 0 ∧
    (sourceJensenPolynomial d).coeff d =
      (d.factorial : ℂ) / (d : ℂ) ^ d * (sourceThetaCoefficient d : ℂ) := by
  have hc (k : ℕ) : (sourceJensenPolynomial d).coeff k =
      if k ≤ d then (d.descFactorial k : ℂ) / (d : ℂ) ^ k *
        (sourceThetaCoefficient k : ℂ) else 0 := by
    simp only [sourceJensenPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
    simp [Finset.mem_range]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp [hc, hd, hd0, Nat.descFactorial_self]

/-- Exact matching fixes both normalization and trace, and hence all literal signs. -/
theorem source_jensen_matching_normalization (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℂ) (hd : 1 ≤ d)
    (hmatch : Matrix.det (1 + (X : ℂ[X]) • K.map C) = sourceJensenPolynomial d) :
    sourceThetaCoefficient 0 = 1 ∧ K.trace = (sourceThetaCoefficient 1 : ℂ) ∧
      (∀ k : ℕ, 0 < sourceThetaCoefficient k) := by
  have hz : (Matrix.det (1 + (X : ℂ[X]) • K.map C)).coeff 0 = 1 := by
    rw [Matrix.det_one_add_X_smul]
    simp
  rw [hmatch, (source_jensen_coeff_edges d hd).1] at hz
  have h0 : sourceThetaCoefficient 0 = 1 := by exact_mod_cast hz
  refine ⟨h0, ?_, (source_theta_normalization h0).2.2.2⟩
  rw [← Matrix.coeff_det_one_add_X_smul_one K, hmatch]
  exact (source_jensen_coeff_edges d hd).2.1

/-- Unit source normalization makes the actual leading coefficient strictly positive. -/
theorem source_jensen_leading_coefficient_pos (d : ℕ) (hd : 1 ≤ d)
    (h0 : sourceThetaCoefficient 0 = 1) : 0 < (sourceJensenPolynomial d).coeff d := by
  rw [(source_jensen_coeff_edges d hd).2.2.2]
  have hreal : 0 < (d.factorial : ℝ) / (d : ℝ) ^ d * sourceThetaCoefficient d := by
    exact mul_pos (div_pos (by positivity) (pow_pos (by exact_mod_cast (show 0 < d by omega)) _))
      ((source_theta_normalization h0).2.2.2 d)
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_natCast] using Complex.zero_lt_real.mpr hreal

/-- An arbitrary fixed principal inclusion with equal traces has only a zero extension. -/
theorem fixed_trace_principal_collapse (d : ℕ)
    (K : Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (e : Fin d → Fin (d + 1)) (he : Function.Injective e) (hH : H.PosSemidef)
    (hsub : H.submatrix e e = K) (htrace : H.trace = K.trace) :
    ∃ q : (Fin d ⊕ Fin 1) ≃ Fin (d + 1), (∀ i, q (.inl i) = e i) ∧
      H (q (.inr 0)) (q (.inr 0)) = 0 ∧
      (∀ i, H (e i) (q (.inr 0)) = 0 ∧ H (q (.inr 0)) (e i) = 0) ∧
      H.submatrix q q = Matrix.fromBlocks K 0 0 (0 : Matrix (Fin 1) (Fin 1) ℂ) ∧
      Matrix.det (1 + (X : ℂ[X]) • H.map C) =
        Matrix.det (1 + (X : ℂ[X]) • K.map C) := by
  classical
  let emb : Fin d ↪ Fin (d + 1) := ⟨e, he⟩
  let r : Fin d ≃ Set.range e := emb.toEquivRange
  have hcard : Fintype.card {j : Fin (d + 1) // j ∉ Set.range e} = 1 := by
    have hrange : Fintype.card (Set.range e) = d :=
      (Fintype.card_congr r).symm.trans (Fintype.card_fin d)
    rw [Fintype.card_subtype_compl, hrange, Fintype.card_fin]
    omega
  let c : Fin 1 ≃ {j : Fin (d + 1) // j ∉ Set.range e} :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  let q : (Fin d ⊕ Fin 1) ≃ Fin (d + 1) :=
    (Equiv.sumCongr r c).trans (Equiv.sumCompl (fun j => j ∈ Set.range e))
  have hq (i : Fin d) : q (.inl i) = e i := rfl
  let j : Fin (d + 1) := q (.inr 0)
  have hdiag : H j j = 0 := by
    have hs := q.sum_comp (fun i => H i i)
    simp only [Fintype.sum_sum_type, hq, Fin.sum_univ_one] at hs
    have hold : (∑ i : Fin d, H (e i) (e i)) = K.trace := by
      rw [← hsub]
      rfl
    rw [hold] at hs
    change K.trace + H j j = H.trace at hs
    rw [htrace] at hs
    exact add_left_cancel (hs.trans (add_zero K.trace).symm)
  let P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.diagonal (Pi.single j 1)
  have hstar : P.conjTranspose = P := by
    simp only [P, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [hi]
  have hidem : P * P = P := by
    dsimp [P]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = j <;> simp [hi]
  have hpTrace : Matrix.trace (H * P) = 0 := by
    simpa [P, Matrix.trace, Matrix.mul_diagonal, Pi.single_apply] using hdiag
  have hface := (zero_weight_support_face H P hH hstar hidem hpTrace).1
  have hrow (i : Fin (d + 1)) : H j i = 0 := by
    have hz := congrFun (congrFun hface.1 j) i
    simpa [P, Matrix.diagonal_mul] using hz
  have hcol (i : Fin (d + 1)) : H i j = 0 := by
    have hz := congrFun (congrFun hface.2 i) j
    simpa [P, Matrix.mul_diagonal] using hz
  have hblock : H.submatrix q q =
      Matrix.fromBlocks K 0 0 (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · simpa only [Matrix.submatrix_apply, hq, Matrix.fromBlocks_apply₁₁] using
        congrFun (congrFun hsub a) b
    · have hb : b = 0 := Subsingleton.elim _ _
      subst b
      simpa only [Matrix.submatrix_apply, hq, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply] using hcol (e a)
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      simpa only [Matrix.submatrix_apply, hq, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply] using hrow (e b)
    · have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = 0 := Subsingleton.elim _ _
      subst a
      subst b
      exact hdiag
  refine ⟨q, hq, hdiag, fun i => ⟨hcol (e i), hrow (e i)⟩, hblock, ?_⟩
  have hreindex : (1 + (X : ℂ[X]) • H.map C).submatrix q q =
      1 + (X : ℂ[X]) • (H.submatrix q q).map C := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, q.injective.eq_iff]
  rw [← Matrix.det_submatrix_equiv_self q, hreindex, hblock]
  have hpencil : 1 + (X : ℂ[X]) •
      (Matrix.fromBlocks K 0 0 (0 : Matrix (Fin 1) (Fin 1) ℂ)).map C =
      Matrix.fromBlocks (1 + (X : ℂ[X]) • K.map C) 0 0
        (1 : Matrix (Fin 1) (Fin 1) ℂ[X]) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply]
  rw [hpencil, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- Adjacent exact positive source models cannot have an unchanged principal block. -/
theorem source_jensen_principal_block_obstruction (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ (K : Matrix (Fin d) (Fin d) ℂ)
      (H : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (e : Fin d → Fin (d + 1)),
      K.PosSemidef ∧ H.PosSemidef ∧ Function.Injective e ∧ H.submatrix e e = K ∧
      Matrix.det (1 + (X : ℂ[X]) • K.map C) = sourceJensenPolynomial d ∧
      Matrix.det (1 + (X : ℂ[X]) • H.map C) = sourceJensenPolynomial (d + 1) := by
  rintro ⟨K, H, e, _, hH, he, hsub, hKmatch, hHmatch⟩
  have hKnorm := source_jensen_matching_normalization d K hd hKmatch
  have hHnorm := source_jensen_matching_normalization (d + 1) H (by omega) hHmatch
  obtain ⟨q, _, _, _, _, hdet⟩ := fixed_trace_principal_collapse d K H e he hH hsub
    (hHnorm.2.1.trans hKnorm.2.1.symm)
  have hpoly : sourceJensenPolynomial (d + 1) = sourceJensenPolynomial d :=
    hHmatch.symm.trans (hdet.trans hKmatch)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (d + 1)) hpoly
  rw [(source_jensen_coeff_edges d hd).2.2.1] at hcoeff
  exact (source_jensen_leading_coefficient_pos (d + 1) (by omega) hKnorm.1).ne' hcoeff

/-- Consequently no unchanged exact family exists at all positive degrees. -/
theorem source_jensen_unchanged_family_obstruction :
    ¬ ∃ (K : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ)
      (e : (d : ℕ) → Fin d → Fin (d + 1)),
      ∀ d : ℕ, 1 ≤ d → (K d).PosSemidef ∧ Function.Injective (e d) ∧
        (K (d + 1)).submatrix (e d) (e d) = K d ∧
        Matrix.det (1 + (X : ℂ[X]) • (K d).map C) = sourceJensenPolynomial d := by
  rintro ⟨K, e, h⟩
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  exact source_jensen_principal_block_obstruction 1 (by omega)
    ⟨K 1, K 2, e 1, h1.1, h2.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.2.2.2⟩

/-- Exact chain matching fixes the weight sum and the literal moment normalization. -/
theorem source_jensen_chain_matching (d : ℕ) (hd : 1 ≤ d)
    (w : Fin (2 * d - 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmatch : (forbiddenPartition w).map Complex.ofRealHom = sourceJensenPolynomial d) :
    sourceThetaCoefficient 0 = 1 ∧ (∑ i, w i) = sourceThetaCoefficient 1 ∧
      (∀ k : ℕ, 0 < sourceThetaCoefficient k) := by
  have hdet := (forbidden_neighbour_determinant hd w hw).1
  have hc0 : (forbiddenPartition w).coeff 0 = 1 := by
    rw [hdet, Matrix.det_one_add_X_smul]
    simp
  have hz := congrArg (fun p : ℂ[X] => p.coeff 0) hmatch
  rw [coeff_map, hc0, (source_jensen_coeff_edges d hd).1] at hz
  change (1 : ℂ) = (sourceThetaCoefficient 0 : ℂ) at hz
  have h0 : sourceThetaCoefficient 0 = 1 := by exact_mod_cast hz.symm
  refine ⟨h0, ?_, (source_theta_normalization h0).2.2.2⟩
  have hc1 : (forbiddenPartition w).coeff 1 = ∑ i, w i := by
    rw [hdet, Matrix.coeff_det_one_add_X_smul_one]
    exact (lower_bidiagonal_trace_weights d hd w hw).2
  have h1 := congrArg (fun p : ℂ[X] => p.coeff 1) hmatch
  rw [coeff_map, hc1, (source_jensen_coeff_edges d hd).2.1] at h1
  change ((∑ i, w i : ℝ) : ℂ) = (sourceThetaCoefficient 1 : ℂ) at h1
  exact_mod_cast h1

/-- Appending unchanged nonnegative weights cannot preserve the next exact source model. -/
theorem source_jensen_unchanged_weights_obstruction (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ (w : Fin (2 * d - 1) → ℝ) (u : Fin (2 * (d + 1) - 1) → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ u i) ∧
      (∀ i : Fin (2 * d - 1), u ⟨i.val, by omega⟩ = w i) ∧
      (forbiddenPartition w).map Complex.ofRealHom = sourceJensenPolynomial d ∧
      (forbiddenPartition u).map Complex.ofRealHom = sourceJensenPolynomial (d + 1) := by
  rintro ⟨w, u, hw, hu, hprefix, hmatchw, hmatchu⟩
  have hnormw := source_jensen_chain_matching d hd w hw hmatchw
  have hnormu := source_jensen_chain_matching (d + 1) (by omega) u hu hmatchu
  obtain ⟨_, _, _, hpartition⟩ := unchanged_weights_zero_append d hd w u hu hprefix
    (hnormu.2.1.trans hnormw.2.1.symm)
  have hpoly : sourceJensenPolynomial (d + 1) = sourceJensenPolynomial d :=
    hmatchu.symm.trans ((congrArg (Polynomial.map Complex.ofRealHom) hpartition).trans hmatchw)
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff (d + 1)) hpoly
  rw [(source_jensen_coeff_edges d hd).2.2.1] at hcoeff
  exact (source_jensen_leading_coefficient_pos (d + 1) (by omega) hnormw.1).ne' hcoeff

end D5.S3.Zeros.Jensen.SourceJensenPrincipalBlockObstruction
