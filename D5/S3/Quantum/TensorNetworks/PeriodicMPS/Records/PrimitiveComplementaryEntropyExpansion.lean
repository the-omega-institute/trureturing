/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveHiddenLabelEntropy, lake/module/D5.S3.SpectralTopology.HermitianEigenvaluePerturbation]
   utility: none
   digest: Exact complementary conditional entropy asymptotic for the primitive periodic collision. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveRecordLeadingCoefficient
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records.PrimitiveHiddenLabelEntropy
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Calculus.MeanValue

/-!
The subdominant transfer modes decay at a base strictly below the quadratic
entropy scale. Rectangular Grams reduce the physical conditional entropy to
eight eigenvalues, and Weyl's inequality replaces the actual Gram by the
phase-adjusted leading path. The checked commutation reduces that path to
scalar Taylor expansions.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PrimitiveComplementaryEntropyExpansion

open Matrix Complex Filter Polynomial
open scoped ComplexOrder CStarAlgebra Matrix MatrixOrder Topology
open PeriodicMPSPrimitiveCollision
open PeriodicMPSParentIntersection (Word)
open ComplementaryRecordRate
open PrimitiveRecordLeadingCoefficient
open D5.S3.SpectralTopology.HermitianEigenvaluePerturbation (abs_eigenvalues0_sub_le_of_entry_le)

noncomputable section

abbrev VisiblePair := Fin 2 × Fin 2
abbrev BlockIndex := VisiblePair ⊕ VisiblePair

def collisionBeta : ℝ := 8 / Real.sqrt 200

private theorem beta_pos : 0 < collisionBeta := by
  unfold collisionBeta
  positivity

private theorem alpha_pos : 0 < collisionAlpha := by
  unfold collisionAlpha
  positivity

theorem collisionBeta_lt_alpha_sq : collisionBeta < collisionAlpha ^ 2 := by
  have hs : (6 : ℝ) ≤ Real.sqrt 41 :=
    (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  have ht : (10 : ℝ) < Real.sqrt 200 :=
    (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]; norm_num)
  have hb : collisionBeta < 4 / 5 := by
    rw [collisionBeta, div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    linarith
  have ha : (9 / 10 : ℝ) ≤ collisionAlpha := by unfold collisionAlpha; linarith
  exact hb.trans_le ((by norm_num : (4 / 5 : ℝ) ≤ (9 / 10) ^ 2).trans
    (pow_le_pow_left₀ (by norm_num) ha 2))

theorem norm_collisionPhaseRate : ‖collisionPhaseRate‖ = collisionAlpha := by
  rw [collisionPhaseRate, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_eq_iff (Real.sqrt_pos.mpr (by norm_num)).ne').mpr
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg alpha_pos.le (Real.sqrt_nonneg _))).mp
  rw [Complex.sq_norm, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200),
    collisionLambda_eq, collisionAlpha]
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring

private def mode (k : VisiblePair) : ℂ :=
  collisionMixedEigenvalues k / (Real.sqrt 200 : ℂ)

private theorem mode_bound (k : VisiblePair) (hk : k ≠ (0, 0)) :
    ‖mode k‖ ≤ collisionBeta := by
  rw [mode, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), collisionBeta]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm]
  have hs : (6 : ℝ) ≤ Real.sqrt 41 :=
    (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
      (by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]; norm_num)
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact (hk rfl).elim
  · change Complex.normSq ((1 + I) * (3 + -(Real.sqrt 41 : ℂ))) ≤ _
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 41)]
  · change Complex.normSq (8 * I) ≤ _
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  · change Complex.normSq (-8 : ℂ) ≤ _
    norm_num [Complex.normSq_apply]

private theorem dominant_term (m : ℕ) (p q : VisiblePair) :
    collisionCrossWeight p q (0, 0) * mode (0, 0) ^ m / 200 =
      collisionPhaseRate ^ (2 + m) * Sstar p q := by
  have hsq : collisionPhaseRate ^ 2 = collisionLambda ^ 2 / 200 := by
    rw [collisionPhaseRate, div_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 200)]
    norm_num
  rw [← Sstar_mul_lambda_sq, show mode (0, 0) = collisionPhaseRate from rfl, pow_add, hsq]
  ring

/-- The exact contraction with the dominant mode removed. -/
theorem collision_cross_remainder (m : ℕ) (p q : VisiblePair) :
    collisionNormalizedCross m p q - collisionPhaseRate ^ (2 + m) * Sstar p q =
      (∑ k ∈ (Finset.univ.erase ((0, 0) : VisiblePair)),
        collisionCrossWeight p q k * mode k ^ m) / 200 := by
  rw [collision_cross_contraction, ← dominant_term]
  change (∑ k, collisionCrossWeight p q k * mode k ^ m) / 200 -
    collisionCrossWeight p q (0, 0) * mode (0, 0) ^ m / 200 = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ ((0, 0) : VisiblePair)),
    add_div, add_sub_cancel_right]

/-- A single constant bounds all sixteen entries at the faster transfer rate. -/
theorem collision_cross_exponential_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (p q : VisiblePair),
      ‖collisionNormalizedCross m p q - collisionPhaseRate ^ (2 + m) * Sstar p q‖ ≤
        C * collisionBeta ^ (2 + m) := by
  let modes := Finset.univ.erase ((0, 0) : VisiblePair)
  let weight := fun p q : VisiblePair =>
    (∑ k ∈ modes, ‖collisionCrossWeight p q k‖) / 200
  let C₀ := ∑ p : VisiblePair, ∑ q : VisiblePair, weight p q
  have hw (p q : VisiblePair) : 0 ≤ weight p q := by dsimp [weight]; positivity
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => hw p q
  refine ⟨C₀ / collisionBeta ^ 2, by positivity, fun m p q => ?_⟩
  have hwC : weight p q ≤ C₀ := calc
    _ ≤ ∑ j : VisiblePair, weight p j :=
      Finset.single_le_sum (fun j _ => hw p j) (Finset.mem_univ q)
    _ ≤ _ := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => hw i j) (Finset.mem_univ p)
  rw [collision_cross_remainder, norm_div,
    show ‖(200 : ℂ)‖ = (200 : ℝ) by rw [← Complex.ofReal_ofNat, Complex.norm_real]; norm_num]
  change ‖∑ k ∈ modes, collisionCrossWeight p q k * mode k ^ m‖ / 200 ≤ _
  calc
    _ ≤ (∑ k ∈ modes, ‖collisionCrossWeight p q k‖ * collisionBeta ^ m) / 200 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (mode_bound k (Finset.mem_erase.mp hk).1) m)
        (norm_nonneg _)
    _ = weight p q * collisionBeta ^ m := by rw [← Finset.sum_mul]; unfold weight; ring
    _ ≤ C₀ * collisionBeta ^ m := mul_le_mul_of_nonneg_right hwC (pow_nonneg beta_pos.le _)
    _ = _ := by rw [pow_add]; field_simp [beta_pos.ne']

section Entropy

variable {i j : Type*} [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]

/-- Spectral von Neumann entropy. A zero eigenvalue contributes zero. -/
def matrixEntropy (A : Matrix i i ℂ) : ℝ :=
  (A.charpoly.roots.map (fun z : ℂ => Real.negMulLog z.re)).sum

theorem matrixEntropy_eq_sum (A : Matrix i i ℂ) (hA : A.IsHermitian) :
    matrixEntropy A = ∑ k, Real.negMulLog (hA.eigenvalues₀ k) := by
  rw [matrixEntropy, hA.roots_charpoly_eq_eigenvalues₀]
  simp [Function.comp_def, List.sum_ofFn]

theorem matrixEntropy_eq_density
    (P : D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState i) :
    matrixEntropy (PrimitiveHiddenLabelEntropy.matrix P) =
      PrimitiveHiddenLabelEntropy.entropy P := by
  let A := PrimitiveHiddenLabelEntropy.matrix P
  have hA : A.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm P.2.1)).isHermitian
  have hlog : CStarMatrix.ofMatrix (cfc Real.log A) = CFC.log P.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log A
      (A.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hA
      (IsSelfAdjoint.of_nonneg P.2.1)
  change matrixEntropy A = -(Matrix.trace (P.1 * CFC.log P.1)).re
  rw [← hlog]
  change matrixEntropy A = -(A * cfc Real.log A).trace.re
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id ℝ A hA
  calc
    _ = -(cfc (fun x : ℝ => x * Real.log x) A).trace.re := by
      rw [D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum A hA, matrixEntropy,
        hA.roots_charpoly_eq_eigenvalues]
      simp [Real.negMulLog, Finset.sum_neg_distrib]
    _ = _ := by
      rw [cfc_mul (fun x : ℝ => x) Real.log A (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _), hid]

theorem matrixEntropy_gram (W : Matrix i j ℂ) :
    matrixEntropy (Wᴴ * W) = matrixEntropy (W * Wᴴ) := by
  have h := congrArg (fun p : Polynomial ℂ => (p.roots.map (fun z => Real.negMulLog z.re)).sum)
    (Matrix.charpoly_mul_comm' Wᴴ W)
  simpa [matrixEntropy, Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero,
    Polynomial.roots_X_pow, Multiset.nsmul_singleton, Multiset.map_replicate] using h

@[simp] theorem matrixEntropy_transpose (A : Matrix i i ℂ) :
    matrixEntropy Aᵀ = matrixEntropy A := by simp only [matrixEntropy, Matrix.charpoly_transpose]

@[simp] theorem matrixEntropy_reindex (e : i ≃ j) (A : Matrix i i ℂ) :
    matrixEntropy (Matrix.reindex e e A) = matrixEntropy A := by
  simp only [matrixEntropy, Matrix.charpoly_reindex]

theorem matrixEntropy_blocks (A : Matrix i i ℂ) (B : Matrix j j ℂ) :
    matrixEntropy (fromBlocks A 0 0 B) = matrixEntropy A + matrixEntropy B := by
  simp [matrixEntropy, Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero]

end Entropy

/-- The row Gram with common visible diagonal block and a variable cross block. -/
def collisionGram (Z : Matrix VisiblePair VisiblePair ℂ) : Matrix BlockIndex BlockIndex ℂ :=
  (1 / 2 : ℝ) • fromBlocks collisionMarginal Z Zᴴ collisionMarginal

private def scaledFlattening (b : Bool) (m : ℕ) : Matrix VisiblePair (Word m) ℂ :=
  (Real.sqrt (1 / 2 : ℝ)) • collisionFlattening b m

private theorem scaled_mul_adjoint (m : ℕ) (b c : Bool) :
    scaledFlattening b m * (scaledFlattening c m)ᴴ =
      (1 / 2 : ℝ) • (collisionFlattening b m * (collisionFlattening c m)ᴴ) := by
  simp only [scaledFlattening, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (by norm_num : 0 ≤ (1 / 2 : ℝ))]

private theorem scaled_adjoint_mul (m : ℕ) (b : Bool) :
    (scaledFlattening b m)ᴴ * scaledFlattening b m =
      (1 / 2 : ℝ) • environmentGram (collisionFlattening b m) := by
  simp only [scaledFlattening, environmentGram, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt (by norm_num : 0 ≤ (1 / 2 : ℝ))]

/-- The conditional entropy of the fair c-q label and its literal complementary partial trace. -/
def collisionComplementaryEntropy (m : ℕ) : ℝ :=
  let E₀ := environmentDensity (collisionFlattening false m)
  let E₁ := environmentDensity (collisionFlattening true m)
  matrixEntropy (fromBlocks ((1 / 2 : ℝ) • E₀) 0 0 ((1 / 2 : ℝ) • E₁)) -
    matrixEntropy ((1 / 2 : ℝ) • (E₀ + E₁))

/-- Both parts of the c-q conditional entropy reduce to eight-dimensional row Grams. -/
theorem collisionComplementaryEntropy_eq_gram (m : ℕ) (hm : 5 ≤ m) :
    collisionComplementaryEntropy m =
      matrixEntropy (collisionGram 0) -
        matrixEntropy (collisionGram (collisionNormalizedCross m)) := by
  let X := scaledFlattening false m
  let Y := scaledFlattening true m
  have hlabel (b : Bool) : matrixEntropy ((1 / 2 : ℝ) •
      environmentDensity (collisionFlattening b m)) =
      matrixEntropy ((1 / 2 : ℝ) • collisionMarginal) := by
    rw [environmentDensity_eq_transpose, ← Matrix.transpose_smul, matrixEntropy_transpose,
      ← scaled_adjoint_mul, matrixEntropy_gram, scaled_mul_adjoint,
      collisionFlattening_common_visible b m hm]
  have hmix :
      (1 / 2 : ℝ) • (environmentDensity (collisionFlattening false m) +
        environmentDensity (collisionFlattening true m)) = ((fromRows X Y)ᴴ * fromRows X Y)ᵀ := by
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
      X, Y, scaled_adjoint_mul, Matrix.transpose_add, Matrix.transpose_smul,
      ← environmentDensity_eq_transpose, smul_add]
  have hcross : collisionFlattening true m * (collisionFlattening false m)ᴴ =
      (collisionNormalizedCross m)ᴴ := by
    rw [← collisionFlattening_cross, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hrow : fromRows X Y * (fromRows X Y)ᴴ = collisionGram (collisionNormalizedCross m) := by
    simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols,
      X, Y, scaled_mul_adjoint, collisionFlattening_common_visible _ m hm,
      collisionFlattening_cross, hcross, collisionGram, Matrix.fromBlocks_smul]
  have hbase : matrixEntropy (collisionGram 0) =
      matrixEntropy ((1 / 2 : ℝ) • collisionMarginal) +
        matrixEntropy ((1 / 2 : ℝ) • collisionMarginal) := by
    simp only [collisionGram, Matrix.conjTranspose_zero, Matrix.fromBlocks_smul, smul_zero,
      matrixEntropy_blocks]
  rw [collisionComplementaryEntropy, matrixEntropy_blocks, hlabel, hlabel, hmix,
    matrixEntropy_transpose, matrixEntropy_gram, hrow, hbase]

private def blockEquiv : BlockIndex ≃ Fin 8 :=
  (Equiv.sumCongr (finProdFinEquiv : VisiblePair ≃ Fin 4)
    (finProdFinEquiv : VisiblePair ≃ Fin 4)).trans finSumFinEquiv

private def gram8 (Z : Matrix VisiblePair VisiblePair ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.reindex blockEquiv blockEquiv (collisionGram Z)

private theorem collisionGram_hermitian (Z : Matrix VisiblePair VisiblePair ℂ) :
    (collisionGram Z).IsHermitian := by
  unfold collisionGram
  exact (collision_marginal_posDef.isHermitian.fromBlocks (rfl : Zᴴ = Zᴴ)
    collision_marginal_posDef.isHermitian).smul
      (show IsSelfAdjoint (1 / 2 : ℝ) by simp [IsSelfAdjoint])

private theorem gram8_hermitian (Z : Matrix VisiblePair VisiblePair ℂ) : (gram8 Z).IsHermitian :=
  (collisionGram_hermitian Z).submatrix blockEquiv.symm

private theorem collisionGram_zero_posDef : (collisionGram 0).PosDef := by
  let R := collisionMarginal
  have hR := collision_marginal_posDef
  have hblock : (fromBlocks R (0 : Matrix VisiblePair VisiblePair ℂ) 0 R).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hR.isHermitian.fromBlocks (by simp)
      hR.isHermitian, ?_⟩
    intro x hx
    let x₀ := x ∘ Sum.inl
    let x₁ := x ∘ Sum.inr
    have heq : star x ⬝ᵥ (fromBlocks R (0 : Matrix VisiblePair VisiblePair ℂ) 0 R *ᵥ x) =
        star x₀ ⬝ᵥ (R *ᵥ x₀) + star x₁ ⬝ᵥ (R *ᵥ x₁) := by
      rw [fromBlocks_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, x₀, x₁]
    rw [heq]
    by_cases h : x₀ = 0
    · have h₁ : x₁ ≠ 0 := by
        intro h'
        apply hx
        funext k
        cases k with
        | inl k => exact congrFun h k
        | inr k => exact congrFun h' k
      simpa [h] using hR.dotProduct_mulVec_pos h₁
    · exact add_pos_of_pos_of_nonneg (hR.dotProduct_mulVec_pos h)
        (hR.posSemidef.dotProduct_mulVec_nonneg x₁)
  simpa [collisionGram, R] using hblock.smul (by norm_num : 0 < (1 / 2 : ℝ))

private theorem gram8_zero_posDef : (gram8 0).PosDef :=
  collisionGram_zero_posDef.submatrix blockEquiv.symm.injective

private theorem gram8_entry_bound {X Y : Matrix VisiblePair VisiblePair ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ p q, ‖X p q - Y p q‖ ≤ ε) (i j : Fin 8) :
    ‖gram8 X i j - gram8 Y i j‖ ≤ ε := by
  change ‖collisionGram X (blockEquiv.symm i) (blockEquiv.symm j) -
    collisionGram Y (blockEquiv.symm i) (blockEquiv.symm j)‖ ≤ ε
  have half (z w : ℂ) (hw : ‖z - w‖ ≤ ε) :
      ‖(1 / 2 : ℝ) • z - (1 / 2 : ℝ) • w‖ ≤ ε := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith
  rcases blockEquiv.symm i with p | p <;> rcases blockEquiv.symm j with q | q
  · simpa [collisionGram] using hε
  · exact half _ _ (h p q)
  · apply half
    simpa only [Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, ← star_sub, norm_star]
      using h q p
  · simpa [collisionGram] using hε

private theorem negMulLog_lipschitz {a b : ℝ} (ha : 0 < a) {x y : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |Real.negMulLog y - Real.negMulLog x| ≤
      (|Real.log a| + |Real.log b| + 1) * |y - x| := by
  have hd (z : ℝ) (hz : z ∈ Set.Icc a b) :=
    Real.hasDerivAt_negMulLog (ha.trans_le hz.1).ne'
  have hbound (z : ℝ) (hz : z ∈ Set.Icc a b) :
      ‖deriv Real.negMulLog z‖ ≤ |Real.log a| + |Real.log b| + 1 := by
    rw [(hd z hz).deriv, Real.norm_eq_abs, abs_le]
    have hlo := Real.log_le_log ha hz.1
    have hhi := Real.log_le_log (ha.trans_le hz.1) hz.2
    constructor
    · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]
    · linarith [neg_le_abs (Real.log a), abs_nonneg (Real.log b)]
  simpa only [Real.norm_eq_abs] using
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hd z hz).differentiableAt) hbound hx hy

/-- A local fixed-size entropy Lipschitz bound around a positive definite reference Gram. -/
theorem entropy_stability_at_posDef (D : Matrix (Fin 8) (Fin 8) ℂ) (hD : D.PosDef) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      ∀ (A B : Matrix (Fin 8) (Fin 8) ℂ), A.IsHermitian → B.IsHermitian →
        (∀ i j, ‖A i j - D i j‖ ≤ δ) → (∀ i j, ‖B i j - D i j‖ ≤ δ) →
        ∀ ε : ℝ, (∀ i j, ‖B i j - A i j‖ ≤ ε) →
          |matrixEntropy B - matrixEntropy A| ≤ K * ε := by
  let e := hD.isHermitian.eigenvalues₀
  have he (k : Fin (Fintype.card (Fin 8))) : 0 < e k := by
    let k' : Fin 8 := Fintype.equivOfCardEq (Fintype.card_fin 8) k
    simpa [e, k', Matrix.IsHermitian.eigenvalues] using hD.eigenvalues_pos k'
  have hnonempty : (Finset.univ : Finset (Fin (Fintype.card (Fin 8)))).Nonempty :=
    ⟨⟨0, by simp⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ e hnonempty
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ e hnonempty
  let δ := e lo / 16
  let a := e lo / 2
  let b := e hi + e lo / 2
  let L := |Real.log a| + |Real.log b| + 1
  have ha : 0 < a := div_pos (he lo) (by norm_num : (0 : ℝ) < 2)
  have hδ : 0 < δ := div_pos (he lo) (by norm_num : (0 : ℝ) < 16)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨δ, 64 * L, hδ, by positivity, ?_⟩
  intro A B hA hB hAD hBD ε hAB
  have hmem {M : Matrix (Fin 8) (Fin 8) ℂ} (hM : M.IsHermitian)
      (hMD : ∀ i j, ‖M i j - D i j‖ ≤ δ) (k : Fin (Fintype.card (Fin 8))) :
      hM.eigenvalues₀ k ∈ Set.Icc a b := by
    have hd := abs_eigenvalues0_sub_le_of_entry_le hD.isHermitian hM hMD k
    change |hM.eigenvalues₀ k - e k| ≤ 8 * δ at hd
    have hmin := hlo k (Finset.mem_univ k)
    have hmax := hhi k (Finset.mem_univ k)
    rcases abs_le.mp hd with ⟨h₁, h₂⟩
    constructor <;> dsimp only [a, b, δ] at * <;> linarith
  rw [matrixEntropy_eq_sum B hB, matrixEntropy_eq_sum A hA, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k : Fin (Fintype.card (Fin 8)),
        |Real.negMulLog (hB.eigenvalues₀ k) - Real.negMulLog (hA.eigenvalues₀ k)| := by
          simpa only [Real.norm_eq_abs] using (norm_sum_le Finset.univ
            (fun k => Real.negMulLog (hB.eigenvalues₀ k) - Real.negMulLog (hA.eigenvalues₀ k)))
    _ ≤ ∑ _k : Fin (Fintype.card (Fin 8)), L * (8 * ε) := by
      apply Finset.sum_le_sum
      intro k _
      exact (negMulLog_lipschitz ha (hmem hA hAD k) (hmem hB hBD k)).trans
        (mul_le_mul_of_nonneg_left (abs_eigenvalues0_sub_le_of_entry_le hA hB hAB k) hL)
    _ = _ := by simp <;> ring

private theorem collisionGram_phase (Z : Matrix VisiblePair VisiblePair ℂ)
    (u : ℂ) (hu : ‖u‖ = 1) : matrixEntropy (collisionGram (u • Z)) =
      matrixEntropy (collisionGram Z) := by
  let U : Matrix BlockIndex BlockIndex ℂ :=
    fromBlocks (u • (1 : Matrix VisiblePair VisiblePair ℂ)) 0 0 1
  let V : Matrix BlockIndex BlockIndex ℂ :=
    fromBlocks (star u • (1 : Matrix VisiblePair VisiblePair ℂ)) 0 0 1
  have huv : starRingEnd ℂ u * u = 1 := by
    rw [Complex.conj_mul', hu]
    norm_num
  have huv' : u * starRingEnd ℂ u = 1 := by rwa [mul_comm]
  have hVU : V * U = 1 := by
    simp [U, V, Matrix.fromBlocks_multiply, smul_smul, huv']
  have heq : U * collisionGram Z * V = collisionGram (u • Z) := by
    simp [U, V, collisionGram, Matrix.fromBlocks_multiply, smul_smul, huv,
      Matrix.conjTranspose_smul]
  have hpoly : (collisionGram (u • Z)).charpoly = (collisionGram Z).charpoly := by
    rw [← heq, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  unfold matrixEntropy
  rw [hpoly]

/-- The commuting model path has the exact leading cross block at real amplitude `t`. -/
def collisionGramPath (t : ℝ) : Matrix BlockIndex BlockIndex ℂ :=
  collisionGram (t • Sstar)

private theorem collisionGramPath_phase (m : ℕ) :
    matrixEntropy (collisionGram (collisionPhaseRate ^ (2 + m) • Sstar)) =
      matrixEntropy (collisionGramPath (collisionAlpha ^ (2 + m))) := by
  let z := collisionPhaseRate ^ (2 + m)
  let u := z / (‖z‖ : ℂ)
  have hz : ‖z‖ = collisionAlpha ^ (2 + m) := by
    change ‖collisionPhaseRate ^ (2 + m)‖ = _
    rw [norm_pow, norm_collisionPhaseRate]
  have hzpos : 0 < ‖z‖ := by rw [hz]; exact pow_pos alpha_pos _
  have hu : ‖u‖ = 1 := by
    change ‖z / (‖z‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hzpos.le, div_self hzpos.ne']
  have hzscale : u * (‖z‖ : ℂ) = z :=
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hzpos.ne')
  have hsmul : u • ((collisionAlpha ^ (2 + m) : ℝ) • Sstar) = z • Sstar := by
    rw [← hz, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    exact congrArg (fun w : ℂ => w • Sstar) hzscale
  calc
    _ = matrixEntropy (collisionGram (u • ((collisionAlpha ^ (2 + m) : ℝ) • Sstar))) :=
      congrArg (fun W => matrixEntropy (collisionGram W)) hsmul.symm
    _ = _ := collisionGram_phase _ u hu

private theorem pow_shift_tendsto {r : ℝ} (hr : 0 ≤ r) (h₁ : r < 1) :
    Tendsto (fun m : ℕ => r ^ (2 + m)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.add_comm] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr h₁).comp (tendsto_add_atTop_nat 2)

private theorem beta_lt_one : collisionBeta < 1 :=
  collisionBeta_lt_alpha_sq.trans (by
    simpa using (pow_lt_pow_left₀ collisionAlpha_lt_one alpha_pos.le (by decide : (2 : ℕ) ≠ 0)))

/-- The actual entropy and the commuting model entropy differ by an exponentially smaller term. -/
theorem collision_entropy_replacement_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ m : ℕ in atTop,
      |matrixEntropy (collisionGram (collisionNormalizedCross m)) -
        matrixEntropy (collisionGramPath (collisionAlpha ^ (2 + m)))| ≤
        K * collisionBeta ^ (2 + m) := by
  obtain ⟨C, hC, hcross⟩ := collision_cross_exponential_remainder
  obtain ⟨δ, L, hδ, hL, hstab⟩ := entropy_stability_at_posDef (gram8 0) gram8_zero_posDef
  let M := ∑ p : VisiblePair, ∑ q : VisiblePair, ‖Sstar p q‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  let Y := fun m : ℕ => collisionPhaseRate ^ (2 + m) • Sstar
  let E := fun m : ℕ => C * collisionBeta ^ (2 + m)
  let F := fun m : ℕ => M * collisionAlpha ^ (2 + m)
  have hE (m : ℕ) : 0 ≤ E m := mul_nonneg hC (pow_nonneg beta_pos.le _)
  have hF (m : ℕ) : 0 ≤ F m := mul_nonneg hM (pow_nonneg alpha_pos.le _)
  have hY (m : ℕ) (p q : VisiblePair) : ‖Y m p q‖ ≤ F m := by
    have hpq : ‖Sstar p q‖ ≤ M := calc
      _ ≤ ∑ j : VisiblePair, ‖Sstar p j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ q)
      _ ≤ _ := Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ p)
    simp only [Y, F, Matrix.smul_apply, norm_smul, norm_pow, norm_collisionPhaseRate]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpq (pow_nonneg alpha_pos.le (2 + m))
  have hlim : Tendsto (fun m => E m + F m) atTop (𝓝 0) := by
    simpa [E, F] using ((pow_shift_tendsto beta_pos.le beta_lt_one).const_mul C).add
      ((pow_shift_tendsto alpha_pos.le collisionAlpha_lt_one).const_mul M)
  refine ⟨L * C, mul_nonneg hL hC, ?_⟩
  filter_upwards [hlim.eventually_lt_const hδ] with m hm
  have hy0 : ∀ i j, ‖gram8 (Y m) i j - gram8 0 i j‖ ≤ δ := by
    intro i j
    have h := gram8_entry_bound (Y := 0) (hF m) (fun p q => by simpa using hY m p q) i j
    exact h.trans (by linarith [hE m])
  have hx0 : ∀ i j, ‖gram8 (collisionNormalizedCross m) i j - gram8 0 i j‖ ≤ δ := by
    intro i j
    apply (gram8_entry_bound (Y := 0) (add_nonneg (hE m) (hF m)) _ i j).trans hm.le
    intro p q
    simpa only [Matrix.zero_apply, sub_zero, sub_add_cancel] using
      (norm_add_le (collisionNormalizedCross m p q - Y m p q) (Y m p q)).trans
        (add_le_add (hcross m p q) (hY m p q))
  have h := hstab (gram8 (Y m)) (gram8 (collisionNormalizedCross m))
    (gram8_hermitian _) (gram8_hermitian _) hy0 hx0 (E m)
    (gram8_entry_bound (hE m) (hcross m))
  simpa only [gram8, matrixEntropy_reindex, Y, collisionGramPath_phase, E, mul_assoc] using h

/-- The normalized entropy replacement error vanishes at the target quadratic scale. -/
theorem collision_entropy_replacement :
    Tendsto (fun m : ℕ =>
      (matrixEntropy (collisionGramPath (collisionAlpha ^ (2 + m))) -
        matrixEntropy (collisionGram (collisionNormalizedCross m))) /
          collisionAlpha ^ (2 * (2 + m))) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := collision_entropy_replacement_bound
  have ht := pow_shift_tendsto (div_nonneg beta_pos.le (sq_nonneg collisionAlpha))
    ((div_lt_one (pow_pos alpha_pos 2)).mpr collisionBeta_lt_alpha_sq)
  apply squeeze_zero_norm' (a := fun m : ℕ => K * (collisionBeta / collisionAlpha ^ 2) ^ (2 + m))
  · filter_upwards [hK] with m hm
    rw [Real.norm_eq_abs, abs_div, abs_sub_comm, abs_of_pos (pow_pos alpha_pos _),
      div_pow, ← pow_mul, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hm (pow_nonneg alpha_pos.le _)
  · simpa using ht.const_mul K

open Asymptotics

/-- Scalar Taylor remainder along a line through a strictly positive eigenvalue. -/
private theorem negMulLog_quadratic (d h : ℝ) (hd : 0 < d) :
    (fun t : ℝ => Real.negMulLog (d + t * h) - Real.negMulLog d -
      t * (h * (-Real.log d - 1)) + t ^ 2 * (h ^ 2 / (2 * d))) =o[𝓝 0]
      (fun t => t ^ 2) := by
  let f := fun t : ℝ => Real.negMulLog (d + t * h)
  let g := fun t : ℝ => h * (-Real.log (d + t * h) - 1)
  let c := h ^ 2 / (2 * d)
  let s : Set ℝ := {t | 0 < d + t * h}
  let r := fun t : ℝ => f t - f 0 - t * g 0 + t ^ 2 * c
  let r' := fun t : ℝ => g t - g 0 + t * (2 * c)
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => d + t * h) h t :=
    (hasDerivAt_mul_const (x := t) h).const_add d
  have hg : HasDerivAt g (-(2 * c)) 0 := by
    have hlog := (hline 0).log (show d + 0 * h ≠ 0 by simpa using hd.ne')
    have hcoeff : h * -(h / (d + 0 * h)) = -(2 * c) := by
      dsimp only [c]
      rw [zero_mul, add_zero]
      field_simp [hd.ne'] <;> ring
    rw [← hcoeff]
    exact (hlog.neg.sub_const 1).const_mul h
  have hr' : r' =o[𝓝 0] (fun t => (t - 0) ^ 1) := by
    refine (hg.isLittleO.congr_left (fun t => ?_)).congr_right (fun t => by simp)
    dsimp [r']
    simp <;> ring
  have hr (t : ℝ) (ht : t ∈ s) : HasDerivWithinAt r (r' t) s t := by
    have hpos : 0 < d + t * h := ht
    have hf := (Real.hasDerivAt_negMulLog hpos.ne').comp t (hline t)
    have hf' : HasDerivAt f (g t) t := by
      simpa [f, g, Function.comp_def, mul_comm] using hf
    have hquad : HasDerivAt (fun x : ℝ => x ^ 2 * c) (t * (2 * c)) t := by
      refine ((hasDerivAt_pow 2 t).mul_const c).congr_deriv ?_
      norm_num <;> ring
    exact (((hf'.sub_const (f 0)).sub (hasDerivAt_mul_const (x := t) (g 0))).add
      hquad).hasDerivWithinAt
  have h0 : (0 : ℝ) ∈ s := by simpa [s] using hd
  have hs : Convex ℝ s := by
    intro x hx y hy a b ha hb hab
    change 0 < d + x * h at hx
    change 0 < d + y * h at hy
    change 0 < d + (a * x + b * y) * h
    have hab' : 0 < a ∨ 0 < b := by
      by_contra! h
      linarith [h.1, h.2]
    rw [show d + (a * x + b * y) * h = a * (d + x * h) + b * (d + y * h) by
      linear_combination -d * (hab : a + b = 1)]
    rcases hab' with ha' | hb'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.le) (mul_pos hb' hy)
  have hsn : s ∈ 𝓝 (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => d + t * h) := by fun_prop
    exact (isOpen_Ioi.preimage hc).mem_nhds h0
  have hsmall := hs.isLittleO_pow_succ_real h0 hr (hr'.mono nhdsWithin_le_nhds)
  rw [nhdsWithin_eq_nhds.mpr hsn] at hsmall
  simpa [r, f, g, c] using hsmall

private theorem negMulLog_symmetric_quadratic (d h : ℝ) (hd : 0 < d) :
    (fun t : ℝ => Real.negMulLog (d + t * h) + Real.negMulLog (d - t * h) -
        2 * Real.negMulLog d + t ^ 2 * (h ^ 2 / d)) =o[𝓝 0]
      (fun t => t ^ 2) := by
  refine ((negMulLog_quadratic d h hd).add (negMulLog_quadratic d (-h) hd)).congr_left ?_
  intro t
  simp only [mul_neg, ← sub_eq_add_neg]
  ring

private theorem matrixEntropy_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    matrixEntropy (Matrix.diagonal fun i => (b i : ℂ)) = ∑ i, Real.negMulLog (b i) := by
  rw [matrixEntropy, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def, Complex.ofReal_re]
    rfl
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

private theorem matrixEntropy_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    matrixEntropy (U.val * X * U.valᴴ) = matrixEntropy X := by
  have hU : U.valᴴ * U.val = 1 := U.2.1
  unfold matrixEntropy
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- Quadratic entropy along an even affine path of commuting Hermitian matrices. -/
private theorem commuting_entropy_quadratic (D H : Matrix BlockIndex BlockIndex ℂ)
    (hD : D.PosDef) (hH : H.IsHermitian) (hc : Commute D H)
    (heven : ∀ t : ℝ, matrixEntropy (D + (-t) • H) = matrixEntropy (D + t • H)) :
    Tendsto (fun t : ℝ => (matrixEntropy D - matrixEntropy (D + t • H)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 ((D⁻¹ * (H * H)).trace.re / 2)) := by
  obtain ⟨U, hUd, hUh⟩ := hc.exists_unitary hD.isHermitian hH
  have hU : U.valᴴ * U.val = 1 := U.2.1
  have hU' : U.val * U.valᴴ = 1 := U.2.2
  have hUdPos : (U.val * D * U.valᴴ).PosDef :=
    ((Unitary.toUnits U).isUnit.posDef_star_right_conjugate_iff).mpr hD
  let d (i : BlockIndex) := ((U.val * D * U.valᴴ) i i).re
  let h (i : BlockIndex) := ((U.val * H * U.valᴴ) i i).re
  have hd (i : BlockIndex) : 0 < d i := (Complex.pos_iff.mp (hUdPos.diag_pos (i := i))).1
  have hdiag (X : Matrix BlockIndex BlockIndex ℂ) (hx : X.IsHermitian) (hx' : X.IsDiag) :
      X = Matrix.diagonal (fun i => ((X i i).re : ℂ)) := by
    calc
      X = Matrix.diagonal (Matrix.diag X) := ((Matrix.isDiag_iff_diagonal_diag X).mp hx').symm
      _ = _ := congrArg Matrix.diagonal (funext fun i => (hx.coe_re_apply_self i).symm)
  have hDdiag : U.val * D * U.valᴴ = Matrix.diagonal (fun i => (d i : ℂ)) :=
    hdiag _ hUdPos.isHermitian hUd
  have hHdiag : U.val * H * U.valᴴ = Matrix.diagonal (fun i => (h i : ℂ)) :=
    hdiag _ (Matrix.isHermitian_mul_mul_conjTranspose U.val hH) hUh
  have hpath (t : ℝ) : matrixEntropy (D + t • H) =
      ∑ i, Real.negMulLog (d i + t * h i) := by
    rw [← matrixEntropy_unitary U (D + t • H)]
    have heq : U.val * (D + t • H) * U.valᴴ =
        Matrix.diagonal (fun i => ((d i + t * h i : ℝ) : ℂ)) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hDdiag, hHdiag]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Complex.real_smul]
      · simp [Matrix.diagonal_apply_ne _ hij, hij]
    rw [heq, matrixEntropy_diagonal]
  have hbase : matrixEntropy D = ∑ i, Real.negMulLog (d i) := by simpa using hpath 0
  have hinv : U.val * D⁻¹ * U.valᴴ = Matrix.diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) := by
    apply (show U.val * D⁻¹ * U.valᴴ = (U.val * D * U.valᴴ)⁻¹ from ?_).trans
    · rw [hDdiag]
      apply Matrix.inv_eq_right_inv
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.one_apply, Pi.mul_apply, Complex.ofReal_inv,
          Complex.ofReal_ne_zero.mpr (hd i).ne']
      · simp [Matrix.one_apply, Matrix.diagonal_apply_ne _ hij, hij]
    · symm
      apply Matrix.inv_eq_right_inv
      calc
        (U.val * D * U.valᴴ) * (U.val * D⁻¹ * U.valᴴ) =
          U.val * (D * (U.valᴴ * U.val) * D⁻¹) * U.valᴴ := by noncomm_ring
        _ = 1 := by rw [hU, Matrix.mul_one, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hD.isUnit),
          Matrix.mul_one, hU']
  have htrace : (D⁻¹ * (H * H)).trace.re = ∑ i, h i ^ 2 / d i := by
    have hsim :
        U.val * (D⁻¹ * (H * H)) * U.valᴴ =
          (U.val * D⁻¹ * U.valᴴ) * ((U.val * H * U.valᴴ) * (U.val * H * U.valᴴ)) := by
      symm
      calc
        _ = U.val * (D⁻¹ * (U.valᴴ * U.val) * H * (U.valᴴ * U.val) * H) * U.valᴴ := by noncomm_ring
        _ = _ := by simp only [hU, Matrix.mul_one, Matrix.mul_assoc]
    have htr : (U.val * (D⁻¹ * (H * H)) * U.valᴴ).trace = (D⁻¹ * (H * H)).trace := by
      rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    rw [← htr, hsim, hinv, hHdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.trace_diagonal, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv, pow_two]
    exact mul_comm _ _
  let q := ∑ i, h i ^ 2 / d i
  have hsmall : (fun t : ℝ =>
      matrixEntropy (D + t • H) + matrixEntropy (D + (-t) • H) -
        2 * matrixEntropy D + t ^ 2 * q) =o[𝓝 0] (fun t => t ^ 2) := by
    have hsum := Asymptotics.IsLittleO.sum (s := (Finset.univ : Finset BlockIndex))
      (fun i _ => negMulLog_symmetric_quadratic (d i) (h i) (hd i))
    refine hsum.congr_left (fun t => ?_)
    simp only [Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hbase, hpath, neg_mul, ← sub_eq_add_neg, q]
  have hlim := (hsmall.mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).tendsto_div_nhds_zero
  rw [htrace]
  have htranslated : Tendsto (fun t : ℝ => q / 2 +
      ((matrixEntropy (D + t • H) + matrixEntropy (D + (-t) • H) -
        2 * matrixEntropy D + t ^ 2 * q) / t ^ 2) / (-2)) (𝓝[≠] 0) (𝓝 (q / 2)) := by
    simpa only [zero_div, add_zero] using (hlim.div_const (-2)).const_add (q / 2)
  refine htranslated.congr' ?_
  have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ∈ ({0}ᶜ : Set ℝ) := eventually_mem_nhdsWithin
  filter_upwards [hevent] with t ht
  have ht0 : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  rw [heven]
  field_simp [ht0] <;> ring

/-- The Hermitian coefficient of `t` in the leading Gram path. -/
def collisionGramSlope : Matrix BlockIndex BlockIndex ℂ :=
  (1 / 2 : ℝ) • fromBlocks 0 Sstar Sstarᴴ 0

private theorem collisionGramPath_eq_affine (t : ℝ) :
    collisionGramPath t = collisionGram 0 + t • collisionGramSlope := by
  unfold collisionGramPath collisionGram collisionGramSlope
  rw [Matrix.conjTranspose_smul, star_trivial, smul_smul]
  simp only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, Matrix.conjTranspose_zero,
    smul_smul, smul_zero, add_zero, zero_add, mul_comm]

private theorem collisionGramSlope_hermitian : collisionGramSlope.IsHermitian :=
  (Matrix.isHermitian_zero.fromBlocks rfl Matrix.isHermitian_zero).smul
    (show IsSelfAdjoint (1 / 2 : ℝ) by simp [IsSelfAdjoint])

private theorem collisionGramSlope_commutes : Commute (collisionGram 0) collisionGramSlope := by
  have hR : collisionMarginalᴴ = collisionMarginal := collision_marginal_posDef.isHermitian.eq
  have hS := Sstar_commutes_observed.eq
  have hAdj : collisionMarginal * Sstarᴴ = Sstarᴴ * collisionMarginal := by
    simpa only [Matrix.conjTranspose_mul, hR] using (congrArg Matrix.conjTranspose hS).symm
  change collisionGram 0 * collisionGramSlope = collisionGramSlope * collisionGram 0
  simp [collisionGram, collisionGramSlope, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.fromBlocks_multiply, hS, hAdj]

private theorem collisionGram_trace_coefficient :
    (((collisionGram 0)⁻¹ * (collisionGramSlope * collisionGramSlope)).trace.re / 2) =
      (collisionMarginal⁻¹ * Sstar * Sstarᴴ).trace.re / 2 := by
  let R := collisionMarginal
  let S := Sstar
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp collision_marginal_posDef.isUnit
  have hDinv : (collisionGram 0)⁻¹ = (2 : ℝ) •
      fromBlocks R⁻¹ (0 : Matrix VisiblePair VisiblePair ℂ) 0 R⁻¹ := by
    apply Matrix.inv_eq_right_inv
    simp [collisionGram, R, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.fromBlocks_multiply,
      Matrix.mul_nonsing_inv _ hdet, show (1 / 2 : ℝ) * 2 = 1 by norm_num]
  have hSinv : R⁻¹ * S = S * R⁻¹ := by
    calc
      R⁻¹ * S = R⁻¹ * S * (R * R⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = R⁻¹ * (S * R) * R⁻¹ := by noncomm_ring
      _ = R⁻¹ * (R * S) * R⁻¹ := by rw [← Sstar_commutes_observed.eq]
      _ = S * R⁻¹ := by rw [← Matrix.mul_assoc R⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have htrace : (R⁻¹ * (Sᴴ * S)).trace = (R⁻¹ * (S * Sᴴ)).trace := by
    calc
      _ = (S * (R⁻¹ * Sᴴ)).trace := Matrix.trace_mul_cycle' R⁻¹ Sᴴ S
      _ = _ := by rw [← Matrix.mul_assoc S R⁻¹ Sᴴ, ← hSinv, Matrix.mul_assoc]
  have hblocks : (collisionGram 0)⁻¹ * (collisionGramSlope * collisionGramSlope) =
      (1 / 2 : ℝ) • fromBlocks (R⁻¹ * (S * Sᴴ)) 0 0 (R⁻¹ * (Sᴴ * S)) := by
    rw [hDinv]
    simp [collisionGramSlope, S, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.fromBlocks_multiply, show (2 : ℝ) * (1 / 2 * (1 / 2)) = 1 / 2 by norm_num]
  rw [hblocks, Matrix.trace_smul, Complex.smul_re]
  have hblockTrace : (fromBlocks (R⁻¹ * (S * Sᴴ)) 0 0 (R⁻¹ * (Sᴴ * S))).trace =
      (R⁻¹ * (S * Sᴴ)).trace + (R⁻¹ * (Sᴴ * S)).trace := by
    simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type]
  rw [hblockTrace, htrace, Complex.add_re, Matrix.mul_assoc]
  change (1 / 2 : ℝ) * (_ + _) / 2 = _
  ring

/-- The commuting Gram path gives the exact complementary conditional entropy prefactor. -/
theorem collision_commuting_entropy_quadratic :
    Tendsto (fun t : ℝ =>
      (matrixEntropy (collisionGram 0) - matrixEntropy (collisionGramPath t)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 ((310625 - 46875 * Real.sqrt 41) / 16384)) := by
  have heven (t : ℝ) :
      matrixEntropy (collisionGramPath (-t)) = matrixEntropy (collisionGramPath t) := by
    unfold collisionGramPath
    simpa [neg_smul, neg_one_smul] using collisionGram_phase (t • Sstar) (-1) (by simp)
  simpa only [← collisionGramPath_eq_affine, collisionGram_trace_coefficient,
    collision_weighted_coefficient] using
    commuting_entropy_quadratic (collisionGram 0) collisionGramSlope collisionGram_zero_posDef
      collisionGramSlope_hermitian collisionGramSlope_commutes (by
        simpa only [collisionGramPath_eq_affine] using heven)

/-- For the literal fair hidden-label c-q state, with total length `2 + m`. -/
theorem collision_complementary_entropy_asymptotic :
    Tendsto (fun m : ℕ => collisionComplementaryEntropy m / collisionAlpha ^ (2 * (2 + m)))
      atTop (𝓝 ((310625 - 46875 * Real.sqrt 41) / 16384)) := by
  have hamp : Tendsto (fun m : ℕ => collisionAlpha ^ (2 + m)) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨pow_shift_tendsto alpha_pos.le collisionAlpha_lt_one,
      Eventually.of_forall fun m => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (pow_pos alpha_pos (2 + m)).ne'⟩
  have hmodel := collision_commuting_entropy_quadratic.comp hamp
  have hsum := hmodel.add collision_entropy_replacement
  simp only [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 5] with m hm
  dsimp only [Function.comp_apply]
  rw [collisionComplementaryEntropy_eq_gram m hm, mul_comm 2 (2 + m), pow_mul, ← add_div]
  congr 1
  ring

end

end D5.S3.Quantum.TensorNetworks.PrimitiveComplementaryEntropyExpansion

#print axioms D5.S3.Quantum.TensorNetworks.PrimitiveComplementaryEntropyExpansion.collision_cross_exponential_remainder
#print axioms D5.S3.Quantum.TensorNetworks.PrimitiveComplementaryEntropyExpansion.collision_entropy_replacement
#print axioms D5.S3.Quantum.TensorNetworks.PrimitiveComplementaryEntropyExpansion.collision_complementary_entropy_asymptotic
