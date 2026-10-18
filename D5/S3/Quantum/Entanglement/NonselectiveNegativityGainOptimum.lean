/- GID: D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The global two-qubit non-selective measurement optimum is N/2 + 1/4. -/

import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

/-! The sharp negativity bound for non-selective measurements on pure two-qubit states. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_add_le exists_svd_sqrt_eigenvalues)
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
  (traceNorm_isometry traceNorm_smul_nonneg)

def measured (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :=
  ∑ j, ((Uᴴ * ρ * U) j j) •
    vecMulVec (fun i => U i j) (star (fun i => U i j))

def claim : Prop := ∀ ψ : Fin 2 × Fin 2 → ℂ, (∑ i, Complex.normSq (ψ i)) = 1 →
  (∀ U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ,
    negativity (measured U (rankOneDensity ψ)) ≤ negativity (rankOneDensity ψ) / 2 + 1 / 4) ∧
  (∃ U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ,
    negativity (measured U (rankOneDensity ψ)) = negativity (rankOneDensity ψ) / 2 + 1 / 4)

private theorem measured_diagonal (U ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    measured U ρ = U * diagonal (fun j => (Uᴴ * ρ * U) j j) * Uᴴ := by
  ext p q
  simp only [measured.eq_1, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Pi.star_apply]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem pure_trace (ψ : Fin 2 × Fin 2 → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) : (rankOneDensity ψ).trace = 1 := by
  rw [rankOneDensity, Matrix.trace_vecMulVec]
  change (∑ i, ψ i * star (ψ i)) = 1
  simp only [RCLike.star_def, Complex.mul_conj]
  exact_mod_cast hψ

private theorem pure_square (ψ : Fin 2 × Fin 2 → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) :
    rankOneDensity ψ * rankOneDensity ψ = rankOneDensity ψ := by
  have hn : star ψ ⬝ᵥ ψ = 1 := by
    rw [dotProduct_comm]
    exact pure_trace ψ hψ
  exact D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment.pure_outer_square ψ hn

private theorem pinching_trace (U ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ) :
    (measured U ρ * measured U ρ).trace = (measured U ρ * ρ).trace := by
  have hleft : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  rw [measured_diagonal]
  let D := diagonal (fun j => (Uᴴ * ρ * U) j j)
  change ((U * D * Uᴴ) * (U * D * Uᴴ)).trace = ((U * D * Uᴴ) * ρ).trace
  calc
    _ = (U * (D * D) * Uᴴ).trace := by
      congr 1
      calc
        _ = U * D * (Uᴴ * U) * D * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hleft]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (D * D).trace := by rw [Matrix.trace_mul_cycle, hleft, Matrix.one_mul]
    _ = (D * (Uᴴ * ρ * U)).trace := by
      simp [D, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    _ = _ := by
      symm
      calc
        _ = (U * (D * (Uᴴ * ρ))).trace := by simp only [Matrix.mul_assoc]
        _ = ((D * (Uᴴ * ρ)) * U).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]

private theorem reflection_trace (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ) (ψ : Fin 2 × Fin 2 → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1) :
    (((2 : ℂ) • measured U (rankOneDensity ψ) - rankOneDensity ψ) *
      ((2 : ℂ) • measured U (rankOneDensity ψ) - rankOneDensity ψ)).trace = 1 := by
  have hp := pinching_trace U (rankOneDensity ψ) hU
  have hc := Matrix.trace_mul_comm (rankOneDensity ψ) (measured U (rankOneDensity ψ))
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [pure_square ψ hψ, pure_trace ψ hψ, hc, ← hp]
  ring

private theorem gram_trace {n : Type*} [Fintype n] (X : Matrix n n ℂ) :
    (Xᴴ * X).trace.re = ∑ p, ∑ q, ‖X p q‖ ^ 2 := by
  have h := congrArg Complex.re
    (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace X)
  rw [← h]
  change ‖WithLp.toLp 2 (fun i => WithLp.toLp 2 (X i))‖ ^ 2 = _
  simp [PiLp.norm_sq_eq_of_L2]

private theorem partialTranspose_frobenius
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (∑ p, ∑ q, ‖partialTranspose X p q‖ ^ 2) = ∑ p, ∑ q, ‖X p q‖ ^ 2 := by
  simp only [partialTranspose, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem traceNorm_frobenius
    (Y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    traceNorm Y ≤ 2 * Real.sqrt (∑ p, ∑ q, ‖Y p q‖ ^ 2) := by
  have h := D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) Y
  have hi : D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 4 := by
    norm_num [D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.entryNormSq.eq_1,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Matrix.one_mul, hi, show Real.sqrt 4 = 2 by norm_num] at h
  exact h

private theorem measured_hermitian (U ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hρ : ρ.IsHermitian) : (measured U ρ).IsHermitian := by
  rw [measured_diagonal]
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro j
  change star ((Uᴴ * ρ * U) j j) = (Uᴴ * ρ * U) j j
  exact (Matrix.isHermitian_conjTranspose_mul_mul U hρ).apply j j

private theorem upper_bound (ψ : Fin 2 × Fin 2 → ℂ)
    (hψ : (∑ i, Complex.normSq (ψ i)) = 1)
    (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hU : U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ) :
    negativity (measured U (rankOneDensity ψ)) ≤ negativity (rankOneDensity ψ) / 2 + 1 / 4 := by
  let X := (2 : ℂ) • measured U (rankOneDensity ψ) - rankOneDensity ψ
  have hρ : (rankOneDensity ψ).IsHermitian := (Matrix.posSemidef_vecMulVec_self_star ψ).1
  have hX : X.IsHermitian :=
    ((measured_hermitian U (rankOneDensity ψ) hρ).smul (by norm_num [IsSelfAdjoint])).sub hρ
  have hf : (∑ p, ∑ q, ‖partialTranspose X p q‖ ^ 2) = 1 := by
    rw [partialTranspose_frobenius, ← gram_trace, hX.eq]
    exact congrArg Complex.re (reflection_trace U hU ψ hψ)
  have hb := traceNorm_frobenius (partialTranspose X)
  rw [hf, Real.sqrt_one, mul_one] at hb
  have he : (2 : ℂ) • partialTranspose (measured U (rankOneDensity ψ)) =
      partialTranspose (rankOneDensity ψ) + partialTranspose X := by
    ext p q
    simp [X, partialTranspose]
  have ht := traceNorm_add_le (partialTranspose (rankOneDensity ψ)) (partialTranspose X)
  have hs : traceNorm ((2 : ℂ) • partialTranspose (measured U (rankOneDensity ψ))) =
      2 * traceNorm (partialTranspose (measured U (rankOneDensity ψ))) := by
    simpa only [Complex.ofReal_ofNat] using
      traceNorm_smul_nonneg (partialTranspose (measured U (rankOneDensity ψ))) 2 (by norm_num)
  rw [← he, hs] at ht
  unfold negativity
  linarith

private def schmidt (x : Fin 2 → ℝ) : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then (x p.1 : ℂ) else 0

private theorem vector_schmidt (ψ : Fin 2 × Fin 2 → ℂ) :
    ∃ (x : Fin 2 → ℝ) (V W : unitaryGroup (Fin 2) ℂ),
      (∀ i, 0 ≤ x i) ∧ ψ =
        ((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
          (W : Matrix (Fin 2) (Fin 2) ℂ).map star) *ᵥ schmidt x := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := fun i j => ψ (i, j)
  let H : (Aᴴ * A).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self A).1
  let x : Fin 2 → ℝ := fun i => Real.sqrt (H.eigenvalues i)
  obtain ⟨V, W, he⟩ := exists_svd_sqrt_eigenvalues A
  refine ⟨x, V, W, fun i => Real.sqrt_nonneg _, ?_⟩
  funext ⟨i, j⟩
  have h := congrFun (congrFun he i) j
  simpa [A, x, H, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, schmidt, Matrix.conjTranspose_apply, Matrix.diagonal,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, mul_comm, mul_left_comm,
    mul_assoc] using h

private theorem negativity_local
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (V W : unitaryGroup (Fin 2) ℂ) :
    negativity (((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (W : Matrix (Fin 2) (Fin 2) ℂ)) *
      M * ((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (W : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) =
      negativity M := by
  unfold negativity
  have hp (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
      partialTranspose A =
        D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation.partialTransposeB
          A := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rfl
  simp only [hp,
    D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation.partialTransposeB_kronecker_conj]
  rw [traceNorm_isometry]
  exact Matrix.mem_unitaryGroup_iff'.mp
    (Matrix.kronecker_mem_unitary V.prop (Matrix.map_star_mem_unitaryGroup_iff.mpr W.prop))

private theorem measured_transport
    (L U ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hL : L ∈ unitaryGroup (Fin 2 × Fin 2) ℂ) :
    measured (L * U) (L * ρ * Lᴴ) = L * measured U ρ * Lᴴ := by
  have hleft : Lᴴ * L = 1 := Matrix.mem_unitaryGroup_iff'.mp hL
  have he : (L * U)ᴴ * (L * ρ * Lᴴ) * (L * U) = Uᴴ * ρ * U := by
    calc
      _ = Uᴴ * (Lᴴ * L) * ρ * (Lᴴ * L) * U := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hleft]; simp
  rw [measured_diagonal, measured_diagonal, he]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private def correlated (a b c : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then
    if p.1 = q.1 then if p.1 = 0 then (a : ℂ) else (b : ℂ) else (c : ℂ) else 0

private theorem correlated_norm (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    traceNorm (partialTranspose (correlated a b c)) = a + b + 2 * c := by
  let D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := diagonal
    (fun p => if p.1 = p.2 then if p.1 = 0 then (a : ℂ) else (b : ℂ) else (c : ℂ))
  have hD : D.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro p
    change (0 : ℂ) ≤ if p.1 = p.2 then if p.1 = 0 then (a : ℂ) else (b : ℂ) else (c : ℂ)
    split_ifs <;> exact RCLike.ofReal_nonneg.mpr (by assumption)
  have hsquare : D * D = (partialTranspose (correlated a b c))ᴴ *
      partialTranspose (correlated a b c) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [D, correlated, partialTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  unfold D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
  rw [CFC.sqrt_unique hsquare hD.nonneg]
  simp [D, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem rotation_parameters (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ∃ s t : ℝ, s ^ 2 + t ^ 2 = 1 ∧
      Real.sqrt 2 * (s ^ 2 - t ^ 2) = a - b ∧
      2 * Real.sqrt 2 * s * t = a + b := by
  let r := Real.sqrt 2
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 < r := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a]
  have hq : 0 < (1 + (a - b) / r) / 2 := by
    apply div_pos _ (by norm_num)
    have hdiv : -1 < (a - b) / r := (lt_div_iff₀ hr).2 (by nlinarith)
    linarith
  let s := Real.sqrt ((1 + (a - b) / r) / 2)
  have hs : 0 < s := Real.sqrt_pos.2 hq
  have hs2 : 2 * r * s ^ 2 = r + a - b := by
    have h := Real.sq_sqrt hq.le
    change s ^ 2 = _ at h
    field_simp [ne_of_gt hr] at h
    nlinarith
  let t := (a + b) / (2 * r * s)
  have hden : 2 * r * s ≠ 0 := ne_of_gt (by positivity)
  have hprod : (2 * r * s) ^ 2 * (1 - s ^ 2) = (a + b) ^ 2 := by
    calc
      _ = 2 * r * (2 * r * s ^ 2) - (2 * r * s ^ 2) ^ 2 := by ring
      _ = 2 * r * (r + a - b) - (r + a - b) ^ 2 := by rw [hs2]
      _ = _ := by nlinarith [hab, hr2]
  have ht2 : t ^ 2 = 1 - s ^ 2 := by
    dsimp [t]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hden)).2
    nlinarith [hprod]
  refine ⟨s, t, by linarith, ?_, ?_⟩
  · change r * (s ^ 2 - t ^ 2) = a - b
    nlinarith [hs2, ht2]
  · change 2 * r * s * ((a + b) / (2 * r * s)) = a + b
    exact mul_div_cancel₀ _ hden

private def rotation (s t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then
    if p.1 = 0 then if q.1 = 0 then (s : ℂ) else (t : ℂ)
    else if q.1 = 0 then (t : ℂ) else (-s : ℂ)
    else if p = q then 1 else 0

private theorem rotation_unitary (s t : ℝ) (hst : s ^ 2 + t ^ 2 = 1) :
    rotation s t ∈ unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hc : (s : ℂ) ^ 2 + (t : ℂ) ^ 2 = 1 := by exact_mod_cast hst
  have hrev : (t : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := (add_comm _ _).trans hc
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [rotation.eq_1, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, ← pow_two, hc, hrev, mul_comm]

private theorem schmidt_pure (x : Fin 2 → ℝ) :
    rankOneDensity (schmidt x) = correlated (x 0 ^ 2) (x 1 ^ 2) (x 0 * x 1) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [rankOneDensity, schmidt.eq_1, correlated.eq_1, Matrix.vecMulVec_apply,
      Pi.star_apply, pow_two, mul_comm]

private theorem rotation_readout (x : Fin 2 → ℝ) (s t : ℝ) :
    measured (rotation s t) (rankOneDensity (schmidt x)) = correlated
      (s ^ 2 * (s * x 0 + t * x 1) ^ 2 + t ^ 2 * (t * x 0 - s * x 1) ^ 2)
      (t ^ 2 * (s * x 0 + t * x 1) ^ 2 + s ^ 2 * (t * x 0 - s * x 1) ^ 2)
      (s * t * ((s * x 0 + t * x 1) ^ 2 - (t * x 0 - s * x 1) ^ 2)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [measured.eq_1, rankOneDensity, schmidt.eq_1, rotation.eq_1, correlated.eq_1,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring

private theorem schmidt_measured (x : Fin 2 → ℝ) (s t : ℝ)
    (hx : x 0 ^ 2 + x 1 ^ 2 = 1) (hst : s ^ 2 + t ^ 2 = 1)
    (hd : Real.sqrt 2 * (s ^ 2 - t ^ 2) = x 0 - x 1)
    (hp : 2 * Real.sqrt 2 * s * t = x 0 + x 1) :
    measured (rotation s t) (rankOneDensity (schmidt x)) =
      correlated (x 0 ^ 2 / 2 + 1 / 4) (x 1 ^ 2 / 2 + 1 / 4)
        (x 0 * x 1 / 2 + 1 / 4) := by
  let P := (s * x 0 + t * x 1) ^ 2
  let Q := (t * x 0 - s * x 1) ^ 2
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsum : P + Q = 1 := by
    calc
      _ = (s ^ 2 + t ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by dsimp [P, Q]; ring
      _ = 1 := by rw [hst, hx]; norm_num
  have hdiff : P - Q = 2 * s * t := by
    apply mul_left_cancel₀ hr
    calc
      Real.sqrt 2 * (P - Q) =
          (Real.sqrt 2 * (s ^ 2 - t ^ 2)) * (x 0 ^ 2 - x 1 ^ 2) +
            2 * (2 * Real.sqrt 2 * s * t) * x 0 * x 1 := by dsimp [P, Q]; ring
      _ = (x 0 + x 1) * (x 0 ^ 2 + x 1 ^ 2) := by rw [hd, hp]; ring
      _ = Real.sqrt 2 * (2 * s * t) := by rw [hx]; nlinarith [hp]
  have hdu : (s ^ 2 - t ^ 2) * (2 * s * t) = (x 0 ^ 2 - x 1 ^ 2) / 2 := by
    have he : (Real.sqrt 2 * (s ^ 2 - t ^ 2)) * (2 * Real.sqrt 2 * s * t) =
        Real.sqrt 2 ^ 2 * ((s ^ 2 - t ^ 2) * (2 * s * t)) := by ring
    rw [hd, hp, hr2] at he
    nlinarith [he]
  have hu2 : (2 * s * t) ^ 2 = (1 + 2 * x 0 * x 1) / 2 := by
    have he := congrArg (fun a : ℝ => a ^ 2) hp
    have hf : (2 * Real.sqrt 2 * s * t) ^ 2 = Real.sqrt 2 ^ 2 * (2 * s * t) ^ 2 := by ring
    rw [hf, hr2] at he
    nlinarith [he, hx]
  have h0 : s ^ 2 * P + t ^ 2 * Q = x 0 ^ 2 / 2 + 1 / 4 := by
    calc
      _ = ((P + Q) * (s ^ 2 + t ^ 2) +
          (P - Q) * (s ^ 2 - t ^ 2)) / 2 := by ring
      _ = _ := by rw [hsum, hst, hdiff, mul_comm (2 * s * t), hdu]; linarith [hx]
  have h1 : t ^ 2 * P + s ^ 2 * Q = x 1 ^ 2 / 2 + 1 / 4 := by
    nlinarith [hsum, hst, h0]
  have h01 : s * t * (P - Q) = x 0 * x 1 / 2 + 1 / 4 := by
    rw [hdiff]
    nlinarith [hu2]
  rw [rotation_readout]
  change correlated (s ^ 2 * P + t ^ 2 * Q) (t ^ 2 * P + s ^ 2 * Q)
      (s * t * (P - Q)) = _
  rw [h0, h1, h01]

private theorem schmidt_attainment (x : Fin 2 → ℝ) (hn : ∀ i, 0 ≤ x i)
    (hx : x 0 ^ 2 + x 1 ^ 2 = 1) :
    ∃ U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ,
      negativity (measured U (rankOneDensity (schmidt x))) =
        negativity (rankOneDensity (schmidt x)) / 2 + 1 / 4 := by
  obtain ⟨s, t, hst, hd, hp⟩ := rotation_parameters (x 0) (x 1) (hn 0) hx
  refine ⟨rotation s t, rotation_unitary s t hst, ?_⟩
  rw [schmidt_measured x s t hx hst hd hp, schmidt_pure]
  unfold negativity
  have h0 := hn 0
  have h1 := hn 1
  rw [correlated_norm _ _ _ (by positivity) (by positivity) (by positivity),
    correlated_norm _ _ _ (sq_nonneg _) (sq_nonneg _) (mul_nonneg (hn 0) (hn 1))]
  linarith

theorem result : claim := by
  intro ψ hψ
  refine ⟨fun U hU => upper_bound ψ hψ U hU, ?_⟩
  obtain ⟨x, V, W, hn, he⟩ := vector_schmidt ψ
  let Z : unitaryGroup (Fin 2) ℂ := Matrix.UnitaryGroup.map_star W
  let L : unitaryGroup (Fin 2 × Fin 2) ℂ :=
    ⟨(V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Z : Matrix (Fin 2) (Fin 2) ℂ),
      Matrix.kronecker_mem_unitary V.prop Z.prop⟩
  have heq : ψ = (L : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) *ᵥ schmidt x := he
  have hpure : rankOneDensity ψ = L.val * rankOneDensity (schmidt x) * L.valᴴ := by
    rw [heq]
    exact (D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment.conjugate_outer
      L.val (schmidt x)).symm
  have hx : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    have ht := pure_trace ψ hψ
    rw [hpure, Matrix.trace_mul_cycle,
      show L.valᴴ * L.val = 1 from Matrix.mem_unitaryGroup_iff'.mp L.prop,
      Matrix.one_mul, schmidt_pure] at ht
    simpa [correlated.eq_1, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two,
      pow_two, Complex.mul_re] using
      congrArg Complex.re ht
  obtain ⟨U, hU, hopt⟩ := schmidt_attainment x hn hx
  refine ⟨L.val * U, (unitaryGroup (Fin 2 × Fin 2) ℂ).mul_mem L.prop hU, ?_⟩
  rw [hpure, measured_transport L.val U (rankOneDensity (schmidt x)) L.prop]
  change negativity (((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Z : Matrix (Fin 2) (Fin 2) ℂ)) *
      measured U (rankOneDensity (schmidt x)) *
      ((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Z : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) =
    negativity (((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Z : Matrix (Fin 2) (Fin 2) ℂ)) *
      rankOneDensity (schmidt x) *
      ((V : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Z : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) / 2 + 1 / 4
  rw [negativity_local _ V Z, negativity_local _ V Z]
  exact hopt

end D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
