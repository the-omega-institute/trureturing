/- GID: D5/S3/Quantum/Divergence/FaithfulConditionalGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/FaithfulConditionalGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Squared trace distance separates complete and conditional contraction coefficients. -/

import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Divergence.FaithfulConditionalGap

open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability

/-- A finite real-valued divergence, with heterogeneous quantum data processing. -/
structure FiniteDivergence where
  value : ∀ {n : Type} [Fintype n] [DecidableEq n], DensityState n → DensityState n → ℝ
  nonnegative : ∀ {n : Type} [Fintype n] [DecidableEq n] (ρ σ : DensityState n),
    0 ≤ value ρ σ
  faithful : ∀ {n : Type} [Fintype n] [DecidableEq n] (ρ σ : DensityState n),
    value ρ σ = 0 ↔ ρ = σ
  dataProcessing : ∀ {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (N : QuantumChannel a b) (ρ σ : DensityState a),
    value (N.mapState ρ) (N.mapState σ) ≤ value ρ σ

private theorem positive_trace_contraction
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ)
    (hpos : ∀ X, 0 ≤ X → 0 ≤ f X)
    (htr : ∀ X, Matrix.trace (f X) = Matrix.trace X)
    (X : Matrix a a ℂ) (hX : X.IsHermitian) : traceNorm (f X) ≤ traceNorm X := by
  have hn (Y : Matrix a a ℂ) (hY : 0 ≤ Y) :
      traceNorm (f Y) = (Matrix.trace Y).re := by
    have h := congrArg Complex.re
      (traceNorm_of_posSemidef (Matrix.nonneg_iff_posSemidef.mp (hpos Y hY)))
    simpa only [Complex.ofReal_re, htr] using h
  rw [← CFC.posPart_sub_negPart X hX, map_sub, sub_eq_add_neg]
  calc
    traceNorm (f (posPart X) + -f (negPart X)) ≤
        traceNorm (f (posPart X)) + traceNorm (-f (negPart X)) := traceNorm_add_le _ _
    _ = traceNorm X := by
      rw [traceNorm_neg, hn _ (CFC.posPart_nonneg X), hn _ (CFC.negPart_nonneg X)]
      exact (trace_norm_jordan_mass X hX).symm

private theorem traceNorm_zero {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) : traceNorm X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hp := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Xᴴ * X))
    have hi := (Complex.nonneg_iff.mp hp.trace_nonneg).2
    have hz : (CFC.sqrt (Xᴴ * X)).trace = 0 := Complex.ext h hi.symm
    exact CFC.abs_eq_zero_iff.mp (hp.trace_eq_zero_iff.mp hz)
  · rintro rfl
    simp [traceNorm]

private theorem state_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : (CStarMatrix.ofMatrix.symm ρ.1).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)).isHermitian

private theorem traceDistance_faithful {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : DensityState n) : traceDistance ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h
    have hz : traceNorm (CStarMatrix.ofMatrix.symm ρ.1 -
        CStarMatrix.ofMatrix.symm σ.1) = 0 := by
      unfold traceDistance at h
      linarith
    have he := sub_eq_zero.mp ((traceNorm_zero _).mp hz)
    apply Subtype.ext
    exact CStarMatrix.ofMatrix.symm.injective he
  · rintro rfl
    simp [traceDistance, traceNorm]

private theorem traceDistance_heterogeneous
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : QuantumChannel a b) (ρ σ : DensityState a) :
    traceDistance (N.mapState ρ) (N.mapState σ) ≤ traceDistance ρ σ := by
  let f : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  have hp : ∀ X, 0 ≤ X → 0 ≤ f X := by
    intro X hX
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg N.toCompletelyPositiveMap
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX))
  have ht : ∀ X, Matrix.trace (f X) = Matrix.trace X :=
    fun X => N.trace_preserving (CStarMatrix.ofMatrix X)
  have hc := positive_trace_contraction f hp ht
    (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1)
    ((state_hermitian ρ).sub (state_hermitian σ))
  have he : f (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1) =
      CStarMatrix.ofMatrix.symm (N.mapState ρ).1 -
        CStarMatrix.ofMatrix.symm (N.mapState σ).1 := by
    rw [map_sub]
    rfl
  rw [he] at hc
  exact div_le_div_of_nonneg_right hc (by norm_num)

private def squareTrace : FiniteDivergence where
  value ρ σ := traceDistance ρ σ ^ 2
  nonnegative ρ σ := sq_nonneg _
  faithful ρ σ := by rw [sq_eq_zero_iff, traceDistance_faithful]
  dataProcessing N ρ σ := by
    exact pow_le_pow_left₀ (traceDistance_nonneg _ _)
      (traceDistance_heterogeneous N ρ σ) 2

/-- Complete ratios range over every finite quantum reference. -/
def completeRatios {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (r : Type) (fr : Fintype r) (dr : DecidableEq r),
    letI := fr
    letI := dr
    ∃ ρ σ : DensityState (r × a),
      marginalRight ρ = marginalRight σ ∧ 0 < D.value ρ σ ∧
      x = D.value (referenceState N ρ) (referenceState N σ) / D.value ρ σ}

/-- Squaring is performed before subtracting the marginal divergence. -/
def conditionalRatios {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (r : Type) (fr : Fintype r) (dr : DecidableEq r),
    letI := fr
    letI := dr
    ∃ ρ σ : DensityState (r × a),
      0 < D.value ρ σ - D.value (marginalRight ρ) (marginalRight σ) ∧
      x = (D.value (referenceState N ρ) (referenceState N σ) -
        D.value (marginalRight ρ) (marginalRight σ)) /
          (D.value ρ σ - D.value (marginalRight ρ) (marginalRight σ))}

def completeCoefficient {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : ℝ :=
  sSup (insert 0 (completeRatios D N))

def conditionalCoefficient {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (D : FiniteDivergence) (N : QuantumChannel a b) : ℝ :=
  sSup (insert 0 (conditionalRatios D N))

private def weight (y x : Fin 2) : ℝ := if y = x then 3 / 4 else 1 / 4

private def amplitude (y x : Fin 2) : ℂ := (Real.sqrt (weight y x) : ℂ)

private def kraus (p : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single p.1 p.2 (amplitude p.1 p.2)

private theorem amplitude_square (y x : Fin 2) :
    amplitude y x * star (amplitude y x) = (weight y x : ℂ) := by
  have hw : 0 ≤ weight y x := by unfold weight; split_ifs <;> norm_num
  simp only [amplitude, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hw]

private theorem kraus_complete : (∑ p, (kraus p)ᴴ * kraus p) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kraus, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, mul_comm, amplitude_square, weight]
    <;> norm_num

private def binaryChannel : QuantumChannel (Fin 2) (Fin 2) :=
  Classical.choose (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    kraus kraus_complete)

private theorem binary_action (X : Matrix (Fin 2) (Fin 2) ℂ) :
    act binaryChannel X = Matrix.diagonal
      (fun y => (weight y 0 : ℂ) * X 0 0 + (weight y 1 : ℂ) * X 1 1) := by
  have h := Classical.choose_spec
    (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
      kraus kraus_complete) X
  change act binaryChannel X = _ at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kraus, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply,
      mul_assoc, mul_left_comm, mul_comm, amplitude_square]

private def phase {r : Type*} [DecidableEq r] :
    Matrix (r × Fin 2) (r × Fin 2) ℂ :=
  Matrix.diagonal (fun p => if p.2 = 0 then 1 else -1)

private theorem phase_isometry {r : Type*} [Fintype r] [DecidableEq r] :
    (phase (r := r))ᴴ * phase = 1 := by
  rw [phase, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext p q
  simp only [Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply]
  split_ifs <;> simp_all

private def pinch {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin 2) (r × Fin 2) ℂ) : Matrix (r × Fin 2) (r × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (X + phase * X * phaseᴴ)

private theorem pinch_entry {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin 2) (r × Fin 2) ℂ) (i j : r) (a b : Fin 2) :
    pinch X (i, a) (j, b) = if a = b then X (i, a) (j, b) else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pinch, phase, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_conjTranspose, Matrix.smul_apply, Matrix.add_apply]
    <;> ring

private theorem pinch_contract {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin 2) (r × Fin 2) ℂ) : traceNorm (pinch X) ≤ traceNorm X := by
  unfold pinch
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    traceNorm_smul_nonneg _ _ (by norm_num)]
  have h := traceNorm_add_le X (phase * X * phaseᴴ)
  rw [traceNorm_isometry phase phase_isometry] at h
  linarith

private theorem equal_marginal_action {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Fin 2) (r × Fin 2) ℂ) (hX : partialTraceRight X = 0) :
    amp binaryChannel X = (1 / 2 : ℂ) • pinch X := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hz := congrFun (congrFun hX i) j
  change (∑ c : Fin 2, X (i, c) (j, c)) = 0 at hz
  rw [Fin.sum_univ_two] at hz
  rw [amp_entry, binary_action]
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul, pinch_entry]
  fin_cases a <;> fin_cases b <;> norm_num [weight] at * <;> linear_combination hz / 4

private theorem reference_contract {a b r : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r] (N : QuantumChannel a b)
    (ρ σ : DensityState (r × a)) :
    traceDistance (referenceState N ρ) (referenceState N σ) ≤ traceDistance ρ σ := by
  let f : Matrix (r × a) (r × a) ℂ →ₗ[ℂ] Matrix (r × b) (r × b) ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)
  have hp : ∀ X, 0 ≤ X → 0 ≤ f X := by
    intro X hX
    let Y := (blockEquiv r a).symm (CStarMatrix.ofMatrix X)
    have hY : 0 ≤ Y := map_nonneg (blockEquiv r a).symm
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX)
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (map_nonneg (blockEquiv r b)
        (N.toCompletelyPositiveMap.map_cstarMatrix_nonneg Y hY))
  have ht : ∀ X, Matrix.trace (f X) = Matrix.trace X := by
    intro X
    change Matrix.trace (amp N X) = Matrix.trace X
    rw [← trace_partialTraceRight (amp N X)]
    have he : partialTraceRight (amp N X) = partialTraceRight X := ptr_amp N X
    rw [he, trace_partialTraceRight]
  have h := positive_trace_contraction f hp ht
    (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1)
    ((state_hermitian ρ).sub (state_hermitian σ))
  have he : f (CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1) =
      CStarMatrix.ofMatrix.symm (referenceState N ρ).1 -
        CStarMatrix.ofMatrix.symm (referenceState N σ).1 := by
    rw [map_sub]
    rfl
  rw [he] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

private theorem complete_pair_bound {r : Type} [Fintype r] [DecidableEq r]
    (ρ σ : DensityState (r × Fin 2)) (hm : marginalRight ρ = marginalRight σ) :
    squareTrace.value (referenceState binaryChannel ρ) (referenceState binaryChannel σ) ≤
      (1 / 4 : ℝ) * squareTrace.value ρ σ := by
  let X := CStarMatrix.ofMatrix.symm ρ.1 - CStarMatrix.ofMatrix.symm σ.1
  have hz : partialTraceRight X = 0 := by
    ext i j
    have h := congrArg (fun τ => τ.1 i j) hm
    change (∑ c, ρ.1 (i,c) (j,c)) = ∑ c, σ.1 (i,c) (j,c) at h
    simpa [X, partialTraceRight, Finset.sum_sub_distrib] using sub_eq_zero.mpr h
  have he : CStarMatrix.ofMatrix.symm (referenceState binaryChannel ρ).1 -
      CStarMatrix.ofMatrix.symm (referenceState binaryChannel σ).1 =
      amp binaryChannel X := by
    change _ = CStarMatrix.ofMatrix.symm (referenceLinear binaryChannel
      (CStarMatrix.ofMatrix X))
    simp only [X, map_sub]
    rfl
  have hb := pinch_contract X
  have hnorm : traceNorm (amp binaryChannel X) ≤ (1 / 2 : ℝ) * traceNorm X := by
    rw [equal_marginal_action X hz,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      traceNorm_smul_nonneg _ _ (by norm_num)]
    linarith
  have ht : traceDistance (referenceState binaryChannel ρ)
      (referenceState binaryChannel σ) ≤ (1 / 2 : ℝ) * traceDistance ρ σ := by
    unfold traceDistance
    rw [he]
    change traceNorm (amp binaryChannel X) / 2 ≤ 1 / 2 * (traceNorm X / 2)
    linarith
  change traceDistance _ _ ^ 2 ≤ 1 / 4 * traceDistance ρ σ ^ 2
  have h1 := traceDistance_nonneg (referenceState binaryChannel ρ)
    (referenceState binaryChannel σ)
  have h2 := traceDistance_nonneg ρ σ
  nlinarith [mul_nonneg (sub_nonneg.mpr ht)
    (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) h2) h1)]

private theorem complete_upper : completeCoefficient squareTrace binaryChannel ≤ 1 / 4 := by
  apply csSup_le (by simp)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · rcases hx with ⟨r, fr, dr, ρ, σ, hm, hd, rfl⟩
    letI := fr
    letI := dr
    exact (div_le_iff₀ hd).mpr (complete_pair_bound ρ σ hm)

private theorem conditional_bounded : BddAbove (insert 0 (conditionalRatios squareTrace binaryChannel)) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · rcases hx with ⟨r, fr, dr, ρ, σ, hd, rfl⟩
    letI := fr
    letI := dr
    apply (div_le_one hd).mpr
    have h := reference_contract binaryChannel ρ σ
    have hs := pow_le_pow_left₀ (traceDistance_nonneg _ _) h 2
    change traceDistance _ _ ^ 2 - _ ≤ traceDistance _ _ ^ 2 - _
    exact sub_le_sub_right hs _

private def diagonalState {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) (ht : ∑ i, d i = 1) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal (fun i => (d i : ℂ))), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast hd i
  · change (∑ i, (d i : ℂ)) = 1
    exact_mod_cast ht

private def rhoProbability (p : Fin 3 × Fin 2) : ℝ :=
  ![![1 / 2, 0], ![0, 0], ![1 / 2, 0]] p.1 p.2

private def sigmaProbability (p : Fin 3 × Fin 2) : ℝ :=
  ![![0, 0], ![1 / 2, 0], ![0, 1 / 2]] p.1 p.2

private def witnessRho : DensityState (Fin 3 × Fin 2) :=
  diagonalState rhoProbability
    (by rintro ⟨i,a⟩; fin_cases i <;> fin_cases a <;> norm_num [rhoProbability])
    (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, rhoProbability])

private def witnessSigma : DensityState (Fin 3 × Fin 2) :=
  diagonalState sigmaProbability
    (by rintro ⟨i,a⟩; fin_cases i <;> fin_cases a <;> norm_num [sigmaProbability])
    (by norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, sigmaProbability])

private theorem diagonal_distance {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : DensityState n) (p q : n → ℝ)
    (hp : ρ.1 = CStarMatrix.ofMatrix (Matrix.diagonal fun i => (p i : ℂ)))
    (hq : σ.1 = CStarMatrix.ofMatrix (Matrix.diagonal fun i => (q i : ℂ))) :
    traceDistance ρ σ = (∑ i, |p i - q i|) / 2 := by
  unfold traceDistance
  rw [hp, hq]
  change traceNorm (Matrix.diagonal (fun i => (p i : ℂ)) -
    Matrix.diagonal (fun i => (q i : ℂ))) / 2 = _
  rw [← Matrix.diagonal_sub]
  have he : (fun i => (p i : ℂ) - (q i : ℂ)) = fun i => ((p i - q i : ℝ) : ℂ) := by
    funext i
    simp
  rw [he, D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]

private theorem reference_diagonal {r : Type*} [Fintype r] [DecidableEq r]
    (d : r × Fin 2 → ℝ) :
    amp binaryChannel (Matrix.diagonal fun p => (d p : ℂ)) =
      Matrix.diagonal (fun p => (weight p.2 0 : ℂ) * (d (p.1,0) : ℂ) +
        (weight p.2 1 : ℂ) * (d (p.1,1) : ℂ)) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  rw [amp_entry, binary_action]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, Prod.mk.injEq]
  · simp [Matrix.diagonal_apply, Prod.mk.injEq, hij]

private theorem marginal_diagonal {r a : Type*} [Fintype r] [DecidableEq r]
    [Fintype a] [DecidableEq a] (d : r × a → ℝ) :
    partialTraceRight (Matrix.diagonal fun p => (d p : ℂ)) =
      Matrix.diagonal (fun i => ∑ c, (d (i,c) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [partialTraceRight, Matrix.diagonal_apply]
  · simp [partialTraceRight, Matrix.diagonal_apply, Prod.mk.injEq, hij]

private theorem witness_distances :
    traceDistance witnessRho witnessSigma = 1 ∧
    traceDistance (marginalRight witnessRho) (marginalRight witnessSigma) = 1 / 2 ∧
    traceDistance (referenceState binaryChannel witnessRho)
      (referenceState binaryChannel witnessSigma) = 3 / 4 := by
  have hi := diagonal_distance witnessRho witnessSigma rhoProbability sigmaProbability rfl rfl
  have hr := diagonal_distance (marginalRight witnessRho) (marginalRight witnessSigma)
    (fun i => ∑ c, rhoProbability (i,c)) (fun i => ∑ c, sigmaProbability (i,c))
    (by
      apply CStarMatrix.ofMatrix.symm.injective
      change partialTraceRight (Matrix.diagonal fun p => (rhoProbability p : ℂ)) = _
      simpa only [Complex.ofReal_sum] using marginal_diagonal rhoProbability)
    (by
      apply CStarMatrix.ofMatrix.symm.injective
      change partialTraceRight (Matrix.diagonal fun p => (sigmaProbability p : ℂ)) = _
      simpa only [Complex.ofReal_sum] using marginal_diagonal sigmaProbability)
  have ho := diagonal_distance (referenceState binaryChannel witnessRho)
    (referenceState binaryChannel witnessSigma)
    (fun p => weight p.2 0 * rhoProbability (p.1,0) + weight p.2 1 * rhoProbability (p.1,1))
    (fun p => weight p.2 0 * sigmaProbability (p.1,0) + weight p.2 1 * sigmaProbability (p.1,1))
    (by
      apply CStarMatrix.ofMatrix.symm.injective
      change amp binaryChannel (Matrix.diagonal fun p => (rhoProbability p : ℂ)) = _
      simpa only [Complex.ofReal_add, Complex.ofReal_mul] using reference_diagonal rhoProbability)
    (by
      apply CStarMatrix.ofMatrix.symm.injective
      change amp binaryChannel (Matrix.diagonal fun p => (sigmaProbability p : ℂ)) = _
      simpa only [Complex.ofReal_add, Complex.ofReal_mul] using reference_diagonal sigmaProbability)
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two,
    rhoProbability, sigmaProbability, weight] at hi hr ho
  exact ⟨hi, hr, ho⟩

private theorem conditional_lower : (5 / 12 : ℝ) ≤ conditionalCoefficient squareTrace binaryChannel := by
  apply le_csSup conditional_bounded
  apply Set.mem_insert_of_mem
  refine ⟨Fin 3, inferInstance, inferInstance, witnessRho, witnessSigma, ?_, ?_⟩
  · change 0 < traceDistance witnessRho witnessSigma ^ 2 -
      traceDistance (marginalRight witnessRho) (marginalRight witnessSigma) ^ 2
    rw [witness_distances.1, witness_distances.2.1]
    norm_num
  · change (5 / 12 : ℝ) =
      (traceDistance (referenceState binaryChannel witnessRho)
        (referenceState binaryChannel witnessSigma) ^ 2 -
        traceDistance (marginalRight witnessRho) (marginalRight witnessSigma) ^ 2) /
      (traceDistance witnessRho witnessSigma ^ 2 -
        traceDistance (marginalRight witnessRho) (marginalRight witnessSigma) ^ 2)
    rw [witness_distances.1, witness_distances.2.1, witness_distances.2.2]
    norm_num

/-- A faithful divergence and an actual finite CPTP channel give a strict gap,
with both optimizations ranging over every finite quantum reference. -/
theorem result : ∃ (D : FiniteDivergence) (N : QuantumChannel (Fin 2) (Fin 2)),
    completeCoefficient D N ≤ 1 / 4 ∧ (1 / 4 : ℝ) < 5 / 12 ∧
      (5 / 12 : ℝ) ≤ conditionalCoefficient D N := by
  exact ⟨squareTrace, binaryChannel, complete_upper, by norm_num, conditional_lower⟩

#print axioms result

end D5.S3.Quantum.Divergence.FaithfulConditionalGap
