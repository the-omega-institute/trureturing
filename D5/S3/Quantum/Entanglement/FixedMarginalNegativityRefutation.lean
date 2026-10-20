/- GID: D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim; result=D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result; claim=D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim
   digest: Fixed two-qutrit marginals admit greater negativity than the Baio et al. candidate. -/

import D5.S3.QuantumBounds.NegativityReductionInclusionRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.FixedMarginalNegativityRefutation

open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (IsDensity)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight partialTraceLeft_kronecker partialTraceRight_kronecker)

/-- The ordered diagonal marginal of Eq. (24), for both `ρ_A` and `ρ_B`. -/
noncomputable def orderedMarginal (x₁ x₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![((1 - x₁ - x₂ : ℝ) : ℂ), (x₁ : ℂ), (x₂ : ℂ)]

/-- The candidate of Eq. (27), written in the matrix form of Eq. (30). -/
noncomputable def candidate (l₁ l₂ m₁ m₂ : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let φ : Fin 3 × Fin 3 → ℂ := Function.uncurry
    ![![(Real.sqrt (1 - l₁ - l₂) : ℂ), 0, 0],
      ![0, (Real.sqrt m₁ : ℂ), 0], ![0, 0, (Real.sqrt m₂ : ℂ)]]
  vecMulVec φ (star φ) + diagonal (Function.uncurry
    ![![0, 0, 0], ![((l₁ - m₁ : ℝ) : ℂ), 0, 0], ![((l₂ - m₂ : ℝ) : ℂ), 0, 0]])

/-- Baio et al., arXiv:1904.07650v2, Section IV: the fixed-marginal maximizing
conjecture restricted to the parameter region of Eq. (27). -/
def claim : Prop :=
  ∀ (l₁ l₂ m₁ m₂ : ℝ),
    l₂ ≤ l₁ → l₁ ≤ 1 - l₁ - l₂ → 0 ≤ l₂ →
    m₂ ≤ m₁ → m₁ ≤ 1 - m₁ - m₂ → 0 ≤ m₂ →
    m₁ + m₂ ≤ l₁ + l₂ → m₁ < l₁ → m₂ < l₂ →
    ∀ R : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      IsDensity R → partialTraceRight R = orderedMarginal l₁ l₂ →
      partialTraceLeft R = orderedMarginal m₁ m₂ →
      negativity R ≤ negativity (candidate l₁ l₂ m₁ m₂)

private noncomputable def chi : Fin 3 × Fin 3 → ℂ :=
  Function.uncurry ![![7/10, 0, 0], ![0, 0, 1/10], ![0, 1/5, 0]]

private noncomputable def rho0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  vecMulVec chi (star chi) + diagonal
    (Function.uncurry ![![0, 0, 0], ![45/100, 1/100, 0], ![0, 0, 0]])

private noncomputable def rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (99/100 : ℂ) • rho0 + (1/100 : ℂ) •
    (orderedMarginal (47/100) (4/100) ⊗ₖ orderedMarginal (5/100) (1/100))

private theorem rho_density : IsDensity rho := by
  constructor
  · apply PosSemidef.add
    · apply PosSemidef.smul (a := (99/100 : ℂ))
      · apply (posSemidef_vecMulVec_self_star chi).add
        apply PosSemidef.diagonal
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> norm_num [Complex.le_def, Matrix.cons_val_two]
      · norm_num [Complex.le_def, Matrix.cons_val_two]
    · apply PosSemidef.smul (a := (1/100 : ℂ))
      · simp only [orderedMarginal.eq_1, diagonal_kronecker_diagonal]
        apply PosSemidef.diagonal
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> norm_num [Complex.le_def, Matrix.cons_val_two]
      · norm_num [Complex.le_def, Matrix.cons_val_two]
  · norm_num [rho.eq_1, rho0.eq_1, chi.eq_1, orderedMarginal.eq_1,
      Matrix.trace, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem rho_marginalA : partialTraceRight rho = orderedMarginal (47/100) (4/100) := by
  have h0 : partialTraceRight rho0 = orderedMarginal (47/100) (4/100) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [partialTraceRight, rho0.eq_1, chi.eq_1,
        orderedMarginal.eq_1, Matrix.vecMulVec_apply,
        Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]
  have ht : (orderedMarginal (5/100) (1/100)).trace = 1 := by
    norm_num [orderedMarginal.eq_1, Matrix.trace, Fin.sum_univ_three,
      Matrix.cons_val_two]
  rw [rho.eq_1]
  ext i j
  simp only [partialTraceRight, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  change (99/100 : ℂ) * partialTraceRight rho0 i j + (1/100 : ℂ) *
    partialTraceRight (orderedMarginal (47/100) (4/100) ⊗ₖ orderedMarginal (5/100) (1/100)) i j = _
  erw [h0, partialTraceRight_kronecker
    (orderedMarginal (47/100) (4/100)) (orderedMarginal (5/100) (1/100)), ht]
  simp only [one_smul]
  ring

private theorem rho_marginalB : partialTraceLeft rho = orderedMarginal (5/100) (1/100) := by
  have h0 : partialTraceLeft rho0 = orderedMarginal (5/100) (1/100) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [partialTraceLeft, rho0.eq_1, chi.eq_1,
        orderedMarginal.eq_1, Matrix.vecMulVec_apply,
        Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]
  have ht : (orderedMarginal (47/100) (4/100)).trace = 1 := by
    norm_num [orderedMarginal.eq_1, Matrix.trace, Fin.sum_univ_three,
      Matrix.cons_val_two]
  rw [rho.eq_1]
  ext i j
  simp only [partialTraceLeft, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  change (99/100 : ℂ) * partialTraceLeft rho0 i j + (1/100 : ℂ) *
    partialTraceLeft (orderedMarginal (47/100) (4/100) ⊗ₖ orderedMarginal (5/100) (1/100)) i j = _
  erw [h0, partialTraceLeft_kronecker
    (orderedMarginal (47/100) (4/100)) (orderedMarginal (5/100) (1/100)), ht]
  simp only [one_smul]
  ring


private noncomputable def rhoPT : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    if p = q then (Function.uncurry
      ![![244853/500000, 49/200000, 49/1000000],
        ![224959/500000, 2027/200000, 9947/1000000],
        ![47/125000, 1981/50000, 1/250000]]) p
    else if (p = (0, 1) ∧ q = (2, 0)) ∨ (p = (2, 0) ∧ q = (0, 1)) then 693/5000
    else if (p = (0, 2) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 2)) then 693/10000
    else if (p = (1, 1) ∧ q = (2, 2)) ∨ (p = (2, 2) ∧ q = (1, 1)) then 99/5000
    else 0

private theorem rho_pt_eq : partialTranspose rho = rhoPT := by
  ext ⟨i, j⟩ ⟨k, l⟩
  change rho (i, l) (k, j) = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
      Fin.reduceFinMk, rho.eq_1, rho0.eq_1, chi.eq_1, rhoPT.eq_1,
      orderedMarginal.eq_1, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Matrix.cons_val_two, map_ofNat]

private noncomputable def K : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let a : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 1, 0], ![0, 0, 0], ![-1, 0, 0]]
  let b : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 7], ![-1, 0, 0], ![0, 0, 0]]
  let c : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 0], ![0, 1, 0], ![0, 0, -1]]
  (1/2 : ℂ) • vecMulVec a (star a) + (1/50 : ℂ) • vecMulVec b (star b) +
    (1/2 : ℂ) • vecMulVec c (star c)

private theorem K_hermitian : K.IsHermitian := by
  exact (((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])).add
    ((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])) |>.add
    ((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def]))).isHermitian

set_option maxHeartbeats 1000000 in
-- The certificate checks all 81 entries of the rational projector product.
private theorem K_idempotent : K * K = K := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [K.eq_1, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem reflection_unitary : (1 - (2 : ℂ) • K) ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
  have hp : IsStarProjection K := ⟨K_idempotent, K_hermitian⟩
  have heq : (1 - (2 : ℂ) • K) = 2 * (1 - K) - 1 := by
    rw [two_mul, two_smul]
    abel
  rw [heq]
  exact hp.one_sub.two_mul_sub_one_mem_unitary

private theorem reflection_trace :
    ((1 - (2 : ℂ) • K) * partialTranspose rho).trace =
      1 + 2 * (8168881/50000000 : ℂ) := by
  rw [rho_pt_eq]
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
    Fin.reduceFinMk, K.eq_1, rhoPT.eq_1, Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two,
    map_ofNat]

private theorem rho_negativity_lower : (8168881/50000000 : ℝ) ≤ negativity rho := by
  have h := (traceNorm_eq_max_re_tr_U (partialTranspose rho)).2
    ⟨⟨1 - (2 : ℂ) • K, reflection_unitary⟩, rfl⟩
  rw [reflection_trace] at h
  norm_num at h
  rw [negativity]
  linarith

private noncomputable def sigma : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let φ : Fin 3 × Fin 3 → ℂ := Function.uncurry
    ![![7/10, 0, 0], ![0, (Real.sqrt 5 : ℂ)/10, 0], ![0, 0, 1/10]]
  vecMulVec φ (star φ) + diagonal
    (Function.uncurry ![![0, 0, 0], ![42/100, 0, 0], ![3/100, 0, 0]])

private theorem candidate_eq_sigma : candidate (47/100) (4/100) (5/100) (1/100) = sigma := by
  have h49 : Real.sqrt (1 - 47/100 - 4/100) = 7/10 := by norm_num
  have h5 : Real.sqrt (5/100) = Real.sqrt 5 / 10 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  have h1 : Real.sqrt (1/100) = 1/10 := by norm_num
  rw [candidate.eq_1, sigma.eq_1, h49, h5, h1]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.vecMulVec_apply,
      Matrix.cons_val_two, map_ofNat]

private noncomputable def ptPositive : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let a : Fin 3 × Fin 3 → ℂ := Function.uncurry
    ![![0, 35, 0], ![47 * (Real.sqrt 5 : ℂ), 0, 0], ![0, 0, 0]]
  let b : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 35], ![0, 0, 0], ![43, 0, 0]]
  let c : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]]
  diagonal (Function.uncurry ![![49/100, 0, 0], ![0, 5/100, 0], ![0, 0, 1/100]]) +
    (1/26000 : ℂ) • vecMulVec a (star a) + (1/35500 : ℂ) • vecMulVec b (star b) +
    ((Real.sqrt 5 : ℂ)/200) • vecMulVec c (star c)

private noncomputable def ptNegative : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let a : Fin 3 × Fin 3 → ℂ := Function.uncurry
    ![![0, 7, 0], ![-(Real.sqrt 5 : ℂ), 0, 0], ![0, 0, 0]]
  let b : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 35], ![0, 0, 0], ![-28, 0, 0]]
  let c : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]]
  (1/1040 : ℂ) • vecMulVec a (star a) + (1/35500 : ℂ) • vecMulVec b (star b) +
    ((Real.sqrt 5 : ℂ)/200) • vecMulVec c (star c)

private noncomputable def positiveEntries : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    if p = q then (Function.uncurry
      ![![49/100, 49/1040, 49/1420], ![2209/5200, 1/20, (Real.sqrt 5 : ℂ)/200],
        ![1849/35500, (Real.sqrt 5 : ℂ)/200, 1/100]]) p
    else if (p = (0, 1) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 1)) then
      329 * (Real.sqrt 5 : ℂ)/5200
    else if (p = (0, 2) ∧ q = (2, 0)) ∨ (p = (2, 0) ∧ q = (0, 2)) then 301/7100
    else if (p = (1, 2) ∧ q = (2, 1)) ∨ (p = (2, 1) ∧ q = (1, 2)) then
      (Real.sqrt 5 : ℂ)/200
    else 0

private noncomputable def negativeEntries : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    if p = q then (Function.uncurry
      ![![0, 49/1040, 49/1420], ![1/208, 0, (Real.sqrt 5 : ℂ)/200],
        ![196/8875, (Real.sqrt 5 : ℂ)/200, 0]]) p
    else if (p = (0, 1) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 1)) then
      -7 * (Real.sqrt 5 : ℂ)/1040
    else if (p = (0, 2) ∧ q = (2, 0)) ∨ (p = (2, 0) ∧ q = (0, 2)) then -49/1775
    else if (p = (1, 2) ∧ q = (2, 1)) ∨ (p = (2, 1) ∧ q = (1, 2)) then
      -(Real.sqrt 5 : ℂ)/200
    else 0

private theorem sqrt5_square : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5))

private theorem positive_entries_eq : ptPositive = positiveEntries := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
      Fin.reduceFinMk, ptPositive.eq_1, positiveEntries.eq_1, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, map_ofNat] <;>
    ring_nf
  all_goals norm_num [sqrt5_square]

private theorem negative_entries_eq : ptNegative = negativeEntries := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
      Fin.reduceFinMk, ptNegative.eq_1, negativeEntries.eq_1, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, map_ofNat] <;>
    ring_nf
  all_goals norm_num [sqrt5_square]

private theorem sigma_pt_split : partialTranspose sigma = ptPositive - ptNegative := by
  rw [positive_entries_eq, negative_entries_eq]
  ext ⟨i, j⟩ ⟨k, l⟩
  change sigma (i, l) (k, j) = _
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
      Fin.reduceFinMk, sigma.eq_1, positiveEntries.eq_1,
      negativeEntries.eq_1, Matrix.vecMulVec_apply, Matrix.cons_val_two, map_ofNat] <;>
    ring_nf
  all_goals norm_num [sqrt5_square]

private theorem positive_psd : ptPositive.PosSemidef := by
  rw [ptPositive.eq_1]
  apply PosSemidef.add
  · apply PosSemidef.add
    · apply PosSemidef.add
      · apply PosSemidef.diagonal
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> norm_num [Complex.le_def, Matrix.cons_val_two]
      · exact (posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])
    · exact (posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])
  · exact (posSemidef_vecMulVec_self_star _).smul (by positivity)

private theorem negative_psd : ptNegative.PosSemidef := by
  rw [ptNegative.eq_1]
  exact (((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])).add
    ((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def]))).add
    ((posSemidef_vecMulVec_self_star _).smul (by positivity))

private theorem positive_trace :
    ptPositive.trace = 1 + (100159/923000 : ℂ) + (Real.sqrt 5 : ℂ)/100 := by
  rw [positive_entries_eq]
  norm_num [positiveEntries.eq_1, Matrix.trace, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

private theorem negative_trace :
    ptNegative.trace = (100159/923000 : ℂ) + (Real.sqrt 5 : ℂ)/100 := by
  rw [negative_entries_eq]
  norm_num [negativeEntries.eq_1, Matrix.trace, Fintype.sum_prod_type,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring

private theorem candidate_negativity_upper :
    negativity (candidate (47/100) (4/100) (5/100) (1/100)) ≤
      100159/923000 + Real.sqrt 5 / 100 := by
  have htriangle := traceNorm_add_le ptPositive (-ptNegative)
  rw [traceNorm_neg, ← sub_eq_add_neg, ← sigma_pt_split] at htriangle
  have hp := congrArg Complex.re (traceNorm_of_posSemidef positive_psd)
  have hq := congrArg Complex.re (traceNorm_of_posSemidef negative_psd)
  change traceNorm ptPositive = ptPositive.trace.re at hp
  change traceNorm ptNegative = ptNegative.trace.re at hq
  rw [positive_trace] at hp
  rw [negative_trace] at hq
  norm_num at hp hq
  rw [candidate_eq_sigma, negativity]
  linarith

/-- At marginals `diag(49,47,4)/100` and `diag(94,5,1)/100`, the candidate
has negativity below `7/50`, whereas a density matrix with the same marginals exceeds it. -/
theorem result : ¬ claim := by
  intro hclaim
  have hmax := hclaim (47/100) (4/100) (5/100) (1/100)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    rho rho_density rho_marginalA rho_marginalB
  have hsqrt : Real.sqrt 5 < 5/2 := by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hsmall : negativity (candidate (47/100) (4/100) (5/100) (1/100)) < 7/50 := by
    linarith [candidate_negativity_upper]
  have hlarge : (7/50 : ℝ) < negativity rho :=
    lt_of_lt_of_le (by norm_num) rho_negativity_lower
  exact (not_lt_of_ge hmax) (hsmall.trans hlarge)

end D5.S3.Quantum.Entanglement.FixedMarginalNegativityRefutation
