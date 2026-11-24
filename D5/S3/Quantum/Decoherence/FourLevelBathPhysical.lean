/- GID: D5/S3/Quantum/Decoherence/FourLevelBathPhysical
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/FourLevelBathPhysical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact coordinate pinching and endpoint bath return for a fixed four-level Gibbs bath. -/

import D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation
import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality
import Mathlib.Data.Matrix.Block

/-! Exact qutrit pinching with a fixed, nondegenerate four-level Gibbs bath. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Decoherence.FourLevelBathPhysical

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
open GibbsBathBandwidth (diagonalReal gibbsWeight gibbsWeight_pos matchingEnergies)
open D5.S3.QuantumChannels.CoolingMapThermalOperationRefutation (IsEnergyConserving)
open D5.S3.QuantumChannels.ThermalOperationDegeneracyRefutation (operation)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (basisProjector projectiveReadout)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality (recordGram)

abbrev System := Fin 3
abbrev Bath := Fin 4
abbrev Qutrit := Matrix System System ℂ
abbrev Joint := Matrix (System × Bath) (System × Bath) ℂ

abbrev inputMatrix (ρ : DensityState System) : Qutrit := CStarMatrix.ofMatrix.symm ρ.1

/-- The initial state is a product with the prescribed diagonal bath state. -/
def jointOutput (p : Bath → ℝ) (U : Joint) (X : Qutrit) : Joint :=
  U * (X ⊗ₖ diagonalReal p) * Uᴴ

/-- Heat is positive for an increase of bath mean energy. -/
def bathHeat (E p : Bath → ℝ) (U : Joint) (X : Qutrit) : ℝ :=
  (diagonalReal E * partialTraceLeft (jointOutput p U X)).trace.re -
    (diagonalReal E * diagonalReal p).trace.re

/-- The actual joint matrix has one diagonal qutrit unitary per bath energy. -/
def phaseUnitary (z : Bath → System → ℂ) : Joint :=
  blockDiagonal (fun b => diagonal (z b))

/-- The record amplitudes, with bath levels as rows and system labels as columns. -/
def weightedColumns (p : Bath → ℝ) (z : Bath → System → ℂ) : Matrix Bath System ℂ :=
  fun b i => (Real.sqrt (p b) : ℂ) * z b i

private theorem energy_form {E : Bath → ℝ} (hE : Function.Injective E)
    {U : Joint} (hU : IsEnergyConserving (fun _ => 0) E U) :
    U = blockDiagonal (blockDiag U) := by
  apply Matrix.ext
  rintro ⟨i, b⟩ ⟨j, c⟩
  by_cases hbc : b = c
  · subst c
    exact (blockDiagonal_apply_eq (blockDiag U) i j b).symm
  · rw [blockDiagonal_apply_ne (blockDiag U) i j hbc]
    have h := congrArg (fun M : Joint => M (i, b) (j, c)) hU
    change
      (U * diagonal (fun x : System × Bath => ((0 + E x.2 : ℝ) : ℂ))) (i, b) (j, c) =
        (diagonal (fun x : System × Bath => ((0 + E x.2 : ℝ) : ℂ)) * U) (i, b) (j, c)
      at h
    simp only [mul_diagonal, diagonal_mul, zero_add] at h
    by_contra hn
    apply hbc
    apply hE
    apply Complex.ofReal_injective
    exact (mul_left_cancel₀ hn (h.trans (mul_comm _ _))).symm

private theorem unitary_blocks {U : Joint}
    (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (hform : U = blockDiagonal (blockDiag U)) (b : Bath) :
    blockDiag U b ∈ Matrix.unitaryGroup System ℂ := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.star_eq_conjTranspose, hform, blockDiagonal_conjTranspose,
    ← blockDiagonal_mul] at h
  have hOne : blockDiagonal (1 : Bath → Qutrit) = (1 : Joint) := blockDiagonal_one
  have hblocks : (fun c => (blockDiag U c)ᴴ * blockDiag U c) = (1 : Bath → Qutrit) :=
    blockDiagonal_injective (h.trans hOne.symm)
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose]
  exact congrFun hblocks b

private theorem jointOutput_blocks (p : Bath → ℝ) (V : Bath → Qutrit) (X : Qutrit) :
    jointOutput p (blockDiagonal V) X =
      blockDiagonal (fun b => (p b : ℂ) • (V b * X * (V b)ᴴ)) := by
  have hprod : X ⊗ₖ diagonalReal p = blockDiagonal (fun b => (p b : ℂ) • X) := by
    apply Matrix.ext
    rintro ⟨i, b⟩ ⟨j, c⟩
    by_cases h : b = c
    · subst c
      simp [diagonalReal, Matrix.smul_apply, mul_comm]
    · simp [diagonalReal, blockDiagonal_apply, diagonal_apply_ne, h]
  rw [jointOutput, hprod, blockDiagonal_conjTranspose, ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  apply congrArg blockDiagonal
  funext b
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem system_output_of_blocks (p : Bath → ℝ) (V : Bath → Qutrit) (X : Qutrit)
    (i j : System) :
    partialTraceRight (jointOutput p (blockDiagonal V) X) i j =
      ∑ b, (p b : ℂ) * (V b * X * (V b)ᴴ) i j := by
  simp [jointOutput_blocks, partialTraceRight, Matrix.smul_apply]

private theorem projector_population (p : Bath → ℝ) (V : Bath → Qutrit) (i j : System) :
    (partialTraceRight (jointOutput p (blockDiagonal V) (basisProjector j)) i i).re =
      ∑ b, p b * Complex.normSq (V b i j) := by
  rw [system_output_of_blocks]
  have hterm (b : Bath) :
      (p b : ℂ) * (V b * basisProjector j * (V b)ᴴ) i i =
        ((p b * Complex.normSq (V b i j) : ℝ) : ℂ) := by
    have hentry : (V b * basisProjector j * (V b)ᴴ) i i =
        V b i j * star (V b i j) := by
      rw [Matrix.mul_apply, basisProjector, Finset.sum_eq_single j]
      · simp only [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]
      · intro k _ hkj
        rw [Matrix.mul_single_apply_of_ne (1 : ℂ) j j i k hkj (V b), zero_mul]
      · simp
    rw [hentry, Complex.star_def, Complex.mul_conj, Complex.ofReal_mul]
  simp only [hterm, Complex.re_sum, Complex.ofReal_re]

private theorem diagonal_of_fixed_projectors {p : Bath → ℝ} (hp : ∀ b, 0 < p b)
    {V : Bath → Qutrit}
    (hfix : ∀ j, partialTraceRight (jointOutput p (blockDiagonal V) (basisProjector j)) =
      projectiveReadout (basisProjector j)) (b : Bath) (i j : System) (hij : i ≠ j) :
    V b i j = 0 := by
  have hpop : (∑ c, p c * Complex.normSq (V c i j)) = 0 := by
    rw [← projector_population, hfix j]
    simp [projectiveReadout, Matrix.diag_apply, basisProjector, Matrix.single, Ne.symm hij]
  have hnonneg (c : Bath) : 0 ≤ p c * Complex.normSq (V c i j) :=
    mul_nonneg (hp c).le (Complex.normSq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hnonneg c)).mp hpop
    b (Finset.mem_univ b)
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hp b).ne')

private theorem phase_normal_form {β : ℝ} {E : Bath → ℝ} (hE : Function.Injective E)
    {U : Joint} (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (henergy : IsEnergyConserving (fun _ => 0) E U)
    (hfix : ∀ j, operation β E U (basisProjector j) = projectiveReadout (basisProjector j)) :
    ∃ z : Bath → System → ℂ, U = phaseUnitary z ∧ ∀ b i, Complex.normSq (z b i) = 1 := by
  let V : Bath → Qutrit := blockDiag U
  have hform : U = blockDiagonal V := energy_form hE henergy
  have hfix' (j : System) :
      partialTraceRight (jointOutput (gibbsWeight β E) (blockDiagonal V) (basisProjector j)) =
        projectiveReadout (basisProjector j) := by
    rw [← hform]
    exact hfix j
  let z : Bath → System → ℂ := fun b i => V b i i
  have hdiag (b : Bath) : V b = diagonal (z b) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [z]
    · rw [diagonal_apply_ne _ hij]
      exact diagonal_of_fixed_projectors (gibbsWeight_pos β E) hfix' b i j hij
  refine ⟨z, hform.trans (congrArg blockDiagonal (funext hdiag)), ?_⟩
  intro b i
  have hb := Matrix.mem_unitaryGroup_iff'.mp (unitary_blocks hU hform b)
  change star (V b) * V b = 1 at hb
  rw [Matrix.star_eq_conjTranspose, hdiag b, diagonal_conjTranspose,
    diagonal_mul_diagonal] at hb
  have hi := congrArg (fun M : Qutrit => (M i i).re) hb
  simpa only [diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.one_re] using hi

private theorem phaseUnitary_unitary (z : Bath → System → ℂ)
    (hz : ∀ b i, Complex.normSq (z b i) = 1) :
    phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [phaseUnitary, Matrix.star_eq_conjTranspose, blockDiagonal_diagonal,
    diagonal_conjTranspose, diagonal_mul_diagonal]
  apply diagonal_eq_one.mpr
  funext x
  change star (z x.2 x.1) * z x.2 x.1 = 1
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hz, Complex.ofReal_one]

private theorem phaseUnitary_energy (E : Bath → ℝ) (z : Bath → System → ℂ) :
    IsEnergyConserving (fun _ => 0) E (phaseUnitary z) := by
  unfold IsEnergyConserving phaseUnitary
  simp only [blockDiagonal_diagonal, diagonal_mul_diagonal]
  exact congrArg diagonal (funext fun x => mul_comm _ _)

private theorem phase_output_entry (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (X : Qutrit) (i j : System) :
    partialTraceRight (jointOutput p (phaseUnitary z) X) i j =
      ((weightedColumns p z)ᴴ * weightedColumns p z) j i * X i j := by
  let r : System → Bath → ℂ := fun i b => weightedColumns p z b i
  have hGram : recordGram r i j = ((weightedColumns p z)ᴴ * weightedColumns p z) j i := by
    simp only [recordGram, Matrix.mul_apply, Matrix.conjTranspose_apply, r]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  rw [← hGram, recordGram, Finset.sum_mul, phaseUnitary, system_output_of_blocks]
  apply Finset.sum_congr rfl
  intro b _
  simp only [diagonal_conjTranspose, mul_diagonal, diagonal_mul, weightedColumns,
    r, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  have hs : ((Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ)) = (p b : ℂ) := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (hp b)]
  calc
    _ = ((Real.sqrt (p b) : ℂ) * (Real.sqrt (p b) : ℂ)) *
        (z b i * X i j * star (z b j)) := by rw [hs, Complex.star_def]
    _ = _ := by
      simp only [Complex.star_def]
      ring

private theorem phase_output_eq_pinching (p : Bath → ℝ) (hp : ∀ b, 0 ≤ p b)
    (z : Bath → System → ℂ) (hGram : (weightedColumns p z)ᴴ * weightedColumns p z = 1)
    (X : Qutrit) :
    partialTraceRight (jointOutput p (phaseUnitary z) X) = projectiveReadout X := by
  apply Matrix.ext
  intro i j
  rw [phase_output_entry p hp, hGram]
  by_cases hij : i = j
  · subst j
    simp [projectiveReadout, Matrix.diag_apply]
  · simp [projectiveReadout, hij, Ne.symm hij]

private def densityOfMatrix (X : Qutrit) (hX : X.PosSemidef) (htr : X.trace = 1) :
    DensityState System :=
  ⟨CStarMatrix.ofMatrix X, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg, htr⟩

private theorem densityOfMatrix_value (X : Qutrit) (hX : X.PosSemidef) (htr : X.trace = 1) :
    inputMatrix (densityOfMatrix X hX htr) = X := rfl

private theorem basisProjector_posSemidef (j : System) : (basisProjector j).PosSemidef := by
  rw [basisProjector, ← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
  intro i
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

private def coherentProbe : Qutrit := Matrix.of (fun _ _ => (1 / 3 : ℂ))

private theorem coherentProbe_posSemidef : coherentProbe.PosSemidef := by
  have h :
      coherentProbe =
        (1 / 3 : ℝ) • Matrix.vecMulVec (fun _ : System => (1 : ℂ)) (fun _ : System => 1) := by
    apply Matrix.ext
    intro i j
    simp [coherentProbe, Matrix.vecMulVec_apply, Matrix.smul_apply, Complex.real_smul]
  rw [h]
  have hstar : star (fun _ : System => (1 : ℂ)) = fun _ : System => 1 := by
    funext i
    exact star_one ℂ
  simpa only [hstar] using
    (Matrix.posSemidef_vecMulVec_self_star (fun _ : System => (1 : ℂ))).smul
      (show 0 ≤ (1 / 3 : ℝ) by norm_num)

private theorem coherentProbe_trace : coherentProbe.trace = 1 := by
  norm_num [coherentProbe, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]

/-- Exact pinching on density states is equivalent to the weighted phase Gram
condition for the same fixed bath energies and Gibbs weights. -/
theorem fixed_bath_pinching_iff (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E) :
    (∃ U : Matrix.unitaryGroup (System × Bath) ℂ,
      IsEnergyConserving (fun _ => 0) E (U : Joint) ∧
      ∀ ρ : DensityState System,
        operation β E (U : Joint) (inputMatrix ρ) = projectiveReadout (inputMatrix ρ)) ↔
    ∃ z : Bath → System → ℂ, (∀ b i, Complex.normSq (z b i) = 1) ∧
      (weightedColumns (gibbsWeight β E) z)ᴴ * weightedColumns (gibbsWeight β E) z = 1 := by
  let p := gibbsWeight β E
  have hp (b : Bath) : 0 ≤ p b := (gibbsWeight_pos β E b).le
  constructor
  · rintro ⟨U, henergy, hpinch⟩
    have hfix (j : System) :
        operation β E (U : Joint) (basisProjector j) = projectiveReadout (basisProjector j) := by
      have htr : (basisProjector j).trace = 1 := by
        simp [basisProjector]
      simpa only [densityOfMatrix_value] using
        hpinch (densityOfMatrix (basisProjector j) (basisProjector_posSemidef j) htr)
    obtain ⟨z, hU, hz⟩ := phase_normal_form hE U.property henergy hfix
    have hprobe := hpinch
      (densityOfMatrix coherentProbe coherentProbe_posSemidef coherentProbe_trace)
    simp only [densityOfMatrix_value, hU] at hprobe
    change partialTraceRight (jointOutput p (phaseUnitary z) coherentProbe) =
      projectiveReadout coherentProbe at hprobe
    refine ⟨z, hz, ?_⟩
    apply Matrix.ext
    intro i j
    have h := congrArg (fun M : Qutrit => M j i) hprobe
    change partialTraceRight (jointOutput p (phaseUnitary z) coherentProbe) j i =
      projectiveReadout coherentProbe j i at h
    rw [phase_output_entry p hp] at h
    have hr : projectiveReadout coherentProbe j i =
        (1 : Qutrit) i j * (1 / 3 : ℂ) := by
      by_cases hij : i = j
      · subst j
        simp [projectiveReadout, Matrix.diag_apply, coherentProbe]
      · simp [projectiveReadout, hij, Ne.symm hij]
    rw [hr] at h
    change ((weightedColumns p z)ᴴ * weightedColumns p z) i j * (1 / 3 : ℂ) =
      (1 : Qutrit) i j * (1 / 3 : ℂ) at h
    exact mul_right_cancel₀ (by norm_num : (1 / 3 : ℂ) ≠ 0) h
  · rintro ⟨z, hz, hGram⟩
    refine ⟨⟨phaseUnitary z, phaseUnitary_unitary z hz⟩, phaseUnitary_energy E z, ?_⟩
    intro ρ
    exact phase_output_eq_pinching p hp z hGram (inputMatrix ρ)

/-- The phase witness implements pinching on the entire qutrit matrix algebra. -/
theorem phase_implements_pinching (β : ℝ) (E : Bath → ℝ) (z : Bath → System → ℂ)
    (hGram : (weightedColumns (gibbsWeight β E) z)ᴴ *
      weightedColumns (gibbsWeight β E) z = 1) (X : Qutrit) :
    operation β E (phaseUnitary z) X = projectiveReadout X :=
  phase_output_eq_pinching (gibbsWeight β E) (fun b => (gibbsWeight_pos β E b).le)
    z hGram X

/-- Every energy-preserving joint unitary for these distinct fixed energies
returns the diagonal bath on trace-one inputs. -/
theorem bath_return {E : Bath → ℝ} (hE : Function.Injective E) (p : Bath → ℝ)
    {U : Joint} (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (henergy : IsEnergyConserving (fun _ => 0) E U) {X : Qutrit} (hX : X.trace = 1) :
    partialTraceLeft (jointOutput p U X) = diagonalReal p := by
  let V : Bath → Qutrit := blockDiag U
  have hform : U = blockDiagonal V := energy_form hE henergy
  have hunit (b : Bath) : (V b)ᴴ * V b = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (unitary_blocks hU hform b)
  rw [hform, jointOutput_blocks]
  apply Matrix.ext
  intro b c
  by_cases hbc : b = c
  · subst c
    change (∑ i : System, blockDiagonal
      (fun c => (p c : ℂ) • (V c * X * (V c)ᴴ)) (i, b) (i, b)) = diagonalReal p b b
    simp only [blockDiagonal_apply_eq, diagonalReal, diagonal_apply_eq]
    change ((p b : ℂ) • (V b * X * (V b)ᴴ)).trace = (p b : ℂ)
    rw [trace_smul, trace_mul_cycle, hunit b, Matrix.one_mul, hX, smul_eq_mul, mul_one]
  · simp [partialTraceLeft, blockDiagonal_apply, diagonalReal, diagonal_apply_ne, hbc]

/-- The bath energy increase vanishes on every density input. -/
theorem zero_heat {E : Bath → ℝ} (hE : Function.Injective E) (p : Bath → ℝ)
    {U : Joint} (hU : U ∈ Matrix.unitaryGroup (System × Bath) ℂ)
    (henergy : IsEnergyConserving (fun _ => 0) E U) (ρ : DensityState System) :
    bathHeat E p U (inputMatrix ρ) = 0 := by
  have htr : (inputMatrix ρ).trace = 1 := ρ.trace_eq_one
  rw [bathHeat, bath_return hE p hU henergy htr, sub_self]

/-- The phase witness gives an energy-preserving unitary, exact pinching on
every matrix, and bath return and zero heat on every density state. -/
theorem phase_realization (β : ℝ) (E : Bath → ℝ) (hE : Function.Injective E)
    (z : Bath → System → ℂ) (hz : ∀ b i, Complex.normSq (z b i) = 1)
    (hGram : (weightedColumns (gibbsWeight β E) z)ᴴ *
      weightedColumns (gibbsWeight β E) z = 1) :
    phaseUnitary z ∈ Matrix.unitaryGroup (System × Bath) ℂ ∧
      IsEnergyConserving (fun _ => 0) E (phaseUnitary z) ∧
      (∀ X, operation β E (phaseUnitary z) X = projectiveReadout X) ∧
      ∀ ρ : DensityState System,
        partialTraceLeft (jointOutput (gibbsWeight β E) (phaseUnitary z) (inputMatrix ρ)) =
          diagonalReal (gibbsWeight β E) ∧
        bathHeat E (gibbsWeight β E) (phaseUnitary z) (inputMatrix ρ) = 0 := by
  have hU := phaseUnitary_unitary z hz
  have henergy := phaseUnitary_energy E z
  refine ⟨hU, henergy, phase_implements_pinching β E z hGram, ?_⟩
  intro ρ
  exact ⟨bath_return hE _ hU henergy ρ.trace_eq_one, zero_heat hE _ hU henergy ρ⟩

/-- If the energies may be chosen, a positive distinct law is the Gibbs law
of a bath with distinct energies at the specified positive inverse temperature. -/
theorem matching_distinct_energies {β : ℝ} (hβ : 0 < β) (p : Bath → ℝ)
    (hp : ∀ b, 0 < p b) (hpSum : ∑ b, p b = 1) (hpDistinct : Function.Injective p) :
    Function.Injective (matchingEnergies β p) ∧ gibbsWeight β (matchingEnergies β p) = p := by
  have hexp (b : Bath) : Real.exp (-β * matchingEnergies β p b) = p b := by
    rw [matchingEnergies, ← mul_assoc, neg_mul_neg, mul_inv_cancel₀ hβ.ne',
      one_mul, Real.exp_log (hp b)]
  refine ⟨fun b c h => hpDistinct (by rw [← hexp b, ← hexp c, h]), ?_⟩
  funext b
  simp only [gibbsWeight, hexp, hpSum, div_one]

end D5.S3.Quantum.Decoherence.FourLevelBathPhysical
