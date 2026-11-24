/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The product-anchor quadratic uses the log resolvent metric and two measured Fisher forms. -/

import D5.S3.Divergence.LogDerivTrace
import D5.S3.Quantum.Information.PartialTrace.Isometries
import D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

/-!
Qian, arXiv:2608.14806v2, (39) and Definition 7.2. The variables are actual
density matrices and a Hermitian tangent with both partial traces zero.
Bob's computational basis is indexed by ZMod 3, with the usual Fin 3 relabeling.
The resolvent term uses the existing matrix logarithm derivative.
-/

noncomputable section

namespace AnchorMeasurement

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)

abbrev Alice := Fin 2
abbrev Bob := ZMod 3
abbrev Joint := Alice × Bob
abbrev Mat (n : Type*) := Matrix n n ℂ
abbrev JointMatrix := Mat Joint

abbrev densityMatrix {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) : Mat n :=
  CStarMatrix.ofMatrix.symm ρ.1

def MarginalFree (D : JointMatrix) : Prop :=
  D.IsHermitian ∧ partialTraceRight D = 0 ∧ partialTraceLeft D = 0

theorem productMatrix_posDef (α : DensityState Alice) (β : DensityState Bob)
    (hα : (densityMatrix α).PosDef) (hβ : (densityMatrix β).PosDef) :
    (densityMatrix (productState α β)).PosDef :=
  hα.kronecker hβ

def aliceR : Matrix.unitaryGroup Alice ℂ :=
  ⟨_, D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation.hadamard_unitary⟩

def bobR : Matrix.unitaryGroup Bob ℂ := by
  refine ⟨D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform 3, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.transform_unitary 3

/-- Columns of U are the measured basis. -/
def inBasis {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (A : Mat n) : Mat n :=
  (Unitary.conjStarAlgAut ℂ (Mat n) U).symm A

def productBasis (U : Matrix.unitaryGroup Alice ℂ) (V : Matrix.unitaryGroup Bob ℂ) :
    Matrix.unitaryGroup Joint ℂ := by
  exact ⟨(U : Mat Alice) ⊗ₖ (V : Mat Bob), Matrix.kronecker_mem_unitary U.property V.property⟩

theorem inBasis_product (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) (A : Mat Alice) (B : Mat Bob) :
    inBasis (productBasis U V) (A ⊗ₖ B) = inBasis U A ⊗ₖ inBasis V B := by
  simp only [inBasis, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose]
  change ((U : Mat Alice) ⊗ₖ (V : Mat Bob))ᴴ * (A ⊗ₖ B) *
    ((U : Mat Alice) ⊗ₖ (V : Mat Bob)) =
    ((U : Mat Alice)ᴴ * A * (U : Mat Alice)) ⊗ₖ
      ((V : Mat Bob)ᴴ * B * (V : Mat Bob))
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

theorem inBasis_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {A : Mat n} (hA : A.PosDef) :
    (inBasis U A).PosDef := by
  apply hA.conjTranspose_mul_mul_same
  intro x y hxy
  have h := congrArg (fun z => (U : Mat n)ᴴ *ᵥ z) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    Unitary.coe_star_mul_self, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- The diagonal of the actual state or tangent in the measurement basis. -/
def readout {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (A : Mat n) (i : n) : ℝ :=
  (inBasis U A i i).re

theorem readout_pos {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) {A : Mat n} (hA : A.PosDef) (i : n) :
    0 < readout U A i :=
  (Complex.pos_iff.mp ((inBasis_posDef U hA).diag_pos (i := i))).1

private theorem inBasis_diagonal_im {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix.unitaryGroup n ℂ) {X : Mat n} (hX : X.IsHermitian) (a : n) :
    (inBasis W X a a).im = 0 := by
  have h : (inBasis W X).IsHermitian := by
    change star ((Unitary.conjStarAlgAut ℂ (Mat n) W).symm X) = _
    rw [← map_star, hX.star_eq]
    rfl
  have hi := congrArg Complex.im (h.apply a a)
  simp at hi
  linarith

theorem readout_product (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) {A : Mat Alice} {B : Mat Bob}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Alice) (j : Bob) :
    readout (productBasis U V) (A ⊗ₖ B) (i, j) = readout U A i * readout V B j := by
  unfold readout
  rw [inBasis_product]
  change ((inBasis U A i i) * (inBasis V B j j)).re = _
  simp [Complex.mul_re, inBasis_diagonal_im U hA i, inBasis_diagonal_im V hB j]

theorem partialTraceRight_inBasis (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) (D : JointMatrix) :
    partialTraceRight (inBasis (productBasis U V) D) = inBasis U (partialTraceRight D) := by
  have hV : ((V : Mat Bob)ᴴ)ᴴ * (V : Mat Bob)ᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose,
      Unitary.coe_star] using Unitary.coe_mul_star_self V
  have h := D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
    (U : Mat Alice)ᴴ (V : Mat Bob)ᴴ hV D
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose] at h
  simp only [inBasis, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose]
  change partialTraceRight (((U : Mat Alice) ⊗ₖ (V : Mat Bob))ᴴ * D *
    ((U : Mat Alice) ⊗ₖ (V : Mat Bob))) =
    (U : Mat Alice)ᴴ * partialTraceRight D * (U : Mat Alice)
  rw [Matrix.conjTranspose_kronecker]
  exact h

theorem partialTraceLeft_inBasis (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) (D : JointMatrix) :
    partialTraceLeft (inBasis (productBasis U V) D) = inBasis V (partialTraceLeft D) := by
  let e := Equiv.prodComm Bob Alice
  let A := (U : Mat Alice)ᴴ
  let B := (V : Mat Bob)ᴴ
  have hs (M : JointMatrix) : partialTraceLeft M = partialTraceRight (M.submatrix e e) := rfl
  have hk : (A ⊗ₖ B).submatrix e e = B ⊗ₖ A := by
    ext i j
    change A i.2 j.2 * B i.1 j.1 = B i.1 j.1 * A i.2 j.2
    exact mul_comm _ _
  have h :
      ((A ⊗ₖ B) * D * (A ⊗ₖ B)ᴴ).submatrix e e =
        (B ⊗ₖ A) * D.submatrix e e * (B ⊗ₖ A)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.conjTranspose_submatrix, hk]
  change partialTraceLeft (((U : Mat Alice) ⊗ₖ (V : Mat Bob))ᴴ * D *
    ((U : Mat Alice) ⊗ₖ (V : Mat Bob))) = _
  have hAB : (A ⊗ₖ B)ᴴ = (U : Mat Alice) ⊗ₖ (V : Mat Bob) := by
    simp only [A, B, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_kronecker, ← hAB]
  change partialTraceLeft ((A ⊗ₖ B) * D * (A ⊗ₖ B)ᴴ) = _
  rw [hs, h, hs D]
  simp only [inBasis, Unitary.conjStarAlgAut_symm_apply, Matrix.star_eq_conjTranspose]
  change partialTraceRight (Matrix.kronecker B A * D.submatrix e e *
      (Matrix.kronecker B A)ᴴ) = B * partialTraceRight (D.submatrix e e) * (V : Mat Bob)
  have hU : Aᴴ * A = 1 := by
    simpa only [A, Matrix.conjTranspose_conjTranspose, Matrix.star_eq_conjTranspose,
      Unitary.coe_star] using Unitary.coe_mul_star_self U
  simpa only [B, Matrix.conjTranspose_conjTranspose] using
    D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
      B A hU (D.submatrix e e)

theorem readout_marginalFree (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) {D : JointMatrix} (hD : MarginalFree D) :
    (∀ i, ∑ j : Bob, readout (productBasis U V) D (i, j) = 0) ∧
    (∀ j, ∑ i : Alice, readout (productBasis U V) D (i, j) = 0) := by
  constructor
  · intro i
    have h := partialTraceRight_inBasis U V D
    rw [hD.2.1] at h
    have he := congrArg (fun A : Mat Alice => (A i i).re) h
    simpa [partialTraceRight, readout, inBasis, Complex.re_sum] using he
  · intro j
    have h := partialTraceLeft_inBasis U V D
    rw [hD.2.2] at h
    have he := congrArg (fun A : Mat Bob => (A j j).re) h
    simpa [partialTraceLeft, readout, inBasis, Complex.re_sum] using he

/-- The exact Fisher score is a product of locally centered scores. The binary
Alice factor is explicit, with no optimization or interpolation. -/
theorem centeredScore_factor (p : Alice → ℝ) (q : Bob → ℝ)
    (d : Joint → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hrow : ∀ i, ∑ j, d (i, j) = 0) (hcol : ∀ j, ∑ i, d (i, j) = 0) :
    ∃ a : Alice → ℝ, ∃ b : Bob → ℝ,
      (∑ i, p i * a i) = 0 ∧ (∑ j, q j * b j) = 0 ∧
      ∀ i j, a i * b j = d (i, j) / (p i * q j) := by
  let a : Alice → ℝ := ![(p 0)⁻¹, -(p 1)⁻¹]
  let b : Bob → ℝ := fun j => d (0, j) / q j
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simp [a, Fin.sum_univ_two, (hp 0).ne', (hp 1).ne', mul_neg]
  · calc
      (∑ j, q j * b j) = ∑ j, d (0, j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_div_cancel₀ _ (hq j).ne'
      _ = 0 := hrow 0
  · intro i j
    have hd : d (1, j) = -d (0, j) := by
      have h := hcol j
      rw [Fin.sum_univ_two] at h
      linarith
    fin_cases i
    · change (p 0)⁻¹ * (d (0, j) / q j) = d (0, j) / (p 0 * q j)
      rw [div_mul_eq_div_div]
      ring
    · change -(p 1)⁻¹ * (d (0, j) / q j) = d (1, j) / (p 1 * q j)
      rw [hd]
      field_simp [(hp 1).ne', (hq j).ne']

/-- Centered spectral score observable in its actual measurement basis. -/
def observable {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) : Mat n :=
  Unitary.conjStarAlgAut ℂ (Mat n) U (diagonal fun i => (a i : ℂ))

theorem inBasis_observable {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) :
    inBasis U (observable U a) = diagonal (fun i => (a i : ℂ)) :=
  StarAlgEquiv.symm_apply_apply _ _

theorem observable_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) : (observable U a).IsHermitian := by
  let F := Unitary.conjStarAlgAut ℂ (Mat n) U
  change star (F (diagonal fun i => (a i : ℂ))) = _
  rw [← map_star]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.star_eq_conjTranspose]
  · simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_apply_ne, hij, Ne.symm hij]

theorem trace_observable {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (X : Mat n) (a : n → ℝ) :
    (X * observable U a).trace.re = ∑ i, readout U X i * a i := by
  have ht (M : Mat n) : (inBasis U M).trace = M.trace := by
    rw [inBasis, Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle,
      ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  rw [← ht (X * observable U a)]
  change ((Unitary.conjStarAlgAut ℂ (Mat n) U).symm (X * observable U a)).trace.re = _
  rw [map_mul]
  change (inBasis U X * inBasis U (observable U a)).trace.re = _
  rw [inBasis_observable]
  simp [Matrix.trace, Matrix.mul_diagonal, Complex.re_sum, Complex.mul_re, readout]

theorem observable_product (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) (a : Alice → ℝ) (b : Bob → ℝ) :
    observable U a ⊗ₖ observable V b =
      observable (productBasis U V) (fun k => a k.1 * b k.2) := by
  apply (Unitary.conjStarAlgAut ℂ (Mat Joint) (productBasis U V)).symm.injective
  change inBasis (productBasis U V) _ = inBasis (productBasis U V) _
  rw [inBasis_product, inBasis_observable, inBasis_observable, inBasis_observable]
  ext i j
  obtain ⟨i, k⟩ := i
  obtain ⟨j, l⟩ := j
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    simp [hij, hkl, Prod.mk.injEq]

/-- Qian's classical Fisher form for one product-basis measurement. -/
def measurementFisher (U : Matrix.unitaryGroup Alice ℂ)
    (V : Matrix.unitaryGroup Bob ℂ) (σ D : JointMatrix) : ℝ :=
  ∑ a, readout (productBasis U V) D a ^ 2 / readout (productBasis U V) σ a

/-- One readout gives exactly its Fisher squared norm, both as the pairing
against its score observable and as that observable's product variance. -/
theorem measurementFisher_centered (α : DensityState Alice) (β : DensityState Bob)
    (hα : (densityMatrix α).PosDef) (hβ : (densityMatrix β).PosDef)
    (U : Matrix.unitaryGroup Alice ℂ) (V : Matrix.unitaryGroup Bob ℂ)
    {D : JointMatrix} (hD : MarginalFree D) :
    let σ := densityMatrix (productState α β)
    ∃ a : Alice → ℝ, ∃ b : Bob → ℝ,
      (∑ i, readout U (densityMatrix α) i * a i) = 0 ∧
      (∑ j, readout V (densityMatrix β) j * b j) = 0 ∧
      (D * (observable U a ⊗ₖ observable V b)).trace.re = measurementFisher U V σ D ∧
      (densityMatrix α * observable U (fun i => (a i) ^ 2)).trace.re *
        (densityMatrix β * observable V (fun j => (b j) ^ 2)).trace.re =
          measurementFisher U V σ D := by
  let σ := densityMatrix (productState α β)
  let p := readout U (densityMatrix α)
  let q := readout V (densityMatrix β)
  let d := readout (productBasis U V) D
  have hp := readout_pos U hα
  have hq := readout_pos V hβ
  have hσ (i : Alice) (j : Bob) : readout (productBasis U V) σ (i, j) = p i * q j :=
    readout_product U V hα.isHermitian hβ.isHermitian i j
  obtain ⟨hr, hc⟩ := readout_marginalFree U V hD
  obtain ⟨a, b, ha, hb, hab⟩ := centeredScore_factor p q d hp hq hr hc
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [observable_product, trace_observable, measurementFisher]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change d (i, j) * (a i * b j) = d (i, j) ^ 2 / readout (productBasis U V) σ (i, j)
    rw [hab, hσ]
    ring
  · rw [trace_observable, trace_observable, measurementFisher]
    rw [Finset.sum_mul]
    simp only [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change p i * (a i) ^ 2 * (q j * (b j) ^ 2) =
      d (i, j) ^ 2 / readout (productBasis U V) σ (i, j)
    rw [hσ, show p i * (a i) ^ 2 * (q j * (b j) ^ 2) =
      (p i * q j) * (a i * b j) ^ 2 by ring, hab]
    field_simp [(hp i).ne', (hq j).ne']

theorem observable_square {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (a : n → ℝ) :
    observable U (fun i => (a i) ^ 2) = observable U a * observable U a := by
  unfold observable
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  have hs (i : n) : ((a i ^ 2 : ℝ) : ℂ) = (a i : ℂ) * (a i : ℂ) := by
    push_cast
    rw [pow_two]
  simp only [hs]

/-- The quadratic expression in (39), using the fixed-reference log resolvent.
Each pair of local unitaries supplies one product measurement basis. -/
def anchorQuadraticIn
    (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ)
    (α : DensityState Alice) (β : DensityState Bob) (D : JointMatrix) : ℝ :=
  let σ := densityMatrix (productState α β)
  (D * logDeriv σ D).trace.re -
    measurementFisher UQ VQ σ D - measurementFisher UR VR σ D

abbrev anchorQuadratic := anchorQuadraticIn 1 aliceR 1 bobR

def ACC₂₃ : Prop :=
  ∀ (α : DensityState Alice) (β : DensityState Bob),
    (densityMatrix α).PosDef → (densityMatrix β).PosDef →
    ∀ D : JointMatrix, MarginalFree D → 0 ≤ anchorQuadratic α β D

/-- The all-bases version of Definition 7.2, before local unitary reduction. -/
def ACC₂₃AllBases : Prop :=
  ∀ (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ),
    (∀ i j, Complex.normSq (((UQ : Mat Alice)ᴴ * (UR : Mat Alice)) i j) = (1 / 2 : ℝ)) →
    (∀ i j, Complex.normSq (((VQ : Mat Bob)ᴴ * (VR : Mat Bob)) i j) = (1 / 3 : ℝ)) →
    ∀ (α : DensityState Alice) (β : DensityState Bob),
      (densityMatrix α).PosDef → (densityMatrix β).PosDef →
      ∀ D : JointMatrix, MarginalFree D → 0 ≤ anchorQuadraticIn UQ UR VQ VR α β D

end AnchorMeasurement
