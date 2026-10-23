/- GID: D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.claim; result=D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result; claim=D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.claim
   digest: Bell-diagonal entanglement distance differs from twice squared concurrence. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot

/-! A concrete two-qubit counterexample to the proposed Bell-diagonal formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot

/-- A one-site operator on the two-qubit product basis. -/
def onSite (μ : Fin 2) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  if μ = 0 then Matrix.of (fun i j => if i.2 = j.2 then U i.1 j.1 else 0)
  else Matrix.of (fun i j => if i.1 = j.1 then U i.2 j.2 else 0)

/-- The Pauli observable on one of the two sites. -/
noncomputable def sitePauli (μ : Fin 2) (i : Fin 3) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  onSite μ (if i = 0 then pauliMatrix .X else if i = 1 then pauliMatrix .Y else pauliMatrix .Z)

private theorem sitePauli_apply (μ : Fin 2) (i : Fin 3) (a b : Fin 2 × Fin 2) :
    sitePauli μ i a b =
      if μ = 0 then
        if a.2 = b.2 then (if i = 0 then pauliMatrix .X else if i = 1 then pauliMatrix .Y else pauliMatrix .Z) a.1 b.1 else 0
      else if a.1 = b.1 then
        (if i = 0 then pauliMatrix .X else if i = 1 then pauliMatrix .Y else pauliMatrix .Z) a.2 b.2 else 0 := by
  by_cases h : μ = 0 <;> simp [sitePauli, onSite, h]

/-- The quantum correlation distance of one site in the variational form of Eq. `QCDrho`. -/
noncomputable def siteQCD (μ : Fin 2)
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  Complex.re (Matrix.trace (σ * σ)) -
    sSup {x : ℝ | ∃ n : Fin 3 → ℝ,
      (∑ i, n i ^ 2 = 1) ∧
        x = Complex.re (Matrix.trace (σ * (∑ i, (n i : ℂ) • sitePauli μ i) * σ *
          (∑ i, (n i : ℂ) • sitePauli μ i)))}

/-- The locally rotated mixture of a finite ensemble. -/
noncomputable def rotated {k : ℕ} (μ : Fin 2) (p : Fin k → ℝ)
    (ρs : Fin k → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (U : Fin k → Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ j, (p j : ℂ) •
    (onSite μ (U j) * ρs j * Matrix.conjTranspose (onSite μ (U j)))

/-- The entanglement distance obtained by minimizing over finite decompositions and local rotations. -/
noncomputable def ED
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  sInf {x : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ)
      (ρs : Fin k → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (_hp : ∀ j, 0 ≤ p j) (_hsum : ∑ j, p j = 1)
      (_hstate : ∀ j, (ρs j).PosSemidef ∧ Matrix.trace (ρs j) = 1)
      (_hmix : ∑ j, (p j : ℂ) • ρs j = ρ),
      x = ∑ μ : Fin 2, sInf {y : ℝ | ∃ U,
        y = siteQCD μ (rotated μ p ρs U)}}

/-- The four Bell projectors, written entrywise in the product basis. -/
noncomputable def bellProjector (α : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    if α = 0 then D5.S3.QuantumBounds.CHSHWitness.bellDensity i j
    else if α = 1 then
      if i = (0, 0) ∧ j = (0, 0) then (1 / 2 : ℂ) else
      if i = (1, 1) ∧ j = (1, 1) then (1 / 2 : ℂ) else
      if i = (0, 0) ∧ j = (1, 1) then (-1 / 2 : ℂ) else
      if i = (1, 1) ∧ j = (0, 0) then (-1 / 2 : ℂ) else 0
    else if α = 2 then
      if i = (0, 1) ∧ j = (0, 1) then (1 / 2 : ℂ) else
      if i = (1, 0) ∧ j = (1, 0) then (1 / 2 : ℂ) else
      if i = (0, 1) ∧ j = (1, 0) then (1 / 2 : ℂ) else
      if i = (1, 0) ∧ j = (0, 1) then (1 / 2 : ℂ) else 0
    else
      if i = (0, 1) ∧ j = (0, 1) then (1 / 2 : ℂ) else
      if i = (1, 0) ∧ j = (1, 0) then (1 / 2 : ℂ) else
      if i = (0, 1) ∧ j = (1, 0) then (-1 / 2 : ℂ) else
      if i = (1, 0) ∧ j = (0, 1) then (-1 / 2 : ℂ) else 0

/-- The Bell-diagonal state with real probability vector `p`. -/
noncomputable def bellDiagonal (p : Fin 4 → ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ α, (p α : ℂ) • bellProjector α

/-- The concurrence of a Bell-diagonal state. -/
def concurrence (p : Fin 4 → ℝ) : ℝ :=
  max 0 (2 * Finset.univ.sup' Finset.univ_nonempty p - 1)

def claim : Prop :=
  ∀ p : Fin 4 → ℝ, (∀ α, 0 ≤ p α) → ∑ α, p α = 1 →
    ED (bellDiagonal p) = 2 * (concurrence p) ^ 2

private noncomputable def pKet (q : ℂ) : Fin 2 × Fin 2 → ℂ := fun ij =>
  if ij = (0, 0) then 1 else if ij = (1, 1) then q else 0

private noncomputable def pProjector (q : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = (0, 0) ∧ j = (0, 0) then (1 / 2 : ℂ) else
    if i = (1, 1) ∧ j = (1, 1) then (1 / 2 : ℂ) else
    if i = (0, 0) ∧ j = (1, 1) then star q / 2 else
    if i = (1, 1) ∧ j = (0, 0) then q / 2 else 0

private noncomputable def qPlus : ℂ := (7 + 24 * Complex.I) / 25
private noncomputable def qMinus : ℂ := (7 - 24 * Complex.I) / 25

private theorem pProjector_eq_vec (q : ℂ) (hq : q * star q = 1) :
    pProjector q = (1 / 2 : ℝ) • Matrix.vecMulVec (pKet q) (star (pKet q)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pProjector, pKet, Matrix.vecMulVec, Pi.star_apply] <;>
      first | exact hq | ring

private theorem pPlus_state : (pProjector qPlus).PosSemidef ∧ Matrix.trace (pProjector qPlus) = 1 := by
  rw [pProjector_eq_vec qPlus (by
    apply Complex.ext <;> norm_num [qPlus])]
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star (pKet qPlus)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [pKet, qPlus, Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.ext_iff,
      Complex.I_mul_I]

private theorem pMinus_state : (pProjector qMinus).PosSemidef ∧ Matrix.trace (pProjector qMinus) = 1 := by
  rw [pProjector_eq_vec qMinus (by
    apply Complex.ext <;> norm_num [qMinus])]
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star (pKet qMinus)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · rw [Matrix.trace_smul, Matrix.trace_vecMulVec]
    simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num [pKet, qMinus, Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.ext_iff,
      Complex.I_mul_I]

private noncomputable def witnessP : Fin 4 → ℝ := ![16 / 25, 9 / 25, 0, 0]

private theorem bellDiagonal_witness :
    bellDiagonal witnessP = (1 / 2 : ℂ) • pProjector qPlus + (1 / 2 : ℂ) • pProjector qMinus := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bellDiagonal, witnessP, bellProjector, pProjector,
      qPlus, qMinus, Fin.sum_univ_succ, D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      Matrix.vecMulVec, D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self]
    <;> norm_num <;> ring

private noncomputable def U1mat : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(4 + 3 * Complex.I) / 5, (4 - 3 * Complex.I) / 5]
private noncomputable def U2mat : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(3 + 4 * Complex.I) / 5, (3 - 4 * Complex.I) / 5]

private noncomputable def U1 : Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨U1mat, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U1mat, Matrix.mul_apply, Matrix.diagonal, Complex.ext_iff, map_ofNat]
  · norm_num [U1mat, Matrix.det_fin_two, Matrix.diagonal, Complex.ext_iff, map_ofNat]

private noncomputable def U2 : Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine ⟨U2mat, ?_⟩
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U2mat, Matrix.mul_apply, Matrix.diagonal, Complex.ext_iff, map_ofNat]
  · norm_num [U2mat, Matrix.det_fin_two, Matrix.diagonal, Complex.ext_iff, map_ofNat]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem rotated_witness (μ : Fin 2) :
    rotated μ (![(1 / 2 : ℝ), 1 / 2]) (fun j : Fin 2 => if j = 0 then pProjector qPlus else pProjector qMinus)
      (fun j : Fin 2 => if j = 0 then U1 else U2) = classicalCorrelatedDensity := by
  simp only [rotated, Fin.sum_univ_two]
  change ((1 / 2 : ℝ) : ℂ) • (onSite μ U1mat * pProjector qPlus * (onSite μ U1mat)ᴴ) +
    ((1 / 2 : ℝ) : ℂ) • (onSite μ U2mat * pProjector qMinus * (onSite μ U2mat)ᴴ) =
      classicalCorrelatedDensity
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases μ <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [classicalCorrelatedDensity, onSite, pProjector, qPlus, qMinus,
      U1mat, U2mat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.ext_iff, map_ofNat]

private theorem chi_trace_square :
    Complex.re (Matrix.trace (classicalCorrelatedDensity * classicalCorrelatedDensity)) = 1 / 2 := by
  norm_num [classicalCorrelatedDensity, Matrix.diagonal, Matrix.trace, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem chi_variational (μ : Fin 2) (n : Fin 3 → ℝ) :
    Complex.re (Matrix.trace (classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i) *
      classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i))) = (n 2) ^ 2 / 2 := by
  fin_cases μ <;>
    norm_num [classicalCorrelatedDensity, sitePauli_apply, pauliMatrix, qubitX, qubitZ,
      Matrix.mul_apply, Matrix.diagonal, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

private theorem chi_qcd_zero (μ : Fin 2) : siteQCD μ classicalCorrelatedDensity = 0 := by
  have hmem : (1 / 2 : ℝ) ∈ {x : ℝ | ∃ n : Fin 3 → ℝ,
      (∑ i, n i ^ 2 = 1) ∧
        x = Complex.re (Matrix.trace (classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i) *
          classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i)))} := by
    refine ⟨![0, 0, 1], ?_, ?_⟩
    · norm_num [Fin.sum_univ_succ]
    · rw [chi_variational]
      norm_num
  have hupper : ∀ x : ℝ, x ∈ {x : ℝ | ∃ n : Fin 3 → ℝ,
      (∑ i, n i ^ 2 = 1) ∧
        x = Complex.re (Matrix.trace (classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i) *
          classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i)))} → x ≤ 1 / 2 := by
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    rw [chi_variational]
    have h2 : (n 2) ^ 2 ≤ 1 := by
      have := Finset.single_le_sum (fun i _ => sq_nonneg (n i)) (Finset.mem_univ (2 : Fin 3))
      calc
        (n 2) ^ 2 ≤ ∑ i, n i ^ 2 := this
        _ = 1 := hn
    nlinarith
  have hs : sSup {x : ℝ | ∃ n : Fin 3 → ℝ,
      (∑ i, n i ^ 2 = 1) ∧
        x = Complex.re (Matrix.trace (classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i) *
          classicalCorrelatedDensity * (∑ i, (n i : ℂ) • sitePauli μ i)))} = 1 / 2 := by
    apply le_antisymm
    · exact csSup_le ⟨1 / 2, hmem⟩ hupper
    · exact le_csSup (show BddAbove _ from ⟨1 / 2, hupper⟩) hmem
  rw [siteQCD, chi_trace_square, hs]
  norm_num

private theorem ed_witness_le_zero : ED (bellDiagonal witnessP) ≤ 0 := by
  let p : Fin 2 → ℝ := ![(1 / 2 : ℝ), 1 / 2]
  let ρs : Fin 2 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    fun j => if j = 0 then pProjector qPlus else pProjector qMinus
  let U : Fin 2 → Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    fun j => if j = 0 then U1 else U2
  have hp : ∀ j, 0 ≤ p j := by intro j; fin_cases j <;> norm_num [p]
  have hpsum : ∑ j, p j = 1 := by norm_num [p]
  have hstate : ∀ j, (ρs j).PosSemidef ∧ Matrix.trace (ρs j) = 1 := by
    intro j; fin_cases j
    · simpa [ρs] using pPlus_state
    · simpa [ρs] using pMinus_state
  have hmix : ∑ j, (p j : ℂ) • ρs j = bellDiagonal witnessP := by
    rw [bellDiagonal_witness]
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [p, ρs, Fin.sum_univ_two, pProjector, qPlus, qMinus,
        Complex.ext_iff, map_ofNat]
  have hinner (μ : Fin 2) : sInf {y : ℝ | ∃ U,
      y = siteQCD μ (rotated μ p ρs U)} ≤ 0 := by
    apply Real.sInf_nonpos'
    refine ⟨0, ?_, le_refl 0⟩
    refine ⟨U, ?_⟩
    rw [rotated_witness, chi_qcd_zero]
  have hmember : (∑ μ : Fin 2, sInf {y : ℝ | ∃ U,
      y = siteQCD μ (rotated μ p ρs U)}) ∈ {x : ℝ | ∃ (k : ℕ) (p : Fin k → ℝ)
      (ρs : Fin k → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
      (_hp : ∀ j, 0 ≤ p j) (_hsum : ∑ j, p j = 1)
      (_hstate : ∀ j, (ρs j).PosSemidef ∧ Matrix.trace (ρs j) = 1)
      (_hmix : ∑ j, (p j : ℂ) • ρs j = bellDiagonal witnessP),
      x = ∑ μ : Fin 2, sInf {y : ℝ | ∃ U,
        y = siteQCD μ (rotated μ p ρs U)}} := by
    exact ⟨2, p, ρs, hp, hpsum, hstate, hmix, rfl⟩
  exact Real.sInf_nonpos' ⟨_, hmember, Finset.sum_nonpos (fun μ _ => hinner μ)⟩

theorem result : ¬ claim := by
  intro h
  have hc := h witnessP (by intro α; fin_cases α <;> norm_num [witnessP])
    (by norm_num [witnessP, Fin.sum_univ_succ])
  have hed := ed_witness_le_zero
  rw [hc] at hed
  change 2 * (max 0 (2 * Finset.univ.sup' Finset.univ_nonempty witnessP - 1)) ^ 2 ≤ 0 at hed
  have hsupp : Finset.univ.sup' Finset.univ_nonempty witnessP = 16 / 25 := by
    apply le_antisymm
    · apply (Finset.sup'_le_iff Finset.univ_nonempty witnessP).2
      intro i hi
      fin_cases i <;> norm_num [witnessP]
    · apply Finset.le_sup'_of_le (s := Finset.univ) (f := witnessP)
        (a := (16 / 25 : ℝ)) (b := (0 : Fin 4))
      · simp
      · norm_num [witnessP]
  rw [hsupp] at hed
  norm_num [concurrence] at hed

end D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation
