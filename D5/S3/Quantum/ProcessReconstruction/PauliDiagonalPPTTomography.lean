/- GID: D5/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography
   generality: I
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/PauliDiagonalPPTTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp Hilbert–Schmidt process reconstruction for Pauli-diagonal PPT probes in dimension four. -/

import D5.S3.Quantum.Matrix.PartialTransposeTrace
import D5.S3.Quantum.Information.Pauli.PauliMatrix
import D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation
import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
# Anticommuting Pauli correlations of PPT states

The Pauli-diagonal conditioning bound uses the unnormalized Choi convention.
Singh v3, arXiv:2605.19182v3, Proposition 5, gives the equal-dimensional
separable optimum and reports the advantage of the six-Bell probe.
The d=4 witness is the six-Bell state of Lukács–Trényi–Vértesi–Tóth,
arXiv:2206.02820v3, Eqs. (153)–(157). It is locally unitarily equivalent to
the earlier Bell-lattice state of Benatti–Floreanini–Piani,
arXiv:quant-ph/0401146v1, §4 p. 11.
-/

noncomputable section

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder Kronecker
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.EntanglementDistanceBellDiagonalRefutation (bellProjector)

-- The public vector form is partial_transpose_trace_duality.
open private trace_pairing from D5.S3.Quantum.Matrix.PartialTransposeTrace

namespace D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography

variable {A B : Type} {S : Type*}

/-- The paired observable of an input matrix and its transposed copy. -/
def paired (P : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ := P ⊗ₖ Pᵀ

/-- The real trace expectation on a finite matrix. -/
def expectation [Fintype A] (ρ M : Matrix A A ℂ) : ℝ := (ρ * M).trace.re

private theorem pt_kronecker (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    partialTranspose (M ⊗ₖ N) = M ⊗ₖ Nᵀ := rfl

private theorem pt_neg (M : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (-M) = -partialTranspose M := rfl

private theorem kronecker_neg_left (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    (-M) ⊗ₖ N = -(M ⊗ₖ N) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.kronecker_apply, Matrix.neg_apply, neg_mul]

private theorem kronecker_neg_right (M : Matrix A A ℂ) (N : Matrix B B ℂ) :
    M ⊗ₖ (-N) = -(M ⊗ₖ N) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.kronecker_apply, Matrix.neg_apply, mul_neg]

private theorem expectation_pt [Fintype A] [Fintype B]
    (ρ M : Matrix (A × B) (A × B) ℂ) :
    expectation (partialTranspose ρ) M = expectation ρ (partialTranspose M) :=
  congrArg Complex.re (trace_pairing ρ M)

section Joint

variable [Fintype A] [DecidableEq A]

private theorem expectation_one (ρ : Matrix A A ℂ) :
    expectation ρ 1 = ρ.trace.re := by simp [expectation]

private theorem expectation_neg (ρ M : Matrix A A ℂ) :
    expectation ρ (-M) = -expectation ρ M := by
  simp [expectation, Matrix.trace_neg]

private theorem expectation_add (ρ M N : Matrix A A ℂ) :
    expectation ρ (M + N) = expectation ρ M + expectation ρ N := by
  simp [expectation, mul_add, Matrix.trace_add]

private theorem expectation_smul (ρ M : Matrix A A ℂ) (a : ℝ) :
    expectation ρ (a • M) = a * expectation ρ M := by
  simp [expectation, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]

private theorem involution_factor_square (U : Matrix A A ℂ) (hU : U * U = 1)
    (a : ℝ) (ha : a * a = 1) :
    (1 + a • U) * (1 + a • U) = (2 : ℝ) • (1 + a • U) := by
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    hU, smul_smul, ha, one_smul]
  module

/-- The joint spectral projector for signs a and b. -/
def jointProjection (U V : Matrix A A ℂ) (a b : ℝ) : Matrix A A ℂ :=
  (1 / 4 : ℝ) • ((1 + a • U) * (1 + b • V))

private theorem jointProjection_psd (U V : Matrix A A ℂ)
    (hU : Uᴴ = U) (hV : Vᴴ = V) (hUU : U * U = 1) (hVV : V * V = 1)
    (hUV : Commute U V) (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1) :
    (jointProjection U V a b).PosSemidef := by
  let F := (1 : Matrix A A ℂ) + a • U
  let G := (1 : Matrix A A ℂ) + b • V
  have hF : Fᴴ = F := by simp [F, Matrix.conjTranspose_smul, hU]
  have hG : Gᴴ = G := by simp [G, Matrix.conjTranspose_smul, hV]
  have hFG : Commute F G := by
    change F * G = G * F
    simp only [F, G, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hUV.eq, mul_comm a b]
    abel
  have hgram : (F * G)ᴴ * (F * G) = (4 : ℝ) • (F * G) := by
    rw [Matrix.conjTranspose_mul, hG, hF]
    calc
      (G * F) * (F * G) = (F * G) * (F * G) :=
        congrArg (fun M => M * (F * G)) hFG.eq.symm
      _ = (F * F) * (G * G) := hFG.symm.mul_mul_mul_comm F G
      _ = (4 : ℝ) • (F * G) := by
        have hf : F * F = (2 : ℝ) • F := involution_factor_square U hUU a ha
        have hg : G * G = (2 : ℝ) • G := involution_factor_square V hVV b hb
        rw [hf, hg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        norm_num
  have hpos := (Matrix.posSemidef_conjTranspose_mul_self (F * G)).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 16)
  rw [hgram, smul_smul] at hpos
  change ((1 / 4 : ℝ) • (F * G)).PosSemidef
  rw [show (1 / 16 : ℝ) * 4 = 1 / 4 by norm_num] at hpos
  exact hpos

private theorem joint_sign_test (ρ U V : Matrix A A ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (hU : Uᴴ = U) (hV : Vᴴ = V)
    (hUU : U * U = 1) (hVV : V * V = 1) (hUV : Commute U V)
    (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1) :
    0 ≤ 1 + a * expectation ρ U + b * expectation ρ V +
      (a * b) * expectation ρ (U * V) := by
  have hp := jointProjection_psd U V hU hV hUU hVV hUV a b ha hb
  have h : 0 ≤ expectation ρ (jointProjection U V a b) :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hρ hp
  simp only [jointProjection, add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, expectation_smul, expectation_add, expectation_one,
    htr, Complex.one_re] at h
  linarith only [h]

end Joint

section PauliTriple

variable [Fintype A] [DecidableEq A]

/-- The paired involutions commute, their product is the paired phase-corrected
third observable, and partial transpose reverses the product sign. -/
theorem paired_anticommuting_mul (X Z : Matrix A A ℂ) (hXZ : Z * X = -(X * Z)) :
    Commute (paired X) (paired Z) ∧
    paired X * paired Z = paired (Complex.I • (X * Z)) ∧
    partialTranspose (paired X * paired Z) = -((X ⊗ₖ X) * (Z ⊗ₖ Z)) := by
  have hc : paired X * paired Z = -((X * Z) ⊗ₖ (X * Z)ᵀ) := by
    rw [paired, paired, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      hXZ, Matrix.transpose_neg, kronecker_neg_right]
  refine ⟨?_, ?_, ?_⟩
  · change paired X * paired Z = paired Z * paired X
    rw [hc, paired, paired, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      hXZ, kronecker_neg_left]
  · rw [hc, paired, Matrix.transpose_smul, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, Complex.I_mul_I, neg_one_smul]
  · rw [hc, pt_neg, pt_kronecker, Matrix.transpose_transpose, ← Matrix.mul_kronecker_mul]

private theorem tensor_involution (X Y : Matrix A A ℂ)
    (hX : Xᴴ = X) (hY : Yᴴ = Y) (hXX : X * X = 1) (hYY : Y * Y = 1) :
    (X ⊗ₖ Y)ᴴ = X ⊗ₖ Y ∧ (X ⊗ₖ Y) * (X ⊗ₖ Y) = 1 := by
  constructor
  · rw [Matrix.conjTranspose_kronecker, hX, hY]
  · rw [← Matrix.mul_kronecker_mul, hXX, hYY, Matrix.one_kronecker_one]

private theorem paired_involution (X : Matrix A A ℂ) (hX : Xᴴ = X)
    (hXX : X * X = 1) :
    (paired X)ᴴ = paired X ∧ paired X * paired X = 1 := by
  apply tensor_involution X Xᵀ hX
  · rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hX]
  · exact hXX
  · rw [← Matrix.transpose_mul, hXX, Matrix.transpose_one]

/-- Every PPT density matrix satisfies the correlation octahedron inequality
for a pair of anticommuting Hermitian involutions. -/
theorem ppt_anticommuting_triple (ρ : Matrix (A × A) (A × A) ℂ)
    (hρ : ρ.PosSemidef) (hpt : (partialTranspose ρ).PosSemidef) (htr : ρ.trace = 1)
    (X Z : Matrix A A ℂ)
    (hX : Xᴴ = X) (hZ : Zᴴ = Z) (hXX : X * X = 1) (hZZ : Z * Z = 1)
    (hXZ : Z * X = -(X * Z)) :
    |expectation ρ (paired X)| + |expectation ρ (paired Z)| +
      |expectation ρ (paired (Complex.I • (X * Z)))| ≤ 1 := by
  obtain ⟨hcomm, hy, hflip⟩ := paired_anticommuting_mul X Z hXZ
  obtain ⟨hxH, hxx⟩ := paired_involution X hX hXX
  obtain ⟨hzH, hzz⟩ := paired_involution Z hZ hZZ
  obtain ⟨hxH', hxx'⟩ := tensor_involution X X hX hX hXX hXX
  obtain ⟨hzH', hzz'⟩ := tensor_involution Z Z hZ hZ hZZ hZZ
  have hcomm' : Commute (X ⊗ₖ X) (Z ⊗ₖ Z) := by
    change (X ⊗ₖ X) * (Z ⊗ₖ Z) = (Z ⊗ₖ Z) * (X ⊗ₖ X)
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hXZ,
      kronecker_neg_left, kronecker_neg_right, neg_neg]
  have htr' : (partialTranspose ρ).trace = 1 := htr
  have hflip' : partialTranspose ((X ⊗ₖ X) * (Z ⊗ₖ Z)) =
      -(paired (Complex.I • (X * Z))) := by
    rw [← hy]
    have h := congrArg partialTranspose hflip
    change paired X * paired Z = partialTranspose (-((X ⊗ₖ X) * (Z ⊗ₖ Z))) at h
    rw [pt_neg] at h
    rw [h, neg_neg]
  let x := expectation ρ (paired X)
  let z := expectation ρ (paired Z)
  let y := expectation ρ (paired (Complex.I • (X * Z)))
  have hplus (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1) :
      0 ≤ 1 + a * x + b * z + (a * b) * y := by
    have h := joint_sign_test ρ (paired X) (paired Z) hρ htr hxH hzH hxx hzz hcomm a b ha hb
    simpa only [x, z, y, hy] using h
  have hminus (a b : ℝ) (ha : a * a = 1) (hb : b * b = 1) :
      0 ≤ 1 + a * x + b * z - (a * b) * y := by
    have h := joint_sign_test (partialTranspose ρ) (X ⊗ₖ X) (Z ⊗ₖ Z)
      hpt htr' hxH' hzH' hxx' hzz' hcomm' a b ha hb
    simpa only [expectation_pt, hflip', pt_kronecker, expectation_neg,
      paired, x, z, y, mul_neg, sub_eq_add_neg] using h
  have h₁ := hplus 1 1 (by norm_num) (by norm_num)
  have h₂ := hplus 1 (-1) (by norm_num) (by norm_num)
  have h₃ := hplus (-1) 1 (by norm_num) (by norm_num)
  have h₄ := hplus (-1) (-1) (by norm_num) (by norm_num)
  have h₅ := hminus 1 1 (by norm_num) (by norm_num)
  have h₆ := hminus 1 (-1) (by norm_num) (by norm_num)
  have h₇ := hminus (-1) 1 (by norm_num) (by norm_num)
  have h₈ := hminus (-1) (-1) (by norm_num) (by norm_num)
  norm_num at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  change |x| + |z| + |y| ≤ 1
  by_cases hx : 0 ≤ x <;> by_cases hz : 0 ≤ z <;> by_cases h' : 0 ≤ y <;>
    (first | rw [abs_of_nonneg hx] | rw [abs_of_neg (lt_of_not_ge hx)]) <;>
    (first | rw [abs_of_nonneg hz] | rw [abs_of_neg (lt_of_not_ge hz)]) <;>
    (first | rw [abs_of_nonneg h'] | rw [abs_of_neg (lt_of_not_ge h')]) <;>
    linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

end PauliTriple

section Diagonal

variable [Fintype A] [DecidableEq A] [Nonempty A] [Fintype S] [DecidableEq S]

/-- The Pauli-diagonal probe with unnormalized Pauli basis matrices. -/
def diagonalProbe (P : S → Matrix A A ℂ) (coeff : S → ℝ) :
    Matrix (A × A) (A × A) ℂ :=
  ∑ s, ((coeff s : ℂ) / (Fintype.card A : ℂ) ^ 2) • paired (P s)

/-- Trace orthogonality identifies an actual trace expectation with the
coefficient in the diagonal expansion. -/
theorem diagonalProbe_correlation (P : S → Matrix A A ℂ) (coeff : S → ℝ)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (t : S) : expectation (diagonalProbe P coeff) (paired (P t)) = coeff t := by
  have hpair (s : S) : (paired (P s) * paired (P t)).trace =
      if s = t then (Fintype.card A : ℂ) ^ 2 else 0 := by
    simp only [paired, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      Matrix.trace_kronecker, Matrix.trace_transpose, Matrix.trace_mul_comm (P t) (P s),
      horth s t]
    split <;> simp [pow_two]
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (diagonalProbe P coeff * paired (P t)).trace = (coeff t : ℂ) := by
    rw [diagonalProbe, Finset.sum_mul, Matrix.trace_sum]
    simp only [Matrix.smul_mul, Matrix.trace_smul, hpair, smul_eq_mul]
    rw [Finset.sum_eq_single t]
    · simp [hcard]
    · intro s _ hst
      simp [hst]
    · simp
  simp [expectation, hsum]

/-- The least magnitude of the diagonal HS coefficients. In normalized Pauli
coordinates the coefficient of each tensor factor is λₛ/d. -/
def leastDiagonalGain [Nonempty S] (d : ℕ) (coeff : S → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun s => |coeff s| / (d : ℝ)

/-- One anticommuting triple suffices for the least diagonal coefficient
bound. The probe assumptions concern the finite matrix and its actual
partial transpose. -/
theorem diagonal_gain_le [Nonempty S] (P : S → Matrix A A ℂ) (coeff : S → ℝ)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (hρ : (diagonalProbe P coeff).PosSemidef)
    (hpt : (partialTranspose (diagonalProbe P coeff)).PosSemidef)
    (htr : (diagonalProbe P coeff).trace = 1)
    (x z y : S) (hx : (P x)ᴴ = P x) (hz : (P z)ᴴ = P z)
    (hxx : P x * P x = 1) (hzz : P z * P z = 1)
    (hanti : P z * P x = -(P x * P z)) (hy : P y = Complex.I • (P x * P z)) :
    leastDiagonalGain (Fintype.card A) coeff ≤ 1 / (3 * (Fintype.card A : ℝ)) := by
  have ht := ppt_anticommuting_triple (diagonalProbe P coeff) hρ hpt htr
    (P x) (P z) hx hz hxx hzz hanti
  rw [← hy, diagonalProbe_correlation P coeff horth, diagonalProbe_correlation P coeff horth,
    diagonalProbe_correlation P coeff horth] at ht
  let d : ℝ := Fintype.card A
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have lower (s : S) : leastDiagonalGain (Fintype.card A) coeff * d ≤ |coeff s| := by
    apply (le_div_iff₀ hd).mp
    exact Finset.inf'_le _ (Finset.mem_univ s)
  have hs : leastDiagonalGain (Fintype.card A) coeff * d ≤ 1 / 3 := by
    linarith only [lower x, lower z, lower y, ht]
  change leastDiagonalGain (Fintype.card A) coeff ≤ 1 / (3 * d)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * d)).2
  calc
    _ = 3 * (leastDiagonalGain (Fintype.card A) coeff * d) := by ring
    _ ≤ 1 := by linarith only [hs]

end Diagonal

section TwoQubit

abbrev QubitPair := Fin 2 × Fin 2
abbrev BellLabel := Fin 4 × Fin 4

/-- The label order of the imported Bell projectors is I, Z, X, Y. -/
def bellPauli (a : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliMatrix (![Pauli.I, Pauli.Z, Pauli.X, Pauli.Y] a)

def twoQubitPauli (s : BellLabel) : Matrix QubitPair QubitPair ℂ :=
  bellPauli s.1 ⊗ₖ bellPauli s.2

private theorem one_qubit_orth (a b : Fin 4) :
    (bellPauli a * bellPauli b).trace = if a = b then (2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [bellPauli, pauliMatrix, qubitX, qubitZ, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Complex.I_mul_I] <;>
    ring

private theorem two_qubit_orth (s t : BellLabel) :
    (twoQubitPauli s * twoQubitPauli t).trace = if s = t then
      (Fintype.card QubitPair : ℂ) else 0 := by
  rcases s with ⟨a, b⟩
  rcases t with ⟨c, d⟩
  simp only [twoQubitPauli, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, one_qubit_orth,
    Prod.mk.injEq, Fintype.card_prod, Fintype.card_fin]
  by_cases h₁ : a = c <;> by_cases h₂ : b = d <;> norm_num [h₁, h₂]

/-- The least diagonal HS coefficient of every d=4 Pauli-diagonal PPT
density matrix is at most 1/12. -/
theorem two_qubit_diagonal_gain_le (coeff : BellLabel → ℝ)
    (hρ : (diagonalProbe twoQubitPauli coeff).PosSemidef)
    (hpt : (partialTranspose (diagonalProbe twoQubitPauli coeff)).PosSemidef)
    (htr : (diagonalProbe twoQubitPauli coeff).trace = 1) :
    leastDiagonalGain 4 coeff ≤ 1 / 12 := by
  obtain ⟨hanti, hx, hz, hxx, hzz⟩ := qubit_weyl_star
  change qubitXᴴ = qubitX at hx
  change qubitZᴴ = qubitZ at hz
  have hx2 := (tensor_involution qubitX (1 : Matrix (Fin 2) (Fin 2) ℂ) hx
    Matrix.conjTranspose_one (by simpa [pow_two] using hxx) (one_mul 1))
  have hz2 := (tensor_involution qubitZ (1 : Matrix (Fin 2) (Fin 2) ℂ) hz
    Matrix.conjTranspose_one (by simpa [pow_two] using hzz) (one_mul 1))
  have ha : twoQubitPauli (1, 0) * twoQubitPauli (2, 0) =
      -(twoQubitPauli (2, 0) * twoQubitPauli (1, 0)) := by
    change (qubitZ ⊗ₖ 1) * (qubitX ⊗ₖ 1) = -((qubitX ⊗ₖ 1) * (qubitZ ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hanti, kronecker_neg_left]
  have hy : twoQubitPauli (3, 0) = Complex.I •
      (twoQubitPauli (2, 0) * twoQubitPauli (1, 0)) := by
    change (Complex.I • (qubitX * qubitZ)) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      Complex.I • ((qubitX ⊗ₖ 1) * (qubitZ ⊗ₖ 1))
    rw [← Matrix.mul_kronecker_mul, one_mul, Matrix.smul_kronecker]
  have h := diagonal_gain_le twoQubitPauli coeff two_qubit_orth hρ hpt htr
    (2, 0) (1, 0) (3, 0) hx2.1 hz2.1 hx2.2 hz2.2 ha hy
  rw [show Fintype.card QubitPair = 4 by simp [QubitPair]] at h
  norm_num at h ⊢
  exact h

private def bellKet (a : Fin 4) (i : Fin 2 × Fin 2) : ℂ :=
  if a < 2 then
    if i = (0, 0) then 1 else if i = (1, 1) then if a = 0 then 1 else -1 else 0
  else
    if i = (0, 1) then 1 else if i = (1, 0) then if a = 2 then 1 else -1 else 0

private theorem bellProjector_eq_outer (a : Fin 4) :
    bellProjector a = (1 / 2 : ℝ) • vecMulVec (bellKet a) (star (bellKet a)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases a <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [bellProjector, bellKet, D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self, Matrix.vecMulVec,
      Complex.real_smul] <;>
    norm_num

private theorem bellProjector_psd (a : Fin 4) : (bellProjector a).PosSemidef := by
  rw [bellProjector_eq_outer]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem bellProjector_trace (a : Fin 4) : (bellProjector a).trace = 1 := by
  rw [bellProjector_eq_outer, Matrix.trace_smul, Matrix.trace_vecMulVec]
  fin_cases a <;> norm_num [dotProduct, bellKet, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.real_smul]

private def interleave : (QubitPair × QubitPair) ≃ (QubitPair × QubitPair) :=
  Equiv.prodProdProdComm (Fin 2) (Fin 2) (Fin 2) (Fin 2)

/-- Tensor-Bell projector in the split (input qubits) × (ancilla qubits). -/
def latticeProjector (t : BellLabel) : Matrix (QubitPair × QubitPair) (QubitPair × QubitPair) ℂ :=
  (bellProjector t.1 ⊗ₖ bellProjector t.2).submatrix interleave interleave

private theorem latticeProjector_psd (t : BellLabel) : (latticeProjector t).PosSemidef :=
  ((bellProjector_psd t.1).kronecker (bellProjector_psd t.2)).submatrix interleave

private theorem latticeProjector_trace (t : BellLabel) : (latticeProjector t).trace = 1 := by
  let M := bellProjector t.1 ⊗ₖ bellProjector t.2
  have hre : (M.submatrix interleave interleave).trace = M.trace := by
    change (∑ i, M (interleave i) (interleave i)) = ∑ i, M i i
    exact Equiv.sum_comp interleave (fun i => M i i)
  change (M.submatrix interleave interleave).trace = 1
  rw [hre]
  simp [M, Matrix.trace_kronecker, bellProjector_trace]

/-- I, Z, X, Y indexing on each Bell pair. -/
def witnessSupport : Fin 6 → BellLabel :=
  ![(2, 2), (3, 3), (0, 0), (1, 2), (1, 3), (1, 0)]

/-- Support after taking the second-factor partial transpose. -/
def witnessPTSupport : Fin 6 → BellLabel :=
  ![(0, 0), (0, 2), (3, 2), (3, 3), (1, 2), (1, 1)]

def latticeMixture (support : Fin 6 → BellLabel) :
    Matrix (QubitPair × QubitPair) (QubitPair × QubitPair) ℂ :=
  ∑ t, (1 / 6 : ℝ) • latticeProjector (support t)

def sixBellWitness := latticeMixture witnessSupport

private theorem latticeMixture_psd (support : Fin 6 → BellLabel) :
    (latticeMixture support).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro t _
  exact (latticeProjector_psd (support t)).smul (by norm_num : (0 : ℝ) ≤ 1 / 6)

private theorem latticeMixture_trace (support : Fin 6 → BellLabel) :
    (latticeMixture support).trace = 1 := by
  simp only [latticeMixture, Matrix.trace_sum, Matrix.trace_smul, latticeProjector_trace]
  norm_num [Fin.sum_univ_succ, Complex.real_smul]

/-- The single-pair Bell character in the I, Z, X, Y label order. -/
def bellCharacter (s t : Fin 4) : ℝ :=
  if s = 0 ∨ t = 0 ∨ s = t then 1 else -1

def latticeCoefficient (support : Fin 6 → BellLabel) (s : BellLabel) : ℝ :=
  (∑ t, bellCharacter s.1 (support t).1 * bellCharacter s.2 (support t).2) / 6

private theorem bellProjector_paired (t : Fin 4) :
    bellProjector t =
      ∑ s : Fin 4, ((bellCharacter s t : ℂ) / 4) • paired (bellPauli s) := by
  rw [bellProjector_eq_outer]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases t <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [bellKet, bellCharacter, paired, bellPauli, pauliMatrix, qubitX, qubitZ,
      Fin.sum_univ_succ, Fin.sum_univ_two, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.kronecker_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Complex.real_smul,
      Complex.I_mul_I] <;> ring

private theorem latticeProjector_paired (t : BellLabel) :
    latticeProjector t = diagonalProbe twoQubitPauli
      (fun s => bellCharacter s.1 t.1 * bellCharacter s.2 t.2) := by
  ext ⟨⟨i, j⟩, ⟨k, l⟩⟩ ⟨⟨i', j'⟩, ⟨k', l'⟩⟩
  change bellProjector t.1 (i, k) (i', k') * bellProjector t.2 (j, l) (j', l') = _
  rw [bellProjector_paired t.1, bellProjector_paired t.2]
  simp only [diagonalProbe, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, paired,
    twoQubitPauli, Matrix.kronecker_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fin, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  norm_num <;> ring

theorem latticeMixture_diagonal (support : Fin 6 → BellLabel) :
    latticeMixture support = diagonalProbe twoQubitPauli (latticeCoefficient support) := by
  simp only [latticeMixture, latticeProjector_paired, diagonalProbe, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = (∑ t : Fin 6,
        (1 / 6 : ℂ) * ((↑(bellCharacter s.1 (support t).1 *
          bellCharacter s.2 (support t).2) : ℂ) / (Fintype.card QubitPair : ℂ) ^ 2)) •
        paired (twoQubitPauli s) := by
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro t _
      rw [← smul_assoc]
      norm_num [Complex.real_smul]
    _ = _ := by
      congr 1
      simp only [latticeCoefficient, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_ofNat,
        Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

private def transposeSign (s : Fin 4) : ℝ := if s = 3 then -1 else 1

private theorem bellPauli_transpose (s : Fin 4) : (bellPauli s)ᵀ = transposeSign s • bellPauli s := by
  ext i j
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [transposeSign, bellPauli, pauliMatrix, qubitX, qubitZ, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Complex.real_smul]

private theorem twoQubitPauli_transpose (s : BellLabel) :
    (twoQubitPauli s)ᵀ = (transposeSign s.1 * transposeSign s.2) • twoQubitPauli s := by
  have h : (twoQubitPauli s)ᵀ = (bellPauli s.1)ᵀ ⊗ₖ (bellPauli s.2)ᵀ := rfl
  rw [h, bellPauli_transpose, bellPauli_transpose, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, twoQubitPauli]

private theorem pt_diagonalProbe (coeff : BellLabel → ℝ) :
    partialTranspose (diagonalProbe twoQubitPauli coeff) =
      diagonalProbe twoQubitPauli (fun s => (transposeSign s.1 * transposeSign s.2) * coeff s) := by
  have hp (s : BellLabel) : partialTranspose (paired (twoQubitPauli s)) =
      (transposeSign s.1 * transposeSign s.2) • paired (twoQubitPauli s) := by
    have ht := congrArg Matrix.transpose (twoQubitPauli_transpose s)
    rw [Matrix.transpose_transpose, Matrix.transpose_smul] at ht
    rw [paired, pt_kronecker, Matrix.transpose_transpose, ← Matrix.kronecker_smul, ← ht]
  have hsum (f : BellLabel → Matrix (QubitPair × QubitPair) (QubitPair × QubitPair) ℂ) :
      partialTranspose (∑ s, f s) = ∑ s, partialTranspose (f s) := by
    ext i j
    simp only [partialTranspose,
      D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose, Matrix.sum_apply]
  have hsmul (c : ℂ) (M : Matrix (QubitPair × QubitPair) (QubitPair × QubitPair) ℂ) :
      partialTranspose (c • M) = c • partialTranspose M := rfl
  simp only [diagonalProbe, hsum, hsmul, hp]
  apply Finset.sum_congr rfl
  intro s _
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The partial transpose is the uniform mixture on the six listed labels. -/
theorem sixBellWitness_partialTranspose :
    partialTranspose sixBellWitness = latticeMixture witnessPTSupport := by
  rw [sixBellWitness, latticeMixture_diagonal, pt_diagonalProbe, latticeMixture_diagonal]
  congr 1
  funext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [latticeCoefficient, transposeSign, witnessSupport, witnessPTSupport,
      bellCharacter, Fin.sum_univ_succ]

private theorem sixBell_coefficient_abs (s : BellLabel) :
    |latticeCoefficient witnessSupport s| = if s = (0, 0) then 1 else 1 / 3 := by
  rcases s with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [latticeCoefficient, witnessSupport, bellCharacter, Fin.sum_univ_succ]

/-- The six-Bell PPT witness attains the d=4 least diagonal coefficient bound. -/
theorem sixBellWitness_attains :
    sixBellWitness.PosSemidef ∧
    (partialTranspose sixBellWitness).PosSemidef ∧
    sixBellWitness.trace = 1 ∧
    sixBellWitness = diagonalProbe twoQubitPauli (latticeCoefficient witnessSupport) ∧
    leastDiagonalGain 4 (latticeCoefficient witnessSupport) = 1 / 12 := by
  refine ⟨latticeMixture_psd _, ?_, latticeMixture_trace _, latticeMixture_diagonal _, ?_⟩
  · rw [sixBellWitness_partialTranspose]
    exact latticeMixture_psd _
  · apply le_antisymm
    · exact two_qubit_diagonal_gain_le _ (latticeMixture_diagonal _ ▸ latticeMixture_psd _)
        (latticeMixture_diagonal _ ▸ (sixBellWitness_partialTranspose ▸ latticeMixture_psd _))
        (latticeMixture_diagonal _ ▸ latticeMixture_trace _)
    · apply Finset.le_inf'
      intro s _
      rw [sixBell_coefficient_abs]
      split <;> norm_num

end TwoQubit

section Channels

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf (MatrixMap)
open Original8340Global (inputChoi inputChoi_index_swap)

variable [Fintype A] [DecidableEq A]

/-- The depolarizing qubit-output map plus a signed Pauli direction. -/
def directionChannel (P : Matrix A A ℂ) (e : ℝ) : MatrixMap A (Fin 2) ℂ where
  toFun M := (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    ((e : ℂ) * (P * M).trace) • qubitZ
  map_add' M N := by
    simp only [Matrix.trace_add, mul_add, add_div, add_smul]
    abel
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.trace_smul, smul_add,
      smul_smul, smul_eq_mul]
    congr 1 <;> congr 1 <;> ring

private theorem qubitZ_trace : qubitZ.trace = 0 := by
  norm_num [qubitZ, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]

private theorem directionChannel_choi (P : Matrix A A ℂ) (e : ℝ) :
    inputChoi (directionChannel P e) =
      (1 / 2 : ℝ) • 1 + e • (Pᵀ ⊗ₖ qubitZ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change ((Matrix.single i j (1 : ℂ)).trace / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) a b +
    ((e : ℂ) * (P * Matrix.single i j 1).trace) * qubitZ a b = _
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul, one_smul]
  by_cases hij : i = j
  · subst j
    by_cases hab : a = b <;>
      norm_num [hab, Matrix.trace_single_eq_same, Matrix.one_apply, Matrix.kronecker_apply,
        Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul] <;> ring
  · simp [hij, Matrix.trace_single_eq_of_ne, Matrix.one_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Matrix.smul_apply, Complex.real_smul, mul_assoc]

/-- For a Hermitian Pauli involution, both signs give actual CPTP maps
to a qubit, with a Choi perturbation in just that Pauli direction. -/
theorem directionChannel_cptp (P : Matrix A A ℂ) (hP : Pᴴ = P) (hPP : P * P = 1)
    (s : ℝ) (hs : s * s = 1) :
    (directionChannel P (s / 2)).IsCompletelyPositive ∧
    (directionChannel P (s / 2)).IsTracePreserving := by
  constructor
  · apply (PhyslibLeaf.MatrixMap.choi_PSD_iff_CP_map _).mpr
    suffices hp : (inputChoi (directionChannel P (s / 2))).PosSemidef by
      rw [inputChoi_index_swap] at hp
      simpa [Matrix.submatrix_submatrix] using hp.submatrix Prod.swap
    rw [directionChannel_choi]
    obtain ⟨-, -, hz, -, hzz⟩ := qubit_weyl_star
    change qubitZᴴ = qubitZ at hz
    let K := Pᵀ ⊗ₖ qubitZ
    have hKt : (Pᵀ : Matrix A A ℂ)ᴴ = Pᵀ := by
      rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hP]
    have hKt2 : Pᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
    have hK : Kᴴ = K := by simp only [K, Matrix.conjTranspose_kronecker, hKt, hz]
    have hKK : K * K = 1 := by
      simp only [K, ← Matrix.mul_kronecker_mul, hKt2, ← pow_two qubitZ, hzz,
        Matrix.one_kronecker_one]
    let F := (1 : Matrix (A × Fin 2) (A × Fin 2) ℂ) + s • K
    have hF : Fᴴ = F := by simp [F, Matrix.conjTranspose_smul, hK]
    have hsquare : F * F = (2 : ℝ) • F := involution_factor_square K hKK s hs
    have hp := (Matrix.posSemidef_conjTranspose_mul_self F).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [hF, hsquare, smul_smul, show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num] at hp
    have he : (1 / 2 : ℝ) • F = (1 / 2 : ℝ) • 1 + (s / 2) • K := by
      dsimp only [F]
      rw [smul_add, smul_smul]
      congr 1 <;> congr 1 <;> ring
    rw [he] at hp
    exact hp
  · intro M
    change (((M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      ((↑(s / 2) : ℂ) * (P * M).trace) • qubitZ).trace = M.trace
    simp [Matrix.trace_add, Matrix.trace_smul, qubitZ_trace, smul_eq_mul]

/-- Difference of the opposite-sign Choi matrices is the tensor direction. -/
theorem directionChannel_choi_sub (P : Matrix A A ℂ) :
    inputChoi (directionChannel P (1 / 2)) - inputChoi (directionChannel P (-1 / 2)) =
      Pᵀ ⊗ₖ qubitZ := by
  rw [directionChannel_choi, directionChannel_choi]
  module

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- The image of a probe under a map on the first factor and the identity
on the ancilla. The output has indices O × A. -/
def probeOutput (M : MatrixMap A O ℂ) :
    Matrix (A × A) (A × A) ℂ →ₗ[ℂ] Matrix (O × A) (O × A) ℂ :=
  PhyslibLeaf.MatrixMap.kron M LinearMap.id

private theorem probeOutput_kronecker (M : MatrixMap A O ℂ) (X Y : Matrix A A ℂ) :
    probeOutput M (X ⊗ₖ Y) = M X ⊗ₖ Y := by
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    ext i j
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  have hM : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul]
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [probeOutput, PhyslibLeaf.MatrixMap.kron_def, hM]
  simp [LinearMap.id_apply, Matrix.single, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, ite_and, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

variable [Fintype S] [DecidableEq S]

/-- The signed Pauli output difference is supported on a single input word. -/
theorem directionChannel_output_sub (P : S → Matrix A A ℂ) (coeff : S → ℝ)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    [Nonempty A] (t : S) :
    probeOutput (directionChannel (P t) (1 / 2)) (diagonalProbe P coeff) -
      probeOutput (directionChannel (P t) (-1 / 2)) (diagonalProbe P coeff) =
        ((coeff t : ℂ) / (Fintype.card A : ℂ)) • (qubitZ ⊗ₖ (P t)ᵀ) := by
  simp only [diagonalProbe, map_sum, map_smul, paired, probeOutput_kronecker, ← Finset.sum_sub_distrib]
  have hdiff (s : S) : directionChannel (P t) (1 / 2) (P s) -
      directionChannel (P t) (-1 / 2) (P s) = (P t * P s).trace • qubitZ := by
    change (((P s).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((↑(1 / 2 : ℝ) : ℂ) * (P t * P s).trace) • qubitZ) -
      (((P s).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((↑(-1 / 2 : ℝ) : ℂ) * (P t * P s).trace) • qubitZ) = _
    push_cast
    module
  have hk (X Y : Matrix (Fin 2) (Fin 2) ℂ) (Z : Matrix A A ℂ) :
      X ⊗ₖ Z - Y ⊗ₖ Z = (X - Y) ⊗ₖ Z := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [Matrix.sub_apply, Matrix.kronecker_apply, sub_mul]
  simp only [← smul_sub, hk, hdiff, horth t]
  rw [Finset.sum_eq_single t]
  · simp only [if_pos rfl, ite_true, Matrix.smul_kronecker, smul_smul]
    congr 1
    have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · intro s _ hst
    simp [Ne.symm hst]
  · simp

/-- The squared Hilbert–Schmidt norm of a finite complex matrix. -/
def hsSquare {J : Type*} [Fintype J] (M : Matrix J J ℂ) : ℝ :=
  (Mᴴ * M).trace.re

private theorem hsSquare_smul {J : Type*} [Fintype J] (r : ℝ) (M : Matrix J J ℂ) :
    hsSquare (r • M) = r ^ 2 * hsSquare M := by
  simp [hsSquare, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, pow_two]

private theorem hsSquare_swapKronecker {I J : Type*} [Fintype I] [Fintype J]
    (X : Matrix I I ℂ) (Y : Matrix J J ℂ) : hsSquare (X ⊗ₖ Y) = hsSquare (Y ⊗ₖ X) := by
  simp only [hsSquare, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker, mul_comm]

/-- The actual signed CPTP direction realizes the squared ratio
corresponding to its diagonal coefficient, with unnormalized Choi matrices. -/
theorem directionChannel_hsSquare (P : S → Matrix A A ℂ) (coeff : S → ℝ)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    [Nonempty A] (t : S) :
    hsSquare (probeOutput (directionChannel (P t) (1 / 2)) (diagonalProbe P coeff) -
      probeOutput (directionChannel (P t) (-1 / 2)) (diagonalProbe P coeff)) =
    (|coeff t| / (Fintype.card A : ℝ)) ^ 2 *
      hsSquare (inputChoi (directionChannel (P t) (1 / 2)) -
        inputChoi (directionChannel (P t) (-1 / 2))) := by
  rw [directionChannel_output_sub P coeff horth, directionChannel_choi_sub]
  have hsmul : ((coeff t : ℂ) / (Fintype.card A : ℂ)) • (qubitZ ⊗ₖ (P t)ᵀ) =
      (coeff t / (Fintype.card A : ℝ)) • (qubitZ ⊗ₖ (P t)ᵀ) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hsmul, hsSquare_smul, hsSquare_swapKronecker qubitZ, div_pow, div_pow, sq_abs]

private theorem hsSquare_submatrix {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I I ℂ) (e : J ≃ I) :
    hsSquare (M.submatrix e e) = hsSquare M := by
  rw [hsSquare, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  exact congrArg Complex.re (Equiv.sum_comp e fun i => (Mᴴ * M) i i)

private theorem hsSquare_tensor_sum
    (X : S → Matrix O O ℂ) (Y : S → Matrix A A ℂ) (w : S → ℝ) (d : ℝ)
    (hY : ∀ s t, ((Y s)ᴴ * Y t).trace = if s = t then (d : ℂ) else 0) :
    hsSquare (∑ s, w s • (X s ⊗ₖ Y s)) =
      d * ∑ s, (w s) ^ 2 * hsSquare (X s) := by
  simp only [hsSquare, Matrix.conjTranspose_sum, Finset.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single s]
  · simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_smul,
      Matrix.trace_kronecker, hY, Complex.real_smul, Complex.mul_re, pow_two]
    <;> ring
  · intro t _ hne
    simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.trace_smul,
      Matrix.trace_kronecker, hY, hne, Ne.symm hne]
  · simp

private theorem transpose_basis_orth (P : S → Matrix A A ℂ)
    (hH : ∀ s, (P s)ᴴ = P s)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (s t : S) : (((P s)ᵀ)ᴴ * (P t)ᵀ).trace =
      if s = t then ((Fintype.card A : ℝ) : ℂ) else 0 := by
  rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hH,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm (P t) (P s), horth]
  simp

/-- Parseval for the actual tensor-channel output of a diagonal probe. Here
each unnormalized input Pauli word has squared Hilbert–Schmidt norm d. -/
theorem diagonalProbe_output_hsSquare (P : S → Matrix A A ℂ) (coeff : S → ℝ)
    (hH : ∀ s, (P s)ᴴ = P s)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (M : MatrixMap A O ℂ) :
    hsSquare (probeOutput M (diagonalProbe P coeff)) =
      (Fintype.card A : ℝ) *
        ∑ s, (coeff s / (Fintype.card A : ℝ) ^ 2) ^ 2 * hsSquare (M (P s)) := by
  simp only [diagonalProbe, map_sum, map_smul, paired, probeOutput_kronecker]
  have he (s : S) :
      ((coeff s : ℂ) / (Fintype.card A : ℂ) ^ 2) • (M (P s) ⊗ₖ (P s)ᵀ) =
      (coeff s / (Fintype.card A : ℝ) ^ 2) • (M (P s) ⊗ₖ (P s)ᵀ) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast]
  simp only [he]
  exact hsSquare_tensor_sum _ _ _ _ (transpose_basis_orth P hH horth)

/-- Parseval for the unnormalized input-first Choi matrix. The basis
hypothesis expands each actual matrix unit in the unnormalized Pauli basis. -/
theorem inputChoi_hsSquare (P : S → Matrix A A ℂ)
    (hH : ∀ s, (P s)ᴴ = P s)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (hBasis : ∀ i j : A, Matrix.single i j (1 : ℂ) =
      ∑ s, (P s j i / (Fintype.card A : ℂ)) • P s)
    (M : MatrixMap A O ℂ) :
    hsSquare (inputChoi M) = (Fintype.card A : ℝ) *
      ∑ s, ((Fintype.card A : ℝ)⁻¹) ^ 2 * hsSquare (M (P s)) := by
  have hEq : M.choi_matrix =
      ∑ s, (Fintype.card A : ℝ)⁻¹ • (M (P s) ⊗ₖ (P s)ᵀ) := by
    ext ⟨a, i⟩ ⟨b, j⟩
    change M (Matrix.single i j 1) a b = _
    rw [hBasis i j]
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, Matrix.kronecker_apply,
      Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro s _
    rw [div_eq_mul_inv]
    ring
  rw [inputChoi_index_swap]
  have hswap : hsSquare (M.choi_matrix.submatrix Prod.swap Prod.swap) =
      hsSquare M.choi_matrix := hsSquare_submatrix _ (Equiv.prodComm A O)
  rw [hswap, hEq]
  exact hsSquare_tensor_sum _ _ _ _ (transpose_basis_orth P hH horth)

/-- Every linear map, including the difference of two channels, obeys the
least-gain bound for the actual output and the unnormalized Choi matrix. -/
theorem leastDiagonalGain_hsSquare_le [Nonempty A] [Nonempty S]
    (P : S → Matrix A A ℂ) (coeff : S → ℝ) (hH : ∀ s, (P s)ᴴ = P s)
    (horth : ∀ s t, (P s * P t).trace = if s = t then (Fintype.card A : ℂ) else 0)
    (hBasis : ∀ i j : A, Matrix.single i j (1 : ℂ) =
      ∑ s, (P s j i / (Fintype.card A : ℂ)) • P s)
    (M : MatrixMap A O ℂ) :
    leastDiagonalGain (Fintype.card A) coeff ^ 2 * hsSquare (inputChoi M) ≤
      hsSquare (probeOutput M (diagonalProbe P coeff)) := by
  rw [inputChoi_hsSquare P hH horth hBasis, diagonalProbe_output_hsSquare P coeff hH horth]
  let d : ℝ := Fintype.card A
  let g := leastDiagonalGain (Fintype.card A) coeff
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hg : 0 ≤ g := Finset.le_inf' _ _ fun s _ => div_nonneg (abs_nonneg _) hd.le
  change g ^ 2 * (d * ∑ s, d⁻¹ ^ 2 * hsSquare (M (P s))) ≤
    d * ∑ s, (coeff s / d ^ 2) ^ 2 * hsSquare (M (P s))
  rw [← mul_assoc, mul_comm (g ^ 2) d, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hd.le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hs : g ≤ |coeff s| / d := Finset.inf'_le _ (Finset.mem_univ s)
  have hp : 0 ≤ hsSquare (M (P s)) :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg).1
  have hsquare : g ^ 2 ≤ (|coeff s| / d) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (add_nonneg hg (hg.trans hs))]
  have hi : g ^ 2 * d⁻¹ ^ 2 ≤ (coeff s / d ^ 2) ^ 2 := by
    calc
      _ ≤ (|coeff s| / d) ^ 2 * d⁻¹ ^ 2 := mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
      _ = _ := by rw [div_pow, sq_abs, div_pow]; field_simp <;> ring
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hi hp

end Channels

section SharpTomography

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open PhyslibLeaf (MatrixMap)
open Original8340Global (inputChoi)

private theorem bellPauli_involution (s : Fin 4) :
    (bellPauli s)ᴴ = bellPauli s ∧ bellPauli s * bellPauli s = 1 := by
  fin_cases s <;> constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [bellPauli, pauliMatrix, qubitX, qubitZ, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two, Complex.I_mul_I]

private theorem twoQubitPauli_involution (s : BellLabel) :
    (twoQubitPauli s)ᴴ = twoQubitPauli s ∧ twoQubitPauli s * twoQubitPauli s = 1 :=
  tensor_involution _ _ (bellPauli_involution s.1).1 (bellPauli_involution s.2).1
    (bellPauli_involution s.1).2 (bellPauli_involution s.2).2

private theorem bellKet_zero (i j : Fin 2) :
    bellKet 0 (i, j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [bellKet]

private theorem twoQubitPauli_basis (i j : QubitPair) :
    Matrix.single i j (1 : ℂ) =
      ∑ s : BellLabel, (twoQubitPauli s j i / (Fintype.card QubitPair : ℂ)) •
        twoQubitPauli s := by
  ext k l
  have hb : latticeProjector (0, 0) (k, i) (l, j) =
      (1 / 4 : ℂ) * Matrix.single i j 1 k l := by
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    rcases k with ⟨k₁, k₂⟩
    rcases l with ⟨l₁, l₂⟩
    change bellProjector 0 (k₁, i₁) (l₁, j₁) *
      bellProjector 0 (k₂, i₂) (l₂, j₂) = _
    rw [bellProjector_eq_outer]
    by_cases hki₁ : k₁ = i₁ <;> by_cases hki₂ : k₂ = i₂ <;>
      by_cases hlj₁ : l₁ = j₁ <;> by_cases hlj₂ : l₂ = j₂ <;>
      norm_num [Matrix.vecMulVec_apply, bellKet_zero, Matrix.single, Complex.real_smul,
        Prod.mk.injEq, hki₁, hki₂, hlj₁, hlj₂] <;> grind
  have h := congrArg (fun M : Matrix (QubitPair × QubitPair) (QubitPair × QubitPair) ℂ =>
    M (k, i) (l, j)) (latticeProjector_paired (0, 0))
  simp only [diagonalProbe, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, paired,
    Matrix.kronecker_apply, Matrix.transpose_apply, bellCharacter, eq_self, or_true, true_or, ite_true,
    mul_one, Complex.ofReal_one, Fintype.card_prod, Fintype.card_fin] at h
  calc
    _ = (4 : ℂ) * latticeProjector (0, 0) (k, i) (l, j) := by rw [hb]; ring
    _ = _ := by
      rw [h]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
        Fintype.card_prod, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro s _
      norm_num <;> ring

private theorem d4_direction_choi_square (s : BellLabel) :
    hsSquare (inputChoi (directionChannel (twoQubitPauli s) (1 / 2)) -
      inputChoi (directionChannel (twoQubitPauli s) (-1 / 2))) = 8 := by
  rw [directionChannel_choi_sub]
  obtain ⟨hP, hPP⟩ := twoQubitPauli_involution s
  obtain ⟨-, -, hz, -, hzz⟩ := qubit_weyl_star
  change qubitZᴴ = qubitZ at hz
  have hT : ((twoQubitPauli s)ᵀ)ᴴ = (twoQubitPauli s)ᵀ := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, hP]
  have hTT : (twoQubitPauli s)ᵀ * (twoQubitPauli s)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  simp only [hsSquare, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hT, hz,
    hTT, ← pow_two qubitZ, hzz, Matrix.one_kronecker_one, Matrix.trace_one, Fintype.card_prod,
    Fintype.card_fin, QubitPair]
  norm_num

/-- A minimizing direction is attained by distinct CPTP maps into a qubit.
Together with leastDiagonalGain_hsSquare_le this identifies the exact gain. -/
theorem d4_cptp_attains (coeff : BellLabel → ℝ) :
    ∃ Φ Ψ : MatrixMap QubitPair (Fin 2) ℂ,
      Φ.IsCompletelyPositive ∧ Φ.IsTracePreserving ∧
      Ψ.IsCompletelyPositive ∧ Ψ.IsTracePreserving ∧
      hsSquare (inputChoi Φ - inputChoi Ψ) = 8 ∧
      hsSquare (probeOutput Φ (diagonalProbe twoQubitPauli coeff) -
        probeOutput Ψ (diagonalProbe twoQubitPauli coeff)) =
        leastDiagonalGain 4 coeff ^ 2 * hsSquare (inputChoi Φ - inputChoi Ψ) := by
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset BellLabel).Nonempty)
    (fun t => |coeff t| / (4 : ℝ))
  obtain ⟨hP, hPP⟩ := twoQubitPauli_involution s
  obtain ⟨hp, htp⟩ := directionChannel_cptp (twoQubitPauli s) hP hPP 1 (by norm_num)
  obtain ⟨hm, htm⟩ := directionChannel_cptp (twoQubitPauli s) hP hPP (-1) (by norm_num)
  refine ⟨_, _, hp, htp, hm, htm, d4_direction_choi_square s, ?_⟩
  change leastDiagonalGain 4 coeff = |coeff s| / (4 : ℝ) at hs
  rw [hs]
  simpa [QubitPair, Fintype.card_prod, Fintype.card_fin] using
    directionChannel_hsSquare twoQubitPauli coeff two_qubit_orth s

/-- On the sharp witness, the squared output gain is at least 1/144
for every actual unnormalized Choi difference. -/
theorem sixBellWitness_hsSquare_lower {O : Type*} [Fintype O] [DecidableEq O]
    (Δ : MatrixMap QubitPair O ℂ) :
    (1 / 144 : ℝ) * hsSquare (inputChoi Δ) ≤ hsSquare (probeOutput Δ sixBellWitness) := by
  rw [sixBellWitness_attains.2.2.2.1]
  have h := leastDiagonalGain_hsSquare_le twoQubitPauli (latticeCoefficient witnessSupport)
    (fun s => (twoQubitPauli_involution s).1) two_qubit_orth twoQubitPauli_basis Δ
  change leastDiagonalGain 4 (latticeCoefficient witnessSupport) ^ 2 *
    hsSquare (inputChoi Δ) ≤ _ at h
  rw [sixBellWitness_attains.2.2.2.2] at h
  norm_num at h
  exact h

end SharpTomography

end D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography

#print axioms D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography.two_qubit_diagonal_gain_le
#print axioms D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography.sixBellWitness_attains
#print axioms D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography.d4_cptp_attains
#print axioms D5.S3.Quantum.ProcessReconstruction.PauliDiagonalPPTTomography.sixBellWitness_hsSquare_lower
