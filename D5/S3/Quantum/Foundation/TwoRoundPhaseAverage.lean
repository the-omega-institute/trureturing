/- GID: D5/S3/Quantum/Foundation/TwoRoundPhaseAverage
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundPhaseAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint signs preserve causal repairs, full tester events and marginal diagonals. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Classical

namespace D5.S3.Quantum.Foundation.TwoRoundPhaseAverage

open D5.S3.Quantum.Information.PartialTraceMutualInformation

abbrev AB := Fin 2 × Fin 2
abbrev Wire := AB × Fin 3
abbrev Phase := Fin 2 × Fin 2

/-- The signs at phases zero and pi on a two-dimensional port. -/
def bitSign (g i : Fin 2) : ℂ := if g = 1 ∧ i = 1 then -1 else 1

def phaseAB (g : Phase) (i : AB) : ℂ := bitSign g.1 i.1 * bitSign g.2 i.2

def phaseB (g : Phase) (i : Fin 2) : ℂ := bitSign g.2 i

def phaseD (g : Phase) (d : Fin 3) : ℂ :=
  if d = 0 then 1 else if d = 1 then bitSign g.1 1
  else bitSign g.1 1 * bitSign g.2 1

def phaseWire (g : Phase) (i : Wire) : ℂ := phaseAB g i.1 * phaseD g i.2

/-- Conjugation by a real diagonal sign matrix, expressed entrywise. -/
def signConjugate {n : Type*} (u : n → ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => u i * M i j * u j

def phaseAverage {n : Type*} (u : Phase → n → ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 / 4 : ℝ) • ∑ g : Phase, signConjugate (u g) M

def averageWire := phaseAverage phaseWire
def averageAB := phaseAverage phaseAB
def averageB := phaseAverage phaseB

/-- The original two-round causal normalization, with no support or rank restriction. -/
def Causal (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  S.PosSemidef ∧ sigma.PosSemidef ∧ Matrix.trace sigma = 1 ∧
    partialTraceRight S = Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) sigma

/-- Both the normalization operator and the complete quantum event remain variables. -/
def Tester (C : Matrix AB AB ℂ) (E : Matrix Wire Wire ℂ) : Prop :=
  C.PosSemidef ∧ partialTraceLeft C = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    E.PosSemidef ∧ (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ) - E).PosSemidef

def response (X E : Matrix Wire Wire ℂ) : ℝ := (Matrix.trace (X * E)).re

def ErrorBound (X : Matrix Wire Wire ℂ) (b : ℝ) : Prop :=
  ∀ C E, Tester C E → |response X E| ≤ b

def candidateVector (eps : ℝ) (i : Wire) : ℂ :=
  if i = ((0, 0), 0) then 1
  else if i = ((1, 0), 1) then (Real.sqrt (1 - eps) : ℂ)
  else if i = ((1, 1), 2) then (Real.sqrt eps : ℂ) else 0

def candidate (eps : ℝ) : Matrix Wire Wire ℂ :=
  Matrix.vecMulVec (candidateVector eps) (star (candidateVector eps))

def MainSupport (i : Wire) : Prop :=
  i = ((0, 0), 0) ∨ i = ((1, 0), 1) ∨ i = ((1, 1), 2)

private theorem bitSign_star (g i : Fin 2) : star (bitSign g i) = bitSign g i := by
  unfold bitSign
  split_ifs <;> simp

private theorem bitSign_sq (g i : Fin 2) : bitSign g i * bitSign g i = 1 := by
  unfold bitSign
  split_ifs <;> norm_num

private theorem phaseAB_star (g : Phase) (i : AB) :
    star (phaseAB g i) = phaseAB g i := by
  simp only [phaseAB, star_mul, bitSign_star]
  ring

private theorem phaseD_star (g : Phase) (d : Fin 3) :
    star (phaseD g d) = phaseD g d := by
  unfold phaseD
  split_ifs <;> simp [bitSign_star]

private theorem phaseD_sq (g : Phase) (d : Fin 3) :
    phaseD g d * phaseD g d = 1 := by
  unfold phaseD
  split_ifs
  · norm_num
  · exact bitSign_sq _ _
  · calc
      _ = (bitSign g.1 1 * bitSign g.1 1) *
          (bitSign g.2 1 * bitSign g.2 1) := by ring
      _ = 1 := by rw [bitSign_sq, bitSign_sq]; norm_num

private theorem phaseWire_star (g : Phase) (i : Wire) :
    star (phaseWire g i) = phaseWire g i := by
  simp only [phaseWire, star_mul, phaseAB_star, phaseD_star]
  ring

private theorem signConjugate_pos {n : Type*} [Finite n]
    (u : n → ℂ) (hu : ∀ i, star (u i) = u i)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) : (signConjugate u M).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  have heq : signConjugate u M = (Matrix.diagonal u)ᴴ * M * Matrix.diagonal u := by
    ext i j
    simp [signConjugate, Matrix.diagonal_conjTranspose, hu]
  rw [heq]
  exact hM.conjTranspose_mul_mul_same _

private theorem phaseAverage_pos {n : Type*} [Finite n]
    (u : Phase → n → ℂ) (hu : ∀ g i, star (u g i) = u g i)
    {M : Matrix n n ℂ} (hM : M.PosSemidef) : (phaseAverage u M).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  exact (Matrix.posSemidef_sum _ (fun g _ => signConjugate_pos _ (hu g) hM)).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 4)

private theorem average_apply {n : Type*} (u : Phase → n → ℂ)
    (M : Matrix n n ℂ) (i j : n) :
    phaseAverage u M i j = (1 / 4 : ℂ) * ∑ g : Phase, u g i * M i j * u g j := by
  simp [phaseAverage, signConjugate, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul]

private theorem average_diagonal {n : Type*} (u : Phase → n → ℂ)
    (hu : ∀ g i, u g i * u g i = 1) (M : Matrix n n ℂ) (i : n) :
    phaseAverage u M i i = M i i := by
  rw [average_apply]
  have heq (g : Phase) : u g i * M i i * u g i = M i i := by
    calc
      _ = (u g i * u g i) * M i i := by ring
      _ = M i i := by rw [hu]; ring
  simp_rw [heq]
  simp

private theorem signConjugate_sub {n : Type*} (u : n → ℂ) (M N : Matrix n n ℂ) :
    signConjugate u (M - N) = signConjugate u M - signConjugate u N := by
  ext i j
  simp [signConjugate, mul_sub, sub_mul]

private theorem average_sub {n : Type*} (u : Phase → n → ℂ) (M N : Matrix n n ℂ) :
    phaseAverage u (M - N) = phaseAverage u M - phaseAverage u N := by
  simp [phaseAverage, signConjugate_sub, Finset.sum_sub_distrib, smul_sub]

private theorem conjugate_partialRight (g : Phase) (S : Matrix Wire Wire ℂ) :
    partialTraceRight (signConjugate (phaseWire g) S) =
      signConjugate (phaseAB g) (partialTraceRight S) := by
  ext i j
  simp only [partialTraceRight, signConjugate, phaseWire, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = phaseAB g i * S (i, d) (j, d) * phaseAB g j * (phaseD g d * phaseD g d) := by ring
    _ = _ := by rw [phaseD_sq]; ring

private theorem conjugate_partialLeft (g : Phase) (C : Matrix AB AB ℂ) :
    partialTraceLeft (signConjugate (phaseAB g) C) =
      signConjugate (phaseB g) (partialTraceLeft C) := by
  let U := Matrix.diagonal (bitSign g.1)
  let V := Matrix.diagonal (bitSign g.2)
  let L := U ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  let R := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ V
  have hU : Uᴴ * U = 1 := by
    change (Matrix.diagonal (bitSign g.1))ᴴ * Matrix.diagonal (bitSign g.1) = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp_rw [Pi.star_apply, bitSign_star, bitSign_sq]
    exact Matrix.diagonal_one
  have hdiag : U ⊗ₖ V = Matrix.diagonal (phaseAB g) := by
    exact Matrix.diagonal_kronecker_diagonal (bitSign g.1) (bitSign g.2)
  have hRL : R * L = U ⊗ₖ V := by
    dsimp [R, L]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hfactor : signConjugate (phaseAB g) C = R * (L * C * Lᴴ) * Rᴴ := by
    calc
      _ = (U ⊗ₖ V) * C * (U ⊗ₖ V)ᴴ := by
        rw [hdiag]
        ext i j
        simp [signConjugate, Matrix.diagonal_conjTranspose, phaseAB_star]
      _ = _ := by rw [← hRL]; simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hfactor]
  have hr := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace1_right V
    (L * C * Lᴴ)
  have hl := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.ptrace1_left U C hU
  change partialTraceLeft (R * (L * C * Lᴴ) * Rᴴ) =
    signConjugate (phaseB g) (partialTraceLeft C)
  rw [hr, hl]
  ext i j
  simp [V, signConjugate, phaseB, Matrix.diagonal_conjTranspose, bitSign_star]

private theorem conjugate_causal_rhs (g : Phase) (sigma : Matrix (Fin 2) (Fin 2) ℂ) :
    signConjugate (phaseAB g) (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) sigma) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ)
        (signConjugate (phaseB g) sigma) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  by_cases h : a = a'
  · subst a'
    simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul,
      phaseAB, phaseB]
    calc
      _ = bitSign g.2 b * sigma b b' * bitSign g.2 b' *
          (bitSign g.1 a * bitSign g.1 a) := by ring
      _ = _ := by rw [bitSign_sq]; ring
  · simp [signConjugate, Matrix.kronecker, h]

private theorem conjugate_tester_rhs (g : Phase) (C : Matrix AB AB ℂ) :
    signConjugate (phaseWire g) (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      Matrix.kronecker (signConjugate (phaseAB g) C) (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rcases i with ⟨ab, d⟩
  rcases j with ⟨ab', d'⟩
  by_cases h : d = d'
  · subst d'
    simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one,
      phaseWire]
    calc
      _ = phaseAB g ab * C ab ab' * phaseAB g ab' * (phaseD g d * phaseD g d) := by ring
      _ = _ := by rw [phaseD_sq]; ring
  · simp [signConjugate, Matrix.kronecker, h]

private theorem signConjugate_one {n : Type*} [DecidableEq n]
    (u : n → ℂ) (hu : ∀ i, u i * u i = 1) :
    signConjugate u (1 : Matrix n n ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [signConjugate, hu]
  · simp [signConjugate, h]

private theorem conjugate_tester (g : Phase) {C : Matrix AB AB ℂ}
    {E : Matrix Wire Wire ℂ} (h : Tester C E) :
    Tester (signConjugate (phaseAB g) C) (signConjugate (phaseWire g) E) := by
  refine ⟨signConjugate_pos _ (phaseAB_star g) h.1, ?_,
    signConjugate_pos _ (phaseWire_star g) h.2.2.1, ?_⟩
  · rw [conjugate_partialLeft, h.2.1]
    exact signConjugate_one _ (bitSign_sq g.2)
  · rw [← conjugate_tester_rhs, ← signConjugate_sub]
    exact signConjugate_pos _ (phaseWire_star g) h.2.2.2

private theorem average_partialRight (S : Matrix Wire Wire ℂ) :
    partialTraceRight (averageWire S) = averageAB (partialTraceRight S) := by
  ext i j
  simp only [partialTraceRight, averageWire, averageAB, average_apply]
  change (∑ d : Fin 3, (1 / 4 : ℂ) *
      ∑ g : Phase, phaseWire g (i, d) * S (i, d) (j, d) * phaseWire g (j, d)) =
    (1 / 4 : ℂ) * ∑ g : Phase,
      phaseAB g i * (∑ d : Fin 3, S (i, d) (j, d)) * phaseAB g j
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have h := congrArg (fun M : Matrix AB AB ℂ => M i j) (conjugate_partialRight g S)
  exact h

private theorem average_partialLeft (C : Matrix AB AB ℂ) :
    partialTraceLeft (averageAB C) = averageB (partialTraceLeft C) := by
  ext i j
  simp only [partialTraceLeft, averageAB, averageB, average_apply]
  change (∑ a : Fin 2, (1 / 4 : ℂ) *
      ∑ g : Phase, phaseAB g (a, i) * C (a, i) (a, j) * phaseAB g (a, j)) =
    (1 / 4 : ℂ) * ∑ g : Phase,
      phaseB g i * (∑ a : Fin 2, C (a, i) (a, j)) * phaseB g j
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
    (conjugate_partialLeft g C)
  exact h

private theorem average_causal_rhs (sigma : Matrix (Fin 2) (Fin 2) ℂ) :
    averageAB (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) sigma) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (averageB sigma) := by
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  simp only [averageAB, averageB, average_apply, Matrix.kronecker, Matrix.kronecker_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have h := congrArg (fun M : Matrix AB AB ℂ => M (a, b) (a', b'))
    (conjugate_causal_rhs g sigma)
  simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply] at h
  linear_combination (1 / 4 : ℂ) * h

private theorem average_tester_rhs (C : Matrix AB AB ℂ) :
    averageWire (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      Matrix.kronecker (averageAB C) (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  rcases i with ⟨ab, d⟩
  rcases j with ⟨ab', d'⟩
  simp only [averageWire, averageAB, average_apply, Matrix.kronecker, Matrix.kronecker_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have h := congrArg (fun M : Matrix Wire Wire ℂ => M (ab, d) (ab', d'))
    (conjugate_tester_rhs g C)
  simp only [signConjugate, Matrix.kronecker, Matrix.kronecker_apply] at h
  linear_combination (1 / 4 : ℂ) * h

private theorem average_causal {S : Matrix Wire Wire ℂ}
    {sigma : Matrix (Fin 2) (Fin 2) ℂ} (h : Causal S sigma) :
    Causal (averageWire S) (averageB sigma) := by
  refine ⟨phaseAverage_pos _ phaseWire_star h.1,
    phaseAverage_pos _ (fun g => bitSign_star g.2) h.2.1, ?_, ?_⟩
  · have heq : Matrix.trace (averageB sigma) = Matrix.trace sigma := by
      change (∑ i : Fin 2, averageB sigma i i) = ∑ i : Fin 2, sigma i i
      apply Finset.sum_congr rfl
      intro i _
      exact average_diagonal _ (fun g => bitSign_sq g.2) sigma i
    exact heq.trans h.2.2.1
  · rw [average_partialRight, h.2.2.2, average_causal_rhs]

private theorem average_tester {C : Matrix AB AB ℂ} {E : Matrix Wire Wire ℂ}
    (h : Tester C E) : Tester (averageAB C) (averageWire E) := by
  refine ⟨phaseAverage_pos _ phaseAB_star h.1, ?_,
    phaseAverage_pos _ phaseWire_star h.2.2.1, ?_⟩
  · rw [average_partialLeft, h.2.1]
    have heq (g : Phase) : signConjugate (phaseB g) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      signConjugate_one _ (bitSign_sq g.2)
    ext i j
    rw [averageB, average_apply]
    have heqentry (g : Phase) :
        phaseB g i * (1 : Matrix (Fin 2) (Fin 2) ℂ) i j * phaseB g j =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) (heq g)
    simp_rw [heqentry]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
    ring
  · rw [← average_tester_rhs]
    change (phaseAverage phaseWire (Matrix.kronecker C (1 : Matrix (Fin 3) (Fin 3) ℂ)) -
      phaseAverage phaseWire E).PosSemidef
    rw [← average_sub]
    exact phaseAverage_pos _ phaseWire_star h.2.2.2

private theorem averageAB_diagonal (C : Matrix AB AB ℂ) : (averageAB C).IsDiag := by
  intro i j hij
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  rw [averageAB, average_apply]
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp_all [Fintype.sum_prod_type, Fin.sum_univ_two, phaseAB, bitSign]

private theorem averageB_diagonal (sigma : Matrix (Fin 2) (Fin 2) ℂ) :
    (averageB sigma).IsDiag := by
  intro i j hij
  rw [averageB, average_apply]
  fin_cases i <;> fin_cases j <;>
    simp_all [Fintype.sum_prod_type, Fin.sum_univ_two, phaseB, bitSign]

/-- The character of each physical address for the four joint signs. -/
def charge (i : Wire) : AB :=
  if i.2 = 0 then i.1
  else if i.2 = 1 then (if i.1.1 = 0 then 1 else 0, i.1.2)
  else (if i.1.1 = 0 then 1 else 0, if i.1.2 = 0 then 1 else 0)

private theorem phaseWire_charge (g : Phase) (i : Wire) :
    phaseWire g i = phaseAB g (charge i) := by
  rcases g with ⟨a, b⟩
  rcases i with ⟨⟨i, j⟩, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> fin_cases d <;>
    norm_num [phaseWire, phaseAB, phaseD, bitSign, charge]

private theorem character_sum (i j : AB) :
    (∑ g : Phase, phaseAB g i * phaseAB g j) = if i = j then 4 else 0 := by
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, phaseAB, bitSign]

private theorem averageWire_mask (S : Matrix Wire Wire ℂ) (i j : Wire) :
    averageWire S i j = if charge i = charge j then S i j else 0 := by
  rw [averageWire, average_apply]
  simp_rw [phaseWire_charge]
  have heq : (∑ g : Phase, phaseAB g (charge i) * S i j * phaseAB g (charge j)) =
      (∑ g : Phase, phaseAB g (charge i) * phaseAB g (charge j)) * S i j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [heq, character_sum]
  split_ifs <;> ring

private theorem mainSupport_charge (i : Wire) : MainSupport i ↔ charge i = (0, 0) := by
  rcases i with ⟨⟨a, b⟩, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> norm_num [MainSupport, charge] <;> decide

private theorem averageWire_main_block (S : Matrix Wire Wire ℂ) (i j : Wire)
    (hi : MainSupport i) (hj : ¬ MainSupport j) : averageWire S i j = 0 := by
  rw [averageWire_mask]
  have hne : charge i ≠ charge j := by
    rw [(mainSupport_charge i).mp hi]
    exact fun h => hj ((mainSupport_charge j).mpr h.symm)
  exact if_neg hne

private theorem candidateVector_fixed (eps : ℝ) (g : Phase) (i : Wire) :
    phaseWire g i * candidateVector eps i = candidateVector eps i := by
  unfold candidateVector
  split_ifs with hx hy hz
  · subst i
    simp [phaseWire, phaseAB, phaseD, bitSign]
  · subst i
    rcases g with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [phaseWire, phaseAB, phaseD, bitSign]
  · subst i
    rcases g with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp [phaseWire, phaseAB, phaseD, bitSign]
  · simp

private theorem candidate_fixed (eps : ℝ) (g : Phase) :
    signConjugate (phaseWire g) (candidate eps) = candidate eps := by
  ext i j
  change phaseWire g i * (candidateVector eps i * star (candidateVector eps j)) *
      phaseWire g j = candidateVector eps i * star (candidateVector eps j)
  have hj : star (candidateVector eps j) * phaseWire g j = star (candidateVector eps j) := by
    have h := congrArg star (candidateVector_fixed eps g j)
    simpa only [star_mul, phaseWire_star] using h
  calc
    _ = (phaseWire g i * candidateVector eps i) *
      (star (candidateVector eps j) * phaseWire g j) := by ring
    _ = _ := by rw [candidateVector_fixed, hj]

private theorem trace_conjugate_swap {n : Type*} [Fintype n]
    (u : n → ℂ) (X E : Matrix n n ℂ) :
    Matrix.trace (X * signConjugate u E) = Matrix.trace (signConjugate u X * E) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, signConjugate]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem response_average_right (X E : Matrix Wire Wire ℂ) :
    response X (averageWire E) =
      (1 / 4 : ℝ) * ∑ g : Phase, response X (signConjugate (phaseWire g) E) := by
  simp [response, averageWire, phaseAverage, Matrix.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum, Complex.real_smul]

private theorem response_average_left (X E : Matrix Wire Wire ℂ) :
    response (averageWire X) E =
      (1 / 4 : ℝ) * ∑ g : Phase, response X (signConjugate (phaseWire g) E) := by
  simp [response, averageWire, phaseAverage, Matrix.sum_mul,
    Matrix.trace_smul, Matrix.trace_sum, Complex.real_smul, ← trace_conjugate_swap]

private theorem average_invariant_response (X E : Matrix Wire Wire ℂ)
    (hX : ∀ g, signConjugate (phaseWire g) X = X) :
    response X (averageWire E) = response X E := by
  rw [response_average_right]
  have heq (g : Phase) : response X (signConjugate (phaseWire g) E) = response X E := by
    unfold response
    rw [trace_conjugate_swap, hX]
  simp_rw [heq]
  simp

private theorem average_fixed (X : Matrix Wire Wire ℂ)
    (hX : ∀ g, signConjugate (phaseWire g) X = X) : averageWire X = X := by
  ext i j
  rw [averageWire, average_apply]
  have heq (g : Phase) : phaseWire g i * X i j * phaseWire g j = X i j :=
    congrArg (fun M : Matrix Wire Wire ℂ => M i j) (hX g)
  simp_rw [heq]
  simp

private theorem average_error_bound (eps : ℝ) (S : Matrix Wire Wire ℂ) (b : ℝ)
    (h : ErrorBound (candidate eps - S) b) :
    ErrorBound (candidate eps - averageWire S) b := by
  intro C E hCE
  have havg : candidate eps - averageWire S = averageWire (candidate eps - S) := by
    change candidate eps - phaseAverage phaseWire S = phaseAverage phaseWire (candidate eps - S)
    rw [average_sub]
    exact congrArg (fun M : Matrix Wire Wire ℂ => M - phaseAverage phaseWire S)
      (average_fixed _ (candidate_fixed eps)).symm
  rw [havg, response_average_left, abs_mul]
  have hsum : |∑ g : Phase, response (candidate eps - S)
      (signConjugate (phaseWire g) E)| ≤ ∑ g : Phase, b := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun g _ => h _ _ (conjugate_tester g hCE)))
  calc
    |(1 / 4 : ℝ)| * |∑ g : Phase, response (candidate eps - S)
        (signConjugate (phaseWire g) E)| ≤ |(1 / 4 : ℝ)| * ∑ _g : Phase, b :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = b := by simp

/-- One coupled phase average keeps all original constraints, the same marginal diagonal,
isolates the candidate's three-dimensional block, and transports every tester error bound.
For invariant differences it also preserves each averaged tester response exactly. -/
theorem joint_phase_reduction (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix AB AB ℂ) (E : Matrix Wire Wire ℂ)
    (hS : Causal S sigma) (hCE : Tester C E) :
    Causal (averageWire S) (averageB sigma) ∧
      (∀ i, averageB sigma i i = sigma i i) ∧
      (averageB sigma).IsDiag ∧
      Tester (averageAB C) (averageWire E) ∧
      (averageAB C).IsDiag ∧
      (∀ i j, MainSupport i → ¬ MainSupport j → averageWire S i j = 0) ∧
      response (candidate eps) (averageWire E) = response (candidate eps) E ∧
      (∀ X : Matrix Wire Wire ℂ, (∀ g, signConjugate (phaseWire g) X = X) →
        response X (averageWire E) = response X E) ∧
      (∀ b : ℝ, ErrorBound (candidate eps - S) b →
        ErrorBound (candidate eps - averageWire S) b) := by
  refine ⟨average_causal hS, ?_, averageB_diagonal sigma, average_tester hCE,
    averageAB_diagonal C, averageWire_main_block S,
    average_invariant_response _ _ (candidate_fixed eps), ?_, average_error_bound eps S⟩
  · intro i
    exact average_diagonal _ (fun g => bitSign_sq g.2) sigma i
  · intro X hX
    exact average_invariant_response X E hX

/-- The three candidate addresses, indexed by their distinct last-port coordinates. -/
def mainAddress (k : Fin 3) : Wire :=
  if k = 0 then ((0, 0), 0) else if k = 1 then ((1, 0), 1) else ((1, 1), 2)

def blockEmbedding : Matrix Wire (Fin 3) ℂ := by
  classical
  exact fun i k => if MainSupport i then if i.2 = k then 1 else 0 else 0

def embedBlock (P : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Wire Wire ℂ :=
  blockEmbedding * P * blockEmbeddingᴴ

def complementWeight (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) (i : Wire) : ℝ :=
  if i = ((0, 0), 1) then 1 - p - (P 0 0).re
  else if i = ((1, 0), 0) then 1 - p - (P 1 1).re
  else if i = ((0, 1), 0) then p
  else if i = ((1, 1), 0) then p - (P 2 2).re else 0

/-- Complete an arbitrary positive three-dimensional principal block with four diagonal masses. -/
def causalCompletion (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Wire Wire ℂ :=
  embedBlock P + Matrix.diagonal (fun i => (complementWeight p P i : ℂ))

def diagonalMarginal (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun b => if b = 0 then (1 - p : ℝ) else p : Fin 2 → ℝ) |>.map
    (fun r : ℝ => (r : ℂ))

private theorem embedBlock_entry (P : Matrix (Fin 3) (Fin 3) ℂ) (i j : Wire) :
    embedBlock P i j = if MainSupport i then if MainSupport j then P i.2 j.2 else 0
      else 0 := by
  classical
  by_cases hi : MainSupport i <;> by_cases hj : MainSupport j <;>
    simp [embedBlock, Matrix.mul_apply, blockEmbedding, Matrix.conjTranspose_apply,
      hi, hj, eq_comm]

private theorem complementWeight_nonneg (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hp : 0 ≤ p) (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p)
    (h2 : (P 2 2).re ≤ p) (i : Wire) : 0 ≤ complementWeight p P i := by
  unfold complementWeight
  split_ifs <;> linarith

private theorem diagonalMarginal_pos (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (diagonalMarginal p).PosSemidef := by
  have heq : diagonalMarginal p =
      Matrix.diagonal (fun b : Fin 2 => ((if b = 0 then 1 - p else p : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonalMarginal, Matrix.diagonal, h]
  rw [heq]
  apply Matrix.PosSemidef.diagonal
  intro b
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Complex.ofReal_re]
    split_ifs <;> linarith
  · simp

private theorem psd_diagonal_real {P : Matrix (Fin 3) (Fin 3) ℂ} (hP : P.PosSemidef)
    (k : Fin 3) : P k k = ((P k k).re : ℂ) :=
  Complex.eq_re_of_ofReal_le (r := 0) hP.diag_nonneg

private theorem completion_partialTrace (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P.PosSemidef) :
    partialTraceRight (causalCompletion p P) =
      Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (diagonalMarginal p) := by
  have h0 := psd_diagonal_real hP 0
  have h1 := psd_diagonal_real hP 1
  have h2 := psd_diagonal_real hP 2
  ext i j
  rcases i with ⟨a, b⟩
  rcases j with ⟨a', b'⟩
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [partialTraceRight, causalCompletion, embedBlock_entry, complementWeight,
      MainSupport, diagonalMarginal, Matrix.kronecker, Matrix.kronecker_apply,
      Matrix.diagonal, Fin.sum_univ_three] <;>
      first | (solve | linear_combination h0) | (solve | linear_combination h1) |
        (solve | linear_combination h2)

private theorem completion_compression (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ) :
    (causalCompletion p P).submatrix mainAddress mainAddress = P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.submatrix_apply, causalCompletion, embedBlock_entry, complementWeight,
      MainSupport, mainAddress, Matrix.diagonal]

/-- Every positive principal block satisfying the three marginal budgets has an actual causal
completion with that same marginal and exactly the original complex principal block. -/
theorem compressed_block_causal_lift (p : ℝ) (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hP : P.PosSemidef)
    (h0 : (P 0 0).re ≤ 1 - p) (h1 : (P 1 1).re ≤ 1 - p) (h2 : (P 2 2).re ≤ p) :
    Causal (causalCompletion p P) (diagonalMarginal p) ∧
      (causalCompletion p P).submatrix mainAddress mainAddress = P ∧
      diagonalMarginal p 1 1 = (p : ℂ) := by
  refine ⟨⟨?_, diagonalMarginal_pos p hp hp1, ?_, completion_partialTrace p P hP⟩,
    completion_compression p P, ?_⟩
  · exact (hP.mul_mul_conjTranspose_same blockEmbedding).add
      (Matrix.PosSemidef.diagonal (fun i => Complex.nonneg_iff.mpr
        ⟨by simpa using complementWeight_nonneg p P hp h0 h1 h2 i, by simp⟩))
  · simp [diagonalMarginal, Matrix.trace, Fin.sum_univ_two]
  · simp [diagonalMarginal]

end D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
