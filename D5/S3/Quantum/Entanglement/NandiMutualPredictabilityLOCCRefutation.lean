/- GID: D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claim; result=D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result; claim=D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claim
   digest: A local measure-and-reset raises the MUB correlation I2 from 1 to 3/2, refuting its LOCC monotonicity. -/

/-
proof_shape (definitions): Setting, prodVec, I2, I2max, branch, claimFixed, claimOptimized,
  claim; private rho0, rhoP, v00, v10, standardSetting.
proof_shape (theorems, same-delivery helpers inlined): result is bind-only — the explicit
  d = 2 state, instrument and computational/Hadamard setting are evaluated from unitarity,
  finite-sum expansion and complex arithmetic, and the supremum is compared through
  `ciSup_le` / `le_ciSup`. Every private theorem is bind-only and is used on the proof path of
  result (CLAUDE.md §3.2, consumed helpers): col_norm_sq, row_norm_sq, rho0_mulVec,
  rho0_expect, i2_rho0, hadamard_eq, half_sqrt_two_sq, hadamard_unitary, hadamard_mub,
  branch_first, branch_second, rhoP_mulVec, rhoP_expect, i2_standard_branch,
  i2_standard_rhoP, rho0_vec, rho0_state, instrument_complete, not_claimFixed,
  normSq_entry_le_one, i2_rhoP_le_two, i2max_rho0, i2max_rhoP_ge, not_claimOptimized.
escape_witness: none.
admission_basis: open-problem-resolution (#13804; Refuted)
Direct frozen dependencies:
  D5/S3/Weil/ZetaLinear/VonNeumann.RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
    statement_id: sha256:10d84d7748c4e7f110f57a63c8faf31b2da6ecba24f5cdf67b5b36281d5a0757
    module statement_id: sha256:5acab7f530ae9cd1e0a27ec64ef7ae56e595b85c7b1f821c8cb42f81b0a9aa7c
    used by col_norm_sq and row_norm_sq.
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.hadamard
    statement_id: sha256:d28d3fee83d154e42cf2331eba2ffeb942edeed66e1ff8e9221f10b0b991ddc4
  D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.s2
    statement_id: sha256:ef4ae1e2fc1bec9bf605d06598d58ce332db9ba1a90facd16a497c70ae0336f7
    module statement_id: sha256:69ba78ef64ec12e1f6906215aa29868687bd77d44554d8e877fbf0c6759edfd4
    both used by hadamard_eq.
  Mathlib entry_norm_bound_of_unitary, used by normSq_entry_le_one.
-/

import D5.S3.Weil.ZetaLinear.VonNeumann
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation

open Matrix
open D5.S3.Quantum.FiniteDimensional D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

/-- The Hadamard matrix of the frozen stabilizer module. -/
local notation "hadamard₂" => D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard
open scoped ComplexOrder Kronecker

structure Setting (d : ℕ) where
  A : Matrix (Fin d) (Fin d) ℂ
  A' : Matrix (Fin d) (Fin d) ℂ
  B : Matrix (Fin d) (Fin d) ℂ
  B' : Matrix (Fin d) (Fin d) ℂ
  hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ
  hA' : A' ∈ Matrix.unitaryGroup (Fin d) ℂ
  hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ
  hB' : B' ∈ Matrix.unitaryGroup (Fin d) ℂ
  mubA : ∀ i j, Complex.normSq ((Aᴴ * A') i j) = 1 / d
  mubB : ∀ i j, Complex.normSq ((Bᴴ * B') i j) = 1 / d

def prodVec {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : Fin d × Fin d → ℂ :=
  fun x => X x.1 i * Y x.2 i

def I2 {d : ℕ} (s : Setting d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (∑ i, (star (prodVec s.A s.B i) ⬝ᵥ (ρ *ᵥ prodVec s.A s.B i)).re) +
  (∑ i, (star (prodVec s.A' s.B' i) ⬝ᵥ (ρ *ᵥ prodVec s.A' s.B' i)).re)

noncomputable def I2max {d : ℕ} (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ := ⨆ s : Setting d, I2 s ρ

def branch {d : ℕ} (E : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.kronecker E 1 * ρ * (Matrix.kronecker E 1)ᴴ

def claimFixed : Prop := ∀ (d : ℕ), 2 ≤ d → ∀ (s : Setting d) (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (E₁ E₂ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef → ρ.trace = 1 → E₁ᴴ * E₁ + E₂ᴴ * E₂ = 1 →
    I2 s (branch E₁ ρ) + I2 s (branch E₂ ρ) ≤ I2 s ρ

def claimOptimized : Prop := ∀ (d : ℕ), 2 ≤ d → ∀ (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (E₁ E₂ : Matrix (Fin d) (Fin d) ℂ), ρ.PosSemidef → ρ.trace = 1 → E₁ᴴ * E₁ + E₂ᴴ * E₂ = 1 →
    I2max (branch E₁ ρ) + I2max (branch E₂ ρ) ≤ I2max ρ

def claim : Prop := claimFixed ∨ claimOptimized

private noncomputable def rho0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2 = 0 ∧ y.2 = 0 then (1 / 2 : ℂ) else 0

private lemma col_norm_sq (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (i : Fin 2) : ∑ a, Complex.normSq (X a i) = 1 := by
  have h := (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hX)).2.2 i
  simpa [RHLinalg.normSqMatrix, Complex.normSq_eq_norm_sq] using h

private lemma row_norm_sq (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (i : Fin 2) : ∑ a, Complex.normSq (X i a) = 1 := by
  have h := (mem_doublyStochastic_iff_sum.mp
    (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hX)).2.1 i
  simpa [RHLinalg.normSqMatrix, Complex.normSq_eq_norm_sq] using h

private lemma rho0_mulVec (X Y : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    rho0 *ᵥ prodVec X Y i = fun x => if x.2 = 0 then (1 / 2 : ℂ) * prodVec X Y i (x.1, 0) else 0 := by
  funext x
  classical
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, rho0, prodVec, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma rho0_expect (X Y : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (star (prodVec X Y i) ⬝ᵥ (rho0 *ᵥ prodVec X Y i)).re =
      (1 / 2 : ℝ) * (∑ a, Complex.normSq (X a i)) * Complex.normSq (Y 0 i) := by
  rw [rho0_mulVec]
  fin_cases i <;>
    simp [dotProduct, prodVec, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

private lemma i2_rho0 (s : Setting 2) : I2 s rho0 = 1 := by
  rcases s with ⟨A, A', B, B', hA, hA', hB, hB', hmA, hmB⟩
  simp only [I2, rho0_expect]
  simp only [Fin.sum_univ_two]
  have hA0 := col_norm_sq A hA 0
  have hA1 := col_norm_sq A hA 1
  have hA'0 := col_norm_sq A' hA' 0
  have hA'1 := col_norm_sq A' hA' 1
  norm_num [Fin.sum_univ_two] at hA0 hA1 hA'0 hA'1
  rw [hA0, hA1, hA'0, hA'1]
  have hrB := row_norm_sq B hB 0
  have hrB' := row_norm_sq B' hB' 0
  norm_num [Fin.sum_univ_two] at hrB hrB' ⊢
  linarith

private lemma hadamard_eq :
    hadamard₂ = !![((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 2 / 2 : ℝ) : ℂ);
      ((Real.sqrt 2 / 2 : ℝ) : ℂ), -((Real.sqrt 2 / 2 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2, pauliMatrix, qubitX, qubitZ]

private lemma half_sqrt_two_sq : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma hadamard_unitary : hadamard₂ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', hadamard_eq, Matrix.star_eq_conjTranspose]
  have hq := half_sqrt_two_sq
  generalize Real.sqrt 2 / 2 = q at hq ⊢
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    apply Complex.ext <;> simp [Matrix.mul_apply]
    all_goals nlinarith [hq]

private lemma hadamard_mub :
    ∀ i j, Complex.normSq (((1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * hadamard₂) i j) = 1 / 2 := by
  intro i j
  rw [hadamard_eq]
  have hq := half_sqrt_two_sq
  generalize Real.sqrt 2 / 2 = q at hq ⊢
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Complex.normSq_ofReal]
    ; nlinarith [hq]

private noncomputable def standardSetting : Setting 2 :=
  { A := 1, A' := hadamard₂, B := 1, B' := hadamard₂
    hA := by simp
    hA' := hadamard_unitary
    hB := by simp
    hB' := hadamard_unitary
    mubA := hadamard_mub
    mubB := hadamard_mub }

private noncomputable def rhoP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x = (0, 0) ∧ y = (0, 0) then (1 / 2 : ℂ) else 0

private lemma branch_first : branch (Matrix.single 0 0 1) rho0 = rhoP := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [branch, rho0, rhoP, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fintype.sum_prod_type]

private lemma branch_second : branch (Matrix.single 0 1 1) rho0 = rhoP := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [branch, rho0, rhoP, Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fintype.sum_prod_type]

private lemma rhoP_mulVec (X Y : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    rhoP *ᵥ prodVec X Y i = fun x => if x = (0, 0) then (1 / 2 : ℂ) * prodVec X Y i (0, 0) else 0 := by
  funext x
  rcases x with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mulVec, dotProduct, rhoP, prodVec]

private lemma rhoP_expect (X Y : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (star (prodVec X Y i) ⬝ᵥ (rhoP *ᵥ prodVec X Y i)).re =
      (1 / 2 : ℝ) * Complex.normSq (X 0 i) * Complex.normSq (Y 0 i) := by
  rw [rhoP_mulVec]
  fin_cases i <;>
    simp [dotProduct, prodVec,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  <;> ring

private lemma i2_standard_branch : I2 standardSetting (branch (Matrix.single 0 0 1) rho0) = 3 / 4 := by
  rw [branch_first]
  simp only [I2, rhoP_expect, Fin.sum_univ_two]
  norm_num [standardSetting, hadamard_eq, Matrix.one_apply,
    Complex.normSq_ofReal, half_sqrt_two_sq]

private lemma i2_standard_rhoP : I2 standardSetting rhoP = 3 / 4 := by
  rw [← branch_first]
  exact i2_standard_branch

private noncomputable def v00 : Fin 2 × Fin 2 → ℂ := fun x => if x = (0, 0) then 1 else 0

private noncomputable def v10 : Fin 2 × Fin 2 → ℂ := fun x => if x = (1, 0) then 1 else 0

private lemma rho0_vec : rho0 =
    (1 / 2 : ℂ) • Matrix.vecMulVec v00 (star v00) +
      (1 / 2 : ℂ) • Matrix.vecMulVec v10 (star v10) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [rho0, v00, v10, Matrix.vecMulVec, Matrix.smul_apply, Prod.ext_iff]

private lemma rho0_state : rho0.PosSemidef ∧ rho0.trace = 1 := by
  rw [rho0_vec]
  constructor
  · exact ((posSemidef_vecMulVec_self_star v00).smul (by norm_num [Complex.le_def])).add
      ((posSemidef_vecMulVec_self_star v10).smul (by norm_num [Complex.le_def]))
  · norm_num [Matrix.trace, Matrix.diag, v00, v10, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.vecMulVec_apply]

private lemma instrument_complete :
    (Matrix.single 0 0 1)ᴴ * Matrix.single 0 0 1 +
      (Matrix.single 0 1 1)ᴴ * Matrix.single 0 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.single, Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma not_claimFixed : ¬ claimFixed := by
  intro h
  have hineq := h 2 (by decide) standardSetting rho0 (Matrix.single 0 0 1) (Matrix.single 0 1 1)
    rho0_state.1 rho0_state.2 instrument_complete
  rw [branch_first, branch_second, i2_standard_rhoP, i2_rho0] at hineq
  norm_num at hineq

private lemma normSq_entry_le_one (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    Complex.normSq (X i j) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [entry_norm_bound_of_unitary hX i j, norm_nonneg (X i j)]

private lemma i2_rhoP_le_two (s : Setting 2) : I2 s rhoP ≤ 2 := by
  simp only [I2, rhoP_expect, Fin.sum_univ_two]
  have key (X Y : Matrix (Fin 2) (Fin 2) ℂ) (hX : X ∈ Matrix.unitaryGroup (Fin 2) ℂ)
      (hY : Y ∈ Matrix.unitaryGroup (Fin 2) ℂ) (j : Fin 2) :
      (1 / 2 : ℝ) * Complex.normSq (X 0 j) * Complex.normSq (Y 0 j) ≤ 1 / 2 := by
    have h1 := normSq_entry_le_one X hX 0 j
    have h2 := normSq_entry_le_one Y hY 0 j
    nlinarith [Complex.normSq_nonneg (X 0 j), Complex.normSq_nonneg (Y 0 j),
      mul_le_one₀ h1 (Complex.normSq_nonneg _) h2]
  linarith [key s.A s.B s.hA s.hB 0, key s.A s.B s.hA s.hB 1,
    key s.A' s.B' s.hA' s.hB' 0, key s.A' s.B' s.hA' s.hB' 1]

private lemma i2max_rho0 : I2max rho0 = 1 := by
  letI : Nonempty (Setting 2) := ⟨standardSetting⟩
  change (⨆ s : Setting 2, I2 s rho0) = 1
  apply le_antisymm
  · apply ciSup_le
    intro s
    simpa [i2_rho0]
  · have hbdd : BddAbove (Set.range (fun s : Setting 2 => I2 s rho0)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨s, rfl⟩
      simpa [i2_rho0]
    have hle := le_ciSup hbdd standardSetting
    rw [i2_rho0] at hle
    exact hle

private lemma i2max_rhoP_ge : (3 / 4 : ℝ) ≤ I2max rhoP := by
  letI : Nonempty (Setting 2) := ⟨standardSetting⟩
  change (3 / 4 : ℝ) ≤ ⨆ s : Setting 2, I2 s rhoP
  have hbdd : BddAbove (Set.range (fun s : Setting 2 => I2 s rhoP)) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact i2_rhoP_le_two s
  apply le_ciSup_of_le hbdd standardSetting
  rw [i2_standard_rhoP]

private lemma not_claimOptimized : ¬ claimOptimized := by
  intro h
  have hineq := h 2 (by decide) rho0 (Matrix.single 0 0 1) (Matrix.single 0 1 1)
    rho0_state.1 rho0_state.2 instrument_complete
  rw [branch_first, branch_second, i2max_rho0] at hineq
  nlinarith [i2max_rhoP_ge]

theorem result : ¬ claim := by
  intro h
  rcases h with hfixed | hoptimized
  · exact not_claimFixed hfixed
  · exact not_claimOptimized hoptimized

end D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
