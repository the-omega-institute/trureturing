/- GID: D5/S3/QuantumChannels/JordanCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/JordanCompatibilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim; result=D5/S3/QuantumChannels/JordanCompatibilityRefutation.result; claim=D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim
   digest: Compatible channels in dimension four need not be Jordan compatible. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

set_option linter.style.longLine false

open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

noncomputable section
namespace D5.S3.QuantumChannels.JordanCompatibilityRefutation

abbrev Mat (ι : Type*) := Matrix ι ι ℂ
abbrev Map (ι κ : Type*) := MatrixMap ι κ ℂ

def IsTP {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Φ : Map ι κ) : Prop :=
  ∀ R, Matrix.trace (Φ R) = Matrix.trace R

def IsCPTP {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Φ : Map ι κ) : Prop :=
  MatrixMap.IsCompletelyPositive Φ ∧ IsTP Φ

def J {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Φ : Map ι κ) : Mat (ι × κ) :=
  Matrix.reindex (Equiv.prodComm κ ι) (Equiv.prodComm κ ι)
    (MatrixMap.choi_matrix Φ)

def ptrRight {ι κ : Type*} [Fintype κ]
    (T : Mat (ι × κ)) : Mat ι :=
  fun a b => ∑ k : κ, T (a, k) (b, k)

def ptrLeft {ι κ : Type*} [Fintype ι]
    (T : Mat (ι × κ)) : Mat κ :=
  fun a b => ∑ i : ι, T (i, a) (i, b)

def traceX1 {d : ℕ} (A : Mat (Fin d × (Fin d × Fin d))) :
    Mat (Fin d × Fin d) :=
  fun p q => ∑ r : Fin d, A (p.1, (r, p.2)) (q.1, (r, q.2))

def traceX2 {d : ℕ} (A : Mat (Fin d × (Fin d × Fin d))) :
    Mat (Fin d × Fin d) :=
  fun p q => ∑ r : Fin d, A (p.1, (p.2, r)) (q.1, (q.2, r))

def jordanAction {d : ℕ} (Φ Ψ : Map (Fin d) (Fin d))
    (A : Mat (Fin d × (Fin d × Fin d))) :
    Mat (Fin d × (Fin d × Fin d)) :=
  MatrixMap.kron (LinearMap.id : Map (Fin d) (Fin d)) (MatrixMap.kron Φ Ψ) A

def Compatible {d : ℕ} (Φ Ψ : Map (Fin d) (Fin d)) : Prop :=
  ∃ Γ : Map (Fin d) (Fin d × Fin d), IsCPTP Γ ∧
    (∀ R, ptrRight (Γ R) = Φ R) ∧ (∀ R, ptrLeft (Γ R) = Ψ R)

def JordanCompatible {d : ℕ} (Φ Ψ : Map (Fin d) (Fin d)) : Prop :=
  ∃ A : Mat (Fin d × (Fin d × Fin d)), A.IsHermitian ∧
    traceX1 A = J (LinearMap.id : Map (Fin d) (Fin d)) ∧
    traceX2 A = J (LinearMap.id : Map (Fin d) (Fin d)) ∧
    (jordanAction Φ Ψ A).PosSemidef

def claim : Prop :=
  ∀ (d : ℕ) (Φ Ψ : Map (Fin d) (Fin d)),
    IsCPTP Φ → IsCPTP Ψ → Compatible Φ Ψ → JordanCompatible Φ Ψ

variable {ι κ η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype η] [DecidableEq η]

private theorem J_apply (Φ : Map ι κ) (a b : ι) (i j : κ) :
    J Φ (a, i) (b, j) = Φ (Matrix.single a b 1) i j := rfl

private theorem cp_iff_J_psd (Φ : Map ι κ) :
    MatrixMap.IsCompletelyPositive Φ ↔ (J Φ).PosSemidef := by
  rw [MatrixMap.choi_PSD_iff_CP_map]
  constructor
  · intro h
    exact h.submatrix Prod.swap
  · intro h
    exact h.submatrix Prod.swap

private def measurePrepare (L : κ → Mat ι) : Map ι κ :=
  MatrixMap.of_choi_matrix
    (fun p q => if p.1 = q.1 then L p.1 q.2 p.2 else 0)

omit [DecidableEq ι] [Fintype κ] in
private theorem measurePrepare_apply (L : κ → Mat ι) (R : Mat ι) :
    measurePrepare L R = Matrix.diagonal (fun i => Matrix.trace (L i * R)) := by
  ext i j
  change (∑ a, ∑ b, R a b * (if i = j then L i b a else 0)) =
    (if i = j then Matrix.trace (L i * R) else 0)
  split_ifs with hij
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  · simp

omit [Fintype κ] in
private theorem measurePrepare_single (L : κ → Mat ι) (a b : ι) (i j : κ) :
    measurePrepare L (Matrix.single a b 1) i j =
      if i = j then L i b a else 0 := by
  rw [measurePrepare_apply]
  simp [Matrix.diagonal_apply, Matrix.trace_mul_single]

private theorem J_measurePrepare (L : κ → Mat ι) :
    J (measurePrepare L) = ∑ i : κ,
      Matrix.kroneckerMap (· * ·) (L i).transpose (Matrix.single i i (1 : ℂ)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [J_apply, measurePrepare_single]
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single, Matrix.of_apply, Matrix.transpose_apply,
    mul_ite, mul_one, mul_zero]
  by_cases hij : i = j
  · subst j
    simp
  · simp only [if_neg hij]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    exact fun hc => hij (hc.1.symm.trans hc.2)

private theorem measurePrepare_cp (L : κ → Mat ι)
    (hL : ∀ i, (L i).PosSemidef) :
    MatrixMap.IsCompletelyPositive (measurePrepare L) := by
  rw [cp_iff_J_psd, J_measurePrepare]
  apply Matrix.posSemidef_sum
  intro i _
  apply (hL i).transpose.kronecker
  have hd : (Matrix.diagonal (fun j : κ => if j = i then (1 : ℂ) else 0)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => by split_ifs <;> norm_num)
  have heq : Matrix.single i i (1 : ℂ) =
      Matrix.diagonal (fun j : κ => if j = i then (1 : ℂ) else 0) := by
    ext a b
    simp only [Matrix.single, Matrix.diagonal_apply]
    split_ifs <;> simp_all [eq_comm]
  rw [heq]
  exact hd

private theorem measurePrepare_tp (L : κ → Mat ι) (hL : ∑ i : κ, L i = 1) :
    IsTP (measurePrepare L) := by
  intro R
  rw [measurePrepare_apply, Matrix.trace_diagonal]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, hL, Matrix.one_mul]

omit [DecidableEq ι] in
private theorem measurePrepare_marginals (L : (κ × η) → Mat ι) (R : Mat ι) :
    ptrRight (measurePrepare L R) = measurePrepare (fun i => ∑ j : η, L (i, j)) R ∧
    ptrLeft (measurePrepare L R) = measurePrepare (fun j => ∑ i : κ, L (i, j)) R := by
  simp only [measurePrepare_apply]
  constructor <;> ext a b
  · unfold ptrRight
    simp [Matrix.diagonal_apply, Matrix.sum_mul, Matrix.trace_sum]
  · unfold ptrLeft
    simp [Matrix.diagonal_apply, Matrix.sum_mul, Matrix.trace_sum]

private abbrev M4 := Mat (Fin 4)
private abbrev A4 := Mat (Fin 4 × (Fin 4 × Fin 4))

private def P : M4 :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
private def Q : M4 := Matrix.diagonal ![(1 : ℂ), 1, -1, -1]
private def S : Fin 4 → M4 := ![P, -P, Q, -Q]
private def E (i : Fin 4) : M4 := (1 / 4 : ℝ) • 1 + (1 / 5 : ℝ) • S i
private def F (i : Fin 4) : M4 := (1 / 4 : ℝ) • 1 + (3 / 16 : ℝ) • S i
private def Phi : Map (Fin 4) (Fin 4) := measurePrepare E
private def Psi : Map (Fin 4) (Fin 4) := measurePrepare F

private theorem pauli_facts :
    P.IsHermitian ∧ Q.IsHermitian ∧ P.transpose = P ∧ Q.transpose = Q ∧
    P * P = 1 ∧ Q * Q = 1 ∧ P * Q + Q * P = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change P.conjTranspose = P
    unfold P
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  · change Q.conjTranspose = Q
    unfold Q
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply]
  all_goals
    try unfold P
    try unfold Q
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.vecMul, dotProduct, Matrix.diagonal_apply]

private theorem S_facts (i : Fin 4) :
    (S i).IsHermitian ∧ (S i).transpose = S i ∧ S i * S i = 1 := by
  obtain ⟨hp, hq, hpt, hqt, hpp, hqq, _⟩ := pauli_facts
  fin_cases i
  · exact ⟨hp, hpt, hpp⟩
  · change (-P).IsHermitian ∧ (-P).transpose = -P ∧ (-P) * (-P) = 1
    exact ⟨hp.neg, by simp [hpt], by simp [hpp]⟩
  · exact ⟨hq, hqt, hqq⟩
  · change (-Q).IsHermitian ∧ (-Q).transpose = -Q ∧ (-Q) * (-Q) = 1
    exact ⟨hq.neg, by simp [hqt], by simp [hqq]⟩

private theorem effects_psd (i : Fin 4) : (E i).PosSemidef ∧ (F i).PosSemidef := by
  have hs := S_facts i
  have hg : ((1 + S i).conjTranspose * (1 + S i)) = (2 : ℝ) • (1 + S i) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hs.1.eq,
      add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hs.2.2]
    module
  have he : E i = (1 / 20 : ℝ) • 1 +
      (1 / 10 : ℝ) • ((1 + S i).conjTranspose * (1 + S i)) := by
    rw [hg]
    unfold E
    module
  have hf : F i = (1 / 16 : ℝ) • 1 +
      (3 / 32 : ℝ) • ((1 + S i).conjTranspose * (1 + S i)) := by
    rw [hg]
    unfold F
    module
  rw [he, hf]
  exact ⟨(Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 20)).add
      ((Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num)),
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 1 / 16)).add
      ((Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num))⟩

private theorem effects_transpose (i : Fin 4) :
    (E i).transpose = E i ∧ (F i).transpose = F i := by
  unfold E F
  simp [(S_facts i).2.1]

private theorem effect_halves :
    E 0 + E 1 = (1 / 2 : ℝ) • (1 : M4) ∧
    E 2 + E 3 = (1 / 2 : ℝ) • (1 : M4) ∧
    F 0 + F 1 = (1 / 2 : ℝ) • (1 : M4) ∧
    F 2 + F 3 = (1 / 2 : ℝ) • (1 : M4) := by
  dsimp [E, F, S]
  constructor
  · module
  constructor
  · module
  constructor <;> module

private theorem effects_sum : (∑ i : Fin 4, E i) = 1 ∧ (∑ i : Fin 4, F i) = 1 := by
  obtain ⟨he, he', hf, hf'⟩ := effect_halves
  simp only [Fin.sum_univ_four]
  constructor
  · rw [add_assoc (E 0 + E 1), he, he']
    module
  · rw [add_assoc (F 0 + F 1), hf, hf']
    module

private theorem channels_cptp : IsCPTP Phi ∧ IsCPTP Psi :=
  ⟨⟨measurePrepare_cp E (fun i => (effects_psd i).1), measurePrepare_tp E effects_sum.1⟩,
   ⟨measurePrepare_cp F (fun i => (effects_psd i).2), measurePrepare_tp F effects_sum.2⟩⟩

private def h (i j : Fin 4) : ℝ := 1 / 64 + (15 / 16) * (if i = j then 1 else 0)
private def jointEffects (p : Fin 4 × Fin 4) : M4 := h p.1 p.2 • E p.1
private def Gamma : Map (Fin 4) (Fin 4 × Fin 4) := measurePrepare jointEffects

private theorem h_nonneg (i j : Fin 4) : 0 ≤ h i j := by
  unfold h
  split_ifs <;> norm_num

private theorem h_row_sum (i : Fin 4) : ∑ j : Fin 4, h i j = 1 := by
  fin_cases i <;> norm_num [h, Fin.sum_univ_four, Fin.ext_iff]

private theorem h_mix (j : Fin 4) : ∑ i : Fin 4, h i j • E i = F j := by
  unfold h
  simp only [add_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
    mul_smul, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [effects_sum.1]
  unfold E F
  module

private theorem jointEffects_marginals :
    (∀ i : Fin 4, ∑ j : Fin 4, jointEffects (i, j) = E i) ∧
    (∀ j : Fin 4, ∑ i : Fin 4, jointEffects (i, j) = F j) := by
  constructor
  · intro i
    change (∑ j, h i j • E i) = E i
    rw [← Finset.sum_smul, h_row_sum, one_smul]
  · exact h_mix

private theorem gamma_cptp : IsCPTP Gamma := by
  constructor
  · apply measurePrepare_cp
    intro p
    exact (effects_psd p.1).1.smul (h_nonneg _ _)
  · apply measurePrepare_tp
    rw [Fintype.sum_prod_type]
    simp only [jointEffects_marginals.1]
    exact effects_sum.1

private theorem compatible_witness : Compatible Phi Psi := by
  refine ⟨Gamma, gamma_cptp, ?_, ?_⟩
  · intro R
    exact (measurePrepare_marginals jointEffects R).1.trans
      (congrArg (fun L => measurePrepare L R) (funext jointEffects_marginals.1))
  · intro R
    exact (measurePrepare_marginals jointEffects R).2.trans
      (congrArg (fun L => measurePrepare L R) (funext jointEffects_marginals.2))

end D5.S3.QuantumChannels.JordanCompatibilityRefutation
