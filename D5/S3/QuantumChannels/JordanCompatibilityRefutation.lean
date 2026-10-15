/- GID: D5/S3/QuantumChannels/JordanCompatibilityRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/JordanCompatibilityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim; result=D5/S3/QuantumChannels/JordanCompatibilityRefutation.result; claim=D5/S3/QuantumChannels/JordanCompatibilityRefutation.claim
   digest: Compatible channels in dimension four need not be Jordan compatible. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Recovery.KrausCompletion
import D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
import D5.S3.Weil.ZetaLinear.RankTrace

set_option linter.style.longLine false

open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.PureProgramQubitObstruction (IsChannel)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Recovery.KrausCompletion (rowReset row_reset_action)

noncomputable section
namespace D5.S3.QuantumChannels.JordanCompatibilityRefutation

abbrev Mat (ι : Type*) := Matrix ι ι ℂ
abbrev Map (ι κ : Type*) := MatrixMap ι κ ℂ

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
  ∃ Γ : Map (Fin d) (Fin d × Fin d), IsChannel (⇑Γ) ∧
    (∀ R, partialTraceRight (Γ R) = Φ R) ∧ (∀ R, partialTraceLeft (Γ R) = Ψ R)

def JordanCompatible {d : ℕ} (Φ Ψ : Map (Fin d) (Fin d)) : Prop :=
  ∃ A : Mat (Fin d × (Fin d × Fin d)), A.IsHermitian ∧
    traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin d) (Fin d)) ∧
    traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin d) (Fin d)) ∧
    (jordanAction Φ Ψ A).PosSemidef

def claim : Prop :=
  ∀ (d : ℕ) (Φ Ψ : Map (Fin d) (Fin d)),
    IsChannel (⇑Φ) → IsChannel (⇑Ψ) → Compatible Φ Ψ → JordanCompatible Φ Ψ

variable {ι κ η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Fintype η] [DecidableEq η]

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

private theorem measurePrepare_channel {α β γ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ]
    (L : β → Mat α) (V : β → γ → Mat α)
    (hL : ∀ i, ∑ t, (V i t).conjTranspose * V i t = L i)
    (hsum : ∑ i, L i = 1) : IsChannel (⇑(measurePrepare L)) := by
  let K (p : β × (γ × α)) : Matrix β α ℂ :=
    rowReset p.1 (V p.1 p.2.1) p.2.2
  have hgram : (∑ p, (K p).conjTranspose * K p) = 1 := by
    calc
      _ = ∑ i, ∑ t, ∑ r : α, (V i t).conjTranspose *
          ((Matrix.single i r (1 : ℂ)).conjTranspose * Matrix.single i r (1 : ℂ)) *
          V i t := by
        simp only [K, Fintype.sum_prod_type, rowReset,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ∑ i, ∑ t, (V i t).conjTranspose * V i t := by
        simp only [Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same,
          one_mul, ← Matrix.mul_sum, ← Matrix.sum_mul, Matrix.sum_single_one,
          Matrix.mul_one]
      _ = 1 := by simp only [hL, hsum]
  have haction (R : Mat α) : MatrixMap.of_kraus K K R = measurePrepare L R := by
    rw [measurePrepare_apply]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [K, Fintype.sum_prod_type, row_reset_action]
    simp_rw [Matrix.trace_mul_cycle (V _ _) R (V _ _).conjTranspose]
    simp only [← Finset.sum_smul, ← Matrix.trace_sum, ← Matrix.sum_mul, hL]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_single_eq_diagonal]
  let e := (Fintype.equivFin (β × (γ × α))).symm
  refine ⟨Fintype.card (β × (γ × α)), fun p => K (e p), ?_, ?_⟩
  · rw [e.sum_comp (fun p => (K p).conjTranspose * K p)]
    exact hgram
  · intro R
    rw [← haction]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk,
      AddHom.coe_mk]
    exact (e.sum_comp (fun p => K p * R * (K p).conjTranspose)).symm

omit [DecidableEq ι] in
private theorem sqrt_gram (c : ℝ) (hc : 0 ≤ c) (V : Mat ι) :
    (Real.sqrt c • V).conjTranspose * (Real.sqrt c • V) =
      c • (V.conjTranspose * V) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hc]

omit [DecidableEq ι] in
private theorem measurePrepare_marginals (L : (κ × η) → Mat ι) (R : Mat ι) :
    partialTraceRight (measurePrepare L R) = measurePrepare (fun i => ∑ j : η, L (i, j)) R ∧
    partialTraceLeft (measurePrepare L R) = measurePrepare (fun j => ∑ i : κ, L (i, j)) R := by
  simp only [measurePrepare_apply]
  constructor <;> ext a b
  · unfold partialTraceRight
    simp [Matrix.diagonal_apply, Matrix.sum_mul, Matrix.trace_sum]
  · unfold partialTraceLeft
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
  have hp : P.IsHermitian ∧ P * P = 1 := by
    simpa only [D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.XITable, P.eq_1]
      using D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.obs_herm_sq 4
  have hqeq : D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.obs 0 = Q := by
    rw [D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.ZITable, Q.eq_1]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]
  have hq : Q.IsHermitian ∧ Q * Q = 1 := by
    simpa only [hqeq]
      using D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.obs_herm_sq 0
  refine ⟨hp.1, hq.1, ?_, ?_, hp.2, hq.2, ?_⟩
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

private def eFactor (i : Fin 4) : M4 :=
  Real.sqrt (1 / 20) • ((2 : ℝ) • 1 + S i)

private def fFactor (i : Fin 4) : Fin 2 → M4 :=
  ![(1 / 4 : ℝ) • 1, Real.sqrt (3 / 32) • (1 + S i)]

private theorem effect_grams (i : Fin 4) :
    (eFactor i).conjTranspose * eFactor i = E i ∧
    (∑ t : Fin 2, (fFactor i t).conjTranspose * fFactor i t) = F i := by
  have hs := S_facts i
  constructor
  · unfold eFactor
    rw [sqrt_gram _ (by norm_num)]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, hs.1.eq, add_mul, mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs.2.2]
    unfold E
    module
  · rw [Fin.sum_univ_two]
    dsimp [fFactor]
    rw [sqrt_gram _ (by norm_num)]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, star_trivial, hs.1.eq, add_mul, mul_add,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hs.2.2]
    unfold F
    module

private theorem channels : IsChannel (⇑Phi) ∧ IsChannel (⇑Psi) := by
  constructor
  · exact measurePrepare_channel E (fun i (_ : Fin 1) => eFactor i)
      (fun i => by simpa using (effect_grams i).1) effects_sum.1
  · exact measurePrepare_channel F fFactor (fun i => (effect_grams i).2) effects_sum.2

private def h (i j : Fin 4) : ℝ := 1 / 64 + (15 / 16) * (if i = j then 1 else 0)
private def jointEffects (p : Fin 4 × Fin 4) : M4 := h p.1 p.2 • E p.1
private def Gamma : Map (Fin 4) (Fin 4 × Fin 4) := measurePrepare jointEffects

private theorem h_nonneg (i j : Fin 4) : 0 ≤ h i j := by
  rw [h.eq_1]
  split_ifs <;> norm_num

private theorem h_row_sum (i : Fin 4) : ∑ j : Fin 4, h i j = 1 := by
  simp only [h.eq_1]
  fin_cases i <;> norm_num [Fin.sum_univ_four, Fin.ext_iff]

private theorem h_mix (j : Fin 4) : ∑ i : Fin 4, h i j • E i = F j := by
  simp only [h.eq_1]
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

private theorem gamma_channel : IsChannel (⇑Gamma) := by
  apply measurePrepare_channel jointEffects
    (fun p (_ : Fin 1) => Real.sqrt (h p.1 p.2) • eFactor p.1)
  · intro p
    simp only [Fin.sum_univ_one]
    rw [sqrt_gram _ (h_nonneg _ _), (effect_grams p.1).1]
    rfl
  · rw [Fintype.sum_prod_type]
    simp only [jointEffects_marginals.1]
    exact effects_sum.1

private theorem compatible_witness : Compatible Phi Psi := by
  refine ⟨Gamma, gamma_channel, ?_, ?_⟩
  · intro R
    exact (measurePrepare_marginals jointEffects R).1.trans
      (congrArg (fun L => measurePrepare L R) (funext jointEffects_marginals.1))
  · intro R
    exact (measurePrepare_marginals jointEffects R).2.trans
      (congrArg (fun L => measurePrepare L R) (funext jointEffects_marginals.2))

private def contract (A : A4) (U V : M4) : M4 :=
  fun a b => Matrix.trace (Matrix.kroneckerMap (· * ·) U V *
    A.submatrix (fun x : Fin 4 × Fin 4 => (a, x)) (fun y : Fin 4 × Fin 4 => (b, y)))

private def B (A : A4) (i j : Fin 4) : M4 := contract A (E i) (F j)

private theorem contract_apply (A : A4) (U V : M4) (a b : Fin 4) :
    contract A U V a b = ∑ x : Fin 4 × Fin 4, ∑ y : Fin 4 × Fin 4,
      A (a, x) (b, y) * U y.1 x.1 * V y.2 x.2 := by
  unfold contract
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.submatrix_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private theorem contract_add_left (A : A4) (U W V : M4) :
    contract A (U + W) V = contract A U V + contract A W V := by
  unfold contract
  ext a b
  rw [Matrix.add_kronecker, Matrix.add_mul, Matrix.trace_add]
  rfl

private theorem contract_add_right (A : A4) (U V W : M4) :
    contract A U (V + W) = contract A U V + contract A U W := by
  unfold contract
  ext a b
  rw [Matrix.kronecker_add, Matrix.add_mul, Matrix.trace_add]
  rfl

private theorem contract_smul_left (A : A4) (c : ℝ) (U V : M4) :
    contract A (c • U) V = c • contract A U V := by
  unfold contract
  ext a b
  rw [Matrix.smul_kronecker, Matrix.smul_mul, Matrix.trace_smul]
  rfl

private theorem contract_smul_right (A : A4) (c : ℝ) (U V : M4) :
    contract A U (c • V) = c • contract A U V := by
  unfold contract
  ext a b
  rw [Matrix.kronecker_smul, Matrix.smul_mul, Matrix.trace_smul]
  rfl

private theorem image_blocks (A : A4) :
    jordanAction Phi Psi A = Matrix.blockDiagonal (fun p : Fin 4 × Fin 4 => B A p.1 p.2) := by
  ext ⟨a, i, j⟩ ⟨b, k, l⟩
  have hk (c d : Fin 4 × Fin 4) :
      MatrixMap.kron Phi Psi (Matrix.single c d 1) (i, j) (k, l) =
        (if i = k then E i d.1 c.1 else 0) * (if j = l then F j d.2 c.2 else 0) := by
    rcases c with ⟨c, c'⟩
    rcases d with ⟨d, d'⟩
    rw [Phi.eq_1, Psi.eq_1, MatrixMap.kron_def]
    simp [measurePrepare_single, Matrix.single_apply,
      Prod.mk.injEq, ite_and, mul_ite, Finset.sum_ite_irrel]
  unfold jordanAction
  rw [MatrixMap.kron_def]
  simp only [LinearMap.id_apply, Matrix.single_apply, ite_and,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, hk]
  rw [Matrix.blockDiagonal_apply']
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp only [if_true, B.eq_1, contract_apply, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring
    · simp [hjl]
  · simp [hik]

private theorem B_possemidef (A : A4)
    (hT : (jordanAction Phi Psi A).PosSemidef) (i j : Fin 4) :
    (B A i j).PosSemidef := by
  rw [image_blocks] at hT
  have hp := hT.submatrix (fun a : Fin 4 => (a, (i, j)))
  have he : (Matrix.blockDiagonal (fun p : Fin 4 × Fin 4 => B A p.1 p.2)).submatrix
      (fun a : Fin 4 => (a, (i, j))) (fun a : Fin 4 => (a, (i, j))) = B A i j := by
    ext a b
    change (if (i, j) = (i, j) then B A i j a b else 0) = B A i j a b
    exact if_pos rfl
  rw [he] at hp
  exact hp

private theorem contract_id_right (A : A4)
    (h2 : traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) (U : M4) :
    contract A U 1 = U.transpose := by
  ext a b
  have hm (r s : Fin 4) :
      (∑ t : Fin 4, A (a, (r, t)) (b, (s, t))) =
        if a = r ∧ b = s then 1 else 0 := by
    have hh := congrArg (fun M => M (a, r) (b, s)) h2
    change (∑ t : Fin 4, A (a, (r, t)) (b, (s, t))) =
      (Matrix.single r s 1) a b at hh
    simpa only [Matrix.single_apply, eq_comm] using hh
  rw [contract_apply]
  simp only [Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    _ = ∑ r : Fin 4, ∑ s : Fin 4,
        (∑ t : Fin 4, A (a, (r, t)) (b, (s, t))) * U s r := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = U.transpose a b := by
      simp [hm, ite_and, ite_mul, Finset.sum_ite_irrel]

private theorem contract_id_left (A : A4)
    (h1 : traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) (V : M4) :
    contract A 1 V = V.transpose := by
  ext a b
  have hm (r s : Fin 4) :
      (∑ t : Fin 4, A (a, (t, r)) (b, (t, s))) =
        if a = r ∧ b = s then 1 else 0 := by
    have hh := congrArg (fun M => M (a, r) (b, s)) h1
    change (∑ t : Fin 4, A (a, (t, r)) (b, (t, s))) =
      (Matrix.single r s 1) a b at hh
    simpa only [Matrix.single_apply, eq_comm] using hh
  rw [contract_apply]
  simp only [Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    _ = ∑ r : Fin 4, ∑ s : Fin 4,
        (∑ t : Fin 4, A (a, (t, r)) (b, (t, s))) * V s r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = V.transpose a b := by
      simp [hm, ite_and, ite_mul, Finset.sum_ite_irrel]

private theorem B_half_row (A : A4)
    (h2 : traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) (i : Fin 4) :
    B A i 2 + B A i 3 = (1 / 2 : ℝ) • E i := by
  rw [B.eq_1, B.eq_1]
  rw [← contract_add_right, effect_halves.2.2.2, contract_smul_right,
    contract_id_right A h2, (effects_transpose i).1]

private theorem B_half_col (A : A4)
    (h1 : traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) (j : Fin 4) :
    B A 0 j + B A 1 j = (1 / 2 : ℝ) • F j := by
  rw [B.eq_1, B.eq_1]
  rw [← contract_add_left, effect_halves.1, contract_smul_left,
    contract_id_left A h1, (effects_transpose j).2]

private def sign : Fin 2 → ℝ := ![1, -1]
private def leftIndex : Fin 2 → Fin 4 := ![0, 1]
private def rightIndex : Fin 2 → Fin 4 := ![2, 3]
private def G (A : A4) (s t : Fin 2) : M4 :=
  (4 : ℝ) • B A (leftIndex s) (rightIndex t)

private theorem G_possemidef (A : A4)
    (hT : (jordanAction Phi Psi A).PosSemidef) (s t : Fin 2) :
    (G A s t).PosSemidef :=
  (B_possemidef A hT _ _).smul (by norm_num : (0 : ℝ) ≤ 4)

private theorem G_marginals (A : A4)
    (h1 : traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4)))
    (h2 : traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) :
    (∀ s : Fin 2, ∑ t : Fin 2, G A s t =
      (1 / 2 : ℝ) • (1 + ((4 / 5 : ℝ) * sign s) • P)) ∧
    (∀ t : Fin 2, ∑ s : Fin 2, G A s t =
      (1 / 2 : ℝ) • (1 + ((3 / 4 : ℝ) * sign t) • Q)) := by
  constructor
  · intro s
    rw [Fin.sum_univ_two]
    change (4 : ℝ) • B A (leftIndex s) 2 + (4 : ℝ) • B A (leftIndex s) 3 = _
    rw [← smul_add, B_half_row A h2]
    fin_cases s <;> dsimp [E, S, leftIndex, sign] <;> module
  · intro t
    rw [Fin.sum_univ_two]
    change (4 : ℝ) • B A 0 (rightIndex t) + (4 : ℝ) • B A 1 (rightIndex t) = _
    rw [← smul_add, B_half_col A h1]
    fin_cases t <;> dsimp [F, S, rightIndex, sign] <;> module

private theorem G_moments (A : A4)
    (h1 : traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4)))
    (h2 : traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) :
    (∑ s : Fin 2, ∑ t : Fin 2, G A s t) = 1 ∧
    (∑ s : Fin 2, ∑ t : Fin 2, sign s • G A s t) = (4 / 5 : ℝ) • P ∧
    (∑ s : Fin 2, ∑ t : Fin 2, sign t • G A s t) = (3 / 4 : ℝ) • Q := by
  obtain ⟨hr, hc⟩ := G_marginals A h1 h2
  have hr0 := hr 0
  have hr1 := hr 1
  have hc0 := hc 0
  have hc1 := hc 1
  simp only [Fin.sum_univ_two] at hr0 hr1 hc0 hc1 ⊢
  dsimp [sign] at hr0 hr1 hc0 hc1 ⊢
  constructor
  · calc
      _ = (G A 0 0 + G A 0 1) + (G A 1 0 + G A 1 1) := rfl
      _ = _ := congrArg₂ (· + ·) hr0 hr1
      _ = 1 := by module
  constructor
  · calc
      _ = (G A 0 0 + G A 0 1) - (G A 1 0 + G A 1 1) := by module
      _ = _ := congrArg₂ (· - ·) hr0 hr1
      _ = (4 / 5 : ℝ) • P := by module
  · calc
      _ = (G A 0 0 + G A 1 0) - (G A 0 1 + G A 1 1) := by module
      _ = _ := congrArg₂ (· - ·) hc0 hc1
      _ = (3 / 4 : ℝ) • Q := by module

private def K (s t : Fin 2) : M4 :=
  (2 : ℝ) • 1 - sign s • P - sign t • Q
private def H (s t : Fin 2) : M4 :=
  (3 / 2 : ℝ) • 1 - sign s • P - sign t • Q

private theorem H_gram (s t : Fin 2) :
    H s t = (1 / 4 : ℝ) • ((K s t).conjTranspose * K s t) := by
  obtain ⟨hp, hq, _, _, hpp, hqq, hpq⟩ := pauli_facts
  unfold H K
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hp.eq, hq.eq, star_trivial]
  fin_cases s <;> fin_cases t <;> dsimp [sign]
  all_goals
    simp only [one_smul, neg_smul, sub_neg_eq_add, sub_mul, mul_sub,
      add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one, hpp, hqq]
    have hx : Q * P = -(P * Q) := by
      exact eq_neg_of_add_eq_zero_right hpq
    rw [hx]
    module

private theorem trace_gram_mul_re_nonneg (K G : M4) (hG : G.PosSemidef) :
    0 ≤ (Matrix.trace ((K.conjTranspose * K) * G)).re := by
  exact RHLinalg.trace_mul_nonneg_of_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self K) hG

private theorem trace_sum_nonneg (A : A4)
    (hT : (jordanAction Phi Psi A).PosSemidef) :
    0 ≤ ∑ s : Fin 2, ∑ t : Fin 2, (Matrix.trace (H s t * G A s t)).re := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro t _
  rw [H_gram, Matrix.smul_mul, Matrix.trace_smul]
  rw [Complex.smul_re, smul_eq_mul]
  exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (trace_gram_mul_re_nonneg (K s t) _ (G_possemidef A hT s t))

private theorem trace_sum_value (A : A4)
    (h1 : traceX1 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4)))
    (h2 : traceX2 A = MatrixMap.choi_matrix (LinearMap.id : Map (Fin 4) (Fin 4))) :
    (∑ s : Fin 2, ∑ t : Fin 2, (Matrix.trace (H s t * G A s t)).re) = -(1 / 5 : ℝ) := by
  have hm := G_moments A h1 h2
  have hs : (∑ s : Fin 2, ∑ t : Fin 2, H s t * G A s t) =
      (3 / 2 : ℝ) • (∑ s : Fin 2, ∑ t : Fin 2, G A s t) -
      P * (∑ s : Fin 2, ∑ t : Fin 2, sign s • G A s t) -
      Q * (∑ s : Fin 2, ∑ t : Fin 2, sign t • G A s t) := by
    unfold H
    simp only [sub_mul, Matrix.smul_mul, Matrix.one_mul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, Matrix.mul_sum, Matrix.mul_smul]
  have hv : (∑ s : Fin 2, ∑ t : Fin 2, H s t * G A s t) =
      (-(1 / 20) : ℝ) • (1 : M4) := by
    rw [hs, hm.1, hm.2.1, hm.2.2, Matrix.mul_smul, Matrix.mul_smul,
      pauli_facts.2.2.2.2.1, pauli_facts.2.2.2.2.2.1]
    module
  calc
    _ = (Matrix.trace (∑ s : Fin 2, ∑ t : Fin 2, H s t * G A s t)).re := by
      simp
    _ = -(1 / 5 : ℝ) := by
      rw [hv, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re]
      norm_num

private theorem not_jordanCompatible : ¬ JordanCompatible Phi Psi := by
  rintro ⟨A, _, h1, h2, hT⟩
  have hn := trace_sum_nonneg A hT
  rw [trace_sum_value A h1 h2] at hn
  norm_num at hn

theorem result : ¬ claim := by
  intro h
  exact not_jordanCompatible
    (h 4 Phi Psi channels.1 channels.2 compatible_witness)

end D5.S3.QuantumChannels.JordanCompatibilityRefutation
