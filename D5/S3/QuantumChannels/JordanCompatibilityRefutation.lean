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

end D5.S3.QuantumChannels.JordanCompatibilityRefutation
