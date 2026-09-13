/- GID: D5/S3/Observer/ProbabilisticClosure/TwinedTraceMemoryObstruction
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TwinedTraceMemoryObstruction
   mirror-E: none(waiver:exact-all-time-matrix-family)
   anchors: []
   utility: none
   digest: Two copies of any finite representation have identical all-time
     symmetry-twined traces but different exact projected memory kernels. -/

import D5.S3.Observer.ProbabilisticClosure.ReversibleProjectionMemory
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped Matrix Kronecker

namespace D5.S3.Observer.ProbabilisticClosure.TwinedTraceMemoryObstruction

/-- Two independent rates on the multiplicity space. -/
def diagonalRates (a b : Real) : Matrix (Fin 2) (Fin 2) Real := ![![a, 0], ![0, b]]

/-- Orthogonal mixing of the same two rates, with the observation kept fixed. -/
def mixedRates (a b : Real) : Matrix (Fin 2) (Fin 2) Real :=
  ![![(a+b)/2, (a-b)/2], ![(a-b)/2, (a+b)/2]]

/-- The retained first copy and the discarded second copy are explicit. -/
def firstCopy : Matrix (Fin 2) (Fin 2) Real := ![![1, 0], ![0, 0]]

def secondCopy : Matrix (Fin 2) (Fin 2) Real := ![![0, 0], ![0, 1]]

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual tensor-product operator on two copies of a finite carrier. -/
def liftCopies (M : Matrix (Fin 2) (Fin 2) Real) :
    Matrix (Fin 2 × I) (Fin 2 × I) Real := M ⊗ₖ (1 : Matrix I I Real)

/-- Use R=rho(g) for any real matrix representation. No faithfulness assumption
or identification of the group with the Monster is built into this definition. -/
def copyAction (R : Matrix I I Real) : Matrix (Fin 2 × I) (Fin 2 × I) Real :=
  (1 : Matrix (Fin 2) (Fin 2) Real) ⊗ₖ R

/-- A hidden excursion of exactly k internal hidden steps, using the same
fixed projection for both dynamics. -/
def returnKernel (K : Matrix (Fin 2 × I) (Fin 2 × I) Real) (k : Nat) :
    Matrix (Fin 2 × I) (Fin 2 × I) Real :=
  let P : Matrix (Fin 2 × I) (Fin 2 × I) Real := liftCopies firstCopy
  let Q := 1 - P
  (P * K * Q) * (Q * K * Q) ^ k * (Q * K * P)

/-- Full power traces, even with every operator on the representation factor
inserted, do not determine memory relative to a fixed observation. The exact
nonzero-lag response is computed, not postulated. This is a finite-dimensional
multiplicity-space theorem; it does not construct the Monster or a VOA. -/
theorem twined_traces_and_exact_memory (a b : Real) :
    (∀ R : Matrix I I Real,
      liftCopies (diagonalRates a b) * copyAction R =
        copyAction R * liftCopies (diagonalRates a b) ∧
      liftCopies (mixedRates a b) * copyAction R =
        copyAction R * liftCopies (mixedRates a b) ∧
      liftCopies firstCopy * copyAction R = copyAction R * liftCopies firstCopy) ∧
    (∀ (R : Matrix I I Real) (k : Nat),
      Matrix.trace (copyAction R * (liftCopies (diagonalRates a b)) ^ k) =
        (a ^ k + b ^ k) * Matrix.trace R ∧
      Matrix.trace (copyAction R * (liftCopies (mixedRates a b)) ^ k) =
        (a ^ k + b ^ k) * Matrix.trace R) ∧
    (∀ k : Nat,
      returnKernel (liftCopies (diagonalRates a b) :
        Matrix (Fin 2 × I) (Fin 2 × I) Real) k = 0 ∧
      returnKernel (liftCopies (mixedRates a b) :
        Matrix (Fin 2 × I) (Fin 2 × I) Real) k =
        ((a-b)^2 / 4 * ((a+b)/2)^k) • liftCopies firstCopy) := by
  have hmul (U V : Matrix (Fin 2) (Fin 2) Real) :
      liftCopies (I := I) (U * V) = liftCopies U * liftCopies V := by
    simp only [liftCopies, ← Matrix.mul_kronecker_mul, mul_one]
  have hpow (U : Matrix (Fin 2) (Fin 2) Real) (k : Nat) :
      (liftCopies (I := I) U)^k = liftCopies (U^k) := by
    induction k with
    | zero => simpa [liftCopies] using
        (Matrix.one_kronecker_one (m := Fin 2) (n := I) (α := Real)).symm
    | succ k ih => rw [pow_succ, pow_succ, ih, hmul]
  have hdiag : ∀ k : Nat,
      diagonalRates a b ^ k = diagonalRates (a^k) (b^k) := by
    intro k
    induction k with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [diagonalRates]
    | succ k ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [diagonalRates, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
  have hmixed : ∀ k : Nat,
      mixedRates a b ^ k = mixedRates (a^k) (b^k) := by
    intro k
    induction k with
    | zero => ext i j; fin_cases i <;> fin_cases j <;> norm_num [mixedRates]
    | succ k ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mixedRates, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  have hQ : (1 : Matrix (Fin 2 × I) (Fin 2 × I) Real) - liftCopies firstCopy =
      liftCopies secondCopy := by
    ext ⟨i, r⟩ ⟨j, s⟩
    fin_cases i <;> fin_cases j <;> by_cases hrs : r = s <;>
      simp [liftCopies, firstCopy, secondCopy, Matrix.one_apply, hrs]
  have hreturn (U : Matrix (Fin 2) (Fin 2) Real) (k : Nat) :
      returnKernel (liftCopies (I := I) U) k =
        liftCopies ((firstCopy * U * secondCopy) *
          (secondCopy * U * secondCopy)^k * (secondCopy * U * firstCopy)) := by
    unfold returnKernel
    dsimp only
    rw [hQ]
    simp only [← hmul, hpow]
  have hz : firstCopy * diagonalRates a b * secondCopy = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstCopy, secondCopy, diagonalRates, Matrix.mul_apply, Fin.sum_univ_two]
  let D := secondCopy * mixedRates a b * secondCopy
  let C := secondCopy * mixedRates a b * firstCopy
  let B := firstCopy * mixedRates a b * secondCopy
  have hDC : D * C = ((a+b)/2) • C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, C, firstCopy, secondCopy, mixedRates, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
  have hBC : B * C = ((a-b)^2/4) • firstCopy := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, C, firstCopy, secondCopy, mixedRates, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring
  have hDCpow : ∀ k : Nat, D^k * C = ((a+b)/2)^k • C := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, hDC, smul_smul, pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · intro R
    simp only [liftCopies, copyAction, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    exact ⟨rfl, rfl, rfl⟩
  · intro R k
    rw [hpow, hpow, hdiag, hmixed]
    simp only [copyAction, liftCopies, ← Matrix.mul_kronecker_mul, one_mul,
      mul_one, Matrix.trace_kronecker]
    constructor <;>
      congr 1 <;> simp [Matrix.trace, Matrix.diag, diagonalRates, mixedRates,
        Fin.sum_univ_two] <;> ring
  · intro k
    constructor
    · rw [hreturn, hz]
      simp [liftCopies, Matrix.zero_kronecker]
    · rw [hreturn]
      change liftCopies (I := I) (B * D^k * C) = _
      rw [mul_assoc, hDCpow, mul_smul_comm, hBC, smul_smul]
      simp only [liftCopies, Matrix.smul_kronecker]
      congr 1
      ring

#print axioms twined_traces_and_exact_memory

end D5.S3.Observer.ProbabilisticClosure.TwinedTraceMemoryObstruction
