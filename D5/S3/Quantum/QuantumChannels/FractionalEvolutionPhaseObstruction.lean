/- GID: D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim; result=D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result; claim=D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim
   digest: Ordinary oracle circuits cannot implement the prescribed fractional branch uniformly. -/

import D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Definitions 1--3 and Appendix B of arXiv:2610.01940v1, with the Section V
uncontrolled-access substitution. No result or proof of either settlement is included.
`true` denotes sigma = -1 and `false` denotes sigma = +1.
-/

noncomputable section

namespace Trureturing.OpenProblems.FractionalEvolutionPhase

open Matrix
open scoped Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (conj)
open D5.S3.Quantum.QuantumChannels.HarrowParallelChernoffExponentRefutation (diamondNorm)

/-- U^sigma for sigma in {-1,+1}; Hermitian-oracle promises make adjoint the inverse. -/
def query {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  if negative then U.conjTranspose else U

/-- Definition 1's controlled query, with control 0 activating the call. -/
def controlledQuery {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  fun p q => if p.1 = q.1 then
    if p.1 = 0 then query negative U p.2 q.2 else (1 : Matrix (Fin d) (Fin d) ℂ) p.2 q.2
  else 0

/-- Definition 1's fixed inter-query unitaries and signs; m+1 is the finite workspace dimension. -/
structure Circuit (d m N : ℕ) where
  W : Fin (N + 1) → Matrix.unitaryGroup (Fin (m + 1) × Fin d) ℂ
  negative : Fin N → Bool

/-- Section V: every slot uses ordinary U or U-adjoint, with identity on the workspace. -/
def run {d m N : ℕ} (A : Circuit d m N) (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (m + 1) × Fin d) (Fin (m + 1) × Fin d) ℂ :=
  (List.ofFn (fun j : Fin N => j)).foldl
    (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc)
    (A.W 0).val

/-- Appendix B's fixed initialization isometry J|psi> = |0> tensor |psi>. -/
def initialization (d m : ℕ) : Matrix (Fin (m + 1) × Fin d) (Fin d) ℂ :=
  fun p j => if p.1 = 0 ∧ p.2 = j then 1 else 0

/-- Definition 3 with its literal Appendix B isometric embedding: compare A_U J and J U^t.
The existing diamondNorm is unhalved, reference stabilized, and valued in ENNReal.
All oracles and logarithms are quantified; the spectral branch is the half-open [delta, 2*pi).
-/
def Successful {d m N : ℕ} (A : Circuit d m N) (t δ ε : ℝ) : Prop :=
  ∀ (U H : Matrix (Fin d) (Fin d) ℂ),
    U = NormedSpace.exp (Complex.I • H) →
    H.IsHermitian →
    (∀ x : ℝ, x ∈ spectrum ℝ H → δ ≤ x ∧ x < 2 * Real.pi) →
    diamondNorm
      (conj (run A U * initialization d m) -
        conj (initialization d m * NormedSpace.exp (((t : ℂ) * Complex.I) • H))) ≤
      ENNReal.ofReal ε

/-- Positive answer to the unnumbered Section V uncontrolled-access question:
Theorem 1's uniform O(delta^-1 log(1/epsilon)) upper bound with ordinary queries.
The universal constant is independent of the dimension and of t, delta, epsilon.
-/
def claim : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (t δ ε : ℝ), 0 < t → t < 1 → 0 < δ → δ < 1 → 0 < ε → ε < 1 / 2 →
      ∀ d : ℕ, 0 < d →
        ∃ (m N : ℕ) (A : Circuit d m N),
          (N : ℝ) ≤ C * (δ⁻¹ * Real.log (ε⁻¹)) ∧ Successful A t δ ε


private theorem query_neg {d : ℕ} (negative : Bool) (U : Matrix (Fin d) (Fin d) ℂ) :
    query negative (-U) = -query negative U := by
  cases negative <;> simp [query]

private theorem fold_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) (L : List (Fin N))
    (B : Matrix (Fin (m + 1) × Fin d) (Fin (m + 1) × Fin d) ℂ) :
    L.foldl (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) (-U)) * acc) B =
    ((-1 : ℂ) ^ L.length) • L.foldl (fun acc j => (A.W j.succ).val *
      ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) B := by
  induction L generalizing B with
  | nil => simp
  | cons j L ih =>
    simp only [List.foldl_cons, query_neg, Matrix.kronecker_neg, Matrix.mul_neg,
      Matrix.neg_mul, List.length_cons]
    rw [ih]
    have hs : ∀ (L : List (Fin N)) (z : ℂ) B,
        L.foldl (fun acc j => (A.W j.succ).val *
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) (z • B) =
        z • L.foldl (fun acc j => (A.W j.succ).val *
          ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ query (A.negative j) U) * acc) B := by
      intro K z B
      induction K generalizing B with
      | nil => rfl
      | cons j K hk => simp only [List.foldl_cons, Matrix.mul_smul]; exact hk _
    rw [show -(↑(A.W j.succ) * (1 ⊗ₖ query (A.negative j) U) * B) =
      (-1 : ℂ) • (↑(A.W j.succ) * (1 ⊗ₖ query (A.negative j) U) * B) by simp,
      hs, smul_smul, pow_succ]

private theorem run_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    run A (-U) = ((-1 : ℂ) ^ N) • run A U := by
  simpa [run] using fold_neg A U (List.ofFn (fun j : Fin N => j)) (A.W 0).val

private theorem channel_neg {d m N : ℕ} (A : Circuit d m N)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    conj (run A (-U) * initialization d m) = conj (run A U * initialization d m) := by
  rw [run_neg, Matrix.smul_mul]
  ext X
  change (((-1 : ℂ) ^ N) • (run A U * initialization d m)) * X *
    (((-1 : ℂ) ^ N) • (run A U * initialization d m))ᴴ = _
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    map_pow, map_neg, map_one, ← pow_add, ← two_mul, pow_mul]
  norm_num

end Trureturing.OpenProblems.FractionalEvolutionPhase
