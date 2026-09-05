/- GID: D5/S3/Observer/Hankel/FiniteHoKalmanBlocks
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/FiniteHoKalmanBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite sampled Hankel blocks determine an exact realization in reachable coordinates. -/

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.FiniteHoKalmanBlocks

/-- Exactly `2*h` Markov parameters, with convention `m(k)=C*A^k*B`. -/
abbrev Samples (F : Type*) (h p m : Nat) :=
  Fin (2 * h) → Matrix (Fin p) (Fin m) F

/-- A selected time/output row and time/input column for each state coordinate. -/
abbrev Pivot (h p m r : Nat) :=
  (Fin r → Fin h × Fin p) × (Fin r → Fin h × Fin m)

variable {F : Type*} {h p m r : Nat}

/-- Selected unshifted Hankel minor. Every array access has a finite bound. -/
def baseBlock (s : Samples F h p m) (q : Pivot h p m r) :
    Matrix (Fin r) (Fin r) F := fun i j =>
  s ⟨(q.1 i).1.val + (q.2 j).1.val, by
    have hi := (q.1 i).1.isLt
    have hj := (q.2 j).1.isLt
    omega⟩ (q.1 i).2 (q.2 j).2

/-- Selected one-step shifted Hankel minor. -/
def shiftBlock (s : Samples F h p m) (q : Pivot h p m r) :
    Matrix (Fin r) (Fin r) F := fun i j =>
  s ⟨(q.1 i).1.val + 1 + (q.2 j).1.val, by
    have hi := (q.1 i).1.isLt
    have hj := (q.2 j).1.isLt
    omega⟩ (q.1 i).2 (q.2 j).2

/-- Columns at time zero, restricted to the selected observation rows. -/
def inputBlock (s : Samples F h p m) (q : Pivot h p m r) :
    Matrix (Fin r) (Fin m) F := fun i j =>
  s ⟨(q.1 i).1.val, by have hi := (q.1 i).1.isLt; omega⟩ (q.1 i).2 j

/-- Rows at time zero, restricted to the selected reachability columns. -/
def outputBlock (s : Samples F h p m) (q : Pivot h p m r) :
    Matrix (Fin p) (Fin r) F := fun i j =>
  s ⟨(q.2 j).1.val, by have hj := (q.2 j).1.isLt; omega⟩ i (q.2 j).2

section Field
variable [Field F]

/-- Explicit adjugate inverse. This definition uses field operations and finite sums only. -/
def adjInverse (K : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  K.det⁻¹ • K.adjugate

theorem adjInverse_mul (K : Matrix (Fin r) (Fin r) F) (hk : K.det ≠ 0) :
    adjInverse K * K = 1 := by
  simp only [adjInverse, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

theorem mul_adjInverse (K : Matrix (Fin r) (Fin r) F) (hk : K.det ≠ 0) :
    K * adjInverse K = 1 := by
  simp only [adjInverse, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul,
    inv_mul_cancel₀ hk, one_smul]

/-- State transition reconstructed from two consecutive finite data blocks. -/
def fittedA (s : Samples F h p m) (q : Pivot h p m r) : Matrix (Fin r) (Fin r) F :=
  adjInverse (baseBlock s q) * shiftBlock s q

/-- Input map reconstructed from the finite data. -/
def fittedB (s : Samples F h p m) (q : Pivot h p m r) : Matrix (Fin r) (Fin m) F :=
  adjInverse (baseBlock s q) * inputBlock s q

/-- Output map in the selected reachable coordinates. -/
def fittedC (s : Samples F h p m) (q : Pivot h p m r) : Matrix (Fin p) (Fin r) F :=
  outputBlock s q

/-- Observation rows selected from a reference realization. -/
def selectedO (A : Matrix (Fin r) (Fin r) F) (C : Matrix (Fin p) (Fin r) F)
    (q : Pivot h p m r) : Matrix (Fin r) (Fin r) F :=
  fun i k => (C * A ^ (q.1 i).1.val) (q.1 i).2 k

/-- Reachability columns selected from a reference realization. -/
def selectedR (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F)
    (q : Pivot h p m r) : Matrix (Fin r) (Fin r) F :=
  fun k j => (A ^ (q.2 j).1.val * B) k (q.2 j).2

/-- Finite data factorization is derived from the sample semantics. -/
theorem sample_factorizations
    (s : Samples F h p m) (q : Pivot h p m r)
    (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F)
    (C : Matrix (Fin p) (Fin r) F)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B) :
    baseBlock s q = selectedO A C q * selectedR A B q ∧
    shiftBlock s q = selectedO A C q * (A * selectedR A B q) ∧
    inputBlock s q = selectedO A C q * B ∧
    outputBlock s q = C * selectedR A B q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    change (s _) _ _ =
      ((C * A ^ (q.1 i).1.val) * (A ^ (q.2 j).1.val * B)) _ _
    rw [hs]
    simp only [pow_add, Matrix.mul_assoc]
  · ext i j
    change (s _) _ _ =
      ((C * A ^ (q.1 i).1.val) * (A * (A ^ (q.2 j).1.val * B))) _ _
    rw [hs]
    simp only [pow_add, pow_one, Matrix.mul_assoc]
  · ext i j
    change (s _) _ _ = (C * A ^ (q.1 i).1.val * B) _ _
    rw [hs]
  · ext i j
    change (s _) _ _ = (C * (A ^ (q.2 j).1.val * B)) _ _
    rw [hs, Matrix.mul_assoc]

/-- Exact all-time reproduction follows from four finite block factorizations.
The factorization equations are consumed below by `finite_samples_exact_recovery`. -/
theorem factorized_exact_recovery
    (K L O R A Q : Matrix (Fin r) (Fin r) F)
    (V B : Matrix (Fin r) (Fin m) F) (W C : Matrix (Fin p) (Fin r) F)
    (hK : K = O * R) (hL : L = O * (A * R))
    (hV : V = O * B) (hW : W = C * R) (hQ : Q * K = 1) :
    ∀ n : Nat, W * (Q * L) ^ n * (Q * V) = C * A ^ n * B := by
  let S := Q * O
  have hSR : S * R = 1 := by
    dsimp [S]
    rw [Matrix.mul_assoc, ← hK, hQ]
  have hRS : R * S = 1 := mul_eq_one_comm.mp hSR
  have hA : Q * L = S * (A * R) := by
    rw [hL]
    simp only [S, Matrix.mul_assoc]
  have hB : Q * V = S * B := by
    rw [hV]
    simp only [S, Matrix.mul_assoc]
  have hp : ∀ n : Nat, R * (Q * L) ^ n = A ^ n * R := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        R * (Q * L) ^ (n + 1) = (R * (Q * L) ^ n) * (Q * L) := by
          rw [pow_succ, Matrix.mul_assoc]
        _ = (A ^ n * R) * (S * (A * R)) := by rw [ih, hA]
        _ = A ^ (n + 1) * R := by
          rw [pow_succ]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc R S, hRS, Matrix.one_mul]
  intro n
  rw [hW, hB]
  calc
    (C * R) * (Q * L) ^ n * (S * B) = C * (R * (Q * L) ^ n) * (S * B) := by
      simp only [Matrix.mul_assoc]
    _ = C * (A ^ n * R) * (S * B) := by rw [hp]
    _ = C * A ^ n * B := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R S, hRS, Matrix.one_mul]

/-- Given any order-r reference system matching the finite samples and a nonsingular
selected Hankel minor, the computed system reproduces its complete behavior.
No diagonalizability, simple spectrum, recurrence oracle or supplied inverse is assumed. -/
theorem finite_samples_exact_recovery
    (s : Samples F h p m) (q : Pivot h p m r)
    (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F)
    (C : Matrix (Fin p) (Fin r) F)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B)
    (hk : (baseBlock s q).det ≠ 0) (n : Nat) :
    fittedC s q * (fittedA s q) ^ n * fittedB s q = C * A ^ n * B := by
  obtain ⟨hK, hL, hV, hW⟩ := sample_factorizations s q A B C hs
  exact factorized_exact_recovery _ _ _ _ _ _ _ _ _ _ hK hL hV hW
    (adjInverse_mul _ hk) n

end Field

#print axioms finite_samples_exact_recovery

end D5.S3.Observer.Hankel.FiniteHoKalmanBlocks
