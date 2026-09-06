/- GID: D5/S3/Observer/Hankel/BalancedRealizationTransport
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/BalancedRealizationTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct a balanced realization from actual infinite Gramians and transfer the certified reduction error to the original system. -/

import D5.S3.Observer.Hankel.ExactGramianSeries
import D5.S3.Observer.Hankel.BalancedTruncationTail

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.BalancedRealizationTransport

open Matrix
open D5.S3.Observer.Hankel.PositiveGramianBalancing
open D5.S3.Observer.Hankel.ExactGramianSeries
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.BalancedTruncationTail
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n m p : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ}

/-- Transition matrix in the constructed balanced coordinates. -/
def balancedA (b : Coordinates P Q) (A : Matrix (Fin n) (Fin n) ℝ) :=
  b.fromOriginal * A * b.toOriginal

/-- Input matrix in the constructed balanced coordinates. -/
def balancedB (b : Coordinates P Q) (B : Matrix (Fin n) (Fin m) ℝ) :=
  b.fromOriginal * B

/-- Output matrix in the constructed balanced coordinates. -/
def balancedC (b : Coordinates P Q) (C : Matrix (Fin p) (Fin n) ℝ) :=
  C * b.toOriginal

private theorem transition_to (b : Coordinates P Q) (A : Matrix (Fin n) (Fin n) ℝ) :
    b.toOriginal * balancedA b A = A * b.toOriginal := by
  simp only [balancedA, ← Matrix.mul_assoc, b.to_from, one_mul]

private theorem transition_from (b : Coordinates P Q) (A : Matrix (Fin n) (Fin n) ℝ) :
    balancedA b A * b.fromOriginal = b.fromOriginal * A := by
  simp only [balancedA, Matrix.mul_assoc, b.to_from, mul_one]

private theorem input_to (b : Coordinates P Q) (B : Matrix (Fin n) (Fin m) ℝ) :
    b.toOriginal * balancedB b B = B := by
  simp only [balancedB, ← Matrix.mul_assoc, b.to_from, one_mul]

/-- Exact observability Stein equality is transported by the constructed congruence. -/
theorem balanced_observability_stein (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hQ : Aᴴ * Q * A + Cᴴ * C = Q) :
    (balancedA b A)ᴴ * diagonal b.weight * balancedA b A +
      (balancedC b C)ᴴ * balancedC b C = diagonal b.weight := by
  calc
    _ = (b.toOriginal * balancedA b A)ᴴ * Q * (b.toOriginal * balancedA b A) +
        (C * b.toOriginal)ᴴ * (C * b.toOriginal) := by
      rw [← b.observability]
      simp only [balancedC, conjTranspose_mul, Matrix.mul_assoc]
    _ = (A * b.toOriginal)ᴴ * Q * (A * b.toOriginal) +
        (C * b.toOriginal)ᴴ * (C * b.toOriginal) := by rw [transition_to]
    _ = b.toOriginalᴴ * (Aᴴ * Q * A + Cᴴ * C) * b.toOriginal := by
      simp only [conjTranspose_mul, mul_add, add_mul, Matrix.mul_assoc]
    _ = diagonal b.weight := by rw [hQ, b.observability]

/-- Exact controllability Stein equality is transported by the dual congruence. -/
theorem balanced_control_stein (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hP : A * P * Aᴴ + B * Bᴴ = P) :
    balancedA b A * diagonal b.weight * (balancedA b A)ᴴ +
      balancedB b B * (balancedB b B)ᴴ = diagonal b.weight := by
  calc
    _ = (balancedA b A * b.fromOriginal) * P * (balancedA b A * b.fromOriginal)ᴴ +
        (b.fromOriginal * B) * (b.fromOriginal * B)ᴴ := by
      rw [← b.controllability]
      simp only [balancedB, conjTranspose_mul, Matrix.mul_assoc]
    _ = (b.fromOriginal * A) * P * (b.fromOriginal * A)ᴴ +
        (b.fromOriginal * B) * (b.fromOriginal * B)ᴴ := by rw [transition_from]
    _ = b.fromOriginal * (A * P * Aᴴ + B * Bᴴ) * b.fromOriginalᴴ := by
      simp only [conjTranspose_mul, mul_add, add_mul, Matrix.mul_assoc]
    _ = diagonal b.weight := by rw [hP, b.controllability]

private theorem quadratic_add {ι : Type} [Fintype ι]
    (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadratic (M + N) x = quadratic M x + quadratic N x := by
  simp [quadratic, add_mulVec, dotProduct_add]

private theorem quadratic_star_self {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    quadratic (Mᴴ * M) x = squareSum (M.mulVec x) := by
  simpa only [mul_one, quadratic_one] using
    quadratic_congruence (1 : Matrix ι ι ℝ) M x

/-- Exact matrix Stein equalities establish all the hypotheses of the existing
balanced-truncation error theorem in the constructed coordinates. -/
theorem balanced_stein (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ)
    (hP : A * P * Aᴴ + B * Bᴴ = P) (hQ : Aᴴ * Q * A + Cᴴ * C = Q) :
    BalancedStein b.weight (balancedA b A) (balancedB b B) (balancedC b C) := by
  refine ⟨b.positive, ?_, ?_⟩
  · intro x
    have he := congrArg (fun M => quadratic M x) (balanced_observability_stein b A C hQ)
    rw [quadratic_add, quadratic_congruence, quadratic_star_self,
      quadratic_diagonal, quadratic_diagonal] at he
    exact le_of_eq he
  · intro x
    have he := congrArg (fun M => quadratic M x) (balanced_control_stein b A B hP)
    rw [quadratic_add] at he
    have hc := quadratic_congruence (diagonal b.weight) (balancedA b A)ᴴ x
    have hb := quadratic_star_self (balancedB b B)ᴴ x
    simp only [conjTranspose_conjTranspose] at hc hb
    rw [hc, hb, quadratic_diagonal, quadratic_diagonal] at he
    simpa only [conjTranspose_eq_transpose_of_trivial] using le_of_eq he

/-- The full forced trajectories, with arbitrary input, are transported exactly. -/
theorem matrixState_transport (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (u : ℕ → Fin m → ℝ) (k : ℕ) :
    b.toOriginal.mulVec (matrixState (balancedA b A) (balancedB b B) u k) =
      matrixState A B u k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [matrixState_succ, matrixState_succ, mulVec_add, mulVec_mulVec,
        mulVec_mulVec, transition_to, input_to, ← mulVec_mulVec, ih]

/-- Balancing preserves the actual input-output behavior for all times. -/
theorem matrixResponse_transport (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    matrixResponse (balancedA b A) (balancedB b B) (balancedC b C) u k =
      matrixResponse A B C u k := by
  unfold matrixResponse balancedC
  rw [← mulVec_mulVec, matrixState_transport]

/-- Construct balancing coordinates from A,B,C themselves. Positive definiteness
and the exact Gramian identities are consequences of the actual infinite series. -/
def systemCoordinates (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    Coordinates (controlGramian A B) (observationGramian A C) :=
  coordinates _ _ (controlGramian_posDef A B hA hcon) (observationGramian_posDef A C hA hobs)

/-- End-to-end finite-window reduction bound for an original system, using only
power stability, controllability and observability hypotheses on that system. -/
theorem constructed_reduction_window_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ) (N : ℕ) :
    let b := systemCoordinates A B C hA hcon hobs
    windowNorm (fun k => matrixResponse A B C u k -
      matrixResponse (prefixA hr (balancedA b A)) (prefixB hr (balancedB b B))
        (prefixC hr (balancedC b C)) u k) N ≤
      2 * tailWeight b.weight r * windowNorm u N := by
  let b := systemCoordinates A B C hA hcon hobs
  have hb := balanced_stein b A B C (controlGramian_stein A B hA) (observationGramian_stein A C hA)
  simpa only [matrixResponse_transport] using
    balanced_truncation_window_bound m p n b.weight (balancedA b A) (balancedB b B)
      (balancedC b C) hb r hr u N

/-- End-to-end infinite-energy reduction guarantee for the actual original
system and constructed reduced model. Error summability is derived. -/
theorem constructed_reduction_l2_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ)
    (hu : Summable (fun k => squareSum (u k))) :
    let b := systemCoordinates A B C hA hcon hobs
    let err := fun k => squareSum (matrixResponse A B C u k -
      matrixResponse (prefixA hr (balancedA b A)) (prefixB hr (balancedB b B))
        (prefixC hr (balancedC b C)) u k)
    Summable err ∧ (∑' k, err k) ≤ (2 * tailWeight b.weight r) ^ 2 * ∑' k, squareSum (u k) := by
  let b := systemCoordinates A B C hA hcon hobs
  have hb := balanced_stein b A B C (controlGramian_stein A B hA) (observationGramian_stein A C hA)
  simpa only [matrixResponse_transport] using
    balanced_truncation_l2_bound b.weight (balancedA b A) (balancedB b B)
      (balancedC b C) hb r hr u hu

#print axioms balanced_stein
#print axioms constructed_reduction_window_bound
#print axioms constructed_reduction_l2_bound

end D5.S3.Observer.Hankel.BalancedRealizationTransport
