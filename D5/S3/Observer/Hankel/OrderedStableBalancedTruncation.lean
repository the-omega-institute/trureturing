/- GID: D5/S3/Observer/Hankel/OrderedStableBalancedTruncation
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/OrderedStableBalancedTruncation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One constructed largest-singular-weight reduced model has both strict complex-spectrum stability and the certified tail-sum error bound. -/

import D5.S3.Observer.Hankel.OrderedBalancedCoordinates
import D5.S3.Observer.Hankel.DiscreteSteinCompressionStability

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.OrderedStableBalancedTruncation

open Matrix
open D5.S3.Observer.Hankel.PositiveGramianBalancing
open D5.S3.Observer.Hankel.ExactGramianSeries
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open D5.S3.Observer.Hankel.BalancedTruncationTail
open D5.S3.Observer.Hankel.BalancedRealizationTransport
open D5.S3.Observer.Hankel.InfiniteHankelGramian
open D5.S3.Observer.Hankel.BalancedHankelSchmidt
open D5.S3.Observer.Hankel.OrderedBalancedCoordinates
open D5.S3.Observer.Hankel.DiscreteSteinCompressionStability
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

variable {n m p : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ}

private theorem transition_intertwines (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    b.toOriginal * balancedA b A = A * b.toOriginal := by
  simp only [balancedA, ← Matrix.mul_assoc, b.to_from, one_mul]

private theorem transition_power_intertwines (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    b.toOriginal * (balancedA b A) ^ k = A ^ k * b.toOriginal := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        b.toOriginal * (balancedA b A) ^ (k + 1) =
            (b.toOriginal * (balancedA b A) ^ k) * balancedA b A := by
          rw [pow_succ, Matrix.mul_assoc]
        _ = (A ^ k * b.toOriginal) * balancedA b A := by rw [ih]
        _ = A ^ k * (A * b.toOriginal) := by
          rw [Matrix.mul_assoc, transition_intertwines]
        _ = A ^ (k + 1) * b.toOriginal := by rw [pow_succ, Matrix.mul_assoc]

/-- Every transformed future readout is the actual original readout after
mapping the state back. This also holds for the sorted coordinate output. -/
theorem balanced_future_readout (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (k : ℕ) :
    balancedC b C * (balancedA b A) ^ k = (C * A ^ k) * b.toOriginal := by
  rw [balancedC, Matrix.mul_assoc, transition_power_intertwines, Matrix.mul_assoc]

/-- Full observation is inherited by the full balanced realization through the
proved inverse coordinate maps. Reduced-model observability is not assumed. -/
theorem balanced_full_observable (b : Coordinates P Q)
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    ∀ x : Fin n → ℝ,
      (∀ k : ℕ, (balancedC b C * (balancedA b A) ^ k).mulVec x = 0) → x = 0 := by
  intro x hx
  have hT : b.toOriginal.mulVec x = 0 := by
    apply hobs
    intro k
    rw [Matrix.mulVec_mulVec, ← balanced_future_readout b A C k]
    exact hx k
  have hS := congrArg b.fromOriginal.mulVec hT
  rw [Matrix.mulVec_mulVec, b.from_to, Matrix.one_mulVec, Matrix.mulVec_zero] at hS
  exact hS

/-- Construct actual infinite Gramians, balancing coordinates and then the
same descending permutation on weights, transition, input and output maps. -/
def orderedSystemCoordinates
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    Coordinates (controlGramian A B) (observationGramian A C) :=
  orderedCoordinates (systemCoordinates A B C hA hcon hobs)

/-- The sorted weights remain the singular weights of the genuine infinite
Hankel operator: actual orthonormal modes, both singular-vector equations,
and the full expansion on every l2 input use the same sorted construction. -/
theorem ordered_hankel_schmidt
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    let b := orderedSystemCoordinates A B C hA hcon hobs
    Antitone b.weight ∧ (∀ i, 0 < b.weight i) ∧
      Orthonormal ℝ (leftMode A B C hA b) ∧ Orthonormal ℝ (rightMode A B C hA b) ∧
      (∀ i, hankel A B C hA (rightMode A B C hA b i) = b.weight i • leftMode A B C hA b i ∧
        (hankel A B C hA).adjoint (leftMode A B C hA b i) = b.weight i • rightMode A B C hA b i) ∧
      (∀ u : Signal (Fin m), hankel A B C hA u = ∑ i,
        (b.weight i * ⟪rightMode A B C hA b i, u⟫) • leftMode A B C hA b i) ∧
      (∀ u : Signal (Fin m), hankel A B C hA u = 0 ↔
        ∀ i, ⟪rightMode A B C hA b i, u⟫ = 0) := by
  let b := orderedSystemCoordinates A B C hA hcon hobs
  exact ⟨ordered_weight_antitone _, b.positive,
    (modes_orthonormal A B C hA b).1, (modes_orthonormal A B C hA b).2,
    hankel_mode_equations A B C hA b, hankel_schmidt_expansion A B C hA b,
    hankel_kernel_iff A B C hA b⟩

/-- The actual largest-weight principal truncation has all its complex poles
strictly inside the unit disk. This includes cuts through repeated weights,
zero-dimensional reduction and full retention. -/
theorem ordered_reduction_spectrum_lt_one
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) :
    let b := orderedSystemCoordinates A B C hA hcon hobs
    ∀ a ∈ spectrum ℂ (complexMatrix (prefixA hr (balancedA b A))), ‖a‖ < 1 := by
  let b := orderedSystemCoordinates A B C hA hcon hobs
  have hb := balanced_stein b A B C (controlGramian_stein A B hA) (observationGramian_stein A C hA)
  exact principal_truncation_spectrum_lt_one b.weight b.positive
    (balancedA b A) (balancedC b C) hb.2.1 (balanced_full_observable b A C hobs) hr

/-- The same ordered actual model satisfies the largest-weight tail error bound
for every finite input-output window of the original system. -/
theorem ordered_reduction_window_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ) (N : ℕ) :
    let b := orderedSystemCoordinates A B C hA hcon hobs
    windowNorm (fun k => matrixResponse A B C u k -
      matrixResponse (prefixA hr (balancedA b A)) (prefixB hr (balancedB b B))
        (prefixC hr (balancedC b C)) u k) N ≤
      2 * tailWeight b.weight r * windowNorm u N := by
  let b := orderedSystemCoordinates A B C hA hcon hobs
  have hb := balanced_stein b A B C (controlGramian_stein A B hA) (observationGramian_stein A C hA)
  simpa only [matrixResponse_transport] using
    balanced_truncation_window_bound m p n b.weight (balancedA b A) (balancedB b B)
      (balancedC b C) hb r hr u N

/-- The same ordered actual model satisfies the infinite-energy tail bound;
error-energy summability is part of the conclusion. -/
theorem ordered_reduction_l2_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) (u : ℕ → Fin m → ℝ)
    (hu : Summable (fun k => squareSum (u k))) :
    let b := orderedSystemCoordinates A B C hA hcon hobs
    let err := fun k => squareSum (matrixResponse A B C u k -
      matrixResponse (prefixA hr (balancedA b A)) (prefixB hr (balancedB b B))
        (prefixC hr (balancedC b C)) u k)
    Summable err ∧ (∑' k, err k) ≤ (2 * tailWeight b.weight r) ^ 2 * ∑' k, squareSum (u k) := by
  let b := orderedSystemCoordinates A B C hA hcon hobs
  have hb := balanced_stein b A B C (controlGramian_stein A B hA) (observationGramian_stein A C hA)
  simpa only [matrixResponse_transport] using
    balanced_truncation_l2_bound b.weight (balancedA b A) (balancedB b B)
      (balancedC b C) hb r hr u hu

/-- A single constructed reduction simultaneously retains the largest singular
weights, is strictly internally stable, and satisfies both error guarantees.
All clauses use the identical returned coordinate maps and retained matrices. -/
theorem ordered_stable_reduction
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : Fin n → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0)
    (hobs : ∀ x : Fin n → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0)
    (r : ℕ) (hr : r ≤ n) :
    let b := orderedSystemCoordinates A B C hA hcon hobs
    let Ar := prefixA hr (balancedA b A)
    let Br := prefixB hr (balancedB b B)
    let Cr := prefixC hr (balancedC b C)
    Antitone b.weight ∧
      (∀ i j : Fin n, i.val < r → r ≤ j.val → b.weight j ≤ b.weight i) ∧
      (∀ a ∈ spectrum ℂ (complexMatrix Ar), ‖a‖ < 1) ∧
      (∀ (u : ℕ → Fin m → ℝ) (N : ℕ),
        windowNorm (fun k => matrixResponse A B C u k - matrixResponse Ar Br Cr u k) N ≤
          2 * tailWeight b.weight r * windowNorm u N) ∧
      (∀ u : ℕ → Fin m → ℝ, Summable (fun k => squareSum (u k)) →
        Summable (fun k => squareSum (matrixResponse A B C u k - matrixResponse Ar Br Cr u k)) ∧
        (∑' k, squareSum (matrixResponse A B C u k - matrixResponse Ar Br Cr u k)) ≤
          (2 * tailWeight b.weight r) ^ 2 * ∑' k, squareSum (u k)) := by
  exact ⟨ordered_weight_antitone _,
    retained_weight_ge_discarded _ r,
    ordered_reduction_spectrum_lt_one A B C hA hcon hobs r hr,
    ordered_reduction_window_bound A B C hA hcon hobs r hr,
    ordered_reduction_l2_bound A B C hA hcon hobs r hr⟩

#print axioms balanced_full_observable
#print axioms ordered_reduction_spectrum_lt_one
#print axioms ordered_stable_reduction

end D5.S3.Observer.Hankel.OrderedStableBalancedTruncation
