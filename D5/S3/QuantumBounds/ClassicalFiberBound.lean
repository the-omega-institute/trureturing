/- GID: D5/S3/QuantumBounds/ClassicalFiberBound
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ClassicalFiberBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the exact CHSH bound for finite classical local fiber models. -/

/- Library-search audit trail (2026-08-09):
   * The complete pinned `Mathlib.Algebra.Star.CHSH` source was read.
     `CHSH_inequality_of_comm` supplies both pointwise sides of the classical bound: the lower
     side is the same theorem applied after flipping both Alice answers. Its ordered-star-algebra
     proof is not reproduced here.
   * The passage from the pointwise bound to `classicalCHSH` uses only finite sums, nonnegative
     weights, and their normalization. No measure-theoretic or infinite-fiber model is introduced.
   * `D5.S3.QuantumBounds.CHSHWitness.bell_chsh_value` is the frozen quantum contrast at
     `2 * sqrt 2`; this module cites that declaration and proves no quantum bound or witness.
-/

import D5.S3.QuantumBounds.CHSHWitness
import Mathlib.Algebra.Star.CHSH

namespace D5.S3.QuantumBounds.ClassicalFiberBound

open scoped BigOperators

/-- A Boolean deterministic answer, read as a classical observable with value `-1` or `1`. -/
def boolValue : Bool -> Real
  | false => -1
  | true => 1

@[simp] theorem bool_value_sq (answer : Bool) : boolValue answer ^ 2 = 1 := by
  cases answer <;> norm_num [boolValue]

@[simp] theorem bool_value_not (answer : Bool) : boolValue (!answer) = -boolValue answer := by
  cases answer <;> norm_num [boolValue]

/-- Two deterministic local answer tables, one for Alice and one for Bob, indexed by the two
measurement settings. Their only shared input is the hidden fiber address. -/
structure DeterministicFiberModel (Fiber : Type*) where
  alice : Fin 2 -> Fiber -> Bool
  bob : Fin 2 -> Fiber -> Bool

/-- The real-valued observable associated to one Boolean answer table. -/
def observable {Fiber : Type*} (answer : Fiber -> Bool) : Fiber -> Real :=
  fun fiber => boolValue (answer fiber)

/-- The deterministic CHSH value at one hidden fiber address. -/
def chshAt {Fiber : Type*} (model : DeterministicFiberModel Fiber) (fiber : Fiber) : Real :=
  observable (model.alice 0) fiber * observable (model.bob 0) fiber +
    observable (model.alice 0) fiber * observable (model.bob 1) fiber +
    observable (model.alice 1) fiber * observable (model.bob 0) fiber -
    observable (model.alice 1) fiber * observable (model.bob 1) fiber

/-- The classical CHSH correlation is the finite weighted expectation of the deterministic
fiber values. Probability assumptions on `mu` are stated by the bound theorems. -/
def classicalCHSH {Fiber : Type*} [Fintype Fiber]
    (mu : Fiber -> Real) (model : DeterministicFiberModel Fiber) : Real :=
  Finset.univ.sum fun fiber => mu fiber * chshAt model fiber

private theorem fiber_is_chsh_tuple {Fiber : Type*}
    (model : DeterministicFiberModel Fiber) (fiber : Fiber) :
    IsCHSHTuple
      (observable (model.alice 0) fiber) (observable (model.alice 1) fiber)
      (observable (model.bob 0) fiber) (observable (model.bob 1) fiber) := by
  refine
    { A₀_inv := ?_
      A₁_inv := ?_
      B₀_inv := ?_
      B₁_inv := ?_
      A₀_sa := ?_
      A₁_sa := ?_
      B₀_sa := ?_
      B₁_sa := ?_
      A₀B₀_commutes := ?_
      A₀B₁_commutes := ?_
      A₁B₀_commutes := ?_
      A₁B₁_commutes := ?_ }
  all_goals simp [observable, mul_comm]

private theorem chsh_at_le_two {Fiber : Type*}
    (model : DeterministicFiberModel Fiber) (fiber : Fiber) :
    chshAt model fiber <= 2 := by
  have h := CHSH_inequality_of_comm
    (observable (model.alice 0) fiber) (observable (model.alice 1) fiber)
    (observable (model.bob 0) fiber) (observable (model.bob 1) fiber)
    (fiber_is_chsh_tuple model fiber)
  simpa [chshAt] using h

/-- Flip both of Alice's deterministic answers, negating the CHSH value pointwise. -/
def flipAlice {Fiber : Type*}
    (model : DeterministicFiberModel Fiber) : DeterministicFiberModel Fiber where
  alice := fun setting fiber => !(model.alice setting fiber)
  bob := model.bob

@[simp] theorem chsh_at_flip_alice {Fiber : Type*}
    (model : DeterministicFiberModel Fiber) (fiber : Fiber) :
    chshAt (flipAlice model) fiber = -chshAt model fiber := by
  simp [chshAt, flipAlice, observable]
  ring

private theorem neg_two_le_chsh_at {Fiber : Type*}
    (model : DeterministicFiberModel Fiber) (fiber : Fiber) :
    -2 <= chshAt model fiber := by
  have h := chsh_at_le_two (flipAlice model) fiber
  rw [chsh_at_flip_alice] at h
  linarith

/-- Every finite classical local fiber model with probability weights satisfies the CHSH bound
in absolute value. The pointwise inequality is mathlib's commutative CHSH theorem. -/
theorem classical_chsh_abs_le_two {Fiber : Type*} [Fintype Fiber]
    (mu : Fiber -> Real) (hmu_nonneg : forall fiber, 0 <= mu fiber)
    (hmu_sum : Finset.univ.sum mu = 1)
    (model : DeterministicFiberModel Fiber) :
    |classicalCHSH mu model| <= 2 := by
  classical
  apply (abs_le).2
  constructor
  · calc
      (-2 : Real) = Finset.univ.sum (fun fiber => mu fiber * (-2)) := by
        rw [<- Finset.sum_mul, hmu_sum]
        norm_num
      _ <= Finset.univ.sum (fun fiber => mu fiber * chshAt model fiber) := by
        exact Finset.sum_le_sum fun fiber _ =>
          mul_le_mul_of_nonneg_left (neg_two_le_chsh_at model fiber) (hmu_nonneg fiber)
  · calc
      Finset.univ.sum (fun fiber => mu fiber * chshAt model fiber) <=
          Finset.univ.sum (fun fiber => mu fiber * 2) := by
        exact Finset.sum_le_sum fun fiber _ =>
          mul_le_mul_of_nonneg_left (chsh_at_le_two model fiber) (hmu_nonneg fiber)
      _ = 2 := by
        rw [<- Finset.sum_mul, hmu_sum]
        norm_num

/-- The constant positive answer tables attain the classical CHSH value `2`. -/
def saturatingModel (Fiber : Type*) : DeterministicFiberModel Fiber where
  alice := fun _ _ => true
  bob := fun _ _ => true

/-- For every normalized finite weight table, a deterministic local model attains CHSH value
exactly `2`. -/
theorem classical_chsh_eq_two_exists {Fiber : Type*} [Fintype Fiber]
    (mu : Fiber -> Real) (hmu_sum : Finset.univ.sum mu = 1) :
    ∃ model : DeterministicFiberModel Fiber, classicalCHSH mu model = 2 := by
  classical
  refine ⟨saturatingModel Fiber, ?_⟩
  simp only [classicalCHSH, chshAt, saturatingModel, observable, boolValue]
  rw [<- Finset.sum_mul, hmu_sum]
  norm_num

/-- The absolute classical local-fiber CHSH bound is exactly `2`: it is an upper bound for every
deterministic answer table and is attained by one such table. -/
theorem classical_chsh_bound_is_exact {Fiber : Type*} [Fintype Fiber]
    (mu : Fiber -> Real) (hmu_nonneg : forall fiber, 0 <= mu fiber)
    (hmu_sum : Finset.univ.sum mu = 1) :
    IsGreatest (Set.range fun model : DeterministicFiberModel Fiber =>
      |classicalCHSH mu model|) 2 := by
  rcases classical_chsh_eq_two_exists mu hmu_sum with ⟨model, hmodel⟩
  constructor
  · refine ⟨model, ?_⟩
    simp [hmodel]
  · rintro _ ⟨model, rfl⟩
    exact classical_chsh_abs_le_two mu hmu_nonneg hmu_sum model

end D5.S3.QuantumBounds.ClassicalFiberBound
