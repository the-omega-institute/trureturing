/- GID: D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular exchanges bound changes in transient depth across arbitrary matrix sizes. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Hom.Defs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

universe u v

abbrev Mat (R : Type u) (n m : ℕ) := Matrix (Fin n) (Fin m) R

section Semiring

variable {R : Type u} [Semiring R] {n m : ℕ}

/-- The elementary identity retains the rectangular intermediate dimensions. -/
theorem rectangular_exchange_power (U : Mat R n m) (V : Mat R m n) (j : ℕ) :
    (U * V) ^ (j + 1) = U * (V * U) ^ j * V := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ _ (j + 1), ih, pow_succ (V * U) j]
      simp only [Matrix.mul_assoc]

/-- A positive nilpotence depth, including depth one for a zero matrix. -/
def ExactDepth (A : Mat R n n) (d : ℕ) : Prop :=
  0 < d ∧ A ^ d = 0 ∧ ∀ j : ℕ, 0 < j → j < d → A ^ j ≠ 0

/-- Every node can have a different finite matrix size. -/
inductive ExchangeChain (R : Type u) [Semiring R] :
    {n m : ℕ} → Mat R n n → Mat R m m → ℕ → Prop where
  | nil {n : ℕ} (A : Mat R n n) : ExchangeChain R A A 0
  | cons {n k m L : ℕ} (U : Mat R n k) (V : Mat R k n) {B : Mat R m m}
      (tail : ExchangeChain R (V * U) B L) :
      ExchangeChain R (U * V) B (L + 1)

/-- A zero power at the terminal node propagates backwards along the entire chain. -/
theorem chain_zero_power {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L) :
    ∀ j : ℕ, B ^ j = 0 → A ^ (j + L) = 0 := by
  induction c with
  | nil A =>
      intro j hj
      simpa using hj
  | cons U V tail ih =>
      intro j hj
      have hz : (U * V) ^ ((j + _) + 1) = 0 := by
        rw [rectangular_exchange_power, ih j hj]
        simp
      simpa [Nat.add_assoc] using hz

/-- The same propagation holds in the opposite direction. -/
theorem chain_zero_power_reverse {A : Mat R n n} {B : Mat R m m} {L : ℕ}
    (c : ExchangeChain R A B L) :
    ∀ j : ℕ, A ^ j = 0 → B ^ (j + L) = 0 := by
  induction c with
  | nil A =>
      intro j hj
      simpa using hj
  | cons U V tail ih =>
      intro j hj
      have hz : (V * U) ^ (j + 1) = 0 := by
        rw [rectangular_exchange_power, hj]
        simp
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (j + 1) hz

/-- A short chain cannot cross a larger positive nilpotence-depth gap. -/
theorem chain_depth_barrier {A : Mat R n n} {B : Mat R m m} {a b L : ℕ}
    (c : ExchangeChain R A B L) (ha : ExactDepth A a) (hb : ExactDepth B b) :
    a ≤ b + L ∧ b ≤ a + L := by
  have hap : 0 < a := ha.1
  have hbp : 0 < b := hb.1
  constructor
  · by_contra h
    exact ha.2.2 (b + L) (by omega) (Nat.lt_of_not_ge h)
      (chain_zero_power c b hb.2.1)
  · by_contra h
    exact hb.2.2 (a + L) (by omega) (Nat.lt_of_not_ge h)
      (chain_zero_power_reverse c a ha.2.1)

end Semiring

section Projection

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

theorem map_exchange_chain (f : R →ₙ+* S) {n m L : ℕ}
    {A : Mat R n n} {B : Mat R m m} (c : ExchangeChain R A B L) :
    ExchangeChain S (A.map f) (B.map f) L := by
  induction c with
  | nil A => exact ExchangeChain.nil _
  | cons U V tail ih =>
      have hUV : (U * V).map f = U.map f * V.map f := by
        ext i j
        simp [Matrix.mul_apply, map_sum, map_mul]
      have hVU : (V * U).map f = V.map f * U.map f := by
        ext i j
        simp [Matrix.mul_apply, map_sum, map_mul]
      rw [hUV, hVU] at ih ⊢
      exact ExchangeChain.cons (U.map f) (V.map f) ih

end Projection

section CentralIdempotent

variable {R : Type u} [Ring R]

/-- Remove the uniform component using a central idempotent. -/
def complementProjection (e : R) (he : e * e = e)
    (hc : ∀ x : R, e * x = x * e) : R →ₙ+* R := by
  let p : R := 1 - e
  have hp : p * p = p := by
    dsimp [p]
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hpc : ∀ x : R, p * x = x * p := by
    intro x
    dsimp [p]
    simp only [sub_mul, one_mul, mul_sub, mul_one, hc x]
  exact
    { toFun := fun x => p * x
      map_zero' := mul_zero p
      map_add' := fun x y => mul_add p x y
      map_mul' := fun x y => by
        change p * (x * y) = (p * x) * (p * y)
        calc
          p * (x * y) = (p * p) * (x * y) := by rw [hp]
          _ = (p * (p * x)) * y := by simp only [mul_assoc]
          _ = (p * (x * p)) * y := by rw [hpc x]
          _ = (p * x) * (p * y) := by simp only [mul_assoc] }

end CentralIdempotent

#print axioms rectangular_exchange_power
#print axioms chain_depth_barrier
#print axioms complementProjection

end D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
