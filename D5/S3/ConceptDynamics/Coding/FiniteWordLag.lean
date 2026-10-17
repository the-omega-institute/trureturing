/- SOURCE ONLY — UNCOMPILED. Reuse the immutable project's ACTUAL
rectangular ExchangeChain, including Fin 0 and arbitrary singular vertices.
This proves the lag identities required by UnitLagReduction from a finite
elementary word; they are not extra hypotheses about that word.
Project pin 8a32282e7f57c3a751640623624ee9d1ac5b3a25.
-/
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SourceOnly.FiniteWordLag
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

universe u
variable {R : Type u} [Semiring R]

/-- Both actual products and both intertwiners for a finite rectangular
elementary word. The construction is U*X and Y*V at each cons. -/
theorem chain_lag {n m ℓ : ℕ} {A : Mat R n n} {B : Mat R m m}
    (c : ExchangeChain R A B ℓ) :
    ∃ X : Mat R n m, ∃ Y : Mat R m n,
      A*X = X*B ∧ B*Y = Y*A ∧ X*Y = A^ℓ ∧ Y*X = B^ℓ := by
  induction c with
  | nil A =>
      refine ⟨1, 1, ?_, ?_, ?_, ?_⟩ <;> simp
  | @cons n k m ℓ U V B tail ih =>
      obtain ⟨X, Y, hCX, hBY, hXY, hYX⟩ := ih
      refine ⟨U*X, Y*V, ?_, ?_, ?_, ?_⟩
      · calc
          (U*V)*(U*X) = U*((V*U)*X) := by simp only [Matrix.mul_assoc]
          _ = U*(X*B) := by rw [hCX]
          _ = (U*X)*B := (Matrix.mul_assoc _ _ _).symm
      · calc
          B*(Y*V) = (B*Y)*V := (Matrix.mul_assoc _ _ _).symm
          _ = (Y*(V*U))*V := by rw [hBY]
          _ = (Y*V)*(U*V) := by simp only [Matrix.mul_assoc]
      · calc
          (U*X)*(Y*V) = U*(X*Y)*V := by simp only [Matrix.mul_assoc]
          _ = U*(V*U)^ℓ*V := by rw [hXY]
          _ = (U*V)^(ℓ+1) := (rectangular_exchange_power U V ℓ).symm
      · calc
          (Y*V)*(U*X) = Y*((V*U)*X) := by simp only [Matrix.mul_assoc]
          _ = Y*(X*B) := by rw [hCX]
          _ = (Y*X)*B := (Matrix.mul_assoc _ _ _).symm
          _ = B^ℓ*B := by rw [hYX]
          _ = B^(ℓ+1) := (pow_succ B ℓ).symm

end SourceOnly.FiniteWordLag
