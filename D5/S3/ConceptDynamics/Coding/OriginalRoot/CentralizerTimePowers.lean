/- GID: D5/S3/ConceptDynamics/Coding/OriginalRoot/CentralizerTimePowers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/OriginalRoot/CentralizerTimePowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed integer time powers of a triangle cocycle on monoid units. -/

/- SOURCE ONLY. UNCOMPILED. A consumed algebraic helper. It applies the
EXISTING centralizer_product body, with its original triangle hypothesis.
No numerical cochain calibration is assumed or defined into B.
-/
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleLocalizedConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnly.CentralizerTimePowers

/-- Integer powers of the actual time unit. Only the time unit is required
to commute with A. The other unit U can be arbitrary; no U*V=V*U premise.
This is an algebraic helper consumed by the actual fixed-row application.
-/
theorem translated_value {M : Type*} [Monoid M] (A : M)
    (B : M → M → ZMod 3)
    (htriangle : ∀ R V W, B R (V*W) + B V (W*R) = B (R*V) W)
    (τ U : Mˣ) (hτ : (τ : M) = A) (s : ℤ) :
    B (((τ^s)*U : Mˣ) : M) (↑(((τ^s)*U)⁻¹)*A) =
      B (U : M) (↑U⁻¹*A) +
        (s : ZMod 3) * B (τ : M) (↑τ⁻¹*A) := by
  let b : Mˣ → ZMod 3 := fun V => B (V : M) (↑V⁻¹*A)
  have hp (V W : Mˣ) (hV : Commute (V : M) A) : b (V*W) = b V+b W :=
    SourceOnlyLocalizedCocycle.centralizer_product A B htriangle V W hV
  have h1 : b 1 = 0 := by
    have he := hp 1 1 (by change (1 : M)*A=A*1; simp)
    rw [one_mul] at he
    exact add_left_cancel (he.symm.trans (add_zero _).symm)
  have ht : Commute (τ : M) A := by rw [hτ]
  have hti : Commute (↑τ⁻¹ : M) A := by
    change (↑τ⁻¹ : M)*A = A*↑τ⁻¹
    rw [← hτ, Units.inv_mul, Units.mul_inv]
  have hinv : b τ⁻¹ = -b τ := by
    have he := hp τ τ⁻¹ ht
    rw [mul_inv_cancel, h1] at he
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he.symm
  have hn (V : Mˣ) (hV : Commute (V : M) A) :
      ∀ n : ℕ, b (V^n*U) = b U + (n : ZMod 3)*b V := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
    | succ n ih =>
        rw [pow_succ', mul_assoc, hp V (V^n*U) hV, ih]
        push_cast
        ring
  change b (τ^s*U) = b U + (s : ZMod 3)*b τ
  cases s with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast] using hn τ ht n
  | negSucc n =>
      rw [zpow_negSucc]
      have he := hn τ⁻¹ hti (n+1)
      rw [hinv] at he
      simpa only [inv_pow, Int.negSucc_eq, Int.cast_neg, Int.cast_natCast,
        Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one, mul_neg, neg_mul] using he

end SourceOnly.CentralizerTimePowers
