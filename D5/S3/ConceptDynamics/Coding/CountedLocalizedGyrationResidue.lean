/- GID: D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular localized gyration and agreement with actual forward orbit offsets. -/

import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleLocalizedConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

abbrev GyrationDyadic := Localization.Away (2 : ℤ)

/-- Exactly the positive representatives used by the supplied transfer proof. -/
def gyrationPositiveLift {n m : ℕ} {L : Type*} [CommRing L] (e : ℕ)
    (rho : L →+* ZMod (3 ^ (e + 1))) (R : Matrix (Fin n) (Fin m) L) :
    Matrix (Fin n) (Fin m) ℤ :=
  fun i j => ((rho (R i j)).val : ℤ) + (3 ^ (e + 1) : ℕ)

private theorem gyrationPositiveLift_pos {n m : ℕ} {L : Type*} [CommRing L]
    (e : ℕ) (rho : L →+* ZMod (3 ^ (e + 1)))
    (R : Matrix (Fin n) (Fin m) L) :
    ∀ i j, 0 < gyrationPositiveLift e rho R i j := by
  intro i j
  dsimp [gyrationPositiveLift]
  positivity

private theorem gyrationPositiveLift_map {n m : ℕ} {L : Type*} [CommRing L]
    (e : ℕ) (rho : L →+* ZMod (3 ^ (e + 1)))
    (R : Matrix (Fin n) (Fin m) L) :
    (gyrationPositiveLift e rho R).map (Int.castRingHom (ZMod (3 ^ (e + 1)))) =
      R.map rho := by
  ext i j
  change (((((rho (R i j)).val : ℤ) + (3 ^ (e + 1) : ℕ) : ℤ) :
    ZMod (3 ^ (e + 1)))) = rho (R i j)
  simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self,
    add_zero, ZMod.natCast_zmod_val]

/-- This is a fixed positive-lift cochain of the ACTUAL counted polynomial. -/
def canonicalLocalizedGyration {n m : ℕ} (d : ℕ) [NeZero d]
    {L : Type*} [CommRing L] (e : ℕ) (rho : L →+* ZMod (3 ^ (e + 1)))
    (R : Matrix (Fin n) (Fin m) L) (S : Matrix (Fin m) (Fin n) L) : ZMod 3 :=
  (integerGyrationValue d (gyrationPositiveLift e rho R)
    (gyrationPositiveLift e rho S) : ZMod 3)

/-- The nonpositive entries in R',S' are allowed. This extends the supplied
strictly-positive agreement using integer values at BOTH signed tuples,
not by postulating a stronger property of the existential transfer. -/
theorem canonicalLocalizedGyration_signed_agreement
    {n m d : ℕ} [NeZero d] {L : Type*} [CommRing L]
    (e : ℕ) (he : padicValInt 3 (((2 * d).factorial : ℕ) : ℤ) ≤ e)
    (rho : L →+* ZMod (3 ^ (e + 1)))
    (R : Matrix (Fin n) (Fin m) L) (S : Matrix (Fin m) (Fin n) L)
    (R' : Matrix (Fin n) (Fin m) ℤ) (S' : Matrix (Fin m) (Fin n) ℤ)
    (hR : R'.map (Int.castRingHom (ZMod (3 ^ (e + 1)))) = R.map rho)
    (hS : S'.map (Int.castRingHom (ZMod (3 ^ (e + 1)))) = S.map rho) :
    canonicalLocalizedGyration d e rho R S =
      (integerGyrationValue d R' S' : ZMod 3) := by
  apply SourceOnlyLocalizedCocycle.integerValues_mod_three
    (rationalGyrationPolynomial n m d) (integralGyrationNumerator n m d)
    (((2 * d).factorial : ℕ) : ℤ)
    (by exact_mod_cast Nat.factorial_ne_zero (2 * d)) e he
    (integralGyrationNumerator_map n m d)
    (Sum.elim
      (fun ij => gyrationPositiveLift e rho R ij.1 ij.2)
      (fun ij => gyrationPositiveLift e rho S ij.1 ij.2))
    (Sum.elim (fun ij => R' ij.1 ij.2) (fun ij => S' ij.1 ij.2))
    (integerGyrationValue d (gyrationPositiveLift e rho R)
      (gyrationPositiveLift e rho S))
    (integerGyrationValue d R' S')
    (by exact rationalGyrationPolynomial_eval_signed _)
    (by exact rationalGyrationPolynomial_eval_signed _)
  intro t
  rcases t with ⟨i,j⟩ | ⟨i,j⟩
  · exact congrArg (fun M : Matrix (Fin n) (Fin m) (ZMod (3 ^ (e + 1))) => M i j)
      ((gyrationPositiveLift_map e rho R).trans hR.symm)
  · exact congrArg (fun M : Matrix (Fin m) (Fin n) (ZMod (3 ^ (e + 1))) => M i j)
      ((gyrationPositiveLift_map e rho S).trans hS.symm)

/-- The SAME polynomial cochain forms a family over three compatible sizes.
Lift the three factors separately and use signed agreement on their products.
Products need only be nonnegative: an empty intermediate type gives zeros.
No square existential witness or stabilization is used. -/
theorem canonicalLocalizedGyration_triangle
    {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    {L : Type*} [CommRing L]
    (e : ℕ) (he : padicValInt 3 (((2 * d).factorial : ℕ) : ℤ) ≤ e)
    (rho : L →+* ZMod (3 ^ (e + 1)))
    (R : Matrix (Fin n) (Fin m) L) (U : Matrix (Fin m) (Fin p) L)
    (V : Matrix (Fin p) (Fin n) L) :
    canonicalLocalizedGyration d e rho R (U*V) +
      canonicalLocalizedGyration d e rho U (V*R) =
    canonicalLocalizedGyration d e rho (R*U) V := by
  have hUV :
      (gyrationPositiveLift e rho U * gyrationPositiveLift e rho V).map
          (Int.castRingHom (ZMod (3 ^ (e + 1)))) = (U*V).map rho := by
    rw [Matrix.map_mul, gyrationPositiveLift_map, gyrationPositiveLift_map,
      Matrix.map_mul]
  have hVR :
      (gyrationPositiveLift e rho V * gyrationPositiveLift e rho R).map
          (Int.castRingHom (ZMod (3 ^ (e + 1)))) = (V*R).map rho := by
    rw [Matrix.map_mul, gyrationPositiveLift_map, gyrationPositiveLift_map,
      Matrix.map_mul]
  have hRU :
      (gyrationPositiveLift e rho R * gyrationPositiveLift e rho U).map
          (Int.castRingHom (ZMod (3 ^ (e + 1)))) = (R*U).map rho := by
    rw [Matrix.map_mul, gyrationPositiveLift_map, gyrationPositiveLift_map,
      Matrix.map_mul]
  have h₁ := canonicalLocalizedGyration_signed_agreement (d := d) e he rho
    R (U*V) (gyrationPositiveLift e rho R)
      (gyrationPositiveLift e rho U * gyrationPositiveLift e rho V)
    (gyrationPositiveLift_map e rho R) hUV
  have h₂ := canonicalLocalizedGyration_signed_agreement (d := d) e he rho
    U (V*R) (gyrationPositiveLift e rho U)
      (gyrationPositiveLift e rho V * gyrationPositiveLift e rho R)
    (gyrationPositiveLift_map e rho U) hVR
  have h₃ := canonicalLocalizedGyration_signed_agreement (d := d) e he rho
    (R*U) V (gyrationPositiveLift e rho R * gyrationPositiveLift e rho U)
      (gyrationPositiveLift e rho V) hRU (gyrationPositiveLift_map e rho V)
  rw [h₁, h₂, h₃]
  exact integerGyrationValue_nonnegative_triangle hd
    (gyrationPositiveLift e rho R) (gyrationPositiveLift e rho U)
    (gyrationPositiveLift e rho V)
    (fun i j => le_of_lt (gyrationPositiveLift_pos e rho R i j))
    (fun i j => le_of_lt (gyrationPositiveLift_pos e rho U i j))
    (fun i j => le_of_lt (gyrationPositiveLift_pos e rho V i j))

/-- The dyadic reduction has its actual localization origin. -/
def gyrationDyadicReduction (d : ℕ) :
    GyrationDyadic →+* ZMod (3 ^
      (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ) + 1)) :=
  Classical.choose (SourceOnlyLocalizedCocycle.dyadicReduction
    (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)))

def dyadicGyration {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) GyrationDyadic)
    (S : Matrix (Fin m) (Fin n) GyrationDyadic) : ZMod 3 :=
  canonicalLocalizedGyration d
    (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)) (gyrationDyadicReduction d) R S


/-- Localization agrees with the actual forward orbit-offset sum at every
nonnegative rectangular matrix pair and period divisible by three. -/
theorem dyadicGyration_nonnegative {n m d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R : CountMat n m) (S : CountMat m n) :
    dyadicGyration d
      ((R.map (Nat.castRingHom ℤ)).map (algebraMap ℤ GyrationDyadic))
      ((S.map (Nat.castRingHom ℤ)).map (algebraMap ℤ GyrationDyadic)) =
      ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) R S) := by
  calc
    _ = (integerGyrationValue d (R.map (Nat.castRingHom ℤ))
        (S.map (Nat.castRingHom ℤ)) : ZMod 3) :=
      canonicalLocalizedGyration_signed_agreement
        (padicValInt 3 (((2 * d).factorial : ℕ) : ℤ)) le_rfl
        (gyrationDyadicReduction d) _ _ _ _ (by ext i j; simp) (by ext i j; simp)
    _ = _ := integerGyrationValue_nat_mod_three hd R S


end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
