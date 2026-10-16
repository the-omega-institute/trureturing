/- GID: D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual orbit triangle for the signed integer gyration lift. -/

import D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleModThree
import D5.S3.ConceptDynamics.Coding.LocalizedCocycle

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

/-- The SAME signed polynomial lift at a compatible rectangular integer pair.
    Signed entries and zero dimensions are allowed.  -/
def integerGyrationValue {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ) : ℤ :=
  signedGyrationLift (d := d)
    (Sum.elim (fun ij => R ij.1 ij.2) (fun ij => S ij.1 ij.2))

private theorem integerGyrationValue_nat {n m d : ℕ} [NeZero d]
    (R : CountMat n m) (S : CountMat m n) :
    integerGyrationValue d (R.map (Nat.castRingHom ℤ)) (S.map (Nat.castRingHom ℤ)) =
      orderTypeGyrationLift (d := d) (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => S ji.1 ji.2)) := by
  have he : Sum.elim
      (fun ij : Fin n × Fin m => (R.map (Nat.castRingHom ℤ)) ij.1 ij.2)
      (fun ij : Fin m × Fin n => (S.map (Nat.castRingHom ℤ)) ij.1 ij.2) =
      (fun e => ((Sum.elim (fun ij => R ij.1 ij.2) (fun ji => S ji.1 ji.2)) e : ℤ)) := by
    funext e
    cases e <;> rfl
  rw [integerGyrationValue,he]
  classical
  simp only [signedGyrationLift, orderTypeGyrationLift, Ring.choose_natCast, Nat.cast_prod]

/-- Concrete integer lifts of the actual orbit triangle. No polynomial triangle
    or signed-domain cocycle is postulated. -/
theorem orderTypeGyrationLift_positive_triangle_mod_three
    {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R : CountMat n m) (U : CountMat m p) (V : CountMat p n) :
    (orderTypeGyrationLift (d := d) (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => (U*V) ji.1 ji.2)) : ZMod 3) +
      (orderTypeGyrationLift (d := d) (Sum.elim (fun ij => U ij.1 ij.2) (fun ji => (V*R) ji.1 ji.2)) : ZMod 3) =
    (orderTypeGyrationLift (d := d) (Sum.elim (fun ij => (R*U) ij.1 ij.2) (fun ji => V ji.1 ji.2)) : ZMod 3) := by
  have ht := relativeForwardGyration_positive_triangle_mod_three hd R U V
  have h₁ : relativeForwardGyration (d := d) R (U*V) =
      (orderTypeGyrationLift (d := d)
        (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => (U*V) ji.1 ji.2)) : ZMod d) :=
    relativeForwardGyration_eq_order_types
      (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => (U*V) ji.1 ji.2))
  have h₂ : relativeForwardGyration (d := d) U (V*R) =
      (orderTypeGyrationLift (d := d)
        (Sum.elim (fun ij => U ij.1 ij.2) (fun ji => (V*R) ji.1 ji.2)) : ZMod d) :=
    relativeForwardGyration_eq_order_types
      (Sum.elim (fun ij => U ij.1 ij.2) (fun ji => (V*R) ji.1 ji.2))
  have h₃ : relativeForwardGyration (d := d) (R*U) V =
      (orderTypeGyrationLift (d := d)
        (Sum.elim (fun ij => (R*U) ij.1 ij.2) (fun ji => V ji.1 ji.2)) : ZMod d) :=
    relativeForwardGyration_eq_order_types
      (Sum.elim (fun ij => (R*U) ij.1 ij.2) (fun ji => V ji.1 ji.2))
  rw [h₁,h₂,h₃] at ht
  simpa only [map_intCast] using ht

/-- Every nonnegative integer matrix is recovered entrywise from its toNat.
    Matrix.map_mul transports the ORIGINAL triangle; no entry interpolation is used. -/
theorem integerGyrationValue_nonnegative_triangle
    {n m p d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (R : Matrix (Fin n) (Fin m) ℤ) (U : Matrix (Fin m) (Fin p) ℤ)
    (V : Matrix (Fin p) (Fin n) ℤ)
    (hR : ∀ i j, 0 ≤ R i j) (hU : ∀ i j, 0 ≤ U i j) (hV : ∀ i j, 0 ≤ V i j) :
    (integerGyrationValue d R (U*V) : ZMod 3) +
      (integerGyrationValue d U (V*R) : ZMod 3) =
    (integerGyrationValue d (R*U) V : ZMod 3) := by
  let R' : CountMat n m := fun i j => (R i j).toNat
  let U' : CountMat m p := fun i j => (U i j).toNat
  let V' : CountMat p n := fun i j => (V i j).toNat
  have hR' : R'.map (Nat.castRingHom ℤ) = R := by
    ext i j; exact Int.toNat_of_nonneg (hR i j)
  have hU' : U'.map (Nat.castRingHom ℤ) = U := by
    ext i j; exact Int.toNat_of_nonneg (hU i j)
  have hV' : V'.map (Nat.castRingHom ℤ) = V := by
    ext i j; exact Int.toNat_of_nonneg (hV i j)
  have h₁ := integerGyrationValue_nat (d := d) R' (U'*V')
  have h₂ := integerGyrationValue_nat (d := d) U' (V'*R')
  have h₃ := integerGyrationValue_nat (d := d) (R'*U') V'
  rw [Matrix.map_mul,hR',hU',hV'] at h₁
  rw [Matrix.map_mul,hR',hU',hV'] at h₂
  rw [Matrix.map_mul,hR',hU',hV'] at h₃
  rw [h₁,h₂,h₃]
  exact orderTypeGyrationLift_positive_triangle_mod_three hd R' U' V'


end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
