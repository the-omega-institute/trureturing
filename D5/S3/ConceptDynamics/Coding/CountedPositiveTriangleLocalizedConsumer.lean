/- GID: D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual orbit triangle for the signed integer gyration lift. -/

import D5.S3.ConceptDynamics.Coding.CountedGyrationPolynomial
import D5.S3.ConceptDynamics.Coding.CountedPositiveTriangleModThree
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnlyLocalizedCocycle

open MvPolynomial

/- Integer evaluations are hypotheses at BOTH tuples. No reduction of the
   rational coefficients into ZMod is attempted. -/
theorem integerValues_mod_three {σ : Type*}
    (P : MvPolynomial σ ℚ) (Q : MvPolynomial σ ℤ)
    (D : ℤ) (hD : D ≠ 0) (e : ℕ) (he : padicValInt 3 D ≤ e)
    (hclear : Q.map (Int.castRingHom ℚ) = C (D : ℚ) * P)
    (x y : σ → ℤ) (a b : ℤ)
    (ha : eval (fun i => (x i : ℚ)) P = (a : ℚ))
    (hb : eval (fun i => (y i : ℚ)) P = (b : ℚ))
    (hxy : ∀ i, (x i : ZMod (3 ^ (e + 1))) = (y i : ZMod (3 ^ (e + 1)))) :
    (a : ZMod 3) = (b : ZMod 3) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hscaled (z : σ → ℤ) (c : ℤ)
      (hc : eval (fun i => (z i : ℚ)) P = (c : ℚ)) : eval z Q = D * c := by
    have hq : (eval z Q : ℚ) = (D : ℚ) * (c : ℚ) := by
      calc
        (eval z Q : ℚ) =
            eval (fun i => (z i : ℚ)) (Q.map (Int.castRingHom ℚ)) := by
          rw [MvPolynomial.eval_map]
          exact MvPolynomial.eval₂_comp (Int.castRingHom ℚ) z Q
        _ = (D : ℚ) * (c : ℚ) := by
          rw [hclear, map_mul, MvPolynomial.eval_C, hc]
    exact_mod_cast hq
  have hfun : (fun i => (x i : ZMod (3 ^ (e + 1)))) =
      (fun i => (y i : ZMod (3 ^ (e + 1)))) := funext hxy
  have hcast : (eval x Q : ZMod (3 ^ (e + 1))) =
      (eval y Q : ZMod (3 ^ (e + 1))) := by
    change (Int.castRingHom (ZMod (3 ^ (e + 1)))) (eval x Q) =
      (Int.castRingHom (ZMod (3 ^ (e + 1)))) (eval y Q)
    rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
    exact congrArg
      (fun z => eval z (Q.map (Int.castRingHom (ZMod (3 ^ (e + 1)))))) hfun
  have hmod := (ZMod.intCast_eq_intCast_iff (eval x Q) (eval y Q)
    (3 ^ (e + 1))).mp hcast
  have hdiv : (3 : ℤ) ^ (e + 1) ∣ D * (b - a) := by
    have hd := hmod.dvd
    rw [hscaled x a ha, hscaled y b hb] at hd
    simpa only [← mul_sub, Nat.cast_pow, Nat.cast_ofNat] using hd
  apply (ZMod.intCast_eq_intCast_iff a b 3).mpr
  apply Int.modEq_iff_dvd.mpr
  by_cases hz : b - a = 0
  · rw [hz]
    exact dvd_zero _
  · have hp : D * (b - a) ≠ 0 := mul_ne_zero hD hz
    have hv := ((padicValInt_dvd_iff (p := 3) (e + 1) (D * (b - a))).mp
      hdiv).resolve_left hp
    rw [padicValInt.mul hD hz] at hv
    have hone : 1 ≤ padicValInt 3 (b - a) := by omega
    simpa only [pow_one] using
      (padicValInt_dvd_iff (p := 3) 1 (b - a)).mpr (Or.inr hone)

/- Dyadic reduction via the universal property of localization, consumed by
   the canonical rectangular cochain.
-/
theorem dyadicReduction (e : ℕ) :
    ∃ rho : Localization.Away (2 : ℤ) →+* ZMod (3 ^ (e + 1)),
      ∀ z : ℤ, rho (algebraMap ℤ (Localization.Away (2 : ℤ)) z) =
        (z : ZMod (3 ^ (e + 1))) := by
  have htwo : IsUnit (2 : ZMod (3 ^ (e + 1))) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow
      (by decide : Nat.Prime 3) (Nat.succ_pos e)).mpr (by norm_num)
  let rho : Localization.Away (2 : ℤ) →+* ZMod (3 ^ (e + 1)) :=
    Localization.awayLift (Int.castRingHom (ZMod (3 ^ (e + 1)))) (2 : ℤ)
      (by simpa using htwo)
  refine ⟨rho, ?_⟩
  intro z
  exact IsLocalization.Away.lift_eq (2 : ℤ) (by simpa using htwo) z

theorem centralizer_product {M : Type*} [Monoid M] (A : M)
    (B : M → M → ZMod 3)
    (htriangle : ∀ R V W, B R (V*W) + B V (W*R) = B (R*V) W)
    (U V : Mˣ) (hU : Commute (U : M) A) :
    B ((U*V : Mˣ) : M) (↑((U*V)⁻¹)*A) =
      B (U : M) (↑U⁻¹*A) + B (V : M) (↑V⁻¹*A) := by
  have hconj : (↑U⁻¹ : M) * (A * (U : M)) = A := by
    rw [← hU.eq, ← mul_assoc, Units.inv_mul, one_mul]
  have hleft : (V : M) * ((↑V⁻¹ : M) * ↑U⁻¹ * A) = (↑U⁻¹ : M) * A := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have hright : ((↑V⁻¹ : M) * ↑U⁻¹ * A) * (U : M) = (↑V⁻¹ : M) * A := by
    simpa only [mul_assoc] using congrArg (fun x : M => (↑V⁻¹ : M) * x) hconj
  change B ((U : M)*(V : M)) ((↑V⁻¹ : M)*↑U⁻¹*A) = _
  rw [← htriangle, hleft, hright]


end SourceOnlyLocalizedCocycle

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

/-- The signed integer lift on natural matrices gives the original forward
orbit-offset residue, including zero entries and empty dimensions. -/
theorem integerGyrationValue_nat_mod_three {n m d : ℕ} [NeZero d]
    (hd : 3 ∣ d) (R : CountMat n m) (S : CountMat m n) :
    (integerGyrationValue d (R.map (Nat.castRingHom ℤ))
      (S.map (Nat.castRingHom ℤ)) : ZMod 3) =
      ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) R S) := by
  have h : relativeForwardGyration (d := d) R S =
      (orderTypeGyrationLift (d := d)
        (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => S ji.1 ji.2)) : ZMod d) :=
    relativeForwardGyration_eq_order_types
      (Sum.elim (fun ij => R ij.1 ij.2) (fun ji => S ji.1 ji.2))
  rw [integerGyrationValue_nat, h, map_intCast]

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
