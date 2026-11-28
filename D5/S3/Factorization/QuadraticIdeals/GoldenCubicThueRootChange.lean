/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicThueRootChange
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: A monic root change and exact local arithmetic for the native Thue cubic. -/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Field.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Positivity

/-! Explicit coordinate inversion, two charts at two, and discriminant readouts. -/

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange

variable {K : Type*} [CommRing K]

/-- Depressing the native Thue coordinate without introducing a
cube root or choosing a complex embedding. -/
theorem depressed_root (A D P x : K)
    (hn : A^2-A*D+D^2=P^2)
    (hx : A*x^3-3*D*x^2+3*(D-A)*x+A=0) :
    (A*x-D)^3-3*P^2*(A*x-D)+(A-2*D)*P^2=0 := by
  linear_combination A^2*hx + (3*(A*x-D)-(A-2*D))*hn

/-- The native coefficient identity controlling the second generator's
discriminant and the shifted mod-nine check. -/
theorem norm_complement (A D P : K) (hn : A^2-A*D+D^2=P^2) :
    4*P^2-(A-2*D)^2=3*A^2 := by
  linear_combination -4*hn

section Field

variable {F : Type*} [Field F]

/-- Squaring the depressed root and dividing by P gives a monic
integral-coefficient model when the input coefficients are integral. -/
theorem monic_root (P E y : F) (hP : P≠0)
    (hy : y^3-3*P^2*y+E*P^2=0) :
    let t := y^2/P;
    t^3-6*P*t^2+9*P^2*t-E^2*P=0 := by
  let t := y^2/P
  have ht : P*t=y^2 := by dsimp [t]; field_simp
  have hlin : y*(3*P-t)=E*P := by
    apply mul_left_cancel₀ hP
    linear_combination -hy - y*ht
  have hsq := congrArg (fun z : F => z^2) hlin
  change t^3-6*P*t^2+9*P^2*t-E^2*P=0
  apply mul_left_cancel₀ hP
  linear_combination hsq + (3*P-t)^2*ht

/-- The monic root recovers the original coordinate by a rational
expression. In particular the field generated does not shrink. -/
theorem root_explicit_inverse (A D P x : F) (hP : P≠0) (hA : A≠0)
    (hE : A-2*D≠0) (hn : A^2-A*D+D^2=P^2)
    (hx : A*x^3-3*D*x^2+3*(D-A)*x+A=0) :
    let t := (A*x-D)^2/P
    3*P-t≠0 ∧ x=(D+(A-2*D)*P/(3*P-t))/A := by
  let y := A*x-D
  let E := A-2*D
  let t := y^2/P
  change 3*P-t≠0 ∧ x=(D+E*P/(3*P-t))/A
  have hy : y^3-3*P^2*y+E*P^2=0 := depressed_root A D P x hn hx
  have ht : P*t=y^2 := by dsimp [t]; field_simp
  have hlin : y*(3*P-t)=E*P := by
    apply mul_left_cancel₀ hP
    linear_combination -hy - y*ht
  have hne : 3*P-t≠0 := by
    intro hz
    rw [hz,mul_zero] at hlin
    exact (mul_ne_zero hE hP) hlin.symm
  have hr : y=E*P/(3*P-t) := (eq_div_iff hne).mpr hlin
  refine ⟨hne,(eq_div_iff hA).mpr ?_⟩
  rw [←hr]
  dsimp only [y]
  ring

end Field

section Adjoin

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- The original native root and the new monic root generate exactly
the same intermediate field, in either direction. -/
theorem same_simple_field (A D P : k) (x : L) (hA : A ≠ 0) (hP : P ≠ 0)
    (hE : A-2*D ≠ 0) (hn : A^2-A*D+D^2=P^2)
    (hx : let a := algebraMap k L A
          let d := algebraMap k L D
          a*x^3-3*d*x^2+3*(d-a)*x+a=0) :
    let a := algebraMap k L A; let d := algebraMap k L D; let p := algebraMap k L P;
    IntermediateField.adjoin k ({(a*x-d)^2/p} : Set L) =
      IntermediateField.adjoin k ({x} : Set L) := by
  let a := algebraMap k L A
  let d := algebraMap k L D
  let p := algebraMap k L P
  let t := (a*x-d)^2/p
  let X := IntermediateField.adjoin k ({x} : Set L)
  let T := IntermediateField.adjoin k ({t} : Set L)
  have hn' : a^2-a*d+d^2=p^2 := by
    simpa only [map_add, map_sub, map_mul, map_pow] using congrArg (algebraMap k L) hn
  have hp' : p ≠ 0 := (map_ne_zero (algebraMap k L)).mpr hP
  have ha' : a ≠ 0 := (map_ne_zero (algebraMap k L)).mpr hA
  have he' : a-2*d ≠ 0 := by
    simpa only [map_sub, map_mul, map_ofNat] using (map_ne_zero (algebraMap k L)).mpr hE
  have hInv := (root_explicit_inverse a d p x hp' ha' he' hn' hx).2
  change T = X
  apply le_antisymm
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    have hX : x ∈ X := IntermediateField.mem_adjoin_simple_self k x
    apply X.div_mem _ (X.algebraMap_mem P)
    have hu := X.sub_mem (X.mul_mem (X.algebraMap_mem A) hX) (X.algebraMap_mem D)
    simpa only [zpow_natCast] using X.pow_mem hu (↑(2:ℕ):ℤ)
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    have hT : t ∈ T := IntermediateField.mem_adjoin_simple_self k t
    rw [hInv]
    apply T.div_mem _ (T.algebraMap_mem A)
    apply T.add_mem (T.algebraMap_mem D)
    apply T.div_mem
    · apply T.mul_mem _ (T.algebraMap_mem P)
      exact T.sub_mem (T.algebraMap_mem A) (T.mul_mem (T.natCast_mem 2) (T.algebraMap_mem D))
    · exact T.sub_mem (T.mul_mem (T.natCast_mem 3) (T.algebraMap_mem P)) hT

end Adjoin



end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange
open Polynomial

/-- When the primary square-role coordinates are odd, the native
homogeneous form has the three distinct projective zeros over F₂. -/
theorem binary_form_mod_two (a b u v : ZMod 2) (ha : a=1) (hb : b=1) :
    let A := a^2-b^2; let D := 2*a*b-b^2;
    A*u^3-3*D*u^2*v+3*(D-A)*u*v^2+A*v^3 = u*v*(u+v) := by
  subst a
  subst b
  have h : ∀ x y : ZMod 2,
      ((1:ZMod 2)^2-1^2)*x^3-3*(2*(1:ZMod 2)*1-1^2)*x^2*y+
        3*((2*(1:ZMod 2)*1-1^2)-((1:ZMod 2)^2-1^2))*x*y^2+
          ((1:ZMod 2)^2-1^2)*y^3 = x*y*(x+y) := by decide
  exact h u v

/-- The dehomogenized product in either chart has derivative one.
This includes the root at infinity via the other chart. -/
theorem binary_form_mod_two_chart_derivative :
    derivative ((X : (ZMod 2)[X])*(X+1)) = 1 := by
  rw [derivative_mul, derivative_add, derivative_X, derivative_one, add_zero, one_mul, mul_one]
  have hh : (2 : (ZMod 2)[X]) = 0 := by
    have hz := congrArg (C : ZMod 2 →+* (ZMod 2)[X]) (show (2:ZMod 2)=0 by decide)
    simpa only [map_ofNat, map_zero] using hz
  calc
    (X+1 : (ZMod 2)[X])+X = 2*X+1 := by ring
    _ = 1 := by rw [hh, zero_mul, zero_add]


end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange

private theorem square_valuation (p : ℕ) [Fact p.Prime] (x : ℤ) (hx : x ≠ 0) :
    padicValInt p (x^2) = padicValInt p x + padicValInt p x := by
  rw [pow_two, padicValInt.mul hx hx]

/-- Exact arithmetic valuations of the integer discriminant expression
for the monic model. Local maximality is a separate field-theoretic step. -/
theorem discriminant_arithmetic_depths (p : ℕ) (A E : ℤ) (hp : p.Prime) (hp3 : p ≠ 3)
    (hAp : ¬ (p:ℤ) ∣ A) (hEp : ¬ (p:ℤ) ∣ E)
    (hA3 : ¬ (3:ℤ) ∣ A) (hE3 : ¬ (3:ℤ) ∣ E) :
    padicValInt p (81*A^2*E^2*(p:ℤ)^2) = 2 ∧
      padicValInt 3 (81*A^2*E^2*(p:ℤ)^2) = 4 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hnA : A ≠ 0 := fun h => hAp (h ▸ dvd_zero _)
  have hnE : E ≠ 0 := fun h => hEp (h ▸ dvd_zero _)
  have hnp : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h81p : ¬ (p:ℤ) ∣ (81:ℤ) := by
    intro h
    have hn : p ∣ (3:ℕ)^4 := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
      (hp.dvd_of_dvd_pow hn))
  have h3p : ¬ (3:ℤ) ∣ (p:ℤ) := by
    intro h
    have hn : (3:ℕ) ∣ p := by exact_mod_cast h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp hn).symm
  have h81 : padicValInt 3 (81:ℤ) = 4 := by
    change padicValInt 3 (↑((3:ℕ)^4):ℤ) = 4
    rw [padicValInt.of_nat, padicValNat.prime_pow]
  have hn81 : (81:ℤ) ≠ 0 := by decide
  have hn81A : (81:ℤ)*A^2 ≠ 0 := mul_ne_zero hn81 (pow_ne_zero _ hnA)
  have hn81AE : (81:ℤ)*A^2*E^2 ≠ 0 := mul_ne_zero hn81A (pow_ne_zero _ hnE)
  constructor
  · rw [padicValInt.mul hn81AE (pow_ne_zero 2 hnp),
      padicValInt.mul hn81A (pow_ne_zero 2 hnE),
      padicValInt.mul (by decide) (pow_ne_zero 2 hnA),
      square_valuation p A hnA, square_valuation p E hnE, square_valuation p (p:ℤ) hnp,
      padicValInt.eq_zero_of_not_dvd h81p, padicValInt.eq_zero_of_not_dvd hAp,
      padicValInt.eq_zero_of_not_dvd hEp, padicValInt_self]
  · rw [padicValInt.mul hn81AE (pow_ne_zero 2 hnp),
      padicValInt.mul hn81A (pow_ne_zero 2 hnE),
      padicValInt.mul (by decide) (pow_ne_zero 2 hnA),
      square_valuation 3 A hnA, square_valuation 3 E hnE, square_valuation 3 (p:ℤ) hnp,
      h81, padicValInt.eq_zero_of_not_dvd hA3, padicValInt.eq_zero_of_not_dvd hE3,
      padicValInt.eq_zero_of_not_dvd h3p]


end D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueRootChange
