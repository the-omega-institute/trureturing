/- GID: D5/S3/Arith/GoldenApparition
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci entry point p divides F(p-eps) and F(p)=eps mod p via golden Frobenius. -/

import D5.S1.Scale.Fibonacci
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Int.Fib.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace D5.S3.Arith.GoldenApparition

open D5.S0.Carrier
open D5.S1.Scale

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

structure GoldenMod (p : ℕ) where
  a : ZMod p
  b : ZMod p
  deriving DecidableEq

namespace GoldenMod

variable {p : ℕ}

instance : Zero (GoldenMod p) := ⟨⟨0, 0⟩⟩
instance : One (GoldenMod p) := ⟨⟨1, 0⟩⟩
instance : Add (GoldenMod p) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg (GoldenMod p) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Mul (GoldenMod p) :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b,
    x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[ext] theorem ext {x y : GoldenMod p} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem a_zero : (0 : GoldenMod p).a = 0 := rfl
@[simp] theorem b_zero : (0 : GoldenMod p).b = 0 := rfl
@[simp] theorem a_one : (1 : GoldenMod p).a = 1 := rfl
@[simp] theorem b_one : (1 : GoldenMod p).b = 0 := rfl
@[simp] theorem a_add (x y : GoldenMod p) : (x + y).a = x.a + y.a := rfl
@[simp] theorem b_add (x y : GoldenMod p) : (x + y).b = x.b + y.b := rfl
@[simp] theorem a_neg (x : GoldenMod p) : (-x).a = -x.a := rfl
@[simp] theorem b_neg (x : GoldenMod p) : (-x).b = -x.b := rfl
@[simp] theorem a_mul (x y : GoldenMod p) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem b_mul (x y : GoldenMod p) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

instance addCommGroup : AddCommGroup (GoldenMod p) := by
  refine
    { sub := fun x y => x + -y
      nsmul := @nsmulRec (GoldenMod p) ⟨0⟩ ⟨(· + ·)⟩
      zsmul := @zsmulRec (GoldenMod p) ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
        (@nsmulRec (GoldenMod p) ⟨0⟩ ⟨(· + ·)⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

instance addGroupWithOne : AddGroupWithOne (GoldenMod p) :=
  { addCommGroup with }

@[simp] theorem a_natCast (n : ℕ) : (n : GoldenMod p).a = n := by
  induction n with
  | zero => simp only [Nat.cast_zero, a_zero]
  | succ n ih => simpa using congrArg (fun z : ZMod p => z + 1) ih

@[simp] theorem b_natCast (n : ℕ) : (n : GoldenMod p).b = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa using ih

@[simp] theorem a_intCast (z : ℤ) : (z : GoldenMod p).a = z := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp

@[simp] theorem b_intCast (z : ℤ) : (z : GoldenMod p).b = 0 := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp

instance : CommRing (GoldenMod p) := by
  refine
    { addGroupWithOne with
      npow := @npowRec (GoldenMod p) ⟨1⟩ ⟨(· * ·)⟩
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      add_comm := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

instance : CharP (GoldenMod p) p where
  cast_eq_zero_iff n := by
    constructor
    · intro h
      apply (CharP.cast_eq_zero_iff (ZMod p) p n).mp
      simpa using congrArg GoldenMod.a h
    · intro h
      ext <;> simp [(CharP.cast_eq_zero_iff (ZMod p) p n).mpr h]

def phi : GoldenMod p := ⟨0, 1⟩

def scalar (p : ℕ) : ZMod p →+* GoldenMod p where
  toFun z := ⟨z, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

@[simp] theorem scalar_a (z : ZMod p) : (scalar p z).a = z := rfl
@[simp] theorem scalar_b (z : ZMod p) : (scalar p z).b = 0 := rfl

theorem natCast_eq_scalar (n : ℕ) :
    (n : GoldenMod p) = scalar p (n : ZMod p) := by
  ext <;> simp

theorem intCast_eq_scalar (z : ℤ) :
    (z : GoldenMod p) = scalar p (z : ZMod p) := by
  ext <;> simp

def reduce (p : ℕ) : GoldenInt →+* GoldenMod p where
  toFun x := ⟨x.a, x.b⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

end GoldenMod

private theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hpneTwo : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hdiv
  exact hpneTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdiv)

private theorem golden_frobenius_relation {p : ℕ} (hp : p.Prime) (hpneTwo : p ≠ 2) :
    (2 : GoldenMod p) * GoldenMod.phi ^ p - 1 =
      (legendreSym 5 p : GoldenMod p) * ((2 : GoldenMod p) * GoldenMod.phi - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  let delta : GoldenMod p := (2 : GoldenMod p) * GoldenMod.phi - 1
  have hpOdd : Odd p := hp.odd_of_ne_two hpneTwo
  have htwoScalar : (2 : GoldenMod p) = GoldenMod.scalar p (2 : ZMod p) := by
    calc
      (2 : GoldenMod p) = ((2 : ℕ) : GoldenMod p) :=
        (Nat.cast_ofNat (R := GoldenMod p)).symm
      _ = GoldenMod.scalar p ((2 : ℕ) : ZMod p) :=
        GoldenMod.natCast_eq_scalar (p := p) 2
      _ = GoldenMod.scalar p (2 : ZMod p) := by
        rw [Nat.cast_ofNat]
  have hdelta : delta = (⟨-1, 2⟩ : GoldenMod p) := by
    dsimp [delta]
    rw [htwoScalar]
    ext <;>
      simp only [sub_eq_add_neg, GoldenMod.a_add, GoldenMod.b_add,
        GoldenMod.a_neg, GoldenMod.b_neg, GoldenMod.a_mul, GoldenMod.b_mul,
        GoldenMod.scalar_a, GoldenMod.scalar_b, GoldenMod.a_one, GoldenMod.b_one,
        GoldenMod.phi]
    · ring
    · ring
  have hdeltaSq : delta ^ 2 = GoldenMod.scalar p 5 := by
    rw [hdelta]
    ext <;>
      simp only [pow_two, GoldenMod.a_mul, GoldenMod.b_mul,
        GoldenMod.scalar_a, GoldenMod.scalar_b]
    · ring
    · ring
  have hreciprocity : legendreSym p 5 = legendreSym 5 p := by
    exact legendreSym.quadratic_reciprocity_one_mod_four
      (p := 5) (q := p) (by norm_num) hpneTwo
  have heuler : ((5 : ZMod p) ^ (p / 2)) = (legendreSym 5 p : ZMod p) := by
    rw [← hreciprocity]
    simpa using (legendreSym.eq_pow p 5).symm
  have hdeltaPow : delta ^ p =
      (legendreSym 5 p : GoldenMod p) * delta := by
    calc
      delta ^ p = delta ^ (2 * (p / 2) + 1) := by
        rw [Nat.two_mul_div_two_add_one_of_odd hpOdd]
      _ = (delta ^ 2) ^ (p / 2) * delta := by
        rw [pow_add, pow_one, pow_mul]
      _ = (GoldenMod.scalar p 5) ^ (p / 2) * delta := by rw [hdeltaSq]
      _ = (legendreSym 5 p : GoldenMod p) * delta := by
        congr 1
        rw [GoldenMod.intCast_eq_scalar, ← map_pow]
        exact congrArg (GoldenMod.scalar p) heuler
  have htwoPow : (2 : GoldenMod p) ^ p = 2 := by
    calc
      (2 : GoldenMod p) ^ p = (GoldenMod.scalar p (2 : ZMod p)) ^ p := by
        rw [htwoScalar]
      _ = GoldenMod.scalar p ((2 : ZMod p) ^ p) := by rw [map_pow]
      _ = GoldenMod.scalar p (2 : ZMod p) := by rw [ZMod.pow_card]
      _ = 2 := htwoScalar.symm
  have hdeltaFrob : delta ^ p =
      (2 : GoldenMod p) * GoldenMod.phi ^ p - 1 := by
    dsimp [delta]
    rw [sub_pow_char, mul_pow, htwoPow]
    simp
  exact hdeltaFrob.symm.trans (hdeltaPow.trans (by rfl))

private theorem two_mul_goldenMod_injective {p : ℕ} (hp : p.Prime) (hpneTwo : p ≠ 2) :
    Function.Injective (fun x : GoldenMod p => (2 : GoldenMod p) * x) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x y hxy
  have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp hpneTwo
  have htwoScalar : (2 : GoldenMod p) = GoldenMod.scalar p (2 : ZMod p) := by
    calc
      (2 : GoldenMod p) = ((2 : ℕ) : GoldenMod p) :=
        (Nat.cast_ofNat (R := GoldenMod p)).symm
      _ = GoldenMod.scalar p ((2 : ℕ) : ZMod p) :=
        GoldenMod.natCast_eq_scalar (p := p) 2
      _ = GoldenMod.scalar p (2 : ZMod p) := by rw [Nat.cast_ofNat]
  rw [htwoScalar] at hxy
  apply GoldenMod.ext
  · apply mul_left_cancel₀ htwo
    simpa only [GoldenMod.a_mul, GoldenMod.scalar_a, GoldenMod.scalar_b,
      zero_mul, add_zero] using congrArg GoldenMod.a hxy
  · apply mul_left_cancel₀ htwo
    simpa only [GoldenMod.b_mul, GoldenMod.scalar_a, GoldenMod.scalar_b,
      zero_mul, zero_add, add_zero] using congrArg GoldenMod.b hxy

private theorem phi_pow_eq_phi_of_legendre_eq_one {p : ℕ} (hp : p.Prime)
    (hpneTwo : p ≠ 2) (heps : legendreSym 5 p = 1) :
    GoldenMod.phi ^ p = (GoldenMod.phi : GoldenMod p) := by
  apply two_mul_goldenMod_injective hp hpneTwo
  have h := golden_frobenius_relation hp hpneTwo
  rw [heps] at h
  linear_combination h

private theorem phi_pow_eq_one_sub_phi_of_legendre_eq_neg_one {p : ℕ} (hp : p.Prime)
    (hpneTwo : p ≠ 2) (heps : legendreSym 5 p = -1) :
    GoldenMod.phi ^ p = 1 - (GoldenMod.phi : GoldenMod p) := by
  apply two_mul_goldenMod_injective hp hpneTwo
  have h := golden_frobenius_relation hp hpneTwo
  rw [heps] at h
  linear_combination h

@[simp] private theorem reduce_phi (p : ℕ) :
    GoldenMod.reduce p D5.S0.Carrier.phi = GoldenMod.phi := by
  ext <;> norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]

private theorem phi_pow_eq_fib_pair_mod (p n : ℕ) :
    (GoldenMod.phi : GoldenMod p) ^ (n + 1) =
      ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
  have h := congrArg (GoldenMod.reduce p) (golden_phi_pow_eq_fib_pair n)
  have hr : GoldenMod.reduce p
      (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) =
      ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
    apply GoldenMod.ext
    · change (((Nat.fib n : ℕ) : ℤ) : ZMod p) = (Nat.fib n : ZMod p)
      rw [Int.cast_natCast]
    · change (((Nat.fib (n + 1) : ℕ) : ℤ) : ZMod p) =
        (Nat.fib (n + 1) : ZMod p)
      rw [Int.cast_natCast]
  simpa only [map_pow, reduce_phi, hr] using h

/-- For every prime `p` not dividing five, the Fibonacci entry point divides
`p - (p / 5)`, and the `p`-th Fibonacci number is `(p / 5)` modulo `p`. -/
theorem fibonacci_apparition_entry_point {p : ℕ} (hp : p.Prime) (hpNotDvdFive : ¬ p ∣ 5) :
    ((Int.fib ((p : ℤ) - legendreSym 5 p) : ℤ) : ZMod p) = 0 ∧
      ((Int.fib (p : ℤ) : ℤ) : ZMod p) = (legendreSym 5 p : ZMod p) := by
  have hpneFive : p ≠ 5 := by
    intro hpFive
    subst p
    exact hpNotDvdFive dvd_rfl
  by_cases hpTwo : p = 2
  · subst p
    have heps : legendreSym 5 2 = -1 := by
      apply (legendreSym.eq_neg_one_iff' (p := 5) (a := 2)).2
      decide
    have heps' : legendreSym 5 ((2 : ℕ) : ℤ) = -1 := by
      simpa only [Nat.cast_ofNat] using heps
    rw [heps']
    constructor
    · norm_num [Int.fib] <;> decide
    · have htwoInt : ((2 : ℕ) : ℤ) = 2 := Nat.cast_ofNat
      rw [htwoInt, Int.fib_two]
      decide
  · letI : Fact p.Prime := ⟨hp⟩
    have hpModFive : (p : ZMod 5) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hFiveDvd
      have hpFive : p = 5 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hFiveDvd).symm
      exact hpneFive hpFive
    have hpOne : 1 ≤ p := hp.one_le
    have hpowCoords : (GoldenMod.phi : GoldenMod p) ^ p =
        ⟨(Nat.fib (p - 1) : ZMod p), (Nat.fib p : ZMod p)⟩ := by
      have h := phi_pow_eq_fib_pair_mod p (p - 1)
      simpa only [Nat.sub_add_cancel hpOne] using h
    rcases legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpModFive with heps | heps
    · have hphi := phi_pow_eq_phi_of_legendre_eq_one hp hpTwo heps
      have hcoords :
          (⟨(Nat.fib (p - 1) : ZMod p), (Nat.fib p : ZMod p)⟩ : GoldenMod p) =
            GoldenMod.phi := hpowCoords.symm.trans hphi
      have ha : (Nat.fib (p - 1) : ZMod p) = 0 := by
        simpa only [GoldenMod.phi] using congrArg GoldenMod.a hcoords
      have hb : (Nat.fib p : ZMod p) = 1 := by
        simpa only [GoldenMod.phi] using congrArg GoldenMod.b hcoords
      have hindex : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
      constructor
      · rw [heps, hindex, Int.fib_natCast, Int.cast_natCast]
        exact ha
      · rw [Int.fib_natCast, Int.cast_natCast, heps, Int.cast_one]
        exact hb
    · have hphi := phi_pow_eq_one_sub_phi_of_legendre_eq_neg_one hp hpTwo heps
      have hcoords :
          (⟨(Nat.fib (p - 1) : ZMod p), (Nat.fib p : ZMod p)⟩ : GoldenMod p) =
            1 - GoldenMod.phi := hpowCoords.symm.trans hphi
      have hb : (Nat.fib p : ZMod p) = -1 := by
        have h := congrArg GoldenMod.b hcoords
        simpa only [sub_eq_add_neg, GoldenMod.b_add, GoldenMod.b_neg,
          GoldenMod.b_one, GoldenMod.phi, zero_add] using h
      have hnext := phi_pow_eq_fib_pair_mod p p
      have hpowNext : (GoldenMod.phi : GoldenMod p) ^ (p + 1) =
          (1 - GoldenMod.phi) * GoldenMod.phi := by
        rw [pow_succ, hphi]
      have hnextCoords :
          (⟨(Nat.fib p : ZMod p), (Nat.fib (p + 1) : ZMod p)⟩ : GoldenMod p) =
            (1 - GoldenMod.phi) * GoldenMod.phi := hnext.symm.trans hpowNext
      have hbNext : (Nat.fib (p + 1) : ZMod p) = 0 := by
        have h := congrArg GoldenMod.b hnextCoords
        simpa only [sub_eq_add_neg, GoldenMod.b_mul, GoldenMod.a_add,
          GoldenMod.b_add, GoldenMod.a_neg, GoldenMod.b_neg, GoldenMod.a_one,
          GoldenMod.b_one, GoldenMod.phi, zero_add, zero_mul, one_mul,
          neg_mul, neg_zero, add_zero, add_neg_cancel] using h
      have hindex : (p : ℤ) - (-1) = ((p + 1 : ℕ) : ℤ) := by omega
      constructor
      · rw [heps, hindex, Int.fib_natCast, Int.cast_natCast]
        exact hbNext
      · rw [Int.fib_natCast, Int.cast_natCast, heps, Int.cast_neg, Int.cast_one]
        exact hb


end D5.S3.Arith.GoldenApparition
