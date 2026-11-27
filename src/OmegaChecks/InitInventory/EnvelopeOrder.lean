module
public import Lean
import all Init.Grind.Ring.Envelope
import all Init.Grind.Module.Envelope

public section

namespace OmegaChecks.InitBoundaries.EnvelopeOrder
open Lean.Grind Std

/-! On the additive group of the two-element field, a translation exchanges the two
off-diagonal comparisons. Any equivalent propositions can serve as those comparisons. -/

@[expose] def parity : Nat → Bool
  | 0 => false
  | n+1 => !(parity n)

local instance xorSemiring : Semiring Bool where
  add := Bool.xor
  mul := Bool.and
  natCast := ⟨parity⟩
  ofNat n := ⟨parity n⟩
  nsmul := ⟨fun n a => parity n && a⟩
  npow := ⟨fun a n => match n with | 0 => true | _+1 => a⟩
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_mul a := rfl
  mul_zero a := by cases a <;> rfl
  pow_zero a := rfl
  pow_succ a n := by cases n <;> cases a <;> rfl
  ofNat_succ n := by
    change (!(parity n)) = Bool.xor (parity n) true
    cases parity n <;> rfl
  ofNat_eq_natCast _ := rfl
  nsmul_eq_natCast_mul _ _ := rfl

@[expose, instance_reducible] def testLE (p q : Prop) : LE Bool :=
  ⟨fun x y => match x, y with
    | false, false | true, true => True
    | false, true => p
    | true, false => q⟩

theorem testPreorder (p q : Prop) : @IsPreorder Bool (testLE p q) :=
  @IsPreorder.mk Bool (testLE p q) (fun a => by cases a <;> exact True.intro)
    (fun a b c h k => by
      cases a <;> cases b <;> cases c <;> first | exact True.intro | exact h | exact k)

theorem testOrdered {p q : Prop} (h : p ↔ q) :
    @OrderedAdd Bool (@instHAdd _ xorSemiring.toAdd) (testLE p q) (testPreorder p q) :=
  @OrderedAdd.mk Bool _ (testLE p q) (testPreorder p q) (fun {a b} c => by
    cases a <;> cases b <;> cases c <;> first | exact Iff.rfl | exact h | exact h.symm)

theorem propextFromRingLift (respect : type_of% @Ring.OfSemiring.instLEQOfOrderedAdd._proof_1.{0}) :
    type_of% @propext := by
  intro p q h
  exact @respect Bool xorSemiring (testLE p q) (testPreorder p q) (testOrdered h)
    (false,false) (true,false) (true,true) (true,false) ⟨false,rfl⟩ ⟨false,rfl⟩

local instance xorNatModule : NatModule Bool where
  zero := false
  add := Bool.xor
  nsmul := ⟨fun n a => parity n && a⟩
  add_zero a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_nsmul _ := rfl
  add_one_nsmul n a := by
    change (!(parity n) && a) = Bool.xor (parity n && a) a
    cases parity n <;> cases a <;> rfl

theorem propextFromModuleLift (respect : type_of% @IntModule.OfNatModule.instLEQOfOrderedAdd._proof_3.{0}) :
    type_of% @propext := by
  intro p q h
  exact @respect Bool xorNatModule (testLE p q) (testPreorder p q) (testOrdered h)
    (false,false) (true,false) (true,true) (true,false) ⟨false,rfl⟩ ⟨false,rfl⟩


/-- Cancellation identifies the diagonal Boolean representative with zero. -/
private theorem diagonalEq {A : Type} (mk : Bool × Bool → A)
    (plus : A → A → A) (minus : A → A) (zero : A)
    (cancel : ∀ x, plus (minus x) x = zero)
    (negValue : minus (mk (true, false)) = mk (false, true))
    (sumValue : plus (mk (false, true)) (mk (true, false)) = mk (true, true))
    (zeroValue : zero = mk (false, false)) : mk (true, true) = mk (false, false) := by
  rw [← sumValue, ← negValue, cancel, zeroValue]

open Ring.OfSemiring in
/-- The ring cancellation field and its three Boolean computations identify two representatives. -/
theorem ringDiagonal (s : Ring (Q Bool))
    (negValue : s.toNeg.neg (Q.mk (true, false)) = Q.mk (false, true))
    (sumValue : s.toSemiring.toAdd.add (Q.mk (false, true)) (Q.mk (true, false)) = Q.mk (true, true))
    (zeroValue : (s.toSemiring.ofNat 0).ofNat = Q.mk (false, false)) :
    Q.mk (true, true) = Q.mk (false, false) :=
  diagonalEq Q.mk s.toSemiring.toAdd.add s.toNeg.neg (s.toSemiring.ofNat 0).ofNat
    s.neg_add_cancel negValue sumValue zeroValue

open IntModule.OfNatModule in
theorem moduleDiagonal (s : IntModule (Q Bool))
    (negValue : s.toAddCommGroup.toNeg.neg (Q.mk (true, false)) = Q.mk (false, true))
    (sumValue : s.toAddCommGroup.toAddCommMonoid.toAdd.add
      (Q.mk (false, true)) (Q.mk (true, false)) = Q.mk (true, true))
    (zeroValue : s.toAddCommGroup.toAddCommMonoid.toZero.zero = Q.mk (false, false)) :
    Q.mk (true, true) = Q.mk (false, false) :=
  diagonalEq Q.mk s.toAddCommGroup.toAddCommMonoid.toAdd.add s.toAddCommGroup.toNeg.neg
    s.toAddCommGroup.toAddCommMonoid.toZero.zero s.toAddCommGroup.neg_add_cancel negValue sumValue zeroValue

open Ring.OfSemiring in
/-- Computing the two translated comparisons distinguishes any pair of equivalent propositions. -/
theorem propextFromRingOrder (order : type_of% @instLEQOfOrderedAdd.{0})
    (diagonal : @Q.mk Bool xorSemiring (true, true) = Q.mk (false, false))
    (values : ∀ (p q : Prop) (h : p ↔ q),
      let rel := (@order Bool xorSemiring (testLE p q) (testPreorder p q) (testOrdered h)).le
      rel (Q.mk (false, false)) (Q.mk (true, false)) = p ∧
      rel (Q.mk (true, true)) (Q.mk (true, false)) = q) : type_of% @propext := by
  intro p q h
  obtain ⟨hp, hq⟩ := values p q h
  rw [diagonal, hp] at hq
  exact hq

open IntModule.OfNatModule in
theorem propextFromModuleOrder (order : type_of% @instLEQOfOrderedAdd.{0})
    (diagonal : @Q.mk Bool xorNatModule (true, true) = Q.mk (false, false))
    (values : ∀ (p q : Prop) (h : p ↔ q),
      let rel := (@order Bool xorNatModule (testLE p q) (testPreorder p q) (testOrdered h)).le
      rel (Q.mk (false, false)) (Q.mk (true, false)) = p ∧
      rel (Q.mk (true, true)) (Q.mk (true, false)) = q) : type_of% @propext := by
  intro p q h
  obtain ⟨hp, hq⟩ := values p q h
  rw [diagonal, hp] at hq
  exact hq

-- The pinned structures satisfy each of the five computation tests by reduction.
open Ring.OfSemiring in
example : type_of% @propext :=
  propextFromRingOrder (@instLEQOfOrderedAdd) (ringDiagonal ofSemiring rfl rfl rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩)

open IntModule.OfNatModule in
example : type_of% @propext :=
  propextFromModuleOrder (@instLEQOfOrderedAdd) (moduleDiagonal ofNatModule rfl rfl rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩)

end OmegaChecks.InitBoundaries.EnvelopeOrder
