module
prelude
public import OmegaInit.Core
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Div.Basic

noncomputable section

@[expose] public section

namespace Omega.Nat

/-- The first argument decreases after each division by two. Its successor bounds the recursion. -/
@[no_expose] def bitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => Nat.zero)
    (fun _ prev a b => Nat.casesOn (motive := fun _ => Nat) a
      (Bool.casesOn (motive := fun _ => Nat) (f Bool.false Bool.true) Nat.zero b)
      (fun i => Nat.casesOn (motive := fun _ => Nat) b
        (Bool.casesOn (motive := fun _ => Nat) (f Bool.true Bool.false) Nat.zero (Nat.succ i))
        (fun j =>
          let x := Nat.succ i
          let y := Nat.succ j
          let one := Nat.succ Nat.zero
          let two := Nat.succ one
          let r := prev (Nat.div x two) (Nat.div y two)
          let bit := f (Nat.beq (Nat.mod x two) one) (Nat.beq (Nat.mod y two) one)
          Bool.casesOn (motive := fun _ => Nat) bit (Nat.add r r) (Nat.succ (Nat.add r r)))))
    (succ n) n m

attribute [irreducible] bitwise

end Omega.Nat

port_definition Nat.land with_native_code
port_definition Nat.lor with_native_code
namespace Nat
/-- The kernel evaluates numerals at this literal name. Symbolic calls retain the pinned bitwise definition. -/
@[extern "lean_nat_lxor", no_expose] def xor : @& Nat → @& Nat → Nat :=
  Omega.Nat.bitwise (@Omega.bne Bool (@Omega.instBEqOfDecidableEq Bool Omega.instDecidableEqBool))
attribute [irreducible] xor
end Nat

port_definition Nat.shiftLeft.match_1

namespace Omega.Nat
export _root_.Nat (xor)

@[extern "lean_nat_shiftr", implicit_reducible] def shiftRight : @& Nat → @& Nat → Nat := fun x n =>
  Nat.brecOn (motive := fun _ => Nat → Nat) n (fun i below num =>
    Nat.shiftLeft.match_1 (fun _ i => Nat.below (motive := fun _ => Nat → Nat) i → Nat) num i
      (fun z _ => z) (fun z _ prior => Nat.div (prior.fst z) (succ (succ zero))) below) x

@[implicit_reducible] def testBit (m n : Nat) : Bool :=
  Bool.not (Nat.beq (Nat.land (succ zero) (Nat.shiftRight m n)) zero)

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (bitwise land lor shiftRight testBit)
end Nat

port_definition Nat.hasNotBit

public section
namespace Nat
export _root_.Omega.Nat (hasNotBit)
end Nat

port_definition Nat.shiftLeft._f
port_definition Nat.shiftLeft with_native_code
port_definition Nat.instShiftLeft with_native_code
port_definition Nat.instShiftRight with_native_code

public section
namespace Nat
export _root_.Omega.Nat (instShiftLeft instShiftRight shiftLeft)
end Nat

port_definition Nat.instAndOp with_native_code
port_definition Nat.instOrOp with_native_code
port_definition Nat.instXorOp with_native_code
attribute [instance] Omega.Nat.instAndOp Omega.Nat.instOrOp Omega.Nat.instXorOp
  Omega.Nat.instShiftLeft Omega.Nat.instShiftRight
namespace Omega.Nat

private theorem halfLt {n : Nat} (h : Ne n zero) : Nat.lt (Nat.div n (succ (succ zero))) n :=
  Nat.div_lt_self (Omega.Nat.pos_of_ne_zero h) Nat.one_lt_two

end Omega.Nat
port_proof Nat.bitwise_rec_lemma using Omega.Nat.halfLt
port_proof Nat.land_eq by_reflexivity
port_proof Nat.lor_eq by_reflexivity
port_proof Nat.xor_eq by_reflexivity
port_proof Nat.shiftLeft_eq' by_reflexivity
port_proof Nat.shiftRight_eq' by_reflexivity
port_proof Nat.shiftRight_zero by_reflexivity
port_proof Nat.shiftRight_succ by_reflexivity
port_proof Nat.hasNotBit_eq by_reflexivity

namespace Omega.Nat

private abbrev twoN := succ (succ zero)

private theorem shiftTimes (a b : Nat) : Eq (shiftLeft a b) (Nat.mul a (Nat.pow twoN b)) :=
  Nat.rec (motive := fun n => ∀ a, Eq (shiftLeft a n) (Nat.mul a (Nat.pow twoN n)))
    (fun a => (Nat.mul_one a).symm)
    (fun k ih a => (ih (Nat.mul twoN a)).trans ((congrArg (fun n => Nat.mul n (Nat.pow twoN k))
      (Nat.mul_comm twoN a)).trans ((Nat.mul_assoc a twoN (Nat.pow twoN k)).trans
      (congrArg (Nat.mul a) (Nat.mul_comm twoN (Nat.pow twoN k)))))) b a

private theorem shiftRightCompose (m n : Nat) (k : Nat) :
    Eq (shiftRight m (Nat.add n k)) (shiftRight (shiftRight m n) k) :=
  Nat.rec (motive := fun i => Eq (shiftRight m (Nat.add n i)) (shiftRight (shiftRight m n) i))
    rfl (fun _ h => congrArg (fun a => Nat.div a twoN) h) k

private theorem shiftDivide (m n : Nat) : Eq (shiftRight m n) (Nat.div m (Nat.pow twoN n)) :=
  Nat.rec (motive := fun k => Eq (shiftRight m k) (Nat.div m (Nat.pow twoN k)))
    (Nat.div_one m).symm (fun i h => (congrArg (fun a => Nat.div a twoN) h).trans
      (Omega.Nat.div_div_eq_div_mul m (Nat.pow twoN i) twoN)) n

private theorem shiftSmall (m n : Nat) (h : Nat.lt m (Nat.pow twoN n)) : Eq (shiftRight m n) zero :=
  (shiftDivide m n).trans (Nat.div_eq_of_lt h)

private theorem shiftSmaller (m n : Nat) : Nat.le (shiftRight m n) m :=
  Eq.subst (motive := fun i => Nat.le i m) (shiftDivide m n).symm (Nat.div_le_self m (Nat.pow twoN n))

end Omega.Nat

port_proof Nat.shiftLeft_eq using Omega.Nat.shiftTimes
port_proof Nat.shiftRight_add using Omega.Nat.shiftRightCompose
port_proof Nat.shiftRight_eq_div_pow using Omega.Nat.shiftDivide
port_proof Nat.shiftRight_eq_zero using Omega.Nat.shiftSmall
port_proof Nat.shiftRight_le using Omega.Nat.shiftSmaller

public section
namespace Nat
export _root_.Omega.Nat (bitwise_rec_lemma hasNotBit_eq instAndOp instOrOp instXorOp land_eq lor_eq
  shiftLeft_eq shiftLeft_eq' shiftRight_add shiftRight_eq' shiftRight_eq_div_pow shiftRight_eq_zero
  shiftRight_le shiftRight_succ shiftRight_zero xor_eq)
end Nat

/- The compiler-generated Nat.bitwise._unsafe_rec, Nat.shiftLeft._unsafe_rec and
Nat.shiftRight._unsafe_rec are partial runtime workers. The public operations above
provide their values. Nat.shiftRight._sunfold is generated for the pinned recursive
body, whereas this strict shift uses the explicit course-of-values recursor. -/
