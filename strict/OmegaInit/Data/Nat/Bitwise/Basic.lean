module
prelude
public import OmegaInit.Core
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
attribute [instance] Omega.Nat.instShiftLeft Omega.Nat.instShiftRight

public section
namespace Nat
export _root_.Omega.Nat (instShiftLeft instShiftRight shiftLeft)
end Nat
