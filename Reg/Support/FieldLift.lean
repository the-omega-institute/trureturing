module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.CharZero.Defs

public section

namespace Reg.Support.FieldLift

universe u v

instance charZero (R : Type u) [AddMonoidWithOne R] [CharZero R] :
    CharZero (ULift.{v} R) where
  cast_injective := by
    intro m n h
    exact Nat.cast_injective (congrArg ULift.down h : (m : R) = n)

end Reg.Support.FieldLift
