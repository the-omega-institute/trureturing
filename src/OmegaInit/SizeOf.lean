module
public import Init.SizeOf
public import OmegaInit.Prelude

/-! Namespace aliases to the pinned public interface. -/
public section
namespace Omega
export _root_ (Array.mk.sizeOf_spec BitVec.ofFin.sizeOf_spec Bool.false.sizeOf_spec Bool.true.sizeOf_spec ByteArray.mk.sizeOf_spec Char.mk.congr_simp Char.mk.sizeOf_spec Decidable.intro.congr_simp Decidable.intro.sizeOf_spec EStateM.Result.error.sizeOf_spec EStateM.Result.ok.sizeOf_spec Except.error.sizeOf_spec Except.ok.sizeOf_spec Fin.mk.congr_simp Fin.mk.sizeOf_spec List.cons.sizeOf_spec List.nil.sizeOf_spec MProd.mk.sizeOf_spec Option.none.sizeOf_spec Option.some.sizeOf_spec PLift.up.sizeOf_spec PProd.mk.sizeOf_spec PUnit.unit.sizeOf_spec Prod.mk.sizeOf_spec SizeOf SizeOf.mk.noConfusion String.Pos.Raw.mk.sizeOf_spec Subtype.mk.congr_simp Subtype.mk.sizeOf_spec UInt16.ofBitVec.sizeOf_spec UInt32.ofBitVec.sizeOf_spec UInt64.ofBitVec.sizeOf_spec UInt8.ofBitVec.sizeOf_spec ULift.up.sizeOf_spec Unit.sizeOf default.sizeOf.match_1 instSizeOfDefault instSizeOfForallUnit instSizeOfNat sizeOf sizeOf_default sizeOf_nat sizeOf_thunk)
end Omega
namespace Omega.Bool
export _root_.Bool (sizeOf_eq_one)
end Omega.Bool
namespace Omega.SizeOf
export _root_.SizeOf (casesOn ctorIdx mk noConfusion noConfusionType rec recOn sizeOf)
end Omega.SizeOf
namespace Omega.default
export _root_.default (sizeOf)
end Omega.default
