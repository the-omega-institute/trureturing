/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Prelude

port_native_records SizeOf
namespace Omega
export SizeOf (sizeOf)
end Omega

port_definition SizeOf.ctorIdx
port_definition SizeOf.noConfusionType
port_definition SizeOf.noConfusion
port_definition SizeOf.mk.noConfusion
port_definition default.sizeOf.match_1
port_definition default.sizeOf with_native_code
port_definition instSizeOfDefault with_native_code
port_definition instSizeOfNat with_native_code
port_definition instSizeOfForallUnit with_native_code
attribute [instance 100] Omega.instSizeOfDefault
attribute [instance] Omega.instSizeOfNat Omega.instSizeOfForallUnit

port_proof sizeOf_default by_reflexivity
port_proof sizeOf_nat by_reflexivity
port_proof sizeOf_thunk by_reflexivity

port_definition PUnit._sizeOf_1
port_definition PUnit._sizeOf_inst
port_proof PUnit.unit.sizeOf_spec by_reflexivity

port_definition Prod._sizeOf_1
port_definition Prod._sizeOf_inst
port_proof Prod.mk.sizeOf_spec by_reflexivity

port_definition PProd._sizeOf_1
port_definition PProd._sizeOf_inst
port_proof PProd.mk.sizeOf_spec by_reflexivity

port_definition MProd._sizeOf_1
port_definition MProd._sizeOf_inst
port_proof MProd.mk.sizeOf_spec by_reflexivity

port_definition Bool._sizeOf_1
port_definition Bool._sizeOf_inst
port_proof Bool.false.sizeOf_spec by_reflexivity
port_proof Bool.true.sizeOf_spec by_reflexivity

port_definition Subtype._sizeOf_1
port_definition Subtype._sizeOf_inst
port_proof Subtype.mk.sizeOf_spec by_reflexivity

port_definition PLift._sizeOf_1
port_definition PLift._sizeOf_inst
port_proof PLift.up.sizeOf_spec by_reflexivity

port_definition ULift._sizeOf_1
port_definition ULift._sizeOf_inst
port_proof ULift.up.sizeOf_spec by_reflexivity

port_definition Decidable._sizeOf_1
port_definition Decidable._sizeOf_inst
port_proof Decidable.intro.sizeOf_spec by_reflexivity

port_definition Fin._sizeOf_1
port_definition Fin._sizeOf_inst
port_proof Fin.mk.sizeOf_spec by_reflexivity

port_definition BitVec._sizeOf_1
port_definition BitVec._sizeOf_inst
port_proof BitVec.ofFin.sizeOf_spec by_reflexivity

port_definition UInt8._sizeOf_1
port_definition UInt8._sizeOf_inst
port_proof UInt8.ofBitVec.sizeOf_spec by_reflexivity

port_definition UInt16._sizeOf_1
port_definition UInt16._sizeOf_inst
port_proof UInt16.ofBitVec.sizeOf_spec by_reflexivity

port_definition UInt32._sizeOf_1
port_definition UInt32._sizeOf_inst
port_proof UInt32.ofBitVec.sizeOf_spec by_reflexivity

port_definition UInt64._sizeOf_1
port_definition UInt64._sizeOf_inst
port_proof UInt64.ofBitVec.sizeOf_spec by_reflexivity

port_definition Option._sizeOf_1
port_definition Option._sizeOf_inst
port_proof Option.none.sizeOf_spec by_reflexivity
port_proof Option.some.sizeOf_spec by_reflexivity

port_definition List._sizeOf_1
port_definition List._sizeOf_inst
port_proof List.cons.sizeOf_spec by_reflexivity
port_proof List.nil.sizeOf_spec by_reflexivity

port_definition Array._sizeOf_1
port_definition Array._sizeOf_inst
port_proof Array.mk.sizeOf_spec by_reflexivity

port_definition ByteArray._sizeOf_1
port_definition ByteArray._sizeOf_inst
port_proof ByteArray.mk.sizeOf_spec by_reflexivity

port_definition Except._sizeOf_1
port_definition Except._sizeOf_inst
port_proof Except.error.sizeOf_spec by_reflexivity
port_proof Except.ok.sizeOf_spec by_reflexivity

port_definition EStateM.Result._sizeOf_1
port_definition EStateM.Result._sizeOf_inst
port_proof EStateM.Result.error.sizeOf_spec by_reflexivity
port_proof EStateM.Result.ok.sizeOf_spec by_reflexivity

port_proof Unit.sizeOf by_reflexivity
port_proof Bool.sizeOf_eq_one by_finite_cases
attribute [instance] Omega.PUnit._sizeOf_inst
attribute [instance] Omega.Prod._sizeOf_inst
attribute [instance] Omega.PProd._sizeOf_inst
attribute [instance] Omega.MProd._sizeOf_inst
attribute [instance] Omega.Bool._sizeOf_inst
attribute [instance] Omega.Subtype._sizeOf_inst
attribute [instance] Omega.PLift._sizeOf_inst
attribute [instance] Omega.ULift._sizeOf_inst
attribute [instance] Omega.Decidable._sizeOf_inst
attribute [instance] Omega.Fin._sizeOf_inst
attribute [instance] Omega.BitVec._sizeOf_inst
attribute [instance] Omega.UInt8._sizeOf_inst
attribute [instance] Omega.UInt16._sizeOf_inst
attribute [instance] Omega.UInt32._sizeOf_inst
attribute [instance] Omega.UInt64._sizeOf_inst
attribute [instance] Omega.Option._sizeOf_inst
attribute [instance] Omega.List._sizeOf_inst
attribute [instance] Omega.Array._sizeOf_inst
attribute [instance] Omega.ByteArray._sizeOf_inst
attribute [instance] Omega.Except._sizeOf_inst
attribute [instance] Omega.EStateM.Result._sizeOf_inst

port_proof Decidable.intro.congr_simp
port_proof Fin.mk.congr_simp
port_proof Subtype.mk.congr_simp

public section
namespace Bool
export _root_.Omega.Bool (sizeOf_eq_one)
end Bool
namespace Bool.false
export _root_.Omega.Bool.false (sizeOf_spec)
end Bool.false
namespace Bool.true
export _root_.Omega.Bool.true (sizeOf_spec)
end Bool.true
namespace Decidable.intro
export _root_.Omega.Decidable.intro (sizeOf_spec)
end Decidable.intro
namespace Omega.Decidable.intro
export _root_.Decidable.intro (congr_simp)
end Omega.Decidable.intro
namespace PProd.mk
export _root_.Omega.PProd.mk (sizeOf_spec)
end PProd.mk
namespace PUnit.unit
export _root_.Omega.PUnit.unit (sizeOf_spec)
end PUnit.unit
namespace Unit
export _root_.Omega.Unit (sizeOf)
end Unit
