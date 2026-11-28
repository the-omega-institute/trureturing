module
import all OmegaChecks.InitPort.Alternatives.Float
public import Init.Data.Float.Float
public import Init.Data.Float.Float32
import all Init.Data.Float.Float
import all Init.Data.Float.Float32

namespace OmegaChecks.InitPort.Alternatives
open _root_.Float.Model
open _root_.Float.Model.UnpackedFloat

private def fraction64 (s : Sign) (mantissa : Nat) : _root_.Float :=
  ⟨⟨UInt64.ofBitVec (packComponents Format.binary64 s 1022 (BitVec.ofNat 52 mantissa)),
    nonExceptional (by decide)⟩⟩

private def fraction32 (s : Sign) (mantissa : Nat) : _root_.Float32 :=
  ⟨⟨UInt32.ofBitVec (packComponents Format.binary32 s 126 (BitVec.ofNat 23 mantissa)),
    nonExceptional (by decide)⟩⟩

/-- Normalize the dyadic mantissa, retaining signed zero and the exceptional input classes. -/
private def splitFraction {F : Type} (width : Nat) (make : Sign → Nat → F) (input : F) :
    UnpackedFloat → F × Int
  | .finite sign m e _ =>
    let top := m.log2
    (make sign (m * 2 ^ (width - top)), e + Int.ofNat (top + 1))
  | _ => (input, 0)

public def Float.frExp (x : _root_.Float) : _root_.Float × Int :=
  splitFraction 52 fraction64 x x.toModel.unpack

public def Float32.frExp (x : _root_.Float32) : _root_.Float32 × Int :=
  splitFraction 23 fraction32 x x.toModel.unpack

public theorem Float.frExp._proof_1 :
    type_of% (private_decl% @_root_.Float.frExp._proof_1) := ⟨Float.frExp⟩

public theorem Float32.frExp._proof_1 :
    type_of% (private_decl% @_root_.Float32.frExp._proof_1) := ⟨Float32.frExp⟩

end OmegaChecks.InitPort.Alternatives
