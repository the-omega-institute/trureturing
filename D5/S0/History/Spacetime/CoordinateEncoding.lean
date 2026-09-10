/- GID: D5/S0/History/Spacetime/CoordinateEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/CoordinateEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed finite integer coordinates and event attributes have exact HF tuple representations. -/

import D5.S0.History.Spacetime.ArchiveCarrier
import D5.S0.History.Spacetime.IntegerEncoding
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace D5.S0.History.Spacetime.CoordinateEncoding

open HFEncoding IntegerEncoding SourceTreeEncoding ArchiveCarrier
noncomputable section

/-- The tuple has exactly d integer entries, terminated by the empty set. -/
def IsPositionCode : Nat → HF → Prop
  | 0 => fun c => c = empty
  | d + 1 => PairCode IsIntCode (IsPositionCode d)

def position_code_equiv : (d : Nat) → (Fin d → Int) ≃ {c // IsPositionCode d c}
  | 0 =>
    { toFun := fun _ => ⟨empty, rfl⟩
      invFun := fun _ => Fin.elim0
      left_inv := fun _ => by funext i; exact Fin.elim0 i
      right_inv := fun c => Subtype.ext c.property.symm }
  | d + 1 =>
    (Fin.consEquiv (fun _ : Fin (d + 1) => Int)).symm.trans
      (prod_code_equiv int_code_equiv (position_code_equiv d))

/-- Signs are the two literal integer codes for -1 and +1. -/
def IsSignCode (c : HF) : Prop := c = intCode (-1) ∨ c = intCode 1

def signCode (b : Bool) : HF := if b then intCode 1 else intCode (-1)

theorem signCode_valid (b : Bool) : IsSignCode (signCode b) := by
  cases b <;> simp [signCode, IsSignCode]

def sign_code_equiv : Bool ≃ {c // IsSignCode c} :=
  Equiv.ofBijective (fun b => ⟨signCode b, signCode_valid b⟩) ⟨by
    intro a b h
    have h' := congrArg Subtype.val h
    cases a <;> cases b <;> simp_all [signCode, intCode_injective.eq_iff], by
    rintro ⟨c, rfl | rfl⟩
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩⟩

/-- The field order is time, position, sign, source tree. -/
def IsAttributesCode (d : Nat) : HF → Prop :=
  PairCode IsIntCode (PairCode (IsPositionCode d) (PairCode IsSignCode IsSourceCode))

def attributes_tuple_equiv (d : Nat) :
    Attributes d ≃ Int × (Fin d → Int) × Bool × SourceTree where
  toFun a := (a.time, a.position, a.positive, a.source)
  invFun a := ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def attributes_code_equiv (d : Nat) : Attributes d ≃ {c // IsAttributesCode d c} :=
  (attributes_tuple_equiv d).trans (prod_code_equiv int_code_equiv
    (prod_code_equiv (position_code_equiv d) (prod_code_equiv sign_code_equiv source_code_equiv)))

def attributesCode {d : Nat} (a : Attributes d) : HF := (attributes_code_equiv d a).val

theorem attributesCode_valid {d : Nat} (a : Attributes d) :
    IsAttributesCode d (attributesCode a) := (attributes_code_equiv d a).property

def decodeAttributes {d : Nat} (c : HF) (h : IsAttributesCode d c) : Attributes d :=
  (attributes_code_equiv d).symm ⟨c, h⟩

@[simp] theorem decodeAttributes_encode {d : Nat} (a : Attributes d) :
    decodeAttributes (attributesCode a) (attributesCode_valid a) = a :=
  (attributes_code_equiv d).symm_apply_apply a

@[simp] theorem encode_decodeAttributes {d : Nat} (c : HF) (h : IsAttributesCode d c) :
    attributesCode (decodeAttributes c h) = c :=
  congrArg Subtype.val ((attributes_code_equiv d).apply_symm_apply ⟨c, h⟩)

end
end D5.S0.History.Spacetime.CoordinateEncoding
