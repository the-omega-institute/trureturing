import LeanInformationAuditRegTests.Fixtures.Provenance
import Reg.Support.CompiledNodeTerm

namespace K2TypeAtValidation

example : (type_of% (@(compiled_node% "{\"declaration\":[\"AllowlistBoundaries\",\"proofArgument\"],\"levels\":[],\"part\":\"value\",\"path\":[\"body\",\"body\",\"function\",\"function\",\"argument\"]}"))) = (∀ (x : @Unit), ∀ (state : @Bool), Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row46.__fieldF_0 : type_of% (fun (x : @Unit) => fun (state : @Bool) => fun (c : @Nat) =>
  @Eq.{1} (@Nat) (@OfNat.ofNat.{0} (@Nat) (nat_lit 4) (@instOfNatNat (nat_lit 4)))
    (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} @Nat @instMulNat)
      (@OfNat.ofNat.{0} (@Nat) (nat_lit 2) (@instOfNatNat (nat_lit 2))) c)) := fun (x : @Unit) => fun (state : @Bool) => fun (c : @Nat) =>
  @Eq.{1} (@Nat) (@OfNat.ofNat.{0} (@Nat) (nat_lit 4) (@instOfNatNat (nat_lit 4)))
    (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} @Nat @instMulNat)
      (@OfNat.ofNat.{0} (@Nat) (nat_lit 2) (@instOfNatNat (nat_lit 2))) c)

example : (type_of% (@K2HeadFamiliesPlaceholder.row46.__fieldF_0)) = (∀ (x : @Unit), ∀ (state : @Bool), ∀ (c : @Nat), Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row46.__fieldEta_0 : type_of% (fun (x : @Unit) => fun (state : @Bool) => fun (c : @Nat) => @K2HeadFamiliesPlaceholder.row46.__fieldF_0 x state c) := fun (x : @Unit) => fun (state : @Bool) => fun (c : @Nat) => @K2HeadFamiliesPlaceholder.row46.__fieldF_0 x state c

example : (type_of% (@K2HeadFamiliesPlaceholder.row46.__fieldEta_0)) = (∀ (x : @Unit), ∀ (state : @Bool), ∀ (c : @Nat), Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row46 : type_of% (@(compiled_node% "{\"declaration\":[\"AllowlistBoundaries\",\"proofArgument\"],\"levels\":[],\"part\":\"value\",\"path\":[\"body\",\"body\",\"function\",\"function\",\"argument\"]}")) := fun (x : @Unit) => fun (state : @Bool) => @Exists.{1} (@Nat) (@K2HeadFamiliesPlaceholder.row46.__fieldF_0 x state)

example : (type_of% (@(compiled_node% "{\"declaration\":[\"AllowlistBoundaries\",\"harmless\"],\"levels\":[],\"part\":\"type\",\"path\":[]}"))) = (Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row340.__fieldF_0 : type_of% (fun (c : @Nat) =>
  @Eq.{1} (@Nat) (@OfNat.ofNat.{0} (@Nat) (nat_lit 4) (@instOfNatNat (nat_lit 4)))
    (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} @Nat @instMulNat)
      (@OfNat.ofNat.{0} (@Nat) (nat_lit 2) (@instOfNatNat (nat_lit 2))) c)) := fun (c : @Nat) =>
  @Eq.{1} (@Nat) (@OfNat.ofNat.{0} (@Nat) (nat_lit 4) (@instOfNatNat (nat_lit 4)))
    (@HMul.hMul.{0, 0, 0} (@Nat) (@Nat) (@Nat) (@instHMul.{0} @Nat @instMulNat)
      (@OfNat.ofNat.{0} (@Nat) (nat_lit 2) (@instOfNatNat (nat_lit 2))) c)

example : (type_of% (@K2HeadFamiliesPlaceholder.row340.__fieldF_0)) = (∀ (c : @Nat), Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row340.__fieldEta_0 : type_of% (fun (c : @Nat) => @K2HeadFamiliesPlaceholder.row340.__fieldF_0 c) := fun (c : @Nat) => @K2HeadFamiliesPlaceholder.row340.__fieldF_0 c

example : (type_of% (@K2HeadFamiliesPlaceholder.row340.__fieldEta_0)) = (∀ (c : @Nat), Prop) := rfl

noncomputable def K2HeadFamiliesPlaceholder.row340 : type_of% (@(compiled_node% "{\"declaration\":[\"AllowlistBoundaries\",\"harmless\"],\"levels\":[],\"part\":\"type\",\"path\":[]}")) := @Exists.{1} @Nat @K2HeadFamiliesPlaceholder.row340.__fieldF_0

end K2TypeAtValidation
