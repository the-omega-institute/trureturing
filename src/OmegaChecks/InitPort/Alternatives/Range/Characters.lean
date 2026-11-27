module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Fin
public import Init.Data.Range.Polymorphic.UInt
import all Init.Data.Range.Polymorphic.Internal.SignedBitVec
import all Init.Data.Range.Polymorphic.SInt
import all Init.Data.Char.Ordinal
import all Init.Data.Range.Polymorphic.Char
import Init.Data.BitVec.Lemmas
public import OmegaChecks.InitPort.Alternatives.Range.WordSize
import all OmegaChecks.InitPort.Alternatives.Range.WordSize

/-! Ordinal enumeration of Unicode scalar values. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

private def doubleBits (value : Nat) (bits : Nat) : Nat :=
  Nat.rec value (fun _ n => n * 2) bits

private theorem doubleBitsAdd (a b k : Nat) : doubleBits a k + doubleBits b k = doubleBits (a + b) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change doubleBits a k * 2 + doubleBits b k * 2 = doubleBits (a + b) k * 2
    rw [← Nat.add_mul, ih]

private theorem packedSize : Char.numCodePoints + Char.numSurrogates = 0x110000 :=
  doubleBitsAdd 543 1 11

private def lowOnes (leading bits : Nat) : Nat :=
  Nat.rec leading (fun _ v => v * 2 + 1) bits

private theorem lowOnesSucc (leading bits : Nat) : lowOnes leading bits + 1 = doubleBits (leading + 1) bits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    change lowOnes leading bits * 2 + 1 + 1 = doubleBits (leading + 1) bits * 2
    rw [← ih, Nat.add_mul, Nat.one_mul]

public theorem Char.ordinal._proof_1 :
    type_of% (private_decl% @_root_.Char.ordinal._proof_1) := by
  intro c h
  have limit : (0xd800 : UInt32).toNat = 0xd800 := UInt32.toNat_ofNat_of_lt (by decide)
  exact Nat.lt_trans (limit ▸ UInt32.lt_iff_toNat_lt.mp h) (show 0xd800 < 1112064 by decide)

public theorem Char.ofOrdinal._proof_1 :
    type_of% (private_decl% @_root_.Char.ofOrdinal._proof_1) := by
  intro _ below
  exact Nat.lt_trans below (show 0xd800 < 4294967296 by decide)

public theorem Char.ofOrdinal._proof_2 :
    type_of% (private_decl% @_root_.Char.ofOrdinal._proof_2) := by
  intro f below
  exact Or.inl ((UInt32.toNat_ofNatLT (n := f.val)).symm ▸ below)

public theorem Char.ofOrdinal._proof_3 :
    type_of% (private_decl% @_root_.Char.ofOrdinal._proof_3) := by
  intro f
  have below : f.val + Char.numSurrogates < 0x110000 := packedSize ▸ Nat.add_lt_add_right f.isLt _
  exact Nat.lt_trans below (show 0x110000 < 4294967296 by decide)

public theorem Char.ofOrdinal._proof_4 :
    type_of% (private_decl% @_root_.Char.ofOrdinal._proof_4) := by
  intro f above
  have low : 0xd800 ≤ f.val := Nat.le_of_not_lt above
  have boundary : 0xdfff < 0xd800 + 2048 := by
    have align : (0xd800 : Nat) + 2048 = 0xe000 := doubleBitsAdd 27 1 11
    exact align.symm ▸ (show 0xdfff < (0xe000 : Nat) by decide)
  exact Or.inr ⟨Nat.lt_of_lt_of_le boundary (Nat.add_le_add_right low _),
    packedSize ▸ Nat.add_lt_add_right f.isLt _⟩

public theorem Char.succ?._proof_2 :
    type_of% (private_decl% @_root_.Char.succ?._proof_2) := by
  have point : (0xe000 : UInt32).toNat = 0xe000 := UInt32.toNat_ofNat_of_lt (by decide)
  change (UInt32.toNat 0xe000).isValidChar
  exact point.symm ▸ (show (0xe000 : Nat).isValidChar from Or.inr ⟨by decide, by decide⟩)

public theorem Char.succ?._proof_1 :
    type_of% (private_decl% @_root_.Char.succ?._proof_1) := by
  intro c h
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have gap : 0xd7ff + 1 = (0xd800 : Nat) := lowOnesSucc 26 11
  have below : c.val.toNat < 0xd7ff := pre ▸ UInt32.lt_iff_toNat_lt.mp h
  have valid : (c.val.toNat + 1).isValidChar := Or.inl (gap ▸ Nat.succ_lt_succ below)
  have inc : (c.val + 1).toNat = c.val.toNat + 1 :=
    (UInt32.toNat_add _ _).trans (Nat.mod_eq_of_lt (Char.isValidUInt32 _ valid))
  exact inc.symm ▸ valid

public theorem Char.ordinal._proof_2 :
    type_of% (private_decl% @_root_.Char.ordinal._proof_2) := by
  intro c _
  obtain small | ⟨large, hi⟩ := c.valid
  · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_trans small (show 0xd800 < 1112064 by decide))
  · have enough := Nat.le_trans (show 2048 ≤ 0xdfff by decide) (Nat.le_of_lt large)
    apply Nat.lt_of_add_lt_add_right (n := Char.numSurrogates)
    rw [Nat.sub_add_cancel enough, packedSize]
    exact hi

public theorem Char.succ?._proof_3 :
    type_of% (private_decl% @_root_.Char.succ?._proof_3) := by
  intro c lower different upper
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have limit : (0x10ffff : UInt32).toNat = 0x10ffff := UInt32.toNat_ofNat_of_lt (by decide)
  have lo : 0xd7ff ≤ c.val.toNat :=
    Nat.le_of_not_lt fun h => lower (UInt32.lt_iff_toNat_lt.mpr (pre.symm ▸ h))
  have hi : c.val.toNat < 0x10ffff := limit ▸ UInt32.lt_iff_toNat_lt.mp upper
  have valid : (c.val.toNat + 1).isValidChar := by
    obtain small | ⟨large, _⟩ := c.valid
    · have gap : 0xd7ff + 1 = (0xd800 : Nat) := lowOnesSucc 26 11
      have below : c.val.toNat < 0xd7ff + 1 := gap.symm ▸ small
      have val := Nat.le_antisymm (Nat.le_of_lt_succ below) lo
      exact (different (UInt32.toNat.inj (val.trans pre.symm))).elim
    · have gap : 0x10ffff + 1 = (0x110000 : Nat) := lowOnesSucc 16 16
      exact Or.inr ⟨Nat.lt_succ_of_lt large, gap ▸ Nat.succ_lt_succ hi⟩
  change (c.val + 1).toNat.isValidChar
  have inc : (c.val + 1).toNat = c.val.toNat + 1 :=
    (UInt32.toNat_add _ _).trans (Nat.mod_eq_of_lt (Char.isValidUInt32 _ valid))
  exact inc.symm ▸ valid

public theorem Char.instIsAlwaysFinite_2 : Rxi.IsAlwaysFinite Char where
  finite c := by
    refine ⟨Char.numCodePoints, ?_⟩
    rw [_root_.Char.pRangeSuccMany?_eq, _root_.Char.succMany?_eq]
    have stop : c.ordinal.addNat? Char.numCodePoints = none :=
      _root_.Fin.addNat?_eq_none_iff.mpr (Nat.le_add_left _ _)
    exact congrArg (Option.map Char.ofOrdinal) stop

public theorem Char.instIsAlwaysFinite : Rxc.IsAlwaysFinite Char :=
  closedOfFiniteEnumeration Char.instIsAlwaysFinite_2

public theorem Char.instIsAlwaysFinite_1 : Rxo.IsAlwaysFinite Char :=
  openOfFiniteEnumeration Char.instIsAlwaysFinite_2

private def packScalar (cut gap n : Nat) := if n < cut then n else n - gap
private def unpackScalar (cut gap i : Nat) := if i < cut then i else i + gap

private theorem packUnpack (cut gap i : Nat) : packScalar cut gap (unpackScalar cut gap i) = i := by
  by_cases small : i < cut
  · rw [unpackScalar, ite_eq_left small, packScalar, ite_eq_left small]
  · rw [unpackScalar, ite_eq_right small, packScalar, ite_eq_right (by omega), Nat.add_sub_cancel]

private theorem unpackPack {cut gap n : Nat} (valid : n < cut ∨ cut + gap ≤ n) :
    unpackScalar cut gap (packScalar cut gap n) = n := by
  cases valid with
  | inl small => rw [packScalar, ite_eq_left small, unpackScalar, ite_eq_left small]
  | inr large =>
    rw [packScalar, ite_eq_right (by omega), unpackScalar, ite_eq_right (by omega)]
    exact Nat.sub_add_cancel (by omega)

private theorem packMono {cut gap n m : Nat} (valid : m < cut ∨ cut + gap ≤ m) (le : n ≤ m) :
    packScalar cut gap n ≤ packScalar cut gap m := by
  unfold packScalar
  split <;> split <;> omega

private theorem unpackMono {cut gap n m : Nat} (le : n ≤ m) :
    unpackScalar cut gap n ≤ unpackScalar cut gap m := by
  unfold unpackScalar
  split <;> split <;> omega

private theorem charCut : (0xd800 : UInt32).toNat = 0xd800 := UInt32.toNat_ofNat_of_lt (by decide)

private theorem charValid (c : Char) : c.val.toNat < 0xd800 ∨ 0xd800 + Char.numSurrogates ≤ c.val.toNat := by
  obtain small | ⟨high, _⟩ := c.valid
  · exact Or.inl small
  · have base : (0xd800 : Nat) + 2048 = 0xe000 := doubleBitsAdd 27 1 11
    have limit : 0xdfff + 1 = (0xe000 : Nat) := lowOnesSucc 6 13
    exact Or.inr ((limit.trans base.symm) ▸ high)

public theorem Char.coe_ordinal : type_of% @_root_.Char.coe_ordinal := by
  intro c
  by_cases h : c.val < 0xd800
  · simp only [_root_.Char.ordinal, h, dite_true, ite_true]
  · simp only [_root_.Char.ordinal, h, dite_false, ite_false]

private theorem charPacked (c : Char) : c.ordinal.val = packScalar 0xd800 Char.numSurrogates c.val.toNat := by
  rw [Char.coe_ordinal]
  unfold packScalar
  have h : c.val < 0xd800 ↔ c.val.toNat < 0xd800 := charCut ▸ UInt32.lt_iff_toNat_lt
  by_cases inside : c.val < 0xd800
  · rw [ite_eq_left inside, ite_eq_left (h.mp inside)]
  · rw [ite_eq_right inside, ite_eq_right (fun ht => inside (h.mpr ht))]

private theorem charUnpacked (i : Fin Char.numCodePoints) :
    (Char.ofOrdinal i).val.toNat = unpackScalar 0xd800 Char.numSurrogates i.val := by
  unfold _root_.Char.ofOrdinal unpackScalar
  by_cases h : i.val < 0xd800
  · rw [dite_eq_left h, ite_eq_left h]
    exact UInt32.toNat_ofNatLT
  · rw [dite_eq_right h, ite_eq_right h]
    exact UInt32.toNat_ofNatLT

public theorem Char.ofOrdinal_ordinal : type_of% @_root_.Char.ofOrdinal_ordinal := by
  intro c
  apply Char.ext
  apply UInt32.toNat.inj
  rw [charUnpacked, charPacked, unpackPack (charValid c)]

public theorem Char.ordinal_ofOrdinal : type_of% @_root_.Char.ordinal_ofOrdinal := by
  intro i
  apply Fin.ext
  rw [charPacked, charUnpacked, packUnpack]

public theorem Char.ordinal_le_of_le : type_of% @_root_.Char.ordinal_le_of_le := by
  intro a b h
  change a.ordinal.val ≤ b.ordinal.val
  rw [charPacked, charPacked]
  exact packMono (charValid b) h

public theorem Char.ofOrdinal_le_of_le : type_of% @_root_.Char.ofOrdinal_le_of_le := by
  intro a b h
  change (Char.ofOrdinal a).val.toNat ≤ (Char.ofOrdinal b).val.toNat
  rw [charUnpacked, charUnpacked]
  exact unpackMono h

public theorem Char.val_ofOrdinal : type_of% @_root_.Char.val_ofOrdinal := by
  intro i
  unfold _root_.Char.ofOrdinal
  split <;> rfl

private theorem charOfValidNat (n : Nat) (h : n.isValidChar) : (Char.ofNat n).val.toNat = n := by
  unfold Char.ofNat
  rw [dite_eq_left h]
  rfl

public theorem Char.ordinal_zero : type_of% @_root_.Char.ordinal_zero := by
  apply Fin.ext
  rw [charPacked, Fin.val_zero]
  have below : (0 : Nat) < 0xd800 := by decide
  rw [charOfValidNat 0 (Or.inl below)]
  exact ite_eq_left below

private theorem scalarNextSome (c d : Char) (step : d.ordinal.val = c.ordinal.val + 1) :
    some d = (c.ordinal.addNat? 1).map Char.ofOrdinal := by
  have h := step ▸ d.ordinal.isLt
  rw [Fin.addNat?_eq_some h, Option.map_some]
  apply congrArg some
  have e : d.ordinal = (⟨c.ordinal.val + 1, h⟩ : Fin Char.numCodePoints) := Fin.ext step
  rw [← e, Char.ofOrdinal_ordinal]

private theorem incrementScalar (c d : Char) (next : d.val = c.val + 1) :
    d.val.toNat = c.val.toNat + 1 := by
  rw [next, UInt32.toNat_add]
  obtain h | ⟨_, h⟩ := c.valid
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h (by decide : 55296 < 4294967296))
  · exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h (by decide : 1114112 < 4294967296))

private theorem ordinalStepBelow (c d : Char) (next : d.val = c.val + 1) (hc : c.val < 0xd7ff) :
    d.ordinal.val = c.ordinal.val + 1 := by
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have bound : c.val.toNat < 0xd7ff := pre ▸ UInt32.lt_iff_toNat_lt.mp hc
  have gap : 0xd7ff + 1 = (0xd800 : Nat) := lowOnesSucc 26 11
  have below : c.val.toNat + 1 < 0xd800 := gap ▸ Nat.succ_lt_succ bound
  rw [charPacked, charPacked, incrementScalar c d next]
  unfold packScalar
  rw [ite_eq_left below, ite_eq_left (Nat.lt_trans (Nat.lt_succ_self _) below)]

private theorem ordinalStepAbove (c d : Char) (next : d.val = c.val + 1)
    (hc : ¬ c.val < 0xd7ff) (distinct : ¬ c.val = 0xd7ff) :
    d.ordinal.val = c.ordinal.val + 1 := by
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have gap : 0xd7ff + 1 = (0xd800 : Nat) := lowOnesSucc 26 11
  have lower : (0xd800 : Nat) ≤ c.val.toNat := by
    rw [← gap]
    apply Nat.lt_of_le_of_ne
    · exact Nat.le_of_not_lt fun h => hc (UInt32.lt_iff_toNat_lt.mpr (pre.symm ▸ h))
    · exact fun e => distinct (UInt32.toNat.inj (e.symm.trans pre.symm))
  rw [charPacked, charPacked, incrementScalar c d next]
  unfold packScalar
  rw [ite_eq_right (Nat.not_lt_of_ge (Nat.le_trans lower (Nat.le_succ _))),
    ite_eq_right (Nat.not_lt_of_ge lower)]
  have pad : Char.numSurrogates ≤ c.val.toNat := Nat.le_trans (by decide : 2048 ≤ 0xd800) lower
  omega

private theorem ordinalStepAcross (c d : Char) (hc : c.val = 0xd7ff) (hd : d.val = 0xe000) :
    d.ordinal.val = c.ordinal.val + 1 := by
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have high : (0xe000 : UInt32).toNat = 0xe000 := UInt32.toNat_ofNat_of_lt (by decide)
  have left : (0xd800 : Nat) + 2048 = 0xe000 := doubleBitsAdd 27 1 11
  have right : 0xd7ff + 1 = (0xd800 : Nat) := lowOnesSucc 26 11
  rw [charPacked, charPacked, hc, hd, pre, high]
  unfold packScalar
  rw [ite_eq_right (by decide), ite_eq_left (by decide), right, ← left, Nat.add_sub_cancel]

private theorem ordinalNextNone (c : Char) (last : ¬ c.val < 0x10ffff) :
    none = (c.ordinal.addNat? 1).map Char.ofOrdinal := by
  have bound : (0x10ffff : UInt32).toNat = 0x10ffff := UInt32.toNat_ofNat_of_lt (by decide)
  have lo : 0x10ffff ≤ c.val.toNat :=
    Nat.le_of_not_lt fun h => last (UInt32.lt_iff_toNat_lt.mpr (bound.symm ▸ h))
  have cut : 0xd800 ≤ c.val.toNat := Nat.le_trans (by decide : 0xd800 ≤ 0x10ffff) lo
  apply Eq.symm
  rw [Fin.addNat?_eq_none_iff.mpr]
  · rfl
  · rw [charPacked, packScalar, ite_eq_right (Nat.not_lt_of_ge cut)]
    have hi : 0x10ffff + 1 = (0x110000 : Nat) := lowOnesSucc 16 16
    have total : 0x10ffff + 1 ≤ c.val.toNat + 1 := Nat.succ_le_succ lo
    rw [hi, ← packedSize] at total
    have pad : Char.numSurrogates ≤ c.val.toNat := Nat.le_trans (by decide : 2048 ≤ 0xd800) cut
    omega

public theorem Char.succ?_eq : type_of% @_root_.Char.succ?_eq := by
  intro c
  unfold _root_.Char.succ?
  split
  next low => exact scalarNextSome c _ (ordinalStepBelow c _ rfl low)
  next above =>
    split
    next edge => exact scalarNextSome c _ (ordinalStepAcross c _ edge rfl)
    next other =>
      split
      next _ => exact scalarNextSome c _ (ordinalStepAbove c _ rfl above other)
      next last => exact ordinalNextNone c last


private theorem unpackMap (o : Option (Fin Char.numCodePoints)) :
    (o.map Char.ofOrdinal).map Char.ordinal = o := by
  cases o with
  | none => rfl
  | some f => exact congrArg some (Char.ordinal_ofOrdinal (f := f))

public theorem Char.map_ordinal_succ? : type_of% @_root_.Char.map_ordinal_succ? := by
  intro c
  rw [_root_.Char.succ?_eq]
  exact unpackMap _

public theorem Char.map._proof_1 : type_of% (private_decl% @_root_.Char.map._proof_1) := by
  intro c
  exact (Char.map_ordinal_succ? (c := c)).symm

public theorem Char.map._proof_2 : type_of% (private_decl% @_root_.Char.map._proof_2) := by
  intro n c
  exact (unpackMap (c.ordinal.addNat? n)).symm

public theorem Char.succ?_eq._proof_1_8 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_8) :=
  fun lower distinct upper => distinct (Nat.eq_of_lt_succ_of_not_lt upper lower)

public theorem Char.coe_ordinal._proof_1_2 :
    type_of% (private_decl% @_root_.Char.coe_ordinal._proof_1_2) := @Char.coe_ordinal

public theorem Char.ofOrdinal_le_of_le._proof_1_4 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_le_of_le._proof_1_4) := by
  intro f g hf hg
  rw [Nat.mod_eq_of_lt (Char.ofOrdinal._proof_3 g)]
  exact Nat.le_trans (Nat.le_of_lt hf) (Nat.le_trans (Nat.le_of_not_lt hg) (Nat.le_add_right ..))

public theorem Char.ofOrdinal_le_of_le._proof_1_5 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_le_of_le._proof_1_5) := fun le notLow low => notLow (Nat.lt_of_le_of_lt le low)

public theorem Char.ofOrdinal_le_of_le._proof_1_6 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_le_of_le._proof_1_6) := by
  intro f g le
  rw [Nat.mod_eq_of_lt (Char.ofOrdinal._proof_3 f), Nat.mod_eq_of_lt (Char.ofOrdinal._proof_3 g)]
  exact Nat.add_le_add_right le _

public theorem Char.ofOrdinal_ordinal._proof_1_1 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_ordinal._proof_1_1) := fun {c} _ _ => c.val.toNat_lt

public theorem Char.ofOrdinal_ordinal._proof_1_4 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_ordinal._proof_1_4) := by
  intro c h
  have low : c.val.toNat < 55296 := charCut ▸ UInt32.lt_iff_toNat_lt.mp h
  rw [dite_eq_left low]
  exact UInt32.toNat.inj UInt32.toNat_ofNatLT

public theorem Char.ofOrdinal_ordinal._proof_1_5 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_ordinal._proof_1_5) := by
  intro c high
  have lower : 55296 ≤ c.val.toNat := Nat.le_of_not_lt fun low =>
    high (UInt32.lt_iff_toNat_lt.mpr (charCut.symm ▸ low))
  rw [Nat.sub_add_cancel (Nat.le_trans (by decide : 2048 ≤ 55296) lower)]
  exact Nat.mod_eq_of_lt c.val.toNat_lt

public theorem Char.ofOrdinal_ordinal._proof_1_6 :
    type_of% (private_decl% @_root_.Char.ofOrdinal_ordinal._proof_1_6) := by
  intro c high
  obtain low | large := charValid c
  · exact (high (UInt32.lt_iff_toNat_lt.mpr (charCut.symm ▸ low))).elim
  · exact Nat.not_lt_of_ge (Nat.le_sub_of_add_le large)

public theorem Char.ordinal_le_of_le._proof_1_4 :
    type_of% (private_decl% @_root_.Char.ordinal_le_of_le._proof_1_4) := fun {_ d} le => packMono (charValid d) le

public theorem Char.ordinal_ofOrdinal._proof_1_1 :
    type_of% (private_decl% @_root_.Char.ordinal_ofOrdinal._proof_1_1) := fun {f} => Char.ofOrdinal._proof_3 f

public theorem Char.ordinal_ofOrdinal._proof_1_2 :
    type_of% (private_decl% @_root_.Char.ordinal_ofOrdinal._proof_1_2) := by
  intro f high
  rw [Nat.mod_eq_of_lt (Char.ofOrdinal._proof_3 f)]
  exact Nat.le_trans (Nat.le_of_not_lt high) (Nat.le_add_right ..)

public theorem Char.succ?._proof_5 :
    type_of% (private_decl% @_root_.Char.succ?._proof_5) := by
  intro c lower different upper
  have pre : (0xd7ff : UInt32).toNat = 0xd7ff := UInt32.toNat_ofNat_of_lt (by decide)
  have limit : (0x10ffff : UInt32).toNat = 0x10ffff := UInt32.toNat_ofNat_of_lt (by decide)
  have valid := Char.succ?._proof_3 c
    (fun low => Nat.not_lt_of_ge lower (pre ▸ UInt32.lt_iff_toNat_lt.mp low))
    (fun e => different ((congrArg UInt32.toNat e).trans pre))
    (UInt32.lt_iff_toNat_lt.mpr (limit.symm ▸ upper))
  change (c.val + 1).toNat.isValidChar at valid
  rw [UInt32.toNat_add] at valid
  exact valid

public theorem Char.succ?_eq._proof_1_11 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_11) := by
  intro c lo ne hi
  let d : Char := ⟨c.val + 1, Char.succ?._proof_3 c lo ne hi⟩
  exact (ordinalStepAbove c d rfl lo ne) ▸ d.ordinal.isLt

public theorem Char.succ?_eq._proof_1_10 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_10) := fun {c} high => Nat.not_lt_of_ge
  (Nat.le_trans (Nat.le_of_not_lt (Char.ofOrdinal_ordinal._proof_1_6 (c := c) high)) (Nat.le_succ _))

public theorem Char.succ?_eq._proof_1_12 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_12) := fun {_} le => Nat.succ_le_succ (Nat.succ_le_succ le)

public theorem Char.succ?_eq._proof_1_13 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_13) := fun {c} high => (ordinalNextNone c high).symm

public theorem Char.succ?_eq._proof_1_5 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_5) := by
  intro c low _ _ ge
  have pre : (55295 : UInt32).toNat = 55295 := UInt32.toNat_ofNat_of_lt (by decide)
  exact (Nat.not_lt_of_ge ge (pre ▸ UInt32.lt_iff_toNat_lt.mp low)).elim

public theorem Char.succ?_eq._proof_1_7 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_7) := by
  intro c low
  have below : c.val < 55296 := UInt32.lt_trans low (by decide)
  have h : c.val.toNat < 55296 := charCut ▸ UInt32.lt_iff_toNat_lt.mp below
  rw [ite_eq_left below]
  exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h) (by decide)

public theorem Char.succ?_eq._proof_1_9 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_9) := by
  intro c high
  have lo : 55296 ≤ c.val.toNat := Nat.le_of_not_lt fun h =>
    high (UInt32.lt_iff_toNat_lt.mpr (charCut.symm ▸ h))
  rw [Nat.add_right_comm (c.val.toNat - 2048) 1 2048,
    Nat.sub_add_cancel (Nat.le_trans (by decide : 2048 ≤ 55296) lo)]

public theorem Char.val_ofOrdinal._proof_1_2 :
    type_of% (private_decl% @_root_.Char.val_ofOrdinal._proof_1_2) := fun le => Nat.lt_of_le_of_lt le (by decide : 55295 < UInt32.size)

public theorem Char.val_ofOrdinal._proof_1_3 :
    type_of% (private_decl% @_root_.Char.val_ofOrdinal._proof_1_3) := fun le => Nat.lt_of_le_of_lt le (by decide : 55295 < 4294967296)

public theorem Char.val_ofOrdinal._proof_1_4 :
    type_of% (private_decl% @_root_.Char.val_ofOrdinal._proof_1_4) := fun le => Or.inl (UInt32.toNat_ofNatLT.symm ▸ Nat.lt_succ_of_le le)

public theorem Char.val_ofOrdinal._proof_1_5 :
    type_of% (private_decl% @_root_.Char.val_ofOrdinal._proof_1_5) := fun {f} denied => Char.ofOrdinal._proof_4 f (fun low => denied (Nat.le_of_lt_succ low))

public theorem Char.val_ofOrdinal._proof_1_6 :
    type_of% (private_decl% @_root_.Char.val_ofOrdinal._proof_1_6) := @Char.val_ofOrdinal

end OmegaChecks.InitPort.Alternatives
