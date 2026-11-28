module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Fin
public import Init.Data.Range.Polymorphic.UInt
import all Init.Data.Range.Polymorphic.Internal.SignedBitVec
import all Init.Data.Range.Polymorphic.BitVec
import all Init.Data.Range.Polymorphic.SInt
import all Init.Data.Char.Ordinal
import all Init.Data.Range.Polymorphic.Char
import Init.Data.BitVec.Lemmas
public import OmegaChecks.InitPort.Alternatives.Range.Enumeration
import all OmegaChecks.InitPort.Alternatives.Range.Enumeration

/-! Size laws for fixed-width integer ranges. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

private theorem enumerableImage {α : Type u} {β : Type v} [UpwardEnumerable α] [UpwardEnumerable β]
    [LawfulUpwardEnumerable α] (f : α → β) (g : β → α)
    (left : ∀ a, g (f a) = a) (right : ∀ b, f (g b) = b)
    (next : ∀ a, succ? (f a) = (succ? a).map f)
    (many : ∀ k a, succMany? k (f a) = (succMany? k a).map f) :
    LawfulUpwardEnumerable β where
  ne_of_lt a _ := by
    rintro ⟨n, reaches⟩ rfl
    generalize ha : g a = x
    have eq : f x = a := ha ▸ right a
    rw [← eq, many] at reaches
    cases hs : succMany? (n + 1) x with
    | none => rw [hs] at reaches; cases reaches
    | some y =>
      rw [hs] at reaches
      have same := (left y).symm.trans ((congrArg g (Option.some.inj reaches)).trans (left x))
      exact LawfulUpwardEnumerable.ne_of_lt _ _ ⟨n, hs⟩ same.symm
  succMany?_zero b := by
    rw [← right b, many, LawfulUpwardEnumerable.succMany?_zero]
    rfl
  succMany?_add_one k b := by
    generalize h : g b = a
    have eq : f a = b := h ▸ right b
    rw [← eq, many, many, LawfulUpwardEnumerable.succMany?_add_one]
    cases middle : succMany? k a with
    | none => rfl
    | some y => exact (next y).symm

private theorem closedSizeImage {α : Type u} {β : Type v} [UpwardEnumerable α] [UpwardEnumerable β]
    [LE α] [LE β] [Rxc.HasSize α] [Rxc.HasSize β] [Rxc.LawfulHasSize α]
    (f : α → β) (g : β → α) (left : ∀ a, g (f a) = a) (right : ∀ b, f (g b) = b)
    (next : ∀ a, succ? (f a) = (succ? a).map f)
    (le : ∀ a b, a ≤ b ↔ g a ≤ g b)
    (size : ∀ a b, Rxc.HasSize.size a b = Rxc.HasSize.size (g a) (g b)) :
    Rxc.LawfulHasSize β where
  size_eq_zero_of_not_le a b denied := (size a b).trans
    (Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ fun h => denied ((le a b).mpr h))
  size_eq_one_of_succ?_eq_none a b h stop := by
    have eq := (next (g a)).symm.trans ((congrArg succ? (right a)).trans stop)
    have noneEq : succ? (g a) = none := by
      cases hs : succ? (g a) with
      | none => rfl
      | some x => rw [hs] at eq; cases eq
    exact (size a b).trans (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((le a b).mp h) noneEq)
  size_eq_succ_of_succ?_eq_some a b c h step := by
    have eq := (next (g a)).symm.trans ((congrArg succ? (right a)).trans step)
    have someEq : succ? (g a) = some (g c) := by
      cases hs : succ? (g a) with
      | none => rw [hs] at eq; cases eq
      | some x =>
        rw [hs] at eq
        exact congrArg some ((left x).symm.trans (congrArg g (Option.some.inj eq)))
    exact (size a b).trans ((Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((le a b).mp h) someEq).trans
      (congrArg Nat.succ (size c b).symm))

public theorem UInt8.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt8 :=
  enumerableImage UInt8.ofBitVec UInt8.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt8.succ?_ofBitVec) (fun _ _ => UInt8.succMany?_ofBitVec)

public theorem UInt8.instLawfulHasSize : Rxc.LawfulHasSize UInt8 :=
  closedSizeImage UInt8.ofBitVec UInt8.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt8.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt16.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt16 :=
  enumerableImage UInt16.ofBitVec UInt16.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt16.succ?_ofBitVec) (fun _ _ => UInt16.succMany?_ofBitVec)

public theorem UInt16.instLawfulHasSize : Rxc.LawfulHasSize UInt16 :=
  closedSizeImage UInt16.ofBitVec UInt16.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt16.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt32.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt32 :=
  enumerableImage UInt32.ofBitVec UInt32.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt32.succ?_ofBitVec) (fun _ _ => UInt32.succMany?_ofBitVec)

public theorem UInt32.instLawfulHasSize : Rxc.LawfulHasSize UInt32 :=
  closedSizeImage UInt32.ofBitVec UInt32.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt32.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt64.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt64 :=
  enumerableImage UInt64.ofBitVec UInt64.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt64.succ?_ofBitVec) (fun _ _ => UInt64.succMany?_ofBitVec)

public theorem UInt64.instLawfulHasSize : Rxc.LawfulHasSize UInt64 :=
  closedSizeImage UInt64.ofBitVec UInt64.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt64.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem USize.instLawfulUpwardEnumerable : LawfulUpwardEnumerable USize :=
  enumerableImage USize.ofBitVec USize.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => USize.succ?_ofBitVec) (fun _ _ => USize.succMany?_ofBitVec)

public theorem USize.instLawfulHasSize : Rxc.LawfulHasSize USize :=
  closedSizeImage USize.ofBitVec USize.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => USize.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

private theorem encodeOption {α : Type u} {β : Type v} (encode : α → β) (decode : β → α)
    (cancel : ∀ b, encode (decode b) = b) (o : Option β) : o = (o.map decode).map encode := by
  cases o with
  | none => rfl
  | some b => exact congrArg some (cancel b).symm

public theorem HasModel.succ?_encode.{u,v} :
    type_of% (private_decl% @_root_.HasModel.succ?_encode.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model x
  exact encodeOption model.encode model.decode (fun _ => model.encode_decode) _

public theorem HasModel.succMany?_encode.{u,v} :
    type_of% (private_decl% @_root_.HasModel.succMany?_encode.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict k model x
  exact encodeOption model.encode model.decode (fun _ => model.encode_decode) _

private theorem reachesEncoded {α : Type u} {β : Type v} (encode : α → β) (decode : β → α)
    (left : ∀ b, encode (decode b) = b) (right : ∀ a, decode (encode a) = a)
    (s : Option β) (y : α) : s.map decode = some y ↔ s = some (encode y) := by
  cases s with
  | none => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | some b =>
    exact ⟨fun h => congrArg some ((left b).symm.trans (congrArg encode (Option.some.inj h))),
      fun h => congrArg some ((congrArg decode (Option.some.inj h)).trans (right y))⟩

public theorem HasModel.le_iff.{u,v} : type_of% (private_decl% @_root_.HasModel.le_iff.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model x y
  have reach := reachesEncoded model.encode model.decode (fun _ => model.encode_decode)
    (fun _ => model.decode_encode)
  exact ⟨fun ⟨k, h⟩ => ⟨k, (reach _ y).mp h⟩, fun ⟨k, h⟩ => ⟨k, (reach _ y).mpr h⟩⟩

public theorem HasModel.lt_iff.{u,v} : type_of% (private_decl% @_root_.HasModel.lt_iff.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model x y
  have reach := reachesEncoded model.encode model.decode (fun _ => model.encode_decode)
    (fun _ => model.decode_encode)
  exact ⟨fun ⟨k, h⟩ => ⟨k, (reach _ y).mp h⟩, fun ⟨k, h⟩ => ⟨k, (reach _ y).mpr h⟩⟩

public theorem HasModel.instLawfulUpwardEnumerable.{u,v} :
    type_of% (private_decl% @_root_.HasModel.instLawfulUpwardEnumerable.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model
  exact @enumerableImage β α next _root_.HasModel.instUpwardEnumerable laws
    model.decode model.encode (fun _ => model.encode_decode) (fun _ => model.decode_encode)
    (fun _ => _root_.HasModel.succ?_decode) (fun _ _ => _root_.HasModel.succMany?_decode)

public theorem HasModel.instRxcLawfulHasSize.{u,v} :
    type_of% (private_decl% @_root_.HasModel.instRxcLawfulHasSize.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model size sizeLaws
  exact @closedSizeImage β α next _root_.HasModel.instUpwardEnumerable le' le size
    _root_.HasModel.instRxcHasSize sizeLaws model.decode model.encode (fun _ => model.encode_decode)
    (fun _ => model.decode_encode) (fun _ => _root_.HasModel.succ?_decode)
    (fun _ _ => model.le_iff_encode_le) (fun _ _ => rfl)

public theorem HasModel.instRxiLawfulHasSize.{u,v} :
    type_of% (private_decl% @_root_.HasModel.instRxiLawfulHasSize.{u,v}) := by
  intro α le lt β le' lt' next laws weak strict model size sizeLaws
  refine @Rxi.LawfulHasSize.mk α _root_.HasModel.instUpwardEnumerable _root_.HasModel.instRxiHasSize ?_ ?_
  · intro x term
    apply Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (model.encode x)
    change (succ? (model.encode x)).map model.decode = none at term
    cases h : succ? (model.encode x) with
    | none => rfl
    | some y => rw [h] at term; cases term
  · intro x y reaches
    apply Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (model.encode x) (model.encode y)
    exact (reachesEncoded model.encode model.decode (fun _ => model.encode_decode)
      (fun _ => model.decode_encode) _ y).mp reaches

public theorem BitVec.Signed.rotate_map_eq_iff :
    type_of% (private_decl% @_root_.BitVec.Signed.rotate_map_eq_iff) := by
  intro n x y
  cases x <;> cases y
  · exact Iff.rfl
  · exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  · exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  · exact ⟨fun h => congrArg some (_root_.BitVec.Signed.rotate_eq_iff.mp (Option.some.inj h)),
      fun h => congrArg some (_root_.BitVec.Signed.rotate_eq_iff.mpr (Option.some.inj h))⟩

public theorem BitVec.Signed.instLawfulUpwardEnumerable :
    type_of% (private_decl% @_root_.BitVec.Signed.instLawfulUpwardEnumerable) := by
  intro w
  exact @enumerableImage (BitVec w) (BitVec w) _root_.BitVec.instUpwardEnumerable
    _root_.BitVec.Signed.instUpwardEnumerable BitVec.instLawfulUpwardEnumerable
    _root_.BitVec.Signed.rotate _root_.BitVec.Signed.rotate (fun _ => _root_.BitVec.Signed.rotate_rotate)
    (fun _ => _root_.BitVec.Signed.rotate_rotate) (fun _ => _root_.BitVec.Signed.succ?_rotate)
    (fun _ _ => _root_.BitVec.Signed.succMany?_rotate)

public theorem BitVec.Signed.instRxcLawfulHasSize :
    type_of% (private_decl% @_root_.BitVec.Signed.instRxcLawfulHasSize) := by
  intro n
  exact @closedSizeImage (BitVec n) (BitVec n)
    _root_.BitVec.instUpwardEnumerable _root_.BitVec.Signed.instUpwardEnumerable
    _root_.instLEBitVec _root_.BitVec.Signed.instLE
    _root_.BitVec.instRxcHasSize _root_.BitVec.Signed.instRxcHasSize _root_.BitVec.instRxcLawfulHasSize
    _root_.BitVec.Signed.rotate _root_.BitVec.Signed.rotate (fun _ => _root_.BitVec.Signed.rotate_rotate)
    (fun _ => _root_.BitVec.Signed.rotate_rotate) (fun _ => _root_.BitVec.Signed.succ?_rotate)
    (fun _ _ => _root_.BitVec.Signed.sle_iff_rotate_le_rotate) (fun _ _ => rfl)

private theorem closedOfFiniteEnumeration {α : Type u} [UpwardEnumerable α] [LE α]
    (finite : Rxi.IsAlwaysFinite α) : Rxc.IsAlwaysFinite α where
  finite lo _ := by
    obtain ⟨n, stop⟩ := finite.finite lo
    exact ⟨n, by rw [stop]; exact True.intro⟩

private theorem openOfFiniteEnumeration {α : Type u} [UpwardEnumerable α] [LT α]
    (finite : Rxi.IsAlwaysFinite α) : Rxo.IsAlwaysFinite α where
  finite lo _ := by
    obtain ⟨n, stop⟩ := finite.finite lo
    exact ⟨n, by rw [stop]; exact True.intro⟩

public theorem Int8.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int8 where
  finite a := by
    refine ⟨(_root_.Int8.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int8.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int8 :=
  closedOfFiniteEnumeration Int8.instRxiIsAlwaysFinite

public theorem Int8.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int8 :=
  openOfFiniteEnumeration Int8.instRxiIsAlwaysFinite

public theorem Int16.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int16 where
  finite a := by
    refine ⟨(_root_.Int16.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int16.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int16 :=
  closedOfFiniteEnumeration Int16.instRxiIsAlwaysFinite

public theorem Int16.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int16 :=
  openOfFiniteEnumeration Int16.instRxiIsAlwaysFinite

public theorem Int32.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int32 where
  finite a := by
    refine ⟨(_root_.Int32.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int32.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int32 :=
  closedOfFiniteEnumeration Int32.instRxiIsAlwaysFinite

public theorem Int32.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int32 :=
  openOfFiniteEnumeration Int32.instRxiIsAlwaysFinite

public theorem Int64.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int64 where
  finite a := by
    refine ⟨(_root_.Int64.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int64.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int64 :=
  closedOfFiniteEnumeration Int64.instRxiIsAlwaysFinite

public theorem Int64.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int64 :=
  openOfFiniteEnumeration Int64.instRxiIsAlwaysFinite

public theorem ISize.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite ISize where
  finite a := by
    refine ⟨(_root_.ISize.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem ISize.instIsAlwaysFinite : Rxc.IsAlwaysFinite ISize :=
  closedOfFiniteEnumeration ISize.instRxiIsAlwaysFinite

public theorem ISize.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite ISize :=
  openOfFiniteEnumeration ISize.instRxiIsAlwaysFinite

private theorem signedSizeLaws {α : Type u} [UpwardEnumerable α] [LE α] [LT α]
    [Rxc.HasSize α] [Rxo.HasSize α] [Rxi.HasSize α]
    (value : α → Int) (limit : Int) (below : ∀ x, value x < limit)
    (le : ∀ a b, a ≤ b ↔ value a ≤ value b) (lt : ∀ a b, a < b ↔ value a < value b)
    (closedSize : ∀ a b, Rxc.HasSize.size a b = (value b + 1 - value a).toNat)
    (openSize : ∀ a b, Rxo.HasSize.size a b = (value b + 1 - value a).toNat - 1)
    (tailSize : ∀ a, Rxi.HasSize.size a = (limit - value a).toNat)
    (endStep : ∀ a, value a = limit - 1 → succ? a = none)
    (nextStep : ∀ a, value a < limit - 1 → ∃ b, succ? a = some b ∧ value b = value a + 1) :
    Rxc.LawfulHasSize α ∧ Rxo.LawfulHasSize α ∧ Rxi.LawfulHasSize α := by
  have stop {a} (h : succ? a = none) : value a = limit - 1 := by
    by_cases before : value a < limit - 1
    · obtain ⟨_, step, _⟩ := nextStep a before
      rw [h] at step
      cases step
    · have bound := below a
      omega
  have inc {a b} (h : succ? a = some b) : value b = value a + 1 := by
    by_cases last : value a = limit - 1
    · rw [endStep a last] at h
      cases h
    · have bound := below a
      obtain ⟨_, found, eq⟩ := nextStep a (by omega)
      cases Option.some.inj (found.symm.trans h)
      exact eq
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a b denied
    rw [closedSize]
    have h : ¬ value a ≤ value b := fun p => denied ((le a b).mpr p)
    exact Int.toNat_eq_zero.mpr (by omega)
  · intro a b ok stopped
    rw [closedSize]
    have eq := stop stopped
    have lower := (le a b).mp ok
    have upper := below b
    omega
  · intro a b c ok step
    rw [closedSize, closedSize]
    have eq := inc step
    have lower := (le a b).mp ok
    omega
  · intro a b denied
    rw [openSize]
    have h : ¬value a < value b := fun p => denied ((lt a b).mpr p)
    omega
  · intro a b ok stopped
    have eq := stop stopped
    have lower := (lt a b).mp ok
    have upper := below b
    omega
  · intro a b c ok step
    rw [openSize, openSize]
    have eq := inc step
    have lower := (lt a b).mp ok
    omega
  · intro a stopped
    rw [tailSize]
    have eq := stop stopped
    omega
  · intro a b step
    rw [tailSize, tailSize]
    have eq := inc step
    have upper := below b
    omega

private theorem signedPowerSizes {α : Type u} [UpwardEnumerable α] [LE α] [LT α] [DecidableEq α]
    [Rxc.HasSize α] [Rxo.HasSize α] [Rxi.HasSize α]
    (value : α → Int) (k : Nat) (low : α) (addOne : α → α)
    (inj : ∀ {a b}, value a = value b → a = b)
    (below : ∀ a, value a < (2 : Int)^k) (above : ∀ a, -(2 : Int)^k ≤ value a)
    (minValue : value low = -(2 : Int)^k)
    (addValue : ∀ a, value (addOne a) = (value a + 1).bmod (2^(k+1)))
    (next : ∀ a, succ? a = if addOne a = low then none else some (addOne a))
    (le : ∀ a b, a ≤ b ↔ value a ≤ value b) (lt : ∀ a b, a < b ↔ value a < value b)
    (closedSize : ∀ a b, Rxc.HasSize.size a b = (value b + 1 - value a).toNat)
    (openSize : ∀ a b, Rxo.HasSize.size a b = (value b + 1 - value a).toNat - 1)
    (tailSize : ∀ a, Rxi.HasSize.size a = ((2 : Int)^k - value a).toNat) :
    Rxc.LawfulHasSize α ∧ Rxo.LawfulHasSize α ∧ Rxi.LawfulHasSize α := by
  let half := 2^k
  have pos : 0 < half := Nat.two_pow_pos k
  have cast : (2 : Int)^k = (half : Int) := (Int.natCast_pow 2 k).symm
  have full : 2^(k+1) = half + half := (Nat.pow_succ 2 k).trans (Nat.mul_two _)
  apply signedSizeLaws value ((2 : Int)^k) below le lt closedSize openSize tailSize
  · intro a last
    rw [next]
    apply ite_eq_left
    apply inj
    rw [addValue, full, minValue, cast]
    rw [cast] at last
    calc
      _ = (-(half : Int) + ↑(half + half)).bmod (half + half) :=
        congrArg (fun z : Int => z.bmod (half + half)) (by omega)
      _ = (-(half : Int)).bmod (half + half) := Int.add_bmod_right _ _
      _ = _ := Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  · intro a before
    have lowBound := above a
    rw [cast] at before lowBound
    have eq : value (addOne a) = value a + 1 := by
      rw [addValue, full]
      exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
    refine ⟨addOne a, ?_, eq⟩
    rw [next]
    apply ite_eq_right
    intro wrap
    have bad := eq.symm.trans ((congrArg value wrap).trans (minValue.trans (congrArg Neg.neg cast)))
    omega

private theorem Int8SizeLaws : Rxc.LawfulHasSize Int8 ∧ Rxo.LawfulHasSize Int8 ∧ Rxi.LawfulHasSize Int8 := by
  apply signedPowerSizes Int8.toInt 7 _root_.Int8.minValueSealed (· + 1) Int8.toInt.inj
    Int8.toInt_lt Int8.le_toInt
    ((congrArg Int8.toInt _root_.Int8.minValueSealed_def).trans Int8.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int8.le_iff_toInt_le) (fun _ _ => Int8.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int8.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int8.toInt 1 = 1 from rfl))

public theorem Int8.instRxcLawfulHasSize : Rxc.LawfulHasSize Int8 := Int8SizeLaws.1
public theorem Int8.instRxoLawfulHasSize : Rxo.LawfulHasSize Int8 := Int8SizeLaws.2.1
public theorem Int8.instRxiLawfulHasSize : Rxi.LawfulHasSize Int8 := Int8SizeLaws.2.2

private theorem Int16SizeLaws : Rxc.LawfulHasSize Int16 ∧ Rxo.LawfulHasSize Int16 ∧ Rxi.LawfulHasSize Int16 := by
  apply signedPowerSizes Int16.toInt 15 _root_.Int16.minValueSealed (· + 1) Int16.toInt.inj
    Int16.toInt_lt Int16.le_toInt
    ((congrArg Int16.toInt _root_.Int16.minValueSealed_def).trans Int16.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int16.le_iff_toInt_le) (fun _ _ => Int16.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int16.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int16.toInt 1 = 1 from rfl))

public theorem Int16.instRxcLawfulHasSize : Rxc.LawfulHasSize Int16 := Int16SizeLaws.1
public theorem Int16.instRxoLawfulHasSize : Rxo.LawfulHasSize Int16 := Int16SizeLaws.2.1
public theorem Int16.instRxiLawfulHasSize : Rxi.LawfulHasSize Int16 := Int16SizeLaws.2.2

private theorem Int32SizeLaws : Rxc.LawfulHasSize Int32 ∧ Rxo.LawfulHasSize Int32 ∧ Rxi.LawfulHasSize Int32 := by
  apply signedPowerSizes Int32.toInt 31 _root_.Int32.minValueSealed (· + 1) Int32.toInt.inj
    Int32.toInt_lt Int32.le_toInt
    ((congrArg Int32.toInt _root_.Int32.minValueSealed_def).trans Int32.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int32.le_iff_toInt_le) (fun _ _ => Int32.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int32.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int32.toInt 1 = 1 from rfl))

public theorem Int32.instRxcLawfulHasSize : Rxc.LawfulHasSize Int32 := Int32SizeLaws.1
public theorem Int32.instRxoLawfulHasSize : Rxo.LawfulHasSize Int32 := Int32SizeLaws.2.1
public theorem Int32.instRxiLawfulHasSize : Rxi.LawfulHasSize Int32 := Int32SizeLaws.2.2

private theorem Int64SizeLaws : Rxc.LawfulHasSize Int64 ∧ Rxo.LawfulHasSize Int64 ∧ Rxi.LawfulHasSize Int64 := by
  apply signedPowerSizes Int64.toInt 63 _root_.Int64.minValueSealed (· + 1) Int64.toInt.inj
    Int64.toInt_lt Int64.le_toInt
    ((congrArg Int64.toInt _root_.Int64.minValueSealed_def).trans Int64.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int64.le_iff_toInt_le) (fun _ _ => Int64.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int64.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int64.toInt 1 = 1 from rfl))

public theorem Int64.instRxcLawfulHasSize : Rxc.LawfulHasSize Int64 := Int64SizeLaws.1
public theorem Int64.instRxoLawfulHasSize : Rxo.LawfulHasSize Int64 := Int64SizeLaws.2.1
public theorem Int64.instRxiLawfulHasSize : Rxi.LawfulHasSize Int64 := Int64SizeLaws.2.2

private theorem ISizeSizeLaws : Rxc.LawfulHasSize ISize ∧ Rxo.LawfulHasSize ISize ∧ Rxi.LawfulHasSize ISize := by
  apply signedPowerSizes ISize.toInt (System.Platform.numBits - 1) _root_.ISize.minValueSealed (· + 1) ISize.toInt.inj
    ISize.toInt_lt_two_pow_numBits ISize.two_pow_numBits_le_toInt
    ((congrArg ISize.toInt _root_.ISize.minValueSealed_def).trans ISize.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => ISize.le_iff_toInt_le) (fun _ _ => ISize.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  rw [ISize.toInt_add, show ISize.toInt 1 = 1 from ISize.toInt_ofNat_of_lt (by decide),
    Nat.sub_add_cancel System.Platform.numBits_pos]

public theorem ISize.instRxcLawfulHasSize : Rxc.LawfulHasSize ISize := ISizeSizeLaws.1
public theorem ISize.instRxoLawfulHasSize : Rxo.LawfulHasSize ISize := ISizeSizeLaws.2.1
public theorem ISize.instRxiLawfulHasSize : Rxi.LawfulHasSize ISize := ISizeSizeLaws.2.2

public theorem Int16.instLawfulUpwardEnumerableLeast?._proof_2 :
    type_of% (private_decl% @_root_.Int16.instLawfulUpwardEnumerableLeast?._proof_2) :=
  fun _ lower impossible => impossible (Int.add_nonneg_iff_neg_le.mpr lower)

public theorem Int32.instLawfulUpwardEnumerableLeast?._proof_2 :
    type_of% (private_decl% @_root_.Int32.instLawfulUpwardEnumerableLeast?._proof_2) :=
  fun _ lower impossible => impossible (Int.add_nonneg_iff_neg_le.mpr lower)

public theorem Int64.instLawfulUpwardEnumerableLeast?._proof_2 :
    type_of% (private_decl% @_root_.Int64.instLawfulUpwardEnumerableLeast?._proof_2) :=
  fun _ lower impossible => impossible (Int.add_nonneg_iff_neg_le.mpr lower)

public theorem ISize.toBitVec_minValueSealed_eq_intMinSealed :
    type_of% (private_decl% @_root_.ISize.toBitVec_minValueSealed_eq_intMinSealed) :=
  by
  rw [private_decl% @_root_.ISize.minValueSealed_def,
    private_decl% @_root_.BitVec.Signed.intMinSealed_def, _root_.ISize.toBitVec_minValue]
  apply _root_.BitVec.eq_of_toNat_eq
  rw [_root_.BitVec.toNat_intMin, _root_.BitVec.natCast_eq_ofNat, _root_.BitVec.toNat_ofNat]

public theorem ISize.toBitVec_maxValueSealed_eq_intMaxSealed :
    type_of% (private_decl% @_root_.ISize.toBitVec_maxValueSealed_eq_intMaxSealed) :=
  by
  rw [private_decl% @_root_.ISize.maxValueSealed_def,
    private_decl% @_root_.BitVec.Signed.intMaxSealed_def, _root_.ISize.toBitVec_maxValue]
  apply _root_.BitVec.eq_of_toNat_eq
  rw [_root_.BitVec.toNat_intMax, _root_.BitVec.natCast_eq_ofNat, _root_.BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (_root_.BitVec.toNat_intMax (w := System.Platform.numBits) ▸
    (_root_.BitVec.intMax System.Platform.numBits).isLt)).symm

end OmegaChecks.InitPort.Alternatives
