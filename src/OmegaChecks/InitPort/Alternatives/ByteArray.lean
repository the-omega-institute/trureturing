module
import all Init.Data.ByteArray.Basic
import all Init.Data.ByteArray.Lemmas

/-! Computation rules for byte-array append and conversion to a list. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem copyAtEnd (a b : ByteArray) : b.copySlice 0 a a.size b.size false = a.append b := by
  apply _root_.ByteArray.ext
  apply Array.ext'
  change (((a.data.extract 0 a.data.size ++ b.data.extract 0 (0 + b.data.size)) ++
    a.data.extract (a.data.size + min b.data.size (b.data.size - 0)) a.data.size).toList =
      a.data.toList ++ b.data.toList)
  rw [Nat.zero_add, Array.extract_size, Array.extract_size,
    Array.extract_empty_of_size_le_start (Nat.le_add_right ..), Array.append_empty, Array.toList_append]

public def ByteArray.fastAppend : type_of% @_root_.ByteArray.fastAppend :=
  @_root_.ByteArray.append

public theorem ByteArray.fastAppend_eq_copySlice {a b : ByteArray} :
    ByteArray.fastAppend a b = b.copySlice 0 a a.size b.size false :=
  (copyAtEnd a b).symm

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.ByteArray.fastAppend.eq_1 (a b : ByteArray) :
    ByteArray.fastAppend a b = b.copySlice 0 a a.size b.size false :=
  (copyAtEnd a b).symm

private theorem atFuel {α : Sort u} {C : α → Sort v} (measure : α → Nat)
    (step : (x : α) → ((y : α) → InvImage (· < ·) measure y x → C y) → C x)
    (x : α) (k : Nat) (eq : measure x + 1 = k) : WellFounded.Nat.fix measure step x =
      WellFounded.Nat.fix.go measure step k x (eq ▸ Nat.lt_succ_self _) := by
  let eager := WellFounded.Nat.eager (measure x + 1)
  have hk : eager = k := (WellFounded.Nat.eager_eq _).trans eq
  have he : measure x < eager := Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) (WellFounded.Nat.eager_eq _).symm
  exact congrArg (fun n : {n // measure x < n} => WellFounded.Nat.fix.go measure step n.val x n.property)
    (Subtype.ext (a1 := ⟨eager, he⟩)
      (a2 := ⟨k, eq ▸ Nat.lt_succ_self _⟩) hk)

public theorem ByteArray.toList.loop.eq_def : type_of% @_root_.ByteArray.toList.loop.eq_def := by
  intro bs i r
  delta _root_.ByteArray.toList.loop _root_.ByteArray.toList.loop._unary
  let measure : ((_ : Nat) ×' List UInt8) → Nat := fun x => x.casesOn fun i _ => bs.size - i
  by_cases hi : i < bs.size
  · have bound : measure ⟨i, r⟩ + 1 = bs.size - (i + 1) + 1 + 1 :=
      congrArg Nat.succ (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hi)).symm
    rw [ite_eq_left hi, atFuel (C := fun _ => List UInt8) measure _ ⟨i, r⟩ _ bound,
      atFuel (C := fun _ => List UInt8) measure _ ⟨i + 1, bs.get! i :: r⟩ _ rfl]
    dsimp only [WellFounded.Nat.fix.go, PSigma.casesOn]
    rw [dite_eq_left hi]
  · have bound : measure ⟨i, r⟩ + 1 = Nat.succ 0 :=
      congrArg Nat.succ (Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi))
    rw [ite_eq_right hi, atFuel (C := fun _ => List UInt8) measure _ ⟨i, r⟩ _ bound]
    dsimp only [WellFounded.Nat.fix.go, PSigma.casesOn]
    rw [dite_eq_right hi, List.unattach_reverse, List.unattach_attach]

public theorem ByteArray.toList.loop._unary.eq_def :
    type_of% @_root_.ByteArray.toList.loop._unary.eq_def := by
  intro bs p
  cases p with
  | mk i acc => with_unfolding_all exact ByteArray.toList.loop.eq_def bs i acc

end OmegaChecks.InitPort.Alternatives
