module
public import Init.Data.String.Pattern.String
public import Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.ByteArray.Lemmas
import all Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.String.Basic
import all Init.Data.String.Pattern.String
namespace OmegaChecks.InitPort.Alternatives
public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_16 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_16) := by
  intro pat i hi
  cases i with
  | zero => exact Nat.le_refl 0
  | succ i => exact False.elim (Nat.not_succ_le_zero i (Nat.le_of_succ_le_succ hi))

public theorem ByteArray.extract_eq_empty_iff._proof_1_1 :
    type_of% (private_decl% @ByteArray.extract_eq_empty_iff._proof_1_1) :=
  fun h => h Nat.sub_eq_zero_iff_le

public theorem Std.Iterators.Types.Take.PlausibleStep._proof_1 :
    type_of% (private_decl% @Std.Iterators.Types.Take.PlausibleStep._proof_1) := by
  intro α m β inst it ne pos denied
  exact denied (Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne pos ne.symm))

public theorem String.Pos.isValidUTF8_extract._proof_1_1 :
    type_of% (private_decl% @String.Pos.isValidUTF8_extract._proof_1_1) := by
  intro _ a b h₁ h₂
  exact (Nat.le_total a.offset.byteIdx b.offset.byteIdx).elim h₁ h₂

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_1 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_1) :=
  fun _ _ positive denied => denied (Nat.sub_one_lt_of_lt positive)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance._proof_1 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance._proof_1) :=
  fun _ _ _ h denied => denied (Nat.lt_of_le_of_lt (Nat.sub_le ..) h)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_7 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_7) :=
  fun _ _ bound _ h denied => denied (Nat.lt_of_lt_of_le h bound)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_5 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_5) :=
  fun _ _ h notLt notEq => notEq (Nat.le_antisymm h (Nat.le_of_not_lt notLt))

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_8 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_8) :=
  fun _ _ _ h denied => denied h

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_12 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_12) :=
  fun _ ne denied => denied (Nat.pos_of_ne_zero ne)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_4 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_4) :=
  fun _ _ _ _ _ _ _ _ ne h denied => denied (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) ne)

end OmegaChecks.InitPort.Alternatives
