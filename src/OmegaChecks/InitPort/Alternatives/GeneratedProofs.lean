module
public import Init.Data.String.Pattern.String
public import Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.ByteArray.Lemmas
import all Init.Data.Iterators.Combinators.Monadic.Take
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

end OmegaChecks.InitPort.Alternatives
