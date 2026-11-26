module
public import Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Slice
public import OmegaChecks.InitPort.Alternatives.StringSearch

/-! Pointwise agreement of finite slice operations with the official iterator operations. -/

namespace OmegaChecks.Interface.Equations

public theorem String.Slice.foldl (f : α → Char → α) (init : α) (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.foldl f init s = s.foldl f init :=
  _root_.String.Slice.foldl_eq_foldl_toList.symm

public theorem String.Slice.foldr (f : Char → α → α) (init : α) (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.foldr f init s = s.foldr f init :=
  _root_.String.Slice.foldr_eq_foldr_toList.symm

public theorem String.Slice.isNat (s : String.Slice) :
    OmegaChecks.InitPort.Alternatives.String.Slice.isNat s = s.isNat := by
  unfold OmegaChecks.InitPort.Alternatives.String.Slice.isNat _root_.String.Slice.isNat
  simp only [_root_.String.Slice.forIn_eq_forIn_toList (m := Id)]

end OmegaChecks.Interface.Equations
