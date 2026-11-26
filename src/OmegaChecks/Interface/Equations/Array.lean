module

public import Init.Data.Array.Lemmas
public import Init.Data.Vector.Lex
public import OmegaChecks.InitPort.Alternatives.ByteArray
import all OmegaChecks.InitPort.Alternatives.ByteArray

/-! Pointwise correspondence between the strict list-backed array operations and pinned Init. -/

namespace OmegaChecks.Interface.Equations

public theorem ByteArray.fastAppend (a b : ByteArray) :
    OmegaChecks.InitPort.Alternatives.ByteArray.fastAppend a b = a.fastAppend b :=
  _root_.ByteArray.fastAppend_eq.symm

public theorem Array.lex {α : Type u} [BEq α] (xs ys : Array α) (lt : α → α → Bool) :
    xs.toList.lex ys.toList lt = xs.lex ys lt := _root_.Array.lex_toList

public theorem Vector.lex {α : Type u} {n : Nat} [BEq α] (xs ys : Vector α n) (lt : α → α → Bool) :
    xs.toArray.lex ys.toArray lt = xs.lex ys lt := _root_.Vector.lex_toArray

public theorem Array.append {α : Type u} (as bs : Array α) :
    _root_.Array.mk (List.append as.toList bs.toList) = _root_.Array.append as bs :=
  _root_.Array.ext' _root_.Array.toList_append.symm

public theorem Array.map {α : Type u} {β : Type v} (f : α → β) (as : Array α) :
    _root_.Array.mk (List.map f as.toList) = _root_.Array.map f as :=
  _root_.Array.ext' _root_.Array.toList_map.symm

public theorem Array.eraseIdxIfInBounds {α : Type u} (xs : Array α) (i : Nat) :
    _root_.Array.mk (List.eraseIdx xs.toList i) = _root_.Array.eraseIdxIfInBounds xs i :=
  _root_.Array.ext' _root_.Array.toList_eraseIdxIfInBounds.symm

public theorem Array.eraseIdx {α : Type u} (xs : Array α) (i : Nat) (h : i < xs.size) :
    _root_.Array.mk (List.eraseIdx xs.toList i) = _root_.Array.eraseIdx xs i h :=
  _root_.Array.ext' _root_.Array.toList_eraseIdx.symm

end OmegaChecks.Interface.Equations
