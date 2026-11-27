module

public import OmegaChecks.InitPort.WordFold
public import OmegaChecks.InitPort.WordForIn
public import OmegaChecks.InitPort.SyntaxArray
public import OmegaChecks.InitPort.BorrowedIndex
public import OmegaChecks.InitPort.ArrayWord
public import Init.Data.RArray
public import Init.Data.Array.DecidableEq
public import Init.Data.Array.Lemmas
import all Init.Data.Array.Basic
public import OmegaChecks.InitPort.Alternatives.ArrayFind
import all OmegaChecks.InitPort.Alternatives.ArrayFind
public import OmegaChecks.InitPort.ArrayModify
public import Init.Data.Vector.Lex
public import Init.Data.Vector.Attach
public import OmegaChecks.InitPort.Alternatives.ByteArray
import all OmegaChecks.InitPort.Alternatives.ByteArray

/-! Pointwise correspondence between the strict list-backed array operations and pinned Init. -/

namespace OmegaChecks.Interface.Equations

public theorem Array.findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w}
    [Monad m] (f : α → m (Option β)) (xs : Array α) :
    OmegaChecks.InitPort.Alternatives.Array.findSomeRevM? f xs = _root_.Array.findSomeRevM? f xs := by
  let go : (i : Nat) → i ≤ xs.size → m (Option β) :=
    (private_decl% @Array.findSomeRevM?.find) (m := m) f xs
  have eq (i : Nat) (h : i ≤ xs.size) :
      OmegaChecks.InitPort.Alternatives.revPrefix f xs i h = go i h := by
    induction i with
    | zero => rfl
    | succ i ih =>
      dsimp only [go]
      rw [Array.findSomeRevM?.find]
      change (f xs[i] >>= _) = f xs[i] >>= _
      apply congrArg (fun k => f xs[i] >>= k)
      funext r
      cases r with
      | none => exact ih _
      | some => rfl
  exact eq _ _

public theorem ByteArray.fastAppend (a b : ByteArray) :
    OmegaChecks.InitPort.Alternatives.ByteArray.fastAppend a b = a.fastAppend b :=
  _root_.ByteArray.fastAppend_eq.symm

public theorem List.pmapImpl {α : Type u} {β : Type v} {P : α → Prop}
    (f : ∀ a, P a → β) (xs : List α) (h : ∀ a ∈ xs, P a) :
    _root_.List.pmap f xs h = _root_.List.pmapImpl f xs h := by
  rw [_root_.List.pmap_eq_pmapImpl]

public theorem Array.pmapImpl {α : Type u} {β : Type v} {P : α → Prop}
    (f : ∀ a, P a → β) (xs : Array α) (h : ∀ a ∈ xs, P a) :
    _root_.Array.pmap f xs h = _root_.Array.pmapImpl f xs h := by
  rw [_root_.Array.pmap_eq_pmapImpl]

public theorem Vector.pmapImpl {α : Type u} {β : Type v} {n : Nat} {P : α → Prop}
    (f : ∀ a, P a → β) (xs : Vector α n) (h : ∀ a ∈ xs, P a) :
    _root_.Vector.pmap f xs h = _root_.Vector.pmapImpl f xs h := by
  rw [_root_.Vector.pmap_eq_pmapImpl]

public theorem Lean.RArray.getImpl {α : Type u} (a : _root_.Lean.RArray α) (i : Nat) :
    a.get i = a.getImpl i := by
  rw [_root_.Lean.RArray.get_eq_getImpl]

public theorem Array.instDecidableEq {α : Type u} [DecidableEq α] :
    @_root_.Array.instDecidableEqImpl α _ = @_root_.Array.instDecidableEq α _ := by
  rw [_root_.Array.instDecidableEq_csimp]

public theorem Array.instDecidableEqEmpImpl {α : Type u} (xs : Array α) :
    _root_.Array.instDecidableEqEmp xs = _root_.Array.instDecidableEqEmpImpl xs :=
  Subsingleton.elim _ _

public theorem Array.instDecidableEmpEqImpl {α : Type u} (xs : Array α) :
    _root_.Array.instDecidableEmpEq xs = _root_.Array.instDecidableEmpEqImpl xs :=
  Subsingleton.elim _ _

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
