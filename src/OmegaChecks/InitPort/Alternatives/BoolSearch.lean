module
public import Init.Data.Array.Lemmas
public import Init.Data.List.Monadic
import all Init.Data.List.Control
import all Init.Data.Array.Basic

/-! Short-circuiting monadic list tests and their array correspondence. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose, implemented_by _root_.List.anyM] public noncomputable def List.anyM
    {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) : List α → m Bool :=
  List.rec (pure false) (fun a _ tail => p a >>= fun b => if b then pure true else tail)

@[expose, implemented_by _root_.List.allM] public noncomputable def List.allM
    {m : Type → Type u} [Monad m] {α : Type v} (p : α → m Bool) : List α → m Bool :=
  List.rec (pure true) (fun a _ tail => p a >>= fun b => if b then tail else pure false)

@[expose, implemented_by _root_.List.findM?] public noncomputable def List.findM?
    {m : Type → Type u} [Monad m] {α : Type} (p : α → m Bool) : List α → m (Option α) :=
  List.rec (pure none) (fun a _ tail => p a >>= fun b => if b then pure (some a) else tail)

public theorem List.anyM_cons [Monad m] {p : α → m Bool} {x : α} {xs : List α} :
    List.anyM p (x :: xs) = (do if ← p x then return true else List.anyM p xs) := rfl

public theorem List.allM_cons [Monad m] {p : α → m Bool} {x : α} {xs : List α} :
    List.allM p (x :: xs) = (do if ← p x then List.allM p xs else return false) := rfl

public theorem Array.anyM_toList [Monad m] {p : α → m Bool} {as : Array α} :
    List.anyM p as.toList = as.anyM p := by
  obtain ⟨xs⟩ := as
  induction xs with
  | nil =>
    have exhausted : min (Array.mk ([] : List α)).size (Array.mk ([] : List α)).size ≤ 0 := Nat.le_refl _
    rw [_root_.Array.anyM_stop_le_start exhausted]
    rfl
  | cons a xs ih =>
    rw [List.anyM_cons]
    unfold _root_.Array.anyM
    rw [dite_eq_left (Nat.le_refl _)]
    dsimp only
    rw [_root_.Array.anyM.loop.eq_def]
    have pos : 0 < (Array.mk (a :: xs)).size := Nat.zero_lt_succ _
    rw [dite_eq_left pos]
    apply congrArg (fun tail => p a >>= fun b => if b then pure true else tail)
    change List.anyM p xs = _root_.Array.anyM.loop p ⟨a :: xs⟩ (xs.length + 1) _ (0 + 1)
    rw [_root_.Array.anyM_loop_cons]
    rw [ih]
    unfold _root_.Array.anyM
    rw [dite_eq_left (Nat.le_refl _)]
    rfl

end OmegaChecks.InitPort.Alternatives
