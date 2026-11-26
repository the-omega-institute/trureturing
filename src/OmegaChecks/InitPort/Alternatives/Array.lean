module

public import Init.Data.Array.Basic
public import Init.Data.Nat.Basic

/-! List-backed implementations and induction proofs for the pinned array interfaces. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public def Array.eraseIdx {α : Type u} (xs : _root_.Array α) (i : Nat) (_h : i < xs.size) :
    _root_.Array α := ⟨xs.toList.eraseIdx i⟩

@[expose] public def Array.eraseIdxIfInBounds {α : Type u} (xs : _root_.Array α) (i : Nat) :
    _root_.Array α := ⟨xs.toList.eraseIdx i⟩

public theorem Array.size_eraseIdx {α : Type u} {xs : _root_.Array α} (i : Nat) (h : i < xs.size) :
    (Array.eraseIdx xs i h).size = xs.size - 1 :=
  (List.rec (motive := fun xs : List α => ∀ j, j < xs.length →
      (xs.eraseIdx j).length = xs.length - 1)
    (fun j bound => False.elim (Nat.not_succ_le_zero j bound))
    (fun a tail ih j => Nat.casesOn (motive := fun j => j < (a :: tail).length →
        ((a :: tail).eraseIdx j).length = (a :: tail).length - 1) j
      (fun _ => (Nat.add_one_sub_one tail.length).symm)
      (fun k bound =>
        have fits : k < tail.length := Nat.le_of_succ_le_succ bound
        have nonzero : tail.length ≠ 0 := fun e =>
          Nat.not_succ_le_zero k (Eq.subst (motive := (k < ·)) e fits)
        (congrArg Nat.succ (ih k fits)).trans
          ((Nat.succ_pred_eq_of_ne_zero nonzero).trans (Nat.add_one_sub_one tail.length).symm))) xs.toList) i h

public theorem Array.toList_eraseIdx {α : Type u} {xs : _root_.Array α} {i : Nat} {h : i < xs.size} :
    (Array.eraseIdx xs i h).toList = xs.toList.eraseIdx i := rfl

public theorem List.eraseIdx_toArray {α : Type u} (l : _root_.List α) (i : Nat) (h : i < l.toArray.size) :
    Array.eraseIdx l.toArray i h = (l.eraseIdx i).toArray := rfl

public theorem List.eraseIdxIfInBounds_toArray {α : Type u} (l : _root_.List α) (i : Nat) :
    Array.eraseIdxIfInBounds l.toArray i = (l.eraseIdx i).toArray := rfl

public theorem Array.eraseIdx_eq_eraseIdxIfInBounds {α : Type u} {xs : _root_.Array α}
    {i : Nat} (h : i < xs.size) : Array.eraseIdx xs i h = Array.eraseIdxIfInBounds xs i := rfl

end OmegaChecks.InitPort.Alternatives
