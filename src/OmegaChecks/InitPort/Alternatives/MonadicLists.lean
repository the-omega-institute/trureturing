module
public import Init.Data.Array.Monadic
import all Init.Data.Array.Basic
public import Init.Data.List.Monadic
import all Init.Data.List.Control
import Init.Data.List.Attach

/-! Reduction of pure monadic list operations on arbitrary accumulators. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.mapM_pure : type_of% @_root_.List.mapM_pure := by
  intro m α β mon law xs f
  have loop (xs : List α) (acc : List β) :
      _root_.List.mapM.loop (m := m) (fun x => pure (f x)) xs acc =
        pure (acc.reverse ++ xs.map f) := by
    induction xs generalizing acc with
    | nil => exact congrArg pure (List.append_nil acc.reverse).symm
    | cons a as ih =>
      rw [List.mapM.loop, pure_bind, ih, List.reverse_cons, List.append_assoc]
      rfl
  exact loop xs []

public theorem List.anyM_pure : type_of% @_root_.List.anyM_pure := by
  intro m α mon law f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.anyM, pure_bind, List.any_cons]
    cases he : f x with
    | false => exact ih
    | true => rfl

public theorem List.allM_pure : type_of% @_root_.List.allM_pure := by
  intro m α mon law f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.allM, pure_bind, List.all_cons]
    cases he : f x with
    | false => rfl
    | true => exact ih

private theorem fixInvariant {A : Sort u} {B : Sort v} (measure : A → Nat) (spec : A → B)
    (action : (x : A) → ((y : A) → measure y < measure x → B) → B)
    (step : ∀ x recur, (∀ y h, recur y h = spec y) → action x recur = spec x) (x : A) :
    WellFounded.Nat.fix measure action x = spec x := by
  have go (n : Nat) (x : A) (hn : measure x < n) :
      WellFounded.Nat.fix.go measure action n x hn = spec x := by
    induction n generalizing x with
    | zero => exact False.elim (Nat.not_lt_zero _ hn)
    | succ n ih => exact step x _ (fun y _ => ih y _)
  exact go _ x _

public theorem Array.mapM_pure : type_of% @_root_.Array.mapM_pure := by
  intro m α β mon law xs f
  let spec (p : (_ : Nat) ×' Array β) : m (Array β) :=
    pure (p.2.toList ++ (xs.toList.drop p.1).map f).toArray
  have run (i : Nat) (acc : Array β) :
      Array.mapM.map (m := m) (fun x => pure (f x)) xs i acc = spec ⟨i, acc⟩ := by
    delta Array.mapM.map Array.mapM.map._unary
    apply fixInvariant _ spec
    rintro ⟨j, bs⟩ recur ih
    dsimp only
    by_cases h : j < xs.size
    · rw [dite_eq_left h, pure_bind, ih]
      dsimp only [spec]
      rw [List.drop_eq_getElem_cons (l := xs.toList) (i := j) h, Array.toList_push,
        List.append_assoc]
      rfl
    · rw [dite_eq_right h]
      dsimp only [spec]
      rw [List.drop_of_length_le (Nat.le_of_not_gt h), List.map_nil, List.append_nil]
  change Array.mapM.map (m := m) (fun x => pure (f x)) xs 0 #[] = _
  rw [run]
  exact congrArg pure (Array.ext' _root_.Array.toList_map.symm)

end OmegaChecks.InitPort.Alternatives
