module
import all Init.Data.AC

/-! Evaluation of associative expressions through sorting, duplicate removal and neutral removal. -/

open Lean.Data.AC
namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Data.AC.Context.evalList_append : type_of% @_root_.Lean.Data.AC.Context.evalList_append := by
  intro α ctx l r
  induction l using _root_.Lean.Data.AC.List.two_step_induction with
  | empty => exact fun h => (h rfl).elim
  | single x =>
    intro _ hr
    cases r with
    | nil => exact (hr rfl).elim
    | cons y ys => rfl
  | step x y ys ih =>
    intro _ hr
    exact (congrArg (ctx.op (ctx.var x).value) (ih (fun h => nomatch h) hr)).trans
      (ctx.assoc.assoc _ _ _).symm

private theorem evalCons {α : Sort u} (ctx : Context α) (x : Nat) {ys : List Nat} (ne : ys ≠ []) :
    evalList α ctx (x :: ys) = ctx.op (ctx.var x).value (evalList α ctx ys) := by
  cases ys with
  | nil => exact (ne rfl).elim
  | cons => rfl

private theorem consNonempty {α : Type u} (x : α) (xs : List α) : x :: xs ≠ [] := fun h => nomatch h

public theorem Lean.Data.AC.Context.evalList_sort_congr : type_of% @_root_.Lean.Data.AC.Context.evalList_sort_congr := by
  intro α a b c ctx comm same ha hb
  induction c generalizing a b with
  | nil => exact same
  | cons x xs ih =>
    apply ih (a := insert x a) (b := insert x b) _ insert_nonEmpty insert_nonEmpty
    exact (ctx.evalList_insert comm x a).trans ((evalCons ctx x ha).trans
      ((congrArg (ctx.op (ctx.var x).value) same).trans ((evalCons ctx x hb).symm.trans
        (ctx.evalList_insert comm x b).symm)))

public theorem Lean.Data.AC.Context.evalList_sort_loop_swap : type_of% @_root_.Lean.Data.AC.Context.evalList_sort_loop_swap := by
  intro α y ctx comm acc ys
  exact ctx.evalList_sort_congr comm (ctx.evalList_insert comm y acc) insert_nonEmpty (consNonempty y acc)

private theorem foldSorted {α : Sort u} (ctx : Context α) (comm : Std.Commutative ctx.op)
    (acc xs : List Nat) (ha : acc ≠ []) (hx : xs ≠ []) :
    evalList α ctx (sort.loop acc xs) = ctx.op (evalList α ctx acc) (evalList α ctx xs) := by
  induction xs using _root_.Lean.Data.AC.List.two_step_induction generalizing acc with
  | empty => exact (hx rfl).elim
  | single x =>
    exact (ctx.evalList_insert comm x acc).trans ((evalCons ctx x ha).trans (comm.comm ..))
  | step x y ys ih =>
    exact (ih (insert x acc) insert_nonEmpty (consNonempty y ys)).trans
      ((congrArg (fun a => ctx.op a (evalList α ctx (y :: ys))) ((ctx.evalList_insert comm x acc).trans
        ((evalCons ctx x ha).trans (comm.comm ..)))).trans (ctx.assoc.assoc ..))

private theorem sortedValue {α : Sort u} (ctx : Context α) (comm : Std.Commutative ctx.op)
    (xs : List Nat) : evalList α ctx (sort xs) = evalList α ctx xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => exact foldSorted ctx comm [x] (y :: ys) (consNonempty x []) (consNonempty y ys)

public theorem Lean.Data.AC.Context.evalList_sort_cons : type_of% @_root_.Lean.Data.AC.Context.evalList_sort_cons := by
  intro α ctx comm x xs
  cases xs with
  | nil => rfl
  | cons y ys =>
    let ne : sort (y :: ys) ≠ [] := _root_.Lean.Data.AC.Context.sort_loop_nonEmpty [y] (consNonempty y [])
    exact (sortedValue ctx comm (x :: y :: ys)).trans
      ((congrArg (ctx.op (ctx.var x).value) (sortedValue ctx comm (y :: ys)).symm).trans (evalCons ctx x ne).symm)

public theorem Lean.Data.AC.Context.evalList_sort : type_of% @_root_.Lean.Data.AC.Context.evalList_sort := by
  intro α ctx h xs
  exact sortedValue ctx ((ctx.comm.get (show ctx.comm.isSome = true from h)).down) xs

private theorem mergeNonempty (x : Nat) (xs : List Nat) : mergeIdem.loop x xs ≠ [] := by
  induction xs generalizing x with
  | nil => exact consNonempty x []
  | cons y ys ih =>
    unfold mergeIdem.loop
    split
    · exact ih x
    · exact consNonempty x _

public theorem Lean.Data.AC.Context.mergeIdem_nonEmpty : type_of% @_root_.Lean.Data.AC.Context.mergeIdem_nonEmpty := by
  intro xs ne
  cases xs with
  | nil => exact (ne rfl).elim
  | cons x xs => exact mergeNonempty x xs

private theorem absorbHead {α : Sort u} (ctx : Context α) (idem : Std.IdempotentOp ctx.op)
    (x : Nat) (xs : List Nat) : ctx.op (ctx.var x).value (evalList α ctx (x :: xs)) = evalList α ctx (x :: xs) := by
  cases xs with
  | nil => exact idem.idempotent _
  | cons y ys =>
    exact (ctx.assoc.assoc ..).symm.trans (congrArg (fun a => ctx.op a (evalList α ctx (y :: ys))) (idem.idempotent _))

public theorem Lean.Data.AC.Context.evalList_mergeIdem : type_of% @_root_.Lean.Data.AC.Context.evalList_mergeIdem := by
  intro α ctx hasIdem xs
  have idem := (ctx.idem.get (show ctx.idem.isSome = true from hasIdem)).down
  induction xs using _root_.Lean.Data.AC.List.two_step_induction with
  | empty => rfl
  | single x => rfl
  | step x y ys ih =>
    by_cases eq : x = y
    · cases eq
      exact (congrArg (evalList α ctx) (_root_.Lean.Data.AC.Context.mergeIdem_head ..)).trans
        (ih.trans (absorbHead ctx idem x ys).symm)
    · exact (congrArg (evalList α ctx) (_root_.Lean.Data.AC.Context.mergeIdem_head2 eq)).trans
        ((evalCons ctx x (mergeNonempty y ys)).trans (congrArg (ctx.op (ctx.var x).value) ih))

private def neutralResult {α : Sort u} (ctx : Context α) (xs : List Nat) : List Nat → Prop
  | [] => Std.LawfulIdentity ctx.op (evalList α ctx xs)
  | y :: ys => evalList α ctx (y :: ys) = evalList α ctx xs

private theorem neutralLoop {α : Sort u} (ctx : Context α) (xs : List Nat) (ne : xs ≠ []) :
    neutralResult ctx xs (removeNeutrals.loop ctx xs) := by
  induction xs using _root_.Lean.Data.AC.List.two_step_induction with
  | empty => exact (ne rfl).elim
  | single x =>
    change neutralResult ctx [x] (match ContextInformation.isNeutral ctx x with | true => [] | false => [x])
    cases h : ContextInformation.isNeutral ctx x with
    | false => rfl
    | true => exact _root_.Lean.Data.AC.Context.unwrap_isNeutral h
  | step x y ys ih =>
    have rest := ih (consNonempty y ys)
    unfold removeNeutrals.loop
    cases h : ContextInformation.isNeutral ctx x with
    | true =>
      have unit := _root_.Lean.Data.AC.Context.unwrap_isNeutral h
      have eq : evalList α ctx (x :: y :: ys) = evalList α ctx (y :: ys) := unit.left_id _
      cases ends : removeNeutrals.loop ctx (y :: ys) with
      | nil =>
        rw [ends] at rest
        change Std.LawfulIdentity ctx.op (evalList α ctx (x :: y :: ys))
        rw [eq]
        exact rest
      | cons z zs =>
        rw [ends] at rest
        exact Eq.trans rest eq.symm
    | false =>
      cases ends : removeNeutrals.loop ctx (y :: ys) with
      | nil =>
        rw [ends] at rest
        exact (show Std.LawfulIdentity ctx.op (evalList α ctx (y :: ys)) from rest).right_id _ |>.symm
      | cons z zs =>
        rw [ends] at rest
        exact congrArg (ctx.op (ctx.var x).value) rest

public theorem Lean.Data.AC.Context.evalList_removeNeutrals :
    type_of% @_root_.Lean.Data.AC.Context.evalList_removeNeutrals := by
  intro α ctx xs
  cases xs with
  | nil => rfl
  | cons x xs =>
    have result := neutralLoop ctx (x :: xs) (consNonempty x xs)
    change evalList α ctx (match removeNeutrals.loop ctx (x :: xs) with | [] => [x] | l => l) = _
    cases ends : removeNeutrals.loop ctx (x :: xs) with
    | cons z zs =>
      rw [ends] at result
      exact result
    | nil =>
      rw [ends] at result
      have head : ContextInformation.isNeutral ctx x = true := by
        unfold removeNeutrals.loop at ends
        cases h : ContextInformation.isNeutral ctx x with
        | true => rfl
        | false => rw [h] at ends; contradiction
      let headUnit := _root_.Lean.Data.AC.Context.unwrap_isNeutral head
      let allUnit : Std.LawfulIdentity ctx.op (evalList α ctx (x :: xs)) := result
      exact (allUnit.right_id (ctx.var x).value).symm.trans (headUnit.left_id _)

end OmegaChecks.InitPort.Alternatives
