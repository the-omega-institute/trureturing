import Init.Data.Array.Lemmas
import Init.Data.List.Monadic
import Init.Data.Vector.Lemmas
import Init.Internal.Order.Lemmas

#check @_root_.List.findM?_pure
#check @_root_.List.anyM_cons
#check @_root_.List.allM_cons
#check @_root_.List.anyM_pure
#check @_root_.List.allM_pure
#check @_root_.Array.anyM_toList
#check @_root_.List.anyM_toArray
#check @_root_.List.anyM_toArray'
#check @_root_.Vector.anyM_toList
#check @_root_.Lean.Order.List.monotone_allM
#check @_root_.Lean.Order.List.monotone_anyM
#check @_root_.Lean.Order.List.monotone_findM?

private abbrev Search := _root_.EStateM Nat Nat
private abbrev searchMonad := @_root_.EStateM.instMonad Nat Nat

private def input : _root_.List Nat := .cons 1 (.cons 4 (.cons 5 .nil))

private def step (key failAt value : Nat) : Search Bool := fun prior =>
  let visited := 10 * prior + value
  if value == failAt then .error 9 visited else .ok (value == key) visited

private def observe (decode : α → Nat) (action : Search α) : Nat × Nat :=
  _root_.EStateM.Result.casesOn (action 0) (fun value state => (decode value, state)) (fun _ state => (99, state))

private def searches (values : _root_.List Nat) (key failAt : Nat) :=
  let predicate := step key failAt
  let anyResult := @_root_.List.anyM Search searchMonad Nat predicate values
  let allResult := @_root_.List.allM Search searchMonad Nat (fun x s =>
    _root_.EStateM.Result.casesOn (predicate x s) (fun b next => .ok (!b) next) (fun e next => .error e next)) values
  let found := @_root_.List.findM? Search searchMonad Nat predicate values
  let flag := fun b : Bool => if b then 1 else 0
  (observe flag anyResult, observe flag allResult, observe (fun x => _root_.Option.casesOn x 0 id) found)

#guard searches .nil 4 5 == ((0, 0), (1, 0), (0, 0))
#guard searches input 4 5 == ((1, 14), (0, 14), (4, 14))
#guard searches input 0 0 == ((0, 145), (1, 145), (0, 145))
#guard searches input 5 4 == ((99, 14), (99, 14), (99, 14))
