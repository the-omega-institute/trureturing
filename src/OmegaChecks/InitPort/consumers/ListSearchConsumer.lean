import OmegaInit.Data.Array.Lemmas
import OmegaInit.Data.List.Monadic
import OmegaInit.Data.Vector.Lemmas
import OmegaInit.Internal.Order.Lemmas

#check @Omega.List.findM?_pure
#check @Omega.List.anyM_cons
#check @Omega.List.allM_cons
#check @Omega.List.anyM_pure
#check @Omega.List.allM_pure
#check @Omega.Array.anyM_toList
#check @Omega.List.anyM_toArray
#check @Omega.List.anyM_toArray'
#check @Omega.Vector.anyM_toList
#check @Omega.Lean.Order.List.monotone_allM
#check @Omega.Lean.Order.List.monotone_anyM
#check @Omega.Lean.Order.List.monotone_findM?

private abbrev Search := Omega.EStateM Nat Nat
private abbrev searchMonad := @Omega.EStateM.instMonad Nat Nat

private def input : Omega.List Nat := .cons 1 (.cons 4 (.cons 5 .nil))

private def step (key failAt value : Nat) : Search Bool := fun prior =>
  let visited := 10 * prior + value
  if value == failAt then .error 9 visited else .ok (value == key) visited

private def observe (decode : α → Nat) (action : Search α) : Nat × Nat :=
  Omega.EStateM.Result.casesOn (action 0) (fun value state => (decode value, state)) (fun _ state => (99, state))

private def searches (values : Omega.List Nat) (key failAt : Nat) :=
  let predicate := step key failAt
  let anyResult := @Omega.List.anyM Search searchMonad Nat predicate values
  let allResult := @Omega.List.allM Search searchMonad Nat (fun x s =>
    Omega.EStateM.Result.casesOn (predicate x s) (fun b next => .ok (!b) next) (fun e next => .error e next)) values
  let found := @Omega.List.findM? Search searchMonad Nat predicate values
  let flag := fun b : Bool => if b then 1 else 0
  (observe flag anyResult, observe flag allResult, observe (fun x => Omega.Option.casesOn x 0 id) found)

#guard searches .nil 4 5 == ((0, 0), (1, 0), (0, 0))
#guard searches input 4 5 == ((1, 14), (0, 14), (4, 14))
#guard searches input 0 0 == ((0, 145), (1, 145), (0, 145))
#guard searches input 5 4 == ((99, 14), (99, 14), (99, 14))
