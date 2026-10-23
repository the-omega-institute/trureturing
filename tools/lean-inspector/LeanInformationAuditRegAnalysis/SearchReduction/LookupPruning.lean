import Lean

/-! A conservative, target-independent necessary condition for one-step lookup.
The finite dependency graph includes every potential proposition obligation and
instance argument, as well as all occurrences in the conclusion. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

structure StarDeterminationPlan where
  required : List Nat
  seeds : List Nat
  dependencies : List (Nat × Nat)
  deriving Inhabited, Repr

/-- A checked barrier contains all initial determination sites and is closed
under type dependencies. An omitted required data argument cannot cross it. -/
def starDeterminationClosed (plan : StarDeterminationPlan) (support : List Nat) : Bool :=
  plan.seeds.all support.contains && plan.dependencies.all fun edge =>
    !support.contains edge.1 || support.contains edge.2

def staticStarImpossible (plan : StarDeterminationPlan) (support : List Nat) : Bool :=
  starDeterminationClosed plan support && plan.required.any (fun i => !support.contains i)

def starDeterminationSupport (plan : StarDeterminationPlan) (size : Nat) : List Nat :=
  (List.range size).foldl (fun support _ => plan.dependencies.foldl (fun known edge =>
    if known.contains edge.1 && !known.contains edge.2 then edge.2 :: known else known) support)
    plan.seeds

/-- Overapproximate every way R can assign an argument: conclusion matching,
unification of proposition premises, instance synthesis (including outParams),
and the types of arguments already assigned. Sort-polymorphic arguments that
can become proofs are seeds too. Unknown analysis always retains the candidate.
Raw occurrences deliberately overapproximate reducible/erased occurrences. -/
def starDeterminationPlan (type : Expr) : MetaM StarDeterminationPlan :=
  forallTelescopeReducing type fun xs body => do
    let occurs (e : Expr) (x : Expr) := (e.find? (· == x)).isSome
    let mut required := []
    let mut seeds := []
    let mut dependencies := []
    for h : i in [:xs.size] do
      let x := xs[i]
      let decl ← getFVarLocalDecl x
      let sort ← withReducible <| whnf (← inferType decl.type)
      let definitelyData := match sort with
        | .sort level => level.isNeverZero
        | _ => false
      if decl.binderInfo.isInstImplicit || !definitelyData || occurs body x then
        seeds := i :: seeds
      if definitelyData && !decl.binderInfo.isInstImplicit then
        required := i :: required
      for h : j in [:xs.size] do
        if occurs decl.type xs[j] then dependencies := (i, j) :: dependencies
    return {required, seeds, dependencies}

def starCandidateImpossible (type : Expr) : MetaM Bool := do
  let plan ← starDeterminationPlan type
  let size := plan.required.length + plan.seeds.length
  return staticStarImpossible plan (starDeterminationSupport plan size)

end LeanInformationAudit.SearchReduction
