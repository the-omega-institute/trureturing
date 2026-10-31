import Lean

/-! A conservative, target-independent necessary condition for one-step lookup.
The finite dependency graph includes every potential proposition obligation and
instance argument, as well as all occurrences in the conclusion. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta

structure StarDeterminationPlan where
  supported : Bool := true
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
  !plan.supported ||
    (starDeterminationClosed plan support && plan.required.any (fun i => !support.contains i))

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
  -- Subtype.property can expose a computation in the candidate's value,
  -- determining arguments absent from its signature. Keep all data-valued
  -- candidates; only proof-valued declarations use this signature analysis.
  unless ← isProp type do
    let sort ← withReducible <| whnf (← inferType type)
    -- A universe that can become Prop must remain eligible. For genuinely
    -- data-valued declarations R only admits a Subtype.property view.
    let definitelyData := match sort with
      | .sort level => level.isNeverZero
      | _ => false
    unless definitelyData do return false
    let subtype ← forallTelescopeReducing type fun _ body => do
      return (← withReducible <| whnf body).isAppOfArity ``Subtype 2
    if subtype then return false
    let unsupported : StarDeterminationPlan := {
      supported := false, required := [], seeds := [], dependencies := []}
    return staticStarImpossible unsupported []
  let plan ← starDeterminationPlan type
  let size := plan.required.length + plan.seeds.length
  return staticStarImpossible plan (starDeterminationSupport plan size)

end LeanInformationAudit.SearchReduction
