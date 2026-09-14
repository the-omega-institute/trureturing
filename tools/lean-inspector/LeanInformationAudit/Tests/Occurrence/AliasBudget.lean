import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer

open Lean LeanInformationAudit D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.ImportClosureProducer
namespace AliasBudget
local instance : DecidableEq lawArena.State := lawArena.toArena.stateDecidableEq
set_option linter.style.longLine false

def twice (f : Arena → Arena) (a : Arena) : Arena := f (f a)
def expensive := twice (twice (twice (twice (twice (twice (twice (twice (twice (twice (twice (twice id))))))))))) objectArena

/-- error: IE-C003 ArenaResolutionBudgetExceeded arena=AliasBudget.expensive limit=4096 -/
#guard_msgs (error) in
information_theorem budgetTarget
  in lawArena object_arena expensive catalog budget
  primitives fixtureRealization
  : lawArena.Law fixtureRealization := by trivial

run_cmd do
  let env ← getEnv
  unless !(InformationRegistry.hasTheorem env `AliasBudget.budgetTarget) do
    throwError "AliasBudget: budget exhaustion inserts a registration"
  let unit := catalogQualifiedName env.header.mainModule `AliasBudget.expensive
    `budget `AliasBudget.budgetTarget theoremUnitSuffix
  unless !env.contains unit do
    throwError "AliasBudget: budget exhaustion leaves a generated companion"
-- A deep global chain and a single exponential application share the same total bound.
run_cmd do
  let type := (← Lean.getConstInfo
    `LeanInformationAudit.Tests.ImportClosureProducer.objectArena).type
  let mut previous := `LeanInformationAudit.Tests.ImportClosureProducer.objectArena
  for index in [:4200] do
    let name := (`AliasBudget.link).num index
    Lean.Elab.Command.liftCoreM <| addDecl (.defnDecl {
      name, levelParams := [], type, value := mkConst previous,
      hints := .abbrev, safety := .safe })
    previous := name
  Lean.Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := `AliasBudget.longChain, levelParams := [], type,
    value := mkConst previous, hints := .abbrev, safety := .safe })

/-- error: IE-C003 ArenaResolutionBudgetExceeded arena=AliasBudget.longChain limit=4096 -/
#guard_msgs (error) in
run_cmd do
  let _ ← Lean.Elab.Command.liftTermElabM <| resolveCanonicalArenaName `AliasBudget.longChain

run_cmd do
  let owner ← Lean.Elab.Command.liftTermElabM <|
    resolveCanonicalArenaName ((`AliasBudget.link).num 63)
  unless owner == `LeanInformationAudit.Tests.ImportClosureProducer.objectArena do
    throwError "AliasBudget: a bounded chain must resolve after earlier exhaustion"
end AliasBudget
