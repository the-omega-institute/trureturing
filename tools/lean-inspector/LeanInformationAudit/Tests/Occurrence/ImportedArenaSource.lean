import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

run_cmd do
  if (← Lean.getEnv).header.moduleNames.any (fun name =>
      name.getRoot == `LeanInformationAudit || name.getRoot == `LeanInformationAuditInterface) then
    throwError "pure provenance source must not import the judge or its construction hook"

open D5.S3.ConceptDynamics.InformationEscape

namespace ProvenanceProbe

def arena : Arena := Arena.ofFintype Bool
def aliasArena : Arena := arena
abbrev abbreviated := aliasArena
@[reducible] def reducibleAlias := abbreviated
@[irreducible] def opaqueHint := reducibleAlias
def hintedForward := id opaqueHint
def forwarding (_ : Unit) : Arena := arena
def application := forwarding ()
def explicitMk : Arena := Arena.mk arena.State arena.stateFintype arena.stateDecidableEq
def copyArena : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq
def literalCopy : Arena :=
  { State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }
def live := (fun x : Arena => x) copyArena
def dead := (fun _ : Arena => arena) copyArena
def inlineLive := id
  ({ State := arena.State, stateFintype := arena.stateFintype,
     stateDecidableEq := arena.stateDecidableEq } : Arena)
def inlineDead := (fun _ : Arena => arena)
  { State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }
def localCopy := let x : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  x
def localFunctionAlias : Arena :=
  let copy (a : Arena) : Arena := a
  copy arena
def localFunctionCopy : Arena :=
  let copy (a : Arena) : Arena :=
    { State := a.State
      stateFintype := a.stateFintype
      stateDecidableEq := a.stateDecidableEq }
  copy arena
def localFunctionUnused : Arena :=
  let copy (a : Arena.{0}) : Arena :=
    { State := a.State, stateFintype := a.stateFintype,
      stateDecidableEq := a.stateDecidableEq }
  arena
def localFunctionDead : Arena :=
  let copy (a : Arena) : Arena :=
    { State := a.State, stateFintype := a.stateFintype,
      stateDecidableEq := a.stateDecidableEq }
  (fun _ : Arena => arena) (copy arena)
def localFunctionBinders : Arena :=
  let copy (_ _a : Arena) {_b : Arena} ⦃c : Arena⦄ [Inhabited Unit] : Arena :=
    { State := c.State, stateFintype := c.stateFintype,
      stateDecidableEq := c.stateDecidableEq }
  copy arena arena (_b := arena) (c := arena)
def localFunctionLambda : Arena :=
  let copy (_ : Unit) : Arena → Arena := fun a =>
    { State := a.State, stateFintype := a.stateFintype,
      stateDecidableEq := a.stateDecidableEq }
  copy () arena
def localFunctionNested : Arena :=
  let copy a : Arena :=
    let forward (_ : Unit) :=
      ({ State := (a : Arena).State, stateFintype := a.stateFintype,
         stateDecidableEq := a.stateDecidableEq } : Arena)
    forward ()
  copy arena
def localFunctionUnsupported : Arena :=
  let copy (a : Arena) : Arena := by first | exact a
  copy arena
def localFunctionUnsupportedDead : Arena :=
  let copy (a : Arena) : Arena := by first | exact a
  (fun _ : Arena => arena) (copy arena)
def localFunctionUnsupportedUnused : Arena :=
  let copy (a : Arena.{0}) : Arena := by first | exact a
  arena
-- Expected types can insert an implicit lambda with no source binder. These
-- literals must fail closed until recovery supports that extra alignment step.
def localImplicitCopy : Arena :=
  let copy : {_u : Unit} → Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  copy (_u := ())
def localImplicitAlias : Arena :=
  let copy : {_u : Unit} → Arena := arena
  copy (_u := ())
def localImplicitDead : Arena :=
  let copy : {_u : Unit} → Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  (fun _ : Arena => arena) (copy (_u := ()))
def copyParameter (a : Arena) : Arena where
  State := a.State
  stateFintype := a.stateFintype
  stateDecidableEq := a.stateDecidableEq
def throughParameter := copyParameter arena
def reservedBinder (realization : Arena) : Arena := realization
def reservedForward := reservedBinder copyArena

def explicit := @id Arena copyArena
def named := id (α := Arena) copyArena
def interleaved (_a : Arena) {b : Arena} (_ : Unit) : Arena := b
def liveImplicit := interleaved arena (b := copyArena) ()
def inlineImplicit := interleaved arena
  (b := { State := arena.State, stateFintype := arena.stateFintype,
          stateDecidableEq := arena.stateDecidableEq }) ()
def groupedNamed := (id (α := Arena)) copyArena
def shadowed (_x : Arena) := fun (_x : Arena) => _x
def ambiguousNamed := (shadowed arena)
  (_x := { State := arena.State, stateFintype := arena.stateFintype,
           stateDecidableEq := arena.stateDecidableEq })
def unusedLet := let _unused : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  arena
def nested := (fun (f : Arena → Arena) (x : Arena) => f x) id copyArena
def groupedLive := (id (fun x : Arena => x)) copyArena
def groupedDead := (id (fun _ : Arena => arena)) copyArena
def groupedInline := (id (fun x : Arena => x))
  ({ State := arena.State, stateFintype := arena.stateFintype,
     stateDecidableEq := arena.stateDecidableEq } : Arena)
def typedLambda := (fun (_a b : Arena) => b) arena copyArena
def tacticAlias : Arena := by exact copyArena
def tacticFactory : Arena := by
  letI : Fintype Bool := inferInstance
  letI : DecidableEq Bool := inferInstance
  exact Arena.ofFintype Bool
def unsupportedLive : Arena := by first | exact copyArena
def unsupportedDead := (fun _ : Arena => arena) (by first | exact copyArena)
def selected := if True then copyArena else arena
def higherOrder {α : Sort u} (k : Arena → α) := k
  { State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }
def higherOrderLive := higherOrder id
def higherOrderDead := higherOrder (fun _ => arena)

def twice (f : Arena → Arena) (a : Arena) : Arena := f (f a)
def expensive := twice (twice (twice (twice (twice (twice
  (twice (twice (twice (twice (twice (twice id))))))))))) arena

private def privateCopy : Arena where
  State := arena.State
  stateFintype := arena.stateFintype
  stateDecidableEq := arena.stateDecidableEq
def privateLive := privateCopy

-- Literals of other structures do not create arena ownership.
structure Box where
  value : Arena
def box : Box := ⟨arena⟩
def projected := box.value

-- This alias is changed to a field-copy literal by the import-invalidation test.
def sourceMutation : Arena := arena

-- Deliberately lacks a source range: recovery must report the missing compiler
-- evidence instead of pretending that a generated definition was a source alias.
run_cmd Lean.Elab.Command.liftCoreM do
  Lean.addDecl (.defnDecl {
    name := `ProvenanceProbe.rangeMissing
    levelParams := []
    type := (← Lean.getConstInfo `ProvenanceProbe.arena).type
    value := Lean.mkConst `ProvenanceProbe.arena
    hints := .abbrev
    safety := .safe })

end ProvenanceProbe
