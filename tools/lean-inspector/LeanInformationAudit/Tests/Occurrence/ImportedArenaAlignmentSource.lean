import LeanInformationAudit.Tests.Occurrence.ImportedArenaSource

open D5.S3.ConceptDynamics.InformationEscape ProvenanceProbe

namespace QualityPure

def defaultCopy (a : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }) : Arena := a
def defaultUse : Arena := defaultCopy

end QualityPure

namespace QualityAlias
abbrev Carrier := Arena
end QualityAlias

namespace QualityContext
open QualityAlias

def drift : Arena := by
  letI localArena : Carrier :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  exact localArena

end QualityContext

-- This later class did not participate in elaborating drift.
class Carrier where
  tag : Nat

namespace QualityPure

def deadDefaultCopy (_a : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }) : Arena := arena
def deadDefaultUse : Arena := deadDefaultCopy
-- Expected-type lambdas must not hide inserted default arguments from recovery.
def localImplicitDefaultUse : Arena :=
  let copy : {_u : Unit} → Arena := defaultCopy
  copy (_u := ())
def localImplicitDeadDefaultUse : Arena :=
  let copy : {_u : Unit} → Arena := deadDefaultCopy
  copy (_u := ())
def defaultTail (_u : Unit) (a : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }) : Arena := a
def defaultTailUse : Arena := defaultTail ()
def deadDefaultTail (_u : Unit) (_a : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }) : Arena := arena
def deadDefaultTailUse : Arena := deadDefaultTail ()
def explicitDefaultUse : Arena := defaultCopy
  { State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }
def namedDefaultUse : Arena := defaultCopy (a :=
  { State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq })
def inferred {a : Arena} (_ : a = arena) : Arena := a
def inferredUse : Arena := inferred rfl
def deadInferred {a : Arena} (_ : a = arena) : Arena := arena
def deadInferredUse : Arena := deadInferred rfl

end QualityPure

namespace QualityContext

def qualified : Arena := by
  letI localArena : QualityAlias.Carrier :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  exact localArena

def direct : Arena := by
  letI localArena : Arena :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  exact localArena

def termLet : Arena :=
  letI localArena : QualityAlias.Carrier :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  localArena

def directAlias : Arena := by
  letI localArena : QualityAlias.Carrier := arena
  exact localArena

def classAlias : Arena := by
  letI label : Carrier := ⟨0⟩
  exact arena

def qualifiedClassAlias : Arena := by
  letI label : _root_.Carrier := ⟨0⟩
  exact arena

def localContext (a : Arena) : Arena := by
  letI : Fintype a.State := a.stateFintype
  letI : DecidableEq a.State := a.stateDecidableEq
  exact { State := a.State, stateFintype := a.stateFintype,
          stateDecidableEq := a.stateDecidableEq }
def localContextUse : Arena := localContext arena

def unresolved : Arena := by
  letI localArena : QualityAlias.Carrier :=
    { State := arena.State, stateFintype := arena.stateFintype,
      stateDecidableEq := arena.stateDecidableEq }
  exact id localArena

end QualityContext


namespace QualityGrouped

def hold (_u : Unit) (a : Arena.{0} := ProvenanceProbe.arena)
    (_ignored : Arena.{0}) : Arena.{0} := a
def shifted : Arena.{0} :=
  (hold ()) {
    State := ProvenanceProbe.arena.State
    stateFintype := ProvenanceProbe.arena.stateFintype
    stateDecidableEq := ProvenanceProbe.arena.stateDecidableEq }

def holdCopy (_u : Unit) (a : Arena.{0} := {
    State := ProvenanceProbe.arena.State
    stateFintype := ProvenanceProbe.arena.stateFintype
    stateDecidableEq := ProvenanceProbe.arena.stateDecidableEq })
    (_ignored : Arena.{0}) : Arena.{0} := a
def shiftedCopy : Arena.{0} := (holdCopy ()) ProvenanceProbe.arena

-- The same inserted argument is harmless when the function discards it.
def discardDefault (_u : Unit) (_a : Arena := {
    State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }) (result : Arena) : Arena := result
def deadInserted : Arena := (discardDefault ()) arena
def liveOuter : Arena := (discardDefault ()) {
    State := arena.State, stateFintype := arena.stateFintype,
    stateDecidableEq := arena.stateDecidableEq }
def explicitInner : Arena := (hold () arena) arena
def namedInner : Arena := (hold () (a := arena)) arena
-- An inner @ does not change implicit argument insertion in an outer call.
def returnsImplicit (_u : Unit) : {a : Arena} → a = arena → Arena := fun {_} _ => arena
def groupedExplicit : Arena := (@returnsImplicit ()) rfl

end QualityGrouped

namespace ArchitectureNamed

-- This producer imports no registration syntax or construction hook. Lean
-- inserts the ordinary explicit a because the same-frame named proof needs it.
def discard (a : Arena.{0}) (_h : a = ProvenanceProbe.arena) : Arena.{0} :=
  ProvenanceProbe.arena
def deadUse : Arena.{0} := discard (_h := rfl)
def explicitUse : Arena.{0} := discard (a := ProvenanceProbe.arena) (_h := rfl)
def keep (a : Arena.{0}) (_h : a = ProvenanceProbe.arena) : Arena.{0} := a
def liveUse : Arena.{0} := keep (_h := rfl)

end ArchitectureNamed
