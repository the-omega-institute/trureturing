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
