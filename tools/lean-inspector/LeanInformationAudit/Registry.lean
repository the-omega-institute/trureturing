import Lean

open Lean

structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  arenaName : Name
  /-- realizationName = Name.anonymous iff the unit is native; deviation from spec §25.1 three-field entry, required by §§24.2/24.4/26.4 realization validation. -/
  realizationName : Name

initialize informationRegistryExt :
    SimplePersistentEnvExtension InformationRegistryEntry
      (Array InformationRegistryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  informationRegistryExt.getState env

def InformationRegistry.containsTheoremName (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.theoremName == n

def InformationRegistry.containsUnitName (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n
