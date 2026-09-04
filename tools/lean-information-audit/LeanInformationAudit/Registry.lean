import Lean

open Lean

structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  arenaName : Name
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

def InformationRegistry.isDuplicate (env : Environment) (theoremName : Name) : Bool :=
  (entries env).any fun entry => entry.theoremName == theoremName
