module
public import Lean

open Lean

namespace OmegaChecks.InitPort.TaskNames

/-- The compiler recognizes the primitive task type, constructor, projection and eliminators
by their root names. These objects remain inductives, constructors and recursors in their owner. -/
public def primitives : Array Name :=
  #[`Task, `Task.pure, `Task.get, `Task.rec, `Task.recOn, `Task.casesOn]

public def isPrimitive (owner name : Name) : Bool :=
  owner == `OmegaInit.Core && primitives.contains name

/-- Method lookup uses the structure's physical namespace, even when callers spell its alias. -/
public def aliasFor? (official : Name) : Option (Name × Name) :=
  if primitives.contains official then some (`Omega ++ official, official)
  else if official.getPrefix == `Task && !official.isInternal then some (official, `Omega ++ official)
  else none

end OmegaChecks.InitPort.TaskNames
