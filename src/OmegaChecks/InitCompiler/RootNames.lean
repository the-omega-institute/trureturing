module
public import Lean

open Lean

namespace OmegaChecks.InitCompiler.RootNames

/-- The compiler recognizes the primitive task type, constructor, projection and eliminators
by their root names. These objects remain inductives, constructors and recursors in their owner. -/
public def taskPrimitives : Array Name :=
  #[`Task, `Task.pure, `Task.get, `Task.rec, `Task.recOn, `Task.casesOn]

/-- Lean recognizes these annotations by their literal head constants before reduction. -/
public def binderAnnotations := #[`optParam, `outParam, `semiOutParam]

public def usesRoot (name : Name) := taskPrimitives.contains name || binderAnnotations.contains name

public def isPrimitive (owner name : Name) : Bool :=
  (owner == `OmegaInit.Core && taskPrimitives.contains name) ||
  (owner == `OmegaInit.Prelude && binderAnnotations.contains name)

/-- Method lookup uses the structure's physical namespace, even when callers spell its alias. -/
public def aliasFor? (official : Name) : Option (Name × Name) :=
  if usesRoot official then some (`Omega ++ official, official)
  else if official.getPrefix == `Task && !official.isInternal then some (official, `Omega ++ official)
  else none

end OmegaChecks.InitCompiler.RootNames
