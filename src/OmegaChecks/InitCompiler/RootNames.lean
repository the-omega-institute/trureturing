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

/-- These literal kernel names preserve numeral evaluation and the runtime Nat representation. -/
public def natPrimitives := #[`Nat, `Nat.zero, `Nat.succ, `Nat.rec, `Nat.recOn, `Nat.casesOn,
  `Nat.add, `Nat.mul, `Nat.pow, `Nat.sub, `Nat.pred,
  `OfNat, `OfNat.mk, `OfNat.rec, `OfNat.ofNat, `instOfNatNat,
  `Add, `Add.mk, `Add.rec, `Add.add, `HAdd, `HAdd.mk, `HAdd.rec, `HAdd.hAdd,
  `instHAdd, `instAddNat]

public def usesRoot (name : Name) :=
  taskPrimitives.contains name || binderAnnotations.contains name || natPrimitives.contains name

public def isPrimitive (owner name : Name) : Bool :=
  (owner == `OmegaInit.Core && taskPrimitives.contains name) ||
  (owner == `OmegaInit.Prelude && (binderAnnotations.contains name || natPrimitives.contains name))

/-- Method lookup uses the structure's physical namespace, even when callers spell its alias. -/
public def aliasFor? (official : Name) : Option (Name × Name) :=
  if usesRoot official then some (`Omega ++ official, official)
  else if (official.getPrefix == `Task || official.getPrefix == `Nat) && !official.isInternal then some (official, `Omega ++ official)
  else none

end OmegaChecks.InitCompiler.RootNames
