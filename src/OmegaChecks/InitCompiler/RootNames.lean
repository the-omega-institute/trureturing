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
public def natPrimitives := #[
  `id,
  `PProd.fst, `PProd.snd,
  `Add, `Add.add, `Add.mk, `Add.rec, `Bool, `Bool.Reflects, `Bool.Reflects.match_1, `Bool.casesOn,
  `Bool.false, `Bool.noConfusion, `Bool.noConfusionType, `Bool.rec, `Bool.true, `Decidable,
  `Decidable.casesOn, `Decidable.intro, `Decidable.rec, `Eq, `Eq.casesOn, `Eq.recOn, `Eq.ndrec,
  `Eq.ndrec_symm, `Eq.rec, `Eq.refl, `Eq.subst, `Eq.symm, `Eq.trans, `False, `False.casesOn,
  `False.rec, `HAdd, `HAdd.hAdd, `HAdd.mk, `HAdd.rec, `HEq, `HEq.casesOn, `HEq.rec, `HEq.refl,
  `Nat.ble, `Nat.ble._f, `Nat.ble.match_1,
  `Nat, `Nat.add, `Nat.add._f, `Nat.add.match_1, `Nat.below, `Nat.beq, `Nat.beq._f,
  `Nat.beq.match_1, `Nat.brecOn, `Nat.brecOn.go, `Nat.casesOn, `Nat.decEq, `Nat.decEq._proof_1,
  `Nat.decEq.match_1, `Nat.eq_of_beq_eq_true, `Nat.eq_of_beq_eq_true._f, `Nat.mul, `Nat.mul._f,
  `Nat.mul.match_1, `Nat.ne_of_beq_eq_false, `Nat.ne_of_beq_eq_false._f, `Nat.noConfusion,
  `Nat.noConfusionType, `Nat.pow, `Nat.pow._f, `Nat.pow.match_1, `Nat.pred, `Nat.rec, `Nat.recOn,
  `Nat.sub, `Nat.sub._f, `Nat.succ, `Nat.zero, `Not, `OfNat, `OfNat.mk, `OfNat.ofNat, `OfNat.rec,
  `PProd, `PProd.casesOn, `PProd.mk, `PProd.rec, `PUnit, `PUnit.casesOn, `PUnit.rec, `PUnit.unit,
  `Unit, `Unit.unit, `absurd, `cast, `cond, `cond.match_1, `eq_of_heq, `heq_of_eq, `instAddNat,
  `instHAdd, `instOfNatNat, `rfl]

/-- Lean resolves reserved equation and congruence names before source aliases
when their parent is a physical declaration. Keep the pinned generated names. -/
private def reservedEquations := #[
  `Eq.congr_simp, `HEq.congr_simp, `Decidable.intro.congr_simp, `Eq.ndrec_symm.congr_simp,
  `cast.congr_simp, `absurd.congr_simp, `Nat.beq.eq_def, `Nat.beq.eq_1, `Nat.beq.eq_2,
  `Nat.beq.eq_3, `Nat.beq.eq_4, `OfNat.ofNat.eq_1, `cond.eq_1, `cond.eq_2, `id.eq_1]

public def usesRoot (name : Name) :=
  taskPrimitives.contains name || binderAnnotations.contains name || natPrimitives.contains name || reservedEquations.contains name

public def isPrimitive (owner name : Name) : Bool :=
  (owner.getRoot == `OmegaInit && reservedEquations.contains name) ||
  (owner == `OmegaInit.Core && taskPrimitives.contains name) ||
  (owner == `OmegaInit.Prelude && (binderAnnotations.contains name || natPrimitives.contains name))

/-- Method lookup uses the structure's physical namespace, even when callers spell its alias. -/
public def aliasFor? (official : Name) : Option (Name × Name) :=
  if usesRoot official then some (`Omega ++ official, official)
  else if (usesRoot official.getPrefix) && !official.isInternal then some (official, `Omega ++ official)
  else none

end OmegaChecks.InitCompiler.RootNames
