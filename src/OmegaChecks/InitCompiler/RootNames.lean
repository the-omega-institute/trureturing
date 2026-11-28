module
public import Lean

open Lean

namespace OmegaChecks.InitCompiler.RootNames

/-- The compiler recognizes the primitive task type, constructor, projection and eliminators
by their root names. These objects remain inductives, constructors and recursors in their owner. -/
public def taskPrimitives : Array Name :=
  #[`Task, `Task.pure, `Task.get, `Task.rec, `Task.recOn, `Task.casesOn]

/-- The compiler lowers raw thunk case analysis to the memoizing root getter. -/
public def thunkPrimitives : Array Name :=
  #[`Thunk, `Thunk.mk, `Thunk.fn, `Thunk.get, `Thunk.pure, `Thunk.rec, `Thunk.recOn, `Thunk.casesOn]

/-- The elaborator detects these constant names when generating the no-confusion API for enums. -/
public def enumPrimitives :=
  #[`noConfusionTypeEnum, `noConfusionEnum, `noConfusionEnum._proof_1, `noConfusionEnum._proof_2]

/-- Lean recognizes these annotations by their literal head constants before reduction. -/
public def binderAnnotations := #[`optParam, `outParam, `semiOutParam]

/-- These literal kernel names preserve numeral evaluation and the runtime Nat representation. -/
public def natPrimitives := #[
  `id,
  `PProd.fst, `PProd.snd,
  -- The elaborator builds constructor eliminators using these literal names once Nat is available.
  `PULift, `PULift.up, `PULift.down, `PULift.rec, `PULift.recOn, `PULift.casesOn,
  `Add, `Add.add, `Add.mk, `Add.rec, `Bool, `Bool.Reflects, `Bool.Reflects.match_1, `Bool.casesOn,
  `Bool.false, `Bool.noConfusion, `Bool.noConfusionType, `Bool.rec, `Bool.true, `Decidable,
  `dite, `Decidable.decide, `Decidable.reflects_decide, `Decidable.casesOn, `Decidable.intro, `Decidable.rec, `Eq, `Eq.casesOn, `Eq.recOn, `Eq.ndrec,
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

private def primitiveName (name : Name) :=
  [`Nat.div, `Nat.mod, `Nat.gcd, `Nat.xor].contains name || taskPrimitives.contains name || thunkPrimitives.contains name ||
    binderAnnotations.contains name || natPrimitives.contains name || enumPrimitives.contains name

/-- The resolver looks up generated theorem names under their physical parent before consulting aliases. -/
private def reservedEquation : Name → Bool
  | .str parent suffix =>
    primitiveName parent && (Meta.isEqnLikeSuffix suffix || suffix == "congr_simp")
  | _ => false

/-- Smart unfolding looks up the helper under the kernel name of the recursive definition. -/
private def primitiveUnfolding (name : Name) : Bool :=
  name == Meta.mkSmartUnfoldingNameFor name.getPrefix && primitiveName name.getPrefix

public def usesRoot (name : Name) := primitiveName name || reservedEquation name || primitiveUnfolding name

/-- Quotient primitives have fixed kernel names. Their public Omega definitions use
the original binder types, referring to Omega constructors and to the kernel equality. -/
public def quotientPrimitives := #[`Quot, `Quot.mk, `Quot.ind, `Quot.lift]

public def quotientInterface (ci : ConstantInfo) : DefinitionVal :=
  let name := `Omega ++ ci.name
  let type := ci.type.replace fun
    | .const n ls => some (.const (if usesRoot n then n else `Omega ++ n) ls)
    | _ => none
  { name, type, levelParams := ci.levelParams, value := mkConst ci.name (ci.levelParams.map Level.param),
    all := [name], hints := .regular 1, safety := .safe }

public def isPrimitive (owner name : Name) : Bool :=
  (owner == `OmegaInit.Data.Nat.Gcd && name == `Nat.gcd) ||
  (owner == `OmegaInit.Data.Nat.Bitwise.Basic && name == `Nat.xor) ||
  (owner.getRoot == `OmegaInit && reservedEquation name) ||
  (owner == `OmegaInit.Core && (taskPrimitives.contains name || thunkPrimitives.contains name || enumPrimitives.contains name)) ||
  (owner == `OmegaInit.Prelude && (binderAnnotations.contains name || natPrimitives.contains name || [`Nat.div, `Nat.mod].contains name))

/-- Method lookup uses the structure's physical namespace, even when callers spell its alias. -/
public def aliasFor? (official : Name) : Option (Name × Name) :=
  if primitiveUnfolding official then none
  else if usesRoot official then some (`Omega ++ official, official)
  else if (usesRoot official.getPrefix) && !official.isInternal then some (official, `Omega ++ official)
  else none

/-- Express a string literal with strict character and string constructors. -/
public def stringTerm (s : String) : Expr :=
  let char := mkConst `Omega.Char
  let chars := s.toList.foldr (init := mkApp (mkConst `Omega.List.nil [.zero]) char) fun ch tail =>
    mkApp3 (mkConst `Omega.List.cons [.zero]) char (mkApp (mkConst `Omega.Char.ofNat) (mkRawNatLit ch.toNat)) tail
  mkApp (mkConst `Omega.String.ofList) chars

end OmegaChecks.InitCompiler.RootNames
