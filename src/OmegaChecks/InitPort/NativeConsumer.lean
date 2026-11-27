import Lean

open Lean

private def consumer := "module
prelude
public import OmegaInit.Data.Function
public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Option.Basic
public import OmegaInit.Control.Id
public def firstValue (x y : Omega.Bool) : Omega.Bool :=
  Omega.Function.curry (fun p => Omega.Prod.fst p) x y
public def secondValue (x y : Omega.Bool) : Omega.Bool :=
  Omega.Function.uncurry (fun _ y => y) (Omega.Prod.mk x y)

public def additionFirst (x y : Omega.Bool) : Omega.Bool :=
  @Omega.HAdd.hAdd _ _ _ (@Omega.instHAdd _ (Omega.Add.mk (fun a _ => a))) x y

public def stateSecond (x y : Omega.Bool) : Omega.Bool :=
  Omega.EStateM.Result.casesOn (motive := fun _ => Omega.Bool)
    (@Omega.EStateM.run Omega.Bool Omega.Bool Omega.PUnit (Omega.EStateM.set y) x)
    (fun _ s => s) (fun _ _ => x)

public def optionFirst (x y : Omega.Bool) : Omega.Bool :=
  (@Omega.Option.mapM Omega.Id _ _ (@Omega.Monad.toApplicative Omega.Id Omega.Id.instMonad) (fun a => a) (Omega.Option.some x)).elim y (fun a => a)

public def composeSecond (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Bind.kleisliRight Omega.Bool Omega.Id Omega.Bool Omega.Bool Omega.Id.hasBind
    (fun _ => y) (fun a => a) x

public def mappedFirst (x y : Omega.Bool) : Omega.Bool :=
  Omega.Prod.fst (Omega.Prod.map (fun a => a) (fun b => b) (Omega.Prod.mk x y))
public def sumIndex (x y : Omega.Bool) : Omega.Bool :=
  let s := Omega.Bool.casesOn (motive := fun _ => Omega.Sum Omega.Bool Omega.Bool) x
    (Omega.Sum.inl y) (Omega.Sum.inr y)
  Omega.Nat.casesOn (motive := fun _ => Omega.Bool) s.ctorIdx .false (fun _ => .true)

public def sumRight (x y : Omega.Bool) : Omega.Bool :=
  Omega.Sum.inr.elim (α := Omega.Bool) (motive := fun _ => Omega.Bool)
    (Omega.Sum.inr y) Omega.rfl (fun value => Omega.strictOr x value)

public def boolEqual (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (Omega.Bool.decEq x y)

public def optionFiltered (x y : Omega.Bool) : Omega.Bool :=
  (Omega.Option.filter (fun _ => x) (Omega.Option.some y)).getD .false

public def controlResult (x y : Omega.Bool) : Omega.Bool :=
  @Omega.controlAt Omega.Id Omega.Id
    (@Omega.instMonadControlTOfPure Omega.Id
      (@Omega.Applicative.toPure Omega.Id (@Omega.Monad.toApplicative Omega.Id Omega.Id.instMonad)))
    Omega.Id.hasBind Omega.Bool (fun run => run (Omega.strictOr x y))

public def optionEqual (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (@Omega.Option.instDecidableEq Omega.Bool Omega.instDecidableEqBool
    (Omega.Option.some x) (Omega.Option.some y))

public def someValue (x y : Omega.Bool) : Omega.Bool :=
  (Omega.Option.some (Omega.strictAnd x y)).get Omega.rfl

public def attachedValue (x y : Omega.Bool) : Omega.Bool :=
  @Omega.MonadAttach.pbind Omega.Id Omega.Bool Omega.Bool Omega.Id.instMonad Omega.Id.instMonadAttach
    x (fun value _ => Omega.strictAnd value y)

public def liftedNumeral (x y : Omega.Bool) : Omega.Bool :=
  @Omega.OfNat.ofNat (Omega.Id Omega.Bool) Omega.Nat.zero
    (@Omega.Id.instOfNat Omega.Bool Omega.Nat.zero
      (Omega.OfNat.mk (Omega.strictOr x y)))

public def lastElement (x y : Omega.Bool) : Omega.Bool :=
  let pair := Omega.Prod.mk x y
  let iteration : Omega.ForIn Omega.Id (Omega.Prod Omega.Bool Omega.Bool) Omega.Bool :=
    Omega.ForIn.mk fun {_} p start step =>
      Omega.ForInStep.casesOn (motive := fun _ => _) (step p.fst start)
        (fun done => done) (fun afterFirst => (step p.snd afterFirst).value)
  let xs := @Omega.ForIn.toList _ _ iteration pair
  Omega.List.casesOn (motive := fun _ => Omega.Bool) xs .false (fun _ rest =>
    Omega.List.casesOn (motive := fun _ => Omega.Bool) rest .false (fun second _ => second))

private def asNat (x : Omega.Bool) : Omega.Nat :=
  Omega.Bool.casesOn (motive := fun _ => Omega.Nat) x .zero (.succ .zero)

public def arithmetic (x y : Omega.Bool) : Omega.Bool :=
  let n := Omega.Nat.sub (Omega.Nat.mul (Omega.Nat.add (asNat x) (asNat y)) (.succ .zero)) (asNat y)
  Omega.Nat.casesOn (motive := fun _ => Omega.Bool) n .false (fun _ => .true)

public def listDisjunction (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.List.append (Omega.List.cons x Omega.List.nil) (Omega.List.cons y Omega.List.nil)
  Omega.List.foldl Omega.strictOr .false (Omega.List.map (fun a => a) xs)

public def naturalEqual (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (Omega.Nat.decEq (asNat x) (asNat y))

public def naturalLe (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (Omega.Nat.decLe (asNat x) (asNat y))

public def arraySecond (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.Array.mkArray2 x y
  let correct := @Omega.Decidable.decide _ (Omega.Nat.decEq xs.size (.succ (.succ .zero)))
  Omega.strictAnd correct (Omega.List.casesOn (motive := fun _ => Omega.Bool) xs.toList .false
    (fun _ tail => Omega.List.casesOn (motive := fun _ => Omega.Bool) tail .false (fun last _ => last)))

private def one := Omega.Nat.succ Omega.Nat.zero
private def two := Omega.Nat.succ one

private def asWordBits {w : Omega.Nat} (hw : Omega.Nat.le one w) (x : Omega.Bool) : Omega.BitVec w :=
  let upper : Omega.Nat.le two (Omega.Nat.pow two w) :=
    Omega.Eq.subst (motive := fun bound => Omega.Nat.le bound (Omega.Nat.pow two w))
      (Omega.Nat.pow_one two) (Omega.Nat.pow_le_pow_right Omega.Nat.zero_lt_two hw)
  Omega.Bool.casesOn (motive := fun _ => Omega.BitVec w) x
    (Omega.BitVec.ofNatLT .zero (Omega.Nat.two_pow_pos w))
    (Omega.BitVec.ofNatLT one upper)

private def asBit (x : Omega.Bool) : Omega.BitVec one :=
  asWordBits (Omega.Nat.le_refl one) x

public def bitEqual (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (Omega.BitVec.decEq (asBit x) (asBit y))

public def boundedLess (x y : Omega.Bool) : Omega.Bool :=
  @Omega.Decidable.decide _ (Omega.Fin.decLt (asBit x).toFin (asBit y).toFin)

public def bitConjunction (x y : Omega.Bool) : Omega.Bool :=
  let both := Omega.strictAnd x y
  @Omega.Decidable.decide _ (Omega.Nat.decEq (asBit both).toNat (.succ .zero))

public def word8Less (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.UInt8.ofBitVec (asWordBits (Omega.Nat.succ_le_succ (Omega.Nat.zero_le _)) b)
  @Omega.Decidable.decide _ (Omega.UInt8.decLt (mk x) (mk y))

public def word16Equal (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.UInt16.ofBitVec (asWordBits (Omega.Nat.succ_le_succ (Omega.Nat.zero_le _)) b)
  @Omega.Decidable.decide _ (Omega.UInt16.decEq (mk x) (mk y))

public def word32Le (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.UInt32.ofBitVec (asWordBits
    (Omega.Nat.le_add_right_of_le (Omega.Nat.succ_le_succ (Omega.Nat.zero_le _))) b)
  @Omega.Decidable.decide _ (Omega.UInt32.decLe (mk x) (mk y))

public def word64Equal (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.UInt64.ofBitVec (asWordBits
    (Omega.Nat.le_add_right_of_le (Omega.Nat.le_add_right_of_le (Omega.Nat.succ_le_succ (Omega.Nat.zero_le _)))) b)
  @Omega.Decidable.decide _ (Omega.UInt64.decEq (mk x) (mk y))

public def disjunction (x y : Omega.Bool) : Omega.Bool := Omega.strictOr x y
public def conjunction (x y : Omega.Bool) : Omega.Bool := Omega.strictAnd x y
"

/-- Compile a fresh ordinary consumer and execute its packaged IR with both Boolean values. -/
unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected generated library path"
  let lib ← IO.FS.realPath lib
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "PairSmoke.lean") consumer
    let proc ← IO.Process.output {
      cmd := "lean", args := #["-c", "PairSmoke.c", "-o", "PairSmoke.olean", "PairSmoke.lean"]
      cwd := dir, env := #[("LEAN_PATH", some lib.toString)] }
    unless proc.exitCode == 0 do throw <| IO.userError (proc.stdout ++ proc.stderr)
    searchPathRef.set [dir, lib]
    let env ← importModules #[{module := `PairSmoke, importAll := true}] {} (level := .private)
    let some (.inductInfo bool) := env.find? `Omega.Bool | throw <| IO.userError "missing Boolean type"
    unless bool.numParams == 0 && bool.ctors == [`Omega.Bool.false, `Omega.Bool.true] do
      throw <| IO.userError "unexpected Boolean representation"
    let b := mkConst `Omega.Bool
    let arity := .forallE `x b (.forallE `y b b .default) .default
    let first := fun (x _ : Bool) => x
    let second := fun (_ y : Bool) => y
    let checks := [(`firstValue, first), (`secondValue, second), (`additionFirst, first),
      (`stateSecond, second), (`optionFirst, first), (`composeSecond, second), (`mappedFirst, first),
      (`sumIndex, first), (`sumRight, or), (`boolEqual, BEq.beq), (`optionFiltered, and),
      (`controlResult, or), (`optionEqual, BEq.beq), (`someValue, and), (`attachedValue, and), (`liftedNumeral, or), (`lastElement, second),
      (`arithmetic, first), (`listDisjunction, or), (`naturalEqual, BEq.beq),
      (`naturalLe, fun x y => !x || y), (`arraySecond, second), (`bitEqual, BEq.beq),
      (`boundedLess, fun x y => !x && y), (`bitConjunction, and), (`word8Less, fun x y => !x && y),
      (`word16Equal, BEq.beq), (`word32Le, fun x y => !x || y), (`word64Equal, BEq.beq),
      (`disjunction, or), (`conjunction, and)]
    for (name, expected) in checks do
      let some ci := env.find? name | throw <| IO.userError s!"missing {name}"
      unless Kernel.isDefEqGuarded env {} ci.type arity do throw <| IO.userError s!"invalid type of {name}"
      let fn ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} name
      for x in [false, true] do
        for y in [false, true] do
          unless fn x y == expected x y do
            throw <| IO.userError s!"invalid executable result for {name} at {x}, {y}"

