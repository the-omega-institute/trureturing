import Lean

open Lean

private def imports := "module
prelude
public import OmegaInit.Data.Function
public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Option.Basic
public import OmegaInit.Control.Id
"

private def consumer := imports ++ "
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

public def transportedDecision (x y : Omega.Bool) : Omega.Bool :=
  let decision := Omega.Bool.decEq x y
  let equivalent := @Omega.decidable_of_decidable_of_iff _ _ decision Omega.Iff.rfl
  @Omega.Decidable.decide _ (@Omega.decidable_of_decidable_of_eq _ _ equivalent Omega.rfl)

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

example (n : Omega.Nat) : Omega.Eq (Omega.Nat.add n 0) n := Omega.rfl
example : Omega.Eq (Omega.Nat.pow 2 64) 18446744073709551616 := Omega.rfl

public def largeArithmetic (n : Omega.Nat) : Omega.Nat :=
  Omega.Nat.mul (Omega.Nat.add n 18446744073709551616) 3

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
    (Omega.Nat.succ_le_succ (Omega.Nat.zero_le 31)) b)
  @Omega.Decidable.decide _ (Omega.UInt32.decLe (mk x) (mk y))

public def word64Equal (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.UInt64.ofBitVec (asWordBits
    (Omega.Nat.succ_le_succ (Omega.Nat.zero_le 63)) b)
  @Omega.Decidable.decide _ (Omega.UInt64.decEq (mk x) (mk y))

public def byteBufferSecond (x y : Omega.Bool) : Omega.Bool :=
  let byte := fun b => Omega.UInt8.ofBitVec (asWordBits (Omega.Nat.succ_le_succ (Omega.Nat.zero_le _)) b)
  let bytes := Omega.List.toByteArray (Omega.List.cons (byte x) (Omega.List.cons (byte y) Omega.List.nil))
  let correct := @Omega.Decidable.decide _ (Omega.Nat.decEq bytes.size two)
  let second := Omega.List.casesOn (motive := fun _ => Omega.Bool) bytes.data.toList .false
    (fun _ tail => Omega.List.casesOn (motive := fun _ => Omega.Bool) tail .false
      (fun last _ => @Omega.Decidable.decide _ (Omega.UInt8.decEq last (byte .true))))
  Omega.strictAnd correct second

public def updatedLookup (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.List.set (Omega.Array.mkArray2 x .false).toList one y
  xs.toArray.getD one .false

public def outsideLookup (x y : Omega.Bool) : Omega.Bool :=
  (Omega.Array.mkArray1 x).getD two y

public def slicedLookup (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.Array.appendCore (Omega.Array.mkArray1 x) (Omega.Array.mkArray1 y)
  let tail := xs.extract one (.succ two)
  Omega.strictAnd (@Omega.Decidable.decide _ (Omega.Nat.decEq tail.size one)) (tail.getD .zero .false)

public def listEqual (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.List.cons x (Omega.List.cons y Omega.List.nil)
  let ys := Omega.List.cons y (Omega.List.cons x Omega.List.nil)
  @Omega.Decidable.decide _ (@Omega.instDecidableEqList Omega.Bool Omega.instDecidableEqBool xs ys)

public def optionalListEmpty (x y : Omega.Bool) : Omega.Bool :=
  let xs := Omega.Bool.casesOn (motive := fun _ => Omega.List Omega.Bool) x .nil (.cons y .nil)
  @Omega.Decidable.decide _ (Omega.List.instDecidableNilEq xs)

public def pairEqual (x y : Omega.Bool) : Omega.Bool :=
  let same := @Omega.instDecidableEqProd Omega.Bool Omega.Bool Omega.instDecidableEqBool Omega.instDecidableEqBool
  @Omega.Decidable.decide _ (same (Omega.Prod.mk x y) (Omega.Prod.mk y x))

public def sumEqual (x y : Omega.Bool) : Omega.Bool :=
  let tag := fun b => Omega.Bool.casesOn (motive := fun _ => Omega.Sum Omega.Bool Omega.Bool) b (.inl .true) (.inr .true)
  @Omega.Decidable.decide _ (@Omega.instDecidableEqSum Omega.Bool Omega.Bool Omega.instDecidableEqBool
    Omega.instDecidableEqBool (tag x) (tag y))

public def subtypeEqual (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun b => Omega.Subtype.mk (p := fun _ : Omega.Bool => Omega.True) b Omega.True.intro
  @Omega.Decidable.decide _ (@Omega.Subtype.instDecidableEq _ _ Omega.instDecidableEqBool (mk x) (mk y))

private def fiber (tag : Omega.Bool) : Type :=
  Omega.Bool.casesOn (motive := fun _ => Type) tag Omega.Nat Omega.Bool

private def fiberValue (tag x : Omega.Bool) : fiber tag :=
  Omega.Bool.casesOn (motive := fiber) tag (asNat x) x

private def fiberEq (tag : Omega.Bool) : Omega.DecidableEq (fiber tag) :=
  Omega.Bool.casesOn (motive := fun t => Omega.DecidableEq (fiber t)) tag
    Omega.instDecidableEqNat Omega.instDecidableEqBool

public def sigmaEqual (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun tag value => @Omega.Sigma.mk _ fiber tag (fiberValue tag value)
  @Omega.Decidable.decide _ (@Omega.instDecidableEqSigma _ fiber Omega.instDecidableEqBool fiberEq (mk x y) (mk y x))

public def psigmaEqual (x y : Omega.Bool) : Omega.Bool :=
  let mk := fun tag value => @Omega.PSigma.mk _ fiber tag (fiberValue tag value)
  @Omega.Decidable.decide _ (@Omega.instDecidableEqPSigma _ fiber Omega.instDecidableEqBool fiberEq (mk x x) (mk x y))

public def chooseValue (x y : Omega.Bool) : Omega.Bool :=
  @Omega.iteInduction Omega.Bool (Omega.Eq x Omega.Bool.true) (Omega.Bool.decEq x .true)
    (fun _ => Omega.Bool) y .false (fun _ => Omega.Lean.opaqueId y) (fun _ => .false)

public def disjunction (x y : Omega.Bool) : Omega.Bool := Omega.strictOr x y
public def conjunction (x y : Omega.Bool) : Omega.Bool := Omega.strictAnd x y
"

/-- Compile a fresh ordinary consumer and execute its packaged IR with both Boolean values. -/
unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected generated library path"
  let lib ← IO.FS.realPath lib
  IO.FS.withTempDir fun dir => do
    let compilerEnv := #[("LEAN_PATH", some lib.toString)]
    -- Initialize just the consumer's imports. Its own functions still run from packaged IR.
    IO.FS.writeFile (dir / "PairImports.lean") imports
    discard <| IO.Process.run {
      cmd := "lean", args := #["-c", "PairImports.c", "PairImports.lean"]
      cwd := dir, env := compilerEnv }
    let objects := (← (lib / ".." / "native").walkDir).filter (·.extension == some "o")
    let plugin := dir / "PairImports.so"
    discard <| IO.Process.run {
      cmd := "leanc", cwd := dir
      args := #["-shared", "-fPIC", "-DLEAN_EXPORTING", "PairImports.c"] ++
        (objects.map (·.toString)) ++ #["-o", plugin.toString] }
    loadPlugin plugin (some "runtime_initialize_PairImports")
    IO.FS.writeFile (dir / "PairSmoke.lean") consumer
    let proc ← IO.Process.output {
      cmd := "lean", args := #["-c", "PairSmoke.c", "-o", "PairSmoke.olean", "PairSmoke.lean"]
      cwd := dir, env := compilerEnv }
    unless proc.exitCode == 0 do throw <| IO.userError (proc.stdout ++ proc.stderr)
    searchPathRef.set [dir, lib]
    let env ← importModules #[{module := `PairSmoke, importAll := true}] {} (level := .private)
    let some (.inductInfo bool) := env.find? `Bool | throw <| IO.userError "missing Boolean type"
    unless bool.numParams == 0 && bool.ctors == [`Bool.false, `Bool.true] do
      throw <| IO.userError "unexpected Boolean representation"
    let natTy := mkConst `Nat
    let some large := env.find? `largeArithmetic | throw <| IO.userError "missing large arithmetic consumer"
    unless Kernel.isDefEqGuarded env {} large.type (.forallE `n natTy natTy .default) do
      throw <| IO.userError "incorrect native Nat interface"
    let compute ← IO.ofExcept <| env.evalConst (Nat → Nat) {} `largeArithmetic
    for n in [0, 2^63, 2^127 + 1] do
      unless compute n == (n + 2^64) * 3 do throw <| IO.userError s!"invalid large arithmetic result at {n}"
    let b := mkConst `Bool
    let arity := .forallE `x b (.forallE `y b b .default) .default
    let first := fun (x _ : Bool) => x
    let second := fun (_ y : Bool) => y
    let checks := [(`firstValue, first), (`secondValue, second), (`additionFirst, first),
      (`stateSecond, second), (`optionFirst, first), (`composeSecond, second), (`mappedFirst, first),
      (`sumIndex, first), (`sumRight, or), (`boolEqual, BEq.beq), (`transportedDecision, BEq.beq), (`optionFiltered, and),
      (`controlResult, or), (`optionEqual, BEq.beq), (`someValue, and), (`attachedValue, and), (`liftedNumeral, or), (`lastElement, second),
      (`arithmetic, first), (`listDisjunction, or), (`naturalEqual, BEq.beq),
      (`naturalLe, fun x y => !x || y), (`arraySecond, second), (`bitEqual, BEq.beq),
      (`boundedLess, fun x y => !x && y), (`bitConjunction, and), (`word8Less, fun x y => !x && y),
      (`word16Equal, BEq.beq), (`word32Le, fun x y => !x || y), (`word64Equal, BEq.beq),
      (`byteBufferSecond, second), (`updatedLookup, second), (`outsideLookup, second),
      (`slicedLookup, second), (`listEqual, BEq.beq), (`optionalListEmpty, fun x _ => !x),
      (`pairEqual, BEq.beq), (`sumEqual, BEq.beq), (`subtypeEqual, BEq.beq),
      (`sigmaEqual, BEq.beq), (`psigmaEqual, BEq.beq), (`chooseValue, and), (`disjunction, or), (`conjunction, and)]
    for (name, expected) in checks do
      let some ci := env.find? name | throw <| IO.userError s!"missing {name}"
      unless Kernel.isDefEqGuarded env {} ci.type arity do throw <| IO.userError s!"invalid type of {name}"
      let fn ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} name
      for x in [false, true] do
        for y in [false, true] do
          unless fn x y == expected x y do
            throw <| IO.userError s!"invalid executable result for {name} at {x}, {y}"
