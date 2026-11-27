module
public import Init.Data.ByteArray.Basic
public import Init.Data.UInt.Lemmas
public import Lean

/-! Bounds required by the first read of the two machine-word byte array helpers. -/

namespace OmegaChecks.InitBoundaries.ByteArrayReads

private def last : USize :=
  USize.ofFin ⟨1, by
    cases USize.size_eq with
    | inl h => rw [h]; decide
    | inr h => rw [h]; decide⟩

private theorem less : (0 : USize) < last :=
  Nat.zero_lt_succ 0

private theorem ne : (0 : USize) ≠ last := fun e =>
  Nat.noConfusion (congrArg USize.toNat e)

public theorem noForInBound (read : ∀ (xs : ByteArray) (stop i : USize), i < stop → i.toNat < xs.size) : False :=
  Nat.not_lt_zero _ (read ByteArray.empty last 0 less)

public theorem noFoldBound (read : ∀ (xs : ByteArray) (i stop : USize), i ≠ stop → i.toNat < xs.size) : False :=
  Nat.not_lt_zero _ (read ByteArray.empty 0 last ne)

/-- The running branch of the pinned fold is the false branch of its Boolean equality. -/
public theorem noFoldBranchBound
    (read : ∀ (xs : ByteArray) (i stop : USize), ¬ ((i == stop) = true) → i.toNat < xs.size) : False := by
  apply noFoldBound
  intro xs i stop h
  exact read xs i stop fun eq => h (eq_of_beq eq)

open Lean Meta

/-- Recover the bound and its branch condition from the worker's own uget call and
match them against the zero-axiom empty-array counterexample. -/
public def readAxiom (witnesses : Environment) (source : ConstantInfo) : MetaM Name := do
  let indexed := source.name == `ByteArray.forInUnsafe.loop
  let .defnInfo d := source | throwError "expected a byte array worker"
  unless (indexed || d.name == `ByteArray.foldlMUnsafe.fold) && d.safety == .unsafe do
    throwError "unexpected byte array worker {source.name}"
  lambdaTelescope d.value fun xs body => do
    unless xs.size == 8 && body.isAppOfArity `ite 5 do throwError "unexpected byte array loop guard"
    let args := body.getAppArgs
    let branch := args[if indexed then 3 else 4]!
    let other := args[if indexed then 4 else 3]!
    let some read := branch.find? (·.isAppOfArity `ByteArray.uget 3)
      | throwError "expected a byte array read"
    unless (other.find? (·.isAppOfArity `ByteArray.uget 3)).isNone && read.appArg!.isAppOfArity `lcProof 1 do
      throwError "unexpected guard or proof of byte array read"
    let array := xs[if indexed then 3 else 4]!
    let i := xs[if indexed then 6 else 5]!
    let stop := xs[if indexed then 5 else 6]!
    unless read.getAppArgs[0]! == array && read.getAppArgs[1]! == i do
      throwError "unexpected byte array read arguments"
    let test := if indexed then args[1]! else mkNot args[1]!
    let bound := ← mkArrow test read.appArg!.appArg!
    let law ← mkForallFVars (if indexed then #[array, stop, i] else #[array, i, stop]) bound
    let name := if indexed then ``noForInBound else ``noFoldBranchBound
    let some proof := witnesses.find? name | throwError "missing bound refutation {name}"
    unless proof.type.isForall && proof.type.bindingBody!.isConstOf `False &&
        Kernel.isDefEqGuarded (← getEnv) {} proof.type.bindingDomain! law do
      throwError "byte array branch differs from {name}"
    return `lcProof

end OmegaChecks.InitBoundaries.ByteArrayReads
