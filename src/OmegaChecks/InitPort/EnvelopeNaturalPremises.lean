module
public import OmegaChecks.InitPort.StrictReplay
import Init.GrindInstances.Ring.Nat

open Lean Meta Lean.Grind InitKernelPort

namespace OmegaChecks.InitPort.EnvelopeNaturalPremises

public def semiring :=
  mkApp2 (mkConst ``CommSemiring.toSemiring [.zero]) (mkConst ``Nat) (mkConst ``instCommSemiringNat)

public def natModule := mkApp2 (mkConst ``Semiring.toNatModule [.zero]) (mkConst ``Nat) semiring

/-- Specialize all the premises together. Check each witness against its fully instantiated
strict domain and replay their combined dependency closure in an empty kernel. -/
public def specialize (strict : Environment) (source : ConstantInfo) : MetaM Expr := do
  let env ← getEnv
  let mut applied := mkConst source.name [.zero]
  let mut ty := source.type.instantiateLevelParams source.levelParams [.zero]
  let mut roots : NameSet := {}
  while let .forallE _ domain body bi := ty do
    let arg ← if domain == .sort (.succ .zero) then pure (mkConst ``Nat)
      else if bi == .instImplicit then
        match domain.getAppFn.constName! with
        | ``Semiring => pure semiring
        | ``NatModule => pure natModule
        | ``AddRightCancel => pure (mkConst ``instAddRightCancelNat)
        | ``NoNatZeroDivisors => pure (mkConst ``instNoNatZeroDivisorsNat)
        | ``IsCharP => pure (mkConst ``instIsCharPNatOfNat)
        | ``LE => pure (mkConst ``instLENat)
        | ``LT => pure (mkConst ``instLTNat)
        | ``Std.LawfulOrderLT => pure (mkConst ``instLawfulOrderLTNat)
        | ``Std.IsPreorder => pure (mkConst ``instIsPreorderNat)
        | ``OrderedRing => pure (mkConst ``instOrderedRingNat)
        | ``ExistsAddOfLT => pure (mkConst ``instExistsAddOfLTNat)
        | cls => throwError "unexpected natural class {cls}"
      else if domain.isConstOf ``Nat then pure (mkRawNatLit 0)
      else throwError "unexpected natural specialization of {source.name}"
    let witness := translate portName arg
    let actual ← ofExceptKernelException (Kernel.check strict {} witness)
    unless Kernel.isDefEqGuarded strict {} actual (translate portName domain) do
      throwError "natural witness has a different strict type for {source.name}"
    for n in witness.getUsedConstants do roots := roots.insert n
    applied := mkApp applied arg
    ty := body.instantiate1 arg
  let actual ← ofExceptKernelException (Kernel.check env {} applied)
  unless Kernel.isDefEqGuarded env {} actual ty do throwError "failed to instantiate every premise"
  let _ ← replayStrict strict.toKernelEnv roots.toArray
  return ty

end OmegaChecks.InitPort.EnvelopeNaturalPremises
