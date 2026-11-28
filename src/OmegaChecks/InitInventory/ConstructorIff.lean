module
public import Lean
import OmegaChecks.InitCompiler.Equivalence
import OmegaChecks.InitPort.Translation

open Lean
namespace OmegaChecks.InitInventory

/-- Keep the binders and both operands of the official constructor law.
Recover its two implication proofs from the pinned implementation. -/
private def constructorIff? (official : Environment) (ctor : Name) (type value : Expr) :
    Option (Expr × Expr) := do
  match type, value with
  | .forallE n d t bi, .lam _ _ v _ =>
    let (target, proof) ← constructorIff? official ctor t v
    return (.forallE n d target bi, .lam n d proof bi)
  | _, _ =>
    let (_, lhs, rhs) ← type.eq?
    let (_, a, b) ← lhs.eq?
    guard (a.getAppFn.isConstOf ctor && a.getAppFn == b.getAppFn)
    let proof ← OmegaChecks.InitCompiler.logicalEquivalence? official lhs rhs value {}
    return (mkApp2 (mkConst ``Iff) lhs rhs, proof)

/-- Check the fully quantified equivalence in this specific strict product.
Partial products may omit a constructor or one of the proof's dependencies. -/
public def hasStrictConstructorIff (official strict : Environment) (ci : ConstantInfo) : Bool := Id.run do
  let .str ctor "injEq" := ci.name | return false
  unless (official.find? ctor).any (· matches .ctorInfo _) do return false
  let .thmInfo law := ci | return false
  let some (target, proof) := constructorIff? official ctor law.type law.value | return false
  let port := InitKernelPort.translate InitKernelPort.portName
  let .ok inferred := Kernel.check strict {} (port proof) | return false
  return Kernel.isDefEqGuarded strict {} inferred (port target)

end OmegaChecks.InitInventory
