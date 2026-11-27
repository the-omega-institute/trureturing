module
public import OmegaChecks.InitPort.BufferReference
public import OmegaChecks.InitPort.StateRunner
public import OmegaChecks.InitPort.ReferenceModify

open Lean
namespace OmegaChecks.InitPort.ReferenceSpecialization

public def supportOwners := [(StateRunner.support, StateRunner.owner), (ReferenceModify.support, ReferenceModify.owner)] ++
  BufferReference.operations.map (fun op => (BufferReference.support op, BufferReference.owner))

public def consumerOwner? (n : Name) : Option Name :=
  if n == ReferenceModify.consumer then some ReferenceModify.owner
  else if StateRunner.consumers.contains n then some StateRunner.owner
  else if BufferReference.consumers.contains n then some BufferReference.owner
  else none

public def models (src templates : Environment) (owner : Name) : IO (Array ConstantInfo) := do
  if owner == ReferenceModify.owner then return #[← ReferenceModify.model src templates]
  if owner == StateRunner.owner then return #[← StateRunner.model src templates]
  if owner == BufferReference.owner then return ← BufferReference.models src templates
  throw <| IO.userError s!"unknown reference specialization owner {owner}"

public def consumerBody (src templates : Environment) (d : DefinitionVal) : IO Expr :=
  if d.name == ReferenceModify.consumer then ReferenceModify.body src templates d
  else if StateRunner.consumers.contains d.name then StateRunner.body src templates d
  else BufferReference.consumerBody src d

public def restore (templates : Environment) (owner : Name) (e : Expr) : IO Expr :=
  if owner == ReferenceModify.owner then ReferenceModify.restore templates e
  else if owner == StateRunner.owner then pure (StateRunner.restore e)
  else pure (BufferReference.restore e)

end OmegaChecks.InitPort.ReferenceSpecialization
