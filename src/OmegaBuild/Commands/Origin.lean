module

public meta import Lean.Environment

public meta section

namespace OmegaBuild

open Lean

/-- Independent official modules can emit the same name. The importer's owner
index and its active term can come from different copies. Read the stored entry. -/
def declaredIn (env : Environment) (name owner : Name) : Bool := Id.run do
  let some expected := env.getModuleIdx? owner | return false
  let some info := env.find? name | return false
  let some entry := env.header.moduleData[expected]!.constants.find? (·.name == name) | return false
  if let .thmInfo a := entry then
    let .thmInfo b := info | return false
    -- Structural equality includes binder names and annotations. The kernel identifies
    -- proofs of the same proposition, including distinct compiler-generated proofs.
    return a.levelParams == b.levelParams && a.type.equal b.type
  unless entry == info && entry.type.equal info.type do return false
  if let .recInfo a := entry then
    let .recInfo b := info | return false
    return (a.rules.zip b.rules).all fun (x, y) => x.rhs.equal y.rhs
  return (entry.value? (allowOpaque := true)).map ExprStructEq.mk ==
    (info.value? (allowOpaque := true)).map ExprStructEq.mk

end OmegaBuild
