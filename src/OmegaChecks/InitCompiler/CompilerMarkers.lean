module
public import Lean

open Lean

namespace OmegaChecks.InitPort.CompilerMarkers

/-- These three root names occur literally in Lean's native type representation. -/
public def names := #[`lcAny, `lcErased, `lcVoid]

/-- Each marker is an opaque type inhabited at the type level by the closed term `Prop`. -/
public def declaration (name : Name) : ConstantInfo :=
  .opaqueInfo {
    name, levelParams := [], type := .sort (.succ .zero), value := .sort .zero
    isUnsafe := false, all := [name]}

public def valid (ci : ConstantInfo) : Bool :=
  let expected := declaration ci.name
  names.contains ci.name && ci == expected && ci.type.equal expected.type &&
    (ci.value? (allowOpaque := true)).any (·.equal (.sort .zero))

/-- Check every physical occurrence, including private imports and duplicate name entries. -/
public def check (env : Environment) : IO Unit := do
  let mut seen := NameSet.empty
  for owner in env.header.moduleNames, data in env.header.moduleData do
    for name in data.constNames, ci in data.constants do
      if names.contains name || names.contains ci.name then
        unless owner == `OmegaInit.Prelude && name == ci.name && valid ci && !seen.contains name do
          throw <| IO.userError s!"invalid native compiler marker {owner}/{name}"
        seen := seen.insert name
  unless seen.isEmpty || names.all seen.contains do
    throw <| IO.userError "incomplete native compiler markers"

end OmegaChecks.InitPort.CompilerMarkers
