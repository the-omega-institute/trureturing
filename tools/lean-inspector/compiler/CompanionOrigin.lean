/- Copyright (c) 2026 The Omega Institute. Released under Apache 2.0. -/
module
prelude
public import Lean.EnvExtension
public section
namespace Lean
private builtin_initialize companionOriginExt : MapDeclarationExtension Name ←
  mkMapDeclarationExtension
-- Called only immediately after successful declaration insertion at compiler generator sites.
def recordCompanionOrigin (env : Environment) (declName site : Name) : Environment :=
  companionOriginExt.insert env declName site
def companionOrigin? (env : Environment) (declName : Name) : Option Name :=
  companionOriginExt.find? env declName
end Lean
