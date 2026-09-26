import Lean

namespace InformationSourceFixture
open Lean Meta Elab Command

-- This imported module has no dependency on a judge or registration module.
abbrev NameAlias := Lean.Name
abbrev BoolAlias := Bool
abbrev IntAlias := Int
abbrev CompositeAlias := Option Int
abbrev DictionaryAlias := DecidableEq Int
abbrev ErasedAlias (_ : Type) := Bool

def nameReadout (_ : NameAlias) : Bool := true
def finiteReadout (_ : BoolAlias) : Bool := true
def finiteCompositeReadout (_ : Option BoolAlias) : Bool := true
def erasedReadout (_ : ErasedAlias Int) : Bool := true
def aliasReadout (_ : IntAlias) : Bool := true
def compositeReadout (_ : Option Int) : Bool := true
def aliasedCompositeReadout (_ : CompositeAlias) : Bool := true
def dictionaryReadout (_ : DictionaryAlias) : Bool := true
def outputOnlyReadout (_ : Bool) : Int := 0

run_meta do
  let .defnInfo info <- getConstInfo ``compositeReadout | throwError "setup: missing source"
  addDecl <| .defnDecl {
    name := `InformationSourceFixture.metadataReadout,
    levelParams := info.levelParams, type := .mdata {} info.type,
    value := info.value, hints := info.hints, safety := info.safety }

end InformationSourceFixture
