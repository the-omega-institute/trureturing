module
import all Init.Data.ToString.Name
import all Init.Data.String.Search
import all Init.Data.String.Extra

open Lean
namespace OmegaChecks.InitPort.Alternatives

public def Lean.Name.escapePart (s : String) (force : Bool := false) : Option String :=
  if h : s.utf8ByteSize > 0 then
    if !force && (private_decl% _root_.Lean.Name.needsNoEscape) s h then
      some s
    else if String.Internal.anyImpl s isIdEndEscape then
      none
    else
      some ((private_decl% _root_.Lean.Name.escape) s)
  else
    some ((private_decl% _root_.Lean.Name.escape) s)

end OmegaChecks.InitPort.Alternatives
