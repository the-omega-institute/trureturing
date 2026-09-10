import Lean

namespace LeanInformationAudit

open Lean

/-- Machine identity preserves Name constructors, independently of display text. -/
def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent part => Json.arr #[toJson "str", nameJson parent, toJson part]
  | .num parent part => Json.arr #[toJson "num", nameJson parent, toJson part]

/-- Parent recursion follows a strict subtree of the structured name. -/
def parseNameJson (json : Json) : Except String Name := do
  match json with
  | .arr ⟨[tag]⟩ =>
    unless (← tag.getStr?) == "anonymous" do throw "name_constructor"
    return .anonymous
  | .arr ⟨[tag, parent, value]⟩ =>
    let parent ← parseNameJson parent
    match ← tag.getStr? with
    | "str" => return .str parent (← value.getStr?)
    | "num" => return .num parent (← fromJson? value)
    | _ => throw "name_constructor"
  | .arr _ => throw "name_components"
  | _ => throw "array expected"
termination_by sizeOf json
decreasing_by simp_wf; omega

namespace DispositionCensus

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray in
private partial def nameKeyParser : Std.Internal.Parsec.ByteArray.Parser Name := do
    skipByteChar 'n'
    match ← any with
    | 48 => return .anonymous
    | 115 =>
      skipByteChar '('
      let parent ← nameKeyParser
      skipByteChar ','
      let size ← digits
      skipByteChar ':'
      let bytes ← take size
      let some text := String.fromUTF8? bytes.toByteArray | fail "invalid UTF-8 name component"
      skipByteChar ')'
      return .str parent text
    | 110 =>
      skipByteChar '('
      let parent ← nameKeyParser
      skipByteChar ','
      let index ← digits
      skipByteChar ')'
      return .num parent index
    | _ => fail "invalid Lean name key"

/-- Decode the inspector's structured, byte-length-prefixed Name encoding. -/
def parseNameKey (text : String) : Except String Name :=
  (nameKeyParser <* Std.Internal.Parsec.eof).run text.toUTF8

end DispositionCensus
end LeanInformationAudit
