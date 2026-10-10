import LeanInformationAuditRegAnalysis.AuricFib.Native

namespace LeanInformationAudit.AuricFib
open Lean
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)

/-- Exact inputs are integer or integer/positive-integer strings, never rounded floats. -/
def parseRational (value : Json) : Except String Rat := do
  let s ← value.getStr?
  let parts := s.splitOn "/"
  let numerator ← match parts with
    | [n] | [n, _] => match n.toInt? with
      | some n => pure n | none => throw "invalid rational numerator"
    | _ => throw "expected an integer or numerator/denominator string"
  let denominator ← match parts with
    | [_] => pure 1
    | [_, d] => match d.toNat? with
      | some d => pure d | none => throw "invalid rational denominator"
    | _ => throw "invalid rational"
  if denominator = 0 then throw "rational denominator must be positive"
  return (numerator : Rat) / (denominator : Rat)

def rationalJson (q : Rat) : Json := Json.mkObj [
  ("numerator", toJson (toString q.num)), ("denominator", toJson (toString q.den))]

def requireKeys (value : Json) (allowed : List String) : Except String Unit := do
  let object ← value.getObj?
  for (key, _) in object.toArray do
    unless allowed.contains key do throw s!"unexpected field: {key}"

structure SourceInput where
  kind : String
  source : String
  law : Option (Array Rat)
  sampleCount : Option Nat := none

def parseCell (value : Json) : Except String Rat := do
  let q ← parseRational value
  if q < 0 then throw "source mass must be nonnegative"
  return q

def validateLaw (law : Array Rat) : Except String (Array Rat) := do
  unless law.size = 5 do throw "law must have five cells in null,2,5,25,3 order"
  unless law.all (· ≥ 0) do throw "source mass must be nonnegative"
  unless law.foldl (· + ·) 0 = 1 do throw "source masses must sum exactly to one"
  return law

/-- Archive coordinates are low 2, high 5, middle 3; the middle excludes both ends. -/
def parseAtom (value : Json) : Except String Window := do
  let cells ← value.getArr?
  unless cells.size = 3 do throw "an atom has exactly x2,y5,z3 coordinates"
  let bits ← cells.mapM fun cell => do
    let n ← cell.getNat?
    unless n ≤ 1 do throw "atom coordinates must be integer bits"
    return n == 1
  let x := bits[0]!
  let y := bits[1]!
  let z := bits[2]!
  if z && (x || y) then throw "illegal atom: middle cannot coexist with either endpoint"
  return if z then .middle else if x && y then .ends else if x then .low
    else if y then .high else .zero

def parseSource (request : Json) : Except String SourceInput := do
  let contract? := request.getObjVal? "source_contract" |>.toOption
  match contract? with
  | none =>
    if (request.getObjVal? "law").isOk || (request.getObjVal? "archive").isOk then
      throw "law or archive requires a source contract"
    return ⟨"unknown", "missing-source-contract", none, none⟩
  | some contract =>
    requireKeys contract ["kind", "source", "window_length", "native_contract"]
    let kind ← contract.getObjValAs? String "kind"
    let source ← contract.getObjValAs? String "source"
    unless !source.trimAscii.toString.isEmpty do throw "source provenance must be nonempty"
    let length ← contract.getObjValAs? Nat "window_length"
    unless length = 1 do throw "only the complete initialized single-window source is implemented"
    let native ← contract.getObjValAs? String "native_contract"
    unless native = "initialized-high-to-low-high-suffix" do
      throw "unsupported native contract; the continuation response bridge does not transfer"
    let hasLaw := (request.getObjVal? "law").isOk
    let hasArchive := (request.getObjVal? "archive").isOk
    match kind with
    | "declared-finite-law" =>
      unless hasLaw && !hasArchive do throw "declared law requires law and excludes archive"
      let law ← (← (request.getObjVal? "law") >>= Json.getArr?).mapM parseCell
      return ⟨kind, source, some (← validateLaw law), none⟩
    | "empirical-archive" =>
      unless hasArchive && !hasLaw do throw "empirical contract requires archive and excludes law"
      let archive ← (← (request.getObjVal? "archive") >>= Json.getArr?).mapM parseAtom
      if archive.isEmpty then return ⟨kind, source, none, some 0⟩
      let law := (List.range 5).toArray.map fun index =>
        ((archive.filter (fun a => modeIndex a == index)).size : Rat) / (archive.size : Rat)
      return ⟨kind, source, some (← validateLaw law), some archive.size⟩
    | "unknown" =>
      unless !hasLaw && !hasArchive do throw "unknown source cannot supply an acquired law"
      return ⟨kind, source, none, none⟩
    | _ => throw "unknown source-contract kind"

def sourceJson (input : SourceInput) : Json := Json.mkObj [
  ("kind", toJson input.kind), ("source", toJson input.source),
  ("window_length", toJson (1 : Nat)),
  ("native_contract", toJson "initialized-high-to-low-high-suffix"),
  ("sample_count", toJson input.sampleCount),
  ("pushforward_law", input.law.map (fun law => Json.arr (law.map rationalJson)) |>.getD Json.null),
  ("numeric_domain", toJson "exact rational cells; nonrational laws are not approximated"),
  ("legality", toJson "five legal atoms; nonnegative cells; exact normalized mass when available"),
  ("physical_law_certified", toJson false), ("iid_assumed", toJson false),
  ("joint_contract", toJson "one initialized window and its same-state suffix only"),
  ("limits", toJson ["a source label supplies provenance, not physical certification",
    "empirical archive frequencies do not certify a true law",
    "a single sample does not identify an unknown source law",
    "single-window pushforward does not identify multiwindow joint history"])]

end LeanInformationAudit.AuricFib
