import LeanInformationAudit.SealCommand
import LeanInformationAudit.Sha256

/-! Positive seal fixtures stay in this test module so their persistent registry
entries are never imported by a production root. -/

open D5.S3.ConceptDynamics.InformationEscape
open Lean

namespace LeanInformationAudit.Tests.SealSuccess

/-- info: "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" -/
#guard_msgs (info) in
#eval Sha256.hex "".toUTF8

/-- info: "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" -/
#guard_msgs (info) in
#eval Sha256.hex "abc".toUTF8

/-! T-003/T-007: the two projections each uniquely capture one coordinate. -/

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Bool × Bool)
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq

def fstRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.1
  anchor := Fin.elim0

def sndRealization : PrimitiveRealization arena.signature where
  readout := fun _ state => state.2
  anchor := Fin.elim0

information_theorem fstTheorem
  in arena
  primitives fstRealization
  : arena.Law fstRealization := by trivial

information_theorem sndTheorem
  in arena
  primitives sndRealization
  : arena.Law sndRealization := by trivial

universe u

def polymorphicArena (X : Type u) [Fintype X] [DecidableEq X] :
    PrimitiveLawArena where
  toArena := Arena.ofFintype X
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

/-! T-001: instantiate a universe-polymorphic arena with the identity Bool CUT. -/
def t001Arena := polymorphicArena Bool

local instance : DecidableEq t001Arena.State :=
  t001Arena.toArena.stateDecidableEq

def idRealization : PrimitiveRealization t001Arena.signature where
  readout := fun _ state => state
  anchor := Fin.elim0

information_theorem idTheorem
  in t001Arena
  primitives idRealization
  : t001Arena.Law idRealization := by trivial

#seal_information_theory output "/tmp/lean-information-audit-seal-success.json"

private def artifactAddress (json : Json) : Except String String := do
  let arenasJson ← Json.getObjVal? json "arenas"
  let arenas ← Json.getArr? arenasJson
  let arena ← match arenas[0]? with
    | some arena => pure arena
    | none => throw "missing first arena"
  let theoremsJson ← Json.getObjVal? arena "theorems"
  let theorems ← Json.getArr? theoremsJson
  let theoremJson ← match theorems[0]? with
    | some theoremJson => pure theoremJson
    | none => throw "missing first theorem"
  let addressJson ← Json.getObjVal? theoremJson "primitive_kernel_address"
  Json.getStr? addressJson

private def isLowerHex (character : Char) : Bool :=
  character.isDigit || ('a' ≤ character && character ≤ 'f')

private def validAddress (address : String) : Bool :=
  address.startsWith "sha256:" && address.length = 71 &&
    (address.toList.drop 7).all isLowerHex

/-- info: artifact SHA-256 address fixture passed -/
#guard_msgs (info) in
run_cmd do
  let contents ← Lean.Elab.Command.liftIO <|
    IO.FS.readFile "/tmp/lean-information-audit-seal-success.json"
  let json ← match Json.parse contents with
    | .ok json => pure json
    | .error message => throwError message
  let address ← match artifactAddress json with
    | .ok address => pure address
    | .error message => throwError message
  unless validAddress address do
    throwError "invalid primitive kernel address: {address}"
  -- `fstRealization` has the documented canonical serialization `2;0,1;2,3`.
  let digest := Sha256.hex "2;0,1;2,3".toUTF8
  let known := "39b8fbab9465b212f3c6c981877af3fbe0316b7b8571e0df3c7bf89e2762b0e1"
  unless digest = known do
    throwError "canonical serialization digest mismatch: {digest}"
  let expected := "sha256:" ++ digest
  unless address = expected do
    throwError "expected {expected}, got {address}"
  logInfo "artifact SHA-256 address fixture passed"

#check fstTheorem.__lowers_escape
#check sndTheorem.__escape_enriched
#check arena.__information_catalog
#check arena.__catalog_irredundant
#check idTheorem.__lowers_escape
#check t001Arena.__catalog_irredundant

#print axioms fstTheorem.__lowers_escape
#print axioms fstTheorem.__escape_enriched
#print axioms sndTheorem.__lowers_escape
#print axioms sndTheorem.__escape_enriched
#print axioms arena.__catalog_irredundant
#print axioms idTheorem.__lowers_escape
#print axioms idTheorem.__escape_enriched
#print axioms t001Arena.__catalog_irredundant

end LeanInformationAudit.Tests.SealSuccess
