import LeanInformationAudit.Census.Coverage
import LeanInformationAudit.Census.Report

namespace LeanInformationAudit.CensusManifest

open Lean Meta DispositionCensus

private def literalNameExpr : Name → Expr
  | .anonymous => mkConst ``Name.anonymous
  | .str parent part => mkApp2 (mkConst ``Name.str) (literalNameExpr parent) (toExpr part)
  | .num parent part => mkApp2 (mkConst ``Name.num) (literalNameExpr parent) (toExpr part)

/-- All renderers consume ascending decoded ids. Name/hex/Nat correspondence is
an elaborator obligation; the JSON retains the original structured Name and hex. -/
def canonicalKeys (keys : Array StatementKey) : Except String (List Nat) := do
  let values ← keys.mapM fun key => decodeStatementId key.theoremName key.statementId
  return (values.qsort (· < ·)).toList

private def bindKeys (component : String) (wire : Array StatementKey)
    (keys : List Nat) : Except String Unit := do
  let sorted := wire.qsort (fun a b => a.statementId < b.statementId)
  unless sorted.size == keys.length do
    throw <| identityError .anonymous component (toString sorted.size) (toString keys.length)
  for (key, value) in sorted.toList.zip keys do
    bindStatementIdNat key.theoremName key.statementId value

/-- Both sides have independent authorities: actual rows and immutable report.
This checks metadata and Name-level binding; the kernel claims only an id set. -/
def checkManifestBinding (report : FrozenReport) (root : Name) (rows : Array StatementKey)
    (m : CensusKeyManifest) (reportKeys : List Nat) : Except String Unit := do
  checkIdentityInputs report.headSha report.theorems rows
  unless m.reportSha256 == report.reportSha256 do
    throw <| identityError .anonymous "report_sha256" report.reportSha256 m.reportSha256
  unless m.censusRoot == root do
    throw <| identityError .anonymous "census_root" (nameJson root).compress (nameJson m.censusRoot).compress
  checkKeyIdentity report.headSha report.theorems m.headSha rows
  bindKeys "manifest_keys" rows m.keys
  bindKeys "report_keys" report.theorems reportKeys
  checkMissingKeys report.headSha report.theorems rows

private def bindingError (component : String) : MetaM α :=
  throwError "{identityError .anonymous component "independent canonical chunks" "alias or expression"}"

/-- Pack validated 256-bit ids, least significant digit first. -/
def packIds (ids : List Nat) : Nat :=
  ids.foldr (fun value packed => value + 2 ^ 256 * packed) 0

/-- Match both the chunk graph and every packed Nat literal. No evalExpr or
unfolding of global definitions: cross-side aliases, moves, duplication, order
and arity changes are rejected before publication. -/
def bindChunkedKeys (listName : Name) (component : String)
    (wire : Array StatementKey) (bucket : Option (Nat × Nat) := none)
    (declarations : Option (Array ConstantInfo) := none) : MetaM (List Nat) := do
  let lookup (name : Name) : MetaM DefinitionVal := do
    if let some declarations := declarations then
      let some (.defnInfo value) := declarations.find? (·.name == name) | bindingError component
      return value
    getConstInfoDefn name
  let keys ← ofExcept <| canonicalKeys wire
  let keyArray := keys.toArray
  let chunkCount := (wire.size + 99) / 100
  let names ← (List.range chunkCount).mapM fun n => do
    let name := listName ++ .mkSimple ("chunk" ++ toString n)
    let present := if let some ds := declarations then ds.any (·.name == name)
      else (← getEnv).contains name
    return if present then name else mkPrivateNameCore listName.getPrefix name
  let decoded := names.zipIdx |>.map fun (name, n) =>
    mkApp2 (mkConst ``decodeIds) (mkNatLit (min 100 (wire.size - n * 100))) (mkConst name)
  let chunks ← mkListLit (toTypeExpr (List Nat)) decoded
  let expected ← mkAppM ``List.flatten #[chunks]
  -- List notation inserts local lets. Substitute only those lets; global
  -- definitions (including an alias to the other side) remain opaque.
  let joined ← zetaReduce (← lookup listName).value (zetaDelta := false) (beta := false)
  unless joined == expected do bindingError (component ++ "_binding")
  for n in [:chunkCount] do
    let actual := (← lookup names[n]!).value
    unless actual.isAppOfArity ``OfNat.ofNat 3 do bindingError component
    let .lit (.natVal value) := actual.getAppArgs[1]! | bindingError component
    unless actual == mkNatLit value do bindingError component
    let chunk := keyArray.extract (n * 100) ((n + 1) * 100) |>.toList
    if let some (k, b) := bucket then
      unless (decodeIds chunk.length value).all (fun id => idPrefix b id == k) do
        bindingError "bucket_prefix"
    let packed := packIds chunk
    unless (.lit (.natVal value) : Expr) == .lit (.natVal packed) do
      -- Preserve the row's strict codec diagnostic on a mismatching digit.
      let ordered := wire.qsort (fun a b => a.statementId < b.statementId)
      for (key, digit) in (ordered.extract (n * 100) ((n + 1) * 100)).toList.zip
          (decodeIds chunk.length value) do
        ofExcept <| bindStatementIdNat key.theoremName key.statementId digit
      bindingError component
  return keys

private def natConstant (name : Name) (component : String) : MetaM Nat := do
  let value := (← getConstInfoDefn name).value
  unless value.isAppOfArity ``OfNat.ofNat 3 do bindingError component
  let .lit (.natVal n) := value.getAppArgs[1]! | bindingError component
  unless value == mkNatLit n do bindingError component
  return n

/-- Read just one leaf's serialized declarations. The existing exported Init
environment supplies types; private Init imports are never reloaded per leaf.
Only Unit escapes the fresh Meta state before the leaf's regions are freed. -/
private unsafe def bindLeafIO (env : Environment) (module scope : Name)
    (rows report : Array StatementKey) (k b n : Nat) : IO Unit := do
  let path ← findOLean module
  let levels : Array OLeanLevel := #[.exported, .server, .private]
  let parts ← readModuleDataParts (levels.map (·.adjustFileName path))
  try
    let some (data, _) := parts[2]? | throw <| IO.userError "missing private leaf declarations"
    let declarations := some data.constants
    let check : MetaM Unit := do
      let inv ← bindChunkedKeys (scope ++ `manifestKeys) "manifest_keys" rows (some (k, b)) declarations
      discard <| bindChunkedKeys (scope ++ `reportKeys) "report_keys" report (some (k, b)) declarations
      unless inv.length == n do bindingError "bucket_length"
    discard <| check.run' |>.toIO { fileName := "<census-leaf-binding>", fileMap := default } { env }
  finally
    for (_, region) in parts do region.free

private def rangeModule (scope : Name) (b k : Nat) : Name :=
  scope ++ .mkSimple ("Range" ++ toString b ++ "_" ++ toString k)

private def bindImports (module : Name) (expected : Array Name) : MetaM Unit := do
  let env ← getEnv
  let some index := env.header.moduleNames.findIdx? (· == module) | bindingError "bucket_imports"
  unless ((env.header.moduleData[index]!).imports.map (·.module)).filter (· != `Init) == expected do
    bindingError "bucket_imports"

/-- The driver holds the exported tree and the two key authorities. Private
literal/proof pages are read one leaf at a time, never as a whole-tree import. -/
def bindBuckets (listName reportName : Name) (rows report : Array StatementKey) : MetaM Unit := do
  let scope := listName.getPrefix
  let minBits ← natConstant (scope ++ `prefixBits) "bucket_prefix_bits"
  let bound ← natConstant (scope ++ `leafBound) "bucket_leaf_bound"
  let repository ← IO.currentDir
  let configured ← IO.Process.output { cmd := "python3", args := #[
    (repository / "tools/lean-inspector/Census/Certificate/config.py").toString] }
  unless minBits ≤ 256 && bound > 0 && configured.exitCode == 0 &&
      configured.stdout.trimAscii.toString.toNat? == some bound do bindingError "bucket_leaf_bound"
  let sorted (keys : Array StatementKey) : MetaM (Array (Nat × StatementKey)) := do
    let pairs ← keys.mapM fun key => do
      return (← ofExcept <| decodeStatementId key.theoremName key.statementId, key)
    return pairs.qsort (fun a b => a.1 < b.1)
  let inv ← sorted rows
  let rep ← sorted report
  let lower (keys : Array (Nat × StatementKey)) (start stop pivot : Nat) : Nat := Id.run do
    let mut lo := start
    let mut hi := stop
    while lo < hi do
      let mid := (lo + hi) / 2
      if keys[mid]!.1 < pivot then lo := mid + 1 else hi := mid
    return lo
  let rec visit (fuel b k il ih rl rh : Nat) : MetaM Unit := do
    let node := if b == 0 then scope else rangeModule scope b k
    let module := if b == 0 then scope ++ `Root else node
    unless (← natConstant (node ++ `k) "bucket_prefix") == k &&
        (← natConstant (node ++ `b) "bucket_prefix") == b do bindingError "bucket_prefix"
    let n ← natConstant (node ++ `n) "bucket_length"
    unless n == ih - il do bindingError "bucket_length"
    let leaf := b ≥ minBits && max (ih - il) (rh - rl) ≤ bound
    unless (← natConstant (node ++ `leaf) "bucket_leaf_bound") == (if leaf then 1 else 0) do
      bindingError "bucket_leaf_bound"
    if leaf then
      bindImports module #[`LeanInformationAudit.Census.Certificate]
      unsafe bindLeafIO (← getEnv) module node
        ((inv.extract il ih).map (·.2)) ((rep.extract rl rh).map (·.2)) k b n
    else
      match fuel with
      | 0 => bindingError "bucket_prefix_bits"
      | fuel + 1 =>
        let left := rangeModule scope (b + 1) (k * 2)
        let right := rangeModule scope (b + 1) (k * 2 + 1)
        bindImports module #[left, right]
        for (list, side, component) in [(if b == 0 then listName else node ++ `manifestKeys,
            `manifestKeys, "manifest_keys"), (if b == 0 then reportName else node ++ `reportKeys,
            `reportKeys, "report_keys")] do
          let expected ← mkAppM ``List.append #[mkConst (left ++ side), mkConst (right ++ side)]
          let joined ← zetaReduce (← getConstInfoDefn list).value (zetaDelta := false) (beta := false)
          -- Compare the canonical append graph without reducing either child.
          unless joined == expected do bindingError (component ++ "_binding")
          let args := joined.getAppArgs
          unless args.size ≥ 2 && args[args.size - 2]! == mkConst (left ++ side) &&
              args[args.size - 1]! == mkConst (right ++ side) do bindingError (component ++ "_binding")
        let pivot := (k * 2 + 1) * 2 ^ (255 - b)
        let im := lower inv il ih pivot
        let rm := lower rep rl rh pivot
        visit fuel (b + 1) (k * 2) il im rl rm
        visit fuel (b + 1) (k * 2 + 1) im ih rm rh
  visit 256 0 0 0 inv.size 0 rep.size

def bindEmittedManifest (report : FrozenReport) (root : Name) (rows : Array StatementKey)
    (manifestName reportKeysName : Name) : MetaM Unit := do
  ofExcept <| checkIdentityInputs report.headSha report.theorems rows
  let value := (← getConstInfoDefn manifestName).value
  unless value.isAppOfArity ``CensusKeyManifest.mk 4 do bindingError "manifest_keys"
  let args := value.getAppArgs
  let .lit (.strVal head) := args[0]! | bindingError "head"
  let .lit (.strVal sha) := args[1]! | bindingError "report_sha256"
  unless sha == report.reportSha256 do
    throwError "{identityError .anonymous "report_sha256" report.reportSha256 sha}"
  unless args[2]! == literalNameExpr root do bindingError "census_root"
  ofExcept <| checkKeyIdentity report.headSha report.theorems head rows
  let listName := manifestName.appendAfter "Keys"
  unless args[3]! == mkConst listName do bindingError "manifest_keys"
  if reportKeysName == listName then bindingError "report_keys_binding"
  bindBuckets listName reportKeysName rows report.theorems
  ofExcept <| checkMissingKeys report.headSha report.theorems rows

/-- Decide only linear order and length. Reflexivity compares the independently
bound chunk graphs for equality without deciding quadratic Nodup/Finset goals. -/
def certificateProof (ids : Expr) (requested : Nat) (reportIds : Expr) : MetaM Expr := do
  let ordered ← mkAppM ``strictlyAscending #[ids]
  let orderProof ← mkDecideProof (← mkEq ordered (toExpr true))
  let length ← mkAppM ``List.length #[ids]
  let lengthProof ← mkDecideProof (← mkEq length (toExpr requested))
  let equalityProof ← mkEqRefl ids
  let tail ← mkAppM ``And.intro #[lengthProof, equalityProof]
  let proof ← mkAppM ``And.intro #[orderProof, tail]
  let expected ← mkAppM ``CensusKeyManifest.Certificate #[ids, toExpr requested, reportIds]
  unless ← isDefEq (← inferType proof) expected do
    throwError "{identityError .anonymous "certificate_type" "id order, length and report equality" "detached proof"}"
  checkWithKernel proof
  return proof

end LeanInformationAudit.CensusManifest
