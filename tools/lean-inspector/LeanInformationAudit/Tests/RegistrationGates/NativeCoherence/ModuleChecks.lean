import LeanInformationAudit.Registry
import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
import LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Modern
import LeanInformationAudit.Tests.SourceIsolation

open Lean LeanInformationAudit LeanInformationAudit.TemplateAudit

-- Resolve the elaborated production declaration without publishing a decoder API.
-- Trace output verification truncates to 16 characters, so it cannot exercise
-- the decoder's width check directly or establish the decoded numeric value.
run_cmd do
  let parsers := (← getEnv).constants.toList.filter fun (name, _) =>
    privateToUserName? name ==
      some `LeanInformationAudit.TemplateAudit.NativeCoherence.parseHash
  unless parsers.length == 1 do
    throwError "[FAIL] direct_trace_hash: expected one private production decoder"
  let parser := mkIdent parsers.head!.1
  Elab.Command.elabCommand (← `(command| run_cmd do
    let decode : String → Except String UInt64 := $parser
    for (label, text, expected) in (#[
        ("zero", "0000000000000000", 0),
        ("signed_boundary", "8000000000000000", 9223372036854775808),
        ("maximum", "ffffffffffffffff", 18446744073709551615),
        ("digit_nine", "0000000000000009", 9),
        ("digit_a", "000000000000000a", 10),
        ("digit_f", "000000000000000f", 15),
        ("leading_nine", "9000000000000000", 10376293541461622784),
        ("leading_a", "a000000000000000", 11529215046068469760),
        ("leading_f", "f000000000000000", 17293822569102704640),
        ("mixed_digits", "0123456789abcdef", 81985529216486895)] :
        Array (String × String × Nat)) do
      match decode text with
      | .ok actual =>
        unless actual.toNat == expected do
          throwError "[FAIL] direct_trace_hash_{label}: expected={expected} actual={actual.toNat}"
      | .error reason => throwError "[FAIL] direct_trace_hash_{label}: {reason}"
      logInfo m!"[PASS] direct_trace_hash_{label} value={expected}"
    for (label, text, width) in (#[
        ("short", "000000000000000", 15),
        ("long", "00000000000000000", 17),
        ("uppercase_a", "000000000000000A", 16),
        ("uppercase_f", "F000000000000000", 16),
        ("below_digit", "/000000000000000", 16),
        ("above_digit", "00000000:0000000", 16),
        ("below_lowercase", "000000000000000`", 16),
        ("above_lowercase", "000000000000000g", 16),
        ("nonascii_short", "0000000000000é", 15),
        ("nonascii_exact", "00000000000000é", 16),
        ("nonascii_long", "000000000000000é", 17),
        ("nonascii_three_bytes", "漢0000000000000", 16),
        ("nonascii_four_bytes", "000000000000😀", 16),
        ("multiple_invalid_first", "g000000A0000000?", 16),
        ("multiple_invalid_middle", "000g000A0000000?", 16)] :
        Array (String × String × Nat)) do
      unless text.utf8ByteSize == width do
        throwError "[FAIL] direct_trace_hash_{label}: fixture byte width differs"
      -- The first-invalid diagnostic is deliberately the same for every invalid
      -- byte; later invalid bytes must not replace it with another error.
      match decode text with
      | .error reason =>
        unless reason == "incomplete_closure:E7.native_trace_hash" do
          throwError "[FAIL] direct_trace_hash_{label}: unexpected diagnostic {reason}"
      | .ok actual =>
        throwError "[FAIL] direct_trace_hash_{label}: accepted value={actual.toNat}"
      logInfo m!"[PASS] direct_trace_hash_{label} bytes={width}"))

private def replaceNative (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temp := path.withExtension "dtr-module-temporary"
  IO.FS.writeBinFile temp bytes
  IO.FS.rename temp path

private def observe (label : String) (root : Name) (expected : String) : CoreM Bool := do
  let reason ← try
    NativeCoherence.validate #[root]
    pure ""
  catch error => pure (← error.toMessageData.toString)
  let ok := reason == expected
  (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label} actual={reason}"
  return ok

run_meta LeanInformationAudit.Tests.withPrivateSources do
  let saved ← getEnv
  let root := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Modern
  let legacy := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Plain
  discard <| observe "legacy_native_still_accepted" legacy ""
  setEnv saved
  let fresh ← observe "fresh_module_native_report_accepted" root ""
  setEnv saved
  let source : System.FilePath := sourcePath root
  let sourceBytes ← IO.FS.readBinFile source
  try
    replaceNative source (sourceBytes ++ "\n-- stale native source\n".toUTF8)
    discard <| observe "stale_module_source_rejected" root
      s!"incomplete_closure:E7.native_source:{root}"
  finally
    replaceNative source sourceBytes
    setEnv saved
  let olean ← findOLean root
  for (path, kind) in #[(olean.addExtension "private", "private"),
      (olean.withExtension "ir", "ir")] do
    let bytes ← IO.FS.readBinFile path
    try
      replaceNative path (bytes.push 0)
      discard <| observe s!"changed_module_{kind}_artifact_rejected" root
        s!"incomplete_closure:E7.loaded_native:{root}"
    finally
      replaceNative path bytes
      setEnv saved
    if fresh then
      NativeCoherence.validate #[root]
      try
        replaceNative path (bytes.push 0)
        discard <| observe s!"cached_module_{kind}_artifact_rejected" root
          "incomplete_closure:E7.native_input_changed"
      finally
        replaceNative path bytes
        setEnv saved
  discard <| observe "restored_module_native_accepted" root ""
  setEnv saved

-- Exercise the real export/verification path: malformed hash text is a syntax
-- rejection, while valid boundary values reach the native-output comparison.
run_meta LeanInformationAudit.Tests.withPrivateSources do
  let saved ← getEnv
  let root := `LeanInformationAudit.Tests.RegistrationGates.NativeCoherence.Modern
  let tracePath := (← findOLean root).withExtension "trace"
  let original ← IO.FS.readBinFile tracePath
  let trace ← ofExcept <| Json.parse (String.fromUTF8! original)
  let outputs ← ofExcept <| trace.getObjVal? "outputs"
  let hashes ← ofExcept <| outputs.getObjValAs? (Array String) "o"
  for (label, text, valid) in #[
      ("zero", "0000000000000000", true),
      ("signed_boundary", "8000000000000000", true),
      ("maximum", "ffffffffffffffff", true),
      ("short", "000000000000000", false),
      ("uppercase", "000000000000000A", false),
      ("nonhex", "000000000000000g", false),
      ("nonascii", "00000000000000é", false)] do
    let changed := trace.setObjVal! "outputs"
      (outputs.setObjVal! "o" (toJson (hashes.set! 0 text)))
    try
      replaceNative tracePath changed.compress.toUTF8
      let expected := if valid then s!"incomplete_closure:E7.native_output:{root}"
        else "incomplete_closure:E7.native_trace_hash"
      discard <| observe ("trace_hash_" ++ label ++ "_rejected") root expected
    finally
      replaceNative tracePath original
      setEnv saved
  discard <| observe "restored_trace_hash_accepted" root ""
  setEnv saved
