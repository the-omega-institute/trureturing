import LeanInformationAudit.Registry

open Lean LeanInformationAudit.TemplateAudit

run_meta IO.FS.withTempDir fun directory => do
  let empty := directory / "empty"
  let abc := directory / "abc"
  IO.FS.writeFile empty ""
  IO.FS.writeFile abc "abc"
  let emptyHash := "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  let abcHash := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  let paths := #[empty.toString, abc.toString, abc.toString]
  let inputs ← readSourceInputs paths
  let ordered := inputs.map (·.path) == paths &&
    inputs.map (·.sha256) == #[emptyHash, abcHash, abcHash]
  logInfo m!"[{if ordered then "PASS" else "FAIL"}] source_digest_batch_order_and_duplicates"
  IO.FS.writeFile empty "abc"
  let changed ← readSourceInput empty.toString
  logInfo m!"[{if changed.sha256 == abcHash then "PASS" else "FAIL"}] source_digest_changed_bytes"
  IO.FS.removeFile abc
  let missing ← try
    discard <| readSourceInputs paths
    pure false
  catch _ => pure true
  logInfo m!"[{if missing then "PASS" else "FAIL"}] source_digest_missing_input_rejected"
