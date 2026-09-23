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
  (if ordered then logInfo else logError) m!"[{if ordered then "PASS" else "FAIL"}] source_digest_batch_order_and_duplicates"
  IO.FS.writeFile empty "abc"
  let changed ← readSourceInput empty.toString
  (if changed.sha256 == abcHash then logInfo else logError) m!"[{if changed.sha256 == abcHash then "PASS" else "FAIL"}] source_digest_changed_bytes"
  let longPath := directory / String.ofList (List.replicate 180 'x')
  IO.FS.writeFile longPath "abc"
  let largePaths := Array.replicate 10000 longPath.toString
  let transported ← try
    let rows ← readSourceInputs largePaths
    pure (rows.map (·.path) == largePaths && rows.all (·.sha256 == abcHash))
  catch _ => pure false
  let transportStatus := if transported then "PASS" else "FAIL"
  let pathBytes := 10000 * (longPath.toString.utf8ByteSize + 1)
  (if transported then logInfo else logError) m!"[{transportStatus}] source_digest_large_input_transport path_bytes={pathBytes}"
  let unicodePath := directory / "λ"
  IO.FS.writeFile unicodePath "abc"
  let utf8 ← try
    pure ((← readSourceInput unicodePath.toString).sha256 == abcHash)
  catch _ => pure false
  (if utf8 then logInfo else logError) m!"[{if utf8 then "PASS" else "FAIL"}] source_digest_utf8_request"
  for _ in [:40] do
    let current ← readSourceInput empty.toString
    unless current.sha256 == abcHash do throwError "source digest changed during repeated reads"
  let originalDirectory ← IO.currentDir
  let otherDirectory := directory / "other"
  IO.FS.createDir otherDirectory
  IO.FS.writeFile (directory / "relative") ""
  IO.FS.writeFile (otherDirectory / "relative") "abc"
  let relocated ← try
    IO.Process.setCurrentDir directory
    let first ← readSourceInput "relative"
    IO.Process.setCurrentDir otherDirectory
    let second ← readSourceInput "relative"
    pure (first.sha256 == emptyHash && second.sha256 == abcHash)
  finally
    IO.Process.setCurrentDir originalDirectory
  (if relocated then logInfo else logError) m!"[{if relocated then "PASS" else "FAIL"}] source_digest_current_directory"
  IO.FS.removeFile abc
  let missing ← try
    discard <| readSourceInputs paths
    pure false
  catch _ => pure true
  (if missing then logInfo else logError) m!"[{if missing then "PASS" else "FAIL"}] source_digest_missing_input_rejected"
  IO.FS.writeFile abc "abc"
  let recovered ← readSourceInput abc.toString
  let recoveryStatus := if recovered.sha256 == abcHash then "PASS" else "FAIL"
  (if recovered.sha256 == abcHash then logInfo else logError) m!"[{recoveryStatus}] source_digest_error_recovery"
