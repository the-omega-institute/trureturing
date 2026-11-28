module
import Lean
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean

open OmegaChecks.InitPort.NativeState (StringRepr BytesRepr)
open OmegaChecks.InitPort.NativeState.StringRepr (encode)

private inductive Status where
  | ok
  | existsAlready (filename : Option StringRepr) (code : Nat) (details : StringRepr)
  | missing (filename : StringRepr) (code : Nat) (details : StringRepr)
  | other
deriving BEq

private inductive Outcome (α : Type) where
  | ok (value : α) (world : Unit)
  | error (error : Unit) (world : Unit)

private def unpack (r : Outcome α) : IO α :=
  match r with
  | .ok a _ => pure a
  | .error _ _ => throw <| IO.userError "unexpected strict path exception"

private abbrev PathOp := StringRepr → Unit → Status × Unit

-- The host interpreter must execute each call at its place in the IO sequence.
@[noinline] private def perform (op : PathOp) (path : StringRepr) : IO Status := do
  let arg ← IO.mkRef path
  return (op (← arg.get) ()).1

@[noinline] private def withHandle (action : IO.FS.Handle → Unit → α) (h : IO.FS.Handle) : IO α := do
  let cell ← IO.mkRef h
  return action (← cell.get) ()

/-- Strict handles are the reference-counted upstream handles. File contents cross the byte and text encodings. -/
private unsafe def checkHandle (env : Environment) (file : String) : IO Unit := do
  let openFile ← IO.ofExcept <| env.evalConst (StringRepr → Unit → Outcome IO.FS.Handle) {} `fileOpen
  let h ← unpack (openFile (encode file) ())
  let unitOp (n : Name) : IO Unit := do
    let act ← IO.ofExcept <| env.evalConst (IO.FS.Handle → Unit → Status × Unit) {} n
    unless (← withHandle act h).1 == .ok do throw <| IO.userError s!"strict {n} failed"
  let tty ← IO.ofExcept <| env.evalConst (IO.FS.Handle → Unit → Bool × Unit) {} `fileTty
  unless !(← withHandle tty h).1 do throw <| IO.userError "ordinary file reported as terminal"
  unitOp `fileLock
  unitOp `fileUnlock
  let tryLock ← IO.ofExcept <| env.evalConst (IO.FS.Handle → Unit → Outcome Bool) {} `fileTryLock
  unless ← unpack (← withHandle tryLock h) do throw <| IO.userError "file lock unavailable"
  unitOp `fileUnlock
  unitOp `fileTruncate
  let put ← IO.ofExcept <| env.evalConst (IO.FS.Handle → StringRepr → Unit → Status × Unit) {} `filePut
  let write ← IO.ofExcept <| env.evalConst (IO.FS.Handle → BytesRepr → Unit → Status × Unit) {} `fileWrite
  let text := "héλ界\n"
  let bytes : List Nat := [0, 255]
  unless (← withHandle (fun h => put h (encode text)) h).1 == .ok &&
      (← withHandle (fun h => write h (.ofList bytes)) h).1 == .ok do throw <| IO.userError "text or binary write failed"
  unitOp `fileFlush
  unless (← IO.FS.readBinFile file) == text.toUTF8 ++ ByteArray.mk #[0, 255] do
    throw <| IO.userError "bytes on disk differ from strict writes"
  unitOp `fileRewind
  let getLine ← IO.ofExcept <| env.evalConst (IO.FS.Handle → Unit → Outcome StringRepr) {} `fileLine
  unless (← unpack (← withHandle getLine h)) == encode text do throw <| IO.userError "unexpected file line"
  let read ← IO.ofExcept <| env.evalConst (IO.FS.Handle → Nat → Unit → Outcome BytesRepr) {} `fileRead
  let readBytes (size : Nat) := withHandle (fun h => read h size) h
  unless (← unpack (← readBytes 0)).data.isEmpty && (← unpack (← readBytes 9)).data == bytes &&
      (← unpack (← readBytes 1)).data.isEmpty do throw <| IO.userError "wrong binary read or EOF"

public unsafe def main (args : List String) : IO Unit := do
  let [library, consumer, oldName, newName, file, link, root] := args | throw <| IO.userError "expected library, consumer and fixture paths"
  searchPathRef.set [library, consumer]
  let env ← importModules #[{module := `PathIOConsumer, importAll := true}] {} (level := .private)
  let getEnv ← IO.ofExcept <| env.evalConst (StringRepr → Unit → Option StringRepr × Unit) {} `pathEnv
  unless (getEnv (encode "OMEGA_PATH_TEST_VALUE") ()).1 == some (encode "héλ界") &&
      (getEnv (encode "OMEGA_PATH_TEST_ABSENT") ()).1 == none do throw <| IO.userError "wrong environment value"
  let mk ← IO.ofExcept <| env.evalConst PathOp {} `pathCreate
  let rm ← IO.ofExcept <| env.evalConst PathOp {} `pathRemoveDir
  let unlink ← IO.ofExcept <| env.evalConst PathOp {} `pathRemoveFile
  let rename ← IO.ofExcept <| env.evalConst (StringRepr → PathOp) {} `pathRename
  let old := encode oldName
  let newPath := encode newName
  unless (← perform mk old) == .ok do throw <| IO.userError "strict createDir failed"
  let duplicate ← perform mk old
  try
    IO.FS.createDir oldName
    throw <| IO.userError "expected duplicate directory"
  catch e =>
    let .alreadyExists name code msg := e | throw e
    unless duplicate == .existsAlready (name.map encode) code.toNat (encode msg) do throw <| IO.userError "changed alreadyExists fields"
  unless (← perform (rename old) newPath) == .ok && (← perform rm newPath) == .ok do
    throw <| IO.userError "rename or directory removal failed"
  let hardLink ← IO.ofExcept <| env.evalConst (StringRepr → PathOp) {} `pathHardLink
  let setCwd ← IO.ofExcept <| env.evalConst PathOp {} `pathSetCwd
  let cwd ← IO.ofExcept <| env.evalConst (Unit → Outcome StringRepr) {} `pathCwd
  let processCwd ← IO.ofExcept <| env.evalConst (Unit → Outcome StringRepr) {} `pathProcessCwd
  let app ← IO.ofExcept <| env.evalConst (Unit → Outcome StringRepr) {} `pathApp
  let tmp ← IO.ofExcept <| env.evalConst (Unit → Outcome StringRepr) {} `pathTempDir
  let canonical ← IO.ofExcept <| env.evalConst (StringRepr → Unit → Outcome StringRepr) {} `pathReal
  let entries ← IO.ofExcept <| env.evalConst (StringRepr → Unit → Outcome (List (StringRepr × StringRepr))) {} `pathList
  let before := (← IO.currentDir).toString
  unless (← perform setCwd (encode root)) == .ok do throw <| IO.userError "setCurrentDir failed"
  try
    let expected := encode (← IO.currentDir).toString
    unless (← unpack (cwd ())) == expected && (← unpack (processCwd ())) == expected &&
        (← unpack (canonical (encode ".") ())) == encode (← IO.FS.realPath ".").toString do
      throw <| IO.userError "current directory or canonical path differs from upstream"
  finally
    IO.Process.setCurrentDir before
  unless (← unpack (app ())) == encode (← IO.appPath).toString do throw <| IO.userError "appPath differs from upstream"
  let created ← unpack (tmp ())
  unless (← perform rm created) == .ok do throw <| IO.userError "temporary directory removal failed"
  checkHandle env file
  unless (← perform (hardLink (encode file)) (encode link)) == .ok do throw <| IO.userError "hard link failed"
  unless (← IO.FS.readBinFile file) == (← IO.FS.readBinFile link) do throw <| IO.userError "link contents differ"
  let names ← unpack (entries (encode root) ())
  let expected := (← (System.FilePath.mk root).readDir).toList.map fun e => (encode e.root.toString, encode e.fileName)
  unless names == expected do throw <| IO.userError "directory enumeration differs from upstream"
  unless (← perform unlink (encode link)) == .ok && (← perform unlink (encode file)) == .ok do
    throw <| IO.userError "file removal failed"
  let missing ← perform unlink (encode file)
  try
    IO.FS.removeFile file
    throw <| IO.userError "expected missing file"
  catch e =>
    let .noFileOrDirectory name code msg := e | throw e
    unless missing == .missing (encode name) code.toNat (encode msg) do throw <| IO.userError "changed noFileOrDirectory fields"
