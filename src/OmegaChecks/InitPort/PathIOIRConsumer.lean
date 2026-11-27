module
import Lean

open Lean

private inductive Unary where
  | zero
  | succ (n : Unary)
deriving BEq

private def fromNat : Nat → Unary
  | 0 => .zero
  | n + 1 => .succ (fromNat n)

private abbrev Bytes := List Unary
private def encode (s : String) : Bytes := s.toUTF8.data.toList.map fun b => fromNat b.toNat

private inductive Status where
  | ok
  | existsAlready (filename : Option Bytes) (code : Unary) (details : Bytes)
  | missing (filename : Bytes) (code : Unary) (details : Bytes)
  | other
deriving BEq

private abbrev PathOp := Bytes → Unit → Status × Unit

-- The host interpreter must execute each call at its place in the IO sequence.
@[noinline] private def perform (op : PathOp) (path : Bytes) : IO Status := do
  let arg ← IO.mkRef path
  return (op (← arg.get) ()).1

public unsafe def main (args : List String) : IO Unit := do
  let [library, consumer, oldName, newName, file] := args | throw <| IO.userError "expected library, consumer and fixture paths"
  searchPathRef.set [library, consumer]
  let env ← importModules #[{module := `PathIOConsumer, importAll := true}] {} (level := .private)
  let getEnv ← IO.ofExcept <| env.evalConst (Bytes → Unit → Option Bytes × Unit) {} `pathEnv
  unless (getEnv (encode "OMEGA_PATH_TEST_VALUE") ()).1 == some (encode "héλ界") &&
      (getEnv (encode "OMEGA_PATH_TEST_ABSENT") ()).1 == none do throw <| IO.userError "wrong environment value"
  let mk ← IO.ofExcept <| env.evalConst PathOp {} `pathCreate
  let rm ← IO.ofExcept <| env.evalConst PathOp {} `pathRemoveDir
  let unlink ← IO.ofExcept <| env.evalConst PathOp {} `pathRemoveFile
  let rename ← IO.ofExcept <| env.evalConst (Bytes → PathOp) {} `pathRename
  let old := encode oldName
  let newPath := encode newName
  unless (← perform mk old) == .ok do throw <| IO.userError "strict createDir failed"
  let duplicate ← perform mk old
  try
    IO.FS.createDir oldName
    throw <| IO.userError "expected duplicate directory"
  catch e =>
    let .alreadyExists name code msg := e | throw e
    unless duplicate == .existsAlready (name.map encode) (fromNat code.toNat) (encode msg) do throw <| IO.userError "changed alreadyExists fields"
  unless (← perform (rename old) newPath) == .ok && (← perform rm newPath) == .ok && (← perform unlink (encode file)) == .ok do
    throw <| IO.userError "rename, directory removal or file removal failed"
  let missing ← perform unlink (encode file)
  try
    IO.FS.removeFile file
    throw <| IO.userError "expected missing file"
  catch e =>
    let .noFileOrDirectory name code msg := e | throw e
    unless missing == .missing (encode name) (fromNat code.toNat) (encode msg) do throw <| IO.userError "changed noFileOrDirectory fields"
