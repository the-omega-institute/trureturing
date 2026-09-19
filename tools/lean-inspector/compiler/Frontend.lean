/- Copyright (c) 2026 The Omega Institute. Released under Apache 2.0.
   The pinned shell owns parsing of option values, plugins, setup and frontend
   execution. The Python launcher only translates its supported CLI spellings. -/
module
import all Lean.Shell
import Lean.CompanionOrigin
open Lean

private def options (args : List String) (opts : ShellOptions := {}) :
    EIO UInt32 (ShellOptions × List String) := do
  match args with
  | "--" :: files => return (opts, files)
  | flag :: value :: rest =>
    let [char] := flag.toList | throw 2
    let opts ← opts.process char (if value.isEmpty then none else some value)
    options rest opts
  | _ => throw 2

public unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match ← (options args).toBaseIO with
  | .error code => return code
  | .ok (opts, files) => shellMain files opts
