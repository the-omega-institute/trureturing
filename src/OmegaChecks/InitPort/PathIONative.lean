module
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import OmegaChecks.InitPort.BufferReference
meta import OmegaChecks.InitPort.BufferReference
import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

private def readFunctions := #[
  (`IO.FS.readFile, "omega_io_read_file", "omega_string_from_lean"),
  (`IO.FS.readBinFile, "omega_io_read_bin_file", "from_byte_array"),
  (`IO.FS.lines, "omega_io_read_lines", "strict_string_array"),
  (`IO.FS.Handle.lines, "omega_io_handle_lines", "strict_string_array"),
  (`IO.FS.Handle.readToEnd, "omega_io_handle_read_to_end", "omega_string_from_lean"),
  (`IO.FS.Handle.readBinToEnd, "omega_io_handle_read_bin_to_end", "from_byte_array"),
  (`IO.FS.Handle.readBinToEndInto, "omega_io_handle_read_bin_into", "from_byte_array")]

private def bufferOperations := OmegaChecks.InitPort.BufferReference.operations.toArray.map fun op =>
  (OmegaChecks.InitPort.BufferReference.support op, "", "omega_buffer_" ++ op.getString!)

private def reads := readFunctions.map fun (name, symbol, _) => (name, "", symbol)

private def readWrapper (source strict : Environment) (n : Name) (symbol decoder : String) : IO String := do
  let some a := source.find? n | throw <| IO.userError s!"missing file reader {n}"
  let some b := strict.find? (`Omega ++ n) | throw <| IO.userError s!"missing strict file reader {n}"
  unless b.type == InitKernelPort.translate InitKernelPort.portName a.type do throw <| IO.userError s!"different file reader types {n}"
  let some (.fdecl _ params .object ..) := IR.findEnvDecl source n | throw <| IO.userError s!"missing pinned file reader IR {n}"
  let path := n.getPrefix != `IO.FS.Handle
  let buffer := n == `IO.FS.Handle.readBinToEndInto
  let extra := if buffer then #[(IR.IRType.object, false)] else #[]
  let args := #[(if path then IR.IRType.object else .tobject, true)] ++ extra ++ #[(.void, false)]
  unless params.map (fun p => (p.ty, p.borrow)) == args do throw <| IO.userError s!"unexpected pinned read signature {n}"
  let some (.extern _ formals .object ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict (`Omega ++ n)
    | throw <| IO.userError s!"missing strict file reader ABI {n}"
  unless formals.map (·.ty) == Array.replicate args.size .tobject && entry == symbol do
    throw <| IO.userError s!"unexpected strict file reader signature {n}"
  let target := getSymbolStem source n
  let more := if buffer then ", lean_obj_arg bytes" else ""
  let input := if path then "native" else "input"
  let rest := if buffer then ", packed" else ""
  let prepare := if path then "  lean_object *native = omega_string_to_lean(input);\n" else
    if buffer then (if formals[1]!.borrow then "  lean_inc(bytes);\n" else "") ++
      "  lean_object *alias;\n  lean_object *packed = omega_bytes_native_owner(bytes, &alias);\n  uintptr_t original = (uintptr_t)packed;\n" else ""
  let release := (if path then "  lean_dec(native);\n" else "") ++ (if !formals[0]!.borrow then "  lean_dec(input);\n" else "") ++
    (if buffer then "  if (alias) lean_dec_ref(alias);\n" else "") ++ (if formals.back!.borrow then "  lean_inc(world);\n" else "")
  let finish := if buffer then "strict_byte_update_result(r, world, bytes, original)" else s!"strict_result(r, world, {decoder})"
  return s!"\nextern lean_obj_res {target}(b_lean_obj_arg input{more});\n" ++
    s!"LEAN_EXPORT lean_obj_res {symbol}(b_lean_obj_arg input{more}, lean_obj_arg world) \{\n" ++
    s!"{prepare}  lean_object *r = {target}({input}{rest});\n{release}  return {finish};\n}\n"

private def entries := #[
  (`System.FilePath.metadata, "lean_io_metadata", "omega_io_metadata"),
  (`System.FilePath.symlinkMetadata, "lean_io_symlink_metadata", "omega_io_symlink_metadata"),
  (`IO.setStdin, "lean_get_set_stdin", "omega_io_set_stdin"),
  (`IO.setStdout, "lean_get_set_stdout", "omega_io_set_stdout"),
  (`IO.setStderr, "lean_get_set_stderr", "omega_io_set_stderr"),
  (`IO.getStdin, "lean_get_stdin", "omega_io_get_stdin"),
  (`IO.getStdout, "lean_get_stdout", "omega_io_get_stdout"),
  (`IO.getStderr, "lean_get_stderr", "omega_io_get_stderr"),
  (`IO.Process.spawn, "lean_io_process_spawn", "omega_io_process_spawn"),
  (`IO.Process.Child.wait, "lean_io_process_child_wait", "omega_io_process_child_wait"),
  (`IO.Process.Child.tryWait, "lean_io_process_child_try_wait", "omega_io_process_child_try_wait"),
  (`IO.Process.Child.kill, "lean_io_process_child_kill", "omega_io_process_child_kill"),
  (`IO.Process.Child.takeStdin, "lean_io_process_child_take_stdin", "omega_io_process_child_take_stdin"),
  (`IO.Process.Child.pid, "lean_io_process_child_pid", "omega_io_process_child_pid"),
  (`IO.Process.exit, "lean_io_exit", "omega_io_exit"),
  (`IO.Process.forceExit, "lean_io_force_exit", "omega_io_force_exit"),
  (`IO.getRandomBytes, "lean_io_get_random_bytes", "omega_io_random_bytes"),
  (`IO.Prim.setAccessRights, "lean_chmod", "omega_io_set_access_rights"),
  (`IO.getEnv, "lean_io_getenv", "omega_io_get_env"),
  (`IO.FS.createDir, "lean_io_create_dir", "omega_io_create_dir"),
  (`IO.FS.removeDir, "lean_io_remove_dir", "omega_io_remove_dir"),
  (`IO.FS.removeFile, "lean_io_remove_file", "omega_io_remove_file"),
  (`IO.FS.rename, "lean_io_rename", "omega_io_rename"),
  (`IO.FS.hardLink, "lean_io_hard_link", "omega_io_hard_link"),
  (`IO.FS.realPath, "lean_io_realpath", "omega_io_real_path"),
  (`IO.FS.createTempFile, "lean_io_create_tempfile", "omega_io_create_temp_file"),
  (`IO.FS.createTempDir, "lean_io_create_tempdir", "omega_io_create_temp_dir"),
  (`IO.appPath, "lean_io_app_path", "omega_io_app_path"), (`IO.currentDir, "lean_io_current_dir", "omega_io_current_dir"),
  (`IO.Process.getCurrentDir, "lean_io_process_get_current_dir", "omega_io_process_get_current_dir"),
  (`IO.Process.setCurrentDir, "lean_io_process_set_current_dir", "omega_io_process_set_current_dir"),
  (`System.FilePath.readDir, "lean_io_read_dir", "omega_io_read_dir"),
  (`IO.FS.Handle.mk, "lean_io_prim_handle_mk", "omega_io_handle_mk"),
  (`IO.FS.Handle.lock, "lean_io_prim_handle_lock", "omega_io_handle_lock"),
  (`IO.FS.Handle.tryLock, "lean_io_prim_handle_try_lock", "omega_io_handle_try_lock"),
  (`IO.FS.Handle.unlock, "lean_io_prim_handle_unlock", "omega_io_handle_unlock"),
  (`IO.FS.Handle.isTty, "lean_io_prim_handle_is_tty", "omega_io_handle_is_tty"),
  (`IO.FS.Handle.flush, "lean_io_prim_handle_flush", "omega_io_handle_flush"),
  (`IO.FS.Handle.rewind, "lean_io_prim_handle_rewind", "omega_io_handle_rewind"),
  (`IO.FS.Handle.truncate, "lean_io_prim_handle_truncate", "omega_io_handle_truncate"),
  (`IO.FS.Handle.read, "lean_io_prim_handle_read", "omega_io_handle_read"),
  (`IO.FS.Handle.write, "lean_io_prim_handle_write", "omega_io_handle_write"),
  (`IO.FS.Handle.getLine, "lean_io_prim_handle_get_line", "omega_io_handle_get_line"),
  (`IO.FS.Handle.putStr, "lean_io_prim_handle_put_str", "omega_io_handle_put_str")]

private def convertError (source strict : Environment) (toNative : Bool) : IO String := do
  let some (.inductInfo errors) := source.find? `IO.Error | throw <| IO.userError "missing official IO.Error"
  let some (.inductInfo targetErrors) := strict.find? `Omega.IO.Error | throw <| IO.userError "missing strict IO.Error"
  unless targetErrors.ctors == errors.ctors.map (`Omega ++ ·) do throw <| IO.userError "IO.Error variants differ"
  let mut cases := ""
  for n in errors.ctors do
    let some (.ctorInfo c) := source.find? n | throw <| IO.userError s!"missing constructor {n}"
    let some src := ctorLayoutExt.find? source n | throw <| IO.userError s!"missing official layout {n}"
    let some dest := ctorLayoutExt.find? strict (`Omega ++ n) | throw <| IO.userError s!"missing strict layout {n}"
    let tag := src.ctorInfo.cidx
    unless tag == dest.ctorInfo.cidx && dest.fieldInfo.size == src.fieldInfo.size &&
        dest.ctorInfo.size == dest.fieldInfo.size && dest.ctorInfo.usize == 0 && dest.ctorInfo.ssize == 0 do
      throw <| IO.userError s!"unexpected IO.Error layout at {n}"
    unless src.ctorInfo.usize == 0 do throw <| IO.userError s!"unexpected native IO.Error pointer-sized field {n}"
    if dest.fieldInfo.isEmpty then
      cases := cases ++ s!"case {tag}: return lean_box({tag});\n"
      continue
    let output := if toNative then src.ctorInfo else dest.ctorInfo
    cases := cases ++ s!"case {tag}: \{ lean_object *out = lean_alloc_ctor({tag}, {output.size}, {output.ssize});\n"
    let mut ty := c.type
    for f in src.fieldInfo, g in dest.fieldInfo do
      let .forallE _ dom body _ := ty | throw <| IO.userError s!"unexpected type of {n}"
      let .object toIdx _ := g | throw <| IO.userError s!"expected boxed strict field of {n}"
      let code ← match f with
        | .object idx _ =>
          let (decode, encode) ← if dom == mkConst `String then pure ("omega_string_from_lean", "omega_string_to_lean")
            else if dom == mkApp (mkConst `Option [.zero]) (mkConst `String) then pure ("strict_option_string", "native_option_string")
            else throw <| IO.userError s!"unrecognized object in {n}: {dom}"
          let (conv, input, output) := if toNative then (encode, toIdx, idx) else (decode, idx, toIdx)
          pure s!"lean_ctor_set(out, {output}, {conv}(lean_ctor_get(error, {input})));\n"
        | .scalar 4 offset _ =>
          unless dom == mkConst `UInt32 do throw <| IO.userError s!"unexpected scalar in {n}"
          let address := s!"{src.ctorInfo.size} * sizeof(void*) + {offset}"
          if toNative then pure s!"lean_ctor_set_uint32(out, {address}, lean_uint32_of_nat(lean_ctor_get(error, {toIdx})));\n"
          else pure s!"lean_ctor_set(out, {toIdx}, omega_nat_from_uint64(lean_ctor_get_uint32(error, {address})));\n"
        | _ => throw <| IO.userError s!"unsupported IO.Error field layout in {n}"
      cases := cases ++ code
      ty := body
    cases := cases ++ "return out; }\n"
  let name := if toNative then "native_io_error" else "strict_io_error"
  return s!"\nstatic lean_obj_res {name}(b_lean_obj_arg error) \{\nswitch (lean_obj_tag(error)) \{\n" ++
    cases ++ "default: lean_internal_panic_unreachable();\n}\n}\n"

private def checkProcesses (source strict : Environment) : IO Unit := do
  for (env, p) in [(source, Name.anonymous), (strict, `Omega)] do
    let ctor := fun (n : Name) => do
      let some (.inductInfo t) := env.find? (p ++ n) | throw <| IO.userError s!"missing {p ++ n}"
      let [c] := t.ctors | throw <| IO.userError s!"expected structure {p ++ n}"
      let some layout := ctorLayoutExt.find? env c | throw <| IO.userError s!"missing layout {c}"
      pure layout
    let spawn ← ctor `IO.Process.SpawnArgs
    let cfg ← ctor `IO.Process.StdioConfig
    let child ← ctor `IO.Process.Child
    let pair ← ctor `Prod
    let shape := fun (l : CtorLayout) (objects scalars : Nat) =>
      l.ctorInfo.cidx == 0 && l.ctorInfo.size == objects && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == scalars
    unless shape spawn 5 2 && (spawn.fieldInfo matches #[.object 0 _, .object 1 _, .object 2 _, .object 3 _, .object 4 _, .scalar 1 0 _, .scalar 1 1 _]) &&
        shape cfg 0 3 && (cfg.fieldInfo matches #[.scalar 1 0 _, .scalar 1 1 _, .scalar 1 2 _]) &&
        shape child 3 0 && (child.fieldInfo matches #[.object 0 _, .object 1 _, .object 2 _]) &&
        shape pair 2 0 && (pair.fieldInfo matches #[.object 0 _, .object 1 _]) do throw <| IO.userError "unexpected process record layout"
    for (n, i) in [(`piped, 0), (`inherit, 1), (`null, 2)] do
      let some layout := ctorLayoutExt.find? env (p ++ `IO.Process.Stdio ++ n) | throw <| IO.userError s!"missing process stream mode {n}"
      unless layout.ctorInfo.cidx == i && layout.fieldInfo.isEmpty do throw <| IO.userError s!"unexpected process stream mode {n}"

private def checkMetadata (source strict : Environment) : IO Unit := do
  for (env, p) in [(source, Name.anonymous), (strict, `Omega)] do
    let native := p.isAnonymous
    let ctor := fun (n : Name) => do
      let some l := ctorLayoutExt.find? env (p ++ n) | throw <| IO.userError s!"missing metadata layout {p ++ n}"
      pure l
    let time ← ctor `IO.FS.SystemTime.mk
    let metadata ← ctor `IO.FS.Metadata.mk
    let timeFields := if native then time.fieldInfo matches #[.object 0 _, .scalar 4 0 _]
      else time.fieldInfo matches #[.object 0 _, .object 1 _]
    let fileFields := if native then metadata.fieldInfo matches #[.object 0 _, .object 1 _, .scalar 8 0 _, .scalar 1 16 _, .scalar 8 8 _]
      else metadata.fieldInfo matches #[.object 0 _, .object 1 _, .object 2 _, .scalar 1 0 _, .object 3 _]
    unless timeFields && fileFields && time.ctorInfo.cidx == 0 && time.ctorInfo.usize == 0 &&
        time.ctorInfo.size == (if native then 1 else 2) && time.ctorInfo.ssize == (if native then 4 else 0) &&
        metadata.ctorInfo.cidx == 0 && metadata.ctorInfo.usize == 0 &&
        metadata.ctorInfo.size == (if native then 2 else 4) && metadata.ctorInfo.ssize == (if native then 17 else 1) do
      throw <| IO.userError "unexpected filesystem time or metadata layout"
    for (name, i) in [(`dir, 0), (`file, 1), (`symlink, 2), (`other, 3)] do
      let kind ← ctor (`IO.FS.FileType ++ name)
      unless kind.ctorInfo.cidx == i && kind.fieldInfo.isEmpty do throw <| IO.userError "unexpected filesystem type index"
  for (ctor, i) in [(`Omega.Int.ofNat, 0), (`Omega.Int.negSucc, 1)] do
    let some l := ctorLayoutExt.find? strict ctor | throw <| IO.userError s!"missing {ctor}"
    unless l.ctorInfo.cidx == i && l.ctorInfo.size == 1 && l.ctorInfo.ssize == 0 &&
        l.ctorInfo.usize == 0 && (l.fieldInfo matches #[.object 0 _]) do throw <| IO.userError "unexpected strict timestamp integer"

public unsafe def main (args : List String) : IO Unit := do
  let (ir, args) := if args.head? == some "--interpreter" then (true, args.drop 1) else (false, args)
  let [lib, file] := args | throw <| IO.userError "expected strict library and C output"
  let source ← importModules #[{module := `Init.System.IO}] {}
  searchPathRef.set [lib]
  let owner := `OmegaInit.System.IO
  let imports := #[{module := owner, importAll := true : Import}]
  let env ← importModules imports {}
  let roots := (entries ++ reads ++ bufferOperations).filter fun (n, _, _) => env.contains (InitKernelPort.portName n)
  if roots.isEmpty then return
  let fs := roots.any fun (n, _, _) => n != `IO.getEnv
  let handles := roots.any fun (n, _, _) => `IO.FS.Handle |>.isPrefixOf n
  let readDir := roots.any fun (n, _, _) => n == `System.FilePath.readDir
  let getters := [`IO.getStdin, `IO.getStdout, `IO.getStderr]
  let setters := [`IO.setStdin, `IO.setStdout, `IO.setStderr]
  let streams := roots.any fun (n, _, _) => (getters ++ setters).contains n
  let buffers := bufferOperations.any fun op => env.contains (InitKernelPort.portName op.1)
  let processes := roots.any fun (n, _, _) => n == `IO.Process.spawn || (`IO.Process.Child).isPrefixOf n
  let metadata := roots.any fun (n, _, _) => [`System.FilePath.metadata, `System.FilePath.symlinkMetadata].contains n
  let extraFields := (if fs then [`Omega.UInt32, `Omega.System.FilePath] else []) ++
    (if metadata then [`Omega.UInt64] else []) ++
    (if roots.any (fun (n, _, _) => n == `IO.FS.Handle.read || n == `IO.getRandomBytes) then [`Omega.USize] else [])
  if !ir then
    for n in [`Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.Array, `Omega.ByteArray, `Omega.String] ++ extraFields ++ [`Omega.Option, `Omega.List, `Omega.ST.Out] ++ (if fs then [`Omega.EST.Out, `Omega.IO.Error] else []) ++
        (if metadata then [`Omega.IO.FS.SystemTime, `Omega.IO.FS.Metadata, `Omega.IO.FS.FileType, `Omega.Int] else []) ++
        (if streams then [`Omega.IO.FS.Stream] else []) ++
        (if buffers then [`Omega.IO.FS.Stream.Buffer] else []) ++
        (if processes then [`Omega.Prod, `Omega.IO.Process.Stdio, `Omega.IO.Process.StdioConfig, `Omega.IO.Process.SpawnArgs, `Omega.IO.Process.Child] else []) ++
        (if roots.any (fun (n, _, _) => n == `IO.FS.createTempFile) then [`Omega.Prod] else []) ++
        (if readDir then [`Omega.IO.FS.DirEntry] else []) ++ (if handles then [`Omega.IO.FS.Mode] else []) do
      let env ← importModules imports {}
      if (monoTypeExt.find? env n).isSome then continue
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing owner for {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  checkStrictString env
  for n in extraFields do checkErasedField env n
  for (n, tag, fields) in [(`Omega.Option.none, 0, 0), (`Omega.Option.some, 1, 1), (`Omega.ST.Out.mk, 0, 2)] ++
      (if fs then [(`Omega.EST.Out.ok, 0, 2), (`Omega.EST.Out.error, 1, 2)] else []) do
    let some l := ctorLayoutExt.find? env n | throw <| IO.userError s!"missing {n} layout"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == fields && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
        l.fieldInfo.size == fields do throw <| IO.userError s!"unexpected {n} layout"
    for f in l.fieldInfo, i in [:fields] do
      let .object j _ := f | throw <| IO.userError s!"expected boxed {n} field"
      unless i == j do throw <| IO.userError s!"unexpected {n} field position"
  if streams then
    for (e, n) in [(source, `IO.FS.Stream.mk), (env, `Omega.IO.FS.Stream.mk)] do
      let some l := ctorLayoutExt.find? e n | throw <| IO.userError s!"missing stream constructor {n}"
      unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 6 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
          (l.fieldInfo matches #[.object 0 _, .object 1 _, .object 2 _, .object 3 _, .object 4 _, .object 5 _]) do
        throw <| IO.userError s!"unexpected stream callback layout {n}"
  if processes then checkProcesses source env
  if roots.any (fun (n, _, _) => n == `IO.FS.createTempFile) then
    for (e, pair) in [(source, `Prod.mk), (env, `Omega.Prod.mk)] do
      let some l := ctorLayoutExt.find? e pair | throw <| IO.userError s!"missing temporary file pair {pair}"
      unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 2 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
          (l.fieldInfo matches #[.object 0 _, .object 1 _]) do throw <| IO.userError s!"unexpected temporary file pair {pair}"
  if metadata then checkMetadata source env
  if handles then
    for (n, tag) in [(`read, 0), (`write, 1), (`writeNew, 2), (`readWrite, 3), (`append, 4)] do
      for (e, mode) in [(source, `IO.FS.Mode), (env, `Omega.IO.FS.Mode)] do
        let some layout := ctorLayoutExt.find? e (mode ++ n) | throw <| IO.userError s!"missing mode {mode ++ n}"
        unless layout.ctorInfo.cidx == tag && layout.fieldInfo.isEmpty do throw <| IO.userError s!"unexpected file mode {n}"
  if readDir then
    for (e, ctor) in [(env, `Omega.IO.FS.DirEntry.mk), (source, `IO.FS.DirEntry.mk)] do
      let some l := ctorLayoutExt.find? e ctor | throw <| IO.userError s!"missing layout for {ctor}"
      let #[.object 0 _, .object 1 _] := l.fieldInfo | throw <| IO.userError s!"invalid directory entry fields in {ctor}"
      unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 2 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do
        throw <| IO.userError s!"incorrect layout for {ctor}"
  let ctx ← localEnv env owner (roots.map fun (n, _, _) => InitKernelPort.portName n)
  let compiled ← compile ctx do
    for (n, _, symbol) in roots do
      let strict := InitKernelPort.portName n
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := strict) e (strict, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[strict] {}
  for (n, upstream, symbol) in roots do
    if readFunctions.any (·.1 == n) then continue
    if let some op := OmegaChecks.InitPort.BufferReference.operations.find? (fun op => n == OmegaChecks.InitPort.BufferReference.support op) then
      let strict := InitKernelPort.portName n
      let some (some ref) := impureTrivialStructureInfoExt.find? compiled `Omega.ST.Ref | throw <| IO.userError "missing strict reference layout"
      unless ref.numParams == 2 && ref.fieldIdx == 0 do throw <| IO.userError "unexpected strict reference layout"
      let implicitArgs := #[(IR.IRType.erased, false), (.erased, false)]
      let action := #[(IR.IRType.tobject, true), (.void, false)]
      if op == `ST.Prim.Ref.get then
        verify source op (implicitArgs ++ action) .tobject "lean_st_ref_get"
        verify compiled strict #[(.tobject, true), (.tobject, false)] .object symbol
      else
        verify source `ST.Prim.Ref.take (implicitArgs ++ action) .tobject "lean_st_ref_take"
        verify source `ST.Prim.Ref.put (implicitArgs ++ #[(.tobject, true), (.tobject, false), (.void, false)]) .tagged "lean_st_ref_put"
        let args := if op == `ST.Prim.Ref.modifyGet then #[(IR.IRType.erased, false)] else #[]
        verify compiled strict (args ++ #[(.tobject, false), (.object, false), (.tobject, false)]) .object symbol
      continue
    if (getters ++ setters).contains n then
      let args := if setters.contains n then #[(IR.IRType.object, false)] else #[]
      verify source n (args ++ #[(.void, false)]) .object upstream
      verify compiled (`Omega ++ n) (args ++ #[(.tobject, false)]) .object symbol
      continue
    if n == `IO.Process.spawn then
      verify source n #[(.object, false), (.void, false)] .object upstream
      verify compiled (`Omega ++ n) #[(.object, false), (.tobject, false)] .object symbol
      continue
    if `IO.Process.Child |>.isPrefixOf n then
      let pid := n == `IO.Process.Child.pid
      let child := #[(IR.IRType.object, true), (.object, !(pid || n == `IO.Process.Child.takeStdin))]
      verify source n (child ++ (if pid then #[] else #[(.void, false)])) (if pid then .uint32 else .object) upstream
      verify compiled (`Omega ++ n) (child ++ (if pid then #[] else #[(.tobject, false)])) (if pid then .tobject else .object) symbol
      continue
    if [`IO.Process.exit, `IO.Process.forceExit].contains n then
      verify source n #[(.erased, false), (.uint8, false), (.void, false)] .object upstream
      verify compiled (`Omega ++ n) #[(.erased, false), (.tobject, false), (.tobject, false)] .object symbol
      continue
    if n == `IO.getRandomBytes then
      verify source n #[(.usize, false), (.void, false)] .object upstream
      verify compiled (`Omega ++ n) #[(.tobject, false), (.tobject, false)] .object symbol
      continue
    if n == `IO.Prim.setAccessRights then
      verify source n #[(.object, true), (.uint32, false), (.void, false)] .object upstream
      verify compiled (`Omega ++ n) #[(.tobject, true), (.tobject, false), (.tobject, false)] .object symbol
      continue
    if `IO.FS.Handle |>.isPrefixOf n then
      let path := n == `IO.FS.Handle.mk
      let obj := if path then IR.IRType.object else .tobject
      let extra : Array (IR.IRType × Bool) :=
        if [`IO.FS.Handle.mk, `IO.FS.Handle.lock, `IO.FS.Handle.tryLock].contains n then #[(.uint8, false)]
        else if n == `IO.FS.Handle.read then #[(.usize, false)]
        else if [`IO.FS.Handle.write, `IO.FS.Handle.putStr].contains n then #[(.object, true)] else #[]
      verify source n (#[(obj, true)] ++ extra ++ #[(.void, false)])
        (if n == `IO.FS.Handle.isTty then .uint8 else .object) upstream
      let strict := extra.map fun (t, borrow) => (if t == .object || t == .usize then .tobject else t, borrow)
      verify compiled (`Omega ++ n) (#[((.tobject : IR.IRType), true)] ++ strict ++ #[(.tobject, false)]) .object symbol
      continue
    let count := if [`IO.FS.rename, `IO.FS.hardLink].contains n then 2
      else if [`IO.FS.createTempFile, `IO.FS.createTempDir, `IO.appPath, `IO.currentDir, `IO.Process.getCurrentDir].contains n then 0 else 1
    let borrow := n != `IO.FS.realPath
    verify source n (Array.replicate count (.object, borrow) ++ #[(.void, false)])
      (if n == `IO.getEnv then .tobject else .object) upstream
    verify compiled (`Omega ++ n) (Array.replicate count (.tobject, borrow) ++ #[(.tobject, false)]) .object symbol
  unless ir do writeCode lib owner compiled codeExtensions
  let idx := (env.getModuleIdx? owner).get!
  let existing := (externAttr.ext.getModuleEntries env idx).any fun (name, _) =>
    !(roots.any fun (n, _, _) => name == InitKernelPort.portName n)
  let nativeOwner := if ir || existing then `StrictPathIO else owner
  let usesPinnedReaders := roots.any fun (n, _, _) => readFunctions.any (·.1 == n)
  emitBridge compiled nativeOwner none file
  if usesPinnedReaders then
    let init := mkModuleInitializationFunctionName (phases := .runtime) nativeOwner compiled.getModulePackage?
    let upstream := mkModuleInitializationFunctionName (phases := .runtime) `Init.System.IO
      (source.getModuleIdx? `Init.System.IO >>= source.getModulePackageByIdx?)
    let text ← IO.FS.readFile file
    let decl := s!"LEAN_EXPORT lean_object* {init}(uint8_t builtin) \{"
    let [before, after] := text.splitOn decl | throw <| IO.userError s!"missing native path initializer {init}"
    IO.FS.writeFile file (before ++ s!"extern lean_obj_res {upstream}(uint8_t);\n" ++ decl ++
      s!"\nlean_obj_res source = {upstream}(builtin);\nif (lean_io_result_is_error(source)) return source;\nlean_dec(source);\n" ++ after)
  let runtime ← IO.FS.readFile "src/OmegaChecks/InitPort/path_io_runtime.c"
  IO.FS.withFile file .append fun h => do
    if fs then h.putStrLn "#define OMEGA_PATH_IO_FS"
    h.putStr runtime
    if fs then
      h.putStr (← convertError source env false)
      h.putStr (← convertError source env true)
    for (name, symbol, decoder) in readFunctions do
      if roots.any (·.1 == name) then h.putStr (← readWrapper source compiled name symbol decoder)
