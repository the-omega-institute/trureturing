module
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

private def entries := #[
  (`System.FilePath.metadata, "lean_io_metadata", "omega_io_metadata"),
  (`System.FilePath.symlinkMetadata, "lean_io_symlink_metadata", "omega_io_symlink_metadata"),
  (`IO.getRandomBytes, "lean_io_get_random_bytes", "omega_io_random_bytes"),
  (`IO.Prim.setAccessRights, "lean_chmod", "omega_io_set_access_rights"),
  (`IO.getEnv, "lean_io_getenv", "omega_io_get_env"),
  (`IO.FS.createDir, "lean_io_create_dir", "omega_io_create_dir"),
  (`IO.FS.removeDir, "lean_io_remove_dir", "omega_io_remove_dir"),
  (`IO.FS.removeFile, "lean_io_remove_file", "omega_io_remove_file"),
  (`IO.FS.rename, "lean_io_rename", "omega_io_rename"),
  (`IO.FS.hardLink, "lean_io_hard_link", "omega_io_hard_link"),
  (`IO.FS.realPath, "lean_io_realpath", "omega_io_real_path"),
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

private def decodeError (source strict : Environment) : IO String := do
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
    if dest.fieldInfo.isEmpty then
      cases := cases ++ s!"case {tag}: return lean_box({tag});\n"
      continue
    cases := cases ++ s!"case {tag}: \{ lean_object *out = lean_alloc_ctor({tag}, {dest.ctorInfo.size}, 0);\n"
    let mut ty := c.type
    for f in src.fieldInfo, g in dest.fieldInfo do
      let .forallE _ dom body _ := ty | throw <| IO.userError s!"unexpected type of {n}"
      let .object toIdx _ := g | throw <| IO.userError s!"expected boxed strict field of {n}"
      let get ← match f with
        | .object idx _ =>
          let decode ← if dom == mkConst `String then pure "omega_string_from_lean"
            else if dom == mkApp (mkConst `Option [.zero]) (mkConst `String) then pure "strict_option_string"
            else throw <| IO.userError s!"unrecognized object in {n}: {dom}"
          pure s!"{decode}(lean_ctor_get(error, {idx}))"
        | .scalar 4 offset _ =>
          unless dom == mkConst `UInt32 do throw <| IO.userError s!"unexpected scalar in {n}"
          pure s!"omega_nat_from_uint64(lean_ctor_get_uint32(error, {src.ctorInfo.size} * sizeof(void*) + {offset}))"
        | _ => throw <| IO.userError s!"unsupported IO.Error field layout in {n}"
      cases := cases ++ s!"lean_ctor_set(out, {toIdx}, {get});\n"
      ty := body
    cases := cases ++ "return out; }\n"
  return "\nstatic lean_obj_res strict_io_error(b_lean_obj_arg error) {\nswitch (lean_obj_tag(error)) {\n" ++
    cases ++ "default: lean_internal_panic_unreachable();\n}\n}\n"

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
  let roots := entries.filter fun (n, _, _) => env.contains (`Omega ++ n)
  if roots.isEmpty then return
  let fs := roots.any fun (n, _, _) => n != `IO.getEnv
  let handles := roots.any fun (n, _, _) => `IO.FS.Handle |>.isPrefixOf n
  let readDir := roots.any fun (n, _, _) => n == `System.FilePath.readDir
  let metadata := roots.any fun (n, _, _) => [`System.FilePath.metadata, `System.FilePath.symlinkMetadata].contains n
  let dicts := [`Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.Array, `Omega.ByteArray, `Omega.String] ++
    (if fs then [`Omega.UInt32, `Omega.System.FilePath] else []) ++
    (if metadata then [`Omega.UInt64] else []) ++
    (if roots.any (fun (n, _, _) => n == `IO.FS.Handle.read || n == `IO.getRandomBytes) then [`Omega.USize] else [])
  if !ir then
    for n in dicts ++ [`Omega.Option, `Omega.List, `Omega.ST.Out] ++ (if fs then [`Omega.EST.Out, `Omega.IO.Error] else []) ++
        (if metadata then [`Omega.IO.FS.SystemTime, `Omega.IO.FS.Metadata, `Omega.IO.FS.FileType, `Omega.Int] else []) ++
        (if readDir then [`Omega.IO.FS.DirEntry] else []) ++ (if handles then [`Omega.IO.FS.Mode] else []) do
      let env ← importModules imports {}
      if (monoTypeExt.find? env n).isSome then continue
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing owner for {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  for n in dicts do
    let some (some field) := impureTrivialStructureInfoExt.find? env n | throw <| IO.userError s!"expected single data field in {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected data field in {n}"
  checkNativeNat env
  for (n, tag, fields) in [(`Omega.List.nil, 0, 0), (`Omega.List.cons, 1, 2), (`Omega.Option.none, 0, 0),
      (`Omega.Option.some, 1, 1), (`Omega.ST.Out.mk, 0, 2)] ++
      (if fs then [(`Omega.EST.Out.ok, 0, 2), (`Omega.EST.Out.error, 1, 2)] else []) do
    let some l := ctorLayoutExt.find? env n | throw <| IO.userError s!"missing {n} layout"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == fields && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
        l.fieldInfo.size == fields do throw <| IO.userError s!"unexpected {n} layout"
    for f in l.fieldInfo, i in [:fields] do
      let .object j _ := f | throw <| IO.userError s!"expected boxed {n} field"
      unless i == j do throw <| IO.userError s!"unexpected {n} field position"
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
  let ctx ← localEnv env owner (roots.map fun (n, _, _) => `Omega ++ n)
  let compiled ← compile ctx do
    for (n, _, symbol) in roots do
      let strict := `Omega ++ n
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := strict) e (strict, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[strict] {}
  for (n, upstream, symbol) in roots do
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
      else if [`IO.FS.createTempDir, `IO.appPath, `IO.currentDir, `IO.Process.getCurrentDir].contains n then 0 else 1
    let borrow := n != `IO.FS.realPath
    verify source n (Array.replicate count (.object, borrow) ++ #[(.void, false)])
      (if n == `IO.getEnv then .tobject else .object) upstream
    verify compiled (`Omega ++ n) (Array.replicate count (.tobject, borrow) ++ #[(.tobject, false)]) .object symbol
  unless ir do writeCode lib owner compiled codeExtensions
  let idx := (env.getModuleIdx? owner).get!
  let existing := (externAttr.ext.getModuleEntries env idx).any fun (name, _) =>
    !(roots.any fun (n, _, _) => name == `Omega ++ n)
  let nativeOwner := if ir || existing then `StrictPathIO else owner
  emitBridge compiled nativeOwner none file
  let runtime ← IO.FS.readFile "src/OmegaChecks/InitPort/path_io_runtime.c"
  IO.FS.withFile file .append fun h => do
    if fs then h.putStrLn "#define OMEGA_PATH_IO_FS"
    h.putStr runtime
    if fs then h.putStr (← decodeError source env)
