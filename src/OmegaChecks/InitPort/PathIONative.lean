module
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

private def entries := #[(`IO.getEnv, "lean_io_getenv", "omega_io_get_env"),
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
  (`System.FilePath.readDir, "lean_io_read_dir", "omega_io_read_dir")]

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
  let readDir := roots.any fun (n, _, _) => n == `System.FilePath.readDir
  let dicts := [`Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.Array, `Omega.ByteArray, `Omega.String] ++
    (if fs then [`Omega.UInt32, `Omega.System.FilePath] else [])
  if !ir then
    for n in dicts ++ [`Omega.Option, `Omega.List, `Omega.ST.Out] ++ (if fs then [`Omega.EST.Out, `Omega.IO.Error] else []) ++
        (if readDir then [`Omega.IO.FS.DirEntry] else []) do
      let env ← importModules imports {}
      if (monoTypeExt.find? env n).isSome then continue
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing owner for {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  for n in dicts do
    let some (some field) := impureTrivialStructureInfoExt.find? env n | throw <| IO.userError s!"expected single data field in {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected data field in {n}"
  checkPriorityLayout env
  for (n, tag, fields) in [(`Omega.List.nil, 0, 0), (`Omega.List.cons, 1, 2), (`Omega.Option.none, 0, 0),
      (`Omega.Option.some, 1, 1), (`Omega.ST.Out.mk, 0, 2)] ++
      (if fs then [(`Omega.EST.Out.ok, 0, 2), (`Omega.EST.Out.error, 1, 2)] else []) do
    let some l := ctorLayoutExt.find? env n | throw <| IO.userError s!"missing {n} layout"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == fields && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 &&
        l.fieldInfo.size == fields do throw <| IO.userError s!"unexpected {n} layout"
    for f in l.fieldInfo, i in [:fields] do
      let .object j _ := f | throw <| IO.userError s!"expected boxed {n} field"
      unless i == j do throw <| IO.userError s!"unexpected {n} field position"
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
