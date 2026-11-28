module
public import Lean
public import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.UnsafeRuntime
import OmegaChecks.InitPort.WordNative
import OmegaChecks.InitPort.FloatArrayNative
import OmegaChecks.InitPort.BufferReference
import OmegaChecks.InitPort.StateRunner
import OmegaChecks.InitPort.ReferenceModify
import OmegaChecks.InitPort.RandomState
import Lean.Elab.ParseImportsFast
import Lean.Compiler.LCNF.SpecInfo
import all Lean.Structure

public section

open Lean

namespace OmegaChecks.ModuleSurface

/-- Restore name resolution from the alias entries of an isolated compiled environment. -/
def withImportedAliases (env : Environment) : Environment := Id.run do
  let mut aliases : AliasState := {}
  for idx in [:env.header.modules.size] do
    aliases := (aliasExtension.getModuleEntries env idx).foldl addAliasEntry aliases
  return aliasExtension.setState env aliases.switch

def isBasis (owner : Name) : Bool :=
  owner.getRoot == `OmegaInit || owner.getRoot == `OmegaMathlib

private def counterpart (owner : Name) : Name :=
  owner.replacePrefix owner.getRoot (if owner.getRoot == `OmegaInit then `Init else `Mathlib)

/-- Include modules independently of the presence of local mathematical declarations. -/
def officialModules (strict : Environment) (lib : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for owner in strict.allImportedModuleNames do
    if !isBasis owner || owner == `OmegaMathlib then continue
    let official := counterpart owner
    let file := if owner.getRoot == `OmegaInit then modToFilePath lib official "olean"
      else modToFilePath ".lake/packages/mathlib" official "lean"
    unless ← file.pathExists do
      throw <| IO.userError s!"no official module {official} for {owner}"
    modules := modules.push official
  return modules

/-- The modules exposed when a consumer imports this root alone. -/
def publicClosure (env : Environment) (root : Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  while let some owner := pending.back? do
    pending := pending.pop
    unless seen.contains owner do
      seen := seen.insert owner
      let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
      for dep in env.header.moduleData[idx]!.imports do
        if dep.isExported then pending := pending.push dep.module
  return seen

/-- Read the Mathlib import index without requiring a full Mathlib build. Init's
compiled umbrella is shipped with Lean and its public imports can be followed directly. -/
private def checkUmbrella (env : Environment) (port : Name) (idx : ModuleIdx) : IO Unit := do
  let exports ← if port == `OmegaMathlib then do
    let path := ".lake/packages/mathlib/Mathlib.lean"
    let header ← Lean.parseImports' (← IO.FS.readFile path) path
    pure <| NameSet.ofList ((header.imports.filter (·.isExported)).map (·.module)).toList
  else do
    let reference ← importModules #[{module := `Init}] {} (level := .exported)
    publicClosure reference `Init
  let data := env.header.moduleData[idx]!
  unless data.constNames.isEmpty do
    throw <| IO.userError s!"the {port} umbrella must contain only public imports of checked ports"
  for dep in data.imports do
    unless dep.isExported && !dep.importAll && dep.module.getRoot == port && exports.contains (counterpart dep.module) do
      throw <| IO.userError s!"unmatched {port} umbrella import {dep.module}"
  unless (aliasExtension.getModuleEntries env idx).isEmpty do
    throw <| IO.userError s!"unmatched export alias in the {port} umbrella"
  unless (classExtension.getModuleEntries env idx).isEmpty do
    throw <| IO.userError s!"unmatched class registration in the {port} umbrella"

/-- The opaque .olean payload can be decoded only by its registered extension. Unknown
extension kinds therefore require a correspondence before a port can expose them. -/
private def supportedExtension (name : Name) : Bool :=
  [-- Compiled interface registrations checked by the port and kernel-interface audits.
   externAttr.ext.name, aliasExtension.name, classExtension.name, Meta.instanceExtension.ext.name, Meta.defaultInstanceExtension.name,
   Meta.simpExtension.ext.name, auxRecExt.name, noConfusionExt.name, Meta.completionBlackListExt.name,
   protectedExt.name, matchPatternAttr.ext.name, Elab.Term.elabAsElim.ext.name, neverExtractAttr.ext.name, reducibilityCoreExt.name,
   privateToUserName structureExt.name, projectionFnInfoExt.name, Meta.Match.Extension.extension.name,
   -- Module provenance, compiled representation and kernel bookkeeping in the pinned toolchain.
   `Lean.namespacesExt, `Lean.noncomputableExt, `Lean.Compiler.inlineAttrs, `Lean.exportedAxiomsExt,
   `Lean.privateConstKindsExt, `Lean.modPkgExt, `Lean.IR.declMapExt, `Lean.Compiler.LCNF.baseExt,
   `Lean.Compiler.LCNF.monoExt, `Lean.Compiler.LCNF.impureSigExt, `Lean.Compiler.LCNF.trivialStructureInfoExt,
   Compiler.LCNF.specExtension.name, Compiler.implementedByAttr.ext.name,
   `Lean.Compiler.LCNF.monoTypeExt, `Lean.Compiler.LCNF.impureTypeExt,
   `Lean.Compiler.LCNF.impureTrivialStructureInfoExt, `Lean.Compiler.LCNF.ctorLayoutExt,
   `Lean.indirectModUseExt, `Lean.deprecatedModuleExt].contains (privateToUserName name)

/-- The compiler may specialize a private helper inside a publicly callable definition. -/
private def checkSpecializations (env : Environment) (owner : Name) : IO Unit := do
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing native owner {owner}"
  let specs := Compiler.LCNF.specExtension.getModuleEntries env idx (level := .private)
  unless specs.isEmpty do
    let base := Compiler.LCNF.baseExt.getModuleEntries env idx (level := .private)
    for entry in specs do
      let some decl := base.find? (·.name == entry.declName)
        | throw <| IO.userError s!"no compiled signature for specialization of {entry.declName} in {owner}"
      unless env.getModuleIdxFor? entry.declName == some idx &&
          entry.paramsInfo.size == decl.params.size &&
          entry.paramsInfo.any Compiler.LCNF.SpecParamInfo.causesSpecialization do
        throw <| IO.userError s!"invalid parameter specialization for {entry.declName} in {owner}"

private def sameMatcherInfo (a b : Meta.MatcherInfo) : Bool :=
  a.numParams == b.numParams && a.numDiscrs == b.numDiscrs && a.altInfos == b.altInfos &&
  a.uElimPos? == b.uElimPos? && a.discrInfos.map (·.hName?) == b.discrInfos.map (·.hName?) &&
  a.overlaps.map.size == b.overlaps.map.size &&
  a.overlaps.map.all fun i set => (b.overlaps.map[i]?).any fun other => set.toList == other.toList

private def checkMatchers (strict full visible pinned : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  let ext := Meta.Match.Extension.extension
  let entries := ext.getModuleEntries strict idx
  let some origIdx := visible.getModuleIdx? (counterpart owner)
    | throw <| IO.userError s!"missing official matcher owner for {owner}"
  let original := ext.getModuleEntries visible origIdx
  -- The upstream matcher extension exports identical entries to ordinary and server consumers.
  let server := ext.getModuleEntries strict idx (level := .server)
  unless entries.size == server.size && (entries.zip server).all (fun (a, b) =>
      a.name == b.name && sameMatcherInfo a.info b.info) do
    throw <| IO.userError s!"inconsistent server matcher registrations in {owner}"
  for entry in entries do
    let upstream := InitKernelPort.originalName entry.name
    unless InitKernelPort.portName upstream == entry.name &&
        strict.getModuleIdxFor? entry.name == some idx &&
        visible.getModuleIdxFor? upstream == some origIdx &&
        original.any (fun e => e.name == upstream && sameMatcherInfo entry.info e.info) &&
        InitKernelPort.exactDefinition pinned full.toKernelEnv upstream do
      throw <| IO.userError s!"unmatched matcher registration for {entry.name} in {owner}"

  for constant in strict.header.moduleData[idx]!.constants do
    unless constant.name == Meta.mkSmartUnfoldingNameFor constant.name.getPrefix do continue
    let upstream := InitKernelPort.originalName constant.name
    unless visible.getModuleIdxFor? upstream == some origIdx &&
        constant.name.getPrefix == InitKernelPort.portName upstream.getPrefix &&
        InitKernelPort.exactDefinition pinned full.toKernelEnv upstream &&
        InitKernelPort.exactDefinition pinned full.toKernelEnv upstream.getPrefix do
      throw <| IO.userError s!"unmatched smart unfolding definition for {constant.name} in {owner}"
    let some (.defnInfo helper) := strict.find? constant.name | continue
    if let some missing := helper.value.find? fun expr => Id.run do
        let some app := Meta.smartUnfoldingMatch? expr | return false
        let some matcher := app.getAppFn.constName? | return true
        let some home := strict.getModuleIdxFor? matcher | return true
        return !(ext.getModuleEntries strict home).any (·.name == matcher) then
      throw <| IO.userError s!"unregistered smart unfolding matcher in {constant.name}: {missing}"

private def checkElaboration (env full : Environment) (reference? : Option Environment)
    (owner : Name) (idx : ModuleIdx) : IO Unit := do
  for (n, data) in externAttr.ext.getModuleEntries env idx do
    let (expectedOwner, symbol) ← match n with
      | `Omega.ShareCommon.Object.eq | `Omega.ShareCommon.Object.hash => do
        let original := InitKernelPort.originalName n
        let some pinned := InitPort.UnsafeRuntime.observerSymbol? full `Init.ShareCommon original true
          | throw <| IO.userError s!"invalid object observation ABI for {n}"
        if let some ref := reference? then
          unless InitPort.UnsafeRuntime.observerSymbol? ref `Init.ShareCommon original false == some pinned do
            throw <| IO.userError s!"invalid pinned object observation ABI for {original}"
        let symbol := if original == `ShareCommon.Object.hash then "omega_share_common_object_hash" else pinned
        pure (`OmegaInit.ShareCommon, symbol)
      | `Omega.ShareCommon.StateFactory.mk => pure (`OmegaInit.ShareCommon, "omega_share_common_factory_mk")
      | `Omega.ShareCommon.State.mk => pure (`OmegaInit.ShareCommon, "l_ShareCommon_mkStateImpl")
      | `Omega.ShareCommon.State.shareCommon => pure (`OmegaInit.ShareCommon, "lean_state_sharecommon")
      | `Omega.EST.Out.ctorElim => pure (`OmegaInit.System.ST, "omega_est_out_elim")
      | `Omega.IO.FS.hardLink => pure (`OmegaInit.System.IO, "omega_io_hard_link")
      | `Omega.IO.FS.realPath => pure (`OmegaInit.System.IO, "omega_io_real_path")
      | `Omega.IO.FS.createTempFile => pure (`OmegaInit.System.IO, "omega_io_create_temp_file")
      | `Omega.IO.FS.createTempDir => pure (`OmegaInit.System.IO, "omega_io_create_temp_dir")
      | `Omega.IO.appPath => pure (`OmegaInit.System.IO, "omega_io_app_path")
      | `Omega.IO.currentDir => pure (`OmegaInit.System.IO, "omega_io_current_dir")
      | `Omega.IO.Process.getCurrentDir => pure (`OmegaInit.System.IO, "omega_io_process_get_current_dir")
      | `Omega.IO.Process.setCurrentDir => pure (`OmegaInit.System.IO, "omega_io_process_set_current_dir")
      | `Omega.System.FilePath.readDir => pure (`OmegaInit.System.IO, "omega_io_read_dir")
      | `Omega.System.FilePath.metadata => pure (`OmegaInit.System.IO, "omega_io_metadata")
      | `Omega.System.FilePath.symlinkMetadata => pure (`OmegaInit.System.IO, "omega_io_symlink_metadata")
      | `Omega.IO.FS.readFile => pure (`OmegaInit.System.IO, "omega_io_read_file")
      | `Omega.IO.FS.readBinFile => pure (`OmegaInit.System.IO, "omega_io_read_bin_file")
      | `Omega.IO.FS.lines => pure (`OmegaInit.System.IO, "omega_io_read_lines")
      | `Omega.IO.FS.Handle.lines => pure (`OmegaInit.System.IO, "omega_io_handle_lines")
      | `Omega.IO.FS.Handle.readToEnd => pure (`OmegaInit.System.IO, "omega_io_handle_read_to_end")
      | `Omega.IO.FS.Handle.readBinToEnd => pure (`OmegaInit.System.IO, "omega_io_handle_read_bin_to_end")
      | `Omega.IO.FS.Handle.readBinToEndInto => pure (`OmegaInit.System.IO, "omega_io_handle_read_bin_into")
      | `Omega.IO.setStdin => pure (`OmegaInit.System.IO, "omega_io_set_stdin")
      | `Omega.IO.setStdout => pure (`OmegaInit.System.IO, "omega_io_set_stdout")
      | `Omega.IO.setStderr => pure (`OmegaInit.System.IO, "omega_io_set_stderr")
      | `Omega.IO.getStdin => pure (`OmegaInit.System.IO, "omega_io_get_stdin")
      | `Omega.IO.getStdout => pure (`OmegaInit.System.IO, "omega_io_get_stdout")
      | `Omega.IO.getStderr => pure (`OmegaInit.System.IO, "omega_io_get_stderr")
      | `Omega.IO.Process.spawn => pure (`OmegaInit.System.IO, "omega_io_process_spawn")
      | `Omega.IO.Process.Child.wait => pure (`OmegaInit.System.IO, "omega_io_process_child_wait")
      | `Omega.IO.Process.Child.tryWait => pure (`OmegaInit.System.IO, "omega_io_process_child_try_wait")
      | `Omega.IO.Process.Child.kill => pure (`OmegaInit.System.IO, "omega_io_process_child_kill")
      | `Omega.IO.Process.Child.takeStdin => pure (`OmegaInit.System.IO, "omega_io_process_child_take_stdin")
      | `Omega.IO.Process.Child.pid => pure (`OmegaInit.System.IO, "omega_io_process_child_pid")
      | `Omega.IO.Process.exit => pure (`OmegaInit.System.IO, "omega_io_exit")
      | `Omega.IO.Process.forceExit => pure (`OmegaInit.System.IO, "omega_io_force_exit")
      | `Omega.IO.getRandomBytes => pure (`OmegaInit.System.IO, "omega_io_random_bytes")
      | `Omega.IO.Prim.setAccessRights => pure (`OmegaInit.System.IO, "omega_io_set_access_rights")
      | `Omega.IO.FS.Handle.mk => pure (`OmegaInit.System.IO, "omega_io_handle_mk")
      | `Omega.IO.FS.Handle.lock => pure (`OmegaInit.System.IO, "omega_io_handle_lock")
      | `Omega.IO.FS.Handle.tryLock => pure (`OmegaInit.System.IO, "omega_io_handle_try_lock")
      | `Omega.IO.FS.Handle.unlock => pure (`OmegaInit.System.IO, "omega_io_handle_unlock")
      | `Omega.IO.FS.Handle.isTty => pure (`OmegaInit.System.IO, "omega_io_handle_is_tty")
      | `Omega.IO.FS.Handle.flush => pure (`OmegaInit.System.IO, "omega_io_handle_flush")
      | `Omega.IO.FS.Handle.rewind => pure (`OmegaInit.System.IO, "omega_io_handle_rewind")
      | `Omega.IO.FS.Handle.truncate => pure (`OmegaInit.System.IO, "omega_io_handle_truncate")
      | `Omega.IO.FS.Handle.read => pure (`OmegaInit.System.IO, "omega_io_handle_read")
      | `Omega.IO.FS.Handle.write => pure (`OmegaInit.System.IO, "omega_io_handle_write")
      | `Omega.IO.FS.Handle.getLine => pure (`OmegaInit.System.IO, "omega_io_handle_get_line")
      | `Omega.IO.FS.Handle.putStr => pure (`OmegaInit.System.IO, "omega_io_handle_put_str")
      | `Omega.IO.getEnv => pure (`OmegaInit.System.IO, "omega_io_get_env")
      | `Omega.IO.FS.createDir => pure (`OmegaInit.System.IO, "omega_io_create_dir")
      | `Omega.IO.FS.removeDir => pure (`OmegaInit.System.IO, "omega_io_remove_dir")
      | `Omega.IO.FS.removeFile => pure (`OmegaInit.System.IO, "omega_io_remove_file")
      | `Omega.IO.FS.rename => pure (`OmegaInit.System.IO, "omega_io_rename")
      | `Omega.Void.mk => pure (`OmegaInit.System.ST, "lean_void_mk")
      | `Nat.div => pure (`OmegaInit.Prelude, "lean_nat_div")
      | `Nat.mod => pure (`OmegaInit.Prelude, "lean_nat_mod")
      | `Nat.gcd => pure (`OmegaInit.Data.Nat.Gcd, "lean_nat_gcd")
      | `Nat.ble => pure (`OmegaInit.Prelude, "lean_nat_dec_le")
      | `Nat.beq => pure (`OmegaInit.Prelude, "lean_nat_dec_eq")
      | `Nat.add => pure (`OmegaInit.Prelude, "lean_nat_add")
      | `Nat.sub => pure (`OmegaInit.Prelude, "lean_nat_sub")
      | `Nat.mul => pure (`OmegaInit.Prelude, "lean_nat_mul")
      | `Nat.pow => pure (`OmegaInit.Prelude, "lean_nat_pow")
      | `Nat.decEq => pure (`OmegaInit.Prelude, "lean_nat_dec_eq")
      | `Omega.ST.Prim.Ref.put => do
        let args := #[(IR.IRType.erased, false), (.erased, false), (.tobject, true), (.tobject, false)]
        InitPort.NativeState.verify full n (args.push (.tobject, false)) .object "omega_st_ref_put"
        if let some ref := reference? then
          InitPort.NativeState.verify ref `ST.Prim.Ref.put (args.push (.void, false)) .tagged "lean_st_ref_put"
        pure (`OmegaInit.System.ST, "omega_st_ref_put")
      | `Omega.ST.Prim.Ref.swap => pure (`OmegaInit.System.ST, "omega_st_ref_swap")
      | `Omega.IO.rand => pure (`OmegaInit.Data.Random, "omega_io_rand")
      | `Omega.ST.Prim.Ref.modify => pure (`OmegaInit.System.ST, "omega_st_ref_modify")
      | `Omega.ST.Prim.Ref.set => pure (`OmegaInit.System.ST, "omega_st_ref_set")
      | `Omega.ST.Prim.Ref.ptrEq => pure (`OmegaInit.System.ST, "omega_st_ref_ptr_eq")
      | `Omega.ST.Prim.mkRef => pure (`OmegaInit.System.ST, "omega_st_mk_ref")
      | `Omega.Task.spawn => pure (`OmegaInit.Core, "omega_task_spawn")
      | `Omega.Task.map => pure (`OmegaInit.Core, "omega_task_map")
      | `Omega.Task.bind => pure (`OmegaInit.Core, "omega_task_bind")
      | `Task.pure => pure (`OmegaInit.Core, "lean_task_pure")
      | `Task.get => pure (`OmegaInit.Core, "lean_task_get_own")
      | `Omega.IO.Promise.resultD => pure (`OmegaInit.System.Promise, "omega_io_promise_result_d")
      | `Omega.IO.Promise.result? => pure (`OmegaInit.System.Promise, "lean_io_promise_result_opt")
      | `Omega.IO.asTask | `Omega.EIO.asTask => pure (`OmegaInit.System.IO, "omega_io_except_as_task")
      | `Omega.IO.mapTask | `Omega.EIO.mapTask => pure (`OmegaInit.System.IO, "omega_io_except_map_task")
      | `Omega.IO.bindTask | `Omega.EIO.bindTask => pure (`OmegaInit.System.IO, "omega_io_except_bind_task")
      | `Omega.IO.chainTask | `Omega.EIO.chainTask => pure (`OmegaInit.System.IO, "omega_io_except_chain_task")
      | `Omega.IO.mapTasks | `Omega.EIO.mapTasks => pure (`OmegaInit.System.IO, "omega_io_except_map_tasks")
      | `Omega.BaseIO.asTask => pure (`OmegaInit.System.IO, "omega_io_as_task")
      | `Omega.BaseIO.mapTask => pure (`OmegaInit.System.IO, "omega_io_map_task")
      | `Omega.BaseIO.chainTask => pure (`OmegaInit.System.IO, "omega_io_chain_task")
      | `Omega.BaseIO.mapTasks => pure (`OmegaInit.System.IO, "omega_io_map_tasks")
      | `Omega.BaseIO.bindTask => pure (`OmegaInit.System.IO, "omega_io_bind_task")
      | `Omega.IO.getTaskState => pure (`OmegaInit.System.IO, "omega_io_get_task_state")
      | `Omega.IO.hasFinished => pure (`OmegaInit.System.IO, "omega_io_task_has_finished")
      | `Omega.IO.wait => pure (`OmegaInit.System.IO, "omega_io_wait")
      | `Omega.IO.waitAny' => pure (`OmegaInit.System.IO, "omega_io_wait_any_rest")
      | `Omega.IO.waitAny => pure (`OmegaInit.System.IO, "omega_io_wait_any")
      | `Omega.IO.cancel => pure (`OmegaInit.System.IO, "omega_io_cancel")
      | `Omega.IO.checkCanceled => pure (`OmegaInit.System.IO, "omega_io_check_canceled")
      | `Omega.IO.Promise.new => pure (`OmegaInit.System.Promise, "omega_io_promise_new")
      | `Omega.IO.Promise.resolve => pure (`OmegaInit.System.Promise, "omega_io_promise_resolve")
      | `Omega.IO.Promise.isResolved => pure (`OmegaInit.System.Promise, "omega_io_promise_is_resolved")
      | `Omega.panicCore => pure (`OmegaInit.Prelude, "omega_panic_core")
      | `Omega.Array.get!Internal => pure (`OmegaInit.Prelude, "omega_array_get_bang")
      | `Omega.Char.ofNat => pure (`OmegaInit.Prelude, "omega_char_of_nat")
      | `Omega.String.toByteArray => pure (`OmegaInit.Prelude, "omega_string_to_bytes")
      | `Omega.String.decEq => pure (`OmegaInit.Prelude, "omega_string_dec_eq")
      | `Omega.String.hash => pure (`OmegaInit.Prelude, "omega_string_hash")
      | `Omega.String.Pos.Raw.get | `Omega.String.get => pure (`OmegaInit.Data.String.Basic, "omega_string_get_char")
      | `Omega.String.Pos.Raw.next | `Omega.String.next => pure (`OmegaInit.Data.String.Basic, "omega_string_next")
      | `Omega.String.Pos.Raw.prev | `Omega.String.prev => pure (`OmegaInit.Data.String.Basic, "omega_string_prev")
      | `Omega.String.Pos.Raw.atEnd | `Omega.String.atEnd => pure (`OmegaInit.Data.String.Basic, "omega_string_at_end")
      | `Omega.String.Pos.Raw.isValid => pure (`OmegaInit.Data.String.Basic, "omega_string_valid_pos")
      | `Omega.ByteArray.validateUTF8 => pure (`OmegaInit.Data.String.Basic, "omega_bytes_valid_utf8")
      | `Omega.String.push => pure (`OmegaInit.Data.String.Bootstrap, "omega_string_push")
      | `Omega.String.Internal.length => pure (`OmegaInit.Data.String.Bootstrap, "omega_string_length")
      | `Omega.String.Internal.append => pure (`OmegaInit.Data.String.Bootstrap, "omega_string_append")
      | `Omega.String.Internal.extract => pure (`OmegaInit.Data.String.Bootstrap, "omega_string_extract")
      | `Omega.String.mk => pure (`OmegaInit.Data.String.Bootstrap, "omega_string_of_list")
      | `Omega.String.append => pure (`OmegaInit.Data.String.Defs, "omega_string_append")
      | `Omega.String.markLinear => pure (`OmegaInit.Data.String.Defs, "omega_string_mark")
      | `Omega.String.propagateMark => pure (`OmegaInit.Data.String.Defs, "omega_string_propagate")
      | `Omega.ByteArray.mk => pure (`OmegaInit.Prelude, "omega_byte_array_mk")
      | `Omega.ByteArray.emptyWithCapacity => pure (`OmegaInit.Prelude, "omega_byte_array_empty")
      | `Omega.ByteArray.push => pure (`OmegaInit.Prelude, "omega_byte_array_push")
      | `Omega.String.ofByteArray => pure (`OmegaInit.Prelude, "omega_string_of_bytes")
      | `Omega.String.toUTF8 => pure (`OmegaInit.Data.String.Defs, "omega_string_utf8")
      | `Omega.String.data => pure (`OmegaInit.Data.String.Basic, "omega_string_data")
      | `Omega.String.decidableLT => pure (`OmegaInit.Data.String.Basic, "omega_string_dec_lt")
      | `Omega.String.utf8ByteSize => pure (`OmegaInit.Prelude, "omega_string_byte_size")
      | `Omega.String.toList => pure (`OmegaInit.Data.String.Basic, "omega_string_to_list")
      | `Omega.String.ofList => pure (`OmegaInit.Prelude, "omega_string_of_list")
      | _ => do
        if n == `Nat.xor && data == ⟨[.standard `all "lean_nat_lxor"]⟩ then
          let args := #[(IR.IRType.tobject, true), (.tobject, true)]
          InitPort.NativeState.checkNativeNat full
          InitPort.NativeState.verify full n args .tobject "lean_nat_lxor"
          if let some ref := reference? then
            InitPort.NativeState.verify ref n args .tobject "lean_nat_lxor"
          pure (`OmegaInit.Data.Nat.Bitwise.Basic, "lean_nat_lxor")
        else if n == InitKernelPort.portName InitPort.RandomState.support then
          pure (`OmegaInit.Data.Random, "omega_std_gen_ref")
        else if n == InitKernelPort.portName InitPort.ReferenceModify.support then
          pure (`OmegaInit.System.ST, "omega_st_ref_read_for_modify")
        else if n == InitKernelPort.portName InitPort.StateRunner.support then
          pure (`OmegaInit.Control.StateRef, "omega_state_ref_read_with_initial")
        else if let some op := InitPort.BufferReference.operations.find? (fun op => n == InitPort.BufferReference.strictName op) then
          pure (`OmegaInit.System.IO, "omega_buffer_" ++ op.getString!)
        else
          let original := InitKernelPort.originalName n
          let some ref := reference? | throw <| IO.userError s!"unverified native symbol for {owner}/{n}"
          unless n == InitKernelPort.portName original && ref.getModuleIdxFor? original == ref.getModuleIdx? (counterpart owner) &&
              InitPort.WordNative.supported ref owner original (InitPort.FloatArrayNative.boxed full) do
            throw <| IO.userError s!"unverified native symbol for {owner}/{n}"
          InitPort.NativeState.checkNativeNat full
          discard <| InitPort.WordNative.wrapper ref full n
          let some (.extern _ _ _ ⟨[.standard `all symbol]⟩) := IR.findEnvDecl full n
            | throw <| IO.userError s!"missing checked native entry for {owner}/{n}"
          pure (owner, symbol)
    unless owner == expectedOwner && env.getModuleIdxFor? n == some idx &&
        data == ⟨[.standard `all symbol]⟩ do throw <| IO.userError s!"invalid native state entry {owner}/{n}"
  for (n, implementation) in Compiler.implementedByAttr.ext.getModuleEntries env idx do
    if n == `Omega.Nat.modCore.go then
      let some pinned := reference? | throw <| IO.userError "missing pinned modulo definition"
      let some (.defnInfo impl) := full.find? implementation | throw <| IO.userError "missing modulo implementation"
      unless owner == `OmegaInit.Prelude && env.getModuleIdxFor? n == some idx &&
          implementation == mkPrivateNameCore owner `Omega.Nat.modCoreGoImpl &&
          full.getModuleIdxFor? implementation == full.getModuleIdx? owner &&
          InitKernelPort.exactDefinition pinned env.toKernelEnv `Nat.modCore.go &&
          impl.value.getNumHeadLambdas == 5 &&
          impl.value.getLambdaBody == mkApp2 (mkConst `Nat.mod) (mkBVar 1) (mkBVar 4) do
        throw <| IO.userError "invalid modulo implementation for the pinned recurrence"
      InitPort.NativeState.checkNativeNat full
      InitPort.NativeState.verify full `Nat.mod #[(.tobject, true), (.tobject, true)] .tobject "lean_nat_mod"
      continue
    let original := InitKernelPort.originalName n
    let expected := if original == `TypeName.typeName then some (mkPrivateNameCore `Init.Dynamic `TypeName.typeNameImpl)
      else if InitPort.DynamicValue.operations.contains original then some (InitPort.DynamicValue.implementation original)
      else none
    unless owner == `OmegaInit.Dynamic && (expected.map InitKernelPort.portName) == some implementation &&
        env.getModuleIdxFor? n == some idx && env.getModuleIdxFor? implementation == some idx do
      throw <| IO.userError s!"unmatched native implementation {n} → {implementation} in {owner}"
  for entry in reducibilityExtraExt.ext.getModuleEntries env idx do
    let (name, _) := match entry with
      | .global value | .scoped _ value => value
    throw <| IO.userError s!"unverified public reducibility override for {name} in {owner}"
  let extensions := #[
    ("parser", (Parser.parserExtension.ext.getModuleEntries env idx).size),
    ("macro", (Elab.macroAttribute.ext.ext.getModuleEntries env idx).size),
    ("term elaborator", (Elab.Term.termElabAttribute.ext.ext.getModuleEntries env idx).size)]
  for (kind, count) in extensions do
    if count != 0 then
      throw <| IO.userError s!"no elaboration correspondence for public {kind} entries in {owner}"
  for (ext, entries) in env.header.moduleData[idx]!.entries do
    unless entries.isEmpty || supportedExtension ext do
      throw <| IO.userError s!"no elaboration correspondence for public environment extension {ext} in {owner}"

/-- Validate the metadata that ordinary field notation and structure literals consume. -/
private def checkStructures (port ref : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  let rename := fun (n : Name) => Id.run do
    if let some lexical := privatePrefix? n then
      if (`_private.OmegaInit).isPrefixOf lexical then
        return lexical.replacePrefix `_private.OmegaInit `_private.Init ++
          (privateToUserName n).replacePrefix `Omega .anonymous
    return n.replacePrefix `Omega .anonymous
  for name in Meta.completionBlackListExt.getModuleEntries port idx do
    unless port.getModuleIdxFor? name == some idx &&
        ref.getModuleIdxFor? (rename name) == ref.getModuleIdx? (counterpart owner) &&
        Meta.completionBlackListExt.isTagged ref (rename name) do
      throw <| IO.userError s!"unmatched completion blacklist entry for {owner}/{name}"
  for (name, info) in noConfusionExt.getModuleEntries port idx do
    let upstream := rename name
    let some original := noConfusionExt.find? ref upstream
      | throw <| IO.userError s!"missing upstream no-confusion registration for {name}"
    let same := match info, original with
      | .regular a l r, .regular b x y => a == b && l == x && r == y
      | .perCtor a f, .perCtor b g => a == b && f == g
      | _, _ => false
    unless same && port.getModuleIdxFor? name == some idx &&
        ref.getModuleIdxFor? upstream == ref.getModuleIdx? (counterpart owner) do
      throw <| IO.userError s!"no-confusion metadata mismatch for {owner}/{name}"
  for s in structureExt.getModuleEntries port idx do
    let some (.inductInfo ind) := port.find? s.structName
      | throw <| IO.userError s!"registered structure {s.structName} is not an inductive type in {owner}"
    unless ind.ctors.length == 1 do
      throw <| IO.userError s!"registered structure {s.structName} must have one constructor in {owner}"
    let some target := getStructureInfo? ref (rename s.structName)
      | throw <| IO.userError s!"unknown public structure {s.structName} in {owner}"
    unless port.getModuleIdxFor? s.structName == some idx &&
        ref.getModuleIdxFor? target.structName == ref.getModuleIdx? (counterpart owner) &&
        s.fieldNames == target.fieldNames && s.fieldInfo.size == target.fieldInfo.size &&
        s.parentInfo.size == target.parentInfo.size do
      throw <| IO.userError s!"structure field order or owner mismatch for {s.structName}"
    for (f, g) in s.fieldInfo.zip target.fieldInfo do
      unless f.fieldName == g.fieldName && rename f.projFn == g.projFn &&
          f.subobject?.map rename == g.subobject? && f.binderInfo == g.binderInfo &&
          f.autoParam?.isNone && g.autoParam?.isNone do
        throw <| IO.userError s!"structure field mismatch for {s.structName}.{f.fieldName}"
    for (p, q) in s.parentInfo.zip target.parentInfo do
      unless rename p.structName == q.structName && p.subobject == q.subobject && rename p.projFn == q.projFn do
        throw <| IO.userError s!"structure parent mismatch for {s.structName}.{p.projFn}"
  for (name, info) in projectionFnInfoExt.getModuleEntries port idx do
    let some (.ctorInfo ctor) := port.find? info.ctorName
      | throw <| IO.userError s!"projection {name} has no constructor {info.ctorName} in {owner}"
    let some target := ref.getProjectionFnInfo? (rename name)
      | throw <| IO.userError s!"unmatched projection {name} in {owner}"
    unless port.getModuleIdxFor? name == some idx &&
        ref.getModuleIdxFor? (rename name) == ref.getModuleIdx? (counterpart owner) &&
        info.i < ctor.numFields && info.numParams == ctor.numParams && rename info.ctorName == target.ctorName &&
        info.numParams == target.numParams && info.i == target.i && info.fromClass == target.fromClass do
      throw <| IO.userError s!"projection metadata mismatch for {name} in {owner}"

private abbrev ClassParameters := Array Nat × Array Nat

private def checkInstances (env reference : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  let installed := Meta.instanceExtension.ext.getModuleEntries env idx
  let defaults := Meta.defaultInstanceExtension.getModuleEntries env idx
  if installed.isEmpty && defaults.isEmpty then return
  let rename := fun (n : Name) => n.replacePrefix `Omega .anonymous
  let key := fun (k : Meta.DiscrTree.Key) => match k with
    | .const n a => .const (rename n) a
    | .proj n i a => .proj (rename n) i a
    | k => k
  let load := fun (e : ScopedEnvExtension.Entry Meta.InstanceEntry) => match e with
    | .global v => (none, v)
    | .scoped ns v => (some ns, v)
  let some upstream := reference.getModuleIdx? (counterpart owner)
    | throw <| IO.userError s!"missing official owner for instances in {owner}"
  let pinnedDefaults := Meta.defaultInstanceExtension.getModuleEntries reference upstream
  let mut remaining := pinnedDefaults.toList
  for d in defaults do
    remaining := remaining.dropWhile fun p =>
      InitKernelPort.portName p.className != d.className ||
      InitKernelPort.portName p.instanceName != d.instanceName || p.priority != d.priority
    let _ :: rest := remaining
      | throw <| IO.userError s!"unmatched default instance {d.instanceName} for {d.className} in {owner}"
    let registeredClass := (env.getModuleIdxFor? d.className).any fun classOwner =>
      (classExtension.getModuleEntries env classOwner).any (·.name == d.className)
    unless env.contains d.instanceName && registeredClass do
      throw <| IO.userError s!"unavailable default instance {d.instanceName} for {d.className} in {owner}"
    remaining := rest
  let actual := (Meta.instanceExtension.ext.getModuleEntries reference upstream).map load
  let mut last := 0
  for e in installed do
    let (scope, v) := load e
    let some name := v.globalName? | throw <| IO.userError s!"unnamed public instance in {owner}"
    let .const n us := v.val | throw <| IO.userError s!"invalid public instance term in {owner}"
    unless name == n && (name.getRoot == `Omega || OmegaChecks.InitCompiler.RootNames.isPrimitive owner name) && env.contains name && reference.contains (rename name) do
      throw <| IO.userError s!"no elaboration correspondence for public instance {name} in {owner}"
    -- Preserve the relative order of registered candidates, including priority ties.
    let mut found := false
    while last < actual.size && !found do
      let (targetScope, target) := actual[last]!
      last := last + 1
      found := targetScope == scope.map rename && target.globalName? == some (rename name) &&
        target.val.equal (.const (rename name) us) && target.priority == v.priority &&
        target.keys == v.keys.map key && target.synthOrder == v.synthOrder && target.attrKind == v.attrKind
    unless found do throw <| IO.userError s!"unmatched public instance registration for {name} in {owner}"

private def classParameters (env : Environment) (modules : Array ModuleIdx) : NameMap ClassParameters :=
  modules.foldl (init := {}) fun classes idx =>
    (classExtension.getModuleEntries env idx).foldl (init := classes) fun m entry =>
      m.insert entry.name (entry.outParams, entry.outLevelParams)

private def checkClasses (strict reference : Environment) (owner : Name) (idx : ModuleIdx)
    (strictClasses officialClasses : NameMap ClassParameters) : IO Unit := do
  -- Registrations can target an imported declaration, including a universe-output override.
  let registered := (classExtension.getModuleEntries strict idx).map (·.name)
  for name in registered ++ strict.header.moduleData[idx]!.constNames do
    if isPrivateName name || name.isInternal then continue
    let upstream := name.replacePrefix `Omega .anonymous
    if (registered.contains name && !reference.contains upstream) ||
        strictClasses.get? name != officialClasses.get? upstream then
      throw <| IO.userError s!"public class registration mismatch for {name} in {owner}"

private def checkSimp (strict reference : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  for entry in Meta.simpExtension.ext.getModuleEntries strict idx do
    -- Unfolding a public definition needs the same upstream instruction and the
    -- definition-level body check. The public rule must not reveal a sealed implementation.
    let .global (.toUnfold name) := entry
      | throw <| IO.userError s!"no correspondence for public simp rewrite or scoped entry in {owner}"
    let upstream := name.replacePrefix `Omega .anonymous
    let isExposed := (strict.find? name).any (· matches .defnInfo _)
    let equivalent := reference.allImportedModuleNames.any fun moduleName => Id.run do
      let some i := reference.getModuleIdx? moduleName | return false
      return (Meta.simpExtension.ext.getModuleEntries reference i).any fun
        | .global (.toUnfold n) => n == upstream
        | _ => false
    unless isExposed && equivalent do
      throw <| IO.userError s!"unmatched public simp unfolding for {name} in {owner}"

/-- Check a port as seen by a consumer importing it alone. Re-exported foundation
declarations and alias targets are mathematical roots, even in a declaration-free module. -/
def check (strict : Environment) (full? : Option Environment := none) : IO (Array (Name × Name)) := do
  let strict := withImportedAliases strict
  let mut roots : NameMap Name := {}
  let nativeOwners := strict.allImportedModuleNames.filter fun owner =>
    owner.getRoot == `OmegaInit && (strict.getModuleIdx? owner).any fun idx =>
      !(externAttr.ext.getModuleEntries strict idx).isEmpty
  let full := full?.getD strict
  let hasMatchers := fun (env : Environment) owner => (env.getModuleIdx? owner).any fun idx =>
    let ext := Meta.Match.Extension.extension
    !(ext.getModuleEntries env idx).isEmpty || !(ext.getModuleEntries env idx (level := .server)).isEmpty ||
    env.header.moduleData[idx]!.constNames.any fun n => n == Meta.mkSmartUnfoldingNameFor n.getPrefix
  let matcherOwners := strict.allImportedModuleNames.filter fun owner =>
    isBasis owner && (hasMatchers strict owner || hasMatchers full owner)
  let pinnedOwners := nativeOwners ++ matcherOwners.filter (!nativeOwners.contains ·)
  let pinned ← importModules (pinnedOwners.map fun n => {module := counterpart n, importAll := true}) {}
  for port in strict.allImportedModuleNames do
    if !isBasis port then continue
    let some idx := strict.getModuleIdx? port | throw <| IO.userError s!"missing module {port}"
    checkSpecializations full port
    if port == port.getRoot then
      checkElaboration strict full none port idx
      unless (structureExt.getModuleEntries strict idx).isEmpty &&
          (projectionFnInfoExt.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched structure registration in the {port} umbrella"
      unless (Meta.instanceExtension.ext.getModuleEntries strict idx).isEmpty &&
          (Meta.defaultInstanceExtension.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched instance registration in the {port} umbrella"
      unless (Meta.simpExtension.ext.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched simp registration in the {port} umbrella"
      if matcherOwners.contains port then
        throw <| IO.userError s!"unmatched matcher registration in the {port} umbrella"
      checkUmbrella strict port idx
      continue
    let official := counterpart port
    let reference := withImportedAliases (← importModules #[{module := official}] {} (level := .exported))
    checkElaboration strict full (some pinned) port idx
    if matcherOwners.contains port then
      checkMatchers strict full reference pinned port idx
      if full?.isSome && port.getRoot == `OmegaInit then
        let fullIdx := (full.getModuleIdx? port).get!
        checkMatchers full full pinned pinned port fullIdx
    let officialClasses := classParameters reference (Array.range reference.header.modules.size)
    let visible ← publicClosure strict port
    let visibleIndices := (Array.range strict.header.modules.size).filter fun i =>
      visible.contains strict.header.moduleNames[i]!
    let strictClasses := classParameters strict visibleIndices
    -- Diagnose the port's own public registrations before those of a re-export.
    for owner in port :: (visible.erase port).toList do
      let some idx := strict.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
      if owner != port then checkElaboration strict full (some pinned) owner idx
      let data := strict.header.moduleData[idx]!
      checkStructures strict reference owner idx
      checkInstances strict reference owner idx
      checkClasses strict reference owner idx strictClasses officialClasses
      checkSimp strict reference owner idx
      if data.imports.any (fun dep => dep.isExported && dep.importAll) then
        throw <| IO.userError s!"unverified public import all exposed by {owner}"
      for name in data.constNames do
        if isPrivateName name || name.isInternal then continue
        let expected := counterpart owner
        let translated := name.replacePrefix `Omega .anonymous
        unless reference.contains translated do
          throw <| IO.userError s!"{official} does not publicly expose {translated} for {name} in {port}"
        unless isProtected strict name == isProtected reference translated do
          throw <| IO.userError s!"protected modifier mismatch for {name} in {official}"
        if hasMatchPatternAttribute strict name && !hasMatchPatternAttribute reference translated then
          throw <| IO.userError s!"unmatched match_pattern attribute for {name} in {official}"
        if hasNeverExtractAttribute strict name != hasNeverExtractAttribute reference translated then
          throw <| IO.userError s!"never_extract mismatch for {name} in {official}"
        if Elab.Term.elabAsElim.hasTag strict name && !Elab.Term.elabAsElim.hasTag reference translated then
          throw <| IO.userError s!"unmatched elab_as_elim attribute for {name} in {official}"
        if let some (alias, target) := OmegaChecks.InitCompiler.RootNames.aliasFor? translated then
          unless name == target && (aliasExtension.getModuleEntries strict idx).contains (alias, target) &&
              ResolveName.resolveGlobalName strict {} .anonymous [] alias == [(target, [])] do
            throw <| IO.userError s!"missing or ambiguous source alias {alias} for {target} in {owner}"
        roots := roots.insert name expected
      for (alias, target) in aliasExtension.getModuleEntries strict idx do
        let officialAlias := alias.replacePrefix `Omega .anonymous
        let officialTarget := target.replacePrefix `Omega .anonymous
        -- An importing module may add overloads, including a declaration with the alias's
        -- own name. Only candidates exported by this strict root participate in its interface.
        let resolved := (ResolveName.resolveGlobalName reference {} .anonymous [] officialAlias).filter
          fun (candidate, _) => candidate == officialTarget ||
            (strict.getModuleIdxFor? (`Omega ++ candidate)).any fun home =>
              visible.contains strict.header.moduleNames[home]!
        let some originalOwner := reference.getModuleIdx? (counterpart owner)
          | throw <| IO.userError s!"missing owner of alias {alias} in {official}"
        let rootAlias := OmegaChecks.InitCompiler.RootNames.aliasFor? officialTarget == some (alias, target) &&
          strict.header.moduleData[idx]!.constNames.contains target &&
          reference.header.moduleData[originalOwner]!.constNames.contains officialTarget
        unless (rootAlias || (aliasExtension.getModuleEntries reference originalOwner).contains (officialAlias, officialTarget)) &&
            resolved == [(officialTarget, [])] do
          throw <| IO.userError s!"unmatched public alias {alias} for {target} exposed by {port} in {official}"
        let some home := strict.getModuleIdxFor? target | throw <| IO.userError s!"unknown alias target {target}"
        roots := roots.insert target (counterpart strict.header.moduleNames[home]!)
  return roots.toList.toArray

end OmegaChecks.ModuleSurface
