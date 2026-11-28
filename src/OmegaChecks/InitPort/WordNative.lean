module

public import OmegaChecks.InitPort.NativeState
public import OmegaChecks.InitPort.WordNative.Operations
import all OmegaChecks.InitPort.WordNative.Operations
import OmegaChecks.InitPort.UnsafeRuntime
import OmegaChecks.InitPort.IONative
import OmegaChecks.InitPort.SeparatorNative
import OmegaChecks.InitPort.ArrayMap
import OmegaChecks.InitPort.MacroNative
import OmegaChecks.InitPort.SyntaxPositionNative
import OmegaChecks.InitPort.FloatArrayNative
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.ByteFoldNative
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.OriginalConstKind
import Lean.Compiler.ImplementedByAttr

/-! Compile scalar primitives over the strict, Nat-backed Fin representation. -/

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

namespace OmegaChecks.InitPort.WordNative

private def symbol (n : Name) := (n.replacePrefix `Omega .anonymous).mangle "omega_word_"

public def install (names : Array Name) : CoreM Unit := do
  unless names.isEmpty do checkNativeNat (← getEnv)
  for n in names do
    unless (← getEnv).find? n matches some (.ctorInfo _) do
      modifyEnv fun e => privateConstKindsExt.insert e n .defn
    let official := InitKernelPort.originalName n
    let natEntry := (InitCompiler.RootNames.borrowedNatExtern? official).map (·.2.1)
    let entry := (thunkExtern n <|> natEntry).getD (symbol n)
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all entry]⟩)
    (← compileDeclsRef.get) #[n] {}

private def layout (env : Environment) (name : Name) : IO Unit := do
  let storage := if name == `Float.Model then `UInt64 else if name == `Float32.Model then `UInt32 else bitsType name
  for n in [`Omega.Fin, `Omega.BitVec, `Omega ++ storage, `Omega ++ name].eraseDups do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"word argument does not erase to Nat: {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"incorrect word layout: {n}"

private def checkIntLayout (strict : Environment) : IO Unit := do
  for (ctor, tag) in [(`Omega.Int.ofNat, 0), (`Omega.Int.negSucc, 1)] do
    let some l := ctorLayoutExt.find? strict ctor | throw <| IO.userError s!"missing {ctor}"
    let #[.object 0 _] := l.fieldInfo | throw <| IO.userError s!"invalid integer field in {ctor}"
    unless l.ctorInfo.cidx == tag && l.ctorInfo.size == 1 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 do
      throw <| IO.userError s!"unexpected integer constructor layout {ctor}"

private def checkFloatLayout (env : Environment) (name : Name) : IO Unit := do
  layout env (if name == `Float32 then `UInt32 else `UInt64)
  for n in [`Omega ++ name, `Omega ++ name ++ `Model] do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"floating-point bits have no strict representation in {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected floating-point field in {n}"

private def checkNameLayout (source strict : Environment) : IO Unit := do
  checkStrictString strict
  unless getExportNameFor? source `Lean.Name.mkStr == some `lean_name_mk_string &&
      getExportNameFor? source `Lean.Name.mkNum == some `lean_name_mk_numeral do
    throw <| IO.userError "unexpected pinned name constructors"
  for (env, root) in [(source, `Lean.Name), (strict, `Omega.Lean.Name)] do
    for (ctor, tag) in [(`anonymous, 0), (`str, 1), (`num, 2)] do
      let name := root ++ ctor
      let some l := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing name layout {name}"
      let valid := if tag == 0 then l.fieldInfo.isEmpty else
        match l.fieldInfo with | #[.object 0 _, .object 1 _] => true | _ => false
      unless valid && l.ctorInfo.cidx == tag && l.ctorInfo.size == l.fieldInfo.size &&
          l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do throw <| IO.userError s!"invalid name layout: {name}"

/-- Dynamic stores the pinned runtime name together with the caller's boxed payload.
The native Option preserves the same tags and payload representation on both sides. -/
private def dynamicWrapper (source strict : Environment) (n op : Name) : IO String := do
  let impl := DynamicValue.implementation op
  let some (.defnInfo pinned) := source.find? impl | throw <| IO.userError s!"missing {impl}"
  let some publicOp := source.find? op | throw <| IO.userError s!"missing {op}"
  let some dest := strict.find? n | throw <| IO.userError s!"missing {n}"
  let privateEntry := InitKernelPort.originalName n == impl
  unless (publicOp matches .opaqueInfo _) && !publicOp.isUnsafe && pinned.safety == .unsafe &&
      source.getModuleIdxFor? op == source.getModuleIdx? `Init.Dynamic &&
      source.getModuleIdxFor? impl == source.getModuleIdx? `Init.Dynamic &&
      Compiler.getImplementedBy? source op == some impl && dest.isUnsafe == privateEntry &&
      InitKernelPort.translate InitKernelPort.portName (if privateEntry then pinned.type else publicOp.type) == dest.type do
    throw <| IO.userError s!"unexpected dynamic interface {n}"
  let some (.fdecl _ args out _ info) := IR.findEnvDecl source impl | throw <| IO.userError s!"missing {impl} code"
  let some (.extern _ actual result ⟨[.standard `all sym]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing native {n}"
  let pack := op == `Dynamic.mk
  let name := op == `Dynamic.typeName
  let kinds : Array (IR.IRType × Bool) := if name then #[(.tobject, true)]
    else #[(.erased, false), (.tobject, !pack), (.tobject, !pack)]
  unless sym == symbol n && args.map (fun a => (a.ty, a.borrow)) == kinds && out == .tobject &&
      info.sorryDep?.isNone && result == .tobject && actual.map (·.ty) == kinds.map Prod.fst do
    throw <| IO.userError s!"unexpected dynamic ABI {n}: {actual.map (fun a => (a.ty, a.borrow))} → {result}"
  checkNameLayout source strict
  checkErasedField strict `Omega.TypeName
  if !name && !pack then IndexedNative.checkDataTypes source strict [`Option]
  let target := getSymbolStem source impl
  let types := if name then "lean_object *" else "lean_object *, lean_object *, lean_object *"
  let header := "#include \"strict_name.h\"\n" ++ s!"extern lean_obj_res {target}({types});\n"
  let release (idx : Nat) (var : String) := if actual[idx]!.borrow then "" else s!"lean_dec({var}); "
  let retain (idx : Nat) (var : String) := if actual[idx]!.borrow then s!"lean_inc({var}); " else ""
  let (params, body) := if pack then
      ("lean_object *tag, lean_object *value",
       "lean_object *native = omega_name_to_lean(tag); " ++ release 1 "tag" ++ retain 2 "value" ++
       s!"return {target}(lean_box(0), native, value);")
    else if name then
      ("lean_object *value", s!"lean_object *native = {target}(value); " ++ release 0 "value" ++
       "lean_object *result = omega_name_from_lean(native); lean_dec(native); return result;")
    else
      ("lean_object *value, lean_object *tag", "lean_object *native = omega_name_to_lean(tag); " ++
       s!"lean_object *result = {target}(lean_box(0), value, native); lean_dec(native); " ++
       release 1 "value" ++ release 2 "tag" ++ "return result;")
  return header ++ s!"LEAN_EXPORT lean_obj_res {sym}({params}) \{ {body} }\n"

private def checkSliceLayout (source strict : Environment) : IO Unit := do
  for (env, ns) in [(source, Name.anonymous), (strict, `Omega)] do
    for pos in [`String.Pos, `String.Pos.Raw] do
      let some (some f) := impureTrivialStructureInfoExt.find? env (ns ++ pos)
        | throw <| IO.userError s!"missing erased slice position {ns ++ pos}"
      unless f.fieldIdx == 0 do throw <| IO.userError s!"incorrect slice offset field {ns ++ pos}"
    let some l := ctorLayoutExt.find? env (ns ++ `String.Slice.mk) | throw <| IO.userError "missing slice layout"
    let #[.object 0 _, .object 1 _, .object 2 _, .erased] := l.fieldInfo | throw <| IO.userError "unexpected slice fields"
    unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 3 && l.ctorInfo.usize == 0 && l.ctorInfo.ssize == 0 do
      throw <| IO.userError "unexpected slice constructor"

/-- Check both sides of the call and generate its ownership conversions from their stored IR. -/
public def wrapper (source strict : Environment) (n : Name) : IO String := do
  let official := InitKernelPort.originalName n
  if let some (_, entry, arity) := InitCompiler.RootNames.borrowedNatExtern? official then
    let args := Array.replicate arity (IR.IRType.tobject, true)
    verify source official args .tobject entry
    verify strict n args .tobject entry
    return ""
  if let some entry := thunkExtern official then
    let read := official == `Thunk.get
    let args := #[(IR.IRType.erased, false), (if read then .object else .tobject, read)]
    let out := if read then IR.IRType.tobject else .object
    unless n == official && (source.find? n).map (·.type) == (strict.find? n).map (·.type) do
      throw <| IO.userError s!"unexpected primitive thunk interface {n}"
    for env in [source, strict] do verify env n args out entry
    return ""
  if official == `ptrAddrUnsafe then
    let pinned := some "lean_ptr_addr"
    unless UnsafeRuntime.observerSymbol? source `Init.Util official false == pinned &&
        UnsafeRuntime.observerSymbol? strict `Init.Util official true == pinned do
      throw <| IO.userError "unexpected borrowed address observer ABI"
    layout strict `USize
    return s!"\nLEAN_EXPORT lean_obj_res {symbol n}(b_lean_obj_arg value) \{ return lean_usize_to_nat(lean_ptr_addr(value)); }\n"
  if official == `isExclusiveUnsafe then
    unless UnsafeRuntime.exclusiveABI source false && UnsafeRuntime.exclusiveABI strict true do
      throw <| IO.userError "unexpected borrowed exclusivity observation ABI"
    IndexedNative.checkDataTypes source strict [`Bool]
    return s!"\nLEAN_EXPORT uint8_t {symbol n}(b_lean_obj_arg value) \{ return lean_is_exclusive_obj(value); }\n"
  if official == `ByteArray.markLinear || official == `ByteArray.propagateMark then
    checkStrictBytes strict
    let unary := official == `ByteArray.markLinear
    let args := if unary then #[(IR.IRType.object, false)] else #[(.object, true), (.object, false)]
    let primitive := if unary then "lean_sarray_mark_linear" else "lean_sarray_propagate_mark"
    verify source official args .object primitive
    verify strict n (args.map (fun (_, b) => (IR.IRType.tobject, b))) .tobject (symbol n)
    let call := if unary then "omega_bytes_mark(value)" else
      "lean_ctor_get_uint8(source, 3 * sizeof(void *)) ? omega_bytes_mark(value) : value"
    let params := (if unary then "" else "b_lean_obj_arg source, ") ++ "lean_obj_arg value"
    return s!"\n#include \"strict_byte_array.h\"\nLEAN_EXPORT lean_obj_res {symbol n}({params}) \{ return {call}; }\n"
  if let some op := DynamicValue.operation? official then return ← dynamicWrapper source strict n op
  if IONative.supported official then return ← IONative.wrapper source strict n (symbol n)
  if (ArrayMap.reference? official).isSome then return ← ArrayMap.wrapper source strict n (symbol n)
  if MacroNative.supported official then return ← MacroNative.wrapper source strict n (symbol n)
  if monadicSeparator official then return ← SeparatorNative.wrapper source strict n official (symbol n)
  if (BorrowedNative.symbol? official).isSome then return ← BorrowedNative.wrapper source strict n (symbol n)
  if ByteFoldNative.supported official then return ← ByteFoldNative.wrapper source strict n (symbol n)
  if IndexedNative.supported official then return ← IndexedNative.wrapper source strict n (symbol n)
  if SyntaxPositionNative.supported official then return ← SyntaxPositionNative.wrapper source strict n (symbol n)
  let some ci := source.find? official | throw <| IO.userError s!"unknown word primitive {official}"
  if official == `Quot.liftOn then
    let some (.defnInfo d) := strict.find? n | throw <| IO.userError "missing strict quotient eliminator"
    let some (.defnInfo original) := source.find? official | throw <| IO.userError "missing pinned quotient eliminator"
    -- Quot and its lift are aliases of the kernel primitives in the packaged Prelude.
    unless Kernel.isDefEqGuarded strict {} d.type original.type &&
        Kernel.isDefEqGuarded strict {} d.value original.value do
      throw <| IO.userError "quotient eliminator differs from the pinned definition"
    let some (.fdecl _ params .tobject (.vdecl res .tobject (.ap f #[.var q]) (.ret (.var out))) _) :=
        IR.findEnvDecl source official | throw <| IO.userError "unexpected pinned quotient implementation"
    let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
      | throw <| IO.userError "missing strict quotient calling convention"
    let types := #[IR.IRType.erased, .erased, .erased, .tobject, .tobject, .erased]
    unless params.map (·.ty) == types && actual.map (·.ty) == types &&
        params.all (!·.borrow) && actual.all (!·.borrow) && entry == symbol n &&
        res == out && f == params[4]!.x && q == params[3]!.x do
      throw <| IO.userError "incompatible quotient eliminator ABI"
    return s!"\nLEAN_EXPORT lean_obj_res {entry}(lean_obj_arg q, lean_obj_arg f) \{ return lean_apply_1(f, q); }\n"
  if FloatArrayNative.operations.contains official && FloatArrayNative.boxed strict then
    return ← FloatArrayNative.wrapper source strict n (symbol n)
  if official == `Array.set! then
    let some target := strict.find? n | throw <| IO.userError "missing strict array update"
    unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError "different strict array update type"
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Array
      | throw <| IO.userError "strict array does not erase to its list"
    IndexedNative.checkDataTypes source strict [`List]
    let some (.extern _ args .object ⟨[.standard `all "lean_array_set"]⟩) := IR.findEnvDecl source official
      | throw <| IO.userError "missing pinned array update primitive"
    let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
      | throw <| IO.userError "missing strict array update primitive"
    unless field.fieldIdx == 0 && args.map (·.ty) == #[.erased, .object, .tobject, .tobject] &&
        actual.map (·.ty) == #[.erased, .tobject, .tobject, .tobject] &&
        args.map (·.borrow) == #[false, false, true, false] &&
        actual.map (·.borrow) == args.map (·.borrow) && entry == symbol n do
      throw <| IO.userError s!"incompatible array update ABI: {args.map fun a => (a.ty, a.borrow)}/{actual.map fun a => (a.ty, a.borrow)}"
    return s!"\n#include \"strict_array_set.h\"\nLEAN_EXPORT lean_obj_res {entry}(lean_obj_arg xs, b_lean_obj_arg i, lean_obj_arg v) \{ return omega_array_list_set_bang(xs, i, v); }\n"
  if floatArrayIndex official then
    let some target := strict.find? n | throw <| IO.userError s!"missing strict float array index {n}"
    unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"different float array index type at {n}"
    checkFloatLayout strict `Float
    IndexedNative.checkDataTypes source strict [`List]
    for name in [`Omega.FloatArray, `Omega.Array] do
      let some (some field) := impureTrivialStructureInfoExt.find? strict name
        | throw <| IO.userError s!"missing list representation in {name}"
      unless field.fieldIdx == 0 do throw <| IO.userError s!"incorrect list field in {name}"
    let read := official == `FloatArray.get!
    let some (.extern _ args ret ⟨[.standard `all pinned]⟩) := IR.findEnvDecl source official
      | throw <| IO.userError s!"missing pinned float array primitive: {official}"
    let some (.extern _ actual out ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
      | throw <| IO.userError s!"missing strict float array primitive: {n}"
    let pinnedArgs : Array IR.IRType := if read then #[.object, .tobject] else #[.object, .tobject, .float]
    let borrows := if read then #[true, true] else #[false, true, false]
    unless pinned == (if read then "lean_float_array_get" else "lean_float_array_set") &&
        args.map (·.ty) == pinnedArgs && args.map (·.borrow) == borrows &&
        ret == (if read then .float else .object) && out == .tobject && actual.size == args.size &&
        actual.all (·.ty == .tobject) && actual.map (·.borrow) == borrows && entry == symbol n do
      throw <| IO.userError s!"unexpected float array indexing ABI: {n} {actual.map fun a => (a.ty, a.borrow)}"
    let params := if read then "lean_object *xs, lean_object *i" else "lean_object *xs, lean_object *i, lean_object *v"
    let call := if read then "omega_float_list_get(xs, i)" else "omega_float_list_set(xs, i, v)"
    return s!"\n#include \"strict_float_array.h\"\nLEAN_EXPORT lean_obj_res {entry}({params}) \{ return {call}; }\n"
  if bootstrapStringOp official || basicStringExtern official || pinnedStringFunction official || syntaxTreeFunction official then
    let some strictInfo := strict.find? n | throw <| IO.userError s!"missing strict string operation {n}"
    unless strictInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"strict string input type differs at {n}"
    checkStrictString strict
    if official.getPrefix == `Substring.Raw.Internal || rawStringFunction official || [`Substring.Raw.toName, `Lean.Syntax.splitNameLit].contains official then
      for (env, name, text) in [(source, `Substring.Raw.mk, ImpureType.object), (strict, `Omega.Substring.Raw.mk, ImpureType.tobject)] do
        let some fields := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing substring record {name}"
        let #[.object 0 field, .object 1 start, .object 2 stop] := fields.fieldInfo | throw <| IO.userError "invalid substring fields"
        unless field == text && start == ImpureType.tobject && stop == ImpureType.tobject && fields.ctorInfo.cidx == 0 && fields.ctorInfo.size == 3 && fields.ctorInfo.usize == 0 && fields.ctorInfo.ssize == 0 do
          throw <| IO.userError "invalid substring record layout"
  if syntaxTreeFunction official then
    SyntaxPositionNative.checkTreeLayout source strict
    checkNameLayout source strict
  let compiled ← if official == `Nat.repr then do
    unless (Compiler.getImplementedBy? source official) == some `Nat.reprFast do throw <| IO.userError "unexpected Nat.repr implementation"
    let some fast := source.find? `Nat.reprFast | throw <| IO.userError "missing pinned Nat.reprFast"
    unless fast.type == ci.type do throw <| IO.userError "Nat.reprFast type differs from Nat.repr"
    pure `Nat.reprFast
  else if official == `Lean.Name.hash then do
    let impl := `Lean.Name.hash._override
    let some fast := source.find? impl | throw <| IO.userError "missing pinned name hash"
    unless (Compiler.getImplementedBy? source official) == some impl && fast.type == ci.type do
      throw <| IO.userError "unexpected pinned name hash implementation"
    pure impl
  else pure official
  let some impl := IR.findEnvDecl source compiled | throw <| IO.userError s!"no pinned IR for {official}"
  if debugPrimitive official then
    let some strictInfo := strict.find? n | throw <| IO.userError s!"missing strict debug operation {n}"
    unless strictInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"different debug operation type at {n}"
  if digitList official then
    let some targetInfo := strict.find? n | throw <| IO.userError s!"missing strict character conversion {n}"
    unless targetInfo.type == InitKernelPort.translate InitKernelPort.portName ci.type do
      throw <| IO.userError s!"character conversion type mismatch {n}"
    IndexedNative.checkDataTypes source strict [`List]
    let some (some f) := impureTrivialStructureInfoExt.find? strict `Omega.Char | throw <| IO.userError "missing strict character"
    unless f.fieldIdx == 0 do throw <| IO.userError "invalid strict character"
    layout strict `UInt32
  let params := impl.params
  let ret := impl.resultType
  let target ← match impl with
    | .extern _ _ _ ⟨[.standard `all entry]⟩ => do
      if let some expected := versionNumber? official then
        let some installed := strict.find? n | throw <| IO.userError s!"missing version getter {n}"
        unless installed.type == InitKernelPort.translate InitKernelPort.portName ci.type &&
            ci.type == (.forallE `u (mkConst `Unit) (mkConst `Nat) .default) && entry == expected do
          throw <| IO.userError s!"unexpected version getter {official}"
      if official == `Lean.getGithash then
        -- The standalone runtime exports the primitive. The shared Lean library exports its boxed entry.
        let boxed := mkBoxedName official
        let some (.fdecl _ args .object ..) := IR.findEnvDecl source boxed
          | throw <| IO.userError "missing boxed git revision getter"
        unless args.map (·.ty) == #[.tagged] && entry == "lean_get_githash" do
          throw <| IO.userError "unexpected git revision getter ABI"
        pure (getSymbolStem source boxed)
      else pure entry
    | .fdecl .. =>
      unless usesPinnedFunction official do
        throw <| IO.userError s!"unexpected compiled word function {official}"
      if let some exported := getExportNameFor? source compiled then
        unless ([ (`String.Internal.pushnImpl, `lean_string_pushn),
                  (`String.Internal.intercalateImpl, `lean_string_intercalate),
                  (`String.Internal.capitalizeImpl, `lean_string_capitalize) ] : List (Name × Name)).contains (official, exported) do
          throw <| IO.userError s!"unexpected exported symbol {exported} for {official}"
        pure exported.toString
      else pure (getSymbolStem source compiled)
    | _ => throw <| IO.userError s!"expected pinned C primitive for {official}"
  let some (.extern _ actual result ⟨[.standard `all adapter]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict C primitive for {n}"
  unless actual.size == params.size && adapter == symbol n do throw <| IO.userError s!"incorrect word ABI: {n}"
  let mut type := ci.type
  let mut decls := #[]
  let mut args := #[]
  let mut prepare := ""
  let mut cleanup := ""
  let mut byteUpdate : Option Nat := none
  let mut hasString := false
  let mut hasName := false
  let passesErased := (pinnedStringFunction official || official == `Int.trailingZeros.aux) &&
    !(modifyStringFunction official && (impl matches .extern ..))
  for (a, b) in params.zip actual, i in [:params.size] do
    let .forallE _ dom body _ := type | throw <| IO.userError s!"expected argument {i} of {n}"
    type := body
    if a.ty == .erased && b.ty == .erased then
      if passesErased then args := args.push "lean_box(0)"
      continue
    let arg := "a" ++ toString i
    let plainDom := if dom.isAppOfArity `optParam 2 then dom.getAppArgs[0]! else dom
    if renderName official && plainDom.isForall then
      unless plainDom.bindingDomain! == mkConst `String && plainDom.bindingBody! == mkConst `Bool &&
          a.ty == .object && b.ty == .object && !a.borrow do throw <| IO.userError "invalid name token predicate"
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      prepare := prepare ++ s!"  lean_object *token = lean_alloc_closure((void *)omega_name_token, 2, 1);\n  lean_closure_set(token, 0, {arg});\n"
      args := args.push "token"
      continue
    if rawFold official && dom.isForall then
      let left := official == `Substring.Raw.foldl
      let first := if left then mkBVar 0 else mkConst `Char
      let second := if left then mkConst `Char else mkBVar 1
      unless dom.bindingDomain! == first && dom.bindingBody!.isForall &&
          dom.bindingBody!.bindingDomain! == second && dom.bindingBody!.bindingBody! == mkBVar 2 &&
          a.ty == .tobject && (b.ty == .tobject || b.ty == .object) && !a.borrow do
        throw <| IO.userError s!"invalid raw substring fold callback {n}"
      layout strict `Char
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      let step := if left then "omega_raw_fold_left" else "omega_raw_fold_right"
      prepare := prepare ++ s!"  lean_object *step = lean_alloc_closure((void *){step}, 3, 1);\n  lean_closure_set(step, 0, {arg});\n"
      args := args.push "step"
      continue
    if (debugPrimitive official || rawFold official) && (dom.isForall || dom.isBVar) then
      -- The runtime either returns the polymorphic payload or invokes its continuation with Unit.unit.
      let payload := (official == `dbgTraceIfShared || rawFold official) && dom == .bvar (i - 1)
      let thunk := dom.isForall && dom.bindingDomain! == mkConst `Unit && dom.bindingBody! == .bvar i
      unless (payload || thunk) && a.ty == .tobject && (b.ty == .tobject || b.ty == .object) && !a.borrow do
        throw <| IO.userError s!"different debug continuation or payload ABI at {n}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      args := args.push arg
      continue
    if syntaxTreeFunction official && dom.isForall then
      let map := official == `Array.mapSepElems
      unless (map || [`Lean.Syntax.findAux, `Array.filterSepElems].contains official) &&
          dom.bindingDomain! == mkConst `Lean.Syntax && dom.bindingBody! == mkConst (if map then `Lean.Syntax else `Bool) && a.ty == .object && b.ty == .object && !a.borrow do
        throw <| IO.userError s!"incorrect syntax predicate signature {n}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      let adapter := if map then "omega_syntax_map" else "omega_syntax_predicate"
      prepare := prepare ++ s!"  lean_object *predicate = lean_alloc_closure((void *){adapter}, 2, 1);\n  lean_closure_set(predicate, 0, {arg});\n"
      args := args.push "predicate"
      continue
    if (bootstrapStringOp official || official == `Substring.Raw.all || modifyStringFunction official) && dom.isForall then
      let arrow := fun (a b : Expr) => Expr.forallE .anonymous a b .default
      let unary := arrow (mkConst `Char) (mkConst `Bool)
      let binary := arrow (mkConst `String) (arrow (mkConst `Char) (mkConst `String))
      let fold := dom == binary && official == `String.Internal.foldl
      let mapChar := modifyStringFunction official && dom == arrow (mkConst `Char) (mkConst `Char)
      unless (fold || mapChar || dom == unary) && a.ty == .object && b.ty == .object do
        throw <| IO.userError s!"invalid pinned string callback {n} argument {i}, types {a.ty} and {b.ty}, borrowed {a.borrow} and {b.borrow}, domain {dom}"
      layout strict `Char
      IndexedNative.checkDataTypes source strict [`Bool]
      hasString := true
      let f := if fold then "omega_string_fold_step" else if mapChar then "omega_string_map_char" else "omega_string_predicate"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      prepare := prepare ++ s!"  lean_object *cb{i} = lean_alloc_closure((void *){f}, {if fold then 3 else 2}, 1);\n  lean_closure_set(cb{i}, 0, {arg});\n"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(cb{i});\n"
      args := args.push s!"cb{i}"
      continue
    if [`String.Internal.intercalate, `String.intercalate, `String.Internal.intercalateImpl, `String.Slice.intercalate].contains official &&
        dom.getAppFn.constName == `List then
      let slice := official == `String.Slice.intercalate
      let elem := if slice then `String.Slice else `String
      unless dom == mkApp (mkConst `List [.zero]) (mkConst elem) && a.ty == .tobject && b.ty == .tobject do
        throw <| IO.userError "invalid list of strings ABI"
      if slice then checkSliceLayout source strict
      IndexedNative.checkDataTypes source strict [`List]
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      let convert := if slice then s!"omega_map_list({arg}, omega_slice_to_lean)" else s!"omega_string_list_to_lean({arg})"
      prepare := prepare ++ s!"  lean_object *texts = {convert};\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      if a.borrow then cleanup := cleanup ++ "  lean_dec(texts);\n"
      args := args.push "texts"
      continue
    let charSeq := fun (t : Name) => mkApp (mkConst t [.zero]) (mkConst `Char)
    if basicStringFunction official && (dom == charSeq `List || dom == charSeq `Array) then
      let array := dom == charSeq `Array
      unless a.ty == (if array then .object else .tobject) && b.ty == .tobject do throw <| IO.userError s!"incorrect character sequence ABI at {n}"
      layout strict `Char
      IndexedNative.checkDataTypes source strict [`List]
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      let conversion := if array then s!"omega_char_array_to_lean({arg})" else s!"omega_map_list({arg}, omega_char_to_lean)"
      prepare := prepare ++ s!"  lean_object *chars{i} = {conversion};\n"
      args := args.push s!"chars{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(chars{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    let byteSearch := official == `ByteArray.findIdx?.loop || official == `ByteArray.findFinIdx?.loop
    if (official == `Nat.bitwise && i == 0) || (byteSearch && i == 1) then
      let bool := mkConst `Bool
      let .forallE _ left right _ := dom.consumeMData | throw <| IO.userError "invalid predicate"
      if byteSearch then
        layout strict `UInt8
        unless left == mkConst `UInt8 && right == bool do throw <| IO.userError "invalid byte predicate signature"
      else
        let .forallE _ middle out _ := right | throw <| IO.userError "invalid binary boolean predicate"
        unless left == bool && middle == bool && out == bool do throw <| IO.userError "invalid binary bit operation"
      let some strictInfo := strict.find? n | throw <| IO.userError "missing strict bit operation"
      let mut callbackTy := strictInfo.type
      for _ in [:i] do callbackTy := callbackTy.bindingBody!
      let .forallE _ callback _ _ := callbackTy | throw <| IO.userError "invalid strict callback type"
      unless callback == InitKernelPort.translate InitKernelPort.portName dom && a.ty == .object && b.ty == .object do
        throw <| IO.userError "strict callback uses an incompatible representation"
      for (name, tag) in [(`Bool.false, 0), (`Bool.true, 1)] do
        let some l := ctorLayoutExt.find? strict name | throw <| IO.userError s!"missing boolean layout: {name}"
        unless l.ctorInfo.cidx == tag && l.fieldInfo.isEmpty do throw <| IO.userError s!"invalid boolean layout: {name}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if !a.borrow && b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    if official == `BitVec.ofBoolListLE || official == `BitVec.ofBoolListBE then
      let some strictInfo := strict.find? n | throw <| IO.userError "missing strict Boolean list conversion"
      let .forallE _ strictList _ _ := strictInfo.type | throw <| IO.userError "invalid Boolean list conversion"
      let boolean := mkConst `Bool
      unless dom == mkApp (mkConst `List [.zero]) boolean && strictList == mkApp (mkConst `Omega.List [.zero]) boolean &&
          a.ty == .tobject && b.ty == .tobject && a.borrow do throw <| IO.userError "incorrect Boolean list ABI"
      for (env, list) in [(strict, `Omega.List), (source, `List)] do
        let some nil := ctorLayoutExt.find? env (list ++ `nil) | throw <| IO.userError "missing list nil layout"
        let some cons := ctorLayoutExt.find? env (list ++ `cons) | throw <| IO.userError "missing list cons layout"
        let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect list cons fields"
        unless nil.ctorInfo.cidx == 0 && nil.fieldInfo.isEmpty && cons.ctorInfo.cidx == 1 &&
            cons.ctorInfo.size == 2 && cons.ctorInfo.usize == 0 && cons.ctorInfo.ssize == 0 do
          throw <| IO.userError "incorrect Boolean list layout"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    let dom := dom.consumeMData
    let dom := if dom.isAppOfArity `optParam 2 then dom.getAppArgs[0]! else dom
    let syntaxArray := dom.getAppFn.constName == `Array &&
      [`Lean.Syntax, `Lean.TSyntax].contains (dom.getArg! 0).getAppFn.constName
    if errorString official && dom.isAppOfArity `Option 1 then
      unless (dom.getArg! 0).isConstOf `String && a.ty == .tobject && b.ty == .tobject do
        throw <| IO.userError "unexpected error detail type"
      IndexedNative.checkDataTypes source strict [`Option]
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_inc({arg});\n  lean_object *details = omega_optional_from_lean({arg}, omega_string_to_lean);\n"
      args := args.push "details"
      if a.borrow then cleanup := cleanup ++ "  lean_dec(details);\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      continue
    let dom := dom.getAppFn.constName
    if let some (w, t) := word? dom then
      layout strict dom
      unless a.ty == t && b.ty == .tobject do throw <| IO.userError s!"wrong word argument at {n} {i}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push s!"lean_{w}_of_nat({arg})"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if let some (f, t) := float? dom then
      checkFloatLayout strict dom
      unless a.ty == t && b.ty == .tobject do throw <| IO.userError s!"wrong float argument at {n} {i}"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push s!"omega_{f}_from_nat_bits({arg})"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Unit && a.ty == .tagged && b.ty == .tagged then
      decls := decls.push ("lean_obj_arg " ++ arg)
      args := args.push arg
    else if dom == `List && digitList official && a.ty == .tobject && b.ty == .tobject then
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *chars{i} = omega_convert_char_list({arg}, true);\n"
      args := args.push s!"chars{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(chars{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `List && official == `ByteArray.toList.loop && a.ty == .tobject && b.ty == .tobject then
      checkStrictString strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if a.borrow && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if [`Nat, `Fin, `BitVec, `String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom && a.ty == .tobject && b.ty == .tobject then
      if [`String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom then
        for (env, pos) in [(source, dom), (strict, `Omega ++ dom)] do
          let some (some field) := impureTrivialStructureInfoExt.find? env pos | throw <| IO.userError s!"missing position {pos}"
          unless field.fieldIdx == 0 do throw <| IO.userError s!"invalid offset field in {pos}"
      else if dom != `Nat then layout strict dom
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      args := args.push arg
      let borrowed := a.borrow || target == "lean_string_get_byte_fast"
      if b.borrow && !borrowed then prepare := prepare ++ s!"  lean_inc({arg});\n"
      if borrowed && !b.borrow then cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && (syntaxArray || [`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains dom) &&
        a.ty == .object && b.ty == .tobject then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *syntax_array{i} = omega_syntax_array_to_lean({arg});\n"
      args := args.push s!"syntax_array{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(syntax_array{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && dom == `Lean.SyntaxNodeKinds && a.ty == .tobject && b.ty == .tobject then
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *kinds{i} = omega_map_list({arg}, omega_name_to_lean);\n"
      args := args.push s!"kinds{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(kinds{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if syntaxTreeFunction official && [`Lean.Syntax, `Lean.TSyntax, `Lean.Syntax.Term, `Lean.Syntax.HexNum,
        `Lean.Syntax.HygieneInfo, `Lean.SourceInfo, `Lean.SyntaxNodeKind].contains dom &&
        a.ty == .tobject && b.ty == .tobject then
      let convert := if dom == `Lean.SourceInfo then s!"omega_convert_source_info({arg}, true)" else
        if dom == `Lean.SyntaxNodeKind then s!"omega_name_to_lean({arg})" else s!"omega_convert_syntax({arg}, true)"
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *input{i} = {convert};\n"
      args := args.push s!"input{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(input{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Lean.Name && a.ty == .tobject && b.ty == .tobject then
      checkNameLayout source strict
      hasName := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *name{i} = omega_name_to_lean({arg});\n"
      args := args.push s!"name{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(name{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `String.Slice && a.ty == .object && b.ty == .object then
      checkStrictString strict
      checkSliceLayout source strict
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *slice{i} = omega_slice_to_lean({arg});\n"
      args := args.push s!"slice{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(slice{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if [`String, `ByteArray, `System.FilePath].contains dom && a.ty == .object && b.ty == .tobject then
      if dom == `ByteArray then checkStrictBytes strict else checkStrictString strict
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      if dom == `System.FilePath then
        for (e, path) in [(source, dom), (strict, `Omega ++ dom)] do
          let some (some f) := impureTrivialStructureInfoExt.find? e path | throw <| IO.userError s!"expected one file path field {path}"
          unless f.fieldIdx == 0 do throw <| IO.userError s!"unexpected file path field {path}"
      let borrowed := a.borrow || target == "lean_string_get_byte_fast"
      if !borrowed then
        let update := dom == `ByteArray && ci.type.getForallBody.getAppFn.isConstOf `ByteArray
        let take := if update then "omega_bytes_native_owner" else if dom == `ByteArray then
          "omega_bytes_take_native" else "omega_string_take_native"
        if b.borrow then prepare := prepare ++ s!"  lean_inc({arg});\n"
        prepare := prepare ++ s!"  lean_object *alias{i};\n  lean_object *string{i} = {take}({arg}, &alias{i});\n"
        if update then
          if byteUpdate.isSome then throw <| IO.userError s!"ambiguous byte array update {n}"
          byteUpdate := some i
          prepare := prepare ++ s!"  uintptr_t original{i} = (uintptr_t)string{i};\n"
        cleanup := cleanup ++ s!"  if (alias{i}) lean_dec_ref(alias{i});\n"
      else
        let convert := if dom == `ByteArray then "omega_bytes_to_lean" else "omega_string_to_lean"
        prepare := prepare ++ s!"  lean_object *string{i} = {convert}({arg});\n"
        if borrowed then cleanup := cleanup ++ s!"  lean_dec(string{i});\n"
        unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
      args := args.push s!"string{i}"
    else if dom == `Substring.Raw && a.ty == .object && b.ty == .object then
      hasString := true
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *slice{i} = omega_convert_substring({arg}, omega_string_to_lean);\n"
      args := args.push s!"slice{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(slice{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Int && a.ty == .tobject && b.ty == .object then
      checkIntLayout strict
      decls := decls.push ((if b.borrow then "b_lean_obj_arg " else "lean_obj_arg ") ++ arg)
      prepare := prepare ++ s!"  lean_object *mag{i} = lean_ctor_get({arg}, 0);\n  lean_inc(mag{i});\n"
      prepare := prepare ++ s!"  lean_object *value{i} = lean_obj_tag({arg}) == 0 ? lean_nat_to_int(mag{i}) : lean_int_neg_succ_of_nat(mag{i});\n"
      args := args.push s!"value{i}"
      if a.borrow then cleanup := cleanup ++ s!"  lean_dec(value{i});\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({arg});\n"
    else if dom == `Bool && a.ty == .uint8 && b.ty == .uint8 then
      decls := decls.push ("uint8_t " ++ arg)
      args := args.push arg
    else throw <| IO.userError s!"unsupported argument of {n}: {dom}/{a.ty}/{b.ty}"
  let call := target ++ "(" ++ String.intercalate ", " args.toList ++ ")"
  let dom := type.consumeMData.getAppFn.constName
  let mut helper := ""
  let (output, value) ← if let some (w, t) := word? dom then do
    layout strict dom
    unless ret == t && result == .tobject do throw <| IO.userError s!"incorrect word result at {n}"
    pure ("lean_obj_res", s!"lean_{w}_to_nat({call})")
  else if dom == `Lean.Name && ret == .tobject && result == .tobject then do
    checkNameLayout source strict
    hasName := true
    prepare := prepare ++ s!"  lean_object *name = {call};\n"
    cleanup := cleanup ++ "  lean_dec(name);\n"
    pure ("lean_obj_res", "omega_name_from_lean(name)")
  else if dom == `Int then do
    checkIntLayout strict
    unless (ret == .tobject || ret == .tagged) && result == .object do throw <| IO.userError s!"incorrect integer result at {n}"
    prepare := prepare ++ s!"  lean_object *integer = {call};\n"
    cleanup := cleanup ++ "  lean_dec(integer);\n"
    pure ("lean_obj_res", "omega_int_from_lean(integer)")
  else if let some (f, t) := float? dom then do
    checkFloatLayout strict dom
    unless ret == t && result == .tobject do throw <| IO.userError s!"incorrect float result at {n}"
    pure ("lean_obj_res", s!"omega_{f}_to_nat_bits({call})")
  else if (float? official.getPrefix).isSome && official == official.getPrefix ++ `frExp then do
    let floatType := official.getPrefix
    unless type == mkApp2 (mkConst `Prod [.zero, .zero]) (mkConst floatType) (mkConst `Int) &&
        ret == .object && result == .object do throw <| IO.userError s!"unexpected fraction/exponent result at {n}"
    checkIntLayout strict
    for (env, ctor) in [(source, `Prod.mk), (strict, `Omega.Prod.mk)] do
      let some l := ctorLayoutExt.find? env ctor | throw <| IO.userError s!"missing {ctor}"
      let #[.object 0 _, .object 1 _] := l.fieldInfo | throw <| IO.userError s!"unexpected fields in {ctor}"
      unless l.ctorInfo.cidx == 0 && l.ctorInfo.size == 2 && l.ctorInfo.ssize == 0 && l.ctorInfo.usize == 0 do
        throw <| IO.userError s!"unexpected product layout at {ctor}"
    let width := if floatType == `Float32 then "float32" else "float"
    prepare := prepare ++ s!"  lean_object *parts = {call};\n"
    prepare := prepare ++ s!"  lean_object *bits = omega_{width}_to_nat_bits(lean_unbox_{width}(lean_ctor_get(parts, 0)));\n"
    prepare := prepare ++ "  lean_object *exponent = lean_ctor_get(parts, 1);\n  uint8_t neg = lean_int_lt(exponent, lean_box(0));\n"
    prepare := prepare ++ "  lean_object *mag = lean_nat_abs(exponent);\n  if (neg) { lean_object *pred = lean_nat_pred(mag); lean_dec(mag); mag = pred; }\n"
    prepare := prepare ++ "  lean_object *integer = lean_alloc_ctor(neg, 1, 0);\n  lean_ctor_set(integer, 0, mag);\n"
    prepare := prepare ++ "  lean_object *pair = lean_alloc_ctor(0, 2, 0);\n  lean_ctor_set(pair, 0, bits);\n  lean_ctor_set(pair, 1, integer);\n  lean_dec(parts);\n"
    pure ("lean_obj_res", "pair")
  else if dom == `Subtype && official == `System.Platform.getNumBits then do
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Subtype
      | throw <| IO.userError "missing platform width subtype layout"
    unless field.fieldIdx == 0 && ret == .tobject && result == .tobject do
      throw <| IO.userError "invalid platform width result ABI"
    pure ("lean_obj_res", call)
  else if official == `BitVec.instToString && dom == `ToString then do
    checkStrictString strict
    layout strict `BitVec
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.ToString
      | throw <| IO.userError "missing ToString dictionary representation"
    unless field.fieldIdx == 0 && ret == .object && result == .object do throw <| IO.userError "incorrect ToString dictionary ABI"
    hasString := true
    helper := "\nstatic lean_obj_res omega_bitvec_to_string(lean_obj_arg render, lean_obj_arg vector) {\n" ++
      "  lean_object *native = lean_apply_1(render, vector);\n  lean_object *bytes = omega_string_from_lean(native);\n" ++
      "  lean_dec(native);\n  return bytes;\n}\n"
    prepare := prepare ++ "  lean_object *closure = lean_alloc_closure((void *)omega_bitvec_to_string, 2, 1);\n"
    prepare := prepare ++ s!"  lean_closure_set(closure, 0, {call});\n"
    pure ("lean_obj_res", "closure")
  else if [`Substring.Raw, `String.Slice].contains dom && ret == .object && result == .object then do
    if dom == `String.Slice then checkSliceLayout source strict
    hasString := true
    prepare := prepare ++ s!"  lean_object *native_slice = {call};\n"
    cleanup := cleanup ++ "  lean_dec(native_slice);\n"
    pure ("lean_obj_res", "omega_convert_substring(native_slice, omega_string_from_lean)")
  else if [`String, `ByteArray].contains dom then do
    if dom == `ByteArray then checkStrictBytes strict else checkStrictString strict
    unless ret == .object && result == .tobject do throw <| IO.userError s!"incorrect string result at {n}"
    prepare := prepare ++ s!"  lean_object *native_string = {call};\n"
    cleanup := cleanup ++ "  lean_dec(native_string);\n"
    let value := if dom == `String then "omega_string_from_lean(native_string)" else if let some i := byteUpdate then
      s!"omega_bytes_finish_update(a{i}, original{i}, native_string)" else "omega_bytes_from_lean(native_string)"
    pure ("lean_obj_res", value)
  else if dom == `List && digitList official && ret == .tobject && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *digits = {call};\n"
    cleanup := cleanup ++ "  lean_dec(digits);\n"
    pure ("lean_obj_res", "omega_convert_char_list(digits, false)")
  else if dom == `List && official == `ByteArray.toList.loop && ret == .tobject && result == .tobject then do
    checkStrictString strict
    pure ("lean_obj_res", call)
  else if official == `String.utf8EncodeCharFast then do
    unless type == mkApp (mkConst `List [.zero]) (mkConst `UInt8) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect UTF-8 byte list ABI"
    layout strict `UInt8
    IndexedNative.checkDataTypes source strict [`List]
    -- A boxed UInt8 and a native Nat below 256 have the same tagged scalar representation.
    pure ("lean_obj_res", call)
  else if dom == `ByteArray.utf8DecodeChar?.FirstByte && ret == .uint8 && result == .uint8 then do
    IndexedNative.checkDataTypes source strict [dom]
    pure ("uint8_t", call)
  else if basicStringFunction official && [`Array, `List].contains dom then do
    let array := dom == `Array
    unless type == mkApp (mkConst dom [.zero]) (mkConst `Char) && ret == (if array then .object else .tobject) && result == .tobject do
      throw <| IO.userError s!"incorrect character sequence result at {n}"
    layout strict `Char
    IndexedNative.checkDataTypes source strict [`List]
    hasString := true
    prepare := prepare ++ s!"  lean_object *chars = {call};\n"
    cleanup := cleanup ++ "  lean_dec(chars);\n"
    pure ("lean_obj_res", if array then "omega_char_array_from_lean(chars)" else "omega_map_list(chars, omega_char_from_lean)")
  else if dom == `Option && (basicStringFunction official || basicStringExtern official || decodeStringFunction official) &&
      [`Char, `Array].contains (type.getArg! 0).getAppFn.constName then do
    let payload := type.getArg! 0
    let scalar := payload == mkConst `Char
    unless (scalar || payload == mkApp (mkConst `Array [.zero]) (mkConst `Char)) && ret == .tobject && result == .tobject do
      throw <| IO.userError s!"incorrect optional character ABI at {n}"
    layout strict `Char
    IndexedNative.checkDataTypes source strict [`Option]
    hasString := true
    prepare := prepare ++ s!"  lean_object *optional = {call};\n"
    pure ("lean_obj_res", "omega_optional_from_lean(optional, " ++ (if scalar then "omega_char_from_lean)" else "omega_char_array_from_lean)"))
  else if [`Lean.Name.escapePart, `System.Uri.fileUriToPath?].contains official then do
    let payload := if official == `Lean.Name.escapePart then `String else `System.FilePath
    unless type == mkApp (mkConst `Option [.zero]) (mkConst payload) && ret == .tobject && result == .tobject do
      throw <| IO.userError s!"incorrect optional text result {n}"
    IndexedNative.checkDataTypes source strict [`Option]
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_string_from_lean)")
  else if official == `String.Slice.toInt? then do
    unless type == mkApp (mkConst `Option [.zero]) (mkConst `Int) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect optional integer ABI"
    checkIntLayout strict
    IndexedNative.checkDataTypes source strict [`Option]
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_int_from_lean)")
  else if syntaxTreeFunction official && [`CoeOut, `CoeTail].contains dom && ret == .object && result == .object then do
    for (env, cls) in [(source, dom), (strict, `Omega ++ dom)] do
      let some (some field) := impureTrivialStructureInfoExt.find? env cls
        | throw <| IO.userError s!"missing syntax coercion layout {cls}"
      unless field.fieldIdx == 0 do throw <| IO.userError s!"invalid syntax coercion field {cls}"
    let arrayLike (t : Expr) := [`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains t.getAppFn.constName ||
      (t.isAppOfArity `Array 1 && (t.getArg! 0).isConstOf `Lean.Syntax)
    unless type.getAppNumArgs == 2 && type.getAppArgs.all arrayLike do throw <| IO.userError "unexpected syntax coercion endpoints"
    prepare := prepare ++ "  lean_object *coerce = lean_alloc_closure((void *)omega_syntax_array_coe, 2, 1);\n"
    prepare := prepare ++ s!"  lean_closure_set(coerce, 0, {call});\n"
    pure ("lean_obj_res", "coerce")
  else if syntaxTreeFunction official && ([`Lean.TSyntaxArray, `Lean.Syntax.TSepArray].contains dom ||
      (dom == `Array && (type.getArg! 0).isConstOf `Lean.Syntax)) && ret == .object && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *values = {call};\n"
    cleanup := cleanup ++ "  lean_dec(values);\n"
    pure ("lean_obj_res", "omega_syntax_array_from_lean(values)")
  else if syntaxTreeFunction official && [`Lean.Syntax.Ident, `Lean.Syntax.Term, `Lean.TSyntax].contains dom && ret == .tobject && result == .tobject then do
    prepare := prepare ++ s!"  lean_object *stx = {call};\n"
    cleanup := cleanup ++ "  lean_dec(stx);\n"
    pure ("lean_obj_res", "omega_syntax_from_lean(stx)")
  else if syntaxTreeFunction official && dom == `Option && ret == .tobject && result == .tobject then do
    let payload := type.getArg! 0
    let converter ← if payload == mkConst `String then pure "omega_string_from_lean"
      else if payload == mkConst `Lean.Syntax then pure "omega_syntax_from_lean"
      else throw <| IO.userError s!"unexpected syntax query payload at {n}"
    pure ("lean_obj_res", s!"omega_optional_from_lean({call}, {converter})")
  else if metaLiteralFunction official && dom == `Option && ret == .tobject && result == .tobject then do
    IndexedNative.checkDataTypes source strict [`Option]
    let payload := type.getArg! 0
    if payload == mkConst `String then
      pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_string_from_lean)")
    else if payload == mkConst `Lean.Name then
      checkNameLayout source strict
      hasName := true
      pure ("lean_obj_res", s!"omega_optional_from_lean({call}, omega_name_from_lean)")
    else if payload == mkConst `Nat then pure ("lean_obj_res", call)
    else
      let pair := fun a b => mkApp2 (mkConst `Prod [.zero, .zero]) a b
      unless payload == pair (mkConst `Nat) (pair (mkConst `Bool) (mkConst `Nat)) do
        throw <| IO.userError s!"unexpected literal payload at {n}"
      IndexedNative.checkDataTypes source strict [`Prod, `Bool]
      pure ("lean_obj_res", call)
  else if official == `Lean.Syntax.splitNameLit then do
    unless type == mkApp (mkConst `List [.zero]) (mkConst `Substring.Raw) && ret == .tobject && result == .tobject do
      throw <| IO.userError "incorrect raw name component ABI"
    IndexedNative.checkDataTypes source strict [`List]
    prepare := prepare ++ s!"  lean_object *components = {call};\n"
    cleanup := cleanup ++ "  lean_dec(components);\n"
    pure ("lean_obj_res", "omega_map_list(components, omega_substring_from_lean)")
  else if dom == `Option && basicStringFunction official then do
    let pos := type.getArg! 0 |>.getAppFn.constName
    unless [`String.Pos, `String.Slice.Pos].contains pos && ret == .tobject && result == .tobject do
      throw <| IO.userError s!"incorrect optional position ABI at {n}"
    for (env, ns) in [(source, Name.anonymous), (strict, `Omega)] do
      for t in [pos, `String.Pos.Raw] do
        let some (some f) := impureTrivialStructureInfoExt.find? env (ns ++ t) | throw <| IO.userError s!"missing position {t}"
        unless f.fieldIdx == 0 do throw <| IO.userError s!"invalid offset layout at {t}"
    IndexedNative.checkDataTypes source strict [`Option]
    pure ("lean_obj_res", call)
  else if dom == `Option && [`ByteArray.findIdx?.loop, `ByteArray.findFinIdx?.loop].contains official &&
      ret == .tobject && result == .tobject then do
    layout strict `Fin
    for (env, opt) in [(source, `Option), (strict, `Omega.Option)] do
      let some nil := ctorLayoutExt.find? env (opt ++ `none) | throw <| IO.userError "missing optional index layout"
      let some val := ctorLayoutExt.find? env (opt ++ `some) | throw <| IO.userError "missing optional index layout"
      let #[.object 0 _] := val.fieldInfo | throw <| IO.userError "incorrect optional index layout"
      unless nil.ctorInfo.cidx == 0 && nil.fieldInfo.isEmpty && val.ctorInfo.cidx == 1 && val.ctorInfo.size == 1 do
        throw <| IO.userError "incorrect optional index constructor"
    pure ("lean_obj_res", call)
  else if dom == `BitVec && ret == .tobject && result == .tobject then do
    layout strict dom
    pure ("lean_obj_res", call)
  else if [`String.Pos.Raw, `String.Pos, `String.Slice.Pos].contains dom && (ret == .tobject || ret == .tagged) && result == .tobject then do
    let some (some field) := impureTrivialStructureInfoExt.find? strict (`Omega ++ dom) | throw <| IO.userError "missing raw position"
    unless field.fieldIdx == 0 do throw <| IO.userError "invalid raw position layout"
    pure ("lean_obj_res", call)
  else if dom == `Nat && (ret == .tobject || ret == .tagged) && result == .tobject then pure ("lean_obj_res", call)
  else if (debugPrimitive official || rawFold official) && type == .bvar (params.size - 1) && ret == .tobject && result == .tobject then
    pure ("lean_obj_res", call)
  else if dom == `Ordering && ret == .uint8 && result == .uint8 then do
    IndexedNative.checkDataTypes source strict [`Ordering]
    pure ("uint8_t", call)
  else if [`Bool, `Decidable].contains dom && ret == .uint8 && result == .uint8 then pure ("uint8_t", call)
  else throw <| IO.userError s!"unsupported result of {n}: {dom}/{ret}/{result}"
  let proto ← if usesPinnedFunction official || usesStringExport official then do
    let ctype (t : IR.IRType) : IO String := match t with
      | .uint8 => pure "uint8_t"
      | .uint16 => pure "uint16_t"
      | .uint32 => pure "uint32_t"
      | .uint64 => pure "uint64_t"
      | .usize => pure "size_t"
      | .object | .tobject | .tagged | .erased => pure "lean_object *"
      | _ => throw <| IO.userError s!"unexpected C type at {official}: {t}"
    let inputs ← (params.filter fun p => p.ty != .erased || passesErased).mapM fun p => ctype p.ty
    pure s!"\nextern {← ctype ret} {target}({String.intercalate ", " inputs.toList});\n"
  else if (float? official.getPrefix).isSome || (float? dom).isSome then do
    let header := "\n#include \"float_bits.h\"\n"
    if target.startsWith "lean_" then pure header else
      let ty := if ret == .float then "double" else "float"
      unless (ret == .float || ret == .float32) && params.all (·.ty == ret) do
        throw <| IO.userError s!"unexpected math library signature {target}"
      pure <| header ++ s!"extern {ty} {target}({String.intercalate ", " (List.replicate params.size ty)});\n"
  else if official == `Lean.getGithash then pure s!"\nextern lean_obj_res {target}(lean_obj_arg);\n"
  else if official == `Lean.Internal.hasLLVMBackend then pure s!"\nextern uint8_t {target}(lean_obj_arg);\n"
  else if [`System.Platform.getIsWindows, `System.Platform.getIsOSX, `System.Platform.getIsLinux,
      `System.Platform.getIsEmscripten, `System.Platform.Internal.getHardwareConcurrency].contains official then
    let t := if ret == .uint8 then "uint8_t" else "uint32_t"
    pure s!"\nextern {t} {target}(lean_obj_arg);\n"
  else if target == "lean_dbg_stack_trace" then
    pure "\nextern lean_obj_res lean_dbg_stack_trace(lean_obj_arg);\n"
  else if target == "lean_string_utf8_get_opt" then
    pure "\nextern lean_obj_res lean_string_utf8_get_opt(b_lean_obj_arg, b_lean_obj_arg);\n"
  else if target == "lean_string_utf8_get_bang" then
    pure "\nextern uint32_t lean_string_utf8_get_bang(b_lean_obj_arg, b_lean_obj_arg);\n"
  else if target == "lean_string_utf8_extract_fast" then
    pure "\nextern lean_obj_res lean_string_utf8_extract_fast(b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg);\n"
  else if official == `ByteArray.copySlice then
    pure "\nextern lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, uint8_t);\n"
  else if official == `System.Platform.getNumBits then
    pure "\nextern lean_obj_res lean_system_platform_nbits(lean_obj_arg);\n" else pure ""
  let header := if syntaxTreeFunction official then "\n#include \"strict_syntax.h\"\n" else if hasName then "\n#include \"strict_name.h\"\n" else if hasString || [`String, `ByteArray].contains dom then "\n#include \"strict_string.h\"\n" else if dom == `Int then "\n#include \"strict_nat.h\"\n" else ""
  return header ++ proto ++ helper ++ s!"\nLEAN_EXPORT {output} {adapter}({String.intercalate ", " decls.toList}) \{\n{prepare}  {output} r = {value};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.WordNative
