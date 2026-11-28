module
import all Lean.Environment
import all Lean.Structure
import OmegaChecks.InitCompiler.StructuralEquations
meta import OmegaChecks.InitCompiler.StructuralEquations
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.ImplementedByAttr
meta import OmegaChecks.InitPort.FloatArrayNative
import OmegaChecks.InitPort.FloatArrayNative
meta import OmegaChecks.InitPort.WordNative
import OmegaChecks.InitPort.WordNative
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.UnsafeRuntime
meta import OmegaChecks.InitPort.UnsafeRuntime

/-! Compile an existing strict owner directly from its checked kernel definitions. -/

open Lean Compiler LCNF OmegaChecks.InitPort.NativeState

namespace GeneratedNative

/-- A pinned partial definition has a safe opaque face and a separate compiler-only recursion.
Keep its original fallback in the kernel and translate the executable code on the strict types. -/
private def pinnedPartialCode? (source : Environment) (ci : ConstantInfo) : Option DefinitionVal := do
  let .opaqueInfo dst := ci | none
  let sourceName := InitKernelPort.originalName dst.name
  guard (sourceName.getRoot != `Omega && InitKernelPort.portName sourceName == dst.name &&
    !isExtern source sourceName && (Compiler.getImplementedBy? source sourceName).isNone)
  let some (.opaqueInfo src) := source.find? sourceName | none
  let recName := Compiler.mkUnsafeRecName src.name
  let some (.defnInfo d) := source.find? recName | none
  let translate := InitKernelPort.translate InitKernelPort.portName
  guard (source.getModuleIdxFor? recName == source.getModuleIdxFor? sourceName &&
    !src.isUnsafe && !dst.isUnsafe && d.safety == DefinitionSafety.partial && d.all == [recName] &&
    src.levelParams == dst.levelParams && d.levelParams == dst.levelParams &&
    translate src.type == dst.type && translate d.type == dst.type && translate src.value == dst.value)
  let name := Compiler.mkUnsafeRecName dst.name
  let value := (translate d.value).replace fun e => if e.isConstOf name then some (.const dst.name e.constLevels!) else none
  return {d with name, all := [name], type := dst.type, value, safety := .safe}

private def pinnedRecursion? (source : Environment) (strictName : Name) : Option DefinitionVal := do
  let recName := Compiler.mkUnsafeRecName (InitKernelPort.originalName strictName)
  let some (.defnInfo code) := source.find? recName | none
  guard (code.safety == .partial && code.all == [recName])
  return code

private partial def dependencies (source env : Environment) (partialCode : NameMap DefinitionVal)
    (localNames : NameSet) (n : Name) : StateM NameSet (Array Name) := do
  if !(localNames.contains n) || (← get).contains n then return #[]
  modify (·.insert n)
  let some ci := env.find? n | return #[]
  let some body := (partialCode.find? n).map (·.value) <|> ci.value? (allowOpaque := true) | return #[]
  let mut prior := #[]
  let mut callees := ci.type.getUsedConstants ++ body.getUsedConstants
  -- The native structural fallback may call a matcher absent from the total kernel body.
  if let some code := pinnedRecursion? source n then
    callees := callees ++ (code.value.getUsedConstants.map InitKernelPort.portName)
  for dep in callees do
    prior := prior ++ (← dependencies source env partialCode localNames dep)
  return prior.push n

/-- A constructor can contain another inductive from the same owner. Defer its layout
until the compiler has installed the referenced representation. -/
private partial def compileLayoutsInOrder (groups : Array InductiveVal) : CoreM Unit := do
  let mut deferred := #[]
  let mut reasons := #[]
  for group in groups do
    let before ← Core.saveState
    try
      if group.name == `Omega.String then OmegaChecks.InitPort.NativeState.prepareStringLayout
      (← compileDeclsRef.get) group.all.toArray {}
      if group.name == `Omega.String then OmegaChecks.InitPort.NativeState.finishStringLayout
      for name in group.all do
        unless (monoTypeExt.find? (← getEnv) name).isSome do throwError "no compiled layout for {name}"
    catch ex =>
      before.restore
      deferred := deferred.push group
      reasons := reasons.push (group.name, ← ex.toMessageData.toString)
  if deferred.isEmpty then return
  if deferred.size < groups.size then compileLayoutsInOrder deferred
  else for (name, reason) in reasons do IO.println s!"missing layout {name}: {reason}"

/-- Use the published strict calling conventions of runtime operands before boxing higher-order calls. -/
private def missingRuntimeDependency (source : Environment) (n : Name) (recursive : Name := .anonymous) : CoreM Bool := do
  let some body := (← getEnv).find? n >>= (·.value?) | return false
  let mut missing : NameSet := {}
  let env ← getEnv
  for dep in body.getUsedConstants do
    if dep == recursive then continue
    -- Constructor applications lower directly using the owning inductive's strict layout.
    if let some (.ctorInfo ctor) := env.find? dep then
      if (monoTypeExt.find? env ctor.induct).isSome then continue
    let original := InitKernelPort.originalName dep
    if (isExtern source original || (getImplementedBy? source original).isSome ||
        (getSigCore? source impureSigExt original).isSome) &&
        (← getImpureSignature? dep).isNone then
      missing := missing.insert dep
  if missing.isEmpty then return false
  -- The compiler has erased proof arguments and types in the executable let-values.
  let before ← Core.saveState
  try
    let decl ← CompilerM.run (toDecl n)
    let visit : StateM Bool Unit := decl.value.forCodeM fun (root : Code .pure) => root.forM fun (code : Code .pure) => do
      if let .let binding _ := code then
        if let .const dep .. := binding.value then
          if missing.contains dep then modify fun _ => true
    return (visit.run false).2
  catch _ =>
    return true
  finally
    before.restore

/-- Install one checked unfolding equation for code generation. Only native compiler
extensions are written to the product, so its kernel definition stays in the original owner. -/
private def compileEquation (source : Environment) (n : Name) (d : DefinitionVal) : CoreM Unit := do
  Lean.addDecl (.defnDecl d) (forceExpose := true)
  if ← missingRuntimeDependency source d.name n then throwError "uncompiled recursive equation dependency of {n}"
  modifyEnv (noncomputableExt.modifyState · (·.erase n))
  modifyEnv fun env => privateConstKindsExt.insert env n .defn
  (← compileDeclsRef.get) #[n] {}

/-- The accessibility proof used by the kernel is erased at runtime. Take the executable
unfolding directly from the axiom-free strict fixpoint equation. -/
private def compileFix (source strict : Environment) (n eqName : Name) : CoreM Unit := do
  let some (.defnInfo d) := strict.find? n | throwError "missing fixpoint {n}"
  let some (.thmInfo _) := strict.find? eqName | return
  let levels := d.levelParams.map Level.param
  let body ← withEnv strict <| Meta.MetaM.run' <| Meta.forallTelescope d.type fun args _ => do
    let proof := mkAppN (mkConst eqName levels) args
    let .ok eq := Kernel.check strict (← getLCtx) proof | throwError "invalid fixpoint equation"
    let some (_, lhs, rhs) := eq.eq? | throwError "expected a fixpoint equation"
    unless Kernel.isDefEqGuarded strict (← getLCtx) lhs (mkAppN (mkConst n levels) args) do
      throwError "unexpected left-hand side of {eqName}"
    Meta.mkLambdaFVars args rhs
  let name := Compiler.mkUnsafeRecName n
  compileEquation source n {d with name, all := [name], value := body, safety := .safe}

/-- Lower a saturated natural recursor on the last lambda parameter to a single constructor
split. The successor branch calls the original function at its predecessor. -/
private def compileNatRec (source strict : Environment) (d : DefinitionVal) : CoreM Unit := do
  let name := Compiler.mkUnsafeRecName d.name
  let body ← withEnv strict <| Meta.MetaM.run' <| Meta.lambdaTelescope d.value fun args rhs => do
    unless rhs.isAppOfArity `Nat.rec 4 && args.back? == some rhs.appArg! do throwError "expected natural recursion"
    let #[motive, base, step, fuel] := rhs.getAppArgs | throwError "invalid natural recursor"
    let self := mkAppN (mkConst d.name (d.levelParams.map Level.param)) args.pop
    let next ← Meta.withLocalDeclD `k (mkConst `Nat) fun k =>
      Meta.mkLambdaFVars #[k] (mkApp2 step k (mkApp self k))
    let body ← Meta.mkLambdaFVars args (mkApp4 (mkConst `Nat.casesOn rhs.getAppFn.constLevels!) motive fuel base next)
    OmegaChecks.InitCompiler.checkConstructorEquations d.name d.levelParams d.type body (args.size - 1)
    return body
  compileEquation source d.name {d with name, all := [name], value := body, safety := .safe}

/-- Compile the natural recursor under a temporary callable name. Both constructor
equations are checked on its alias and every caller is definitionally equal after unfolding. -/
private def compileRecursorCall (source strict : Environment) (d : DefinitionVal) : CoreM Unit := do
  let helper := d.name ++ `_nativeNatRec
  let some (.recInfo recInfo) := strict.find? `Nat.rec | return
  let levels := recInfo.levelParams.map Level.param
  let value ← withEnv strict <| Meta.MetaM.run' <| Meta.forallTelescope recInfo.type fun args _ =>
    Meta.mkLambdaFVars args (mkAppN (mkConst `Nat.rec levels) args)
  let alias : DefinitionVal := {
    name := helper, levelParams := recInfo.levelParams, type := recInfo.type, value := value
    hints := .regular 1, safety := .safe, all := [helper] }
  let .ok checked := strict.addDeclCore 0 4096 (.defnDecl alias) none | throwError "invalid natural recursor alias"
  let body := d.value.replace fun e => if e.isConstOf `Nat.rec then some (mkConst helper e.constLevels!) else none
  unless Kernel.isDefEqGuarded checked {} d.value body do throwError "natural recursor alias changed {d.name}"
  Lean.addDecl (.defnDecl alias) (forceExpose := true)
  compileNatRec source checked alias
  let name := Compiler.mkUnsafeRecName d.name
  compileEquation source d.name {d with name, all := [name], value := body, safety := .safe}

private def compileDirectRecursor (source strict : Environment) (d : DefinitionVal) : CoreM Unit := do
  let body ← withEnv strict <| Meta.MetaM.run' <| OmegaChecks.InitCompiler.directRecursorEquation d
  let name := Compiler.mkUnsafeRecName d.name
  compileEquation source d.name {d with name, all := [name], value := body, safety := .safe}

/-- A recursive eliminator also performs plain case analysis when a branch ignores all
its induction hypotheses. Retain the constructor fields and all outer variable bindings. -/
private def withoutHypotheses (branch : Expr) : Nat → Nat → Option Expr
  | _, 0 => some branch
  | fields + 1, count => do
    let .lam name domain body info := branch | none
    return .lam name domain (← withoutHypotheses body fields count) info
  | 0, count + 1 => do
    let .lam _ _ body _ := branch | none
    if body.hasLooseBVar 0 then none else withoutHypotheses (body.lowerLooseBVars 1 1) 0 count

/-- Reorder the arguments of an unindexed eliminator that only examines constructors.
Validate the changed term against the full original kernel definition. -/
private def compileCases (source strict : Environment) (d : DefinitionVal) : CoreM Unit := do
  let body := d.value.replace fun e => do
    let .const recName levels := e.getAppFn | none
    let some (.recInfo r) := strict.find? recName | none
    unless r.numIndices == 0 && r.numMotives == 1 && e.getAppNumArgs > r.getMajorIdx do none
    let indName := r.getMajorInduct
    let some (.inductInfo ind) := strict.find? indName | none
    unless !ind.isNested && ind.all == [indName] && recName == indName ++ `rec do none
    let casesName := indName ++ `casesOn
    unless strict.contains casesName do none
    let args := e.getAppArgs
    let n := r.getMajorIdx
    let m := r.getFirstMinorIdx
    let mut branches := args[m:n].toArray
    if ind.isRec then
      unless r.rules.length == branches.size do none
      for rule in r.rules, i in [:branches.size] do
        let arity := rule.rhs.getLambdaBody.getAppNumArgs
        unless rule.nfields <= arity do none
        branches := branches.set! i (← withoutHypotheses branches[i]! rule.nfields (arity - rule.nfields))
    return mkAppN (mkConst casesName levels) (args[:m].toArray.push args[n]! ++ branches ++ args[n+1:].toArray)
  if body == d.value then return
  unless Kernel.isDefEqGuarded strict {} d.value body do return
  let name := Compiler.mkUnsafeRecName d.name
  compileEquation source d.name {d with name, all := [name], value := body, safety := .safe}

/-- Reuse the pinned executable recursion only after the kernel identifies every constructor
equation with the checked total function. The temporary declaration is excluded from the product. -/
private def compilePinnedRecursion (source strict : Environment) (n : Name) : CoreM Bool := do
  let some d := pinnedRecursion? source n | return false
  let name := InitKernelPort.portName d.name
  let raw := InitKernelPort.translate InitKernelPort.portName d.value
  let body := raw.replace fun e => if e.isConstOf name then some (.const n e.constLevels!) else none
  let type := InitKernelPort.translate InitKernelPort.portName d.type
  unless body.getUsedConstants.all strict.contains && type.getUsedConstants.all strict.contains do return false
  for i in [:type.getForallArity] do
    try
      withEnv strict <| Meta.MetaM.run' <| OmegaChecks.InitCompiler.checkConstructorEquations n d.levelParams type body i
    catch _ => continue
    let tmp := {d with name, all := [name], type, value := body, safety := .safe}
    compileEquation source n tmp
    return true
  return false

private def compileStructural (source strict : Environment) (n : Name) : CoreM Unit := do
  let before ← Core.saveState
  try
    if ← compilePinnedRecursion source strict n then return
  catch _ => before.restore
  if let some (.defnInfo d) := strict.find? n then
    try
      compileDirectRecursor source strict d
      return
    catch _ => before.restore
    if d.value.getUsedConstants.contains `Nat.rec then compileRecursorCall source strict d
    else compileCases source strict d

/-- The pinned boxing pass expects signatures for every call left after inlining and
specialization. In a partial Init product an imported callee can still be unavailable. -/
private def checkCallSignatures : Pass := Pass.mkPerDeclaration `checkCallSignatures .impure fun decl => do
  decl.value.forCodeM fun root => root.forM fun code => do
    if let .let binding _ := code then
      match binding.value with
      | .fap callee _ | .pap callee _ =>
        unless (← getImpureSignature? callee).isSome do
          throwError "missing compiled callee {callee} in {decl.name}"
      | _ => pure ()
  return decl

/-- Supply the two pinned borrowed parameters before Lean infers ownership and emits reference counts. -/
private def listPointerBorrows : Pass := Pass.mkPerDeclaration `listPointerBorrows .impure fun decl => do
  if decl.name != `Omega.ptrEqList then return decl
  let #[type, xs, ys] := decl.params | throwError "unexpected list comparison arity"
  return {decl with params := #[type, ← xs.updateBorrow true, ← ys.updateBorrow true]}

private def compileOwner (source : Environment) (partialCode : NameMap DefinitionVal) (groups : Array InductiveVal) (words order : Array Name) : CoreM Unit := do
  let strict ← getEnv
  let manager ← PassInstaller.run (← getPassManager)
    (.installBefore .impure `explicitBoxing (fun _ => checkCallSignatures))
  let manager ← if order.contains `Omega.ptrEqList then do
    unless OmegaChecks.InitPort.PointerComparison.hasBorrowedABI source `ptrEqList false do
      throwError "unexpected pinned list comparison ownership"
    PassInstaller.run manager (.installBefore .impure `inferBorrow (fun _ => listPointerBorrows))
  else pure manager
  modifyEnv fun env => passManagerExt.setState env ((passManagerExt.getState env).1, manager)
  -- ToLCNF replaces nested proofs with this marker while inferring erased argument types.
  -- Only compiler extensions are serialized. Check equations in the original environment.
  let some (.axiomInfo marker) := source.find? `lcProof | throwError "missing pinned proof erasure marker"
  unless marker.isUnsafe && !strict.contains marker.name do throwError "unexpected proof erasure marker"
  Lean.addDecl (.axiomDecl marker)
  -- Init.LetFun imports no Prelude. Its universe-polymorphic argument and result
  -- need the compiler's boxed and erased type markers while lowering its checked term.
  if order.contains `Omega.letFun then
    for name in [`lcErased, `lcAny] do
      unless strict.contains name do
        let type := mkSort (.succ .zero)
        let some (.axiomInfo decl) := source.find? name | throwError "missing compiler type marker {name}"
        unless decl.isUnsafe && decl.type == type && decl.levelParams.isEmpty do
          throwError "unexpected compiler type marker {name}"
        Lean.addDecl (.opaqueDecl {name, levelParams := [], type, value := mkSort .zero, isUnsafe := false, all := [name]})
  let newFloatArray := groups.any (·.name == `Omega.FloatArray) && words.contains `Omega.FloatArray.mk
  if newFloatArray then OmegaChecks.InitPort.FloatArrayNative.prepareLayout
  compileLayoutsInOrder groups
  if newFloatArray then OmegaChecks.InitPort.FloatArrayNative.finishLayout
  OmegaChecks.InitPort.WordNative.install words
  for n in order do
    if let some code := partialCode.find? n then
      let before ← Core.saveState
      try
        compileEquation source n code
      catch e =>
        IO.println s!"cannot compile pinned partial definition {n}: {← e.toMessageData.toString}"
        before.restore
      continue
    if n == `Thunk.fn then
      -- Raw builtin projections lower back to the named field. Use the pinned
      -- fnImpl computation so the named field forces the memoized value once.
      let some (.defnInfo field) := strict.find? n | throwError "missing thunk field"
      let some (.defnInfo impl) := strict.find? `Omega.Thunk.fnImpl | throwError "missing thunk getter implementation"
      let value := impl.value.instantiateLevelParams impl.levelParams (field.levelParams.map Level.param)
      unless Kernel.isDefEqGuarded strict {} field.value value do throwError "incorrect thunk field implementation"
      let name := Compiler.mkUnsafeRecName n
      compileEquation source n {field with name, all := [name], value, safety := .safe}
      continue
    if n == `Omega.Lean.RArray.get && (← getImpureSignature? `Omega.Lean.RArray.getImpl).isSome then
      let impl := `Omega.Lean.RArray.getImpl
      let some (.defnInfo d) := strict.find? n | throwError "missing reflected array lookup"
      let value := mkConst impl (d.levelParams.map Level.param)
      unless Kernel.isDefEqGuarded strict {} (mkConst n (d.levelParams.map Level.param)) value do
        throwError "reflected array lookup differs from its strict implementation"
      let name := Compiler.mkUnsafeRecName n
      compileEquation source n {d with name, all := [name], value, safety := .safe}
      continue
    if [`Omega.Lean.Grind.CommRing.Poly.combineC, `Omega.Lean.Grind.CommRing.Poly.denote'.go,
        `Omega.Lean.Grind.Linarith.Poly.combine, `Omega.Lean.Grind.Linarith.Poly.denote'.go].contains n then
      let before ← Core.saveState
      try
        compileFix source strict n (n ++ `eq_def)
        if (← getImpureSignature? n).isSome then continue
      catch _ => pure ()
      before.restore
    if n == `Omega.WellFounded.fix || n == `Omega.WellFounded.fixF then
      compileFix source strict n (n.appendAfter "_eq")
      continue
    if n == `Omega.WellFounded.Nat.fix.go then
      let some (.defnInfo d) := strict.find? n | throwError "missing natural fixpoint recursion"
      compileNatRec source strict d
      continue
    if OmegaChecks.InitPort.EffectRun.names.contains (InitKernelPort.originalName n) then
      let some kind := getInlineAttribute? source (InitKernelPort.originalName n)
        | throwError "missing pinned effect-runner inlining policy for {n}"
      let expected := if n == `Omega.unsafeBaseIO then .noinline else .inline
      unless kind == expected do throwError "unexpected pinned effect-runner inlining policy for {n}"
      setEnv (← ofExcept (setInlineAttribute (← getEnv) n kind))
      modifyEnv fun env => privateConstKindsExt.insert env n .defn
      let opts := if n == `Omega.unsafeBaseIO then ({} : Options).setBool `compiler.extract_closed false else {}
      (← compileDeclsRef.get) #[n] opts
      unless (← CompilerM.run (getLocalDeclAt? n .impure)).isSome do throwError "missing effect-runner code for {n}"
      continue
    let recursive := if n == `Omega.ptrEqList then n else Name.anonymous
    if ← missingRuntimeDependency source n recursive then continue
    let before ← Core.saveState
    try
      modifyEnv fun env => privateConstKindsExt.insert env n .defn
      (← compileDeclsRef.get) #[n] {}
      -- Type aliases and proof-only definitions have no executable declaration.
      unless (← CompilerM.run (getLocalDeclAt? n .impure)).isSome do before.restore
    catch _ =>
      before.restore
      try
        compileStructural source strict n
        unless (← CompilerM.run (getLocalDeclAt? n .impure)).isSome do before.restore
      catch _ =>
        before.restore

  let compiled ← getEnv
  if (IR.collectUsedDecls compiled (IR.getDecls compiled)).contains marker.name then
    throwError "proof erasure marker survived in runtime code"

/-- The strict array is a record containing a list. Compile its safe reference definitions
for indexing, updates and effectful traversals on that representation. -/
private def arrayDefinition (n : Name) : Bool :=
  [`Array.set, `Array.uget, `Array.uset, `Array.usize, `Array.pop, `Array.replicate,
   `Array.swap, `Array.swapIfInBounds, `Array.forIn', `Array.mapFinIdxM, `Array.mapM, `Array.modifyM,
   `Array.foldlM, `Array.foldrM, `Array.anyM,
   `FloatArray.data, `FloatArray.emptyWithCapacity, `FloatArray.push, `FloatArray.size, `FloatArray.usize,
   `FloatArray.uget, `FloatArray.get, `FloatArray.uset, `FloatArray.set, `FloatArray.forIn,
   `FloatArray.foldlM].contains n

/-- Use ordinary module initialization so closed functions and imported modules are ready before calls. -/
private def emitOwner (env : Environment) (owner : Name) (imports : Array Import)
    (ctx : Core.Context) (out : System.FilePath) : IO Unit := do
  let kernel := env.toKernelEnv
  let cenv := Environment.ofKernelEnv {kernel with header.imports := imports, header.isModule := true}
  let cenv := (externAttr.ext.setState cenv (externAttr.ext.getState env)).setModulePackage env.getModulePackage?
  IO.FS.createDirAll out.parent.get!
  IO.FS.writeFile out (← (emitC owner).toIO' ctx {env := cenv})

private unsafe def install (source publicSource : Environment) (lib out : System.FilePath) (owner : Name)
    (onlyLayouts mixed : Bool) : IO Unit := do
  let env ← importModules #[{module := owner, importAll := true}] {}
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"unknown owner {owner}"
  let path := modToFilePath lib owner "olean"
  let raw ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
  let parts := raw.map (·.1)
  let part := parts[2]!
  let oldNative := NameSet.ofList ((impureSigExt.getModuleEntries env idx).map (·.name)).toList
  let onlyLayouts := onlyLayouts || (!mixed && !oldNative.isEmpty)
  let mut groups := #[]
  let mut locals := #[]
  let mut candidates := #[]
  let mut partialCode : NameMap DefinitionVal := {}
  let mut words := #[]
  -- These eager word cardinalities require 65,536 through 2^64 successor cells
  -- when a detached seed uses a separately defined unary Nat.
  let unaryNat := (env.find? `Omega.Nat).any (· matches .inductInfo _)
  let largeWordSizes := [`UInt16.size, `UInt32.size, `UInt64.size, `USize.size]
  let floatArray := owner == `OmegaInit.Data.FloatArray.Basic && !unaryNat &&
    (OmegaChecks.InitPort.FloatArrayNative.boxed env || (monoTypeExt.find? env `Omega.FloatArray).isNone)
  for ci in part.constants do
    if !onlyLayouts && !unaryNat && !oldNative.contains ci.name &&
        (!ci.isUnsafe || OmegaChecks.InitPort.UnsafeRuntime.isOriginal ci true) && !ci.isPartial &&
        OmegaChecks.InitPort.WordNative.supported source owner (InitKernelPort.originalName ci.name) floatArray then
      words := words.push ci.name
      continue
    match ci with
    | .inductInfo i =>
      if i.all.head? != some i.name then continue
      let mut family := #[]
      let mut hasLayout := false
      let mut missing := false
      for name in i.all do
        let some (.inductInfo member) := env.find? name | throw <| IO.userError s!"missing inductive {name}"
        family := family ++ #[name] ++ member.ctors.toArray
        if (monoTypeExt.find? env name).isSome then hasLayout := true else missing := true
      if missing && hasLayout then throw <| IO.userError s!"partially compiled mutual inductive {i.name}"
      if missing then
        groups := groups.push i
        locals := locals ++ family
    | .opaqueInfo dst =>
      if !onlyLayouts && !oldNative.contains ci.name then
        if let some d := pinnedPartialCode? source ci then
          candidates := candidates.push ci.name
          partialCode := partialCode.insert ci.name d
        else
          let official := InitKernelPort.originalName ci.name
          if let some (.opaqueInfo src) := source.find? official then
            if let some (.fdecl _ #[] .erased (.ret .erased) ..) := IR.findEnvDecl source official then
              let tr := InitKernelPort.translate InitKernelPort.portName
              if !src.isUnsafe && !dst.isUnsafe && src.levelParams == dst.levelParams &&
                  tr src.type == dst.type && tr src.value == dst.value then
                candidates := candidates.push ci.name
    | .defnInfo d =>
      if onlyLayouts || oldNative.contains d.name || ci.isPartial then continue
      if ci.isUnsafe && !OmegaChecks.InitPort.UnsafeImplementation.isImplementation ci && !OmegaChecks.InitPort.ArraySafety.isOriginal ci true &&
          !OmegaChecks.InitPort.EffectRun.isOriginal ci true && !OmegaChecks.InitPort.PointerComparison.isOriginal ci true then continue
      let upstream := InitKernelPort.originalName d.name
      if unaryNat && largeWordSizes.contains upstream then continue
      if (isExtern source upstream || (getImplementedBy? source upstream).isSome) && !arrayDefinition upstream then continue
      candidates := candidates.push d.name
    | _ => continue
  if onlyLayouts && groups.isEmpty then return
  let localNames := NameSet.ofList candidates.toList
  let order : Array Name := Id.run <|
    (candidates.foldlM (fun acc n => return acc ++ (← dependencies source env partialCode localNames n)) #[]).run' {}
  let mut context ← localEnv env owner (locals ++ words ++ candidates)
  -- Compiler tags stored under the imported module index need local entries while compiling.
  for n in locals ++ candidates do
    if n == `Thunk then
      let some info := getStructureInfo? env n | throw <| IO.userError "missing thunk structure fields"
      context := structureExt.addEntry context info
    let upstream := InitKernelPort.originalName n
    let macroMatchers := [`Lean.expandMacros.match_1, `Lean.Syntax.setTailInfo.match_1, `Lean.Syntax.structEq._sparseCasesOn_2]
    if owner == `OmegaInit.Meta.Defs && (privateToUserName? upstream).any macroMatchers.contains then
      if let some (.defnInfo original) := source.find? upstream then
        if let some (.defnInfo installed) := env.find? n then
          let translate := InitKernelPort.translate InitKernelPort.portName
          if installed.type == translate original.type && installed.value == translate original.value then
            if let some matcher := Meta.getMatcherInfoCore? source upstream then
              context := Meta.Match.Extension.addMatcherInfo context n matcher
            if isSparseCasesOn source upstream then context := markSparseCasesOn context n
    if isAuxRecursor env n then context := markAuxRecursor context n
    if isSparseCasesOn env n then context := markSparseCasesOn context n
    if isNoConfusion env n then context := markNoConfusion context n (getNoConfusionInfo env n)
    if let some proj := env.getProjectionFnInfo? n then
      context := addProjectionFnInfo context n proj.ctorName proj.numParams proj.i proj.fromClass
  let ctx : Core.Context := {fileName := "<generated native Init>", fileMap := default, options := Elab.async.set {} false}
  let (_, st) ← (compileOwner source partialCode groups words order).toIO ctx {env := context}
  if onlyLayouts then
    writeCode lib owner st.env layouts
  else
    for n in (declOrderExt.getState st.env).1 do
      if oldNative.contains n then throw <| IO.userError s!"native symbol collision at {n}"
    let file := modToFilePath out owner "c"
    emitOwner st.env owner part.imports ctx file
    let stringExports := words.any fun n => OmegaChecks.InitPort.WordNative.usesStringExport (InitKernelPort.originalName n)
    if stringExports || words.any (fun n => OmegaChecks.InitPort.WordNative.usesPinnedFunction (InitKernelPort.originalName n)) then
      let upstream := if stringExports then `Init.Data.String else owner.replacePrefix `OmegaInit `Init
      let init := mkModuleInitializationFunctionName (phases := .runtime) owner st.env.getModulePackage?
      let upstreamInit := mkModuleInitializationFunctionName (phases := .runtime) upstream
        (source.getModuleIdx? upstream >>= source.getModulePackageByIdx?)
      let generated ← IO.FS.readFile file
      let decl := s!"LEAN_EXPORT lean_object* {init}(uint8_t builtin) \{"
      let parts := generated.splitOn decl
      let [before, after] := parts | throw <| IO.userError s!"missing runtime initializer {init}"
      IO.FS.writeFile file <| before ++ s!"extern lean_obj_res {upstreamInit}(uint8_t);\n" ++ decl ++
        s!"\nlean_obj_res upstream = {upstreamInit}(builtin);\nif (lean_io_result_is_error(upstream)) return upstream;\nlean_dec_ref(upstream);\n" ++ after
    unless words.isEmpty do
      IO.FS.withFile file .append fun h => do
        for n in words do h.putStr (← OmegaChecks.InitPort.WordNative.wrapper source st.env n)
    let computable := NameSet.ofList <| part.constants.toList.filterMap fun ci =>
      if !ci.isUnsafe && !ci.isPartial && isNoncomputable env ci.name &&
          (IR.findEnvDecl st.env ci.name).isSome && (getSigCore? st.env impureSigExt ci.name).isSome then
        some ci.name
      else none
    let mut compiled := st.env
    let mut extensions := layouts ++ codeExtensions ++ #[privateConstKindsExt.name]
    if owner == `OmegaInit.Dynamic then
      extensions := extensions.push Compiler.implementedByAttr.ext.name
      for op in OmegaChecks.InitPort.DynamicValue.operations do
        let pub := InitKernelPort.portName op
        let impl := OmegaChecks.InitPort.DynamicValue.implementation op
        let target := InitKernelPort.portName impl
        if words.contains pub && words.contains target then
          unless Compiler.getImplementedBy? source op == some impl do throw <| IO.userError s!"missing pinned implementation {op}"
          compiled ← IO.ofExcept <| Compiler.setImplementedBy compiled pub target
    writeCode lib owner compiled extensions computable
    let fresh ← importModules #[{module := owner}] {} (level := .exported)
    let actual := NameSet.ofList ((impureSigExt.getModuleEntries fresh (fresh.getModuleIdx? owner).get!).map (·.name)).toList
    let originalOwner := owner.replacePrefix `OmegaInit `Init
    let some originalIdx := publicSource.getModuleIdx? originalOwner | throw <| IO.userError s!"no official owner {originalOwner}"
    let published := NameSet.ofList ((impureSigExt.getModuleEntries publicSource originalIdx).map (·.name)).toList
    let publicSigs := publicSource.header.moduleData[originalIdx]!.constants.filter fun ci =>
      !ci.name.isInternalOrNum && !isPrivateName ci.name && published.contains ci.name &&
      (source.find? ci.name).any fun full => full.hasValue (allowOpaque := true) && !full.isUnsafe && !full.isPartial
    let covered := publicSigs.filter fun ci => actual.contains (InitKernelPort.portName ci.name)
    IO.println s!"{owner}: {covered.size}/{publicSigs.size} public executable signatures"
    let missing := publicSigs.filterMap fun ci =>
      if actual.contains (InitKernelPort.portName ci.name) then none else some ci.name
    if !missing.isEmpty then IO.println s!"{owner}: missing public executable signatures: {missing}"

/-- A detached seed may supply only Lean's compiled modules. Execute the ordinary consumer
using the saved IR under the same Boolean representation used by its C entry points. -/
private unsafe def checkControl (lib dir : System.FilePath) : IO Unit := do
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `GeneratedControlConsumer, importAll := true}] {} (level := .private)
  let some (.inductInfo b) := env.find? `Bool | throw <| IO.userError "missing Boolean type"
  unless b.numParams == 0 && b.ctors == [`Bool.false, `Bool.true] do
    throw <| IO.userError "unexpected Boolean representation"
  let ty := mkConst `Bool
  let arity := .forallE `x ty (.forallE `y ty ty .default) .default
  for (name, expected) in [(`exceptResult, or), (`optionResult, and), (`stateResult, and)] do
    unless (env.find? name).any (·.type == arity) do throw <| IO.userError s!"unexpected type for {name}"
    let fn ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} name
    for x in [false, true] do
      for y in [false, true] do
        unless fn x y == expected x y do throw <| IO.userError s!"incorrect {name} {x} {y}"

end GeneratedNative

public unsafe def main (args : List String) : IO Unit := do
  if let ["--check-control", lib, dir] := args then
    return ← GeneratedNative.checkControl lib dir
  let lib :: out :: requests := args | throw <| IO.userError "expected library, C output and ordered owners"
  let modules := requests.toArray.map fun s => ((s.dropPrefix "layouts=").dropPrefix "mixed=").toString.toName
  let official := modules.map fun n => {module := n.replacePrefix `OmegaInit `Init : Import}
  let published ← importModules official {} (level := .exported)
  let src ← importModules official {}
  searchPathRef.set [lib]
  for name in modules, s in requests do
    GeneratedNative.install src published lib out name (s.startsWith "layouts=") (s.startsWith "mixed=")
    (← IO.getStdout).flush
