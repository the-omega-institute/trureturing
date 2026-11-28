import Lean
import Lean.Replay
import OmegaChecks.InitCompiler.Proofs
import OmegaChecks.InitCompiler.Recursion
import OmegaChecks.InitCompiler.FiniteCollectors
import OmegaChecks.InitPort.Alternatives
import OmegaChecks.InitPort.Arithmetic
import OmegaChecks.InitPort.LogicalHandle
import OmegaChecks.InitPort.ReferenceSpecialization
import OmegaChecks.InitPort.TypeName
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.NativeQuot
import OmegaChecks.InitPort.UnsafeRuntime
import OmegaChecks.InitPort.Address
import OmegaChecks.InitPort.ArrayMap
import OmegaChecks.InitPort.WordFold
import OmegaChecks.InitPort.WordForIn
import OmegaChecks.InitPort.SyntaxArray

open Lean

namespace InitKernelPort

def moduleOf (env : Environment) (n : Name) : Option Name := do
  if let some rule := OmegaChecks.InitPort.LawfulLoop.rules.find? (·.helper == n) then return rule.owner
  if let some rule := OmegaChecks.InitPort.PatternMatch.rules.find? (·.helper == n) then return rule.owner
  let i ← env.getModuleIdxFor? n
  return env.header.moduleNames[i]!

def invalidExpr (e : Expr) : Bool :=
  e.hasFVar || e.hasMVar || e.hasLooseBVars

/-- String literals introduce foundation declarations absent from the original constant set. -/
private def usedConstants (e : Expr) : NameSet := Id.run do
  let mut deps := e.getUsedConstantsAsSet
  if (e.find? fun x => x matches .lit (.strVal _)).isSome then
    deps := ((deps.insert `String.ofList).insert `List.nil).insert `Char
    if (e.find? fun x => match x with | .lit (.strVal s) => !s.isEmpty | _ => false).isSome then
      deps := (deps.insert `List.cons).insert `Char.ofNat
  return deps

def translateDecl (info : ConstantInfo) (type body : Expr) : Except String Declaration := do
  let rename := portName
  let val (v : ConstantVal) := { v with name := rename v.name, type := translate rename type }
  if (info.isUnsafe && !OmegaChecks.InitPort.UnsafeRuntime.isOriginal info false) || info.isPartial then throw "unsafe/partial"
  if invalidExpr type || invalidExpr body then throw "open term or unsupported string literal"
  let body := translate rename body
  match info with
  | .defnInfo d => return .defnDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | .thmInfo d => return .thmDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | .opaqueInfo d => return .opaqueDecl { d with toConstantVal := val d.toConstantVal, value := body, all := d.all.map rename }
  | _ => throw "unsupported declaration kind"

inductive Outcome
  | existing
  | added
  | blocked (reason : String) (cause : Option Name := none)
  deriving Inhabited

structure State where
  env : Kernel.Environment
  results : Std.HashMap Name Outcome := {}
  visiting : NameSet := {}
  proofsByType : Std.HashMap Expr (List Name) := {}

structure Context where
  source : Environment
  base : Environment
  maxHeartbeats : Nat
  excluded : NameMap String
  publicNames : NameSet
  literalProofs : NameMap ConstantInfo
  alternatives : NameMap ConstantInfo
  proofRules : NameMap ConstantInfo
  referenceTemplates : Environment
  referenceModels : NameMap (Array ConstantInfo)
  handles : NameMap OmegaChecks.InitPort.LogicalHandle.Templates
  typeNameTemplates : OmegaChecks.InitPort.TypeName.Templates
  recursionRule : ConstantInfo
  output : IO.FS.Handle

abbrev M := ReaderT Context (StateRefT State IO)

private def loadLiteralProofs (strictPath : System.FilePath) : IO (NameMap ConstantInfo) :=
  IO.FS.withTempDir fun temp => do
    let dir := System.FilePath.mk "strict/OmegaChecks/InitPort"
    let lean := (← findSysroot) / "bin" / "lean"
    let build ← IO.Process.output {
      cmd := lean.toString
      args := #["-R", dir.toString, "-o", (temp / "LiteralProofs.olean").toString,
        (dir / "LiteralProofs.lean").toString]
      env := #[("LEAN_PATH", some strictPath.toString)] }
    unless build.exitCode == 0 do throw <| IO.userError (build.stdout ++ build.stderr)
    searchPathRef.set [temp, strictPath]
    let env ← importModules #[{module := `LiteralProofs}] {}
    let mut proofs := {}
    for ci in env.header.moduleData[(env.getModuleIdx? `LiteralProofs).get!]!.constants do
      if ci.name.getRoot == `OmegaLiteralProofs then
        proofs := proofs.insert ci.name ci
    return proofs

/-- Abstract each shared proof before substituting its implementation. The kernel
checks each bound proof once and its uses retain the stated proposition. -/
private def inlineLiteralProofs (proofs : NameMap ConstantInfo) (e : Expr) : Expr := Id.run do
  let mut term := e
  for leaf in [`raiseBound, `digitBounds, `bounds, `double_eq, `leftMono, `plusSucc, `rightMono] do
    let name := `OmegaLiteralProofs ++ leaf
    if !term.getUsedConstantsAsSet.contains name then continue
    let ci := (proofs.find? name).get!
    let x := mkFVar ⟨name⟩
    let openBody := term.replace fun sub => if sub.isConstOf name then some x else none
    term := mkApp (.lam leaf ci.type (openBody.abstract #[x]) .default) (ci.value! (allowOpaque := true))
  let twice := ((proofs.find? `OmegaLiteralProofs.double).get!).value!
  return term.replace fun sub => if sub.isConstOf `OmegaLiteralProofs.double then some twice else none

/-- Build small bounds using the constructors of the indexed Nat.le family. -/
private def smallLe (a b : Nat) : Expr := Id.run do
  let left := mkRawNatLit a
  let mut proof := mkApp (mkConst `Omega.Nat.le.refl) left
  for i in [a:b] do
    proof := mkApp3 (mkConst `Omega.Nat.le.step) left (mkRawNatLit i) proof
  return proof

private partial def binaryLt (a b : Nat) : Expr := Id.run do
  if b < 32 then return smallLe (a + 1) b
  let x := mkRawNatLit (a / 2)
  let y := mkRawNatLit (b / 2)
  let succ := mkApp (mkConst `Nat.succ)
  let double := mkApp (mkConst `OmegaLiteralProofs.double)
  if a / 2 == b / 2 then return mkApp (mkConst `Omega.Nat.lt_succ_self) (double x)
  let rule := if a % 2 == 0 then `OmegaLiteralProofs.digitBounds else `OmegaLiteralProofs.bounds
  let h := mkApp3 (mkConst rule) x y (binaryLt (a / 2) (b / 2))
  if b % 2 == 0 then return h
  let left := if a % 2 == 0 then double x else succ (double x)
  return mkApp3 (mkConst `OmegaLiteralProofs.raiseBound) left (double y) h

/-- Evaluate just the numeral expressions for which the resulting comparison proof
can be independently checked. The cap bounds generated certificate size. -/
private def numeral? (source : Environment) (expr : Expr) (fuel : Nat := 4) : Option Nat := do
  let e := expr.consumeMData
  if let some n := e.rawNatLit? then return n
  if e.getAppFn.isConstOf `OfNat.ofNat then return ← e.getAppArgs[1]?.bind Expr.rawNatLit?
  let fuel + 1 := fuel | none
  if e.getAppFn.isConstOf `HPow.hPow then
    let #[_, _, _, _, base, exponent] := e.getAppArgs | none
    let b ← numeral? source base fuel
    let k ← numeral? source exponent fuel
    guard (b == 2 && k ≤ 256)
    return 2 ^ k
  let .const n _ := e | none
  let ci ← source.find? n
  let body ← ci.value?
  numeral? source body fuel

/-- Match the binary term used for wide even natural literals. -/
private partial def binaryNonzero (size : Nat) : Expr :=
  if size < 32 || size % 2 == 1 then
    mkApp (mkConst `Nat.instNeZeroSucc) (mkNatLit (size - 1))
  else
    mkApp4 (mkConst `instNeZeroNatHMul) (mkNatLit (size / 2)) (mkNatLit 2)
      (binaryNonzero (size / 2)) (mkApp (mkConst `Nat.instNeZeroSucc) (mkNatLit 1))

/-- Give wide finite bounds a nonzero instance with a compact kernel conversion. -/
private def compactNonzeroBounds (source : Environment) (owner : Name) (type : Expr) : Expr :=
  type.replace fun e => do
    guard (e.isAppOfArity `Nat.instNeZeroSucc 1)
    let n ← numeral? source e.getAppArgs[0]!
    let size := n + 1
    guard (size ≥ 256)
    if size != 2 ^ size.log2 then
      guard (size % 2 == 0)
      let provider ← source.getModuleIdxFor? `instNeZeroNatHMul
      let current ← source.getModuleIdxFor? owner
      guard (provider.toNat < current.toNat)
      return binaryNonzero size
    let one := mkApp (mkConst `Nat.instNeZeroSucc) (mkNatLit 1)
    return mkApp3 (mkConst `Nat.instNeZeroHPow) (mkNatLit 2) (mkNatLit size.log2) one

/-- Compare the underlying naturals for order instances whose strict implementation
computes through Nat.le. The target kernel checks those conversions and the complete proof. -/
private def orderTruthProof? (source : Environment) (proofs : NameMap ConstantInfo)
    (type : Expr) : IO (Option Expr) := do
  let goal := type.getForallBody
  let #[_, rel, value] := goal.getAppArgs | return none
  unless goal.isAppOf `Eq && (value.isConstOf `True || value.isConstOf `False) &&
      (rel.isAppOf `LE.le || rel.isAppOf `LT.lt) do return none
  let truth := value.isConstOf `True
  let action : MetaM (Option Expr) := Meta.forallTelescope type fun xs result => do
    let some h := xs.back? | return none
    let ht ← Meta.inferType h
    let #[_, test, bit] := ht.getAppArgs | return none
    let #[p, dec] := test.getAppArgs | return none
    unless ht.isAppOf `Eq && test.isAppOf `Decidable.decide &&
        bit.isConstOf (if truth then `Bool.true else `Bool.false) do return none
    let relation := result.getAppArgs[1]!
    let #[α, _, a, b] := relation.getAppArgs | return none
    let some numType := α.getAppFn.constName? | return none
    let convert : Option (Expr → Expr) := match numType with
      | `Nat => some id
      | `Fin => some (mkApp (mkAppN (mkConst `Fin.val) α.getAppArgs))
      | `BitVec => some (mkApp (mkAppN (mkConst `BitVec.toNat) α.getAppArgs))
      | `UInt8 | `UInt16 | `UInt32 | `UInt64 | `USize | `Char => some (mkApp (mkConst (numType ++ `toNat)))
      | _ => none
    let some asNat := convert | return none
    let lo := if relation.isAppOf `LT.lt then mkApp (mkConst `Nat.succ) (asNat a) else asNat a
    let rule := if truth then `OmegaLiteralProofs.leTrue else `OmegaLiteralProofs.leFalse
    let extract := if truth then `of_decide_eq_true else `of_decide_eq_false
    let computedLE := (proofs.find? `OmegaLiteralProofs.computedLE).get!.value!
    let proof := (proofs.find? rule).get!.value! (allowOpaque := true)
    let expanded := proof.replace fun e =>
      if e.isConstOf `OmegaLiteralProofs.computedLE then some computedLE else none
    let induction := expanded.replace fun
      | .const n ls => some (.const (n.replacePrefix `Omega .anonymous) ls)
      | _ => none
    let body := mkApp3 induction lo (asNat b) (mkApp3 (mkConst extract) p dec h)
    return some (← Meta.mkLambdaFVars xs body)
  action.run' |>.toIO' {fileName := "<natural order truth>", fileMap := default} {env := source}

private def comparisonProofs (source : Environment) (proofs : NameMap ConstantInfo)
    (body : Expr) (owner : Name) : Option Expr := Id.run do
  let earlier (lemma : Name) := match source.getModuleIdxFor? lemma, source.getModuleIdxFor? owner with
    | some provider, some current => provider.toNat < current.toNat
    | _, _ => false
  let original := fun (term : Expr) => term.replace fun
    | .const n us => some (.const (n.replacePrefix `Omega .anonymous) us)
    | _ => none
  let result := body.replace fun e => Id.run do
    if e.isAppOfArity `of_eq_true 2 then
      let eq := e.getAppArgs[1]!
      if eq.isAppOfArity `Nat.dvd_eq_true_of_mod_eq_zero 3 && earlier `Nat.pow_dvd_pow then
        let some divisor := numeral? source eq.getAppArgs[0]! | return none
        let some dividend := numeral? source eq.getAppArgs[1]! | return none
        let lo := divisor.log2
        let hi := dividend.log2
        if lo ≤ hi && hi ≤ 256 && 2^lo == divisor && 2^hi == dividend then
          return some (mkApp4 (mkConst `Nat.pow_dvd_pow) (mkRawNatLit lo) (mkRawNatLit hi)
            (mkRawNatLit 2) (original (smallLe lo hi)))
    unless e.getAppFn.isConstOf `of_decide_eq_true do return none
    let some p := e.getAppArgs[0]? | return none
    let asProof := mkApp (mkConst `id [.zero]) p
    if p.getAppFn.isConstOf `Eq then
      let #[α, a, b] := p.getAppArgs | return none
      unless α.isConstOf `Nat do return none
      let some x := numeral? source a | return none
      let some y := numeral? source b | return none
      unless x == y && x ≥ 32 do return none
      return some <| mkApp asProof (mkApp2 (mkConst `Eq.refl [.succ .zero]) α a)
    let strict := p.getAppFn.isConstOf `LT.lt
    unless strict || p.getAppFn.isConstOf `LE.le do return none
    let #[α, _, a, b] := p.getAppArgs | return none
    let some x := numeral? source a | return none
    let some y := numeral? source b | return none
    unless (if strict then x < y else x ≤ y) && y ≥ 32 do return none
    let word := strict && α.isConstOf `UInt32 && x == 0 && y < 2 ^ 32 &&
      earlier `UInt32.ofNatLT_lt_of_lt
    unless α.consumeMData.isConstOf `Nat || word do return none
    if !strict && earlier `Nat.pow_le_pow_right && x > 0 && y > 0 && y.log2 < 128 &&
        2 ^ x.log2 == x && 2 ^ y.log2 == y then
      return some <| mkApp asProof <| mkApp5 (mkConst `Nat.pow_le_pow_right) (mkRawNatLit 2)
        (original (smallLe 1 2)) (mkRawNatLit x.log2) (mkRawNatLit y.log2) (original (smallLe x.log2 y.log2))
    let cert := if x == y then mkApp (mkConst `Omega.Nat.le_refl) (mkRawNatLit x)
      else if strict then binaryLt x y
      else mkApp5 (mkConst `Omega.Nat.le_trans) (mkRawNatLit x) (mkApp (mkConst `Nat.succ) (mkRawNatLit x))
        (mkRawNatLit y) (mkApp (mkConst `Omega.Nat.le_succ) (mkRawNatLit x)) (binaryLt x y)
    let cert := if word then mkApp5 (mkConst `Omega.UInt32.ofNatLT_lt_of_lt) (mkRawNatLit x) (mkRawNatLit y)
        (binaryLt x (2 ^ 32)) (binaryLt y (2 ^ 32)) cert
      else cert
    let cert := inlineLiteralProofs proofs cert
    return some <| mkApp asProof (original cert)
  return if result.equal body then none else some result

def describe : Outcome → String × Option Name
  | .existing => ("existing", none)
  | .added => ("added", none)
  | .blocked s n => (s,n)

/-- Index proved statements independently of the compiler's universe parameter names. -/
private def theoremKey (ci : ConstantInfo) : Expr :=
  ci.type.instantiateLevelParams ci.levelParams
    ((List.range ci.numLevelParams).map fun i => Level.param (.num .anonymous i))

def record (name : Name) (outcome : Outcome) : M Bool := do
  let c ← read
  let owner := moduleOf c.source name |>.getD .anonymous
  let (diagnostic, cause) := describe outcome
  c.output.putStrLn (toJson #[owner.toString,name.toString, (toString (c.publicNames.contains name)),
    diagnostic, (cause.map Name.toString).getD ""]).compress
  c.output.flush
  modify fun s => { s with results := s.results.insert name outcome, visiting := s.visiting.erase name }
  if outcome matches .blocked .. then return false
  if let some ci := c.source.find? name then
    if ci.isTheorem && !name.isInternal then
      let key := theoremKey ci
      modify fun s => {s with proofsByType := s.proofsByType.insert key (name :: s.proofsByType.getD key [])}
  return true

/-- Compare the entire generated kernel entry, including the iota rules of recursors. -/
def expectGenerated (src : Environment) (ci : ConstantInfo) : IO (Option ConstantInfo) := do
  let newType ← OmegaChecks.InitCompiler.finiteCollectors src ci.type
  let ren := portName
  let val (v : ConstantVal) := {v with name := ren v.name, type := translate ren newType}
  match ci with
  | .inductInfo v => return some <| .inductInfo { v with toConstantVal := val v.toConstantVal, ctors := v.ctors.map ren, all := v.all.map ren }
  | .ctorInfo v => return some <| .ctorInfo { v with toConstantVal := val v.toConstantVal, induct := ren v.induct }
  | .recInfo v =>
    let rules ← v.rules.mapM fun r => do
      let rhs ← OmegaChecks.InitCompiler.finiteCollectors src r.rhs
      pure {r with ctor := ren r.ctor, rhs := translate ren rhs}
    return some <| .recInfo {v with toConstantVal := val v.toConstantVal, all := v.all.map ren, rules}
  | _ => return none

/-- The original kernel erases typeclass output markers while generating recursors.
Our independently named markers are definitionally transparent, so compare all shape data
literally and the types and computation rules up to kernel conversion. -/
def agrees (env : Kernel.Environment) (src target : Option ConstantInfo) : Bool := Id.run do
  if src == target then return true
  let eqv := Kernel.isDefEqGuarded (.ofKernelEnv env) {}
  if let some (.recInfo a) := src then
    if let some (.recInfo b) := target then
      unless {a with type := b.type, rules := b.rules} == b && a.rules.length == b.rules.length && eqv a.type b.type do return false
      for x in a.rules, y in b.rules do
        unless x.ctor == y.ctor && x.nfields == y.nfields && eqv x.rhs y.rhs do return false
      return true
  return false

structure Family where
  decl : Declaration
  externals : NameSet
  generated : Array Name

def family (src : Environment) (i : InductiveVal) : ExceptT String IO Family := do
  let rename := portName
  let mut types := []
  let mut deps : NameSet := {}
  let mut names := #[]
  for n in i.all do
    let some (.inductInfo v) := src.find? n | throw "missing family member"
    if v.isUnsafe || invalidExpr v.type then throw "inadmissible family"
    let mut ctors := []
    deps := deps ++ usedConstants v.type
    names := names.push n
    for k in v.ctors do
      let some (.ctorInfo cv) := src.find? k | throw "missing constructor"
      if cv.isUnsafe || invalidExpr cv.type then throw "inadmissible constructor"
      names := names.push k
      let ctorType ← liftM (m := IO) (OmegaChecks.InitCompiler.finiteCollectors src cv.type)
      deps := deps ++ usedConstants ctorType
      ctors := ctors ++ [{name := rename k, type := translate rename ctorType : Constructor}]
    let recn := n ++ `rec
    names := names.push recn
    types := types ++ [{name := rename n, type := translate rename v.type, ctors : InductiveType}]
  for n in names do deps := deps.erase n
  return {decl := .inductDecl i.levelParams i.numParams types false, externals := deps, generated := names}

/-- Run each declaration on a fresh worker so the kernel heartbeat counter is local. -/
def checkDecl (env : Kernel.Environment) (decl : Declaration) (budget : Nat) :
    BaseIO (Except Kernel.Exception Kernel.Environment) := do
  let work : BaseIO (Except Kernel.Exception Kernel.Environment) := do
    let initial ← IO.getNumHeartbeats
    let limit := (initial + budget).toUSize
    if decl.getNames.any (fun n => OmegaChecks.InitPort.ArraySafety.names.contains (originalName n)) then
      return OmegaChecks.InitPort.ArraySafety.verify env decl limit
    return env.addDeclCore limit 1000 decl none
  let task ← work.asTask (prio := .dedicated)
  return task.get

/-- Reserve a larger worker budget for declarations which exhaust the first one. -/
private def checkWithRetry (env : Kernel.Environment) (decl : Declaration) (budget : Nat) :
    BaseIO (Except Kernel.Exception Kernel.Environment) := do
  let result ← checkDecl env decl budget
  if result matches .error .deterministicTimeout then checkDecl env decl (200 * budget)
  else return result

/-- For equations compiled by the pattern matcher, expose at most two Nat or List arguments.
Each leaf proposes reflexivity. The kernel checks the entire resulting elimination term. -/
private partial def equationCases? (type : Expr) (fuel := 2) (depth := 0) : Option Expr := do
  let fresh := fun (n : Name) => mkFVar ⟨Name.num n depth⟩
  let lam := fun (x : Expr) n domain body bi => Expr.lam n domain (body.abstract #[x]) bi
  let .forallE n dom body bi := type |
    let .const `Eq us := type.getAppFn | none
    let #[α, lhs, _] := type.getAppArgs | none
    return mkApp2 (mkConst `Eq.refl us) α lhs
  let x := fresh `x
  let motive := Expr.lam n dom body .default
  let after := fun y f => equationCases? (body.instantiate1 y) f (depth + 1)
  if fuel > 0 && dom.isConstOf `Nat then
    let zero ← after (mkConst `Nat.zero) (fuel - 1)
    let k := fresh `k
    let step ← after (mkApp (mkConst `Nat.succ) k) (fuel - 1)
    let ihType := body.instantiate1 k
    let succ := lam k `k dom (.lam `ih ihType step .default) .default
    return lam x n dom (mkApp4 (mkConst `Nat.rec [.zero]) motive zero succ x) bi
  if let .app (.const `Omega.List [u]) α := dom then
    if fuel > 0 then
      let nil ← after (mkApp (mkConst `Omega.List.nil [u]) α) (fuel - 1)
      let head := fresh `head
      let tail := fresh `tail
      let step ← after (mkApp3 (mkConst `Omega.List.cons [u]) α head tail) (fuel - 1)
      let ih := Expr.lam `ih (body.instantiate1 tail) step .default
      let cons := lam head `head α (lam tail `tail dom ih .default) .default
      return lam x n dom (mkApp5 (mkConst `Omega.List.rec [.zero,u]) α motive nil cons x) bi
  return lam x n dom (← after x fuel) bi

/-- Search only theorem interfaces with all referenced constants present. Share one kernel
heartbeat limit across all attempted proofs and keep the original rejection on failure. -/
private def alternateProof (ci : ConstantInfo) (sourceType : Expr) : M Bool := do
  let .thmInfo th := ci | return false
  let c ← read
  let rename := portName
  let type := translate rename sourceType
  let state ← get
  if invalidExpr type || type.getUsedConstants.any (fun n => (state.env.find? n).isNone) then return false
  let base := {th with name := rename th.name, type, all := [rename th.name]}
  let work : BaseIO (Option Kernel.Environment) := do
    let stop := (← IO.getNumHeartbeats) + c.maxHeartbeats
    let mut candidates := OmegaChecks.InitCompiler.elementaryCandidates type
    if th.name == th.name.getPrefix ++ `eq_def then
      if let some term := equationCases? type then candidates := term :: candidates
    for term in candidates do
      if (← IO.getNumHeartbeats) >= stop then break
      let decl := Declaration.thmDecl {base with value := term}
      if let .ok next := state.env.addDeclCore stop.toUSize 1000 decl none then return some next
    return none
  let task ← work.asTask (prio := .dedicated)
  if let some next := task.get then
    modify fun s => {s with env := next}
    return ← record ci.name .added
  return false

private def keepImplementationSafety (n : Name) (decl : Declaration) : Declaration :=
  match decl with
  | .defnDecl d => if OmegaChecks.InitPort.UnsafeImplementation.supported n then
      .defnDecl {d with safety := .unsafe} else decl
  | _ => decl

partial def visit (n : Name) : M Bool := do
  let c ← read
  if let some result := (← get).results[n]? then
    return match result with | .blocked .. => false | _ => true
  if (← get).visiting.contains n then return false
  let some owner := moduleOf c.source n | return ← record n (.blocked "unknown official module")
  if owner.getRoot != `Init then return ← record n (.blocked "outside Init")
  let some ci := c.source.find? n | return ← record n (.blocked "missing official constant")
  let dest := portName n
  if OmegaChecks.InitPort.ArraySafety.names.contains n && !OmegaChecks.InitPort.ArraySafety.isOriginal ci false then
    return ← record n (.blocked "unexpected pinned array declaration")
  if let some i := c.base.find? dest then
    if i.isAxiom || i.isUnsafe || i.isPartial || (i matches .quotInfo _) ||
        moduleOf c.base dest != some (owner.replacePrefix `Init `OmegaInit) then
      return ← record n (.blocked "unverified seed name or wrong seed owner")
    return ← record n .existing
  if let some generated := (← get).env.find? dest then
    if agrees (← get).env (← expectGenerated c.source ci) (some generated) then return ← record n .added
    return ← record n (.blocked "target name collision")
  if let some reason := c.excluded.find? n then return ← record n (.blocked reason)
  if n == Meta.mkSmartUnfoldingNameFor n.getPrefix then
    let parent := n.getPrefix
    modify fun s => {s with visiting := s.visiting.insert n}
    unless ← visit parent do return ← record n (.blocked "unavailable smart unfolding parent" (some parent))
    unless exactDefinition c.source (← get).env parent do
      return ← record n (.blocked "smart unfolding belongs to a different implementation" (some parent))
    let some (.defnInfo helper) := c.source.find? n | return ← record n (.blocked "unexpected smart unfolding declaration")
    -- Install the same body whose annotated matcher applications Lean will reduce.
    for dep in usedConstants helper.type ++ usedConstants helper.value do
      unless ← visit dep do return ← record n (.blocked "unavailable dependency" (some dep))
    let kernel := (← get).env
    let missing := helper.value.find? fun expr => Id.run do
      let some app := Meta.smartUnfoldingMatch? expr | return false
      let some matcher := app.getAppFn.constName? | return true
      return (Meta.getMatcherInfoCore? c.source matcher).isNone || !exactDefinition c.source kernel matcher
    if missing.isSome then return ← record n (.blocked "smart unfolding requires unavailable matcher metadata")
    let .ok decl := translateDecl ci helper.type helper.value | return ← record n (.blocked "open smart unfolding term")
    let .ok next ← checkWithRetry kernel decl c.maxHeartbeats | return ← record n (.blocked "kernel rejected smart unfolding definition")
    modify fun s => {s with env := next}
    return ← record n .added
  if ci.isAxiom then return ← record n (.blocked "axiom")
  let mapRef := OmegaChecks.InitPort.ArrayMap.reference? n
  let allocator := OmegaChecks.InitPort.LogicalHandle.implementation? n
  let dynamicOp := OmegaChecks.InitPort.DynamicValue.operation? n |>.filter (· != n)
  let atomicUpdate := n == OmegaChecks.InitPort.ReferenceModify.implementation
  let readsMethods := n == `Lean.Macro.getMethodsImp
  if mapRef.isSome || n == `Array.modifyMUnsafe || allocator.isSome || dynamicOp.isSome || atomicUpdate || readsMethods then
    let .defnInfo native := ci | return ← record n (.blocked "missing native implementation")
    let name := (mapRef <|> dynamicOp).getD <| if readsMethods then `Lean.Macro.getMethods else if atomicUpdate then OmegaChecks.InitPort.ReferenceModify.consumer else
      allocator.map (·.allocator) |>.getD `Array.modifyM
    let reference := mkConst name (native.levelParams.map Level.param)
    if mapRef.isSome then OmegaChecks.InitPort.ArrayMap.check c.source native reference
    if dynamicOp.isSome then OmegaChecks.InitPort.LogicalHandle.checkOpaqueImplementation `Init.Dynamic name c.source native reference
    if readsMethods then OmegaChecks.InitPort.LogicalHandle.checkOpaqueImplementation `Init.Prelude name c.source native reference
    if atomicUpdate then OmegaChecks.InitPort.ReferenceModify.checkImplementation c.source native reference
    if let some api := allocator then OmegaChecks.InitPort.LogicalHandle.checkImplementation api c.source native reference
    unless Compiler.getImplementedBy? c.source name == some n do
      return ← record n (.blocked "mismatched native implementation" (some name))
    unless ← visit name do return ← record n (.blocked "unavailable logical reference" (some name))
    let info := if mapRef.isSome || n == `Array.modifyMUnsafe then ci else ConstantInfo.defnInfo {native with safety := if dynamicOp.isSome then .unsafe else .safe, value := reference}
    let .ok decl := translateDecl info ci.type reference | return ← record n (.blocked "invalid logical reference")
    let .ok env ← checkWithRetry (← get).env (keepImplementationSafety n decl) c.maxHeartbeats
      | return ← record n (.blocked "kernel rejected logical reference")
    modify fun s => {s with env}
    return ← record n .added
  if n == `TypeName.typeName then
    unless ← visit OmegaChecks.InitPort.TypeName.reader do
      return ← record n (.blocked "unavailable type name implementation" (some OmegaChecks.InitPort.TypeName.reader))
  if n == `TypeNameData || n == `TypeName.mk || n == OmegaChecks.InitPort.TypeName.reader then
    let t := c.typeNameTemplates
    let body := (if n == `TypeNameData then t.family else if n == `TypeName.mk then t.make else t.decode)
      |>.instantiateLevelParams [`u] (ci.levelParams.map Level.param)
    for dep in usedConstants ci.type ++ usedConstants body do
      unless ← visit dep do return ← record n (.blocked "unavailable type name dependency" (some dep))
    let safety := if OmegaChecks.InitPort.TypeName.unsafeConversion n then DefinitionSafety.unsafe else .safe
    let info : DefinitionVal := {ci.toConstantVal with value := body, hints := .regular 0, safety, all := [n]}
    let .ok decl := translateDecl (.defnInfo info) ci.type body | return ← record n (.blocked "invalid type name model")
    let .ok env ← checkWithRetry (← get).env decl c.maxHeartbeats
      | return ← record n (.blocked "kernel rejected type name model")
    modify fun s => {s with env}
    return ← record n .added
  let referenceOwner := if n == OmegaChecks.InitPort.StateRunner.monotonicity then
    some OmegaChecks.InitPort.StateRunner.owner else OmegaChecks.InitPort.ReferenceSpecialization.consumerOwner? n
  if let some refOwner := referenceOwner then
    let (type, body) ← match ci with
      | .thmInfo th =>
        let some type := OmegaChecks.InitPort.alternativeType? c.alternatives ci
          | throw <| IO.userError s!"missing pointwise order interface for {n}"
        pure (type, ← OmegaChecks.InitPort.StateRunner.monotonicityProof c.source c.referenceTemplates th type)
      | .defnInfo d => pure (ci.type, ← OmegaChecks.InitPort.ReferenceSpecialization.consumerBody c.source c.referenceTemplates d)
      | .opaqueInfo _ =>
        if n == OmegaChecks.InitPort.RandomState.refName then pure (ci.type, OmegaChecks.InitPort.RandomState.refBody)
        else throw <| IO.userError s!"unexpected opaque reference consumer {n}"
      | _ => throw <| IO.userError s!"unexpected reference consumer {n}"
    let models := c.referenceModels.getD refOwner #[]
    let mut deps := usedConstants type ++ usedConstants body
    for model in models do
      deps := deps ++ usedConstants model.type ++ usedConstants (model.value! (allowOpaque := true))
    for dep in deps do
      unless models.any (·.name == dep) || (← visit dep) do return ← record n (.blocked "unavailable reference dependency" (some dep))
    let mut env := (← get).env
    for model in models do
      if (env.find? (portName model.name)).isSome then continue
      let .ok decl := translateDecl model model.type (model.value! (allowOpaque := true))
        | throw <| IO.userError s!"invalid private reference operation {model.name}"
      let .ok next ← checkWithRetry env decl c.maxHeartbeats | throw <| IO.userError s!"kernel rejected {model.name}"
      env := next
    let .ok decl := translateDecl ci type body | return ← record n (.blocked "invalid reference consumer")
    let .ok next ← checkWithRetry env decl c.maxHeartbeats | return ← record n (.blocked "kernel rejected specialized reference consumer")
    modify fun state => {state with env := next}
    return ← record n .added
  if let some api := OmegaChecks.InitPort.LogicalHandle.forDecl? n then
    let .opaqueInfo native := ci | return ← record n (.blocked "missing opaque handle declaration")
    let some handle := c.handles.find? api.pointed | throw <| IO.userError s!"missing handle templates for {api.owner}"
    let isFamily := n == api.pointed
    let pkg := handle.package
    let body := if isFamily then handle.family else handle.allocation
    let deps := usedConstants ci.type ++ usedConstants body ++ usedConstants pkg.type ++ usedConstants pkg.value
    for dep in deps do
      unless dep == pkg.name || (← visit dep) do return ← record n (.blocked "unavailable handle dependency" (some dep))
    let mut env := (← get).env
    if (env.find? (portName pkg.name)).isNone then
      let .ok decl := translateDecl (.opaqueInfo pkg) pkg.type pkg.value | throw <| IO.userError "invalid handle package"
      let .ok next ← checkWithRetry env decl c.maxHeartbeats | throw <| IO.userError "kernel rejected handle package"
      env := next
    let info := if isFamily then ConstantInfo.defnInfo
      {native.toConstantVal with value := body, hints := .regular 0, safety := .safe, all := [n]} else ci
    let .ok decl := translateDecl info ci.type body | return ← record n (.blocked "invalid handle model")
    let .ok next ← checkWithRetry env decl c.maxHeartbeats
      | return ← record n (.blocked "kernel rejected handle model")
    modify fun s => {s with env := next}
    return ← record n .added
  if n == `Void.nonemptyType then
    let .opaqueInfo native := ci | return ← record n (.blocked "missing opaque state family")
    let some body := OmegaChecks.InitPort.alternativeBody? c.alternatives ci
      | return ← record n (.blocked "missing indexed state token package")
    for dep in usedConstants ci.type ++ usedConstants body do
      unless ← visit dep do return ← record n (.blocked "unavailable state token dependency" (some dep))
    let family : DefinitionVal := {native.toConstantVal with value := body, hints := .regular 0, safety := .safe, all := [n]}
    let .ok decl := translateDecl (.defnInfo family) ci.type body | return ← record n (.blocked "invalid state carrier")
    let .ok env ← checkWithRetry (← get).env decl c.maxHeartbeats
      | return ← record n (.blocked "kernel rejected state carrier")
    modify fun s => {s with env}
    return ← record n .added
  if n == `Array.get!InternalBorrowed || n == `Array.anyMUnsafe || OmegaChecks.InitPort.WordFold.supported n ||
      OmegaChecks.InitPort.WordForIn.supported n || OmegaChecks.InitPort.SyntaxArray.supported n then
    let info := match ci with
      | .defnInfo native =>
        if OmegaChecks.InitPort.SyntaxArray.supported n then .defnInfo {native with safety := .safe} else ci
      | _ => ci
    let some body := OmegaChecks.InitPort.alternativeBody? c.alternatives ci
      | return ← record n (.blocked "missing safe array implementation")
    for dep in usedConstants ci.type ++ usedConstants body do
      unless ← visit dep do return ← record n (.blocked "unavailable safe array implementation dependency" (some dep))
    let .ok decl := translateDecl info ci.type body
      | return ← record n (.blocked "invalid safe array implementation")
    let .ok env ← checkWithRetry (← get).env (keepImplementationSafety n decl) c.maxHeartbeats
      | return ← record n (.blocked "kernel rejected safe array implementation")
    modify fun s => {s with env}
    return ← record n .added
  if (ci.isUnsafe && !OmegaChecks.InitPort.UnsafeRuntime.isOriginal ci false) || ci.isPartial then return ← record n (.blocked "unsafe/partial")
  if let .inductInfo i := ci then
    let .ok f ← (family c.source i).run | return ← record n (.blocked "malformed family")
    if let some member := f.generated.find? (fun member => c.excluded.contains member) then
      return ← record n (.blocked "unavailable family member" (some member))
    modify fun s => {s with visiting := s.visiting.insert n}
    for dep in f.externals do
      if !(← visit dep) then return ← record n (.blocked "unavailable family dependency" (some dep))
    match ← checkWithRetry (← get).env f.decl c.maxHeartbeats with
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      return ← record n (.blocked ("kernel family: " ++ (msg.take 1200).toString))
    | .ok env =>
      for orig in f.generated do
        let some spec := c.source.find? orig | return ← record n (.blocked "missing family result" (some orig))
        if !agrees env (← expectGenerated c.source spec) (env.find? (portName orig)) then
          return ← record n (.blocked "generated kernel entry mismatch" (some orig))
      modify fun s => {s with env}
      return ← record n .added
  if ci matches .ctorInfo _ | .recInfo _ then
    let parent := match ci with | .ctorInfo v => v.induct | .recInfo v => v.all.head! | _ => Name.anonymous
    if !(← visit parent) then return ← record n (.blocked "unavailable family" (some parent))
    if let some generated := (← get).env.find? dest then
      if agrees (← get).env (← expectGenerated c.source ci) (some generated) then return ← record n .added
    return ← record n (.blocked "generated kernel entry mismatch" (some parent))
  if !(ci matches .thmInfo _ | .defnInfo _ | .opaqueInfo _) then
    return ← record n (.blocked "requires inductive family or primitive")
  modify fun s => {s with visiting := s.visiting.insert n}
  -- A dependent type can contain a proof emitted by simp. Keep its official
  -- conversion class and let the target kernel check the replacement.
  -- The finite list collector and the original named loop coexist in the subarray fold.
  let keepLoop := if n == `Subarray.foldl_toList then some `instIteratorLoopSubarrayIteratorIdOfMonad else none
  let specialized ← OmegaChecks.InitCompiler.finiteCollectors c.source ci.type (keepLoop := keepLoop)
  let compact ← OmegaChecks.InitCompiler.namedLogicalProjections c.source (compactNonzeroBounds c.source n specialized)
  let mut type := if !compact.equal ci.type && Kernel.isDefEqGuarded c.source {} ci.type compact then compact else ci.type
  for dep in usedConstants type do
    if !(← visit dep) then
      let rewritten := OmegaChecks.InitCompiler.constructiveCasts c.source ci.type c.proofRules true
      let rewritten ← OmegaChecks.InitCompiler.decidableProof c.source rewritten c.proofRules
      let mut blocker := dep
      let mut found := false
      let declared := OmegaChecks.InitPort.alternativeType? c.alternatives ci
      -- Prefer the declared constructive signature to a tactic-generated proof in its indices.
      for candidate in declared.toList ++ [rewritten] do
        let candidate ← OmegaChecks.InitCompiler.namedLogicalProjections c.source candidate
        if candidate == ci.type || (Kernel.check c.source {} candidate).toOption.isNone ||
            !Kernel.isDefEqGuarded c.source {} ci.type candidate then continue
        if let some missing ← (usedConstants candidate).toList.findM? (fun name => return !(← visit name)) then
          blocker := missing
          continue
        type := candidate
        found := true
        break
      unless found do return ← record n (.blocked "unavailable dependency" (some blocker))
      break
  -- Collection can specialize a named public loop to its implementation. Retain
  -- the original operand whenever its strict type is already convertible here,
  -- as the implementation can be sealed when its defining module is imported.
  if !specialized.equal ci.type && !type.equal ci.type then
    if ← ci.type.getUsedConstants.allM visit then
      let current := Environment.ofKernelEnv (← get).env
      let original := translate portName ci.type
      if (Kernel.check current {} original).isOk &&
          Kernel.isDefEqGuarded current {} original (translate portName type) then
        type := ci.type
  let some body := ci.value? (allowOpaque := true) | return ← record n (.blocked "no kernel body")
  let checkValue (value : Expr) (budget : Nat) : M Outcome := do
    let value ← OmegaChecks.InitCompiler.finiteCollectors c.source value (withinImplementation := true)
    let value ← OmegaChecks.InitCompiler.namedLogicalProjections c.source value
    for dep in usedConstants value do
      if dep == n && OmegaChecks.InitPort.PointerList.isOriginal ci false then continue
      if !(← visit dep) then return .blocked "unavailable dependency" (some dep)
    let .ok decl := translateDecl ci type value | return .blocked "open term"
    let check := if budget == c.maxHeartbeats then checkWithRetry else checkDecl
    match ← check (← get).env decl budget with
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      return .blocked ("kernel: " ++ (msg.take 1200).toString)
    | .ok next =>
      modify fun s => {s with env := next}
      return .added
  let attempt (value : Expr) (budget := c.maxHeartbeats) : M Outcome := do
    let result ← checkValue value budget
    if result matches .added then return result
    let compact := compactNonzeroBounds c.source n value
    unless compact.equal value do
      if (← checkValue compact budget) matches .added then return .added
    return result
  -- A binary comparison certificate for a Unicode or machine-word bound may
  -- exhaust the ordinary budget while the kernel checks its numeral conversions.
  let comparisonBudget := 400 * c.maxHeartbeats
  if let some alt := OmegaChecks.InitPort.alternativeBody? c.alternatives ci then
    let result ← attempt alt
    if result matches .added then return ← record n .added
    if let .blocked _ (some missing) := result then
      unless c.source.contains missing do
        -- An auxiliary theorem can live in a later official module than the requested root.
        -- Inline its checked alternative so the earlier module can be published independently.
        let localized := alt.replace fun e => do
          let .const name levels := e | none
          guard (!c.source.contains name)
          let .thmInfo info ← c.alternatives.find? name | none
          return info.value.instantiateLevelParams info.levelParams levels
        if !localized.equal alt && (← attempt localized) matches .added then
          return ← record n .added
    -- An alternative can contain index proofs inherited from the official statement.
    let mut candidate := alt
    if ci.isTheorem && (result matches .blocked _ (some _)) then
      let simplified := OmegaChecks.InitCompiler.constructiveCasts c.source alt c.proofRules true
      candidate ← OmegaChecks.InitCompiler.decidableProof c.source simplified c.proofRules
      if !candidate.equal alt then
        if (← attempt candidate) matches .added then return ← record n .added
    if let some certified := comparisonProofs c.source c.literalProofs alt n then
      if (← attempt certified comparisonBudget) matches .added then return ← record n .added
    if !candidate.equal alt then
      if let some certified := comparisonProofs c.source c.literalProofs candidate n then
        if (← attempt certified comparisonBudget) matches .added then return ← record n .added
  if ci.isTheorem then
    if let some proof ← orderTruthProof? c.source c.literalProofs type then
      if (← attempt proof) matches .added then return ← record n .added
  let result ← attempt body
  if result matches .added then return ← record n result
  let rewritten := OmegaChecks.InitCompiler.constructiveCasts c.source body c.proofRules
  if !rewritten.equal body then
    if (← attempt rewritten) matches .added then return ← record n .added
  let congruent := OmegaChecks.InitCompiler.constructiveCasts c.source body c.proofRules true
  if !congruent.equal rewritten && !congruent.equal body then
    if (← attempt congruent) matches .added then return ← record n .added
  let decided ← OmegaChecks.InitCompiler.decidableProof c.source rewritten c.proofRules
  if !decided.equal rewritten then
    if (← attempt (OmegaChecks.InitCompiler.constructiveCasts c.source decided c.proofRules)) matches .added then
      return ← record n .added
  let current := (← get).env
  let projected := OmegaChecks.InitCompiler.specializeProjections c.source body
    (fun dep => (current.find? (portName dep)).isNone)
  if !projected.equal body then
    let simplified := OmegaChecks.InitCompiler.constructiveCasts c.source projected c.proofRules true
    if (← attempt simplified) matches .added then return ← record n .added
  let recursive ← OmegaChecks.InitCompiler.Recursion.specialize c.source c.recursionRule ci decided
  if !recursive.equal decided then
    if (← attempt recursive) matches .added then return ← record n .added
    -- Some tuple recurrences need a proof connecting the unfolded branches to the
    -- official equation. Try it only after the direct pointwise law fails in the kernel.
    let aligned ← OmegaChecks.InitCompiler.Recursion.specialize c.source c.recursionRule ci decided true
    if !aligned.equal recursive && !aligned.equal decided then
      if (← attempt aligned) matches .added then return ← record n .added
  if let some certified := comparisonProofs c.source c.literalProofs decided n then
    -- Rechecking the closed proof of comparison costs proportionally more than
    -- applying the original opaque theorem; its bound remains deterministic.
    if (← attempt certified comparisonBudget) matches .added then return ← record n .added
  if ci.isTheorem then
    for previous in (← get).proofsByType.getD (theoremKey ci) [] do
      let some thm := c.source.find? previous | continue
      if thm.numLevelParams == ci.numLevelParams then
        if (← attempt (mkConst previous (ci.levelParams.map Level.param))) matches .added then
          return ← record n .added
  if ← alternateProof ci type then return true
  if ci.isTheorem then
    if let some term ← OmegaChecks.InitCompiler.finiteProof? c.source ci.type then
      if (← attempt term) matches .added then return ← record n .added
    if let some term ← OmegaChecks.InitCompiler.finiteProof? c.source ci.type true then
      if (← attempt term) matches .added then return ← record n .added
    let checked := (← get).env
    if (checked.find? (portName `Lean.Omega.Constraint.not_sat'_of_isImpossible)).isSome then
      if let some term ← OmegaChecks.InitPort.arithmeticProof? c.source ci.type then
        -- Avoid introducing a recursive dependency on a solver lemma still being proved.
        if (usedConstants term).all (fun dep => (checked.find? (portName dep)).isSome) then
          if (← attempt term) matches .added then return ← record n .added
  return ← record n result

def modulesIn (root : System.FilePath) : IO (Array Name) := do
  let mut names := #[`Init]
  for f in ← (root / "Init").walkDir do
    if f.extension == some "olean" then names := names.push (← moduleNameOfFileName f root)
  return names.qsort Name.lt

/-- Save the kernel-checked additions as an importable file. Seed constants remain imported. -/
def writeMonolithic (base : Environment) (final : Kernel.Environment)
    (output : System.FilePath) : IO Unit := do
  let mut cs := #[]
  for (n, c) in final.constants.toList do
    if !base.contains n then cs := cs.push c
  cs := cs.qsort fun a b => Name.lt a.name b.name
  let imports := base.header.moduleNames.map (fun owner => {module := owner, isExported := true : Import})
  let data : ModuleData := { isModule := false, imports, constNames := cs.map (·.name), constants := cs, extraConstNames := #[], entries := #[] }
  IO.FS.createDirAll output
  saveModuleData (output / "OmegaImported.olean") `OmegaImported data
  IO.println s!"Wrote {cs.size} kernel declarations to {output / "OmegaImported.olean"}"

def run (strictPath artifacts : System.FilePath) (outPath : String) (exclude : System.FilePath) (modules : List Name) : IO Unit := do
  let recursionRule ← OmegaChecks.InitCompiler.Recursion.loadRule
  let referenceTemplates ← importModules #[{module := `OmegaChecks.InitPort.BufferReference, importAll := true},
    {module := `OmegaChecks.InitPort.StateRunner, importAll := true},
    {module := `OmegaChecks.InitPort.ReferenceModify, importAll := true},
    {module := `OmegaChecks.InitPort.CancelFlag, importAll := true},
    {module := `OmegaChecks.InitPort.RandomState, importAll := true}] {} (level := .private)
  let handleEnv ← importModules #[{module := `OmegaChecks.InitPort.LogicalHandle}] {} (level := .private)
  let mut handles : NameMap OmegaChecks.InitPort.LogicalHandle.Templates := {}
  for api in OmegaChecks.InitPort.LogicalHandle.apis do
    handles := handles.insert api.pointed (← OmegaChecks.InitPort.LogicalHandle.templates api handleEnv)
  let typeNameTemplates ← OmegaChecks.InitPort.TypeName.templates (← importModules #[{module := `OmegaChecks.InitPort.TypeName}] {} (level := .private))
  let loopTemplates ← importModules #[{module := `OmegaChecks.InitPort.LawfulLoop}] {} (level := .private)
  let mut alternatives ← OmegaChecks.InitPort.loadAlternatives
  let inlineLoop := fun n => (loopTemplates.getModuleIdxFor? n).any fun idx =>
    loopTemplates.header.moduleNames[idx]! ∈ [`OmegaChecks.InitPort.LawfulLoop,
      `OmegaChecks.InitPort.RangeFix, `OmegaChecks.InitPort.Alternatives.RangeLoop]
  for rule in OmegaChecks.InitPort.LawfulLoop.rules do
    let some (.defnInfo impl) := loopTemplates.find? rule.implementation | throw <| IO.userError s!"missing {rule.implementation}"
    let body ← (Meta.deltaExpand impl.value inlineLoop (allowOpaque := true)).toIO'
      {fileName := "<well-founded iterator>", fileMap := default} {env := loopTemplates}
    alternatives := alternatives.insert rule.helper (.defnInfo {impl with value := body})
  let patternTemplates ← importModules #[{module := `OmegaChecks.InitPort.PatternMatch}] {} (level := .private)
  let isSplitLocal := fun n => patternTemplates.getModuleIdxFor? n == patternTemplates.getModuleIdx? `OmegaChecks.InitPort.CharacterSplit
  for rule in OmegaChecks.InitPort.PatternMatch.rules do
    let some (.defnInfo impl) := patternTemplates.find? rule.implementation | throw <| IO.userError s!"missing {rule.implementation}"
    let body ← (Meta.deltaExpand impl.value isSplitLocal (allowOpaque := true)).toIO'
      {fileName := "<character split>", fileMap := default} {env := patternTemplates}
    alternatives := alternatives.insert rule.helper (.defnInfo {impl with value := body})
  let some (.thmInfo splitStep) := patternTemplates.find? ``OmegaChecks.InitPort.CharacterSplit.splitStep
    | throw <| IO.userError "missing character split equation"
  let stepBody ← (Meta.deltaExpand splitStep.value isSplitLocal (allowOpaque := true)).toIO'
    {fileName := "<character split equation>", fileMap := default} {env := patternTemplates}
  alternatives := alternatives.insert ``String.Slice.Pattern.Model.split_bool_eq_internal
    (.thmInfo {splitStep with value := stepBody})
  let imageProofs ← importModules #[{module := `OmegaChecks.InitPort.Alternatives.GrindRing}] {} (level := .private)
  let some (.thmInfo cases) := imageProofs.find? ``OmegaChecks.InitPort.SemiringImage.denoteCases
    | throw <| IO.userError "missing semiring interpreter cases"
  let casesBody := cases.value.replace fun e => do
    let .const name levels := e | none
    guard <| `OmegaChecks.InitPort.Alternatives |>.isPrefixOf name
    return .const (name.replacePrefix `OmegaChecks.InitPort.Alternatives .anonymous) levels
  alternatives := alternatives.insert `Lean.Grind.CommRing.Expr.denoteSAsRing.eq_def
    (.thmInfo {cases with value := casesBody})
  let ruleModule := `OmegaChecks.InitCompiler.ProofRules
  let ruleEnv ← importModules #[{module := ruleModule}] {} (level := .private)
  let mut proofRules := {}
  for name in #[`notLtDecidable, `notLtOrDecidable, `iteCongr, `diteCongr, `forallDomain, `decideCongr, `natBEq, `intBEq, `intBNe, `intBLt, `intBLe,
                `polyBEq, `ringPowerBEq, `ringMonBEq, `ringPolyBEq] do
    let some info := ruleEnv.find? (ruleModule ++ name) | throw <| IO.userError s!"missing proof rule {name}"
    let .thmInfo th := info | throw <| IO.userError s!"expected a theorem for {name}"
    let localRule := fun n => ruleEnv.getModuleIdxFor? n == ruleEnv.getModuleIdx? ruleModule
    let body ← (Meta.deltaExpand th.value localRule (allowOpaque := true)).toIO'
      {fileName := "<constructive transport>", fileMap := default} {env := ruleEnv}
    proofRules := proofRules.insert name (.thmInfo {th with value := body})
  let lib ← getLibDir (← findSysroot)
  searchPathRef.set [lib]
  let allMods ← if modules.isEmpty then modulesIn lib else pure modules.toArray
  let imports := allMods.map fun n => {module := n : Import}
  unsafe enableInitializersExecution
  let source ← importModules imports {} (loadExts := true) (level := .private)
  if let some (.defnInfo runner) := source.find? `unsafeBaseIO then
    unless OmegaChecks.InitPort.EffectRun.isOriginal (.defnInfo runner) false do
      throw <| IO.userError "unexpected pinned unsafeBaseIO"
    alternatives := alternatives.insert runner.name (.defnInfo {runner with value := OmegaChecks.InitPort.EffectRun.withInitialWorld runner.value})
  let source ← OmegaChecks.InitPort.LawfulLoop.addReferences source loopTemplates
  let source ← OmegaChecks.InitPort.PatternMatch.addReferences source patternTemplates
  let mut referenceModels := {}
  for (consumer, owner) in [(`IO.FS.Stream.ofBuffer, `Init.System.IO), (`StateRefT'.run, `Init.Control.StateRef),
      (`ST.Prim.Ref.modify, `Init.System.ST), (`IO.stdGenRef, `Init.Data.Random)] do
    if source.contains consumer then
      referenceModels := referenceModels.insert owner (← OmegaChecks.InitPort.ReferenceSpecialization.models source referenceTemplates owner)
  let vis ← importModules imports {} (level := .exported)
  let mut publicNames : NameSet := {}
  for d in vis.header.moduleData do
    for n in d.constNames do
      if !isPrivateName n && !n.isInternalOrNum && !n.hasMacroScopes then
        publicNames := publicNames.insert n
  searchPathRef.set [strictPath]
  let mut seedModules := #[{module := `OmegaInit : Import}]
  for file in ← (strictPath / "OmegaInit").walkDir do
    if file.extension == some "olean" then
      seedModules := seedModules.push {module := ← moduleNameOfFileName file strictPath}
  let base ← importModules seedModules {}
  OmegaChecks.InitPort.NativeQuot.checkSupport base
  for (_, ci) in base.constants.toList do
    if ci.isAxiom || ci.isUnsafe || ci.isPartial then
      throw <| IO.userError s!"invalid strict seed {ci.name}"
  let initial ← (← mkEmptyEnvironment).toKernelEnv.replay base.constants.map₁
  let output ← IO.FS.Handle.mk outPath .write
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile exclude)
  let exclusions : Array (String × String) ← IO.ofExcept <| do
    if let .ok entries := fromJson? (α := Array (String × String)) config then return entries
    return (← fromJson? (α := Array String) config).map fun n => (n, "no computation correspondence")
  for (name, _) in exclusions do
    if base.contains (portName name.toName) then
      throw <| IO.userError s!"cannot exclude {name}: already present in the source seed"
  let excluded := exclusions.foldl (init := ({} : NameMap String)) fun acc (n, r) => acc.insert n.toName r
  let maxHeartbeats := (← IO.getEnv "OMEGA_PORT_HEARTBEATS").bind String.toNat? |>.getD 5000
  let literalProofs ← loadLiteralProofs strictPath
  let ctx := {source,base,publicNames,excluded,output,maxHeartbeats,literalProofs,alternatives,proofRules,referenceTemplates,referenceModels,handles,typeNameTemplates,recursionRule : Context}
  let action : M Unit := do
    for owner in source.header.moduleNames, data in source.header.moduleData do
      if owner.getRoot == `Init then
        for n in data.constNames do discard <| visit n
  let (_, s) ← action.run ctx |>.run {env := initial}
  output.flush
  writeMonolithic base s.env artifacts
  IO.println s!"{s.results.size} outcomes in {outPath}"

end InitKernelPort

def main (args : List String) : IO Unit := do
  if let ["--prepare-quot", dir] := args then
    return ← OmegaChecks.InitPort.NativeQuot.prepareSeed dir
  let dir :: artifacts :: out :: exclusions :: mods := args | throw <| IO.userError "expected seed, artifacts, report, exclusions, and official roots"
  InitKernelPort.run dir artifacts out exclusions (mods.map String.toName)
