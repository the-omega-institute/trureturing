import LeanInformationAuditRegAnalysis.SearchReduction.Runner

/-! Frozen, syntax-directed presentation retrieval. Hashes only locate entries;
actual support membership is compared before any certificate is attempted. -/
namespace LeanInformationAudit.SearchReduction
open Lean Meta Elab Tactic

/-- The shared executable directional lookup; the model proves its coverage. -/
def supportIncluded {α : Type} [BEq α] (target source : List α) : Bool :=
  target.all source.contains

def presentationLookup {α : Type} [BEq α] (target : List α) (entries : List (Name × List α)) :
    List (Name × List α) := entries.filter (supportIncluded target ·.2)

private abbrev primitive := DiskLookup.statementPrimitive

/-- Only noncomputational aliases are unfolded. Recursive definitions,
matchers, recursors and general computations are opaque. The visited graph
rejects cycles; fuel exhaustion is an error, never an opaque miss. -/
private abbrev aliasBody := DiskLookup.statementAliasBody

private abbrev instanceParameters := DiskLookup.statementInstanceParameters

/-- Rigid domain heads cannot be erased by alias expansion. Unknown heads
remain unconstrained; no reducible definition is treated as rigid. -/
inductive ScopeHead where
  | sortHead | forallHead | constant (name : Name) | variable (index : Nat) | other
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

private def binderTag : BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

private def scopeHead (e : Expr) : ScopeHead :=
  match e.consumeMData with
  | .sort _ => .sortHead
  | .forallE .. => .forallHead
  | e => match e.getAppFn.consumeMData with
    | .const n _ => .constant n
    | .bvar i => .variable i
    | _ => .other

/-- Read alias heads without normalizing their arguments or predicate bodies.
Unfinished head analysis remains unknown. The accepted N checks this same bound. -/
private def rigidScopeHead (env : Environment) (e : Expr) : Option ScopeHead :=
  go 64 {} e
where
  go (fuel : Nat) (seen : NameSet) (e : Expr) : Option ScopeHead := do
    let fuel + 1 := fuel | none
    match scopeHead e with
    | .constant n =>
      match (env.setExporting false).find? n with
      | some (.inductInfo _) => some (.constant n)
      | some (.defnInfo d) =>
        if primitive n || seen.contains n || instanceParameters d.type ||
            !aliasBody env d.value then none
        else
          let .const _ levels := e.getAppFn | none
          go fuel (seen.insert n)
            ((d.value.instantiateLevelParams d.levelParams levels).beta e.getAppArgs)
      | _ => none
    | .other => none
    | head => some head

private def rawScope (env : Environment) (e : Expr) : List (Nat × Option ScopeHead) :=
  match e with
  | .forallE _ d b bi => (binderTag bi, rigidScopeHead env d) :: rawScope env b
  | .mdata _ b => rawScope env b
  | _ => []

def scopePrefixCompatible : List (Nat × Option ScopeHead) → List (Nat × ScopeHead) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | (kind, head) :: rest, (kind', head') :: rest' =>
    kind == kind' && head.all (· == head') && scopePrefixCompatible rest rest'

/-- A target-independent overapproximation of the names that N can expose.
Only compiled expression constants and definition values are read. A cycle or
analysis depth limit widens to top; it never discards a possible source. -/
structure RawOriginBound where
  names : NameSet := {}
  unknown : Bool := false
  scope : List (Nat × Option ScopeHead) := []
  extensibleScope : Bool := true

/-- Only a rigid nonlogical terminal forbids additional projected binders. -/
private def rawExtensibleScope (env : Environment) (e : Expr) : Bool :=
  let body := e.getForallBody.consumeMData
  let extensible := match body.getAppFn.constName? with
    | some n => match (env.setExporting false).find? n with
      | some (.inductInfo _) => n == ``And || n == ``Iff
      | _ => true
    | none => true
  extensible

def rawScopeBound (env : Environment) (e : Expr) : RawOriginBound :=
  {scope := rawScope env e, extensibleScope := rawExtensibleScope env e}

private abbrev OriginMemo := Std.HashMap Name RawOriginBound

private def mergeOrigins (a b : RawOriginBound) : RawOriginBound :=
  { names := b.names.toList.foldl (fun s n => s.insert n) a.names,
    unknown := a.unknown || b.unknown }

private def expandableAlias (env : Environment) (name : Name) : Option DefinitionVal := do
  if primitive name then none else
  let .defnInfo d ← (env.setExporting false).find? name | none
  if !instanceParameters d.type && aliasBody env d.value then some d else none

private def originName (env : Environment) (fuel : Nat) (seen : NameSet)
    (name : Name) : StateM OriginMemo RawOriginBound := do
  match fuel with
  | 0 => return { unknown := true }
  | fuel + 1 =>
    if let some result := (← get)[name]? then return result
    if seen.contains name then return { unknown := true }
    let mut result : RawOriginBound := { names := ({} : NameSet).insert name }
    if let some d := expandableAlias env name then
      for dep in d.value.getUsedConstants do
        result := mergeOrigins result (← originName env fuel (seen.insert name) dep)
    modify (·.insert name result)
    return result

/-- A closed raw bound contains the input constants and every constant in
any expandable alias value it admits. This checker reads compiled data only. -/
def rawBoundClosed (env : Environment) (e : Expr) (bound : RawOriginBound) : Bool :=
  bound.scope == (rawScopeBound env e).scope &&
    bound.extensibleScope == (rawScopeBound env e).extensibleScope &&
    e.getUsedConstants.all bound.names.contains &&
    bound.names.toList.all (fun name => match expandableAlias env name with
      | none => true
      | some d => d.value.getUsedConstants.all bound.names.contains)

/-- A malformed or unfinished raw dependency certificate widens to top. -/
def certifyRawBound (env : Environment) (e : Expr) (bound : RawOriginBound) : RawOriginBound :=
  if bound.unknown || rawBoundClosed env e bound then bound else { unknown := true }

/-- Shared memoization changes cost only. Unknown bounds always retain sources. -/
def rawOrigins (env : Environment) (e : Expr) : StateM OriginMemo RawOriginBound := do
  let mut result : RawOriginBound := {}
  for name in e.getUsedConstants do
    result := mergeOrigins result (← originName env 1024 {} name)
  return certifyRawBound env e {result with
    scope := (rawScopeBound env e).scope,
    extensibleScope := (rawScopeBound env e).extensibleScope}

/-- Every bound used to reject a source has a checked raw alias closure. -/
theorem certified_raw_bound_closed (env : Environment) (e : Expr) (bound : RawOriginBound)
    (known : (certifyRawBound env e bound).unknown = false) :
    rawBoundClosed env e (certifyRawBound env e bound) = true := by
  by_cases h : (bound.unknown || rawBoundClosed env e bound) = true
  · simp only [certifyRawBound, h, ite_true] at known ⊢
    simpa [known] using h
  · simp [certifyRawBound, h] at known

/-- The complete expression rendering is a structural locator. Its constant
origins are retained as data, so lookup laws use lawful equality rather than
an unproved property of the compiler's pointer-optimized Expr equality. -/
structure PresentationKey where
  rendering : String
  constants : List Name
  scope : List (Nat × ScopeHead)
  isScope : Bool := false
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

private def expressionKey (telescope : List (Expr × BinderInfo)) (e : Expr) : PresentationKey :=
  { rendering := reprStr e, constants := e.getUsedConstants.toList,
    scope := telescope.map fun (domain, kind) => (binderTag kind, scopeHead domain) }

/-- Key constructors and numeral constructors are generated syntax, not source
anchors. All other compiled constants must have an origin in the source. -/
def originAnchor (env : Environment) (name : Name) : Bool :=
  !#[`Nat, `Int, `Neg.neg, `OfNat.ofNat, `Int.instNegInt, `instOfNat].contains name &&
  match (env.setExporting false).find? name with
    | none | some (.ctorInfo _) => false
    | _ => true

/-- Every key, including a neutral scope marker, retains its telescope. -/
def scopeKeyCompatible (bound : RawOriginBound) (key : PresentationKey) : Bool :=
  scopePrefixCompatible bound.scope key.scope &&
    (bound.extensibleScope || bound.scope.length == key.scope.length)

def scopeNecessary (bound : RawOriginBound) (keys : List PresentationKey) : Bool :=
  keys.all (scopeKeyCompatible bound)

/-- Short-circuit the same prefix predicate before analyzing later domains. -/
def sourceScopePrefix (env : Environment) : Expr → List (Nat × ScopeHead) → Bool
  | .forallE _ domain body kind, (tag, head) :: rest =>
    binderTag kind == tag && (rigidScopeHead env domain).all (· == head) &&
      sourceScopePrefix env body rest
  | .forallE .., [] => false
  | .mdata _ body, scope => sourceScopePrefix env body scope
  | _, _ => true

def sourceBinderCount : Expr → Nat
  | .forallE _ _ body _ => 1 + sourceBinderCount body
  | .mdata _ body => sourceBinderCount body
  | _ => 0

def sourceScopeNecessary (env : Environment) (source : Expr)
    (keys : List PresentationKey) : Bool :=
  keys.all fun key => sourceScopePrefix env source key.scope &&
    (rawExtensibleScope env source || sourceBinderCount source == key.scope.length)

theorem source_scope_prefix_eq (env : Environment) (source : Expr)
    (scope : List (Nat × ScopeHead)) :
    sourceScopePrefix env source scope = scopePrefixCompatible (rawScope env source) scope := by
  induction source generalizing scope <;> cases scope <;>
    simp_all [sourceScopePrefix, rawScope, scopePrefixCompatible]

theorem source_binder_count_eq (env : Environment) (source : Expr) :
    sourceBinderCount source = (rawScope env source).length := by
  induction source <;> simp_all [sourceBinderCount, rawScope, Nat.add_comm]

/-- Production's cheaper prefilter is exactly the certified scope predicate. -/
theorem source_scope_necessary_eq (env : Environment) (source : Expr)
    (keys : List PresentationKey) :
    sourceScopeNecessary env source keys = scopeNecessary (rawScopeBound env source) keys := by
  unfold sourceScopeNecessary scopeNecessary
  congr 1
  funext key
  simp only [scopeKeyCompatible, rawScopeBound, source_scope_prefix_eq,
    source_binder_count_eq env source]

def keyOriginCompatible (env : Environment) (bound : RawOriginBound)
    (key : PresentationKey) : Bool :=
  bound.unknown || (scopeKeyCompatible bound key &&
    key.constants.all (fun n => !originAnchor env n || bound.names.contains n))

/-- The raw necessary condition reads the raw alias dependency bound only. -/
def rawNecessary (env : Environment) (targetAtoms : List PresentationKey)
    (bound : RawOriginBound) : Bool :=
  targetAtoms.all (keyOriginCompatible env bound)

abbrev normalizeSyntax := DiskLookup.normalizeStatementSyntax

private structure Affine where
  constant : Int := 0
  terms : List (Expr × Int) := []
  deriving Inhabited

private def affineAdd (a b : Affine) : Affine := Id.run do
  let mut terms := a.terms
  for (atom, coefficient) in b.terms do
    match terms.find? (fun t => t.1 == atom) with
    | some old => terms := (atom, old.2 + coefficient) :: terms.filter (fun t => t.1 != atom)
    | none => terms := (atom, coefficient) :: terms
  return {constant := a.constant + b.constant, terms := terms.filter (fun t => t.2 != 0)}

private def affineScale (n : Int) (a : Affine) : Affine :=
  {constant := n * a.constant, terms := a.terms.map (fun (e, c) => (e, n*c))}

private def numeral (e : Expr) : Option Nat := do
  if let .lit (.natVal n) := e then return n
  if e.isAppOf ``OfNat.ofNat then
    if let .lit (.natVal n) := e.getArg! 1 then return n
  none

private partial def affine (e : Expr) : Affine :=
  if let some n := numeral e then {constant := n}
  else if e.isAppOf ``HAdd.hAdd || e.isAppOf ``Nat.add || e.isAppOf ``Int.add then
    affineAdd (affine (e.getAppArgs[e.getAppNumArgs-2]!)) (affine e.getAppArgs.back!)
  else if e.isAppOf ``HMul.hMul || e.isAppOf ``Nat.mul || e.isAppOf ``Int.mul then
    let left := e.getAppArgs[e.getAppNumArgs-2]!
    let right := e.getAppArgs.back!
    if let some n := numeral left then affineScale n (affine right)
    else if let some n := numeral right then affineScale n (affine left)
    else {terms := [(e, 1)]}
  else if e.isAppOf ``Int.sub ||
      (e.isAppOf ``HSub.hSub && e.getAppArgs.any (·.isConstOf ``Int)) then
    affineAdd (affine (e.getAppArgs[e.getAppNumArgs-2]!))
      (affineScale (-1) (affine e.getAppArgs.back!))
  else if e.isAppOf ``Neg.neg || e.isAppOf ``Int.neg then
    affineScale (-1) (affine e.getAppArgs.back!)
  else if e.isAppOf ``Nat.succ then affineAdd (affine e.getAppArgs.back!) {constant := 1}
  else {terms := [(e, 1)]}

private def arithmeticNeutral (e : Expr) : Bool := Id.run do
  let eq := e.isAppOfArity ``Eq 3
  let le := e.isAppOf ``LE.le || e.isAppOf ``Nat.le || e.isAppOf ``Int.le
  let lt := e.isAppOf ``LT.lt || e.isAppOf ``Nat.lt || e.isAppOf ``Int.lt
  unless eq || le || lt do return false
  let args := e.getAppArgs
  if args.size < 2 then return false
  let difference := affineAdd (affine args.back!)
    (affineScale (-1) (affine args[args.size-2]!))
  if eq then return difference.constant == 0 && difference.terms.isEmpty
  let natural := args.any (·.isConstOf ``Nat)
  return (if lt then difference.constant > 0 else difference.constant ≥ 0) &&
    difference.terms.all (fun (_, c) => natural && c ≥ 0)

private def syntacticNeutral (e : Expr) : Bool :=
  e.isConstOf ``True || arithmeticNeutral e

private partial def nameless : Expr → Expr
  | .forallE _ d b bi => .forallE .anonymous (nameless d) (nameless b) bi
  | .lam _ d b bi => .lam .anonymous (nameless d) (nameless b) bi
  | .app f a => .app (nameless f) (nameless a)
  | .mdata _ b => nameless b
  | e => e

/-- Complete structural expression keys retain the canonical affine vector.
Expression hashes accelerate comparison without replacing structural equality. -/
private def componentKey (telescope : List (Expr × BinderInfo)) (e : Expr) : Expr := Id.run do
  let eq := e.isAppOfArity ``Eq 3
  let arithmetic := eq || e.isAppOf ``LE.le || e.isAppOf ``LT.lt ||
    e.isAppOf ``Nat.le || e.isAppOf ``Nat.lt || e.isAppOf ``Int.le || e.isAppOf ``Int.lt
  let withScope := fun key => telescope.foldr
    (fun (domain, kind) body => Expr.forallE .anonymous (nameless domain) body kind) key
  if arithmetic && e.getAppNumArgs ≥ 2 then
    let args := e.getAppArgs
    let mut vector := affineAdd (affine args.back!)
      (affineScale (-1) (affine args[args.size-2]!))
    vector := {vector with terms := vector.terms.map fun (a, c) => (nameless a, c)}
    let sorted := vector.terms.toArray.qsort (fun a b =>
      if a.1.hash != b.1.hash then a.1.hash < b.1.hash
      else if a.1 == b.1 then false
      else reprStr (nameless a.1) < reprStr (nameless b.1))
    vector := {vector with terms := sorted.toList.filter (fun t => t.2 != 0)}
    if eq && (vector.terms.head?.map (fun t => decide (t.2 < 0))).getD
        (decide (vector.constant < 0)) then
      vector := affineScale (-1) vector
    let relation := if eq then "eq" else if e.isAppOf ``LT.lt || e.isAppOf ``Nat.lt ||
      e.isAppOf ``Int.lt then "lt" else "le"
    let domain := if e.isAppOf ``Nat.le || e.isAppOf ``Nat.lt then mkConst ``Nat
      else if e.isAppOf ``Int.le || e.isAppOf ``Int.lt then mkConst ``Int
      else if args.size > 2 then nameless args[0]! else mkConst `_presentationDomain
    let terms := vector.terms.toArray.map fun (a, c) =>
      mkAppN (mkConst `_presentationTerm) #[nameless a, toExpr c]
    return withScope <| mkAppN (mkConst (Name.mkSimple ("_presentation_" ++ relation)))
      #[domain, toExpr vector.constant, mkAppN (mkConst `_presentationVector) terms]
  return withScope (nameless e)

/-- Nonneutral component sets form the directional index. The complete
outer telescope is part of every component. Iff contributes its two views. -/
partial def syntaxAtoms (e : Expr) (telescope : List (Expr × BinderInfo) := []) :
    List PresentationKey :=
  if let .forallE _ d b bi := e then syntaxAtoms b (telescope ++ [(d, bi)])
  else Id.run do
    let marker := telescope.foldr
      (fun (domain, kind) body => Expr.forallE .anonymous (nameless domain) body kind)
      (mkConst `_presentationScope)
    let scope := {(expressionKey telescope marker) with isScope := true}
    if syntacticNeutral e then return [scope]
    if e.isAppOfArity ``And 2 then
      return (scope :: syntaxAtoms e.appFn!.appArg! telescope ++
        syntaxAtoms e.appArg! telescope).eraseDups
    if e.isAppOfArity ``Iff 2 then
      let p := e.appFn!.appArg!
      let q := e.appArg!
      let forward := mkForall .anonymous .default p (q.liftLooseBVars 0 1)
      let backward := mkForall .anonymous .default q (p.liftLooseBVars 0 1)
      return (scope :: syntaxAtoms forward telescope ++ syntaxAtoms backward telescope).eraseDups
    return [scope, expressionKey telescope (componentKey telescope e)]

/-- The target-independent origin check certifies the actual keys returned by
N. A violated origin invariant is an execution error, never an opaque miss. -/
def normalizedAtomsWithOrigins (env : Environment) (e : Expr)
    (bound : RawOriginBound) : Except String (List PresentationKey) := do
  let atoms := syntaxAtoms (← normalizeSyntax env e)
  if scopeNecessary (rawScopeBound env e) atoms && rawNecessary env atoms bound then return atoms
  else throw ("search.presentation_origin_invariant: " ++
    reprStr (atoms.flatMap (·.constants) |>.filter fun n =>
      originAnchor env n && !bound.names.contains n))

def normalizedAtoms (env : Environment) (e : Expr) : Except String (List PresentationKey) :=
  normalizedAtomsWithOrigins env e ((rawOrigins env e).run' {})

/-- Every exact directional match of actual, origin-certified normalized keys
passes the raw necessary condition. The predicate certifies all source keys,
independently of the requested target, before this monotonicity is applied. -/
theorem raw_necessary_of_normalized_match (env : Environment) (source : Expr)
    (bound : RawOriginBound) (sourceAtoms targetAtoms : List PresentationKey)
    (normalized : normalizedAtomsWithOrigins env source bound = .ok sourceAtoms)
    (matched : supportIncluded targetAtoms sourceAtoms = true) :
    rawNecessary env targetAtoms bound = true := by
  have valid : rawNecessary env sourceAtoms bound = true := by
    unfold normalizedAtomsWithOrigins at normalized
    cases hn : normalizeSyntax env source with
    | error err => simp [hn, bind, Except.bind] at normalized
    | ok value =>
      simp only [hn, bind, Except.bind] at normalized
      split at normalized
      · have eq : syntaxAtoms value = sourceAtoms := Except.ok.inj normalized
        have h := ‹(scopeNecessary (rawScopeBound env source) (syntaxAtoms value) &&
            rawNecessary env (syntaxAtoms value) bound) = true›
        simp only [Bool.and_eq_true] at h
        simpa only [eq] using h.2
      · contradiction
  simp only [rawNecessary, List.all_eq_true] at valid ⊢
  simp only [supportIncluded, List.all_eq_true, List.contains_iff_mem] at matched
  exact fun a ha => valid a (matched a ha)

/-- Adding the raw prefilter preserves the actual directional query. -/
theorem raw_prefilter_preserves_match (env : Environment) (source : Expr)
    (bound : RawOriginBound) (sourceAtoms targetAtoms : List PresentationKey)
    (normalized : normalizedAtomsWithOrigins env source bound = .ok sourceAtoms) :
    (rawNecessary env targetAtoms bound && supportIncluded targetAtoms sourceAtoms) =
      supportIncluded targetAtoms sourceAtoms := by
  cases h : supportIncluded targetAtoms sourceAtoms
  · simp
  · simp [raw_necessary_of_normalized_match env source bound sourceAtoms targetAtoms normalized h]

/-- The production domain is exactly the safe, visible compiled enumeration.
There is no unaccounted proposition or rigid-telescope prefilter. -/
def productionAllowed (name : Name) (info : ConstantInfo) : Bool :=
  !info.isUnsafe && !(name.isInternalDetail && !isPrivateName name)

def productionDomain (entries : Array (Name × ConstantInfo)) : Array (Name × ConstantInfo) :=
  entries.filter (fun (name, info) => productionAllowed name info)

/-- The early telescope predicate is certified by N itself, including neutral
scope markers. It is not an independent heuristic rejection. -/
theorem scope_necessary_of_normalized_match (env : Environment) (source : Expr)
    (bound : RawOriginBound) (sourceAtoms targetAtoms : List PresentationKey)
    (normalized : normalizedAtomsWithOrigins env source bound = .ok sourceAtoms)
    (matched : supportIncluded targetAtoms sourceAtoms = true) :
    scopeNecessary (rawScopeBound env source) targetAtoms = true := by
  have valid : scopeNecessary (rawScopeBound env source) sourceAtoms = true := by
    unfold normalizedAtomsWithOrigins at normalized
    cases hn : normalizeSyntax env source with
    | error err => simp [hn, bind, Except.bind] at normalized
    | ok value =>
      simp only [hn, bind, Except.bind] at normalized
      split at normalized
      · have eq : syntaxAtoms value = sourceAtoms := Except.ok.inj normalized
        have h := ‹(scopeNecessary (rawScopeBound env source) (syntaxAtoms value) &&
            rawNecessary env (syntaxAtoms value) bound) = true›
        simp only [Bool.and_eq_true] at h
        simpa only [eq] using h.1
      · contradiction
  simp only [scopeNecessary, List.all_eq_true] at valid ⊢
  simp only [supportIncluded, List.all_eq_true, List.contains_iff_mem] at matched
  exact fun a ha => valid a (matched a ha)

/-- Instantiated by the actual production loop for every compiled declaration,
its complete source type and its memoized raw bound. All preceding filters are
included; exact membership is still directional inclusion of N's scoped keys. -/
theorem production_lookup_complete (env : Environment)
    (entries : Array (Name × ConstantInfo)) (entry : Name × ConstantInfo)
    (bound : RawOriginBound) (sourceAtoms targetAtoms : List PresentationKey)
    (normalized : normalizedAtomsWithOrigins env entry.2.type bound = .ok sourceAtoms) :
    (entry ∈ productionDomain entries ∧
      (sourceScopeNecessary env entry.2.type targetAtoms &&
        rawNecessary env targetAtoms bound && supportIncluded targetAtoms sourceAtoms) = true) ↔
    (entry ∈ entries ∧ productionAllowed entry.1 entry.2 = true ∧
      supportIncluded targetAtoms sourceAtoms = true) := by
  simp only [source_scope_necessary_eq]
  have scope := scope_necessary_of_normalized_match env entry.2.type bound sourceAtoms targetAtoms
  have raw := raw_necessary_of_normalized_match env entry.2.type bound sourceAtoms targetAtoms
  constructor
  · rintro ⟨member, checks⟩
    have member := Array.mem_filter.mp member
    simp only [Bool.and_eq_true] at checks
    exact ⟨member.1, member.2, checks.2⟩
  · rintro ⟨member, allowed, matched⟩
    exact ⟨Array.mem_filter.mpr ⟨member, allowed⟩, by simp [scope normalized matched,
      raw normalized matched, matched]⟩

def normalizedLookup (env : Environment) (target : Expr)
    (entries : List (Name × List PresentationKey)) :
    Except String (List (Name × List PresentationKey)) := do
  return presentationLookup (← normalizedAtoms env target) entries

/-- A leaf certificate sees the common telescope and at most one source view.
No baseline fact index, source proof or other source component is available. -/
private def onePremise (target : Expr) (source? : Option Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let type ← match source? with | some s => mkArrow s target | none => pure target
    let goal ← mkFreshExprMVar type
    let goals ← (Term.withoutErrToSorry <| Tactic.run goal.mvarId! do
      if source?.isSome then evalTactic (← `(tactic| intro _presentationPremise))
      evalTactic (← `(tactic| first | assumption | rfl | exact True.intro | omega))).run'
    if goals.isEmpty then return some (← instantiateMVars goal)
  catch ex =>
    if ex.isRuntime || ex.isInterrupt || ex.isMaxHeartbeat then throw ex
  saved.restore
  return none

private partial def viewTypes (type : Expr) : MetaM (Array (Expr × List Name)) := do
  let type ← withReducible <| whnf type
  let mut result := if type.isAppOfArity ``And 2 || type.isAppOfArity ``Iff 2 then #[]
    else #[(type, [])]
  if type.isAppOfArity ``And 2 then
    for (part, projection) in #[(type.appFn!.appArg!, ``And.left), (type.appArg!, ``And.right)] do
      result := result ++ (← viewTypes part).map (fun (t, p) => (t, projection :: p))
  if type.isAppOfArity ``Iff 2 then
    result := result ++ #[(← mkArrow type.appFn!.appArg! type.appArg!, [``Iff.mp]),
      (← mkArrow type.appArg! type.appFn!.appArg!, [``Iff.mpr])]
  return result

private def projectView (h : Expr) (path : List Name) : MetaM Expr :=
  path.foldlM (fun e n => mkAppM n #[e]) h

private partial def assemble (target source : Expr) : MetaM (Option Expr) := do
  let target ← withReducible <| whnf target
  if target == source then
    return ← withLocalDeclD `_singleSource source fun h => do
      return some (← mkLambdaFVars #[h] h)
  if target.isAppOfArity ``And 2 || target.isAppOfArity ``Iff 2 then
    let iff := target.isAppOfArity ``Iff 2
    let leftType ← if iff then mkArrow target.appFn!.appArg! target.appArg!
      else pure target.appFn!.appArg!
    let rightType ← if iff then mkArrow target.appArg! target.appFn!.appArg!
      else pure target.appArg!
    let some left ← assemble leftType source | return none
    let some right ← assemble rightType source | return none
    return ← withLocalDeclD `_singleSource source fun h => do
      let constructor := if iff then ``Iff.intro else ``And.intro
      let proof ← mkAppM constructor #[mkApp left h, mkApp right h]
      return some (← mkLambdaFVars #[h] proof)
  if let some proof ← onePremise target none then
    return ← withLocalDeclD `_singleSource source fun h => do
      return some (← mkLambdaFVars #[h] proof)
  for (view, path) in ← viewTypes source do
    if let some proof ← onePremise target (some view) then
      return ← withLocalDeclD `_singleSource source fun h => do
        return some (← mkLambdaFVars #[h] (mkApp proof (← projectView h path)))
  return none

private partial def singleTelescope (target source : Expr) (xs : Array Expr) :
    MetaM (Option Expr) := do
  match target, source with
  | .forallE n d b bi, .forallE _ d' b' bi' =>
    if bi != bi' then return none
    unless ← withReducible <| isDefEq d d' do return none
    withLocalDecl n bi d fun x => singleTelescope (b.instantiate1 x) (b'.instantiate1 x) (xs.push x)
  | _, .forallE .. => return none
  | _, _ =>
    let some body ← assemble target source | return none
    return ← withLocalDeclD `_wholeSource (← mkForallFVars xs source) fun h => do
      let proof ← mkLambdaFVars xs (mkApp body (mkAppN h xs))
      return some (← mkLambdaFVars #[h] proof)

/-- N's definitional certificate is a reflexivity term checked against the
normalized expression. It is closed over the common telescope for kernel use. -/
def normalizeCertified (e : Expr) : MetaM Expr := do
  let normalized ← match normalizeSyntax (← getEnv) e with
    | .ok e => pure e | .error err => throwError err
  let type ← mkEq e normalized
  let proof ← mkEqRefl e
  let xs := (← getLCtx).getFVarIds.map mkFVar
  let proof ← mkLambdaFVars xs proof
  let type ← mkForallFVars xs type
  let levels := (collectLevelParams {} type).params.toList
  discard <| checkProof (← mkFreshUserName `_normalizationCertificate) levels type proof
  return normalized

/-- Match the complete common telescope before constructing the source-arrow
certificate. The actual source theorem is restored only by the caller. -/
def singleSourceConversion (target source : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  let targetAtoms ← match normalizedAtoms env target with
    | .ok atoms => pure atoms | .error err => throwError err
  if targetAtoms.all (·.isScope) then
    let target ← normalizeCertified target
    if let some conversion ← singleTelescope target source #[] then return some conversion
  let sourceAtoms ← match normalizedAtoms env source with
    | .ok atoms => pure atoms | .error err => throwError err
  unless supportIncluded targetAtoms sourceAtoms do return none
  let target ← normalizeCertified target
  let source ← normalizeCertified source
  singleTelescope target source #[]
end LeanInformationAudit.SearchReduction
