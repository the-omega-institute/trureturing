module

public import Lean
import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitCompiler.ProofRules
import OmegaChecks.InitCompiler.Equivalence
import OmegaChecks.InitCompiler.NatProofs

/-! Translate proof terms from the pinned Init environment into the strict namespace. -/

open Lean
namespace OmegaChecks.InitCompiler

private initialize cachedOwner : IO.Ref (Option (Name × Environment)) ← IO.mkRef none

/-- The Lean frontend repeatedly elaborates declarations in the same source module. -/
public def officialEnvironment (owner : Name) : IO Environment := do
  if let some (cached, env) ← cachedOwner.get then
    if cached == owner then return env
  let env ← importModules #[{module := owner}] {}
  cachedOwner.set (some (owner, env))
  return env

private abbrev Helpers := Std.HashMap Name (List Name × Expr)

/-- Preserve sharing while expanding the private implementation of an official proof. -/
private partial def translateTerm (env : Environment) (visiting : NameSet) (term : Expr) :
    StateT Helpers (Except String) Expr := do
  for n in term.getUsedConstants do
    unless isPrivateName n do continue
    if (← get).contains n then continue
    if visiting.contains n then throw s!"recursive private proof dependency {n}"
    let some info := env.find? n | throw s!"unknown private proof dependency {n}"
    let some idx := env.getModuleIdxFor? n | throw s!"private helper {n} has no official owner"
    unless env.header.moduleNames[idx]!.getRoot == `Init do throw s!"private helper outside Init: {n}"
    if info.isUnsafe || info.isPartial then throw s!"inadmissible private helper {n}"
    let some value := info.value? (allowOpaque := true) | throw s!"no kernel term for private helper {n}"
    let value ← translateTerm env (visiting.insert n) value
    modify (·.insert n (info.levelParams, value))
  if (term.find? (fun e => e matches .lit (.strVal _))).isSome then
    throw "strict string literal encoding is unavailable"
  let helpers ← get
  let rec go (e : Expr) : Expr :=
    e.replace fun
      | .const n us =>
        if let some (params, body) := helpers[n]? then some (body.instantiateLevelParams params us)
        else some (.const (if RootNames.usesRoot n then n else `Omega ++ n) us)
      | .proj n i x => some (.proj (if RootNames.usesRoot n then n else `Omega ++ n) i (go x))
      | _ => none
  return go term

public def translateProofTerm (env : Environment) (term : Expr) : Except String Expr :=
  (translateTerm env {} term).run' {}

/-- Translate a recursive equation with self-calls bound to its checked strict definition. -/
public def translateRecursiveBody (env : Environment) (recFn : DefinitionVal) (target : Name) : Except String Expr :=
  let self := mkConst target (recFn.levelParams.map Level.param)
  (translateTerm env {} recFn.value).run' (({} : Helpers).insert recFn.name (recFn.levelParams, self))

private def castProof (back : Bool) (p q eq input : Expr) : Expr :=
  mkApp4 (mkConst (if back then `Eq.mpr else `Eq.mp) [.zero]) p q eq input

/-- Pointwise equality of mapped functions suffices at a particular container. -/
private def mapCongruence? (h xs : Expr) : Option Expr := do
  guard (h.isAppOfArity `congrArg 6)
  let #[_, _, f, g, map, eq] := h.getAppArgs | none
  guard (eq.isAppOfArity `funext 5)
  let .const mapName us := map.getAppFn | none
  let (rule, container, inst) ← match mapName with
    | `List.map => some (`List.map_congr_left, `List, `List.instMembership)
    | `Array.map => some (`Array.map_congr_left, `Array, `Array.instMembership)
    | `List.filter => some (`List.filter_congr, `List, `List.instMembership)
    | _ => none
  let some α := map.getAppArgs[0]? | none
  let u :: _ := us | none
  let lift := fun (e : Expr) => e.liftLooseBVars 0 1
  let member := mkApp5 (mkConst `Membership.mem [u,u]) (lift α) (mkApp (mkConst container [u]) (lift α))
    (mkApp (mkConst inst [u]) (lift α)) (lift xs) (mkBVar 0)
  let pointwise := eq.getAppArgs[4]!
  let proof := Expr.lam `a α (.lam `mem member
    ((pointwise.liftLooseBVars 0 2).beta #[mkBVar 1]) .default) .default
  if mapName == `List.filter then return mkApp5 (mkConst rule us) α f g xs proof
  let #[_, β] := map.getAppArgs | none
  return mkApp6 (mkConst rule us) α xs β f g proof

/-- The Boolean folds already have pointwise congruence under the predicate binder. -/
private def predicateCongruence? (op eq : Expr) : Option Expr := do
  guard (eq.isAppOfArity `funext 5)
  let .const name us := op.getAppFn | none
  let #[α, xs] := op.getAppArgs | none
  let rule ← match name with
    | `List.any => some `List.any_congr
    | `List.all => some `List.all_congr
    | _ => none
  let u :: _ := us | none
  let refl := mkApp2 (mkConst `Eq.refl [.succ u]) (mkApp (mkConst `List us) α) xs
  let args := eq.getAppArgs
  return mkAppN (mkConst rule us) #[α, xs, xs, refl, args[2]!, args[3]!, args[4]!]

/-- Lift a logical equivalence through the connectives in a simp congruence. -/
private partial def congrIff? (p q iff a b : Expr) : Option Expr := do
  if a == b then return mkApp (mkConst `Iff.rfl) a
  if a == p && b == q then return iff
  if a.isArrow && b.isArrow then
    let (a₁, a₂) := (a.bindingDomain!, a.bindingBody!.lowerLooseBVars 1 1)
    let (b₁, b₂) := (b.bindingDomain!, b.bindingBody!.lowerLooseBVars 1 1)
    return mkApp6 (mkConst `imp_congr) a₁ a₂ b₁ b₂
      (← congrIff? p q iff a₁ b₁) (← congrIff? p q iff a₂ b₂)
  let some n := a.getAppFn.constName? | none
  guard (b.getAppFn.isConstOf n)
  match n, a.getAppArgs, b.getAppArgs with
  | `Not, #[x], #[y] => return mkApp3 (mkConst `not_congr) x y (← congrIff? p q iff x y)
  | _, #[x, y], #[z, w] =>
    let rule ← match n with
      | `And => some `and_congr
      | `Or => some `or_congr
      | `Iff => some `iff_congr
      | _ => none
    return mkApp6 (mkConst rule) x z y w (← congrIff? p q iff x z) (← congrIff? p q iff y w)
  | _, _, _ => none

private def propositionChange? (h : Expr) (fuel : Nat) : Option (Expr × Expr × Expr) := do
  let fuel + 1 := fuel | none
  match h.getAppFn.constName?, h.getAppArgs with
  | some `congrArg, #[.sort .zero, _, p, q, _, eq] => return (p, q, eq)
  | some `congrArg, #[_, _, _, _, _, eq]
  | some `congrFun, #[_, _, _, _, eq, _]
  | some `congrFun', #[_, _, _, _, eq, _]
  | some `id, #[_, eq] => propositionChange? eq fuel
  | _, _ => none

/-- A simp proof sometimes builds an equality of propositions only to transport a
proof along it. Compose the underlying implications when the equality is consumed. -/
private partial def transport? (source : Environment) (back : Bool) (p q eq input : Expr)
    (fuel : Nat) : Option Expr := do
  let fuel + 1 := fuel | none
  if back && q.isConstOf `True then
    if let some proof := natComparison? p then return proof
  let .const n us := eq.getAppFn | none
  let xs := eq.getAppArgs
  match n, xs with
  | `id, #[_, h] => transport? source back p q h input fuel
  | `propext, #[_, _, iff] =>
    if iff.isAppOfArity `Iff.intro 4 then
      return iff.getAppArgs[if back then 3 else 2]!.beta #[input]
    return mkApp4 (mkConst (if back then `Iff.mpr else `Iff.mp)) p q iff input
  | `Eq.refl, _ | `rfl, _ => return input
  | `Eq.symm, #[_, a, b, h] => transport? source (!back) a b h input fuel
  | `Eq.trans, #[_, a, b, c, h, k] =>
    let through := fun p q h input => (transport? source back p q h input (fuel / 2)).getD
      (castProof back p q h input)
    return if back then through a b h (through b c k input) else through b c k (through a b h input)
  | `eq_true, #[_, h] => return if back then h else mkConst `True.intro
  | `eq_false, #[a, h] | `eq_false', #[a, h] =>
    return if back then mkApp2 (mkConst `False.elim [.zero]) a input else h.beta #[input]
  | `congr, #[_, _, f, g, b, d, hf, hb] =>
    let .app op a := f | none
    let .app op' c := g | none
    guard (op == op')
    let rule ← match op.constName? with
      | some `And => some `and_congr
      | some `Or => some `or_congr
      | some `Iff => some `iff_congr
      | _ => none
    let fromEq := fun a b h => do
      if a == b then return mkApp (mkConst `Iff.rfl) a
      let dir := fun rev dom => do
        let lift := fun (e : Expr) => e.liftLooseBVars 0 1
        let map ← transport? source rev (lift a) (lift b) (lift h) (mkBVar 0) (fuel / 4)
        return Expr.lam `hp dom map .default
      return mkApp4 (mkConst `Iff.intro) a b (← dir false a) (← dir true b)
    let ac ← if a == c then pure (mkApp (mkConst `Iff.rfl) a) else do
      let (x, y, h) ← propositionChange? hf fuel
      guard (x == a && y == c)
      fromEq a c h
    let lifted := mkApp6 (mkConst rule) a c b d ac (← fromEq b d hb)
    return mkApp4 (mkConst (if back then `Iff.mpr else `Iff.mp)) p q lifted input
  | `congrArg, _ | `congrFun, _ | `congrFun', _ =>
    let (a, b, h) ← propositionChange? eq fuel
    let localMap := fun (rev : Bool) (dom : Expr) => do
      let under := fun (e : Expr) => e.liftLooseBVars 0 1
      let term ← transport? source rev (under a) (under b) (under h) (mkBVar 0) (fuel / 2)
      return Expr.lam `hp dom term .default
    let equiv := mkApp4 (mkConst `Iff.intro) a b (← localMap false a) (← localMap true b)
    let lifted ← congrIff? a b equiv p q
    return mkApp4 (mkConst (if back then `Iff.mpr else `Iff.mp)) p q lifted input
  | _, _ =>
    -- Unfold wrappers like eq_self and generated simp lemmas only at a cast.
    -- A first-class result of type p = q must still prove the original equality.
    let some ci := source.find? n | none
    let some value := ci.value? (allowOpaque := true) | none
    let rhs := (value.instantiateLevelParams ci.levelParams us).beta xs
    guard <| [`propext, `Eq.propIntro, `eq_true, `eq_false, `eq_false', `Eq.symm, `Eq.trans].any rhs.isAppOf
    transport? source back p q rhs input fuel

/-- Specialize fully applied casts in the official proof term before translating
its constants. Every resulting term still goes through the destination kernel. -/
public def constructiveCasts (source : Environment) (body : Expr) (rules : NameMap ConstantInfo := {})
    (useEquivalences := false) : Expr := Id.run do
  let mapProof := fun back p q h x => do
    if useEquivalences then
      if let some iff := logicalEquivalence? source p q h rules then
        return mkApp4 (mkConst (if back then `Iff.mpr else `Iff.mp)) p q iff x
    transport? source back p q h x 32
  let equiv := fun (a b h : Expr) => do
    if useEquivalences then
      if let some iff := logicalEquivalence? source a b h rules then return iff
    let direction := fun rev dom => do
      let lift := fun (e : Expr) => e.liftLooseBVars 0 1
      let proof ← mapProof rev (lift a) (lift b) (lift h) (mkBVar 0)
      return Expr.lam `hp dom proof .default
    return mkApp4 (mkConst `Iff.intro) a b (← direction false a) (← direction true b)
  let rewrite := fun (e : Expr) => do
    let .const n us := e.getAppFn | none
    match n, us, e.getAppArgs with
    | `congrArg, _, #[_, _, _, _, op, eq] => predicateCongruence? op eq
    | `Decidable.decide.congr_simp, _, #[p, q, eq, dp, dq] =>
      let rule ← rules.find? `decideCongr
      return (← rule.value? (allowOpaque := true)).beta #[p, q, dp, dq, ← equiv p q eq]
    | `ite_congr, _, #[α, b, c, x, y, s, t, db, dc, h, yes, no]
    | `dite_congr, _, #[b, c, α, db, dc, x, s, y, t, h, yes, no] =>
      let eqv ← equiv b c h
      let (name, args) := if n == `ite_congr then
        (`iteCongr, #[α, b, c, x, y, s, t, db, dc, eqv, yes, no])
      else (`diteCongr, #[b, c, α, db, dc, x, s, y, t, eqv, yes, no])
      let rule ← rules.find? name
      return ((← rule.value? (allowOpaque := true)).instantiateLevelParams rule.levelParams us).beta args
    | `ite_cond_congr, _, #[α, b, c, db, dc, x, y, h] =>
      let rule ← rules.find? `iteCongr
      let sameBranch := fun (dom v : Expr) => Expr.lam `h dom
        ((mkApp2 (mkConst `Eq.refl us) α v).liftLooseBVars 0 1) .default
      let args := #[α, b, c, x, y, x, y, db, dc, ← equiv b c h,
        sameBranch c x, sameBranch (mkApp (mkConst `Not) c) y]
      return ((← rule.value? (allowOpaque := true)).instantiateLevelParams rule.levelParams us).beta args
    | `Eq.substr, _, #[.sort .zero, motive, a, b, h, x] =>
      let fromType := motive.beta #[a]
      let toType := motive.beta #[b]
      if fromType == a && toType == b then mapProof true b a h x
      else
        let lifted ← congrIff? b a (← equiv b a h) toType fromType
        return mkApp4 (mkConst `Iff.mpr) toType fromType lifted x
    | `Eq.mpr_prop, _, #[p, q, h, x] => mapProof true p q h x
    | `Eq.mpr_not, _, #[p, q, h, x] =>
      let lift := fun (e : Expr) => e.liftLooseBVars 0 1
      let term ← mapProof false (lift p) (lift q) (lift h) (mkBVar 0)
      return Expr.lam `hp p ((lift x).beta #[term]) .default
    | `ite_eq_left_of_eq_true, _, #[α, p, dec, t, f, h]
    | `dite_eq_left_of_eq_true, _, #[α, p, dec, t, f, h] =>
      let hp ← mapProof true p (mkConst `True) h (mkConst `True.intro)
      let lemma := if n == `ite_eq_left_of_eq_true then `if_pos else `dif_pos
      return mkApp6 (mkConst lemma us) p dec hp α t f
    | `ite_eq_right_of_eq_false, _, #[α, p, dec, t, f, h]
    | `dite_eq_right_of_eq_false, _, #[α, p, dec, t, f, h] =>
      let proof ← mapProof false (p.liftLooseBVars 0 1) (mkConst `False)
        (h.liftLooseBVars 0 1) (mkBVar 0)
      let lemma := if n == `ite_eq_right_of_eq_false then `if_neg else `dif_neg
      return mkApp6 (mkConst lemma us) p dec (.lam `hp p proof .default) α t f
    | `congrFun, _, #[_, _, _, _, h, a] | `congrFun', _, #[_, _, _, _, h, a] =>
      if let some term := mapCongruence? h a then return term
      let pointwise ← if h.isAppOfArity `funext 5 then pure h else do
        let .const name levels := h.getAppFn | none
        let ci ← source.find? name
        let proof ← ci.value? (allowOpaque := true)
        let unfolded := (proof.instantiateLevelParams ci.levelParams levels).beta h.getAppArgs
        guard (unfolded.isAppOfArity `funext 5)
        pure unfolded
      return pointwise.getAppArgs[4]!.beta #[a]
    | `Eq.mp, [.zero], #[p, q, h, x] | `Eq.mpr, [.zero], #[p, q, h, x]
    | `cast, [.zero], #[p, q, h, x] =>
      mapProof (n == `Eq.mpr) p q h x
    | `of_eq_true, _, #[p, h] =>
      mapProof true p (mkConst `True) h (mkConst `True.intro)
    | `Iff.of_eq, _, #[p, q, h] => equiv p q h
    | `Eq.ndrec, .zero :: _, #[.sort .zero, p, motive, x, q, h]
    | `Eq.rec, .zero :: _, #[.sort .zero, p, motive, x, q, h] =>
      let left := if n == `Eq.rec then motive.beta #[p, mkApp2 (mkConst `Eq.refl [.succ .zero]) (.sort .zero) p]
        else motive.beta #[p]
      let right := if n == `Eq.rec then motive.beta #[q, h] else motive.beta #[q]
      if left == p && right == q then mapProof false p q h x
      else
        let lifted ← congrIff? p q (← equiv p q h) left right
        return mkApp4 (mkConst `Iff.mp) left right lifted x
    | `of_eq_false, _, #[p, h] =>
      let hp := mkBVar 0
      let proof ← mapProof false (p.liftLooseBVars 0 1) (mkConst `False)
        (h.liftLooseBVars 0 1) hp
      return Expr.lam `hp p proof .default
    | _, _, _ => none
  let mut term := body
  for _ in [:8] do
    let next := term.replace rewrite
    if next == term then break
    term := next
  return term

/-- Select a field of an official conjunction or equivalence before translating
its proof. This avoids requiring an unused direction at a constructive use site. -/
public def specializeProjections (source : Environment) (body : Expr) (unavailable : Name → Bool) : Expr := Id.run do
  let reduce := fun (e : Expr) => do
    let (kind, index, proof, args) ← match e.getAppFn with
      | .proj kind i proof => some (kind, i, proof, e.getAppArgs)
      | .const n _ => do
        let args := e.getAppArgs
        let proof ← args[2]?
        let (kind, i) ← match n with
          | `Iff.mp => some (`Iff, 0)
          | `Iff.mpr => some (`Iff, 1)
          | `And.left => some (`And, 0)
          | `And.right => some (`And, 1)
          | _ => none
        pure (kind, i, proof, args.extract 3 args.size)
      | _ => none
    guard ((kind == `Iff || kind == `And) && index < 2)
    let ctor := kind ++ `intro
    let mut term := proof.consumeMData
    guard (term.isAppOf ctor || term.getAppFn.constName?.any unavailable)
    for _ in [:8] do
      if term.isAppOfArity ctor 4 then return term.getAppArgs[index + 2]!.beta args
      if let .letE _ _ val next _ := term then
        term := (next.instantiate1 val).consumeMData
      else
        let .const name levels := term.getAppFn | none
        let ci ← source.find? name
        let val ← ci.value? (allowOpaque := true)
        term := ((val.instantiateLevelParams ci.levelParams levels).beta term.getAppArgs).consumeMData
    none
  let mut term := body
  for _ in [:4] do
    let next := term.replace reduce
    if next.equal term then break
    term := next
  return term

/-- The strict foundation encodes logical types with eliminators. For an existential
whose witness is a proof, both projections can eliminate into Prop. -/
public def namedLogicalProjections (source : Environment) (body : Expr) : IO Expr := do
  let logical := fun e => match e with
    | Expr.proj name _ _ => name == `And || name == `Iff || name == `Exists
    | _ => false
  unless (body.find? logical).isSome do return body
  let action := Meta.transform body (post := fun e => do
    unless logical e do return .done e
    let .proj owner idx target := e | return .done e
    let ty ← Meta.whnf (← Meta.inferType target)
    unless ty.isAppOfArity owner 2 && idx < 2 do return .done e
    if owner == `Exists then
      let #[α, pred] := ty.getAppArgs | return .done e
      unless ← Meta.isProp α do return .done e
      let levels := ty.getAppFn.constLevels!
      let chooseProof ← Meta.withLocalDeclD `h α fun h =>
        Meta.withLocalDeclD `hp (pred.beta #[h]) fun hp => Meta.mkLambdaFVars #[h, hp] h
      let witness := mkApp5 (mkConst `Exists.elim levels) α pred α target chooseProof
      if idx == 0 then return .done witness
      let branch ← Meta.withLocalDeclD `h α fun h =>
        Meta.withLocalDeclD `hp (pred.beta #[h]) fun hp => Meta.mkLambdaFVars #[h, hp] hp
      return .done (mkApp5 (mkConst `Exists.elim levels) α pred (pred.beta #[witness]) target branch)
    let field := if owner == `And then (if idx == 0 then `And.left else `And.right)
      else (if idx == 0 then `Iff.mp else `Iff.mpr)
    return .done (mkAppN (mkConst field) (ty.getAppArgs.push target)))
  try
    return ← action.run' |>.toIO' {fileName := "<logical projection>", fileMap := default} {env := source}
  catch _ => return body

private def nonemptyChoices := [`Classical.choice, `Classical.ofNonempty, `Classical.inhabited_of_nonempty]

private def choiceWitness? (e : Expr) : Bool :=
  (nonemptyChoices.any fun n => e.isAppOfArity n 2) ||
    ([`Classical.choose, `Classical.choose_spec, `Exists.choose, `Exists.choose_spec,
      `Classical.indefiniteDescription].any fun n => e.isAppOfArity n 3)

/-- Eliminate each selected witness in the proof of the same proposition. Each
recursive call replaces the selected occurrences with fresh local variables. -/
private partial def eliminateChoice (e : Expr) : MetaM Expr := do
  unless e.isApp do return e
  let some chosen := e.find? (fun expr => !expr.hasLooseBVars && choiceWitness? expr) | return e
  let conclusion ← Meta.inferType e
  unless ← Meta.isProp conclusion do return e
  let .const name us := chosen.getAppFn | return e
  let args := chosen.getAppArgs
  let α := args[0]!
  if nonemptyChoices.contains name then
    if chosen.occurs conclusion then return e
    let branch ← Meta.withLocalDeclD `w α fun x => do
      let value := if name == `Classical.inhabited_of_nonempty then mkApp2 (mkConst `Inhabited.mk us) α x else x
      let body := e.replace fun sub => if sub == chosen then some value else none
      Meta.mkLambdaFVars #[x] (← eliminateChoice body)
    return mkApp4 (mkConst `Nonempty.elim us) α conclusion args[1]! branch
  let p := args[1]!
  let witnesses := [`Classical.choose, `Exists.choose].map fun n => mkAppN (mkConst n us) args
  let specs := [`Classical.choose_spec, `Exists.choose_spec].map fun n => mkAppN (mkConst n us) args
  let desc := mkAppN (mkConst `Classical.indefiniteDescription us) args
  if (desc :: witnesses ++ specs).any (·.occurs conclusion) then return e
  let branch ← Meta.withLocalDeclD `w α fun x =>
    Meta.withLocalDeclD `hw (p.beta #[x]) fun hx => do
      let term := e.replace fun sub =>
        if witnesses.contains sub then some x
        else if specs.contains sub then some hx
        else if sub == desc then some (mkApp4 (mkConst `Subtype.mk us) α p x hx)
        else none
      Meta.mkLambdaFVars #[x, hx] (← eliminateChoice term)
  return mkApp5 (mkConst `Exists.elim us) α p conclusion args[2]! branch

/-- Some classical theorems are direct applications of a decidable theorem. Expose
the instance argument at the use site, where its concrete proposition is known. -/
private def exposeDecidableTheorems (source : Environment) (body : Expr) : Expr := Id.run do
  let mut wrappers : NameMap ConstantInfo := {}
  for name in body.getUsedConstants do
    unless name.getRoot == `Classical do continue
    let some (.thmInfo ci) := source.find? name | continue
    let mut rhs := ci.value
    while rhs.isLambda do rhs := rhs.bindingBody!
    unless rhs.getAppFn.constName?.any (·.getRoot == `Decidable) do continue
    wrappers := wrappers.insert name (.thmInfo ci)
  if wrappers.isEmpty then return body
  return body.replace fun e => do
    let .const name levels := e.getAppFn | none
    let ci ← wrappers.find? name
    return ((← ci.value? (allowOpaque := true)).instantiateLevelParams ci.levelParams levels).beta e.getAppArgs

/-- Recover decidable case splits and eliminate a chosen witness directly into a
proposition when the conclusion is independent of that witness. -/
public def decidableProof (source : Environment) (body : Expr) (rules : NameMap ConstantInfo := {}) : IO Expr := do
  let body := exposeDecidableTheorems source body
  let classical := [`Classical.em, `Classical.byCases, `Classical.byContradiction, `Classical.propDecidable]
  let deps := body.getUsedConstants
  let orderRules := [`Std.not_lt, `Std.not_lt_iff_not_le_or_ge]
  let usesChoice := deps.any nonemptyChoices.contains || deps.any [`Classical.choose, `Classical.choose_spec,
    `Exists.choose, `Exists.choose_spec, `Classical.indefiniteDescription].contains
  unless usesChoice || deps.any classical.contains || deps.any orderRules.contains do return body
  let action : MetaM Expr := Meta.transform body (post := fun e => do
    if usesChoice then
      let without ← eliminateChoice e
      if without != e then return .done without
    let .const name us := e.getAppFn | return .done e
    let args := e.getAppArgs
    if orderRules.contains name then
      let count := if name == `Std.not_lt then 7 else 6
      unless args.size == count do return .done e
      let some rule := rules.find? (if name == `Std.not_lt then `notLtDecidable else `notLtOrDecidable)
        | return .done e
      let reverse := mkApp4 (mkConst `LE.le us) args[0]! args[2]! args[count-1]! args[count-2]!
      let some dec ← Meta.synthInstance? (mkApp (mkConst `Decidable) reverse) | return .done e
      let value := (rule.value! (allowOpaque := true)).instantiateLevelParams rule.levelParams us
      return .done (value.beta (args.push dec))
    unless classical.contains name do return .done e
    let some p := args[0]? | return .done e
    let some dec ← Meta.synthInstance? (mkApp (mkConst `Decidable) p) | return .done e
    let mapArgs (term : Expr) (consumed : Nat) := mkAppN term (args.extract consumed args.size)
    match name with
    | `Classical.propDecidable => return .done (mapArgs dec 1)
    | `Classical.em => return .done (mapArgs (mkApp2 (mkConst `Decidable.em) p dec) 1)
    | `Classical.byContradiction => return .done (mapArgs (mkApp2 (mkConst `Decidable.byContradiction) p dec) 1)
    | _ =>
      let some q := args[1]? | return .done e
      return .done (mapArgs (mkApp3 (mkConst `Decidable.byCases [.zero]) p q dec) 2))
  try
    let result ← action.run' |>.toIO' {fileName := "<constructive decision>", fileMap := default}
      {env := source}
    if result.hasFVar || result.hasMVar || result.hasLooseBVars then return body
    return result
  catch _ =>
    return body

/-- Candidate terms for assumptions and reflexive propositions in a telescope. -/
public partial def elementaryCandidates (type : Expr) : List Expr :=
  let rec terms (goal : Expr) (depth : Nat) : List Expr := Id.run do
    let mut candidates := (List.range depth).map mkBVar
    if let .const n us := goal.getAppFn then
      let xs := goal.getAppArgs
      if (n == `Eq && xs.size == 3) || (n == `HEq && xs.size == 4) then
        candidates := mkApp2 (mkConst (n ++ `refl) us) xs[0]! xs[1]! :: candidates
      if n == `Omega.Iff && xs.size == 2 then
        candidates := mkApp (mkConst `Omega.Iff.rfl) xs[0]! :: candidates
      if n == `Omega.True then candidates := mkConst `Omega.True.intro :: candidates
    if let .forallE n dom body bi := goal then
      candidates := (terms body (depth + 1)).map (fun b => Expr.lam n dom b bi) ++ candidates
    return candidates
  terms type 0

/-- Return a candidate that the kernel checks against the full interface. -/
public def elementaryProof? (env : Environment) (type : Expr) : Option Expr :=
  (elementaryCandidates type).find? (fun e =>
    (Kernel.check env {} e).toOption.any (Kernel.isDefEqGuarded env {} type))

private def splitContainer (type : Expr) : Bool :=
  type.getAppFn.constName?.any [`Option, `Sum, `Prod, `List].contains

/-- Split finite enumeration arguments, or additionally split container arguments by their
constructors. Every branch uses the motive of the original theorem. -/
public partial def finiteProof? (source : Environment) (type : Expr) (splitContainers := false) : IO (Option Expr) := do
  let enums := [`Bool, `Ordering]
  let hasDecision := (type.find? fun e =>
    e.isForall && e.bindingDomain!.isAppOfArity `Decidable 1).isSome
  let conditional := hasDecision && (type.getUsedConstants.any [`ite, `dite, `Decidable.decide].contains)
  if splitContainers then
    unless (type.find? fun e => e.isForall && splitContainer e.bindingDomain!).isSome do return none
  else
    unless conditional || (type.find? fun e => e.isForall && e.bindingDomain!.constName?.any enums.contains).isSome do
      return none
  try
    let proof ← (go type 3 conditional splitContainers).run' |>.toIO'
      {fileName := "<finite proof>", fileMap := default, options := maxHeartbeats.set {} 2000}
      {env := source}
    return if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars then none else some proof
  catch _ => return none
where
  go (goal : Expr) (splits : Nat) (conditional splitContainers : Bool) : MetaM Expr := do
    if let .forallE n dom body bi := goal then
      return ← Meta.withLocalDecl n bi dom fun x => do
        if splits > 0 && (dom.isConstOf `Bool || dom.isConstOf `Ordering) then
          let ind ← getConstInfoInduct dom.constName!
          let branches ← ind.ctors.mapM fun ctor => go (body.instantiate1 (mkConst ctor)) (splits - 1) conditional splitContainers
          let motive := Expr.lam n dom body .default
          let term := mkAppN (mkConst (ind.name ++ `rec) [.zero]) (#[motive] ++ branches.toArray ++ #[x])
          return ← Meta.mkLambdaFVars #[x] term
        if splitContainers && splits > 0 && splitContainer dom then
          let .const name levels := dom.getAppFn | throwError "expected an inductive type"
          let ind ← getConstInfoInduct name
          let params := dom.getAppArgs
          let branches ← ind.ctors.mapM fun ctor => do
            let head := mkAppN (mkConst ctor levels) params
            Meta.forallTelescope (← Meta.inferType head) fun fields _ => do
              let term ← go (body.instantiate1 (mkAppN head fields)) (splits - 1) conditional splitContainers
              Meta.mkLambdaFVars fields term
          let motive := Expr.lam n dom body .default
          let cases := mkConst (name ++ `casesOn) (.zero :: levels)
          return ← Meta.mkLambdaFVars #[x] (mkAppN cases (params ++ #[motive, x] ++ branches.toArray))
        if conditional && splits > 0 && dom.isAppOfArity `Decidable 1 then
          let p := dom.appArg!
          let branch := fun (ctor : Name) witness =>
            Meta.withLocalDeclD `h witness fun h => do
              let result ← go (body.instantiate1 (mkApp2 (mkConst ctor) p h)) (splits - 1) conditional splitContainers
              Meta.mkLambdaFVars #[h] result
          let motive := Expr.lam n dom body .default
          let no ← branch `Decidable.isFalse (mkApp (mkConst `Not) p)
          let yes ← branch `Decidable.isTrue p
          return ← Meta.mkLambdaFVars #[x] (mkApp5 (mkConst `Decidable.falseTrueCases [.zero]) p motive no yes x)
        Meta.mkLambdaFVars #[x] (← go (body.instantiate1 x) splits conditional splitContainers)
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && (← Meta.isDefEq decl.type goal) then return decl.toExpr
    if let some (_, a, b) := goal.eq? then
      if ← Meta.isDefEq a b then return ← Meta.mkEqRefl a
    if splitContainers && !conditional then
      try return ← Meta.mkDecideProof goal catch _ => pure ()
    if let some (a, b) := goal.iff? then
      if ← Meta.isDefEq a b then return mkApp (mkConst `Iff.rfl) a
      if conditional || splitContainers then
        try
          let forward ← go (← mkArrow a b) splits conditional splitContainers
          let reverse ← go (← mkArrow b a) splits conditional splitContainers
          return mkApp4 (mkConst `Iff.intro) a b forward reverse
        catch _ => pure ()
    if conditional || splitContainers then
      try
        let hole ← Meta.mkFreshExprSyntheticOpaqueMVar goal
        let rules := [`Iff.intro, `True.intro, `Eq.refl, `False.elim]
        let remaining ← Meta.SolveByElim.solveByElim {maxDepth := 5, symm := false}
          (rules.map fun name => Meta.mkConstWithFreshMVarLevels name)
          (fun _ => return (← getLocalHyps).toList) [hole.mvarId!]
        if remaining.isEmpty then return ← instantiateMVars hole
      catch _ => pure ()
    Meta.mkDecideProof goal

end OmegaChecks.InitCompiler
