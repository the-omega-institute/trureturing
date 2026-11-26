module

public import Lean

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

/-- Kernel numeral literals denote the official Nat; strict numerals use the Omega constructors. -/
private partial def natTerm (n : Nat) : Expr :=
  if n < 32 then
    n.fold (init := mkConst `Omega.Nat.zero) (fun _ _ x => mkApp (mkConst `Omega.Nat.succ) x)
  else
    let x := mkBVar 0
    let twice := mkApp2 (mkConst `Omega.Nat.add) x x
    .letE `half (mkConst `Omega.Nat) (natTerm (n / 2))
      (if n % 2 == 0 then twice else mkApp (mkConst `Omega.Nat.succ) twice) false

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
        else some (.const (`Omega ++ n) us)
      | .proj n i x => some (.proj (`Omega ++ n) i (go x))
      | .lit (.natVal n) => some (natTerm n)
      | _ => none
  return go term

public def translateProofTerm (env : Environment) (term : Expr) : Except String Expr :=
  (translateTerm env {} term).run' {}

private def castProof (back : Bool) (p q eq input : Expr) : Expr :=
  mkApp4 (mkConst (if back then `Eq.mpr else `Eq.mp) [.zero]) p q eq input

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
private def transport? (source : Environment) (back : Bool) (p q eq input : Expr)
    (fuel : Nat) : Option Expr := do
  let fuel + 1 := fuel | none
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
    let through := fun p q h input => (transport? source back p q h input fuel).getD
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
        let map ← transport? source rev (lift a) (lift b) (lift h) (mkBVar 0) fuel
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
      let term ← transport? source rev (under a) (under b) (under h) (mkBVar 0) fuel
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
public def constructiveCasts (source : Environment) (body : Expr) : Expr := Id.run do
  let equiv := fun (a b h : Expr) => do
    let direction := fun rev dom => do
      let lift := fun (e : Expr) => e.liftLooseBVars 0 1
      let proof ← transport? source rev (lift a) (lift b) (lift h) (mkBVar 0) 32
      return Expr.lam `hp dom proof .default
    return mkApp4 (mkConst `Iff.intro) a b (← direction false a) (← direction true b)
  let rewrite := fun (e : Expr) => do
    let .const n us := e.getAppFn | none
    match n, us, e.getAppArgs with
    | `ite_eq_left_of_eq_true, _, #[α, p, dec, t, f, h]
    | `dite_eq_left_of_eq_true, _, #[α, p, dec, t, f, h] =>
      let hp ← transport? source true p (mkConst `True) h (mkConst `True.intro) 32
      let lemma := if n == `ite_eq_left_of_eq_true then `if_pos else `dif_pos
      return mkApp6 (mkConst lemma us) p dec hp α t f
    | `ite_eq_right_of_eq_false, _, #[α, p, dec, t, f, h]
    | `dite_eq_right_of_eq_false, _, #[α, p, dec, t, f, h] =>
      let proof ← transport? source false (p.liftLooseBVars 0 1) (mkConst `False)
        (h.liftLooseBVars 0 1) (mkBVar 0) 32
      let lemma := if n == `ite_eq_right_of_eq_false then `if_neg else `dif_neg
      return mkApp6 (mkConst lemma us) p dec (.lam `hp p proof .default) α t f
    | `congrFun, _, #[_, _, _, _, h, a] | `congrFun', _, #[_, _, _, _, h, a] =>
      guard (h.isAppOfArity `funext 5)
      return h.getAppArgs[4]!.beta #[a]
    | `Eq.mp, [.zero], #[p, q, h, x] | `Eq.mpr, [.zero], #[p, q, h, x]
    | `cast, [.zero], #[p, q, h, x] =>
      transport? source (n == `Eq.mpr) p q h x 32
    | `of_eq_true, _, #[p, h] =>
      transport? source true p (mkConst `True) h (mkConst `True.intro) 32
    | `Iff.of_eq, _, #[p, q, h] => equiv p q h
    | `Eq.ndrec, .zero :: _, #[.sort .zero, p, motive, x, q, h]
    | `Eq.rec, .zero :: _, #[.sort .zero, p, motive, x, q, h] =>
      let left := if n == `Eq.rec then motive.beta #[p, mkApp2 (mkConst `Eq.refl [.succ .zero]) (.sort .zero) p]
        else motive.beta #[p]
      let right := if n == `Eq.rec then motive.beta #[q, h] else motive.beta #[q]
      if left == p && right == q then transport? source false p q h x 32
      else
        let lifted ← congrIff? p q (← equiv p q h) left right
        return mkApp4 (mkConst `Iff.mp) left right lifted x
    | `of_eq_false, _, #[p, h] =>
      let hp := mkBVar 0
      let proof ← transport? source false (p.liftLooseBVars 0 1) (mkConst `False)
        (h.liftLooseBVars 0 1) hp 32
      return Expr.lam `hp p proof .default
    | _, _, _ => none
  let mut term := body
  for _ in [:8] do
    let next := term.replace rewrite
    if next == term then break
    term := next
  return term

private def eliminateChoice (e : Expr) : MetaM Expr := do
  unless e.isApp do return e
  let some chosen := e.find? (fun expr => !expr.hasLooseBVars &&
    (expr.isAppOfArity `Classical.choose 3 || expr.isAppOfArity `Classical.choose_spec 3 ||
     expr.isAppOfArity `Classical.choice 2 || expr.isAppOfArity `Classical.indefiniteDescription 3)) | return e
  let conclusion ← Meta.inferType e
  unless ← Meta.isProp conclusion do return e
  let .const name us := chosen.getAppFn | return e
  let args := chosen.getAppArgs
  let α := args[0]!
  if name == `Classical.choice then
    if chosen.occurs conclusion then return e
    let branch ← Meta.withLocalDeclD `w α fun x => Meta.mkLambdaFVars #[x] (e.replace fun sub =>
      if sub == chosen then some x else none)
    return mkApp4 (mkConst `Nonempty.elim us) α conclusion args[1]! branch
  let p := args[1]!
  let witness := mkAppN (mkConst `Classical.choose us) args
  let spec := mkAppN (mkConst `Classical.choose_spec us) args
  let desc := mkAppN (mkConst `Classical.indefiniteDescription us) args
  if [witness, spec, desc].any (·.occurs conclusion) then return e
  let branch ← Meta.withLocalDeclD `w α fun x =>
    Meta.withLocalDeclD `hw (p.beta #[x]) fun hx => do
      let term := e.replace fun sub =>
        if sub == witness then some x
        else if sub == spec then some hx
        else if sub == desc then some (mkApp4 (mkConst `Subtype.mk us) α p x hx)
        else none
      Meta.mkLambdaFVars #[x, hx] term
  return mkApp5 (mkConst `Exists.elim us) α p conclusion args[2]! branch

/-- Recover decidable case splits and eliminate a chosen witness directly into a
proposition when the conclusion is independent of that witness. -/
public def decidableProof (source : Environment) (body : Expr) : IO Expr := do
  let classical := [`Classical.em, `Classical.byCases, `Classical.byContradiction, `Classical.propDecidable]
  let deps := body.getUsedConstants
  let usesChoice := deps.any [`Classical.choose, `Classical.choose_spec, `Classical.choice,
    `Classical.indefiniteDescription].contains
  unless usesChoice || deps.any classical.contains do return body
  let action : MetaM Expr := Meta.transform body (post := fun e => do
    if usesChoice then
      let without ← eliminateChoice e
      if without != e then return .done without
    let .const name _ := e.getAppFn | return .done e
    unless classical.contains name do return .done e
    let args := e.getAppArgs
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
      if (n == `Omega.Eq && xs.size == 3) || (n == `Omega.HEq && xs.size == 4) then
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

/-- Split finite enumeration arguments before checking reflexivity, local hypotheses,
or a decision procedure. Every branch uses the motive of the original theorem. -/
public partial def finiteProof? (source : Environment) (type : Expr) : IO (Option Expr) := do
  let enums := [`Bool, `Ordering]
  unless (type.find? fun e => e.isForall && e.bindingDomain!.constName?.any enums.contains).isSome do
    return none
  try
    let proof ← (go type 3).run' |>.toIO'
      {fileName := "<finite proof>", fileMap := default, options := maxHeartbeats.set {} 2000}
      {env := source}
    return if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars then none else some proof
  catch _ => return none
where
  go (goal : Expr) (splits : Nat) : MetaM Expr := do
    if let .forallE n dom body bi := goal then
      return ← Meta.withLocalDecl n bi dom fun x => do
        if splits > 0 && (dom.isConstOf `Bool || dom.isConstOf `Ordering) then
          let ind ← getConstInfoInduct dom.constName!
          let branches ← ind.ctors.mapM fun ctor => go (body.instantiate1 (mkConst ctor)) (splits - 1)
          let motive := Expr.lam n dom body .default
          let term := mkAppN (mkConst (ind.name ++ `rec) [.zero]) (#[motive] ++ branches.toArray ++ #[x])
          return ← Meta.mkLambdaFVars #[x] term
        Meta.mkLambdaFVars #[x] (← go (body.instantiate1 x) splits)
    for decl in ← getLCtx do
      if !decl.isImplementationDetail && (← Meta.isDefEq decl.type goal) then return decl.toExpr
    if let some (_, a, b) := goal.eq? then
      if ← Meta.isDefEq a b then return ← Meta.mkEqRefl a
    if let some (a, b) := goal.iff? then
      if ← Meta.isDefEq a b then return mkApp (mkConst `Iff.rfl) a
    Meta.mkDecideProof goal

end OmegaChecks.InitCompiler
