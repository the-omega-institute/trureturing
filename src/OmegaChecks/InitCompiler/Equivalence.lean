module

public import Lean

namespace OmegaChecks.InitCompiler

open Lean

private def under (e : Expr) := e.liftLooseBVars 0 1

private def binaryCongruence? (op : Expr) : Option Name :=
  match op.constName? with
  | some `And => some `and_congr
  | some `Or => some `or_congr
  | some `Iff => some `iff_congr
  | _ => none

/-- Interpret a simplifier's equality of propositions as a single equivalence.
Both directions share the same subproofs, including under dependent binders. -/
public partial def logicalEquivalence? (env : Environment) (p q proof : Expr) (rules : NameMap ConstantInfo) (fuel := 64) : Option Expr := do
  let fuel + 1 := fuel | none
  let again := fun a b h => logicalEquivalence? env a b h rules fuel
  let liftEq := fun a b h =>
    (again a b h).getD (mkApp3 (mkConst `Iff.of_eq) a b h)
  let pointwise := fun dom a b h =>
    Expr.lam `x dom (liftEq ((under a).beta #[mkBVar 0]) ((under b).beta #[mkBVar 0])
      ((under h).beta #[mkBVar 0])) .default
  if p == q then return mkApp (mkConst `Iff.rfl) p
  let .const n us := proof.consumeMData.getAppFn | none
  let args := proof.consumeMData.getAppArgs
  match n, args with
  | `id, #[_, h] => again p q h
  | `propext, #[_, _, h] => return h
  | `Bool.and_eq_true, #[a, b] => return mkApp2 (mkConst `Bool.and_eq_true_iff) a b
  | `Nat.beq_eq, #[a, b] | `Int.beq'_eq, #[a, b] | `Int.beq'_ne, #[a, b]
  | `Int.blt'_eq_true, #[a, b] | `Int.ble'_eq_true, #[a, b]
  | `Int.Internal.Linear.Poly.beq'_eq, #[a, b] | `Lean.Grind.CommRing.Power.beq'_eq, #[a, b]
  | `Lean.Grind.CommRing.Mon.beq'_eq, #[a, b] | `Lean.Grind.CommRing.Poly.beq'_eq, #[a, b] =>
    let name := match n with
      | `Nat.beq_eq => `natBEq
      | `Int.beq'_eq => `intBEq
      | `Int.beq'_ne => `intBNe
      | `Int.blt'_eq_true => `intBLt
      | `Int.ble'_eq_true => `intBLe
      | `Int.Internal.Linear.Poly.beq'_eq => `polyBEq
      | `Lean.Grind.CommRing.Power.beq'_eq => `ringPowerBEq
      | `Lean.Grind.CommRing.Mon.beq'_eq => `ringMonBEq
      | _ => `ringPolyBEq
    let rule ← rules.find? name
    return (← rule.value? (allowOpaque := true)).beta #[a, b]
  | `Eq.propIntro, #[a, b, f, g] => return mkApp4 (mkConst `Iff.intro) a b f g
  | `eq_true, #[a, h] => return mkApp2 (mkConst `iff_true_intro) a h
  | `eq_false, #[a, h] | `eq_false', #[a, h] => return mkApp2 (mkConst `iff_false_intro) a h
  | `Bool.false_eq_true, #[] =>
    return mkApp2 (mkConst `iff_false_intro) p (mkConst `Bool.false_ne_true)
  | `Bool.true_eq_false, #[] =>
    let ne := mkApp4 (mkConst `Ne.symm [.succ .zero]) (mkConst `Bool) (mkConst `Bool.false)
      (mkConst `Bool.true) (mkConst `Bool.false_ne_true)
    return mkApp2 (mkConst `iff_false_intro) p ne
  | `Bool.not_eq_true, #[b] =>
    return mkApp3 (mkConst `Iff.symm) q p (mkApp (mkConst `Bool.eq_false_iff) b)
  | `Eq.symm, #[_, a, b, h] => return mkApp3 (mkConst `Iff.symm) a b (← again a b h)
  | `Eq.trans, #[_, a, b, c, h, k] =>
    return mkApp5 (mkConst `Iff.trans) a b c (liftEq a b h) (liftEq b c k)
  | `implies_congr, #[a, c, b, d, h, k] =>
    return mkApp6 (mkConst `imp_congr) a b c d (liftEq a c h) (liftEq b d k)
  | `implies_congr_left, #[a, c, b, h] =>
    return mkApp6 (mkConst `imp_congr) a b c b (liftEq a c h) (mkApp (mkConst `Iff.rfl) b)
  | `implies_congr_right, #[a, b, d, k] =>
    return mkApp6 (mkConst `imp_congr) a b a d (mkApp (mkConst `Iff.rfl) a) (liftEq b d k)
  | `implies_congr_ctx, #[a, c, b, d, h, k] =>
    let branch := Expr.lam `hc c (liftEq (under b) (under d) ((under k).beta #[mkBVar 0])) .default
    return mkApp6 (mkConst `imp_congr_ctx) a b c d (liftEq a c h) branch
  | `forall_prop_domain_congr, #[a, c, b, d, h, k] =>
    let ac := liftEq a c h
    let hc := mkBVar 0
    let ha := mkApp4 (mkConst `Iff.mpr) (under a) (under c) (under ac) hc
    let pred := (under b).beta #[ha]
    let step := Expr.lam `hc c (liftEq pred ((under d).beta #[hc]) ((under k).beta #[hc])) .default
    let rule ← rules.find? `forallDomain
    return (← rule.value? (allowOpaque := true)).beta #[a, c, b, d, ac, step]
  | `forall_congr, #[dom, a, b, h] =>
    return mkApp4 (mkConst `forall_congr' us) dom a b (pointwise dom a b h)
  | `congrArg, #[_, _, a, b, .app (.const `Exists ls) dom, h] =>
    guard (h.isAppOfArity `funext 5)
    return mkApp4 (mkConst `exists_congr ls) dom a b (pointwise dom a b h.getAppArgs[4]!)
  | `congrArg, #[.sort .zero, _, a, b, f, h] =>
    if f.isConstOf `Not then return mkApp3 (mkConst `not_congr) a b (liftEq a b h)
    let .app op x := f | none
    return mkApp6 (mkConst (← binaryCongruence? op)) x x a b (mkApp (mkConst `Iff.rfl) x) (liftEq a b h)
  | `congrFun, #[_, _, _, _, h, x] | `congrFun', #[_, _, _, _, h, x] =>
    guard (h.isAppOfArity `congrArg 6)
    let #[.sort .zero, _, a, b, op, eq] := h.getAppArgs | none
    return mkApp6 (mkConst (← binaryCongruence? op)) a b x x (liftEq a b eq) (mkApp (mkConst `Iff.rfl) x)
  | `congr, #[_, _, f, g, b, d, h, k] =>
    let .app op a := f | none
    let .app op' c := g | none
    guard (op == op')
    let rule ← binaryCongruence? op
    let ac ← if a == c then pure (mkApp (mkConst `Iff.rfl) a) else do
      guard (h.isAppOfArity `congrArg 6)
      let xs := h.getAppArgs
      guard (xs[2]! == a && xs[3]! == c && xs[4]! == op)
      pure (liftEq a c xs[5]!)
    return mkApp6 (mkConst rule) a c b d ac (liftEq b d k)
  | _, _ =>
    let ci ← env.find? n
    let rhs := ((← ci.value? (allowOpaque := true)).instantiateLevelParams ci.levelParams us).beta args
    guard ([`propext, `Eq.propIntro, `eq_true, `eq_false, `eq_false'].any rhs.isAppOf)
    again p q rhs

end OmegaChecks.InitCompiler
