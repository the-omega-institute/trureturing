module

public import Lean

namespace OmegaChecks.InitCompiler

open Lean

private def under (e : Expr) := e.liftLooseBVars 0 1

/-- Interpret a simplifier's equality of propositions as a single equivalence.
Both directions share the same subproofs, including under dependent binders. -/
public partial def logicalEquivalence? (env : Environment) (p q proof : Expr) (fuel := 64) : Option Expr := do
  let fuel + 1 := fuel | none
  let again := fun a b h => logicalEquivalence? env a b h fuel
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
  | `Eq.propIntro, #[a, b, f, g] => return mkApp4 (mkConst `Iff.intro) a b f g
  | `eq_true, #[a, h] => return mkApp2 (mkConst `iff_true_intro) a h
  | `eq_false, #[a, h] | `eq_false', #[a, h] => return mkApp2 (mkConst `iff_false_intro) a h
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
  | `forall_congr, #[dom, a, b, h] =>
    return mkApp4 (mkConst `forall_congr' us) dom a b (pointwise dom a b h)
  | `congrArg, #[_, _, a, b, .app (.const `Exists ls) dom, h] =>
    guard (h.isAppOfArity `funext 5)
    return mkApp4 (mkConst `exists_congr ls) dom a b (pointwise dom a b h.getAppArgs[4]!)
  | `congr, #[_, _, f, g, b, d, h, k] =>
    let .app op a := f | none
    let .app op' c := g | none
    guard (op == op')
    let rule ← match op.constName? with
      | some `And => some `and_congr
      | some `Or => some `or_congr
      | some `Iff => some `iff_congr
      | _ => none
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
