import LeanInformationAudit.Registry.Entries

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

private abbrev EraseM := StateT Nat MetaM

private partial def erase (e : Expr) (depth : Nat) : EraseM Expr := do
  Core.checkMaxHeartbeats "template proof erasure"
  if depth > 256 then throwError "incomplete_closure:E8.erasure_depth"
  let remaining ← get
  if remaining == 0 then throwError "incomplete_closure:E8.erasure_work"
  set (remaining - 1)
  -- Inference classifies the proposition; no visitor descends into a proof.
  if ← isProof e then return proofPlaceholder (← erase (← inferType e) (depth + 1))
  let child := fun e => erase e (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi | .forallE n t b bi =>
    let type ← child t
    let body ← fun state => withLocalDecl n bi t fun x => do
      let (body, state) ← (child (b.instantiate1 x)).run state
      return (body.abstract #[x], state)
    return if e.isLambda then .lam n type body bi else .forallE n type body bi
  | .letE n t v b nd =>
    let type ← child t
    let value ← child v
    let body ← fun state => withLetDecl n t v fun x => do
      let (body, state) ← (child (b.instantiate1 x)).run state
      return (body.abstract #[x], state)
    return .letE n type value body nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ => throwError "incomplete_closure:E7.metavariable"
  | .bvar _ => throwError "incomplete_closure:E7.open_expression"
  | _ => return e

/-- Preserve all data syntax and replace each proof by its proposition. Typing
uses the original binder domains; the result retains no proof implementation.
The caller charges this walk before any transformation or serialization. -/
def eraseProofs (e : Expr) (fuel : Nat := 524288) : MetaM (Expr × Nat) := do
  let limit := min fuel 524288
  let (result, remaining) ← (erase e 0).run limit
  return (result, limit - remaining)

end LeanInformationAudit.TemplateAudit
