module
public import Init.Internal.Order.Basic
public import Lean

public section

namespace OmegaChecks.InitBoundaries.InternalOrder.ChainIteration

universe u
open Lean Lean.Order

variable {α : Sort u} [CCPO α]

/-- Closure under a step and under every point satisfying the supremum relation. -/
inductive Generated (f : α → α) : α → Prop
  | step {a} : Generated f a → Generated f (f a)
  | sup {c : α → Prop} {s : α} (hc : chain c) (members : ∀ a, c a → Generated f a)
      (least : is_sup c s) : Generated f s

theorem inductionOnGenerated {f : α → α} {P : α → Prop} (next : ∀ a, P a → P (f a))
    (complete : ∀ c s, chain c → (∀ a, c a → P a) → is_sup c s → P s)
    {x : α} (generated : Generated f x) : P x := by
  induction generated with
  | step h ih => exact next _ ih
  | sup hc members least ih => exact complete _ _ hc ih least

/-- The comparison uses the pinned selector only in the official predicate and its supremum law. -/
theorem officialIff (f : α → α) (a : α) : Generated f a ↔ iterates f a := by
  constructor
  · apply inductionOnGenerated (P := iterates f) (fun _ => iterates.step)
    intro c s hc members hs
    exact is_sup_unique (CCPO.csup_spec hc) hs ▸ iterates.sup hc members
  · intro h
    induction h with
    | step h ih => exact Generated.step ih
    | sup hc members ih => exact Generated.sup hc ih (CCPO.csup_spec hc)

open Meta in
/-- The result index of the pinned supremum constructor contains the full chain selector.
Its empty-chain specialization on inhabited subsingletons yields a value of each such carrier. -/
private def checkSupremumIndex : MetaM Unit := do
  let constructor ← getConstInfo ``iterates.sup
  let select ← getConstInfo ``CCPO.csup
  let levels := constructor.levelParams.map Level.param
  forallTelescope constructor.type fun xs result => do
    let #[α, inst, f, c, hc, _] := xs | throwError "unexpected iteration constructor telescope"
    let selector := mkConst select.name levels
    let index := mkAppN selector #[α, inst, c, hc]
    unless result.equal (mkAppN (mkConst ``iterates levels) #[α, inst, f, index]) do
      throwError "unexpected iteration supremum index"
    let operation ← mkLambdaFVars #[α, inst, c, hc] index
    let env ← getEnv
    let signature ← Lean.ofExceptKernelException (Kernel.check env {} operation)
    unless Kernel.isDefEqGuarded env {} operation selector &&
        Kernel.isDefEqGuarded env {} signature (select.type.instantiateLevelParams select.levelParams levels) do
      throwError "iteration supremum index does not recover the full chain selector"

run_meta checkSupremumIndex

end OmegaChecks.InitBoundaries.InternalOrder.ChainIteration
