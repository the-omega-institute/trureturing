module
public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic
public import Init.Internal.Order.Lemmas
import all Init.Internal.Order.Lemmas
meta import Lean

/-! Pointwise orders and monotone operations. -/

open _root_.Lean.Order

namespace OmegaChecks.InitPort.Alternatives.Lean.Order

private theorem productSupremum {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    {c : α ×' β → Prop} {a : α} {b : β}
    (ha : is_sup (fun i => ∃ j, c ⟨i, j⟩) a) (hb : is_sup (fun j => ∃ i, c ⟨i, j⟩) b) :
    is_sup c ⟨a, b⟩ := by
  intro ⟨x, y⟩
  constructor
  · intro ⟨hx, hy⟩ ⟨i, j⟩ hij
    exact ⟨(ha x).mp hx i ⟨j, hij⟩, (hb y).mp hy j ⟨i, hij⟩⟩
  · intro upper
    exact ⟨(ha x).mpr (fun i ⟨j, hij⟩ => (upper ⟨i, j⟩ hij).1),
      (hb y).mpr (fun j ⟨i, hij⟩ => (upper ⟨i, j⟩ hij).2)⟩

@[instance_reducible] public def instCCPOPProd {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] : CCPO (α ×' β) where
  has_csup hc := by
    obtain ⟨a, ha⟩ := CCPO.has_csup (PProd.chain.chain_fst hc)
    obtain ⟨b, hb⟩ := CCPO.has_csup (PProd.chain.chain_snd hc)
    exact ⟨⟨a, b⟩, productSupremum ha hb⟩

@[instance_reducible] public def instCompleteLatticePProd {α : Sort u} {β : Sort v}
    [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α ×' β) where
  has_sup c := by
    obtain ⟨a, ha⟩ := CompleteLattice.has_sup (_root_.Lean.Order.PProd.fst c)
    obtain ⟨b, hb⟩ := CompleteLattice.has_sup (_root_.Lean.Order.PProd.snd c)
    exact ⟨⟨a, b⟩, productSupremum ha hb⟩

@[instance_reducible] public def instCCPOProd {α : Type u} {β : Type v} [CCPO α] [CCPO β] : CCPO (α × β) where
  has_csup {c} hc := by
    have hc' : chain (fun p : α ×' β => c (p.1, p.2)) := fun _ _ ha hb => hc _ _ ha hb
    obtain ⟨p, hp⟩ := @CCPO.has_csup _ instCCPOPProd _ hc'
    exact ⟨(p.1, p.2), Prod.is_sup_of_pprod hp⟩

@[instance_reducible] public def instCompleteLatticeProd {α : Type u} {β : Type v}
    [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  has_sup c := by
    obtain ⟨p, hp⟩ := @CompleteLattice.has_sup _ instCompleteLatticePProd
      (fun p : α ×' β => c (p.1, p.2))
    exact ⟨(p.1, p.2), Prod.is_sup_of_pprod hp⟩

public theorem monotone_bind (m : Type u → Type v) [Bind m] [∀ α, PartialOrder (m α)] [MonoBind m]
    {α β : Type u} {γ : Sort w} [PartialOrder γ]
    (f : γ → m α) (g : γ → α → m β) (hf : monotone f)
    (hg : ∀ x y : γ, x ⊑ y → ∀ a, g x a ⊑ g y a) :
    monotone fun x => f x >>= g x :=
  fun x y h => PartialOrder.rel_trans (MonoBind.bind_mono_left (hf x y h))
    (MonoBind.bind_mono_right (hg x y h))

public theorem monotone_dite {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β]
    (c : Prop) [d : Decidable c] (f : α → c → β) (g : α → ¬ c → β)
    (hf : ∀ x y : α, x ⊑ y → ∀ h, f x h ⊑ f y h)
    (hg : ∀ x y : α, x ⊑ y → ∀ h, g x h ⊑ g y h) :
    monotone fun x => dite c (f x) (g x) := by
  intro x y xy
  cases d with
  | isTrue h => exact hf x y xy h
  | isFalse h => exact hg x y xy h

public theorem Functor.monotone_map {m : Type u → Type v} [Monad m] [∀ t, PartialOrder (m t)] [MonoBind m]
    {α β : Type u} {γ : Type w} [PartialOrder γ] [LawfulMonad m]
    (f : γ → m α) (g : α → β) (hf : monotone f) : monotone fun x => g <$> f x := by
  intro x y xy
  change (g <$> f x) ⊑ (g <$> f y)
  rw [← bind_pure_comp g (f x), ← bind_pure_comp g (f y)]
  exact MonoBind.bind_mono_left (hf x y xy)

end OmegaChecks.InitPort.Alternatives.Lean.Order

open Lean Meta in
/-- Reduce relation projections before a function or implication order can bring its
extensionality proof into a term. Applied monotonicity lemmas introduce the same
projections when their codomain is itself a function. -/
private meta def expandPointwise (e : Expr) : MetaM Expr :=
  transform e (pre := fun node => do
    let .const name levels := node.getAppFn | return .continue
    let projection := [``Order.PartialOrder.rel, ``Order.PartialOrder.rel_refl,
      ``Order.PartialOrder.rel_trans, ``Order.monotone, ``Order.is_meet, ``Order.chain].contains name
    let pointwiseLemma := [``Order.monotone_apply, ``Order.monotone_of_monotone_apply,
      ``Order.monotone_const, ``Order.monotone_id].contains name
    unless projection || pointwiseLemma do return .continue
    let args := node.getAppArgs
    let affected (arg : Expr) := (arg.find? fun t => t.isConstOf ``Order.instOrderPi ||
      t.isConstOf ``Order.ImplicationOrder.instOrder ||
      t.isConstOf ``Order.ReverseImplicationOrder.instOrder).isSome
    unless args.any affected do return .continue
    if projection then
      let result ← withTransparency .all (whnf node)
      if result != node then return .visit result
    let ci ← getConstInfo name
    let expanded := (ci.instantiateValueLevelParams! levels (allowOpaque := true)).beta args
    return .visit (← withTransparency .all (whnf expanded)))

open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let orderLemmas := env.header.moduleData[(env.getModuleIdx? `Init.Internal.Order.Lemmas).get!.toNat]!
  let basicLemmas := #[``Order.monotone_apply, ``Order.monotone_of_monotone_apply,
    ``Order.chain_apply, ``Order.is_meet_pi, ``Order.ImplicationOrder.is_meet_and,
    ``Order.ReverseImplicationOrder.is_meet_or, ``Order.implication_order_monotone_and,
    ``Order.implication_order_monotone_or, ``Order.implication_order_monotone_exists,
    ``Order.implication_order_monotone_forall, ``Order.coind_monotone_and,
    ``Order.coind_monotone_or, ``Order.coind_monotone_exists, ``Order.coind_monotone_forall,
    ``Order.ind_not, ``Order.coind_not, ``Order.ind_impl, ``Order.coind_impl]
  for name in basicLemmas ++ orderLemmas.constants.map (·.name) do
    let some (.thmInfo ci) := env.find? name | continue
    let destination := `OmegaChecks.InitPort.Alternatives ++ name
    unless (`Lean.Order).isPrefixOf name && !env.contains destination do continue
    let type ← expandPointwise ci.type
    let value ← expandPointwise ci.value
    unless type == ci.type && value == ci.value do
      addDecl (.thmDecl {ci with name := destination, type, value})
