module
public import OmegaChecks.InitPort.Alternatives.BoolSearch
public import Init.Internal.Order.Basic
import all Init.Internal.Order.Basic
public import Init.Internal.Order.Lemmas
import all Init.Internal.Order.Lemmas
import all Init.Internal.Order.MonadTail
import all Init.Data.Array.Basic
public import OmegaChecks.InitPort.Alternatives.ArrayFind
import all OmegaChecks.InitPort.Alternatives.ArrayFind
public meta import Lean.Elab.Term.TermElabM
meta import Lean

/-! Pointwise orders and monotone operations. -/

open _root_.Lean.Order

namespace OmegaChecks.InitPort.Alternatives.Lean.Order

/-- The implication order has suprema by existential introduction and elimination. -/
public theorem ImplicationOrder.instCompleteLattice._proof_1 (c : ImplicationOrder → Prop) :
    ∃ s : ImplicationOrder, ∀ x : ImplicationOrder, (s → x) ↔ ∀ y, c y → y → x :=
  ⟨∃ y, c y ∧ y, fun _ => ⟨fun h y hy proof => h ⟨y, hy, proof⟩,
    fun h ⟨y, hy, proof⟩ => h y hy proof⟩⟩

/-- Reverse implication has the corresponding supremum given by a universal quantifier. -/
public theorem ReverseImplicationOrder.instCompleteLattice._proof_1 (c : ReverseImplicationOrder → Prop) :
    ∃ s : ReverseImplicationOrder, ∀ x : ReverseImplicationOrder, (x → s) ↔ ∀ y, c y → x → y :=
  ⟨∀ y, c y → y, fun _ => ⟨fun h y hy proof => h proof y hy,
    fun h proof y hy => h y hy proof⟩⟩

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

public theorem instCCPOPProd._proof_1 :
    type_of% (private_decl% @_root_.Lean.Order.instCCPOPProd._proof_1) := by
  intro α β _ _ c hc
  obtain ⟨a, ha⟩ := CCPO.has_csup (PProd.chain.chain_fst hc)
  obtain ⟨b, hb⟩ := CCPO.has_csup (PProd.chain.chain_snd hc)
  exact ⟨⟨a, b⟩, productSupremum ha hb⟩

@[instance_reducible] public def instCCPOPProd {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] : CCPO (α ×' β) where
  has_csup := instCCPOPProd._proof_1

public theorem instCompleteLatticePProd._proof_1 :
    type_of% (private_decl% @_root_.Lean.Order.instCompleteLatticePProd._proof_1) := by
  intro α β _ _ c
  obtain ⟨a, ha⟩ := CompleteLattice.has_sup (_root_.Lean.Order.PProd.fst c)
  obtain ⟨b, hb⟩ := CompleteLattice.has_sup (_root_.Lean.Order.PProd.snd c)
  exact ⟨⟨a, b⟩, productSupremum ha hb⟩

@[instance_reducible] public def instCompleteLatticePProd {α : Sort u} {β : Sort v}
    [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α ×' β) where
  has_sup := instCompleteLatticePProd._proof_1

public theorem instCCPOProd._proof_1 :
    type_of% (private_decl% @_root_.Lean.Order.instCCPOProd._proof_1) := by
  intro α β _ _ c hc
  have hc' : chain (fun p : α ×' β => c (p.1, p.2)) := fun _ _ ha hb => hc _ _ ha hb
  obtain ⟨p, hp⟩ := @CCPO.has_csup _ instCCPOPProd _ hc'
  exact ⟨(p.1, p.2), Prod.is_sup_of_pprod hp⟩

@[instance_reducible] public def instCCPOProd {α : Type u} {β : Type v} [CCPO α] [CCPO β] : CCPO (α × β) where
  has_csup := instCCPOProd._proof_1

public theorem instCompleteLatticeProd._proof_1 :
    type_of% (private_decl% @_root_.Lean.Order.instCompleteLatticeProd._proof_1) := by
  intro α β _ _ c
  obtain ⟨p, hp⟩ := @CompleteLattice.has_sup _ instCompleteLatticePProd
    (fun p : α ×' β => c (p.1, p.2))
  exact ⟨(p.1, p.2), Prod.is_sup_of_pprod hp⟩

@[instance_reducible] public def instCompleteLatticeProd {α : Type u} {β : Type v}
    [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  has_sup := instCompleteLatticeProd._proof_1

public theorem instMonadTailOption._proof_1 {α β : Type u} {a : Option α} {f g : α → Option β}
    [Nonempty β] (h : ∀ x, @PartialOrder.rel (Option β) instPartialOrderOption (f x) (g x)) :
    @PartialOrder.rel (Option β) instPartialOrderOption (a >>= f) (a >>= g) := by
  cases a with
  | none => exact FlatOrder.rel.refl
  | some x => exact h x

@[expose] public def admissible {α : Sort u} [CCPO α] (P : α → Prop) : Prop :=
  ∀ (c : α → Prop), chain c → (∀ x, c x → P x) → ∀ s, is_sup c s → P s

public theorem admissible_const_true {α : Sort u} [CCPO α] : admissible (fun (_ : α) => True) :=
  fun _ _ _ _ _ => trivial

public theorem admissible_and {α : Sort u} [CCPO α] (P Q : α → Prop)
    (hadm₁ : admissible P) (hadm₂ : admissible Q) : admissible (fun x => P x ∧ Q x) :=
  fun c hc h s hs => ⟨hadm₁ c hc (fun x hx => (h x hx).1) s hs,
    hadm₂ c hc (fun x hx => (h x hx).2) s hs⟩

public theorem admissible_pi {α : Sort u} [CCPO α] {β : Sort v} (P : α → β → Prop)
    (hadm₁ : ∀ y, admissible (fun x => P x y)) : admissible (fun x => ∀ y, P x y) :=
  fun c hc h s hs y => hadm₁ y c hc (fun x hx => h x hx y) s hs

public theorem admissible_pprod_fst {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] (P : α → Prop)
    (hadm : admissible P) : admissible (fun (x : α ×' β) => P x.1) := by
  intro c hc h s hs
  obtain ⟨a, ha⟩ := CCPO.has_csup (PProd.chain.chain_fst hc)
  obtain ⟨b, hb⟩ := CCPO.has_csup (PProd.chain.chain_snd hc)
  have same := is_sup_unique hs (productSupremum ha hb)
  cases same
  exact hadm _ (PProd.chain.chain_fst hc) (fun i ⟨j, hij⟩ => h ⟨i, j⟩ hij) a ha

public theorem admissible_pprod_snd {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] (P : β → Prop)
    (hadm : admissible P) : admissible (fun (x : α ×' β) => P x.2) := by
  intro c hc h s hs
  obtain ⟨a, ha⟩ := CCPO.has_csup (PProd.chain.chain_fst hc)
  obtain ⟨b, hb⟩ := CCPO.has_csup (PProd.chain.chain_snd hc)
  have same := is_sup_unique hs (productSupremum ha hb)
  cases same
  exact hadm _ (PProd.chain.chain_snd hc) (fun j ⟨i, hij⟩ => h ⟨i, j⟩ hij) b hb

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
      t.isConstOf ``Order.ReverseImplicationOrder.instOrder || t.isConstOf ``Order.instPartialOrderReaderT ||
      t.isConstOf ``Order.instPartialOrderStateT || t.isConstOf ``Order.instPartialOrderStateRefT').isSome
    unless args.any affected do return .continue
    if projection then
      let result ← withTransparency .all (whnf node)
      if result != node then return .visit result
    let ci ← getConstInfo name
    let expanded := (ci.instantiateValueLevelParams! levels (allowOpaque := true)).beta args
    return .visit (← withTransparency .all (whnf expanded)))

open Lean Elab Term in
local elab "pointwise_type% " t:term : term => do
  expandPointwise (← elabTerm t none)

namespace OmegaChecks.InitPort.Alternatives.Lean.Order

private theorem bindSteps {m : Type u → Type v} [Bind m] [∀ t, PartialOrder (m t)] [MonoBind m]
    {α β : Type u} {a b : m α} {f g : α → m β} (ab : a ⊑ b) (fg : ∀ t, f t ⊑ g t) :
    a >>= f ⊑ b >>= g :=
  PartialOrder.rel_trans (MonoBind.bind_mono_left ab) (MonoBind.bind_mono_right fg)

public theorem monotone_dite : pointwise_type% (type_of% @_root_.Lean.Order.monotone_dite) := by
  intro α β _ _ c d f g hf hg x y xy
  cases d with
  | isTrue h => exact hf x y xy h
  | isFalse h => exact hg x y xy h

public theorem Seq.monotone_seq : type_of% @_root_.Lean.Order.Seq.monotone_seq := by
  intro m _ _ _ α β γ _ _ f g hg hf x y xy
  change (g x <*> f x) ⊑ (g y <*> f y)
  rw [← bind_map, ← bind_map]
  exact bindSteps (hg x y xy) fun z => Functor.monotone_map f z hf x y xy

public theorem SeqLeft.monotone_seqLeft : type_of% @_root_.Lean.Order.SeqLeft.monotone_seqLeft := by
  intro m _ _ _ α β γ _ _ g f hf hg x y xy
  change (f x <* g x) ⊑ (f y <* g y)
  rw [seqLeft_eq, seqLeft_eq]
  exact Seq.monotone_seq g _ (Functor.monotone_map f _ hf) hg x y xy

public theorem SeqRight.monotone_seqRight : type_of% @_root_.Lean.Order.SeqRight.monotone_seqRight := by
  intro m _ _ _ α β γ _ _ g f hf hg x y xy
  change (f x *> g x) ⊑ (f y *> g y)
  rw [seqRight_eq, seqRight_eq]
  exact Seq.monotone_seq g _ (Functor.monotone_map f _ hf) hg x y xy

public theorem Array.monotone_modifyM :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_modifyM) := by
  intro m _ _ _ α γ _ xs i f hf x y xy
  change xs.modifyM i (f x) ⊑ xs.modifyM i (f y)
  unfold _root_.Array.modifyM
  by_cases h : i < xs.size
  · rw [dite_eq_left h, dite_eq_left h]
    exact MonoBind.bind_mono_left (hf x y xy _)
  · rw [dite_eq_right h, dite_eq_right h]

public theorem Array.monotone_foldlM_loop :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_foldlM_loop) := by
  intro m _ _ _ α β γ _ f xs stop bound i j b hf x y xy
  change _root_.Array.foldlM.loop (f x) xs stop bound i j b ⊑ _root_.Array.foldlM.loop (f y) xs stop bound i j b
  induction i generalizing j b with
  | zero =>
    unfold _root_.Array.foldlM.loop
    by_cases hj : j < stop
    · rw [dite_eq_left hj] <;> exact PartialOrder.rel_refl
    · rw [dite_eq_right hj] <;> exact PartialOrder.rel_refl
  | succ i ih =>
    unfold _root_.Array.foldlM.loop
    by_cases hj : j < stop
    · rw [dite_eq_left hj, dite_eq_left hj]
      exact bindSteps (hf x y xy _ _) (fun z => ih _ z)
    · rw [dite_eq_right hj, dite_eq_right hj] <;> exact PartialOrder.rel_refl

public theorem Array.monotone_foldrM_fold :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_foldrM_fold) := by
  intro m _ _ _ α β γ _ f xs stop i bound b hf x y xy
  change _root_.Array.foldrM.fold (f x) xs stop i bound b ⊑ _root_.Array.foldrM.fold (f y) xs stop i bound b
  induction i generalizing b with
  | zero =>
    unfold _root_.Array.foldrM.fold
    split <;> exact PartialOrder.rel_refl
  | succ i ih =>
    unfold _root_.Array.foldrM.fold
    split
    · exact PartialOrder.rel_refl
    · exact bindSteps (hf x y xy _ _) (fun z => ih _ z)

public theorem Array.monotone_findSomeRevM? :
    pointwise_type% (∀ {m : Type u → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
      {α β : Type u} {γ : Type w} [PartialOrder γ] (f : γ → α → m (Option β)) (xs : Array α),
      ∀ (hmono : monotone f), monotone fun x => InitPort.Alternatives.Array.findSomeRevM? (f x) xs) := by
  intro m _ _ _ α β γ _ f xs hf x y xy
  suffices ∀ i (h : i ≤ xs.size), InitPort.Alternatives.revPrefix (f x) xs i h ⊑
      InitPort.Alternatives.revPrefix (f y) xs i h by exact this _ _
  intro i h
  induction i with
  | zero => exact PartialOrder.rel_refl
  | succ i ih =>
    apply bindSteps (hf x y xy _)
    intro z
    cases z with
    | none => exact ih _
    | some _ => exact PartialOrder.rel_refl

public theorem Array.monotone_foldlM :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_foldlM) := by
  intro m _ _ _ α β γ _ f b xs start stop hf x y xy
  change xs.foldlM (f x) b start stop ⊑ xs.foldlM (f y) b start stop
  unfold _root_.Array.foldlM
  split <;> exact Array.monotone_foldlM_loop f xs _ _ _ _ b hf x y xy

public theorem Array.monotone_foldrM :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_foldrM) := by
  intro m _ _ _ α β γ _ f b xs start stop hf x y xy
  change xs.foldrM (f x) b start stop ⊑ xs.foldrM (f y) b start stop
  unfold _root_.Array.foldrM
  split <;> split
  all_goals first | exact PartialOrder.rel_refl | exact Array.monotone_foldrM_fold f xs _ _ _ b hf x y xy

public theorem List.monotone_allM {γ : Type u} [PartialOrder γ] {m : Type → Type v}
    [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type} (f : γ → α → m Bool) (xs : List α)
    (hmono : ∀ x y, x ⊑ y → (fun g k : α → m Bool => ∀ x, g x ⊑ k x) (f x) (f y)) :
    monotone (fun x => OmegaChecks.InitPort.Alternatives.List.allM (f x) xs) := by
  intro x y xy
  induction xs with
  | nil => exact PartialOrder.rel_refl
  | cons a xs ih =>
    apply bindSteps (hmono x y xy a)
    intro result
    cases result with
    | false => exact PartialOrder.rel_refl
    | true => exact ih

public theorem List.monotone_anyM {γ : Type u} [PartialOrder γ] {m : Type → Type v}
    [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type} (f : γ → α → m Bool) (xs : List α)
    (hmono : ∀ x y, x ⊑ y → (fun g k : α → m Bool => ∀ x, g x ⊑ k x) (f x) (f y)) :
    monotone (fun x => OmegaChecks.InitPort.Alternatives.List.anyM (f x) xs) := by
  intro x y xy
  induction xs with
  | nil => exact PartialOrder.rel_refl
  | cons a xs ih =>
    apply bindSteps (hmono x y xy a)
    intro result
    cases result with
    | false => exact ih
    | true => exact PartialOrder.rel_refl

public theorem Array.monotone_anyM_loop :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_anyM_loop) := by
  intro γ _ m _ _ _ α f xs stop bound j hf x y xy
  change _root_.Array.anyM.loop (f x) xs stop bound j ⊑ _root_.Array.anyM.loop (f y) xs stop bound j
  induction j using _root_.Array.anyM.loop.induct (h := bound) with
  | case2 j hj =>
    rw [_root_.Array.anyM.loop.eq_def, _root_.Array.anyM.loop.eq_def (p := f y),
      dite_eq_right hj, dite_eq_right hj]
  | case1 j hj _ ih =>
    rw [_root_.Array.anyM.loop.eq_def, _root_.Array.anyM.loop.eq_def (p := f y),
      dite_eq_left hj, dite_eq_left hj]
    apply bindSteps (hf x y xy _)
    intro result
    cases result with
    | false => exact ih
    | true => exact PartialOrder.rel_refl

public theorem Array.monotone_anyM :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_anyM) := by
  intro γ _ m _ _ _ α f xs start stop hf x y xy
  change xs.anyM (f x) start stop ⊑ xs.anyM (f y) start stop
  unfold _root_.Array.anyM
  split <;> exact Array.monotone_anyM_loop f xs _ _ _ hf x y xy

private theorem fuelMonotone {α : Sort u} {β : Sort v} [PartialOrder β] (measure : α → Nat)
    (left right : (x : α) → ((y : α) → InvImage (· < ·) measure y x → β) → β)
    (step : ∀ x f g, (∀ y h, f y h ⊑ g y h) → left x f ⊑ right x g) (x : α) :
    WellFounded.Nat.fix measure left x ⊑ WellFounded.Nat.fix measure right x := by
  suffices ∀ fuel x (h : measure x < fuel),
      WellFounded.Nat.fix.go measure left fuel x h ⊑ WellFounded.Nat.fix.go measure right fuel x h by
    exact this _ x _
  intro fuel
  induction fuel with
  | zero => exact fun _ h => (Nat.not_succ_le_zero _ h).elim
  | succ _ ih => exact fun x _ => step x _ _ fun y _ => ih y _

public theorem Array.monotone_mapM :
    pointwise_type% (type_of% @_root_.Lean.Order.Array.monotone_mapM) := by
  intro m _ _ _ α β γ _ xs f hf x y xy
  change xs.mapM (f x) ⊑ xs.mapM (f y)
  delta _root_.Array.mapM _root_.Array.mapM.map _root_.Array.mapM.map._unary
  apply fuelMonotone
  intro ⟨i, bs⟩ left right next
  dsimp only
  split
  · apply bindSteps (hf x y xy _)
    exact fun b => next ⟨i + 1, bs.push b⟩ _
  · exact PartialOrder.rel_refl

end OmegaChecks.InitPort.Alternatives.Lean.Order

open Lean Meta Elab Command in
run_meta do
  let env ← getEnv
  let orderLemmas := env.header.moduleData[(env.getModuleIdx? `Init.Internal.Order.Lemmas).get!.toNat]!
  let basicLemmas := #[``Order.MonadTail.monotone_bind_right, ``Order.monotone_bind, ``Order.monotone_dite, ``Order.monotone_readerTRun,
    ``Order.monotone_stateTRun, ``Order.monotone_stateRefT'Run, ``Order.monotone_apply, ``Order.monotone_of_monotone_apply,
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
