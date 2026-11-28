module
public import OmegaChecks.InitPort.Alternatives.Logic.Quotient
public import Init.WFComputable
public import Init.Ext
public import Init.SimpLemmas
public import Init.PropLemmas
public import Init.Sym.Lemmas
public import Init.Data.Sum.Lemmas
public import Init.Data.Erased
import all Init.System.Promise
import all Init.ShareCommon

namespace OmegaChecks.InitPort.Alternatives

public theorem IO.Option.getOrBlock!._proof_1 :
    type_of% (private_decl% @_root_.IO.Option.getOrBlock!._proof_1) := by
  rintro α ⟨fallback⟩
  exact ⟨fun opt => opt.getD fallback⟩

public theorem ShareCommon.StateFactory.mk._proof_1 :
    type_of% (private_decl% @_root_.ShareCommon.StateFactory.mk._proof_1) := by
  obtain ⟨factory⟩ := _root_.ShareCommon.StateFactoryPointed.property
  exact ⟨fun _ => factory⟩

/-- The argument of a thunk has a unique constructor, so applying it at unit reconstructs the thunk. -/
public theorem Thunk.ext : type_of% @_root_.Thunk.ext := by
  intro α a b h
  exact congrArg (fun x => _root_.Thunk.mk (fun _ => x)) h

public theorem Erased.mk_inj : type_of% @_root_.Erased.mk_inj := by
  intro α a b
  constructor
  · intro h
    have test := congrArg (fun e : _root_.Erased α => e.val b) h
    exact cast test.symm (Eq.refl b)
  · intro h
    exact congrArg _root_.Erased.mk h

public theorem eqRec_heq_iff._simp_1.{u,v} :
    type_of% @_root_.eqRec_heq_iff._simp_1.{u,v} := by
  intro β α a motive b base h c
  cases h
  rfl

public theorem heq_eqRec_iff._simp_1.{u,v} :
    type_of% @_root_.heq_eqRec_iff._simp_1.{u,v} := by
  intro β α a motive b base h c
  cases h
  rfl

public theorem let_congr : type_of% @_root_.let_congr :=
  fun {_ _ a _ _ _} ha hb => ha ▸ hb a

public theorem let_body_congr : type_of% @_root_.let_body_congr :=
  fun {_ _ _ _} a h => h a

public theorem have_congr' : type_of% @_root_.have_congr' :=
  @_root_.OmegaChecks.InitPort.Alternatives.let_congr

public theorem Lean.Sym.ite_of_decide_eq_true_congr :
    type_of% @_root_.Lean.Sym.ite_of_decide_eq_true_congr :=
  fun {_} _ {_} _ _ _ h {_ ht} => ite_eq_left (h.mpr (of_decide_eq_true ht))

public theorem Lean.Sym.ite_of_decide_eq_false_congr :
    type_of% @_root_.Lean.Sym.ite_of_decide_eq_false_congr :=
  fun {_} _ {_} _ _ _ h {_ ht} => ite_eq_right (fun hc => of_decide_eq_false ht (h.mp hc))

public theorem Sum.elim_eq_iff : type_of% @_root_.Sum.elim_eq_iff := by
  intro α β γ u u' v v'
  constructor
  · intro e
    exact ⟨congrArg (fun f => f ∘ Sum.inl) e, congrArg (fun f => f ∘ Sum.inr) e⟩
  · rintro ⟨rfl, rfl⟩
    rfl

public theorem Decidable.not_or_self (p : Prop) [d : Decidable p] : ¬p ∨ p :=
  match d with
  | .isTrue hp => .inr hp
  | .isFalse hn => .inl hn

public theorem Decidable.not_imp_self {a : Prop} [d : Decidable a] : (¬a → a) ↔ a :=
  ⟨fun f => match d with
    | .isTrue h => h
    | .isFalse h => f h,
   fun h _ => h⟩

public theorem Decidable.imp_or {a b c : Prop} [d : Decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := by
  constructor
  · intro f
    cases d with
    | isTrue ha => exact (f ha).elim (fun hb => .inl fun _ => hb) (fun hc => .inr fun _ => hc)
    | isFalse ha => exact .inl fun h => (ha h).elim
  · exact fun h a => h.elim (fun f => .inl (f a)) (fun f => .inr (f a))

public theorem Decidable.imp_or' {b : Prop} {a : Sort u} {c : Prop} [d : Decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := by
  constructor
  · intro f
    cases d with
    | isTrue hb => exact .inl fun _ => hb
    | isFalse hb => exact .inr fun ha => (f ha).resolve_left hb
  · exact fun h a => h.elim (fun f => .inl (f a)) (fun f => .inr (f a))

public theorem ite_false_left {p q : Prop} [d : Decidable p] : (if p then False else q) ↔ ¬p ∧ q := by
  cases d with
  | isTrue h => exact ⟨False.elim, fun s => s.1 h⟩
  | isFalse h => exact ⟨fun q => ⟨h, q⟩, And.right⟩

public theorem ite_not_self_left {p : Prop} [d : Decidable p] {q : Prop} : (if p then ¬p else q) ↔ ¬p ∧ q := by
  cases d with
  | isTrue h => exact ⟨fun n => (n h).elim, And.left⟩
  | isFalse h => exact ⟨fun q => ⟨h, q⟩, And.right⟩

public theorem dite_false_left {p : Prop} [d : Decidable p] {x : ¬p → Prop} :
    (if h : p then False else x h) ↔ ∃ h : ¬p, x h := by
  cases d with
  | isTrue h => exact ⟨False.elim, fun ⟨n, _⟩ => n h⟩
  | isFalse n => exact ⟨fun x => ⟨n, x⟩, fun ⟨_, x⟩ => x⟩

public theorem Bool.ite_false_left_eq_true : type_of% @_root_.Bool.ite_false_left_eq_true := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Bool.noConfusion, fun s => (s.1 h).elim⟩
  | isFalse n => exact ⟨fun e => ⟨n, e⟩, And.right⟩

public theorem Bool.ite_true_left_eq_false : type_of% @_root_.Bool.ite_true_left_eq_false := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Bool.noConfusion, fun s => (s.1 h).elim⟩
  | isFalse n => exact ⟨fun e => ⟨n, e⟩, And.right⟩

public theorem Bool.ite_true_right_eq_true : type_of% @_root_.Bool.ite_true_right_eq_true := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Or.inr, fun s => s.resolve_left (fun n => n h)⟩
  | isFalse n => exact ⟨fun _ => .inl n, fun _ => rfl⟩

public theorem Bool.ite_false_right_eq_false : type_of% @_root_.Bool.ite_false_right_eq_false := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Or.inr, fun s => s.resolve_left (fun n => n h)⟩
  | isFalse n => exact ⟨fun _ => .inl n, fun _ => rfl⟩

public theorem Bool.dite_false_left_eq_true : type_of% @_root_.Bool.dite_false_left_eq_true := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Bool.noConfusion, fun ⟨n, _⟩ => (n h).elim⟩
  | isFalse n => exact ⟨fun e => ⟨n, e⟩, fun ⟨_, e⟩ => e⟩

public theorem Bool.dite_true_left_eq_false : type_of% @_root_.Bool.dite_true_left_eq_false := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨Bool.noConfusion, fun ⟨n, _⟩ => (n h).elim⟩
  | isFalse n => exact ⟨fun e => ⟨n, e⟩, fun ⟨_, e⟩ => e⟩

public theorem Bool.dite_false_right_eq_true : type_of% @_root_.Bool.dite_false_right_eq_true := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨fun e => ⟨h, e⟩, fun ⟨_, e⟩ => e⟩
  | isFalse n => exact ⟨Bool.noConfusion, fun ⟨h, _⟩ => (n h).elim⟩

public theorem Bool.dite_true_right_eq_false : type_of% @_root_.Bool.dite_true_right_eq_false := by
  intro p d x
  cases d with
  | isTrue h => exact ⟨fun e => ⟨h, e⟩, fun ⟨_, e⟩ => e⟩
  | isFalse n => exact ⟨Bool.noConfusion, fun ⟨h, _⟩ => (n h).elim⟩

@[expose] public noncomputable def Acc.recC : type_of% @_root_.Acc.recC := @_root_.Acc.rec
public theorem Acc.rec_eq_recC : @_root_.Acc.rec = @Acc.recC := rfl

end OmegaChecks.InitPort.Alternatives
