module

public import Init.Data.Option.Lemmas
public import Init.Data.Option.Attach
public import Init.Data.Option.Monadic
public import Init.Data.Option.Array
public import Init.Data.Option.List

/-! Constructive witnesses for optional values and finite cases for filters and order. -/

namespace OmegaChecks.InitPort.Alternatives
namespace Option

/- Restoring the public constructor matcher also requires a whole-function proof of
`not_comp_isSome`. `PublicAlgorithmEquations.ofClassifier` characterizes that obligation
by absence testing after an arbitrary optional step. -/
@[expose] public def isNone {α : Type u} (x : _root_.Option α) : Bool := !x.isSome

public theorem not_comp_isSome {α : Type u} :
    (! ·) ∘ @_root_.Option.isSome α = @isNone α := rfl

open _root_.Option

public theorem eq_none_iff_forall_some_ne : type_of% @_root_.Option.eq_none_iff_forall_some_ne := by
  intro α o
  exact ⟨fun e a h => some_ne_none a (h.trans e), fun h => by
    cases o with
    | none => rfl
    | some a => exact (h a rfl).elim⟩

public theorem ne_none_iff_exists : type_of% @_root_.Option.ne_none_iff_exists := by
  intro α o
  constructor
  · intro h
    cases o with
    | none => exact (h rfl).elim
    | some a => exact ⟨a, rfl⟩
  · exact fun ⟨a, ha⟩ h => some_ne_none a (ha.trans h)

public theorem all_eq_false_iff_get : type_of% @_root_.Option.all_eq_false_iff_get := by
  intro α p o
  cases o with
  | none => exact ⟨(fun h => nomatch h), fun ⟨h, _⟩ => nomatch h⟩
  | some a => exact ⟨fun h => ⟨rfl, h⟩, fun ⟨_, h⟩ => h⟩

public theorem filter_filter : type_of% @_root_.Option.filter_filter := by
  intro α q p o
  cases o with
  | none => rfl
  | some a =>
    simp only [filter_some]
    cases hp : p a <;> cases hq : q a <;> simp only [Bool.and_self, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, ite_true, ite_false, filter_none, filter_some, hq]

public theorem filter_or_filter : type_of% @_root_.Option.filter_or_filter := by
  intro α o o' p
  cases o with
  | some _ => rfl
  | none =>
    cases o' with
    | none => rfl
    | some a =>
      change ((some a).filter p).filter p = (some a).filter p
      simp only [filter_some]
      cases h : p a <;> simp only [Bool.false_eq_true, ite_true, ite_false, filter_none, filter_some, h]

public theorem min_eq_or : type_of% @_root_.Option.min_eq_or := by
  intro α _ _ choose a b
  cases a with
  | none => cases b <;> exact .inl rfl
  | some a =>
    cases b with
    | none => exact .inr rfl
    | some b =>
      exact (choose a b).elim (fun h => .inl (congrArg some h)) (fun h => .inr (congrArg some h))

public theorem max_eq_or : type_of% @_root_.Option.max_eq_or := by
  intro α _ _ choose a b
  cases a with
  | none => cases b <;> exact .inr rfl
  | some a =>
    cases b with
    | none => exact .inl rfl
    | some b =>
      exact (choose a b).elim (fun h => .inl (congrArg some h)) (fun h => .inr (congrArg some h))

public theorem guard_le_some : type_of% @_root_.Option.guard_le_some := by
  intro α _ refl x p
  rw [guard_eq_ite]
  cases h : p x with
  | false => exact none_le
  | true => exact some_le_some.mpr (refl x)

public theorem guard_lt_some : type_of% @_root_.Option.guard_lt_some := by
  intro α _ irrefl x p
  rw [guard_eq_ite]
  cases h : p x with
  | false => exact ⟨fun _ => rfl, fun _ => none_lt_some⟩
  | true => exact ⟨fun hx => (irrefl x (some_lt_some.mp hx)).elim, fun e => nomatch e⟩

public theorem dite_none_left_eq_some : type_of% @_root_.Option.dite_none_left_eq_some := by
  intro β a p dec f
  cases dec with
  | isTrue yes => exact ⟨(fun e => nomatch e), fun ⟨no, _⟩ => (no yes).elim⟩
  | isFalse no => exact ⟨fun e => ⟨no, e⟩, fun ⟨_, e⟩ => e⟩

public theorem some_eq_dite_none_left : type_of% @_root_.Option.some_eq_dite_none_left := by
  intro β a p dec f
  cases dec with
  | isTrue yes => exact ⟨(fun e => nomatch e), fun ⟨no, _⟩ => (no yes).elim⟩
  | isFalse no => exact ⟨fun e => ⟨no, e⟩, fun ⟨_, e⟩ => e⟩

public theorem pbind_congr : type_of% @_root_.Option.pbind_congr := by
  intro α β o o' eq f g same
  cases eq
  cases o with
  | none => rfl
  | some a => exact same a rfl

public theorem pfilter_congr : type_of% @_root_.Option.pfilter_congr := by
  intro α o o' eq f g same
  cases eq
  cases o with
  | none => rfl
  | some a => rw [pfilter_some, pfilter_some, same a rfl]

public theorem filter_le : type_of% @_root_.Option.filter_le := by
  intro α inst refl o p
  cases o with
  | none => exact none_le
  | some a =>
    cases h : p a with
    | true => rw [filter_some_pos h]; exact some_le_some.mpr (refl a)
    | false => rw [filter_some_neg h]; exact none_le

public theorem filter_lt : type_of% @_root_.Option.filter_lt := by
  intro α inst irrefl o p
  cases o with
  | none => exact ⟨(fun h => (not_lt_none h).elim), (fun e => nomatch e)⟩
  | some a =>
    change (some a).filter p < some a ↔ (!p a) = true
    cases h : p a with
    | true =>
      rw [filter_some_pos h]
      exact ⟨fun h => (irrefl a (some_lt_some.mp h)).elim, (fun e => nomatch e)⟩
    | false =>
      rw [filter_some_neg h]
      exact ⟨fun _ => rfl, fun _ => none_lt_some⟩

public theorem not_lt_filter : type_of% @_root_.Option.not_lt_filter := by
  intro α inst irrefl o p
  cases o with
  | none => exact not_lt_none
  | some a =>
    cases h : p a with
    | true => rw [filter_some_pos h]; exact fun h => irrefl a (some_lt_some.mp h)
    | false => rw [filter_some_neg h]; exact not_lt_none

public theorem le_filter : type_of% @_root_.Option.le_filter := by
  intro α inst refl o p
  cases o with
  | none => exact ⟨fun _ => rfl, fun _ => none_le⟩
  | some a =>
    change some a ≤ (some a).filter p ↔ p a = true
    cases h : p a with
    | true => rw [filter_some_pos h]; exact ⟨fun _ => rfl, fun _ => some_le_some.mpr (refl a)⟩
    | false => rw [filter_some_neg h]; exact ⟨fun h => (not_some_le_none h).elim, (fun e => nomatch e)⟩

public theorem pfilter_le : type_of% @_root_.Option.pfilter_le := by
  intro α inst refl o p
  cases o with
  | none => exact none_le
  | some a =>
    rw [pfilter_some]
    cases h : p a rfl with
    | true => exact some_le_some.mpr (refl a)
    | false => exact none_le

public theorem not_lt_pfilter : type_of% @_root_.Option.not_lt_pfilter := by
  intro α inst irrefl o p
  cases o with
  | none => exact not_lt_none
  | some a =>
    rw [pfilter_some]
    cases h : p a rfl with
    | true => exact fun h => irrefl a (some_lt_some.mp h)
    | false => exact not_lt_none

public theorem ite_none_left_eq_some : type_of% @_root_.Option.ite_none_left_eq_some := by
  intro β a p dec b
  cases dec with
  | isTrue yes => exact ⟨(fun e => nomatch e), fun ⟨no, _⟩ => (no yes).elim⟩
  | isFalse no => exact ⟨fun e => ⟨no, e⟩, And.right⟩

public theorem some_eq_ite_none_left : type_of% @_root_.Option.some_eq_ite_none_left := by
  intro β a p dec b
  cases dec with
  | isTrue yes => exact ⟨(fun e => nomatch e), fun ⟨no, _⟩ => (no yes).elim⟩
  | isFalse no => exact ⟨fun e => ⟨no, e⟩, And.right⟩

public theorem le_min : type_of% @_root_.Option.le_min := by
  intro α inst min law a b c
  cases a <;> cases b <;> cases c
  all_goals first
    | exact law _ _ _
    | exact ⟨fun _ => ⟨none_le, none_le⟩, fun _ => none_le⟩
    | exact ⟨fun h => (not_some_le_none h).elim, fun h => h.1⟩
    | exact ⟨fun h => (not_some_le_none h).elim, fun h => h.2⟩

public theorem max_le : type_of% @_root_.Option.max_le := by
  intro α inst max law a b c
  cases a <;> cases b <;> cases c
  all_goals first
    | exact law _ _ _
    | exact ⟨fun h => ⟨none_le, h⟩, And.right⟩
    | exact ⟨fun h => ⟨h, none_le⟩, And.left⟩
    | exact ⟨fun h => (not_some_le_none h).elim, fun h => (not_some_le_none h.1).elim⟩

public theorem merge_le_iff : type_of% @_root_.Option.merge_le_iff := by
  intro α inst f a b c law
  cases a <;> cases b <;> cases c
  all_goals first
    | exact law _ _ _
    | exact ⟨fun h => ⟨none_le, h⟩, And.right⟩
    | exact ⟨fun h => ⟨h, none_le⟩, And.left⟩
    | exact ⟨fun h => (not_some_le_none h).elim, fun h => (not_some_le_none h.1).elim⟩

public theorem merge_lt_iff : type_of% @_root_.Option.merge_lt_iff := by
  intro α inst f a b c law
  cases a <;> cases b <;> cases c
  all_goals first
    | exact law _ _ _
    | exact ⟨fun h => (not_lt_none h).elim, fun h => (not_lt_none h.1).elim⟩
    | exact ⟨fun h => ⟨none_lt_some, h⟩, And.right⟩
    | exact ⟨fun h => ⟨h, none_lt_some⟩, And.left⟩

public theorem mem_ite_none_left : type_of% @_root_.Option.mem_ite_none_left := by
  intros
  apply Option.ite_none_left_eq_some

public theorem mem_dite_none_left : type_of% @_root_.Option.mem_dite_none_left := by
  intros
  apply Option.dite_none_left_eq_some

public theorem forIn'_congr [Monad m] [LawfulMonad m] {as bs : Option α} (w : as = bs)
    {b b' : β} (hb : b = b') {f : (a : α) → a ∈ as → β → m (ForInStep β)}
    {g : (a : α) → a ∈ bs → β → m (ForInStep β)}
    (h : ∀ a h b, f a (w.symm ▸ h) b = g a h b) : forIn' as b f = forIn' bs b' g := by
  cases w
  cases hb
  cases as with
  | none => rfl
  | some a => exact congrArg (fun x => x >>= _) (h a rfl b)

public theorem forIn'_pure_yield_eq_pelim : type_of% @_root_.Option.forIn'_pure_yield_eq_pelim := by
  intro m α β _ _ o f b
  cases o with
  | none => rfl
  | some a => exact pure_bind _ _

public theorem forIn_pure_yield_eq_elim : type_of% @_root_.Option.forIn_pure_yield_eq_elim := by
  intro m α β _ _ o f b
  cases o with
  | none => rfl
  | some a => exact pure_bind _ _

public theorem toArray_pbind : type_of% @_root_.Option.toArray_pbind := by
  intro α β o f
  cases o with
  | none => rfl
  | some a =>
    exact (@Array.flatMap_singleton _ _
      (fun x : {a' // some a = some a'} => (f x.val x.property).toArray) ⟨a, rfl⟩).symm

public theorem attach_filter : type_of% @_root_.Option.attach_filter := by
  intro α o p
  cases o with
  | none => rfl
  | some a =>
    apply (Option.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
    rw [Option.attach_map_subtype_val]
    simp only [Option.attach_some, Option.bind_some]
    by_cases eq : p a = true
    · rw [dite_eq_left eq]
      change Option.filter p (some a) = some a
      exact ite_eq_left eq
    · rw [dite_eq_right eq]
      exact ite_eq_right eq

public theorem toArray_bind : type_of% @_root_.Option.toArray_bind := by
  intro α β o f
  cases o with
  | none => rfl
  | some x => exact (_root_.Array.flatMap_singleton (f := Option.toArray ∘ f)).symm

public theorem toArray_join : type_of% @_root_.Option.toArray_join := by
  intro α o
  exact toArray_bind (o := o) (f := id)

public theorem foldrM_toArray : type_of% @_root_.Option.foldrM_toArray := by
  intro m β α _ _ o a f
  cases o with
  | none => exact Array.foldrM_empty
  | some b =>
    change (#[].push b).foldrM f a = f b a
    change (f b a >>= pure) = _
    exact bind_pure _

public theorem foldrM_toList : type_of% @_root_.Option.foldrM_toList := by
  intro m β α _ _ o a f
  cases o with
  | none => rfl
  | some b =>
    change (f b a >>= pure) = f b a
    exact bind_pure _

end Option
end OmegaChecks.InitPort.Alternatives
