module
public import OmegaChecks.InitPort.Alternatives.RangeLoop
import all OmegaChecks.InitPort.Alternatives.RangeLoop
public import Init.Data.Range.Polymorphic.Lemmas
import all Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Iterators.Consumers.Loop

/-! Transport finite range iteration along equality of its first element. -/

open Std Std.PRange Std.Iterators
namespace OmegaChecks.InitPort.Alternatives

attribute [local instance 1100] Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
attribute [local instance 1100] Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId
attribute [local instance 1100] Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
attribute [local instance 1100] Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId
attribute [local instance 1100] Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
attribute [local instance 1100] Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId

public theorem Std.Rii.forIn'_eq_match_rci {α : Type u} {r : Rii α}
    [LE α] [Least? α] [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = Option.casesOn (Least?.least? (α := α)) (pure init)
      (fun next => ForIn'.forIn' (next...*) init (fun a _ acc => f a True.intro acc)) := by
  let run (start : Option α) : m γ := by
    letI : IteratorLoop (Rxi.Iterator α) Id m := finiteRxiLoop
    letI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    exact ForIn'.forIn' (Iter.mk (β := α) (Rxi.Iterator.mk start)) init (fun a _ => f a True.intro)
  change run Least?.least? = _
  cases Least?.least? (α := α) <;> rfl

public theorem Std.Ric.forIn'_eq_forIn'_rcc {α : Type u} {r : Ric α} [LE α] [DecidableLE α] [Least? α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f =
      ForIn'.forIn' (UpwardEnumerable.least...=r.upper) init
        (fun a ha acc => f a (_root_.Std.Ric.mem_of_mem_rcc ha) acc) := by
  letI : Nonempty α := ⟨r.upper⟩
  let run (start : Option α) : m γ := by
    letI : IteratorLoop (Rxc.Iterator α) Id m := finiteRxcLoop
    letI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (Iter.mk (β := α) (Rxc.Iterator.mk start r.upper)) init (fun a ha => f a ?_)
    exact (_root_.Std.Rxc.Iterator.isPlausibleIndirectOutput_iff.mp ha).choose_spec.2
  change run Least?.least? = run (some UpwardEnumerable.least)
  exact congrArg run UpwardEnumerable.least?_eq_some

public theorem Std.Rio.forIn'_eq_forIn'_rco {α : Type u} {r : Rio α} [LE α] [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {m : Type u → Type w} [Monad m]
    [LawfulMonad m] {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    haveI : Nonempty α := ⟨r.upper⟩
    ForIn'.forIn' r init f = ForIn'.forIn' (UpwardEnumerable.least...r.upper) init
        (fun a ha acc => f a (_root_.Std.Rio.mem_of_mem_rco ha) acc) := by
  letI : Nonempty α := ⟨r.upper⟩
  let run (start : Option α) : m γ := by
    letI : IteratorLoop (Rxo.Iterator α) Id m := finiteRxoLoop
    letI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    refine ForIn'.forIn' (Iter.mk (β := α) (Rxo.Iterator.mk start r.upper)) init (fun a ha => f a ?_)
    exact (_root_.Std.Rxo.Iterator.isPlausibleIndirectOutput_iff.mp ha).choose_spec.2
  change run Least?.least? = run (some UpwardEnumerable.least)
  exact congrArg run UpwardEnumerable.least?_eq_some

end OmegaChecks.InitPort.Alternatives
