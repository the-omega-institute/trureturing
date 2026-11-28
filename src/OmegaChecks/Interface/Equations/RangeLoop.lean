module
public import OmegaChecks.InitPort.Alternatives.RangeLoop
import all OmegaChecks.InitPort.Alternatives.RangeLoop
import all Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Iterators.Consumers.Loop

/-! On finite ranges both implementations use the same step function at every input. -/

open Std Std.Iterators Std.PRange OmegaChecks.InitPort.Alternatives
namespace OmegaChecks.Interface.Equations
variable {α : Type u}

private theorem finiteRxcLoop_eq [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    {n : Type u → Type w} [Monad n] [Finite (Rxc.Iterator α) Id] :
    finiteRxcLoop (α := α) (n := n) = _root_.Std.Rxc.Iterator.instIteratorLoop := by
  change IteratorLoop.mk _ = IteratorLoop.mk _
  congr 1
  funext lift γ Pl it init f
  rcases it with ⟨⟨next, upper⟩⟩
  cases next with
  | none => rfl
  | some next =>
    dsimp only
    unfold finiteRxcLoop.loop _root_.Std.Rxc.Iterator.instIteratorLoop.loop
    letI : Nonempty γ := ⟨init⟩
    symm
    apply WellFounded.extrinsicFix₃_eq_fix

private theorem finiteRxoLoop_eq [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    {n : Type u → Type w} [Monad n] [Finite (Rxo.Iterator α) Id] :
    finiteRxoLoop (α := α) (n := n) = _root_.Std.Rxo.Iterator.instIteratorLoop := by
  change IteratorLoop.mk _ = IteratorLoop.mk _
  congr 1
  funext lift γ Pl it init f
  rcases it with ⟨⟨next, upper⟩⟩
  cases next with
  | none => rfl
  | some next =>
    dsimp only
    unfold finiteRxoLoop.loop _root_.Std.Rxo.Iterator.instIteratorLoop.loop
    letI : Nonempty γ := ⟨init⟩
    symm
    apply WellFounded.extrinsicFix₃_eq_fix

private theorem finiteRxiLoop_eq [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    {n : Type u → Type w} [Monad n] [Finite (Rxi.Iterator α) Id] :
    finiteRxiLoop (α := α) (n := n) = _root_.Std.Rxi.Iterator.instIteratorLoop := by
  change IteratorLoop.mk _ = IteratorLoop.mk _
  congr 1
  funext lift γ Pl it init f
  rcases it with ⟨⟨next⟩⟩
  cases next with
  | none => rfl
  | some next =>
    dsimp only
    unfold finiteRxiLoop.loop _root_.Std.Rxi.Iterator.instIteratorLoop.loop
    letI : Nonempty γ := ⟨init⟩
    symm
    apply WellFounded.extrinsicFix₃_eq_fix

public theorem Std.Rxc.Iterator.instIteratorLoop.loop [UpwardEnumerable α] [LE α] [DecidableLE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] {n : Type u → Type w} [Monad n]
    (γ : Type u) (Pl : α → γ → ForInStep γ → Prop) (large : α → Prop) (closed : ∀ a b : α, a ≤ b → large a → large b)
    (upper : α) (acc : γ) (next : α) (h : large next)
    (f : (out : α) → large out → out ≤ upper → (c : γ) → n (Subtype (Pl out c))) :
    OmegaChecks.InitPort.Alternatives.Std.Rxc.Iterator.instIteratorLoop.loop γ Pl large closed upper acc next h f =
      _root_.Std.Rxc.Iterator.instIteratorLoop.loop γ Pl large closed upper acc next h f := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rxc.Iterator.instIteratorLoop.loop finiteRxcLoop.loop _root_.Std.Rxc.Iterator.instIteratorLoop.loop
  letI : Nonempty γ := ⟨acc⟩
  symm
  apply WellFounded.extrinsicFix₃_eq_fix

public theorem Std.Rxo.Iterator.instIteratorLoop [UpwardEnumerable α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] {n : Type u → Type w} [Monad n] :
    OmegaChecks.InitPort.Alternatives.Std.Rxo.Iterator.instIteratorLoop (α := α) (n := n) = _root_.Std.Rxo.Iterator.instIteratorLoop := by
  letI := openFinite (α := α)
  exact finiteRxoLoop_eq

public theorem Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ =
      @_root_.Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId _root_.Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId
  rw [finiteRxcLoop_eq]

public theorem Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α] [LE α] [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ =
      @_root_.Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId _root_.Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId
  rw [finiteRxoLoop_eq]

public theorem Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ =
      @_root_.Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId _root_.Std.Rci.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId
  rw [finiteRxiLoop_eq]

public theorem Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LT α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ =
      @_root_.Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId _root_.Std.Roc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId
  rw [finiteRxcLoop_eq]

public theorem Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ =
      @_root_.Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId _root_.Std.Roo.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId
  rw [finiteRxoLoop_eq]

public theorem Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ =
      @_root_.Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId α m _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId _root_.Std.Roi.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId
  rw [finiteRxiLoop_eq]

public theorem Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LE α] [DecidableLE α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxc.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ =
      @_root_.Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId _root_.Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
  rw [finiteRxcLoop_eq]

public theorem Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α]
    [LT α] [DecidableLT α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxo.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ =
      @_root_.Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId _root_.Std.Rio.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
  rw [finiteRxoLoop_eq]

public theorem Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId {m} [UpwardEnumerable α] [Least? α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Monad m] [Finite (Rxi.Iterator α) Id] :
    @OmegaChecks.InitPort.Alternatives.Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ =
      @_root_.Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId α m _ _ _ _ _ _ := by
  unfold OmegaChecks.InitPort.Alternatives.Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId _root_.Std.Rii.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
  rw [finiteRxiLoop_eq]

end OmegaChecks.Interface.Equations
