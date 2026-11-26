module

public import OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.IteratorSlice
import all Init.Data.Slice.Array.Iterator
import all Init.Data.Slice.List.Iterator
import all Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Combinators.Monadic.Take

/-! The finite collectors run the same step function as the general official collectors. -/

open Std Std.Iterators Std.Iterators.Types
namespace OmegaChecks.Interface.Equations

public theorem Std.IterM.Total.toArray {α : Type u} {m : Type u → Type v} {β : Type u}
    [Monad m] [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray it = it.toArray := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray OmegaChecks.InitPort.Alternatives.collectArrayFrom
    _root_.Std.IterM.Total.toArray IterM.toArray IterM.toArray.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := Array β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.IterM.Total.toListRev {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev it = it.toListRev := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev
    _root_.Std.IterM.Total.toListRev IterM.toListRev IterM.toListRev.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := List β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.Iterators.Types.Take.Rel {α β : Type w} (m : Type w → Type v)
    [Monad m] [Iterator α m β] [Productive α m] (a b : IterM (α := Take α m) m β) :
    OmegaChecks.InitPort.Alternatives.Std.Iterators.Types.Take.Rel m a b = _root_.Std.Iterators.Types.Take.Rel m a b := by
  apply propext
  unfold OmegaChecks.InitPort.Alternatives.Std.Iterators.Types.Take.Rel _root_.Std.Iterators.Types.Take.Rel
  split
  next hf =>
    rw [InvImage, Prod.lex_def]
    constructor
    · rintro (hlt | ⟨heq, hp | ⟨_, hfin⟩⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, .of_productive hp⟩
      · exact Or.inr ⟨heq, hfin⟩
    · rintro (hlt | ⟨heq, hfin⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, Or.inr ⟨hf, hfin⟩⟩
  next hnf =>
    rw [InvImage, Prod.lex_def]
    constructor
    · rintro (hlt | ⟨heq, hp | ⟨hf, _⟩⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, hp⟩
      · exact False.elim (hnf hf)
    · rintro (hlt | ⟨heq, hp⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, Or.inl hp⟩

public theorem instSliceSizeListSliceData (α : Type u) :
    @OmegaChecks.InitPort.Alternatives.instSliceSizeListSliceData α = @_root_.instSliceSizeListSliceData α := by
  change Std.Slice.SliceSize.mk _ = Std.Slice.SliceSize.mk _
  congr 1
  funext s
  change (match s.internalRepresentation.stop with
    | none => s.internalRepresentation.list.length
    | some n => min n s.internalRepresentation.list.length) = s.size
  rw [ListSlice.size_eq_length_toList, ListSlice.toList_eq]
  cases s.internalRepresentation.stop <;> simp [List.length_take]

public theorem Array.instAppendSubarray {α : Type u} :
    @OmegaChecks.InitPort.Alternatives.Array.instAppendSubarray α = @_root_.Array.instAppendSubarray α := by
  change Append.mk _ = Append.mk _
  congr 1

public theorem List.instAppendListSlice {α : Type u} :
    @OmegaChecks.InitPort.Alternatives.List.instAppendListSlice α = @_root_.List.instAppendListSlice α := by
  change Append.mk _ = Append.mk _
  congr 1
  funext x y
  change ((OmegaChecks.InitPort.Alternatives.listSliceContents x ++ OmegaChecks.InitPort.Alternatives.listSliceContents y).toSlice 0 _) =
    (x.toList ++ y.toList).toSlice 0 _
  rw [ListSlice.toList_eq (xs := x), ListSlice.toList_eq (xs := y)]
  rcases x with ⟨⟨a, o⟩⟩
  rcases y with ⟨⟨b, p⟩⟩
  cases o <;> cases p <;> rfl

end OmegaChecks.Interface.Equations
