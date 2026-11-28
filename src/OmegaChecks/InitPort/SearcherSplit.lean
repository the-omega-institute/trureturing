module
public import OmegaChecks.InitPort.CertifiedFunction
public import Init.Data.String.Lemmas.Pattern.Split.Basic
import all Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.Iterators.Lemmas.Consumers.Collect

/-! The terminal suffix is empty and a finite lawful searcher determines the split of the entire slice. -/

open String String.Slice String.Slice.Pattern String.Slice.Pattern.Model
namespace OmegaChecks.InitPort.SearcherSplit

@[expose] public noncomputable def terminalReference {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat] {s : Slice} (f : s.Pos) (le : f ≤ s.endPos) :=
  Model.split pat f s.endPos le

public def terminal : type_of% @terminalReference :=
  fun {_} _ _ _ {s} f le => [s.subslice f s.endPos le]

public theorem terminalAgreement : @terminalReference = @terminal := by
  funext ρ pat model strict s f le
  exact Model.split_endPos

@[expose] public noncomputable def searchReference {ρ : Type} (pat : ρ) [PatternModel pat]
    [StrictPatternModel pat] {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id]
    [LawfulToForwardSearcherModel pat] (s : Slice) (le : s.startPos ≤ s.startPos) :=
  Model.split pat s.startPos s.startPos le

public def search : type_of% @searchReference :=
  fun {_} pat _ _ {_} _ _ _ _ s _ =>
    splitFromSteps s.startPos (ToForwardSearcher.toSearcher pat s).ensureTermination.toList

public theorem searchAgreement : @searchReference = @search := by
  funext ρ pat model strict σ searcher iter finite law s le
  unfold searchReference search
  rw [Std.Iter.toList_ensureTermination,
    ← toList_splitToSubslice_eq_splitFromSteps, toList_splitToSubslice_eq_modelSplit]

end OmegaChecks.InitPort.SearcherSplit
