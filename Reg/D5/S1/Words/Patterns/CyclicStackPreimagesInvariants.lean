import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace GapsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Gaps

theorem dependence : ObservationalDependence Gaps.signature actual := by
  intro i
  refine ⟨(0 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [Gaps.actual, Gaps.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ Gaps.arena.Law rejected := by
  intro h
  have h := @h 0 [1] (Gapped.last (by decide))
  have h := h.2.1
  change (0 : ℕ) = 1 at h
  cases h

def registration : Registration Gaps.arena (∀ {m : ℕ} {input : List ℕ}
    (hgapped : Gapped m input),
    assembleGaps (highEntries m input) (gapSlots m input) = input ∧
      (gapSlots m input).length = (highEntries m input).length ∧
      (gapSlots m input).filterMap id = lowEntries m input) where
  actual := Gaps.actual
  bridge := Iff.rfl
  variation := ⟨@gapped_filters_slots, Gaps.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem gapped_filters_slots in Gaps.arena
  readout via (realize Gaps.signature (fun _ m input => gapSlots m input) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end GapsAudit

namespace SuccessPermAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessPerm

theorem dependence : ObservationalDependence SuccessPerm.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [SuccessPerm.actual, SuccessPerm.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ SuccessPerm.arena.Law rejected := by
  intro h
  have h := @h 0 [0] rfl
  have h := h.length_eq
  change (1 : ℕ) = 0 at h
  cases h

def registration : Registration SuccessPerm.arena (∀ {n : ℕ} {input : List ℕ}
    (houtput : cyclicStackSort input = target n),
    input.Perm (List.range' 1 n)) where
  actual := SuccessPerm.actual
  bridge := Iff.rfl
  variation := ⟨@success_perm_range, SuccessPerm.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem success_perm_range in SuccessPerm.arena
  readout via (realize SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end SuccessPermAudit

namespace SuccessGappedAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.SuccessGapped

theorem dependence : ObservationalDependence SuccessPerm.signature SuccessPerm.actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [SuccessPerm.actual, SuccessPerm.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ SuccessGapped.arena.Law rejected := by
  intro h
  have h := @h 2 (by decide) [1] rfl
  cases h with
  | last hhigh => exact (Nat.lt_irrefl 1) hhigh

def registration : Registration SuccessGapped.arena (∀ {n : ℕ} (hn : 2 ≤ n) {input : List ℕ}
    (houtput : cyclicStackSort input = target n),
    Gapped (n / 2) input) where
  actual := SuccessPerm.actual
  bridge := Iff.rfl
  variation := ⟨@successful_gapped, SuccessGapped.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem successful_gapped in SuccessGapped.arena
  readout via (realize SuccessPerm.signature (fun _ _ input => cyclicStackSort input) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

end SuccessGappedAudit

namespace LowOrderAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.LowOrder

theorem dependence : ObservationalDependence LowOrder.signature actual := by
  intro i
  refine ⟨(2 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [LowOrder.actual, LowOrder.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ LowOrder.arena.Law rejected := by
  intro h
  have h := @h 0 [] Gapped.nil rfl
  have h := (List.pairwise_cons.mp h).1 0 (by simp)
  exact (Nat.not_lt_zero 1) h

def registration : Registration LowOrder.arena (∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (houtput : cyclicStackSort input = target n),
    (lowEntries (n / 2) input).Pairwise (fun x y => x < y)) where
  actual := LowOrder.actual
  bridge := Iff.rfl
  variation := ⟨@successful_lows_pairwise, LowOrder.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem successful_lows_pairwise in LowOrder.arena
  readout via (realize LowOrder.signature (fun _ (n : ℕ) input => lowEntries (n / 2) input) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end LowOrderAudit

namespace OneNoneAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OneNone

theorem dependence : ObservationalDependence OneNone.signature actual := by
  intro i
  refine ⟨(), [], [some (0 : ℕ)], ?_⟩
  dsimp only [OneNone.actual, OneNone.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ OneNone.arena.Law rejected := by
  intro h
  have h := @h [some 0] [] rfl rfl
  obtain ⟨i, hi, heq⟩ := h
  have hi : i = 0 := by simpa using hi
  subst i
  cases heq

def registration : Registration OneNone.arena (∀ {slots : List (Option ℕ)} {lows : List ℕ}
    (hfilter : slots.filterMap id = lows)
    (hlen : slots.length = lows.length + 1),
    ∃ omitted < lows.length + 1, slots = insertNone omitted lows) where
  actual := OneNone.actual
  bridge := Iff.rfl
  variation := ⟨@options_one_none, OneNone.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem options_one_none in OneNone.arena
  readout via (realize OneNone.signature (fun _ _ slots => slots.filterMap id) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "domain", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end OneNoneAudit

namespace EvenSlotsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.EvenSlots

theorem dependence : ObservationalDependence EvenSlots.signature actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenSlots.actual, EvenSlots.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ EvenSlots.arena.Law rejected := by
  intro h
  have h := @h 1
  change ([] : List (Option ℕ)) = [some 1] at h
  cases h

def registration : Registration EvenSlots.arena (∀ (m : ℕ),
    candidateSlots m 0 m = (List.range' 1 m).map some) where
  actual := EvenSlots.actual
  bridge := Iff.rfl
  variation := ⟨@candidateSlots_even, EvenSlots.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem candidateSlots_even in EvenSlots.arena
  readout via (realize EvenSlots.signature (fun _ _ m => candidateSlots m 0 m) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end EvenSlotsAudit

namespace OddSlotsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.OddSlots

theorem dependence : ObservationalDependence OddSlots.signature actual := by
  intro i
  refine ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [OddSlots.actual, OddSlots.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ OddSlots.arena.Law rejected := by
  intro h
  have h := @h 0 0 (by decide)
  change ([] : List (Option ℕ)) = [none] at h
  cases h

def registration : Registration OddSlots.arena (∀ (m omitted : ℕ) (homitted : omitted < m + 1),
    candidateSlots omitted 0 (m + 1) = insertNone omitted (List.range' 1 m)) where
  actual := OddSlots.actual
  bridge := Iff.rfl
  variation := ⟨@candidateSlots_odd, OddSlots.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem candidateSlots_odd in OddSlots.arena
  readout via (realize OddSlots.signature (fun _ (m : ℕ) omitted => candidateSlots omitted 0 (m + 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end OddSlotsAudit

namespace CandidateAssemblyAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.CandidateAssembly

theorem dependence : ObservationalDependence CandidateAssembly.signature actual := by
  intro i
  refine ⟨⟨(1 : ℕ), (2 : ℕ)⟩, (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [CandidateAssembly.actual, CandidateAssembly.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ CandidateAssembly.arena.Law rejected := by
  intro h
  have h := @h 0 1 0
  change ([] : List ℕ) = [1] at h
  cases h

def registration : Registration CandidateAssembly.arena (∀ (m highCount omitted : ℕ),
    candidate m highCount omitted =
      assembleGaps (List.range' (m + 1) highCount)
        (candidateSlots omitted 0 highCount)) where
  actual := CandidateAssembly.actual
  bridge := Iff.rfl
  variation := ⟨@candidate_eq_assemble, CandidateAssembly.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem candidate_eq_assemble in CandidateAssembly.arena
  readout via (realize CandidateAssembly.signature (fun _ p omitted => candidate p.1 p.2 omitted) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

end CandidateAssemblyAudit

namespace FilledSomeAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledSome

theorem dependence : ObservationalDependence FilledSome.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [FilledSome.actual, FilledSome.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ FilledSome.arena.Law rejected := by
  intro h
  have h := @h []
  cases h

def registration : Registration FilledSome.arena (∀ (lows : List ℕ),
    FilledUntilLast (lows.map some)) where
  actual := FilledSome.actual
  bridge := Iff.rfl
  variation := ⟨@filledUntilLast_map_some, FilledSome.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem filledUntilLast_map_some in FilledSome.arena
  readout via (realize FilledSome.signature (fun _ _ lows => lows.map some) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end FilledSomeAudit

namespace FilledLastAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FilledLast

theorem dependence : ObservationalDependence FilledLast.signature actual := by
  intro i
  refine ⟨(), [], [(0 : ℕ)], ?_⟩
  dsimp only [FilledLast.actual, FilledLast.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ FilledLast.arena.Law rejected := by
  intro h
  have h := @h []
  cases h

def registration : Registration FilledLast.arena (∀ (lows : List ℕ),
    FilledUntilLast (insertNone lows.length lows)) where
  actual := FilledLast.actual
  bridge := Iff.rfl
  variation := ⟨@filledUntilLast_insertNone_last, FilledLast.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem filledUntilLast_insertNone_last in FilledLast.arena
  readout via (realize FilledLast.signature (fun _ _ lows => insertNone lows.length lows) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end FilledLastAudit

namespace HighOrderAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighOrder

theorem dependence : ObservationalDependence HighOrder.signature actual := by
  intro i
  refine ⟨(0 : ℕ), [], [(1 : ℕ)], ?_⟩
  dsimp only [HighOrder.actual, HighOrder.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ HighOrder.arena.Law rejected := by
  intro h
  have h := @h 0 [] Gapped.nil FilledUntilLast.nil rfl
  have h := (List.pairwise_cons.mp h).1 0 (by simp)
  exact (Nat.not_lt_zero 1) h

def registration : Registration HighOrder.arena (∀ {n : ℕ} {input : List ℕ}
    (hgapped : Gapped (n / 2) input)
    (hfilled : FilledUntilLast (gapSlots (n / 2) input))
    (houtput : cyclicStackSort input = target n),
    (highEntries (n / 2) input).Pairwise (fun x y => x < y)) where
  actual := HighOrder.actual
  bridge := Iff.rfl
  variation := ⟨@successful_highs_of_filled_until_last, HighOrder.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem successful_highs_of_filled_until_last in HighOrder.arena
  readout via (realize HighOrder.signature (fun _ (n : ℕ) input => highEntries (n / 2) input) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

end HighOrderAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
