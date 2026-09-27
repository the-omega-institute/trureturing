import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[], [], [(0 : ℕ)], ?_⟩
  change ([] : List ℕ) ≠ [0]
  simp

theorem rejected_run : ¬ runArena.Law rejected := by
  intro h
  have h := h [] [0]
  change ([] : List ℕ) = [0] at h
  cases h

theorem rejected_perm : ¬ permArena.Law rejected := by
  intro h
  have h := (h [] [0]).length_eq
  change (0 : ℕ) = 1 at h
  cases h

def runRegistration : Registration runArena (∀ input stack,
    process input stack = (run input stack).1 ++ (run input stack).2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨process_eq_run, rejected, rejected_run⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_run⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := dependence

def permRegistration : Registration permArena (∀ input stack,
    (process input stack).Perm (input ++ stack)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨process_perm, rejected, rejected_perm⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_perm⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := dependence

register_information_theorem process_eq_run in runArena
  readout via (realize signature (fun _ input stack => process input stack) (fun e => nomatch e))
  realizes runRegistration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

register_information_theorem process_perm in permArena
  readout via (realize signature (fun _ input stack => process input stack) (fun e => nomatch e))
  realizes permRegistration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

namespace AppendAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.Append

theorem dependence : ObservationalDependence Append.signature actual := by
  intro i
  refine ⟨⟨[], []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [Append.actual, Append.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ Append.arena.Law rejected := by
  intro h
  have h := @h [] [] [0]
  change ([] : List ℕ) = [0] at h
  cases h

def registration : Registration Append.arena (∀ (pre suffix stack : List ℕ),
    process (pre ++ suffix) stack =
      (run pre stack).1 ++ process suffix (run pre stack).2) where
  actual := Append.actual
  bridge := Iff.rfl
  variation := ⟨@process_append, Append.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem process_append in Append.arena
  readout via (realize Append.signature (fun _ p stack => process (p.1 ++ p.2) stack) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2 }] })
  escape continues (open)

end AppendAudit

namespace DrainLowAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainLow

theorem dependence : ObservationalDependence DrainLow.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainLow.actual, DrainLow.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainLow.arena.Law rejected := by
  intro h
  have h := @h 2 1 2 (by decide) (by decide) [] [] (by decide)
  change (([], []) : List ℕ × List ℕ) = ([], [2]) at h
  cases h

def registration : Registration DrainLow.arena (∀ {n low high : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low :: input) (high :: stack)).Sublist (target n)),
    drain low (high :: stack) = ([], high :: stack)) where
  actual := DrainLow.actual
  bridge := Iff.rfl
  variation := ⟨@drain_low_over_high, DrainLow.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem drain_low_over_high in DrainLow.arena
  readout via (realize DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6 }] })
  escape continues (open)

end DrainLowAudit

namespace TwoLowsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.TwoLows

theorem dependence : ObservationalDependence TwoLows.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [TwoLows.actual, TwoLows.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ TwoLows.arena.Law rejected := by
  intro h
  have h := @h 2 0 1 2 (by decide) (by decide) (by decide) (by decide) [] [] (List.nil_sublist _)
  exact h

def registration : Registration TwoLows.arena (∀ {n low₁ low₂ high : ℕ}
    (hlow₁ : low₁ ≤ n / 2) (hlow₂ : low₂ ≤ n / 2)
    (hne : low₁ ≠ low₂) (hhigh : n / 2 < high) {input stack : List ℕ}
    (houtput : (process (low₁ :: low₂ :: input) (high :: stack)).Sublist
      (target n)),
    False) where
  actual := TwoLows.actual
  bridge := Iff.rfl
  variation := ⟨@no_two_lows_after_high, TwoLows.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem no_two_lows_after_high in TwoLows.arena
  readout via (realize TwoLows.signature (fun _ p stack => process (p.1 :: p.2.1 :: p.2.2.2) (p.2.2.1 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2, 3, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 9 }] })
  escape continues (open)

end TwoLowsAudit

namespace HighIncreaseAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.HighIncrease

theorem dependence : ObservationalDependence HighIncrease.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [HighIncrease.actual, HighIncrease.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ HighIncrease.arena.Law rejected := by
  intro h
  have h := @h 0 0 1 1 (by decide) (by decide) [] [] (List.nil_sublist _)
  exact (Nat.lt_irrefl 1) h

def registration : Registration HighIncrease.arena (∀ {n low high next : ℕ}
    (hlow : low ≤ n / 2) (hnext : n / 2 < next)
    {input stack : List ℕ}
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    high < next) where
  actual := HighIncrease.actual
  bridge := Iff.rfl
  variation := ⟨@pending_low_forces_high_increase, HighIncrease.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem pending_low_forces_high_increase in HighIncrease.arena
  readout via (realize HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

end HighIncreaseAudit

namespace DrainHighAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainHigh

theorem dependence : ObservationalDependence DrainLow.signature DrainLow.actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainLow.actual, DrainLow.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainHigh.arena.Law DrainLow.rejected := by
  intro h
  have h := @h 4 4 3 1 (by decide) (by decide) [1] [] (by simp) (by decide)
  change (([], []) : List ℕ × List ℕ) = ([], [3]) at h
  cases h

def registration : Registration DrainHigh.arena (∀ {n x high futureLow : ℕ}
    (hhigh : n / 2 < high) (hlow : futureLow ≤ n / 2)
    {input stack : List ℕ} (hmem : futureLow ∈ input)
    (houtput : (process (x :: input) (high :: stack)).Sublist (target n)),
    drain x (high :: stack) = ([], high :: stack)) where
  actual := DrainLow.actual
  bridge := Iff.rfl
  variation := ⟨@drain_high_while_low_remains, DrainLow.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem drain_high_while_low_remains in DrainHigh.arena
  readout via (realize DrainLow.signature (fun _ p stack => drain p.1 (p.2 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

end DrainHighAudit

namespace DrainPendingAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.DrainPending

theorem dependence : ObservationalDependence DrainPending.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ)⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [DrainPending.actual, DrainPending.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ DrainPending.arena.Law rejected := by
  intro h
  have h := @h 4 1 3 4 2 (by decide) (by decide) (by decide) (by decide) [2] [] (by simp) (by decide)
  change (([], []) : List ℕ × List ℕ) = ([1], [3]) at h
  cases h

def registration : Registration DrainPending.arena (∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    drain next (low :: high :: stack) = ([low], high :: stack)) where
  actual := DrainPending.actual
  bridge := Iff.rfl
  variation := ⟨@pending_low_drains_only_low_while_low_remains, DrainPending.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem pending_low_drains_only_low_while_low_remains in DrainPending.arena
  readout via (realize DrainPending.signature (fun _ p stack => drain p.2.2 (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

end DrainPendingAudit

namespace ProcessPendingAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.ProcessPending

theorem dependence : ObservationalDependence HighIncrease.signature HighIncrease.actual := by
  intro i
  refine ⟨⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [HighIncrease.actual, HighIncrease.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ ProcessPending.arena.Law HighIncrease.rejected := by
  intro h
  have h := @h 4 1 3 4 2 (by decide) (by decide) (by decide) (by decide) [2] [] (by simp) (by decide)
  change ([] : List ℕ) = [1, 2, 4, 3] at h
  cases h

def registration : Registration ProcessPending.arena (∀
    {n low high next futureLow : ℕ}
    (hlow : low ≤ n / 2) (hhigh : n / 2 < high) (hnext : n / 2 < next)
    (hfutureLow : futureLow ≤ n / 2) {input stack : List ℕ}
    (hmem : futureLow ∈ input)
    (houtput : (process (next :: input) (low :: high :: stack)).Sublist
      (target n)),
    process (next :: input) (low :: high :: stack) =
      low :: process input (next :: high :: stack)) where
  actual := HighIncrease.actual
  bridge := Iff.rfl
  variation := ⟨@process_pending_low_while_low_remains, HighIncrease.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem process_pending_low_while_low_remains in ProcessPending.arena
  readout via (realize HighIncrease.signature (fun _ p stack => process (p.2.2.1 :: p.2.2.2) (p.1 :: p.2.1 :: stack)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2, 3, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10 }] })
  escape continues (open)

end ProcessPendingAudit

namespace InitialLowsAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.InitialLows

theorem dependence : ObservationalDependence InitialLows.signature actual := by
  intro i
  refine ⟨⟨(0 : ℕ), []⟩, [], [(0 : ℕ)], ?_⟩
  dsimp only [InitialLows.actual, InitialLows.signature, singleObservation, realize]
  decide

theorem rejected_law : ¬ InitialLows.arena.Law rejected := by
  intro h
  have h := @h 2 2 [1] [] (by simp) (by decide) rfl
  cases h

def registration : Registration InitialLows.arena (∀ {n high : ℕ} {pre rest : List ℕ}
    (hpre : ∀ low ∈ pre, low ≤ n / 2) (hhigh : n / 2 < high)
    (houtput : cyclicStackSort (pre ++ high :: rest) = target n),
    pre = []) where
  actual := InitialLows.actual
  bridge := Iff.rfl
  variation := ⟨@no_lows_before_first_high, InitialLows.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem no_lows_before_first_high in InitialLows.arena
  readout via (realize InitialLows.signature (fun _ p rest => cyclicStackSort (p.2 ++ p.1 :: rest)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

end InitialLowsAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
