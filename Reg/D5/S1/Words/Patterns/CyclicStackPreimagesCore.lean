import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[], [], [0], ?_⟩
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
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1 }] })
  escape continues (open)

register_information_theorem process_perm in permArena
  readout via (realize signature (fun _ input stack => process input stack) (fun e => nomatch e))
  realizes permRegistration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimagesCore
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1 }] })
  escape continues (open)

end Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
