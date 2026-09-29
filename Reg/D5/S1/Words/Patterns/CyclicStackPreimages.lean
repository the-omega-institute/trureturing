import D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
import Reg.Support.CyclicStackFamily

namespace Reg.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S1.Words.Patterns.CyclicStackPreimages
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace FibreCountAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily.FibreCount

theorem dependence : ObservationalDependence EvenFibre.signature EvenFibre.actual := by
  intro i
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  dsimp only [EvenFibre.actual, EvenFibre.signature, singleObservation, realize]
  exact _root_.Reg.Support.CyclicStackFamily.fibre_distinct_of_member
    (m := 0) (n := 2) (word := [])
    (List.mem_filter.mpr ⟨List.mem_permutations.mpr (List.Perm.refl []), rfl⟩)
    (by decide)

theorem rejected_law : ¬ FibreCount.arena.Law EvenFibre.rejected := by
  intro h
  have h := @h 2 (by decide)
  have h := h.1
  change (0 : ℕ) = 1 at h
  cases h

def registration : Registration FibreCount.arena (∀ (m : ℕ) (hm : 2 ≤ m),
    (fibre (2 * m)).length = 1 ∧ (fibre (2 * m + 1)).length = m + 1) where
  actual := EvenFibre.actual
  bridge := Iff.rfl
  variation := ⟨@zhan_bie_conjectures_3_4, EvenFibre.rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.CyclicStackFamily.singleSensitivity _ _ _ rejected_law
  dependence := dependence

register_information_theorem zhan_bie_conjectures_3_4 in FibreCount.arena
  readout via (realize EvenFibre.signature (fun _ _ (m : ℕ) => fibre (2 * m)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S1.Words.Patterns.CyclicStackPreimages
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

end FibreCountAudit

end Reg.D5.S1.Words.Patterns.CyclicStackPreimages
