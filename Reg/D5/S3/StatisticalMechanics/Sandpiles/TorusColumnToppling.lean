import D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
open _root_.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a023855 (n - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 2 ≤ n →
    (∃ L : List (Cell n 1), Legal L ∧ Stable (run L)) ∧
      ∀ L : List (Cell n 1), Legal L → Stable (run L) → L.length = r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have original := _root_.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling.result 2
    (by norm_num)
  obtain ⟨L, hL, hstable⟩ := original.1
  have hlength := original.2 L hL hstable
  have hzero := (h 2 (by norm_num)).2 L hL hstable
  change L.length = 0 at hzero
  norm_num [a023855] at hlength
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 2, 3, ?_⟩
  change a023855 (2 - 1) ≠ a023855 (3 - 1)
  norm_num [a023855]

def registration : Registration arena (_root_.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling.result in arena
  readout via (realize signature (fun _ _ n => a023855 (n - 1)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
    «definition» := some {
      owner := `D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
      name := `D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling.claim }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
