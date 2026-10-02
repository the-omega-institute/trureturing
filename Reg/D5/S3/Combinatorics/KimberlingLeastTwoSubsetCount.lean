import D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
open _root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ n => oeisSequence n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := subsetCount 0 = 0 ∧ subsetCount 1 = 0 ∧ subsetCount 2 = 0 ∧
    ∀ n : ℕ, subsetCount (n + 3) = r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood : subsetCount 3 = 1 := by
    have h0 := result.2.2.2 0
    simpa [oeisSequence] using h0
  have hbad := h.2.2.2 0
  change subsetCount 3 = 0 at hbad
  omega

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨(), 0, 1, ?_⟩
  change oeisSequence 0 ≠ oeisSequence 1
  norm_num [oeisSequence]

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result,
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
  _root_.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.result in arena
  readout via (realize signature (fun _ _ n => oeisSequence n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
    «definition» := some {
      owner := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
      name := `D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount.claim }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.KimberlingLeastTwoSubsetCount
