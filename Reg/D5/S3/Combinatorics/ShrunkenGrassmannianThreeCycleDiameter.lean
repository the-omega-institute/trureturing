import D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
open _root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ L N => ecc 3 L N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both original diameter readings and all three guards remain in the Law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ L N : ℕ, 2 ≤ L → L ≤ N → 3 < N →
    r.readout () L N = (L * (N - L) + 1) / 2 ∧
      diam 3 L N = (L * (N - L) + 1) / 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h 2 4 (by decide) (by decide) (by decide)).1
  change 0 = 2 at hzero
  contradiction

theorem dependence_proof : ObservationalDependence signature actual := by
  intro ⟨⟩
  refine ⟨2, 4, 5, ?_⟩
  change ecc 3 2 4 ≠ ecc 3 2 5
  rw [(_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
    2 4 (by decide) (by decide) (by decide)).1,
    (_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result
    2 5 (by decide) (by decide) (by decide)).1]
  decide

noncomputable def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result,
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
  _root_.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.result in arena
  readout via (realize signature (fun _ L N => ecc 3 L N) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
    «definition» := some {
      owner := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
      name := `D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter.claim }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
