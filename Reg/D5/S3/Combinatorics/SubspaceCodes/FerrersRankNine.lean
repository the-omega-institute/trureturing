import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ZMod

/-! # Source readout for the attained rank in the Ferrers example -/

namespace Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine

open _root_.D5.S3.Combinatorics.SubspaceCodes
open _root_.D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := Sigma fun F : Type => Field F
  State p := Mat p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def attainedRank (_ : Unit) (p : signature.Params) (M : Mat p.1) : ℕ :=
  letI := p.2
  M.rank

private def actual : Realization signature :=
  realize signature attainedRank (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : Type) [f : Field F] [Fintype F],
    Odd (Fintype.card F) → 3 < Fintype.card F →
      (∃ C : Submodule F (Mat F), Supported C ∧ Module.finrank F C = 27 ∧
        MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 C ∧
        ∃ M ∈ C, M ≠ 0 ∧ r.readout () ⟨F, f⟩ M = 9) ∧
      (∀ D : Submodule F (Mat F), Supported D →
        MRDDensityColumnReduction.MinDistanceAtLeast F 12 12 9 D → Module.finrank F D ≤ 27)

private theorem rejected_law : ¬ arena.Law rejected := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h
  have h5 : Fintype.card (ZMod 5) = 5 := ZMod.card 5
  obtain ⟨C, _, _, _, M, _, _, hm⟩ :=
    (h (ZMod 5) (by rw [h5]; decide) (by rw [h5]; decide)).1
  exact (by decide : (0 : ℕ) ≠ 9) hm

def source_registration : Registration arena Problem1RankNine where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨problem1_rank_nine, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    intro i
    cases i
    refine ⟨⟨ZMod 5, inferInstance⟩, (0 : Mat (ZMod 5)), (1 : Mat (ZMod 5)), ?_⟩
    change (0 : Mat (ZMod 5)).rank ≠ (1 : Mat (ZMod 5)).rank
    rw [Matrix.rank_zero, Matrix.rank_one]
    decide

def problem1RankNine :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      problem1_rank_nine (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine.problem1RankNine.unit
  realizationName := `Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature attainedRank (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
    definition := some {
      owner := `D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
      name := `D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine.Problem1RankNine
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "body",
        "arg", "arg", "arg", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

#print axioms problem1RankNine

end
end Reg.D5.S3.Combinatorics.SubspaceCodes.FerrersRankNine
