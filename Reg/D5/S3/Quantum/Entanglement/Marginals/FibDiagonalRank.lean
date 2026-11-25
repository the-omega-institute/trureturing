import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank
import Reg.Support.DependentFamily

/-! Registration of the joint-rank readout for the diagonal criterion. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank

open LeanInformationAudit
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Word)
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension

noncomputable section

private abbrev Joint := Matrix Word Word ℂ

private abbrev signature : Signature where
  Params := Unit
  State _ := Joint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ T => T.rank) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (b l r : ℚ), 0 < b → 0 < l → 0 < r → l ≠ r →
    ((∃ z : ℂ, ∃ T : Joint, T.PosSemidef ∧
      MatchesCoherentData b (diagonalEdgeBlock b l) (diagonalEdgeBlock b r) 0 0 0 z T ∧
      R.readout () () T ≤ 2 ∧ ∀ i j, RationalEntry (T i j)) ↔
    (∃ z : ℂ, RationalEntry z ∧ Complex.normSq z = (b * (1 - b - l - r) : ℚ)) ∧
    (∃ w : ℂ, RationalEntry w ∧ Complex.normSq w = (l * r : ℚ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hnorm :
      (∃ z : ℂ, RationalEntry z ∧ Complex.normSq z =
        ((1 / 4 : ℚ) * (1 - 1 / 4 - 1 / 32 - 5 / 32) : ℚ)) ∧
      (∃ w : ℂ, RationalEntry w ∧ Complex.normSq w = ((1 / 32 : ℚ) * (5 / 32) : ℚ)) := by
    constructor
    · exact ⟨Complex.mk (3 / 8) 0, ⟨3 / 8, 0, by norm_num, by norm_num⟩,
        by norm_num [Complex.normSq_apply]⟩
    · exact ⟨Complex.mk (1 / 16) (1 / 32), ⟨1 / 16, 1 / 32, by norm_num, by norm_num⟩,
        by norm_num [Complex.normSq_apply]⟩
  obtain ⟨_, _, _, _, hrank, _⟩ :=
    (h (1 / 4) (1 / 32) (5 / 32) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).mpr hnorm
  exact (by decide : ¬ (3 : ℕ) ≤ 2) hrank

def family : Registration arena (type_of% @rational_rank_le_two_diagonal_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_rank_le_two_diagonal_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Joint).rank ≠ (1 : Joint).rank
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_rank_le_two_diagonal_iff) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank.rational_rank_le_two_diagonal_iff "audit"
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T.rank) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.FibDiagonalRank
