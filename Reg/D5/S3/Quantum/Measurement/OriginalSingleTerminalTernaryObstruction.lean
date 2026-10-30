import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction
import Reg.Support.DependentFamily

/-! # Source-bound dyadic-weight audit

The source law retains the complete original theorem telescope. The selected
readout is the dyadic weight of an actual word. Nonemptiness of the original
Source carrier is required to close the whole-family intervention evidence.
-/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction

open _root_.D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction
open _root_.D5.S3.Quantum.Tomography.RankOneContextCommutator
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ word => alpha word) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (S : Source) (Mark : Type),
    ((preparation S).PosSemidef ∧ Matrix.trace (preparation S) = 1) ∧
    (∀ t : CausalTree Mark,
      (∑ l : t.Leaf, R.readout () () (t.word l)) = 1 ∧
      ∀ l : t.Leaf,
        0 < R.readout () () (t.word l) ∧
        R.readout () () (t.word l) = ((2 : ℝ) ^ jcount (t.word l))⁻¹ ∧
        IsNormalizedRankOneProjection (leafProjection S t l) ∧
        ∀ X : Mat,
          leafRun S t l X = R.readout () () (t.word l) •
            ((wordUnitary S (t.word l) : Mat) * X *
              star (wordUnitary S (t.word l) : Mat)) ∧
          (∀ b : Bool, leafProbability S t X l b = R.readout () () (t.word l) *
            (Matrix.trace ((if b then leafProjection S t l else
              1 - leafProjection S t l) * X)).re) ∧
          (∀ b : Bool, liftedProbability S t X l b = leafProbability S t X l b) ∧
          (X.PosSemidef → Matrix.trace X = 1 →
            (∀ b : Bool, 0 ≤ leafProbability S t X l b) ∧
              (∑ b : Bool, leafProbability S t X l b) = R.readout () () (t.word l))) ∧
    (∀ (t : CausalTree Mark) (c : Stochastic t),
      IsPOVM (effects S t c) ∧
      (∀ (X : Mat) (a : Fin 3),
        postProbability S t c X a = (Matrix.trace (effects S t c a * X)).re) ∧
      (∀ X : Mat, X.PosSemidef → Matrix.trace X = 1 →
        (∀ a, 0 ≤ postProbability S t c X a) ∧ ∑ a, postProbability S t c X a = 1) ∧
      ∀ B : RankOneContext 3, BasisObstruction B (effects S t c)) ∧
    (∀ B : RankOneContext 3,
      Continuous (score B) ∧
      (∀ (M L : Tuple) (a b : ℝ),
        score B (a • M + b • L) = a * score B M + b * score B L) ∧
      Convex ℝ {M : Tuple | score B M ≤ 2 / 3} ∧
      IsClosed {M : Tuple | score B M ≤ 2 / 3} ∧
      (∀ M ∈ convexHull ℝ (operationalImage S Mark),
        IsPOVM M ∧ BasisObstruction B M) ∧
      (∀ M ∈ closure (convexHull ℝ (operationalImage S Mark)),
        IsPOVM M ∧ BasisObstruction B M) ∧
      ∀ M : Tuple, maxDistance B M = ‖M - B.projector‖) ∧
    (∀ X : Mat, ‖X‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖) ∧
    (∀ (checkpoint : ℕ → Bool) (stop : List Letter → Bool)
      (mark : List Letter → Mark) (actions : List Action) (past : List Letter)
      (c : Stochastic (fixedStoppingTree checkpoint stop mark actions past)),
      effects S (fixedStoppingTree checkpoint stop mark actions past) c ∈
        operationalImage S Mark)

private theorem rejected_law (hSource : Nonempty Source) : ¬ arena.Law rejected := by
  intro h
  obtain ⟨S⟩ := hSource
  have hz := ((h S Unit).2.1 (CausalTree.stop ())).1
  norm_num [rejected, realize] at hz

/-- The complete source-law bridge and whole-family intervention evidence,
conditional on a witness for the original source domain. -/
def familyOfNonemptySource (hSource : Nonempty Source) : Registration arena
    (type_of% (@complete_original_single_terminal_ternary_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_original_single_terminal_ternary_obstruction,
    rejected, rejected_law hSource⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim (α := Unit) j i)).elim,
        rfl, rejected_law hSource⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), [], [.j false], ?_⟩
    change alpha [] ≠ alpha [.j false]
    norm_num [alpha, jcount]

#print axioms familyOfNonemptySource

/- The audit remains unfinished: a closed Source nonemptiness witness, source
occurrence selection and current typed binding evidence are absent.
https://github.com/the-omega-institute/trureturing/issues/22279 -/

end Reg.D5.S3.Quantum.Measurement.OriginalSingleTerminalTernaryObstruction
