import D5.S3.Constants.Billiards.CollidingBlocksRecords
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

open LeanInformationAudit Real
noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords
open _root_.D5.S3.Constants.Billiards.CollidingBlocksRecords

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 1 ≤ n →
    r.readout () () n ≠ ⌊π * √(n : ℝ)⌋ →
      ∀ k : ℕ, 1 ≤ k → k < n → r.readout () () k < r.readout () () n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfloor : (0 : ℤ) < ⌊π * √(2 : ℝ)⌋ := by
    rw [Int.floor_pos]
    have hs : (1 : ℝ) ≤ √2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.pi_gt_three,
      mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.mpr hs)]
  have hbad := h 2 (by norm_num) (by change (0 : ℤ) ≠ ⌊π * √(2 : ℝ)⌋; omega) 1 (by norm_num) (by norm_num)
  change (0 : ℤ) < 0 at hbad
  exact (lt_irrefl _ hbad)

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  change a 0 ≠ a 1
  have ha0 : a 0 = -1 := by simp [a]
  have ha1 : a 1 = 3 := by
    simp [a, Real.arctan_one]
  omega

def registration : Registration arena (_root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.result,
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
  _root_.D5.S3.Constants.Billiards.CollidingBlocksRecords.result in arena
  readout via (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords
    «definition» := some {
      owner := `D5.S3.Constants.Billiards.CollidingBlocksRecords
      name := `D5.S3.Constants.Billiards.CollidingBlocksRecords.claim }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords
