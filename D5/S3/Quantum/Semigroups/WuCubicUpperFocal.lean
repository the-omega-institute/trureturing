import D5.S3.Quantum.Semigroups.WuCubicUpperScalarCells
import D5.S3.Quantum.Semigroups.WuCubicUpperMatrixCells
import D5.S3.Quantum.Semigroups.WuCubicUpperRegion

/-! Exact leaf checks for the upper Wu cubic focal region. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicUpperFocal

open _root_.Matrix
open WuCubicAngularCertificate (normalizedDeficit)
open WuCubicDirectedOccupationCap (Mat)
open WuCubicHellingerMatrix (longTest weightSum signedMatrix)
open WuCubicThermalDerivatives (upperRoot)
open WuCubicUpperCornerJet
  (replayFocalY replayScalarMinus replayScalarPlus replayP0 replayP2 replayLong
    replayResidual)
open WuCubicUpperPartition (Box tree root)
open WuCubicUpperRegion (UpperRootTests offsetRadius)
open private padBox from D5.S3.Quantum.Semigroups.WuCubicUpperCornerJetRational

/-- Test the two scalar floors and the two signed matrices on a closed cell. -/
def cellCheck (b : Box) : Bool :=
  WuCubicUpperScalarCells.longTestCheck b (1 / 8) && WuCubicUpperMatrixCells.check b

/-- The accepted partition supplies the four tests needed by the physical bridge. -/
theorem upper_root_tests_of_check (hcheck : tree.check root cellCheck = true) :
    UpperRootTests := by
  intro z hz
  let x : Fin 4 → ℝ := fun i => z i.castSucc
  have hx : WuCubicUpperPartition.InBox root x := by
    intro i
    change ((upperRoot i).1 : ℝ) ≤ z i.castSucc ∧ z i.castSucc ≤ ((upperRoot i).2 : ℝ)
    have hi := hz i.castSucc
    change ((padBox upperRoot i.castSucc).1 : ℝ) ≤ z i.castSucc ∧
      z i.castSucc ≤ ((padBox upperRoot i.castSucc).2 : ℝ) at hi
    simpa only [padBox, Fin.lastCases_castSucc] using hi
  obtain ⟨b, hb, hxb⟩ := tree.covers root hx
  have hcell :
      (WuCubicUpperScalarCells.longTestCheck b (1 / 8) && WuCubicUpperMatrixCells.check b) =
        true :=
    List.all_eq_true.mp (show (tree.leaves root).all cellCheck = true from hcheck) b hb
  obtain ⟨hscalar, hmatrix⟩ := Bool.and_eq_true_iff.mp hcell
  obtain ⟨hfloor, hminus, hplus⟩ :=
    WuCubicUpperScalarCells.longTestCheck_sound (b := b) (floor := 1 / 8) hscalar hxb
  have hlongMinus : 0 < longTest (-1) (z 0) (replayFocalY z) := hfloor.trans_le hminus
  have hlongPlus : 0 < longTest 1 (z 0) (replayFocalY z) := hfloor.trans_le hplus
  have hm := WuCubicUpperMatrixCells.check_sound (b := b) hmatrix (x := x) hxb
  have hy : replayFocalY (Fin.lastCases 0 x) = replayFocalY z := rfl
  have hmMinus : (signedMatrix ((-1 : ℚ) : ℝ) (z 0)
      (replayFocalY (Fin.lastCases 0 x))).PosSemidef := hm.1.posSemidef
  have hmPlus : (signedMatrix ((1 : ℚ) : ℝ) (z 0)
      (replayFocalY (Fin.lastCases 0 x))).PosSemidef := hm.2.posSemidef
  rw [hy, Rat.cast_neg, Rat.cast_one] at hmMinus
  rw [hy, Rat.cast_one] at hmPlus
  refine ⟨?_, ?_, hmMinus, hmPlus⟩
  · simpa only [longTest, weightSum, neg_one_mul, sub_eq_add_neg, replayScalarMinus,
      replayLong, replayP0, replayP2, replayResidual, replayFocalY] using hlongMinus
  · simpa only [longTest, weightSum, one_mul, replayScalarPlus, replayLong,
      replayP0, replayP2, replayResidual, replayFocalY] using hlongPlus

/-- Checker acceptance also supplies the physical displacement margin. -/
theorem normalized_deficit_ge_of_check (hcheck : tree.check root cellCheck = true)
    (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n - r⁻¹ ≤ q - r⁻¹) (hq₁ : q - r⁻¹ ≤ 1 / 128)
    (hne : m ≠ (r ^ 2)⁻¹ ∨ n ≠ r⁻¹ ∨ q ≠ r⁻¹) :
    offsetRadius r m n q ^ 2 / 64 ≤ normalizedDeficit r U m n q :=
  WuCubicUpperRegion.normalized_deficit_ge (upper_root_tests_of_check hcheck)
    U hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁ hne

/-- Checker acceptance implies strict positivity at every non-Gibbs point. -/
theorem normalized_deficit_pos_of_check (hcheck : tree.check root cellCheck = true)
    (U : unitary Mat) {r m n q : ℝ}
    (hr₀ : 1049 / 1000 ≤ r) (hr₁ : r ≤ 6 / 5)
    (hm₀ : 0 ≤ m - (r ^ 2)⁻¹) (hm₁ : m - (r ^ 2)⁻¹ ≤ 1 / 256)
    (hn₀ : -(1 / 128) ≤ n - r⁻¹) (hnq : n - r⁻¹ ≤ q - r⁻¹) (hq₁ : q - r⁻¹ ≤ 1 / 128)
    (hne : m ≠ (r ^ 2)⁻¹ ∨ n ≠ r⁻¹ ∨ q ≠ r⁻¹) :
    0 < normalizedDeficit r U m n q :=
  WuCubicUpperRegion.normalized_deficit_pos (upper_root_tests_of_check hcheck)
    U hr₀ hr₁ hm₀ hm₁ hn₀ hnq hq₁ hne

run_cmd do
  for name in #[``normalized_deficit_ge_of_check, ``normalized_deficit_pos_of_check] do
    for axiomName in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom for {name}: {axiomName}"

private theorem first_leaf_accepted :
    cellCheck ((tree.leaves root).get ⟨0, by rw [WuCubicUpperPartition.leaf_count]; decide⟩) =
      true := by
  have hbox : (tree.leaves root).get ⟨0, by rw [WuCubicUpperPartition.leaf_count]; decide⟩ =
      WuCubicUpperScalarCells.firstUpperReplayCell := by
    funext i
    fin_cases i <;> decide +kernel
  rw [hbox]
  exact Bool.and_eq_true_iff.mpr
    ⟨WuCubicUpperScalarCells.firstUpperReplayCell_accepted,
      WuCubicUpperMatrixCells.firstLeaf_checked⟩

#print axioms first_leaf_accepted

end D5.S3.Quantum.Semigroups.WuCubicUpperFocal
