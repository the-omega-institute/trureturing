import CFMPActualExtendedAngle268Transient
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (rad numerator cosine)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rad_positive)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)

namespace CFMPActualFlatGraph269Transient

/-- The opposite cosh coordinate at which the original cosine first reaches -1.
The five inputs are the other coordinates in their original frame order. -/
def flatThreshold (u : Fin 5 → ℝ) : ℝ :=
  (u 1 * u 2 + u 3 * u 4 + u 0 * u 1 * u 3 + u 0 * u 2 * u 4 +
    Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3))) / (u 0 ^ 2 - 1)

def lengthThreshold (u : Fin 5 → ℝ) : ℝ :=
  Real.arcosh (flatThreshold (fun j => Real.cosh (u j)))

def fiveCoordinates (a : Lengths) (q : Fin 6) : Fin 5 → ℝ :=
  ![a (frame q 0), a (frame q 1), a (frame q 2), a (frame q 4), a (frame q 5)]

theorem flatThreshold_gt_one (u : Fin 5 → ℝ) (hu : ∀ j, 1 < u j) :
    1 < flatThreshold u := by
  have hp (j : Fin 5) : 0 < u j := lt_trans (by norm_num) (hu j)
  have hp0 : 0 < u 0 := hp 0
  have hp1 : 0 < u 1 := hp 1
  have hp2 : 0 < u 2 := hp 2
  have hp3 : 0 < u 3 := hp 3
  have hp4 : 0 < u 4 := hp 4
  have hA : 0 < u 0 ^ 2 - 1 := by nlinarith [hu 0]
  have hL : u 0 ^ 2 - 1 < rad (u 0) (u 1) (u 4) := by
    have hm : 0 < 2 * u 0 * u 1 * u 4 := by positivity
    dsimp only [rad]
    nlinarith [sq_nonneg (u 1), sq_nonneg (u 4)]
  have hR : u 0 ^ 2 - 1 < rad (u 0) (u 2) (u 3) := by
    have hm : 0 < 2 * u 0 * u 2 * u 3 := by positivity
    dsimp only [rad]
    nlinarith [sq_nonneg (u 2), sq_nonneg (u 3)]
  have hL0 := hA.trans hL
  have hR0 := hA.trans hR
  have hprod : (u 0 ^ 2 - 1) * (u 0 ^ 2 - 1) <
      rad (u 0) (u 1) (u 4) * rad (u 0) (u 2) (u 3) := by
    exact (mul_lt_mul_of_pos_right hL hA).trans
      (mul_lt_mul_of_pos_left hR hL0)
  have hsq : (Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3))) ^ 2 =
      rad (u 0) (u 1) (u 4) * rad (u 0) (u 2) (u 3) := by
    rw [mul_pow, Real.sq_sqrt hL0.le, Real.sq_sqrt hR0.le]
  have hD0 : 0 < Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3)) :=
    mul_pos (Real.sqrt_pos.mpr hL0) (Real.sqrt_pos.mpr hR0)
  have hD : u 0 ^ 2 - 1 < Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3)) := by
    nlinarith
  have hS : 0 < u 1 * u 2 + u 3 * u 4 + u 0 * u 1 * u 3 +
      u 0 * u 2 * u 4 := by positivity
  rw [flatThreshold, one_lt_div₀ hA]
  linarith

/-- An exact graph, not merely an implicit-function existence assertion. -/
theorem cosine_flat_iff (u : Fin 5 → ℝ) (hu : ∀ j, 1 < u j) (o : ℝ) :
    cosine (u 0) (u 1) (u 2) o (u 3) (u 4) ≤ -1 ↔
      flatThreshold u ≤ o := by
  have hA : 0 < u 0 ^ 2 - 1 := by nlinarith [hu 0]
  have hD : 0 < Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3)) :=
    mul_pos (Real.sqrt_pos.mpr (rad_positive _ _ _ (hu 0) (hu 1) (hu 4)))
      (Real.sqrt_pos.mpr (rad_positive _ _ _ (hu 0) (hu 2) (hu 3)))
  rw [cosine, div_div, div_le_iff₀ hD, flatThreshold, div_le_iff₀ hA]
  unfold numerator
  constructor <;> intro h <;> nlinarith

theorem cosine_interface_iff (u : Fin 5 → ℝ) (hu : ∀ j, 1 < u j) (o : ℝ) :
    cosine (u 0) (u 1) (u 2) o (u 3) (u 4) = -1 ↔
      o = flatThreshold u := by
  have hA : 0 < u 0 ^ 2 - 1 := by nlinarith [hu 0]
  have hD : 0 < Real.sqrt (rad (u 0) (u 1) (u 4)) *
      Real.sqrt (rad (u 0) (u 2) (u 3)) :=
    mul_pos (Real.sqrt_pos.mpr (rad_positive _ _ _ (hu 0) (hu 1) (hu 4)))
      (Real.sqrt_pos.mpr (rad_positive _ _ _ (hu 0) (hu 2) (hu 3)))
  rw [cosine, div_div, div_eq_iff hD.ne', flatThreshold, eq_div_iff hA.ne']
  unfold numerator
  constructor <;> intro h <;> nlinarith

theorem flatThreshold_contDiffAt (u : Fin 5 → ℝ) (hu : ∀ j, 1 < u j) :
    ContDiffAt ℝ ∞ flatThreshold u := by
  have hS : ContDiff ℝ ∞ (fun p : Fin 5 → ℝ =>
      p 1 * p 2 + p 3 * p 4 + p 0 * p 1 * p 3 + p 0 * p 2 * p 4) := by
    fun_prop
  have hL : ContDiff ℝ ∞ (fun p : Fin 5 → ℝ => rad (p 0) (p 1) (p 4)) := by
    unfold rad
    fun_prop
  have hR : ContDiff ℝ ∞ (fun p : Fin 5 → ℝ => rad (p 0) (p 2) (p 3)) := by
    unfold rad
    fun_prop
  have hA : ContDiff ℝ ∞ (fun p : Fin 5 → ℝ => p 0 ^ 2 - 1) := by
    fun_prop
  exact (hS.contDiffAt.add ((hL.contDiffAt.sqrt
    (rad_positive _ _ _ (hu 0) (hu 1) (hu 4)).ne').mul
    (hR.contDiffAt.sqrt (rad_positive _ _ _ (hu 0) (hu 2) (hu 3)).ne'))).div
    hA.contDiffAt (by nlinarith [hu 0])

theorem lengthThreshold_pos (u : Fin 5 → ℝ) (hu : ∀ j, 0 < u j) :
    0 < lengthThreshold u :=
  Real.arcosh_pos (flatThreshold_gt_one _ (fun j => Real.one_lt_cosh.mpr (hu j).ne'))

theorem lengthThreshold_contDiffAt (u : Fin 5 → ℝ) (hu : ∀ j, 0 < u j) :
    ContDiffAt ℝ ∞ lengthThreshold u := by
  have hc : ContDiff ℝ ∞ (fun p : Fin 5 → ℝ => fun j => Real.cosh (p j)) := by
    fun_prop
  have ht := (flatThreshold_contDiffAt (fun j => Real.cosh (u j))
    (fun j => Real.one_lt_cosh.mpr (hu j).ne')).comp u hc.contDiffAt
  exact (Real.contDiffAt_arcosh (flatThreshold_gt_one _
    (fun j => Real.one_lt_cosh.mpr (hu j).ne'))).comp u ht

theorem positive_length_flat_iff (u : Fin 5 → ℝ) (hu : ∀ j, 0 < u j)
    (o : ℝ) (ho : 0 < o) :
    cosine (Real.cosh (u 0)) (Real.cosh (u 1)) (Real.cosh (u 2))
      (Real.cosh o) (Real.cosh (u 3)) (Real.cosh (u 4)) ≤ -1 ↔
      lengthThreshold u ≤ o := by
  rw [cosine_flat_iff _ (fun j => Real.one_lt_cosh.mpr (hu j).ne')]
  have ht := flatThreshold_gt_one (fun j => Real.cosh (u j))
    (fun j => Real.one_lt_cosh.mpr (hu j).ne')
  have heq : Real.cosh (lengthThreshold u) =
      flatThreshold (fun j => Real.cosh (u j)) := Real.cosh_arcosh ht.le
  rw [← heq, Real.cosh_le_cosh, abs_of_pos (lengthThreshold_pos u hu), abs_of_pos ho]

/-- Each native closed sector is the epigraph of this explicit smooth graph
over its other five original length coordinates. -/
theorem source_sector_graph (a : Lengths) (ha : ∀ j, 0 < a j) (k : Fin 3) :
    D5.S3.Geometry.Hyperideal.PositiveFlatClassification.Sector
      (fun q => Real.cosh (a q)) k ↔
      lengthThreshold (fiveCoordinates a (k.castAdd 3)) ≤
        a (frame (k.castAdd 3) 3) := by
  have hu : ∀ j, 0 < fiveCoordinates a (k.castAdd 3) j := by
    intro j
    fin_cases j <;> exact ha _
  exact positive_length_flat_iff (fiveCoordinates a (k.castAdd 3)) hu
    (a (frame (k.castAdd 3) 3)) (ha _)

end CFMPActualFlatGraph269Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualFlatGraph269Transient.flatThreshold_gt_one,
      ``CFMPActualFlatGraph269Transient.cosine_flat_iff,
      ``CFMPActualFlatGraph269Transient.cosine_interface_iff,
      ``CFMPActualFlatGraph269Transient.flatThreshold_contDiffAt,
      ``CFMPActualFlatGraph269Transient.lengthThreshold_contDiffAt,
      ``CFMPActualFlatGraph269Transient.positive_length_flat_iff,
      ``CFMPActualFlatGraph269Transient.source_sector_graph] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP269 original flat-interface graph absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP269 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP269 CHECKED {name} axioms={axioms}"
