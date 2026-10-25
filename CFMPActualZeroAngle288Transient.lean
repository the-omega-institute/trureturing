import CFMPActualNormalizedFlat287Transient
import Mathlib.Analysis.Normed.Order.Lattice
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalPhysicalEdge237Transient (sourceCosine sourceAngle)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open CFMPActualExtendedAngle268Transient (positiveLengths)
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (rad numerator cosine)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open private frame_properties from D5.S3.Geometry.Hyperideal.PositiveFlatClassification

namespace CFMPActualZeroAngle288Transient

/-- The original radicand remains strictly positive when a length vanishes. -/
theorem rad_positive_closed (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    0 < rad x y z := by
  have hx2 : 1 ≤ x^2 := by nlinarith [sq_nonneg (x-1)]
  have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
  have hz2 : 1 ≤ z^2 := by nlinarith [sq_nonneg (z-1)]
  have hp : 0 ≤ 2*x*y*z := by positivity
  unfold rad
  linarith

/-- Continuity here concerns the raw cosh formula, including signed inputs. -/
theorem sourceCosine_continuous (q : Fin 6) :
    Continuous (fun a : Lengths => sourceCosine a q) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hleft : 0 < rad (Real.cosh (a (frame q 0)))
      (Real.cosh (a (frame q 1))) (Real.cosh (a (frame q 5))) :=
    rad_positive_closed _ _ _ (Real.one_le_cosh _) (Real.one_le_cosh _) (Real.one_le_cosh _)
  have hright : 0 < rad (Real.cosh (a (frame q 0)))
      (Real.cosh (a (frame q 2))) (Real.cosh (a (frame q 4))) :=
    rad_positive_closed _ _ _ (Real.one_le_cosh _) (Real.one_le_cosh _) (Real.one_le_cosh _)
  have hn : Continuous (fun p : Lengths =>
      numerator (Real.cosh (p (frame q 0))) (Real.cosh (p (frame q 1)))
        (Real.cosh (p (frame q 2))) (Real.cosh (p (frame q 3)))
        (Real.cosh (p (frame q 4))) (Real.cosh (p (frame q 5)))) := by
    unfold numerator
    fun_prop
  have hL : Continuous (fun p : Lengths =>
      Real.sqrt (rad (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 1))) (Real.cosh (p (frame q 5))))) := by
    unfold rad
    fun_prop
  have hR : Continuous (fun p : Lengths =>
      Real.sqrt (rad (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 2))) (Real.cosh (p (frame q 4))))) := by
    unfold rad
    fun_prop
  exact (hn.continuousAt.div hL.continuousAt (Real.sqrt_pos.mpr hleft).ne').div
    hR.continuousAt (Real.sqrt_pos.mpr hright).ne'

theorem sourceAngle_continuous (q : Fin 6) :
    Continuous (fun a : Lengths => sourceAngle a q) :=
  Real.continuous_arccos.comp (sourceCosine_continuous q)

theorem sourceDifferential_continuous : Continuous sourceDifferential := by
  unfold sourceDifferential
  apply continuous_finsetSum
  intro q _
  exact (sourceAngle_continuous q).smul continuous_const

/-- At target cosh-length one both positive square roots cancel the numerator. -/
theorem cosine_target_one (y z o v w : ℝ)
    (hy : 1 ≤ y) (hz : 1 ≤ z) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    cosine 1 y z o v w = 1 := by
  have hyw : 0 < y+w := by linarith
  have hzv : 0 < z+v := by linarith
  have hL : rad 1 y w = (y+w)^2 := by unfold rad; ring
  have hR : rad 1 z v = (z+v)^2 := by unfold rad; ring
  have hn : numerator 1 y z o v w = (y+w)*(z+v) := by unfold numerator; ring
  rw [cosine,hn,hL,hR,Real.sqrt_sq hyw.le,Real.sqrt_sq hzv.le]
  field_simp

theorem sourceCosine_eq_one_of_zero (a : Lengths) (q : Fin 6) (hq : a q = 0) :
    sourceCosine a q = 1 := by
  have hframe : frame q 0 = q := (frame_properties q).1
  change cosine (Real.cosh (a (frame q 0))) (Real.cosh (a (frame q 1)))
    (Real.cosh (a (frame q 2))) (Real.cosh (a (frame q 3)))
    (Real.cosh (a (frame q 4))) (Real.cosh (a (frame q 5))) = 1
  rw [hframe,hq,Real.cosh_zero]
  exact cosine_target_one _ _ _ _ _
    (Real.one_le_cosh _) (Real.one_le_cosh _) (Real.one_le_cosh _) (Real.one_le_cosh _)

theorem sourceAngle_eq_zero_of_zero (a : Lengths) (q : Fin 6) (hq : a q = 0) :
    sourceAngle a q = 0 := by
  simp only [sourceAngle,sourceCosine_eq_one_of_zero a q hq,Real.arccos_one]

/-- Signed lengths are first truncated, as in the generalized angle field. -/
def positivePart (a : Lengths) : Lengths := fun q => max 0 (a q)

def extendedAngle (a : Lengths) (q : Fin 6) : ℝ := sourceAngle (positivePart a) q

def extendedDifferential (a : Lengths) : Lengths →L[ℝ] ℝ :=
  sourceDifferential (positivePart a)

theorem positivePart_continuous : Continuous positivePart := by
  apply continuous_pi
  intro q
  exact continuous_const.max (continuous_apply q)

theorem positivePart_eq_self (a : Lengths) (ha : ∀ q, 0 ≤ a q) : positivePart a = a := by
  funext q
  exact max_eq_right (ha q)

theorem extendedAngle_continuous (q : Fin 6) : Continuous (fun a => extendedAngle a q) :=
  (sourceAngle_continuous q).comp positivePart_continuous

theorem extendedDifferential_continuous : Continuous extendedDifferential :=
  sourceDifferential_continuous.comp positivePart_continuous

theorem extendedAngle_zero_of_nonpos (a : Lengths) (q : Fin 6) (hq : a q ≤ 0) :
    extendedAngle a q = 0 := by
  exact sourceAngle_eq_zero_of_zero _ q (max_eq_left hq)

theorem extendedAngle_bounds (a : Lengths) (q : Fin 6) :
    0 ≤ extendedAngle a q ∧ extendedAngle a q ≤ Real.pi :=
  ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩

theorem sourceDifferential_norm_le (a : Lengths) : ‖sourceDifferential a‖ ≤ 6*Real.pi := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [sourceDifferential_apply]
  calc
    ‖∑ q : Fin 6, sourceAngle a q * v q‖ ≤
        ∑ q : Fin 6, ‖sourceAngle a q * v q‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin 6, Real.pi * ‖v‖ := by
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ sourceAngle a q from Real.arccos_nonneg _)]
      exact mul_le_mul (Real.arccos_le_pi _) (norm_le_pi_norm v q)
        (norm_nonneg _) Real.pi_pos.le
    _ = (6*Real.pi)*‖v‖ := by simp; ring

theorem extendedDifferential_norm_le (a : Lengths) :
    ‖extendedDifferential a‖ ≤ 6*Real.pi := sourceDifferential_norm_le _

theorem extendedDifferential_apply (a v : Lengths) :
    extendedDifferential a v = ∑ q : Fin 6, extendedAngle a q * v q :=
  sourceDifferential_apply _ _

end CFMPActualZeroAngle288Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualZeroAngle288Transient.sourceCosine_continuous,
      ``CFMPActualZeroAngle288Transient.sourceCosine_eq_one_of_zero,
      ``CFMPActualZeroAngle288Transient.sourceAngle_eq_zero_of_zero,
      ``CFMPActualZeroAngle288Transient.extendedAngle_zero_of_nonpos,
      ``CFMPActualZeroAngle288Transient.extendedDifferential_continuous,
      ``CFMPActualZeroAngle288Transient.extendedDifferential_norm_le] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP288 zero-boundary angle interface absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP288 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP288 CHECKED {name} axioms={axioms}"
