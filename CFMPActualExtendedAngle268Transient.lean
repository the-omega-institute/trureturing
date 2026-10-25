import CFMPActualPrimitiveCalibration267Transient
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Sector)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (extendedAngle rawCos)

namespace CFMPActualExtendedAngle268Transient

def positiveLengths : Set Lengths := {a | ∀ q, 0 < a q}

def flatDifferential (k : Fin 3) : Lengths →L[ℝ] ℝ :=
  Real.pi • ((ContinuousLinearMap.proj (k.castAdd 3) : Lengths →L[ℝ] ℝ) +
    ContinuousLinearMap.proj (k.natAdd 3))

def flatPrimitive (k : Fin 3) (a : Lengths) : ℝ :=
  Real.pi * (a (k.castAdd 3) + a (k.natAdd 3))

private theorem arccos_clip (x : ℝ) :
    Real.arccos (max (-1) (min x 1)) = Real.arccos x := by
  by_cases hlo : x ≤ -1
  · rw [min_eq_left (hlo.trans (by norm_num)), max_eq_left hlo,
      Real.arccos_neg_one, Real.arccos_of_le_neg_one hlo]
  · by_cases hhi : 1 ≤ x
    · rw [min_eq_right hhi, max_eq_right (by norm_num), Real.arccos_one,
        Real.arccos_of_one_le hhi]
    · rw [min_eq_left (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]

theorem sourceAngle_eq_extendedAngle (a : Lengths) (q : Fin 6) :
    sourceAngle a q = extendedAngle (fun j => Real.cosh (a j)) q := by
  exact (arccos_clip (rawCos (fun j => Real.cosh (a j)) q)).symm

theorem positiveLengths_open : IsOpen positiveLengths := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  exact Filter.eventually_all.mpr (fun q =>
    (continuous_apply q).continuousAt.eventually (Ioi_mem_nhds (ha q)))

/-- The covector already used for actual physical covolume is continuous even
at flat interfaces, as long as all six original lengths stay positive. -/
theorem sourceDifferential_continuousOn_positive :
    ContinuousOn sourceDifferential positiveLengths := by
  unfold sourceDifferential
  apply continuousOn_finsetSum
  intro q _
  have hangle : ContinuousOn (fun a : Lengths => sourceAngle a q) positiveLengths := by
    intro a ha
    exact (Real.continuous_arccos.continuousAt.comp
      (CFMPGenuineLengthNeighborhood435Transient.sourceCosine_continuousAt
        a ha q)).continuousWithinAt
  exact hangle.smul continuousOn_const

theorem sourceDifferential_continuousAt_positive (a : Lengths)
    (ha : a ∈ positiveLengths) : ContinuousAt sourceDifferential a :=
  (sourceDifferential_continuousOn_positive a ha).continuousAt
    (positiveLengths_open.mem_nhds ha)

/-- This includes the closed flat-sector boundary and uses six unordered edges. -/
theorem flat_sourceAngle (a : Lengths) (ha : a ∈ positiveLengths) (k : Fin 3)
    (hk : Sector (fun q => Real.cosh (a q)) k) (q : Fin 6) :
    sourceAngle a q =
      if q = k.castAdd 3 ∨ q = k.natAdd 3 then Real.pi else 0 := by
  rw [sourceAngle_eq_extendedAngle]
  exact ((D5.S3.Geometry.Hyperideal.PositiveFlatClassification.positive_classification
    (fun j => Real.cosh (a j))
    (fun j => Real.one_lt_cosh.mpr (ha j).ne')).2.2 k).2.mp hk q

theorem sourceDifferential_eq_flat (a : Lengths) (ha : a ∈ positiveLengths)
    (k : Fin 3) (hk : Sector (fun q => Real.cosh (a q)) k) :
    sourceDifferential a = flatDifferential k := by
  ext v
  rw [sourceDifferential_apply]
  simp only [flat_sourceAngle a ha k hk]
  fin_cases k <;> simp [flatDifferential, Fin.sum_univ_succ] <;> ring

theorem flatPrimitive_hasFDerivAt (k : Fin 3) (a : Lengths) :
    HasFDerivAt (flatPrimitive k) (flatDifferential k) a := by
  have heq : flatPrimitive k = (flatDifferential k : Lengths → ℝ) := by
    funext b
    simp [flatPrimitive, flatDifferential, mul_add]
  rw [heq]
  exact (flatDifferential k).hasFDerivAt

/-- This is the derivative of the affine chamber primitive, not a derivative
of a globally patched physical covolume at the interface. -/
theorem flatPrimitive_actual_derivative (a : Lengths) (ha : a ∈ positiveLengths)
    (k : Fin 3) (hk : Sector (fun q => Real.cosh (a q)) k) :
    HasFDerivAt (flatPrimitive k) (sourceDifferential a) a := by
  rw [sourceDifferential_eq_flat a ha k hk]
  exact flatPrimitive_hasFDerivAt k a

/-- Only the stated segment is required to lie in the same closed flat sector. -/
theorem flat_segment_integral (a b : Lengths) (k : Fin 3)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap a b t ∈ positiveLengths ∧
      Sector (fun q => Real.cosh (AffineMap.lineMap a b t q)) k) :
    (∫ᶜ x in Path.segment a b, sourceDifferential x) =
      flatPrimitive k b - flatPrimitive k a := by
  rw [curveIntegral_segment]
  have heq : (∫ t in (0 : ℝ)..1,
      sourceDifferential (AffineMap.lineMap a b t) (b - a)) =
      ∫ t in (0 : ℝ)..1, flatDifferential k (b - a) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    change sourceDifferential (AffineMap.lineMap a b t) (b - a) = flatDifferential k (b - a)
    rw [sourceDifferential_eq_flat _ (hsegment t ht').1 k (hsegment t ht').2]
  rw [heq]
  simp [flatDifferential, flatPrimitive] <;> ring

end CFMPActualExtendedAngle268Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualExtendedAngle268Transient.sourceAngle_eq_extendedAngle,
      ``CFMPActualExtendedAngle268Transient.sourceDifferential_continuousOn_positive,
      ``CFMPActualExtendedAngle268Transient.sourceDifferential_eq_flat,
      ``CFMPActualExtendedAngle268Transient.flatPrimitive_actual_derivative,
      ``CFMPActualExtendedAngle268Transient.flat_segment_integral] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP268 actual extended-angle interface absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP268 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP268 CHECKED {name} axioms={axioms}"
