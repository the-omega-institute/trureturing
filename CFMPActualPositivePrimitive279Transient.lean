import CFMPLocalExactConvex278Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths physicalCovolume RealizationFamily)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualExtendedAngle268Transient
open CFMPActualPrimitiveCalibration267Transient (normalizedPrimitive normalized_primitive_matches_actual)

namespace CFMPActualPositivePrimitive279Transient

def positivePrimitive (a0 a : Lengths) : ℝ :=
  ∫ᶜ x in Path.segment a0 a, sourceDifferential x

theorem positiveLengths_convex : Convex ℝ positiveLengths := by
  intro x hx y hy c d hc hd hcd q
  exact (convex_Ioi (0 : ℝ)) (hx q) (hy q) hc hd hcd

/-- The primitive is constructed by the actual six-angle segment integral;
local exactness supplies the missing global triangle identity. -/
theorem positivePrimitive_C1 (a0 : Lengths) (ha0 : a0 ∈ positiveLengths) :
    ContDiffOn ℝ 1 (positivePrimitive a0) positiveLengths ∧
      ∀ a ∈ positiveLengths,
        HasFDerivAt (positivePrimitive a0) (sourceDifferential a) a := by
  have hlocal : ∀ z ∈ positiveLengths, ∃ V : Set Lengths,
      z ∈ V ∧ IsOpen V ∧ ∃ G : Lengths → ℝ,
        ∀ w ∈ V, HasFDerivAt G (sourceDifferential w) w := by
    intro z hz
    obtain ⟨V,h0,hV,_,G,_,hG⟩ :=
      CFMPActualEverywhereLocalPrimitive276Transient.exists_local_angle_primitive z hz
    exact ⟨V,h0,hV,G,hG⟩
  exact CFMPLocalExactConvex278Transient.segment_primitive_C1_of_local_exactness
    positiveLengths positiveLengths_convex positiveLengths_open sourceDifferential
    sourceDifferential_continuousOn_positive hlocal a0 ha0

/-- Calibrating this constructed positive-domain primitive at one genuine
basepoint gives a C1 extension of the same actual physical covolume. Its
flat-sector additive constants and convexity are not asserted here. -/
theorem positive_C1_actual_extension (a0 : Lengths) (ha0 : genuine a0) :
    ContDiffOn ℝ 1 (normalizedPrimitive (positivePrimitive a0) a0) positiveLengths ∧
      (∀ a ∈ positiveLengths,
        HasFDerivAt (normalizedPrimitive (positivePrimitive a0) a0)
          (sourceDifferential a) a) ∧
      ∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn (normalizedPrimitive (positivePrimitive a0) a0)
          (physicalCovolume G) {a | genuine a} := by
  have hp := positivePrimitive_C1 a0 ha0.1
  have hC1 : ContDiffOn ℝ 1 (normalizedPrimitive (positivePrimitive a0) a0)
      positiveLengths := hp.1.add contDiffOn_const
  have hD (a : Lengths) (ha : a ∈ positiveLengths) :
      HasFDerivAt (normalizedPrimitive (positivePrimitive a0) a0)
        (sourceDifferential a) a :=
    (hp.2 a ha).add_const (physicalCovolume wholeFamily a0 - positivePrimitive a0 a0)
  refine ⟨hC1,hD,?_⟩
  intro G hG
  exact normalized_primitive_matches_actual (positivePrimitive a0)
    (fun a ha => hp.2 a ha.1) a0 ha0 G hG

end CFMPActualPositivePrimitive279Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPositivePrimitive279Transient.positivePrimitive_C1,
      ``CFMPActualPositivePrimitive279Transient.positive_C1_actual_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP279 constructed positive-domain covolume primitive absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP279 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP279 CHECKED {name} axioms={axioms}"
