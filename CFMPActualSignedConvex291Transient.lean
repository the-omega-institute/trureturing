import CFMPActualSignedC1290Transient
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPActualExtendedAngle268Transient (positiveLengths flatPrimitive)
open CFMPActualFlatVolume286Transient
open CFMPActualZeroAngle288Transient
open CFMPActualClosedOrthant289Transient
open CFMPActualSignedC1290Transient
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Sector)

namespace CFMPActualSignedConvex291Transient

theorem positivePart_idempotent (a : Lengths) : positivePart (positivePart a) = positivePart a :=
  positivePart_eq_self _ (fun q => le_max_left _ _)

theorem positivePartExtension_eq_on_nonnegative (g : Lengths → ℝ) (a : Lengths)
    (ha : a ∈ nonnegativeLengths) : positivePartExtension g a = g a :=
  congrArg g (positivePart_eq_self a ha)

/-- Nonnegative angle coefficients give monotonicity for the coordinate order
on the entire signed space, even along lines crossing sign interfaces. -/
theorem positivePartExtension_monotone
    (g : Lengths → ℝ)
    (hg : ∀ a ∈ nonnegativeLengths,
      HasFDerivWithinAt g (sourceDifferential a) nonnegativeLengths a) :
    Monotone (positivePartExtension g) := by
  intro x y hxy
  have hd (t : ℝ) :
      HasDerivAt (fun s => positivePartExtension g (AffineMap.lineMap x y s))
        (extendedDifferential (AffineMap.lineMap x y t) (y-x)) t :=
    (positivePartExtension_hasFDerivAt g hg _).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
  have hnonneg (t : ℝ) :
      0 ≤ extendedDifferential (AffineMap.lineMap x y t) (y-x) := by
    rw [extendedDifferential_apply]
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (extendedAngle_bounds _ q).1 (sub_nonneg.mpr (hxy q))
  have hm := monotone_of_hasDerivAt_nonneg hd hnonneg
  simpa only [AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hm zero_le_one

theorem positivePart_combo_le (x y : Lengths) (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    positivePart (c • x + d • y) ≤ c • positivePart x + d • positivePart y := by
  intro q
  change max 0 (c*x q+d*y q) ≤ c*max 0 (x q)+d*max 0 (y q)
  apply max_le
  · exact add_nonneg (mul_nonneg hc (le_max_left _ _))
      (mul_nonneg hd (le_max_left _ _))
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hc)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hd)

/-- Convexity of the cone extension and coordinate monotonicity combine with
the coordinatewise convex positive-part map. -/
theorem positivePartExtension_convex
    (g : Lengths → ℝ)
    (hg : ∀ a ∈ nonnegativeLengths,
      HasFDerivWithinAt g (sourceDifferential a) nonnegativeLengths a)
    (hconv : ConvexOn ℝ nonnegativeLengths g) :
    ConvexOn ℝ Set.univ (positivePartExtension g) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ c d hc hd hcd
  have hx : positivePart x ∈ nonnegativeLengths := fun q => le_max_left _ _
  have hy : positivePart y ∈ nonnegativeLengths := fun q => le_max_left _ _
  have hmix : c • positivePart x + d • positivePart y ∈ nonnegativeLengths :=
    nonnegativeLengths_convex hx hy hc hd hcd
  calc
    positivePartExtension g (c • x + d • y) =
        positivePartExtension g (positivePart (c • x + d • y)) := by
      simp only [positivePartExtension,positivePart_idempotent]
    _ ≤ positivePartExtension g (c • positivePart x + d • positivePart y) :=
      positivePartExtension_monotone g hg (positivePart_combo_le x y c d hc hd)
    _ = g (c • positivePart x + d • positivePart y) :=
      positivePartExtension_eq_on_nonnegative g _ hmix
    _ ≤ c • g (positivePart x) + d • g (positivePart y) := hconv.2 hx hy hc hd hcd
    _ = c • positivePartExtension g x + d • positivePartExtension g y := rfl

/-- The same calibrated actual physical covolume has a C1 convex extension to
all signed lengths. Negative coordinates are truncated before reading angles;
the value at the zero vector is inherited, not normalized to zero. -/
theorem exists_actual_signed_C1_convex_extension (a0 : Lengths) (ha0 : genuine a0) :
    ∃ F : Lengths → ℝ,
      ContDiff ℝ 1 F ∧
      ConvexOn ℝ Set.univ F ∧
      (∀ a, HasFDerivAt F (extendedDifferential a) a) ∧
      (∀ a, F a = F (positivePart a)) ∧
      Set.EqOn F referenceCovolume positiveLengths ∧
      (∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn F (physicalCovolume G) {a | genuine a}) ∧
      ∀ a ∈ positiveLengths, ∀ k : Fin 3,
        Sector (fun q => Real.cosh (a q)) k → F a = flatPrimitive k a := by
  obtain ⟨g,hgLip,heq,hconv,hder⟩ := exists_actual_closed_orthant_extension a0 ha0
  let F := positivePartExtension g
  have hpositive : Set.EqOn F referenceCovolume positiveLengths := by
    intro a ha
    exact (positivePartExtension_eq_on_nonnegative g a (fun q => (ha q).le)).trans (heq ha)
  refine ⟨F,positivePartExtension_contDiff g hder,
    positivePartExtension_convex g hder hconv,
    positivePartExtension_hasFDerivAt g hder,?_,hpositive,?_,?_⟩
  · intro a
    simp only [F,positivePartExtension,positivePart_idempotent]
  · intro G hG a ha
    exact (hpositive ha.1).trans (referenceCovolume_eq_actual G hG a ha)
  · intro a ha k hk
    exact (hpositive ha).trans (referenceCovolume_eq_flat a ha k hk)

end CFMPActualSignedConvex291Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualSignedConvex291Transient.positivePartExtension_monotone,
      ``CFMPActualSignedConvex291Transient.positivePartExtension_convex,
      ``CFMPActualSignedConvex291Transient.exists_actual_signed_C1_convex_extension] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP291 signed actual C1 convex covolume absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP291 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP291 CHECKED {name} axioms={axioms}"
