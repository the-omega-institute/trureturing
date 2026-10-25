import CFMPActualSignedConvex291Transient
import CFMPConvexCoercivity292Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential)
open CFMPGenuineLengthNeighborhood435Transient (genuine genuine_open)
open CFMPGlobalGenuineCovolume256Transient (wholeFamily wholeFamily_realized realizedFamily)
open CFMPActualPhysicalHessian258Transient (physicalHessian_posDef)
open CFMPActualCompactHessian261Transient (physicalQuadratic physicalQuadratic_dotProduct)
open CFMPActualLineAngleDerivative283Transient (directionAngle directionAngle_hasDerivAt_genuine)
open CFMPActualZeroAngle288Transient (positivePart_eq_self extendedDifferential)
open CFMPActualSignedConvex291Transient
open CFMPConvexCoercivity292Transient

namespace CFMPActualTiltedCoercivity293Transient

set_option backward.isDefEq.respectTransparency.types false in
/-- The positive native Hessian supplies a strict local sphere gap for the
actual-angle primitive tilted by the angle covector at a genuine point. -/
theorem actual_tilted_sphere_gap (F : Lengths → ℝ)
    (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (a : Lengths) (ha : genuine a) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.sphere a r,
      F a-sourceDifferential a a < F x-sourceDifferential a x := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp genuine_open a ha
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r,hr,?_⟩
  intro x hx
  have hdist : dist x a = r := Metric.mem_sphere.mp hx
  have hxa : x ≠ a := by
    intro h
    have : r = 0 := by simpa [h] using hdist.symm
    linarith
  have hv : x-a ≠ 0 := sub_ne_zero.mpr hxa
  have hxb : x ∈ Metric.ball a ε := by
    apply Metric.mem_ball.mpr
    rw [hdist]
    dsimp [r]
    linarith
  have hab : a ∈ Metric.ball a ε := Metric.mem_ball_self hε
  have hgenuine (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      genuine (AffineMap.lineMap a x t) :=
    hball ((convex_ball a ε).lineMap_mem hab hxb ht)
  have hdg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    directionAngle_hasDerivAt_genuine a x t (hgenuine t ht)
  have hgc : ContinuousOn (directionAngle a x) (Icc (0 : ℝ) 1) :=
    fun t ht => (hdg t ht).continuousAt.continuousWithinAt
  have hgm : StrictMonoOn (directionAngle a x) (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hgc
    intro t ht
    rw [(hdg t (interior_subset ht)).deriv,physicalQuadratic_dotProduct]
    simpa using (physicalHessian_posDef wholeFamily wholeFamily_realized
      (AffineMap.lineMap a x t) (hgenuine t (interior_subset ht))).dotProduct_mulVec_pos hv
  let q : ℝ → ℝ := fun t => F (AffineMap.lineMap a x t)-
    sourceDifferential a (AffineMap.lineMap a x t)
  have hdq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt q (directionAngle a x t-sourceDifferential a (x-a)) t := by
    have hp := hgenuine t ht
    have hext : extendedDifferential (AffineMap.lineMap a x t) =
        sourceDifferential (AffineMap.lineMap a x t) := by
      unfold extendedDifferential
      rw [positivePart_eq_self _ (fun j => (hp.1 j).le)]
    have hleft := (hF (AffineMap.lineMap a x t)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap
    have hright := (sourceDifferential a).hasFDerivAt.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := a) (b := x) (x := t))
    simpa only [q,Function.comp_def,hext,directionAngle]
      using hleft.fun_sub hright
  have hqc : ContinuousOn q (Icc (0 : ℝ) 1) :=
    fun t ht => (hdq t ht).continuousAt.continuousWithinAt
  have hqm : StrictMonoOn q (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hqc
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
    rw [(hdq t (interior_subset ht)).deriv,sub_pos]
    simpa only [directionAngle,AffineMap.lineMap_apply_zero] using
      hgm (Set.left_mem_Icc.mpr zero_le_one) (interior_subset ht) ht'.1
  simpa only [q,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using
    hqm (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
      (by norm_num : (0 : ℝ) < 1)

/-- Coercivity is proved for the actual tilt at each known genuine length
vector. This does not assume or assert that every strict angle is realized. -/
theorem actual_tilted_coercive_minimum (F : Lengths → ℝ)
    (hc : Continuous F) (hconv : ConvexOn ℝ Set.univ F)
    (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (a : Lengths) (ha : genuine a) :
    Tendsto (fun b => F b-sourceDifferential a b) (cocompact Lengths) atTop ∧
      ∃ b : Lengths, ∀ c : Lengths,
        F b-sourceDifferential a b ≤ F c-sourceDifferential a c := by
  obtain ⟨r,hr,hgap⟩ := actual_tilted_sphere_gap F hF a ha
  exact convex_sphere_gap_coercive_minimum _
    (hc.sub (sourceDifferential a).continuous)
    (hconv.sub ((sourceDifferential a).toLinearMap.concaveOn convex_univ))
    a r hr hgap

/-- The same physically calibrated signed extension has coercive local
angle tilts for all genuine vectors, simultaneously for every legal family. -/
theorem exists_actual_signed_coercive_tilts (a0 : Lengths) (ha0 : genuine a0) :
    ∃ F : Lengths → ℝ,
      ContDiff ℝ 1 F ∧ ConvexOn ℝ Set.univ F ∧
      (∀ b, HasFDerivAt F (extendedDifferential b) b) ∧
      (∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn F (physicalCovolume G) {a | genuine a}) ∧
      ∀ a : Lengths, genuine a →
        Tendsto (fun b => F b-sourceDifferential a b) (cocompact Lengths) atTop := by
  obtain ⟨F,hC,hconv,hder,hpart,heq,hphysical,hflat⟩ :=
    exists_actual_signed_C1_convex_extension a0 ha0
  exact ⟨F,hC,hconv,hder,hphysical,
    fun a ha => (actual_tilted_coercive_minimum F hC.continuous hconv hder a ha).1⟩

end CFMPActualTiltedCoercivity293Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualTiltedCoercivity293Transient.actual_tilted_sphere_gap,
      ``CFMPActualTiltedCoercivity293Transient.actual_tilted_coercive_minimum,
      ``CFMPActualTiltedCoercivity293Transient.exists_actual_signed_coercive_tilts] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP293 actual local angle-tilt coercivity absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP293 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP293 CHECKED {name} axioms={axioms}"
