/- GID: D5/S3/Observer/CubicGain/BoundedWholeGain
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/BoundedWholeGain
   mirror-E: none(waiver:unbounded-source-uniform-estimate)
   anchors: []
   utility: none
   digest: Bounded actual fifth responses uniformly bound drift and the whole cubic gain on the unrestricted parent. -/

import D5.S3.Observer.CubicGain.SourceCompactification
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform bounds use a nonvanishing vector on a derived compact source space.
The original parent remains unbounded and includes its singular Lambda stratum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

def qNorm (z : CompactCoordinates) : ℝ := (6/5)*(9*z 1-1)*(2+3*z 1)
def driftRight (z : CompactCoordinates) : ℝ := -qNorm z*z 2*(1-z 3)
def fifthRight (z : CompactCoordinates) (p : ℝ) : ℝ :=
  z 2*(1-z 3)*((p-24)*(1-z 2)-vNorm z*(108*z 1-12))

def driftLift (z : CompactCoordinates) (p : ℝ) : ℝ :=
  (ell z*driftRight z+alpha z*fifthRight z p)/((ell z)^2+(alpha z)^2)

private theorem drift_den_pos (z : CompactCoordinates) (hz : ClosedSource z) :
    0 < (ell z)^2+(alpha z)^2 := by
  rcases compact_drift_vector_nonzero z hz with h | h
  · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (alpha z)]
  · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (ell z)]

theorem normalized_parent_equations (C : Coordinates) (hC : StrictParent C) :
    C.2.2*ell (compactSource C.1 C.2.1)=driftRight (compactSource C.1 C.2.1) ∧
    C.2.2*alpha (compactSource C.1 C.2.1)=
      fifthRight (compactSource C.1 C.2.1) (fifthResponse C) := by
  obtain ⟨r,b,e⟩ := C
  obtain ⟨hr,hr1,hb,hp⟩ := hC
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  have hs : 0 < sourceJ r b+sourceN r b := by positivity
  have hj1 : 0 < 1+sourceJ r b := by positivity
  have heq : e*ell (compactSource r b)-driftRight (compactSource r b) =
      ((1+b/(1+b))*(sourceJ r b/(1+sourceJ r b))*
        (sourceN r b/(sourceJ r b+sourceN r b)))*parentEq (r,b,e) := by
    unfold ell driftRight qNorm compactSource parentEq parentLambda parentB
    dsimp
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hu,
      ne_of_gt hs,ne_of_gt hj1]
    <;> ring
  constructor
  · rw [hp,mul_zero] at heq
    exact sub_eq_zero.mp heq
  · unfold alpha fifthRight vNorm compactSource fifthResponse fifthDrift
    dsimp
    simp only [sourceN]
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hu,
      ne_of_gt hs,ne_of_gt hj1]
    <;> ring

/-- The lift formula is derived from the literal parent and actual fifth reading. -/
theorem driftLift_actual (C : Coordinates) (hC : StrictParent C) :
    driftLift (compactSource C.1 C.2.1) (fifthResponse C)=C.2.2 := by
  have hz := compactSource_mem C.1 C.2.1 hC.1 hC.2.1 hC.2.2.1
  obtain ⟨hl,ha⟩ := normalized_parent_equations C hC
  unfold driftLift
  apply (div_eq_iff (ne_of_gt (drift_den_pos _ hz))).mpr
  rw [← hl,← ha]
  ring

/-- Bounded fifth responses bound the fixed drift over all strict sources. -/
theorem bounded_fifth_bounds_drift (M : ℝ) :
    ∃ D : ℝ, ∀ C : Coordinates, StrictParent C → |fifthResponse C| ≤ M → |C.2.2| ≤ D := by
  let K : Set (CompactCoordinates × ℝ) := {z | ClosedSource z} ×ˢ Set.Icc (-M) M
  have hK : IsCompact K := by
    change IsCompact ({z | ClosedSource z} ×ˢ Set.Icc (-M) M)
    exact closedSource_isCompact.prod isCompact_Icc
  have hcont : ContinuousOn (fun z : CompactCoordinates × ℝ => driftLift z.1 z.2) K := by
    unfold driftLift
    apply ContinuousOn.div
    · apply Continuous.continuousOn
      unfold ell alpha driftRight fifthRight qNorm vNorm
      fun_prop
    · apply Continuous.continuousOn
      unfold ell alpha vNorm
      fun_prop
    · intro z hz
      exact ne_of_gt (drift_den_pos z.1 hz.1)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨D,?_⟩
  intro C hC hp
  have hz := compactSource_mem C.1 C.2.1 hC.1 hC.2.1 hC.2.2.1
  have hmem : (compactSource C.1 C.2.1,fifthResponse C) ∈ K :=
    ⟨hz,abs_le.mp hp⟩
  simpa [driftLift_actual C hC] using hD _ hmem

private def evenFourth (z : CompactCoordinates) (e : ℝ) : ℝ :=
  (1-z 1)/(1+z 1)*(-6-e)
private def oddSum (z : CompactCoordinates) (e : ℝ) : ℝ :=
  ((-24-e)+6*(1-z 1)*(27/5-e)+evenFourth z e)/4

def boundedGain (z : CompactCoordinates) (e : ℝ) : Gain :=
  ![-24-e,(1-z 3)*oddSum z e,(1-z 1)*(27/5-e),z 3*oddSum z e]

/-- The equal odd readings control the whole gain without dividing by either
limiting odd trace. -/
theorem boundedGain_actual (C : Coordinates) (hC : StrictParent C) :
    boundedGain (compactSource C.1 C.2.1) C.2.2=parentGain C := by
  obtain ⟨r,b,e⟩ := C
  obtain ⟨hr,hr1,hb,hp⟩ := hC
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  have hs : 0 < sourceJ r b+sourceN r b := by positivity
  have hj1 : 0 < 1+sourceJ r b := by positivity
  have heq := normalized_parent_equations (r,b,e) ⟨hr,hr1,hb,hp⟩
  ext i
  fin_cases i
  · rfl
  · dsimp [boundedGain,parentGain,oddSum,evenFourth,compactSource]
    unfold parentEq parentLambda parentB at hp
    dsimp at hp
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hu,ne_of_gt hs] at hp ⊢
    nlinarith only [hp]
  · dsimp [boundedGain,parentGain,compactSource]
    field_simp [ne_of_gt ht]
    ring
  · dsimp [boundedGain,parentGain,oddSum,evenFourth,compactSource]
    unfold parentEq parentLambda parentB at hp
    dsimp at hp
    field_simp [ne_of_gt hj,ne_of_gt hn,ne_of_gt ht,ne_of_gt hu,ne_of_gt hs] at hp ⊢
    nlinarith only [hp]

/-- All four fixed-node gain coordinates are uniformly bounded. Polynomial
coefficients are fixed linear combinations of these same four samples. -/
theorem bounded_fifth_bounds_whole_gain (M : ℝ) :
    ∃ D G : ℝ, ∀ C : Coordinates, StrictParent C → |fifthResponse C| ≤ M →
      |C.2.2| ≤ D ∧ ∀ i : Fin 4, |parentGain C i| ≤ G := by
  obtain ⟨D,hD⟩ := bounded_fifth_bounds_drift M
  let K : Set (CompactCoordinates × ℝ) := {z | ClosedSource z} ×ˢ Set.Icc (-D) D
  have hK : IsCompact K := by
    change IsCompact ({z | ClosedSource z} ×ˢ Set.Icc (-D) D)
    exact closedSource_isCompact.prod isCompact_Icc
  have hcont : ContinuousOn (fun z : CompactCoordinates × ℝ => boundedGain z.1 z.2) K := by
    apply continuousOn_pi.mpr
    intro i
    fin_cases i <;> dsimp [boundedGain]
    · fun_prop
    · apply ContinuousOn.mul
      · fun_prop
      · unfold oddSum evenFourth
        fun_prop (disch := intro z hz; have := (hz.1.1 1).1; positivity)
    · fun_prop
    · apply ContinuousOn.mul
      · fun_prop
      · unfold oddSum evenFourth
        fun_prop (disch := intro z hz; have := (hz.1.1 1).1; positivity)
  obtain ⟨G,hG⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨D,G,?_⟩
  intro C hC hp
  have hd := hD C hC hp
  refine ⟨hd,?_⟩
  have hz := compactSource_mem C.1 C.2.1 hC.1 hC.2.1 hC.2.2.1
  have hmem : (compactSource C.1 C.2.1,C.2.2) ∈ K :=
    ⟨hz,abs_le.mp hd⟩
  have hg : ‖parentGain C‖ ≤ G := by simpa [boundedGain_actual C hC] using hG _ hmem
  intro i
  have hi : |parentGain C i| ≤ ‖parentGain C‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (parentGain C) i
  exact hi.trans hg

#print axioms bounded_fifth_bounds_drift
#print axioms bounded_fifth_bounds_whole_gain

end D5.S3.Observer.CubicGain
