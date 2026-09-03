/- GID: D5/S3/Zeros/TransverseStopLossTomography
   generality: G
   mirror-B: D5/B/S3/Zeros/TransverseStopLossTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recover a finite transverse divisor from its stop-loss transport profile. -/

import D5.S3.Zeros.ObservationDepthStopLoss
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Library-search audit trail (2026-09-03):
   * Exact and spelling-variant D5 searches covered stop-loss, transverse
     tomography, tail-count integrals, observation transport, and slope jumps.
     `ObservationDepthStopLoss` is the adjacent owner of the finite profile
     definitions; its audit explicitly leaves the integral and derivative laws
     to the following atom.
   * The digestion receipt and residual-open indexes contain no receipt for this
     atom. The related receipt `0c78bc...` covers only positivity and saturation
     bounds, not any transport identity.
   * Generalized searches covered fundamental-theorem, layer-cake, distribution,
     and finite-measure formulations. No existing D5 theorem gives these three
     identities or recovers point masses from the slope jump.
   * All local and remote in-flight lane logs were checked. The only related
     lane is the already merged preceding stop-loss module, whose statement is
     disjoint from this one.
   * Pinned Mathlib supplies `MeasureTheory.setIntegral_indicator`,
     `Real.volume_Ioo`, `intervalIntegral.integral_Ioi_sub_Ioi'`, and the finite
     sum derivative rules. They are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval

open D5.S3.Zeros.ObservationDepthStopLoss

namespace D5.S3.Zeros.TransverseStopLossTomography

/-- The real-valued tail count used as an integrand. -/
def tailCount {ι : Type*} [Fintype ι]
    (delta : ι -> Real) (multiplicity : ι -> Nat) (omega : Real) : Real :=
  ∑ j, if omega < delta j then (multiplicity j : Real) else 0

/-- The tail count with poles exactly at the observation depth retained. -/
def closedTailCount {ι : Type*} [Fintype ι]
    (delta : ι -> Real) (multiplicity : ι -> Nat) (omega : Real) : Real :=
  ∑ j, if omega <= delta j then (multiplicity j : Real) else 0

/-- Total divisor multiplicity carried by one transverse distance. -/
def divisorMultiplicity {ι : Type*} [Fintype ι]
    (delta : ι -> Real) (multiplicity : ι -> Nat) (omega : Real) : Real :=
  ∑ j, if delta j = omega then (multiplicity j : Real) else 0

/-- Area swept out between observation depths `omega` and `omega + y`. -/
def observationArea {ι : Type*} [Fintype ι]
    (delta : ι -> Real) (multiplicity : ι -> Nat) (omega y : Real) : Real :=
  remainingDepth delta multiplicity omega -
    remainingDepth delta multiplicity (omega + y)

private theorem sum_neg_indicator_eq_neg_sum
    {ι : Type*} [Fintype ι] (predicate : ι -> Prop)
    [DecidablePred predicate] (weight : ι -> Real) :
    (∑ j, weight j * if predicate j then (-1 : Real) else 0) =
      -(∑ j, if predicate j then weight j else 0) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : predicate j <;> simp [h]

private theorem tailAtom_integrableOn_Ioi (delta omega weight : Real) :
    IntegrableOn (fun u : Real => if u < delta then weight else 0) (Ioi omega) := by
  have hfun : (fun u : Real => if u < delta then weight else 0) =
      (Iio delta).indicator (fun _ : Real => weight) := by
    funext u
    simp only [indicator_apply, mem_Iio]
  rw [hfun]
  change Integrable ((Iio delta).indicator (fun _ : Real => weight))
    (volume.restrict (Ioi omega))
  rw [integrable_indicator_iff measurableSet_Iio]
  refine integrableOn_const ?_ (by finiteness)
  simp [Iio_inter_Ioi, Real.volume_Ioo]

private theorem integral_tailAtom_Ioi (delta omega weight : Real) :
    (∫ u : Real in Ioi omega, if u < delta then weight else 0) =
      weight * activePoleHeight delta omega := by
  have hfun : (fun u : Real => if u < delta then weight else 0) =
      (Iio delta).indicator (fun _ : Real => weight) := by
    funext u
    simp only [indicator_apply, mem_Iio]
  rw [hfun, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    setIntegral_const]
  rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal']
  simp only [smul_eq_mul]
  rw [mul_comm]
  rfl

theorem tailCount_integrableOn_Ioi
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) : IntegrableOn (tailCount delta multiplicity) (Ioi omega) := by
  unfold tailCount
  exact integrable_finsetSum Finset.univ fun j _ =>
    tailAtom_integrableOn_Ioi (delta j) omega (multiplicity j : Real)

/-- Remaining transverse depth is exactly the integral of the active tail. -/
theorem remainingDepth_eq_integral_tailCount
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) :
    remainingDepth delta multiplicity omega =
      ∫ u : Real in Ioi omega, tailCount delta multiplicity u := by
  change remainingDepth delta multiplicity omega =
    ∫ u : Real in Ioi omega,
      ∑ j, if u < delta j then (multiplicity j : Real) else 0
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_tailAtom_Ioi]
    rfl
  · intro j _
    exact tailAtom_integrableOn_Ioi (delta j) omega (multiplicity j : Real)

private theorem min_activePoleHeight_eq_sub (delta omega y : Real) (hy : 0 <= y) :
    min y (activePoleHeight delta omega) =
      activePoleHeight delta omega - activePoleHeight delta (omega + y) := by
  by_cases hcut : delta <= omega
  · have hcut' : delta <= omega + y := by linarith
    simp [activePoleHeight, sub_nonpos.mpr hcut, sub_nonpos.mpr hcut', hy]
  · have homega : omega < delta := lt_of_not_ge hcut
    by_cases hsaturated : delta <= omega + y
    · have hheight : delta - omega <= y := by linarith
      simp [activePoleHeight, sub_nonneg.mpr homega.le,
        sub_nonpos.mpr hsaturated, min_eq_right hheight]
    · have hlinear : y <= delta - omega := by linarith
      have hshift : omega + y < delta := lt_of_not_ge hsaturated
      simp [activePoleHeight, sub_nonneg.mpr homega.le,
        sub_nonneg.mpr hshift.le, min_eq_left hlinear]

/-- The capped finite-sum decay is the difference of the two remaining-depth
profiles. The nonnegativity premise is necessary for the capped definition. -/
theorem doubleDepthDecay_eq_observationArea
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega y : Real) (hy : 0 <= y) :
    doubleDepthDecay delta multiplicity omega y =
      observationArea delta multiplicity omega y := by
  unfold doubleDepthDecay observationArea remainingDepth
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_sub, min_activePoleHeight_eq_sub (delta j) omega y hy]

/-- The observation area is the tail count integrated over the swept interval. -/
theorem observationArea_eq_integral_tailCount
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega y : Real) :
    observationArea delta multiplicity omega y =
      ∫ u : Real in omega..(omega + y), tailCount delta multiplicity u := by
  rw [observationArea, remainingDepth_eq_integral_tailCount,
    remainingDepth_eq_integral_tailCount]
  exact intervalIntegral.integral_Ioi_sub_Ioi'
    (tailCount_integrableOn_Ioi delta multiplicity omega)
    (tailCount_integrableOn_Ioi delta multiplicity (omega + y))

private theorem activePoleHeight_hasDerivAt (delta omega : Real)
    (hjump : omega ≠ delta) :
    HasDerivAt (activePoleHeight delta)
      (if omega < delta then -1 else 0) omega := by
  by_cases hactive : omega < delta
  · have hlocal : activePoleHeight delta =ᶠ[nhds omega]
        (fun u : Real => delta - u) := by
      filter_upwards [eventually_lt_nhds hactive] with u hu
      simp [activePoleHeight, sub_nonneg.mpr hu.le]
    simpa [hactive] using
      ((hasDerivAt_const omega delta).sub (hasDerivAt_id omega)).congr_of_eventuallyEq hlocal
  · have hinactive : delta < omega :=
      lt_of_le_of_ne (le_of_not_gt hactive) hjump.symm
    have hlocal : activePoleHeight delta =ᶠ[nhds omega]
        (fun _ : Real => 0) := by
      filter_upwards [eventually_gt_nhds hinactive] with u hu
      simp [activePoleHeight, sub_nonpos.mpr hu.le]
    simpa [hactive] using
      (hasDerivAt_const omega (0 : Real)).congr_of_eventuallyEq hlocal

/-- Away from a transverse distance, the remaining-depth slope is minus the
strict tail count. -/
theorem remainingDepth_hasDerivAt
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) (hjump : forall j, omega ≠ delta j) :
    HasDerivAt (remainingDepth delta multiplicity)
      (-tailCount delta multiplicity omega) omega := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (activePoleHeight_hasDerivAt (delta j) omega (hjump j)).const_mul
      (multiplicity j : Real)
  change HasDerivAt
    (fun u : Real => ∑ j, (multiplicity j : Real) * activePoleHeight (delta j) u)
    (-tailCount delta multiplicity omega) omega
  apply hsum.congr_deriv
  simpa only [tailCount] using
    sum_neg_indicator_eq_neg_sum (fun j => omega < delta j)
      (fun j => (multiplicity j : Real))

/-- The derivative in observation length reads the tail count at the far
endpoint. -/
theorem observationArea_hasDerivAt_y
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega y : Real) (hjump : forall j, omega + y ≠ delta j) :
    HasDerivAt (fun t => observationArea delta multiplicity omega t)
      (tailCount delta multiplicity (omega + y)) y := by
  have hfar := remainingDepth_hasDerivAt delta multiplicity (omega + y) hjump
  have hcomp := hfar.comp_const_add omega y
  have h :=
    (hasDerivAt_const y (remainingDepth delta multiplicity omega)).sub hcomp
  have hfun :
      (fun t => observationArea delta multiplicity omega t) =ᶠ[nhds y]
        ((fun _ : Real => remainingDepth delta multiplicity omega) -
          fun t => remainingDepth delta multiplicity (omega + t)) := by
    filter_upwards [] with t
    rfl
  exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)

/-- The derivative in initial observation depth is the difference of the far
and near tail counts. -/
theorem observationArea_hasDerivAt_omega
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega y : Real) (hnear : forall j, omega ≠ delta j)
    (hfar : forall j, omega + y ≠ delta j) :
    HasDerivAt (fun t => observationArea delta multiplicity t y)
      (tailCount delta multiplicity (omega + y) -
        tailCount delta multiplicity omega) omega := by
  have hleft := remainingDepth_hasDerivAt delta multiplicity omega hnear
  have hright := remainingDepth_hasDerivAt delta multiplicity (omega + y) hfar
  have hcomp := hright.comp_add_const omega y
  have h := hleft.sub hcomp
  have hfun :
      (fun t => observationArea delta multiplicity t y) =ᶠ[nhds omega]
        (remainingDepth delta multiplicity -
          fun t => remainingDepth delta multiplicity (t + y)) := by
    filter_upwards [] with t
    rfl
  exact (h.congr_of_eventuallyEq hfun).congr_deriv (by ring)

private theorem activePoleHeight_hasDerivWithinAt_right (delta omega : Real) :
    HasDerivWithinAt (activePoleHeight delta)
      (if omega < delta then -1 else 0) (Ici omega) omega := by
  by_cases hactive : omega < delta
  · exact (activePoleHeight_hasDerivAt delta omega hactive.ne).hasDerivWithinAt
  · have hglobal : EqOn (activePoleHeight delta) (fun _ : Real => 0) (Ici omega) := by
      intro u hu
      simp [activePoleHeight, sub_nonpos.mpr ((le_of_not_gt hactive).trans hu)]
    simpa [hactive] using
      (hasDerivWithinAt_const (x := omega) (s := Ici omega) (c := (0 : Real))).congr
        (fun _ hu => hglobal hu) (hglobal (mem_Ici.mpr le_rfl))

private theorem activePoleHeight_hasDerivWithinAt_left (delta omega : Real) :
    HasDerivWithinAt (activePoleHeight delta)
      (if omega <= delta then -1 else 0) (Iic omega) omega := by
  by_cases hactive : omega <= delta
  · have hglobal : EqOn (activePoleHeight delta) (fun u : Real => delta - u) (Iic omega) := by
      intro u hu
      simp [activePoleHeight, sub_nonneg.mpr (hu.trans hactive)]
    simpa [hactive] using
      (((hasDerivAt_const omega delta).sub (hasDerivAt_id omega)).hasDerivWithinAt).congr
        (fun _ hu => hglobal hu) (hglobal (mem_Iic.mpr le_rfl))
  · have hlt : delta < omega := lt_of_not_ge hactive
    have hnotlt : ¬omega < delta := not_lt_of_ge hlt.le
    simpa [hactive, hnotlt] using
      (activePoleHeight_hasDerivAt delta omega (ne_of_gt hlt)).hasDerivWithinAt

theorem remainingDepth_hasDerivWithinAt_right
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) :
    HasDerivWithinAt (remainingDepth delta multiplicity)
      (-tailCount delta multiplicity omega) (Ici omega) omega := by
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ =>
    (activePoleHeight_hasDerivWithinAt_right (delta j) omega).const_mul
      (multiplicity j : Real)
  change HasDerivWithinAt
    (fun u : Real => ∑ j, (multiplicity j : Real) * activePoleHeight (delta j) u)
    (-tailCount delta multiplicity omega) (Ici omega) omega
  apply hsum.congr_deriv
  simpa only [tailCount] using
    sum_neg_indicator_eq_neg_sum (fun j => omega < delta j)
      (fun j => (multiplicity j : Real))

theorem remainingDepth_hasDerivWithinAt_left
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) :
    HasDerivWithinAt (remainingDepth delta multiplicity)
      (-closedTailCount delta multiplicity omega) (Iic omega) omega := by
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) fun j _ =>
    (activePoleHeight_hasDerivWithinAt_left (delta j) omega).const_mul
      (multiplicity j : Real)
  change HasDerivWithinAt
    (fun u : Real => ∑ j, (multiplicity j : Real) * activePoleHeight (delta j) u)
    (-closedTailCount delta multiplicity omega) (Iic omega) omega
  apply hsum.congr_deriv
  simpa only [closedTailCount] using
    sum_neg_indicator_eq_neg_sum (fun j => omega <= delta j)
      (fun j => (multiplicity j : Real))

/-- The jump from the left slope to the right slope is exactly the total
multiplicity at that transverse distance. This is the finite-profile meaning of
`R'' = sum m_j delta_{delta_j}` and gives pointwise divisor recovery. -/
theorem slope_jump_eq_divisorMultiplicity
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega : Real) :
    (-tailCount delta multiplicity omega) -
        (-closedTailCount delta multiplicity omega) =
      divisorMultiplicity delta multiplicity omega := by
  unfold tailCount closedTailCount divisorMultiplicity
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy omega (delta j) with hlt | heq | hgt
  · simp [hlt, hlt.le, hlt.ne']
  · subst omega
    simp
  · simp [not_lt_of_ge hgt.le, not_le_of_gt hgt, hgt.ne]

/-- **Transverse stop-loss tomography.** For a finite multiplicity-weighted
transverse profile, the remaining depth and swept area satisfy the three source
transport identities. At non-jump endpoints their two derivatives satisfy the
transport PDE, while at every depth the one-sided slope jump recovers exactly
the divisor multiplicity there. -/
theorem transverse_stop_loss_tomography
    {ι : Type*} [Fintype ι] (delta : ι -> Real) (multiplicity : ι -> Nat)
    (omega y : Real) (hy : 0 <= y)
    (hnear : forall j, omega ≠ delta j)
    (hfar : forall j, omega + y ≠ delta j) :
    remainingDepth delta multiplicity omega =
        ∫ u : Real in Ioi omega, tailCount delta multiplicity u /\
      observationArea delta multiplicity omega y =
        remainingDepth delta multiplicity omega -
          remainingDepth delta multiplicity (omega + y) /\
      observationArea delta multiplicity omega y =
        ∫ u : Real in omega..(omega + y), tailCount delta multiplicity u /\
      doubleDepthDecay delta multiplicity omega y =
        observationArea delta multiplicity omega y /\
      HasDerivAt (fun t => observationArea delta multiplicity omega t)
        (tailCount delta multiplicity (omega + y)) y /\
      HasDerivAt (fun t => observationArea delta multiplicity t y)
        (tailCount delta multiplicity (omega + y) -
          tailCount delta multiplicity omega) omega /\
      (tailCount delta multiplicity (omega + y) -
          tailCount delta multiplicity omega) -
          tailCount delta multiplicity (omega + y) =
        -tailCount delta multiplicity omega /\
      forall x,
        HasDerivWithinAt (remainingDepth delta multiplicity)
            (-tailCount delta multiplicity x) (Ici x) x /\
          HasDerivWithinAt (remainingDepth delta multiplicity)
            (-closedTailCount delta multiplicity x) (Iic x) x /\
          (-tailCount delta multiplicity x) -
              (-closedTailCount delta multiplicity x) =
            divisorMultiplicity delta multiplicity x := by
  refine ⟨remainingDepth_eq_integral_tailCount delta multiplicity omega,
    rfl, observationArea_eq_integral_tailCount delta multiplicity omega y,
    doubleDepthDecay_eq_observationArea delta multiplicity omega y hy,
    observationArea_hasDerivAt_y delta multiplicity omega y hfar,
    observationArea_hasDerivAt_omega delta multiplicity omega y hnear hfar,
    by ring, ?_⟩
  intro x
  exact ⟨remainingDepth_hasDerivWithinAt_right delta multiplicity x,
    remainingDepth_hasDerivWithinAt_left delta multiplicity x,
    slope_jump_eq_divisorMultiplicity delta multiplicity x⟩

#print axioms transverse_stop_loss_tomography

end D5.S3.Zeros.TransverseStopLossTomography
