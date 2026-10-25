import CFMPActualIncidenceCoercivity294Transient
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
universe u295 v295
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (Incidence star source)
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPOriginalCovolumeC1253Transient (sourceDifferential sourceDifferential_apply)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPActualGlobalEnergy259Transient (localRead occurrence_regroup)
open CFMPActualZeroAngle288Transient
open CFMPActualSignedConvex291Transient
open CFMPActualTiltedCoercivity293Transient
open CFMPActualIncidenceCoercivity294Transient

namespace CFMPActualPrescribedCone295Transient

variable {T : Type u295} {E : Type v295}
  [Fintype T] [Fintype E] [DecidableEq E]

/-- Each local angle vector here is already supplied by an actual genuine
length vector. No inverse angle-realization theorem is assumed. -/
def realizedConeTarget (s : Incidence T E) (A : T → Lengths) (e : E) : ℝ :=
  ∑ o ∈ star s e, sourceAngle (A o.1) o.2

/-- Actual signed angles, read at every original local edge occurrence. -/
def signedCone (s : Incidence T E) (p : E → ℝ) (e : E) : ℝ :=
  ∑ o ∈ star s e, extendedAngle (localRead s o.1 p) o.2

def signedEnergy (s : Incidence T E) (F : Lengths → ℝ) (k : E → ℝ) (p : E → ℝ) : ℝ :=
  (∑ t : T, F (localRead s t p))-(∑ e : E, k e*p e)

theorem local_tilts_sum (s : Incidence T E) (F : Lengths → ℝ)
    (A : T → Lengths) (p : E → ℝ) :
    (∑ t : T, (F (localRead s t p)-sourceDifferential (A t) (localRead s t p))) =
      signedEnergy s F (realizedConeTarget s A) p := by
  classical
  simp only [Finset.sum_sub_distrib,sourceDifferential_apply,signedEnergy]
  congr 1
  simpa only [localRead,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,realizedConeTarget] using
    occurrence_regroup s (fun o => sourceAngle (A o.1) o.2) p

theorem signedEnergy_realized_coercive_minimum (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (F : Lengths → ℝ) (hc : Continuous F) (hconv : ConvexOn ℝ Set.univ F)
    (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (A : T → Lengths) (hA : ∀ t, genuine (A t)) :
    Tendsto (signedEnergy s F (realizedConeTarget s A)) (cocompact (E → ℝ)) atTop ∧
      ∃ p : E → ℝ, ∀ q : E → ℝ,
        signedEnergy s F (realizedConeTarget s A) p ≤
          signedEnergy s F (realizedConeTarget s A) q := by
  let f : T → Lengths → ℝ := fun t v => F v-sourceDifferential (A t) v
  have hfc (t : T) : Continuous (f t) := hc.sub (sourceDifferential (A t)).continuous
  have hgrow (t : T) : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ,
      ∀ v : Lengths, c*‖v‖-C ≤ f t v := by
    obtain ⟨r,hr,hgap⟩ := actual_tilted_sphere_gap F hF (A t) (hA t)
    exact sphere_gap_global_linear (f t) (hfc t)
      (hconv.sub ((sourceDifferential (A t)).toLinearMap.concaveOn convex_univ))
      (A t) r hr hgap
  have hsum := finite_incidence_coercive_minimum s hobs f hfc hgrow
  have heq : (fun p : E → ℝ => ∑ t : T, f t (localRead s t p)) =
      signedEnergy s F (realizedConeTarget s A) := by
    funext p
    exact local_tilts_sum s F A p
  simpa only [← heq] using hsum

set_option backward.isDefEq.respectTransparency.types false in
theorem signedEnergy_hasFDerivAt (s : Incidence T E)
    (F : Lengths → ℝ) (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (k : E → ℝ) (p : E → ℝ) :
    HasFDerivAt (signedEnergy s F k)
      (∑ e : E, (signedCone s p e-k e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
  classical
  have hlocal (t : T) : HasFDerivAt (fun q : E → ℝ => F (localRead s t q))
      ((extendedDifferential (localRead s t p)).comp (localRead s t)) p :=
    (hF _).comp p (localRead s t).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (fun t (_ : t ∈ (Finset.univ : Finset T)) => hlocal t)
  have hlin : HasFDerivAt (fun q : E → ℝ => ∑ e : E, k e*q e)
      (∑ e : E, k e • (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
    exact HasFDerivAt.fun_sum (fun e (_ : e ∈ (Finset.univ : Finset E)) =>
      (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_mul (k e))
  have hmap :
      (∑ t : T, (extendedDifferential (localRead s t p)).comp (localRead s t))-
        (∑ e : E, k e • (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) =
      ∑ e : E, (signedCone s p e-k e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul,extendedDifferential_apply]
    have heq : (∑ t : T, ∑ q : Fin 6,
        extendedAngle (localRead s t p) q*localRead s t v q) =
      ∑ e : E, (∑ o ∈ star s e, extendedAngle (localRead s o.1 p) o.2)*v e := by
      simpa only [localRead,ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.proj_apply] using occurrence_regroup s
          (fun o => extendedAngle (localRead s o.1 p) o.2) v
    rw [heq]
    simp only [signedCone,sub_mul,Finset.sum_sub_distrib]
  rw [← hmap]
  exact hsum.fun_sub hlin

/-- At a global minimum every original edge cone sum equals the prescribed
value, including repeated occurrences in the same tetrahedron. -/
theorem minimum_cone_equations (s : Incidence T E)
    (F : Lengths → ℝ) (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (k : E → ℝ) (p : E → ℝ)
    (hp : ∀ q : E → ℝ, signedEnergy s F k p ≤ signedEnergy s F k q) :
    ∀ e : E, signedCone s p e = k e := by
  classical
  have hmin : IsLocalMin (signedEnergy s F k) p := Filter.Eventually.of_forall hp
  have hzero := hmin.hasFDerivAt_eq_zero (signedEnergy_hasFDerivAt s F hF k p)
  intro e
  have he := congrArg (fun L : (E → ℝ) →L[ℝ] ℝ => L (Pi.single e 1)) hzero
  have hz : signedCone s p e-k e = 0 := by
    simpa [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,Pi.single_apply] using he
  exact sub_eq_zero.mp hz

theorem realizedConeTarget_positive (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (A : T → Lengths) (hA : ∀ t, genuine (A t)) :
    ∀ e : E, 0 < realizedConeTarget s A e := by
  classical
  intro e
  obtain ⟨t,q,hq⟩ := hobs e
  apply Finset.sum_pos'
  · intro o _
    exact Real.arccos_nonneg _
  · refine ⟨(t,q),?_,?_⟩
    · simp only [D5.S3.Geometry.Hyperideal.FourCycleCurvature.star,Finset.mem_filter,Finset.mem_univ,true_and,source,hq]
    · exact Real.arccos_pos.mpr ((hA t).2 q).2

/-- A nonpositive global coordinate makes every incident signed angle zero;
it cannot satisfy a strictly positive prescribed cone sum. -/
theorem positive_of_cone_equations (s : Incidence T E) (p k : E → ℝ)
    (hk : ∀ e, 0 < k e) (hp : ∀ e, signedCone s p e = k e) :
    ∀ e : E, 0 < p e := by
  classical
  intro e
  by_contra hnot
  have hpe : p e ≤ 0 := le_of_not_gt hnot
  have hz : signedCone s p e = 0 := by
    apply Finset.sum_eq_zero
    intro o ho
    apply extendedAngle_zero_of_nonpos
    change p (source s o) ≤ 0
    rw [(Finset.mem_filter.mp ho).2]
    exact hpe
  have hk0 : k e = 0 := (hp e).symm.trans hz
  exact (ne_of_gt (hk e)) hk0

/-- Independently supplied genuine local metrics yield a common positive
generalized length vector with their same actual cone sums. Flat local
blocks at the resulting vector have not been excluded. -/
theorem exists_positive_realized_cone_solution (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (F : Lengths → ℝ) (hc : Continuous F) (hconv : ConvexOn ℝ Set.univ F)
    (hF : ∀ b, HasFDerivAt F (extendedDifferential b) b)
    (A : T → Lengths) (hA : ∀ t, genuine (A t)) :
    ∃ p : E → ℝ, (∀ e : E, 0 < p e) ∧
      ∀ e : E, signedCone s p e = realizedConeTarget s A e := by
  obtain ⟨p,hp⟩ := (signedEnergy_realized_coercive_minimum s hobs F hc hconv hF A hA).2
  have heq := minimum_cone_equations s F hF (realizedConeTarget s A) p hp
  exact ⟨p,positive_of_cone_equations s p (realizedConeTarget s A)
    (realizedConeTarget_positive s hobs A hA) heq,heq⟩

/-- The variational construction keeps the original physical calibration;
arbitrary-angle inverse realization remains a separate obligation. -/
theorem exists_actual_positive_realized_cone (a0 : Lengths) (ha0 : genuine a0)
    (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (A : T → Lengths) (hA : ∀ t, genuine (A t)) :
    ∃ F : Lengths → ℝ, ContDiff ℝ 1 F ∧ ConvexOn ℝ Set.univ F ∧
      (∀ b, HasFDerivAt F (extendedDifferential b) b) ∧
      (∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn F (physicalCovolume G) {a | genuine a}) ∧
      ∃ p : E → ℝ, (∀ e : E, 0 < p e) ∧
        ∀ e : E, signedCone s p e = realizedConeTarget s A e := by
  obtain ⟨F,hC,hconv,hder,hpart,heq,hphysical,hflat⟩ :=
    exists_actual_signed_C1_convex_extension a0 ha0
  exact ⟨F,hC,hconv,hder,hphysical,
    exists_positive_realized_cone_solution s hobs F hC.continuous hconv hder A hA⟩

end CFMPActualPrescribedCone295Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPrescribedCone295Transient.signedEnergy_realized_coercive_minimum,
      ``CFMPActualPrescribedCone295Transient.signedEnergy_hasFDerivAt,
      ``CFMPActualPrescribedCone295Transient.minimum_cone_equations,
      ``CFMPActualPrescribedCone295Transient.positive_of_cone_equations,
      ``CFMPActualPrescribedCone295Transient.exists_actual_positive_realized_cone] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP295 actual realized prescribed-cone theorem absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP295 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP295 CHECKED {name} axioms={axioms}"
