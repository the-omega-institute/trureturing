import CFMPActualCompactHessian261Transient
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
universe u262 v262
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualGlobalEnergy259Transient

namespace CFMPActualPhysicalMinimum262Transient

variable {T : Type u262} {E : Type v262}
  [Fintype T] [Fintype E] [DecidableEq E]

def tiltedPhysicalEnergy (s : Incidence T E) (G : RealizationFamily)
    (kappa p : E → ℝ) : ℝ := physicalEnergy s G p + ∑ e : E, kappa e * p e

theorem tiltedPhysicalEnergy_hasFDerivAt
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (kappa p : E → ℝ) (hp : p ∈ globalGenuine s) :
    HasFDerivAt (tiltedPhysicalEnergy s G kappa)
      (∑ e : E, (kappa e - physicalCurvature s p e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
  classical
  have hlin : HasFDerivAt (fun a : E → ℝ => ∑ e : E, kappa e * a e)
      (∑ e : E, kappa e • (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) p := by
    exact HasFDerivAt.fun_sum (fun e _ =>
      (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_mul (kappa e))
  have hmap :
      (∑ e : E, (-physicalCurvature s p e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) +
      (∑ e : E, kappa e • (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) =
      ∑ e : E, (kappa e - physicalCurvature s p e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [← add_smul]
    congr 1
    ring
  rw [← hmap]
  exact (physicalEnergy_hasFDerivAt s G hG p hp).add hlin

theorem physical_box_minimum_characterization
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (kappa a b : E → ℝ) (hwidth : ∀ e : E, a e < b e)
    (hreads : Set.Icc a b ⊆ globalGenuine s)
    (hlower : ∀ p ∈ Set.Icc a b, ∀ e, p e = a e →
      kappa e < physicalCurvature s p e)
    (hupper : ∀ p ∈ Set.Icc a b, ∀ e, p e = b e →
      physicalCurvature s p e < kappa e)
    (c : E → ℝ) (hc : c ∈ Set.Icc a b)
    (hmin : IsMinOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) c) :
    (∀ e : E, a e < c e ∧ c e < b e) ∧ physicalCurvature s c = kappa := by
  classical
  have hd := tiltedPhysicalEnergy_hasFDerivAt s G hG kappa c (hreads hc)
  have hnormal (y : E → ℝ) (hy : y ∈ Set.Icc a b) :
      0 ≤ (∑ e : E, (kappa e - physicalCurvature s c e) •
        (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ)) (y-c) :=
    hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc a b).segment_subset hc hy))
  have hdir (e : E) (r : ℝ) (hr : a e ≤ r ∧ r ≤ b e) :
      0 ≤ (kappa e - physicalCurvature s c e) * (r - c e) := by
    have hy : Function.update c e r ∈ Set.Icc a b := by
      constructor
      · intro j
        by_cases hj : j = e
        · subst j
          simpa using hr.1
        · simpa [Function.update_of_ne hj] using hc.1 j
      · intro j
        by_cases hj : j = e
        · subst j
          simpa using hr.2
        · simpa [Function.update_of_ne hj] using hc.2 j
    have hdelta : Function.update c e r - c = (r-c e) • Pi.single e (1 : ℝ) := by
      ext j
      by_cases hj : j = e
      · subst j
        simp
      · simp [Function.update_of_ne hj,Pi.single_apply,hj,Ne.symm hj]
    have hh := hnormal (Function.update c e r) hy
    rw [hdelta] at hh
    simpa [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,Pi.single_apply,mul_comm] using hh
  have hinside : ∀ e : E, a e < c e ∧ c e < b e := by
    intro e
    constructor
    · by_contra h
      have heq : c e = a e := le_antisymm (le_of_not_gt h) (hc.1 e)
      have hK := hlower c hc e heq
      have hh := hdir e (b e) ⟨(hwidth e).le,le_rfl⟩
      have hnegative : (kappa e - physicalCurvature s c e) * (b e-c e) < 0 :=
        mul_neg_of_neg_of_pos (sub_neg.mpr hK) (by rw [heq]; exact sub_pos.mpr (hwidth e))
      exact (not_le_of_gt hnegative) hh
    · by_contra h
      have heq : c e = b e := le_antisymm (hc.2 e) (le_of_not_gt h)
      have hK := hupper c hc e heq
      have hh := hdir e (a e) ⟨le_rfl,(hwidth e).le⟩
      have hnegative : (kappa e - physicalCurvature s c e) * (a e-c e) < 0 :=
        mul_neg_of_pos_of_neg (sub_pos.mpr hK) (by rw [heq]; exact sub_neg.mpr (hwidth e))
      exact (not_le_of_gt hnegative) hh
  refine ⟨hinside,?_⟩
  funext e
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := hdir e (a e) ⟨le_rfl,(hwidth e).le⟩
    have hnegative : (kappa e - physicalCurvature s c e) * (a e-c e) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (sub_neg.mpr (hinside e).1)
    exact (not_le_of_gt hnegative) hh
  · have hh := hdir e (b e) ⟨(hwidth e).le,le_rfl⟩
    have hnegative : (kappa e - physicalCurvature s c e) * (b e-c e) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hgt) (sub_pos.mpr (hinside e).2)
    exact (not_le_of_gt hnegative) hh

theorem exists_prescribed_physical_box_minimum
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (kappa a b : E → ℝ) (hwidth : ∀ e : E, a e < b e)
    (hreads : Set.Icc a b ⊆ globalGenuine s)
    (hlower : ∀ p ∈ Set.Icc a b, ∀ e, p e = a e →
      kappa e < physicalCurvature s p e)
    (hupper : ∀ p ∈ Set.Icc a b, ∀ e, p e = b e →
      physicalCurvature s p e < kappa e) :
    ∃ c ∈ Set.Icc a b,
      IsMinOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) c ∧
      (∀ e : E, a e < c e ∧ c e < b e) ∧ physicalCurvature s c = kappa := by
  have hcont : ContinuousOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) := by
    apply ((physicalEnergy_smoothOn s G hG).continuousOn.mono hreads).add
    fun_prop
  have hne : (Set.Icc a b).Nonempty :=
    ⟨a,le_rfl,fun e => (hwidth e).le⟩
  obtain ⟨c,hc,hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  have hchar := physical_box_minimum_characterization s G hG kappa a b
    hwidth hreads hlower hupper c hc hmin
  exact ⟨c,hc,hmin,hchar.1,hchar.2⟩

theorem exists_zero_physical_box_minimum
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (a b : E → ℝ) (hwidth : ∀ e : E, a e < b e)
    (hreads : Set.Icc a b ⊆ globalGenuine s)
    (hlower : ∀ p ∈ Set.Icc a b, ∀ e, p e = a e → 0 < physicalCurvature s p e)
    (hupper : ∀ p ∈ Set.Icc a b, ∀ e, p e = b e → physicalCurvature s p e < 0) :
    ∃ c ∈ Set.Icc a b,
      IsMinOn (physicalEnergy s G) (Set.Icc a b) c ∧
      (∀ e : E, a e < c e ∧ c e < b e) ∧ physicalCurvature s c = 0 := by
  have hz : tiltedPhysicalEnergy s G (0 : E → ℝ) = physicalEnergy s G := by
    funext p
    simp [tiltedPhysicalEnergy]
  simpa only [hz] using exists_prescribed_physical_box_minimum s G hG
    (0 : E → ℝ) a b hwidth hreads hlower hupper

end CFMPActualPhysicalMinimum262Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualPhysicalMinimum262Transient.physical_box_minimum_characterization,
      ``CFMPActualPhysicalMinimum262Transient.exists_prescribed_physical_box_minimum,
      ``CFMPActualPhysicalMinimum262Transient.exists_zero_physical_box_minimum] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP262 actual physical minimizer theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP262 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP262 CHECKED {name} axioms={axioms}"
