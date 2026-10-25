import CFMPActualPrescribedResidual265Transient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualGlobalEnergy259Transient
open CFMPActualPhysicalMinimum262Transient
open CFMPActualPrescribedResidual265Transient

namespace CFMPFourCyclePhysicalUnique266Transient

theorem fourcycle_actual_unique_prescribed_minimum
    (T E : Type*) [Fintype T] [DecidableEq E]
    (s : Incidence T E) (hs : FourCycle s) :
    let a : E → ℝ := fun e => Real.arcosh (lower s e)
    let b : E → ℝ := fun e => Real.arcosh (upper s e)
    ∃ inst : Fintype E, letI := inst
      ∃ G : RealizationFamily, realizedFamily G ∧
        ∃ mu : ℝ, 0 < mu ∧
          ∀ kappa : E → ℝ, (∀ e : E, |kappa e| < margin) →
            ∃ c ∈ Set.Icc a b,
              IsMinOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) c ∧
              (∀ e : E, a e < c e ∧ c e < b e) ∧ physicalCurvature s c = kappa ∧
              (∀ e : E, 0 < (degree s e : ℝ)) ∧
              ∀ p ∈ Set.Icc a b,
                mu * Real.sqrt (∑ e : E, (degree s e : ℝ) * (p e - c e)^2) ≤
                  Real.sqrt (∑ e : E, (physicalCurvature s p e - kappa e)^2 /
                    (degree s e : ℝ)) ∧
                (physicalCurvature s p = kappa → p = c) ∧
                (IsMinOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) p → p = c) := by
  classical
  obtain ⟨inst,G,hG,hbox,hminimum⟩ :=
    CFMPFourCyclePhysicalMinimum263Transient.fourcycle_actual_prescribed_minimum T E s hs
  letI : Fintype E := inst
  let a : E → ℝ := fun e => Real.arcosh (lower s e)
  let b : E → ℝ := fun e => Real.arcosh (upper s e)
  let C : Set Lengths := ⋃ t : T, localRead s t '' Set.Icc a b
  have hC : IsCompact C := isCompact_iUnion (fun t =>
    isCompact_Icc.image (localRead s t).continuous)
  have hsub : C ⊆ {a : Lengths | genuine a} := by
    intro z hz
    obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hz
    obtain ⟨p,hp,rfl⟩ := ht
    exact (hbox p hp).2 t
  have hreads (p : E → ℝ) (hp : p ∈ Set.Icc a b) (t : T) : localRead s t p ∈ C :=
    Set.mem_iUnion.mpr ⟨t,Set.mem_image_of_mem (localRead s t) hp⟩
  obtain ⟨mu,hmu,hall⟩ := compact_actual_antimonotonicity_and_residual C hC hsub
  obtain ⟨hanti,hresidual⟩ := hall T E s a b hreads
  refine ⟨inst,G,hG,mu,hmu,?_⟩
  intro kappa hkappa
  obtain ⟨c,hc,hmin,hinside,hzero⟩ := hminimum kappa hkappa
  have hkappa_ne (e : E) : kappa e ≠ 2 * Real.pi := by
    intro he
    have hh := (le_abs_self (kappa e)).trans_lt (hkappa e)
    have hm : margin ≤ Real.pi := min_le_left _ _
    rw [he] at hh
    linarith [Real.pi_pos]
  obtain ⟨hdegree,hres⟩ := hresidual kappa c hc hzero hkappa_ne
  refine ⟨c,hc,hmin,hinside,hzero,hdegree,?_⟩
  intro p hp
  refine ⟨(hres p hp).1,(hres p hp).2,?_⟩
  intro hpmin
  have hd := tiltedPhysicalEnergy_hasFDerivAt s G hG kappa p (hbox p hp).2
  have hnormal := hpmin.isLocalMinOn.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset ((convex_Icc a b).segment_subset hp hc))
  have hpair : 0 ≤ ∑ e : E, (physicalCurvature s p e - kappa e) * (p e - c e) := by
    calc
      0 ≤ ∑ e : E, (kappa e - physicalCurvature s p e) * (c e - p e) := by
        simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.proj_apply,smul_eq_mul,Pi.sub_apply] using hnormal
      _ = ∑ e : E, (physicalCurvature s p e - kappa e) * (p e - c e) := by
        apply Finset.sum_congr rfl
        intro e _
        ring
  have hstrong : mu * (∑ e : E, (degree s e : ℝ) * (p e - c e)^2) ≤
      -(∑ e : E, (physicalCurvature s p e - kappa e) * (p e - c e)) := by
    simpa only [hzero] using hanti c hc p hp
  have hmasszero : (∑ e : E, (degree s e : ℝ) * (p e - c e)^2) = 0 := by
    have hnonneg : 0 ≤ ∑ e : E, (degree s e : ℝ) * (p e - c e)^2 :=
      Finset.sum_nonneg (fun e _ => mul_nonneg (hdegree e).le (sq_nonneg _))
    nlinarith
  funext e
  have hterm : (degree s e : ℝ) * (p e - c e)^2 ≤
      ∑ j : E, (degree s j : ℝ) * (p j - c j)^2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hdegree j).le (sq_nonneg (p j - c j)))
      (Finset.mem_univ e)
  have htermzero : (degree s e : ℝ) * (p e - c e)^2 = 0 :=
    le_antisymm (by simpa only [hmasszero] using hterm)
      (mul_nonneg (hdegree e).le (sq_nonneg _))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp
    ((mul_eq_zero.mp htermzero).resolve_left (hdegree e).ne'))

end CFMPFourCyclePhysicalUnique266Transient

run_cmd do
  let name := ``CFMPFourCyclePhysicalUnique266Transient.fourcycle_actual_unique_prescribed_minimum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP266 actual unique FourCycle physical minimum absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP266 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP266 CHECKED {name} axioms={axioms}"
