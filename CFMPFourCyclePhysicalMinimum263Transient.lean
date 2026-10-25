import CFMPActualPhysicalMinimum262Transient
import D5.S3.Geometry.Hyperideal.FourCycleCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualGlobalEnergy259Transient
open CFMPActualPhysicalMinimum262Transient

namespace CFMPFourCyclePhysicalMinimum263Transient

theorem fourcycle_actual_prescribed_minimum
    (T E : Type*) [Fintype T] [DecidableEq E]
    (s : Incidence T E) (hs : FourCycle s) :
    let a : E → ℝ := fun e => Real.arcosh (lower s e)
    let b : E → ℝ := fun e => Real.arcosh (upper s e)
    ∃ inst : Fintype E, letI := inst
      ∃ G : RealizationFamily, realizedFamily G ∧
        (∀ p ∈ Set.Icc a b, (∀ e : E, 0 < p e) ∧ p ∈ globalGenuine s) ∧
        ∀ kappa : E → ℝ, (∀ e : E, |kappa e| < margin) →
          ∃ c ∈ Set.Icc a b,
            IsMinOn (tiltedPhysicalEnergy s G kappa) (Set.Icc a b) c ∧
            (∀ e : E, a e < c e ∧ c e < b e) ∧ physicalCurvature s c = kappa := by
  classical
  have hsurj : Function.Surjective (source s) := by
    intro e
    have hpos : 0 < degree s e := by
      cases he : s.low e with
      | false => have h := hs.2.2 e he; omega
      | true => rw [hs.2.1 e he]; norm_num
    obtain ⟨o,ho⟩ := Finset.card_pos.mp hpos
    exact ⟨o,(Finset.mem_filter.mp ho).2⟩
  letI : Fintype E := Fintype.ofSurjective (source s) hsurj
  let a : E → ℝ := fun e => Real.arcosh (lower s e)
  let b : E → ℝ := fun e => Real.arcosh (upper s e)
  refine ⟨inferInstance,wholeFamily,wholeFamily_realized,?_⟩
  obtain ⟨hdelta,hdelta8,hmargin,hbase,hfaces⟩ := fourcycle_curvature_box s hs
  have hlo (e : E) : 1 < lower s e := by
    unfold lower
    split_ifs <;> linarith
  have hhi (e : E) : 1 < upper s e := by
    unfold upper
    split_ifs <;> norm_num
  have hwidthx (e : E) : lower s e < upper s e := by
    unfold lower upper
    split_ifs <;> linarith
  have hwidth (e : E) : a e < b e :=
    (Real.arcosh_lt_arcosh (lt_trans (by norm_num) (hlo e))
      (lt_trans (by norm_num) (hhi e))).mpr (hwidthx e)
  have ha (e : E) : 0 < a e := Real.arcosh_pos (hlo e)
  have hb (e : E) : 0 < b e := Real.arcosh_pos (hhi e)
  have hpos (p : E → ℝ) (hp : p ∈ Set.Icc a b) (e : E) : 0 < p e :=
    (ha e).trans_le (hp.1 e)
  have hbox (p : E → ℝ) (hp : p ∈ Set.Icc a b) :
      Box s (fun e => Real.cosh (p e)) := by
    intro e
    constructor
    · calc
        lower s e = Real.cosh (a e) := (Real.cosh_arcosh (hlo e).le).symm
        _ ≤ Real.cosh (p e) :=
          Real.cosh_strictMonoOn.monotoneOn (ha e).le (hpos p hp e).le (hp.1 e)
    · calc
        Real.cosh (p e) ≤ Real.cosh (b e) :=
          Real.cosh_strictMonoOn.monotoneOn (hpos p hp e).le (hb e).le (hp.2 e)
        _ = upper s e := Real.cosh_arcosh (hhi e).le
  have hgenuine (p : E → ℝ) (hp : p ∈ Set.Icc a b) : p ∈ globalGenuine s := by
    intro t
    refine ⟨fun q => hpos p hp (s.edge t q),?_⟩
    intro q
    have h := (hfaces (fun e => Real.cosh (p e)) (hbox p hp)).1 (t,q)
    simpa only [sourceCosine,D5.S3.Geometry.Hyperideal.TwoLengthAngleSum.rawCos,
      localCosine,coordinate,localRead, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.proj_apply] using h
  constructor
  · intro p hp
    exact ⟨hpos p hp,hgenuine p hp⟩
  · intro kappa hkappa
    apply exists_prescribed_physical_box_minimum s wholeFamily wholeFamily_realized
      kappa a b hwidth (fun _ hp => hgenuine _ hp)
    · intro p hp e he
      have hm : margin ≤ physicalCurvature s p e := by
        apply ((hfaces (fun j => Real.cosh (p j)) (hbox p hp)).2 e).1
        rw [he]
        exact Real.cosh_arcosh (hlo e).le
      exact ((le_abs_self (kappa e)).trans_lt (hkappa e)).trans_le hm
    · intro p hp e he
      have hm : physicalCurvature s p e ≤ -margin := by
        apply ((hfaces (fun j => Real.cosh (p j)) (hbox p hp)).2 e).2
        rw [he]
        exact Real.cosh_arcosh (hhi e).le
      exact hm.trans_lt (abs_lt.mp (hkappa e)).1

end CFMPFourCyclePhysicalMinimum263Transient

run_cmd do
  let name := ``CFMPFourCyclePhysicalMinimum263Transient.fourcycle_actual_prescribed_minimum
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP263 original FourCycle actual physical minimizer absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP263 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP263 CHECKED {name} axioms={axioms}"
