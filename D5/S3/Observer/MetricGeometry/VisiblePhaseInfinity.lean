/- GID: D5/S3/Observer/MetricGeometry/VisiblePhaseInfinity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: ENNReal observer distance is top across distinct visible phases. -/

import D5.S1.Dynamics.UniversalSolenoid
import D5.S1.Solenoid.StreamlineDecomposition
import D5.S3.Observer.ObserverMetric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.ContinuousMap.Algebra

namespace D5.S3.Observer.MetricGeometry.VisiblePhaseInfinity

open D5.S1.Dynamics
open D5.S3.Observer.ObserverMetric

abbrev Observable := C(UniversalSolenoid, ℂ)

def admissibleObservable (tau : Equiv.Perm UniversalSolenoid) : Set Observable :=
  {f | ∀ z, ‖f (tau.symm z) - f z‖ ≤ 1}

noncomputable def observerExtendedDistance (tau : Equiv.Perm UniversalSolenoid)
    (x y : UniversalSolenoid) : ENNReal :=
  ⨆ f : admissibleObservable tau, ENNReal.ofReal ‖f.1 x - f.1 y‖

noncomputable def visiblePhaseObservable : Observable :=
  ⟨fun z => (AddCircle.toCircle (UniversalSolenoid.projection z) : ℂ),
    (continuous_subtype_val.comp AddCircle.continuous_toCircle).comp
      UniversalSolenoid.continuous_projection⟩

private theorem visiblePhaseObservable_apply (z : UniversalSolenoid) :
    visiblePhaseObservable z = (AddCircle.toCircle (UniversalSolenoid.projection z) : ℂ) := by
  rfl

private theorem visiblePhaseObservable_update (tau : Equiv.Perm UniversalSolenoid)
    (hphase : ∀ z, UniversalSolenoid.projection (tau.symm z) =
      UniversalSolenoid.projection z) :
    ∀ z, visiblePhaseObservable (tau.symm z) = visiblePhaseObservable z := by
  intro z
  rw [visiblePhaseObservable_apply, visiblePhaseObservable_apply, hphase]

private theorem visiblePhaseObservable_separates {x y : UniversalSolenoid}
    (hxy : UniversalSolenoid.projection x ≠ UniversalSolenoid.projection y) :
    ‖visiblePhaseObservable x - visiblePhaseObservable y‖ > 0 := by
  have hcircle : (AddCircle.toCircle (UniversalSolenoid.projection x) : ℂ) ≠
      (AddCircle.toCircle (UniversalSolenoid.projection y) : ℂ) := by
    intro h
    have hne : UniversalSolenoid.projection x ≠ UniversalSolenoid.projection y := by
      simpa using hxy
    apply hne
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)
  rw [visiblePhaseObservable_apply, visiblePhaseObservable_apply]
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hcircle)

noncomputable def hiddenTranslation : Equiv.Perm UniversalSolenoid :=
  Equiv.addRight D5.S1.Solenoid.StreamlineDecomposition.hiddenUnitOffset.1

theorem hiddenTranslation_nonidentity : hiddenTranslation ≠ Equiv.refl _ := by
  intro h
  have hzero := congrArg (fun e : Equiv.Perm UniversalSolenoid => e 0) h
  apply D5.S1.Solenoid.StreamlineDecomposition.hiddenUnitOffset_ne_zero
  simpa [hiddenTranslation] using hzero

theorem hiddenTranslation_preserves_phase : ∀ z,
    UniversalSolenoid.projection (hiddenTranslation.symm z) =
      UniversalSolenoid.projection z := by
  intro z
  simp [hiddenTranslation, D5.S1.Solenoid.StreamlineDecomposition.hiddenUnitOffset]

private theorem scaled_visiblePhaseObservable_mem (tau : Equiv.Perm UniversalSolenoid)
    (hphase : ∀ z, UniversalSolenoid.projection (tau.symm z) =
      UniversalSolenoid.projection z) (n : ℕ) :
    (n : ℂ) • visiblePhaseObservable ∈ admissibleObservable tau := by
  intro z
  change ‖(n : ℂ) * visiblePhaseObservable (tau.symm z) -
    (n : ℂ) * visiblePhaseObservable z‖ ≤ 1
  rw [visiblePhaseObservable_update tau hphase z]
  simp

theorem visible_phase_separation_distance_eq_top (tau : Equiv.Perm UniversalSolenoid)
    (hphase : ∀ z, UniversalSolenoid.projection (tau.symm z) =
      UniversalSolenoid.projection z) {x y : UniversalSolenoid}
    (hxy : UniversalSolenoid.projection x ≠ UniversalSolenoid.projection y) :
    observerExtendedDistance tau x y = ⊤ := by
  apply iSup_eq_top.mpr
  intro b hb
  let gap : ℝ := ‖visiblePhaseObservable x - visiblePhaseObservable y‖
  have hgap : 0 < gap := visiblePhaseObservable_separates hxy
  obtain ⟨m, hm⟩ := exists_nat_gt (b.toReal / gap)
  refine ⟨⟨(m : ℂ) • visiblePhaseObservable,
    scaled_visiblePhaseObservable_mem tau hphase m⟩, ?_⟩
  simp only [ContinuousMap.smul_apply]
  rw [← smul_sub]
  change b < ENNReal.ofReal (‖(m : ℂ) *
    (visiblePhaseObservable x - visiblePhaseObservable y)‖)
  rw [norm_mul, Complex.norm_natCast]
  apply (ENNReal.lt_ofReal_iff_toReal_lt hb.ne).mpr
  simpa [gap] using (div_lt_iff₀ hgap).mp hm

theorem visible_phase_separation_witness (x y : UniversalSolenoid)
    (hxy : UniversalSolenoid.projection x ≠ UniversalSolenoid.projection y) :
    visiblePhaseObservable x ≠ visiblePhaseObservable y := by
  intro h
  rw [visiblePhaseObservable_apply, visiblePhaseObservable_apply] at h
  exact hxy (AddCircle.injective_toCircle one_ne_zero (Subtype.ext h))

theorem hiddenTranslation_visible_phase_witness :
    ∃ tau : Equiv.Perm UniversalSolenoid,
      tau ≠ Equiv.refl _ ∧
        (∀ z, UniversalSolenoid.projection (tau.symm z) =
          UniversalSolenoid.projection z) ∧
        UniversalSolenoid.projection (UniversalSolenoid.realFlow 0) ≠
          UniversalSolenoid.projection (UniversalSolenoid.realFlow (1 / 2 : ℝ)) ∧
        observerExtendedDistance tau (UniversalSolenoid.realFlow 0)
          (UniversalSolenoid.realFlow (1 / 2 : ℝ)) = ⊤ := by
  refine ⟨hiddenTranslation, hiddenTranslation_nonidentity,
    hiddenTranslation_preserves_phase, ?_, ?_⟩
  · rw [UniversalSolenoid.projection_realFlow, UniversalSolenoid.projection_realFlow]
    intro h
    have hzero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simpa using h.symm
    rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero with ⟨z, hz⟩
    have hz' : (z : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hz
    have : (2 : ℤ) * z = 1 := by
      exact_mod_cast (show (2 : ℝ) * z = 1 by linarith)
    omega
  · apply visible_phase_separation_distance_eq_top hiddenTranslation
      hiddenTranslation_preserves_phase
    rw [UniversalSolenoid.projection_realFlow, UniversalSolenoid.projection_realFlow]
    intro h
    have hzero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simpa using h.symm
    rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero with ⟨z, hz⟩
    have hz' : (z : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hz
    have : (2 : ℤ) * z = 1 := by
      exact_mod_cast (show (2 : ℝ) * z = 1 by linarith)
    omega

end D5.S3.Observer.MetricGeometry.VisiblePhaseInfinity
