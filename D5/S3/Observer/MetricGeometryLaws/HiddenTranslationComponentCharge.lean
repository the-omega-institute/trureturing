/- GID: D5/S3/Observer/MetricGeometryLaws/HiddenTranslationComponentCharge
   generality: I
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/HiddenTranslationComponentCharge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hidden translation changes component iff its canonical charge is nonzero. -/

import D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion
import D5.S1.Solenoid.StreamlineDecomposition

/- Library-search audit trail (2026-08-27):
   * The frozen `same_fiber_path_orbit_criterion` is the canonical path-component
     classification within a visible projection fiber and is applied directly.
   * The frozen `hiddenUnitOffset` is the canonical unit real-flow element in the
     projection kernel; no sibling component generator is introduced here.
   * Pinned Mathlib hits `QuotientAddGroup.eq_zero_iff` and
     `AddSubgroup.mem_zmultiples_iff` identify zero quotient charge with an
     integer multiple. No exact whole-statement theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.HiddenTranslationComponentCharge

open D5.S1.Dynamics
open D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion
open D5.S1.Solenoid.StreamlineDecomposition

private theorem realFlow_int (n : Int) :
    UniversalSolenoid.realFlow (n : Real) =
      n • hiddenUnitOffset.1 := by
  simpa [UniversalSolenoid.realFlowHom, hiddenUnitOffset] using
    UniversalSolenoid.realFlowHom.map_zsmul n (1 : Real)

/-- Translation by a hidden kernel element crosses path components exactly
when that element has nonzero class modulo the canonical integer-flow subgroup. -/
theorem hidden_translation_component_charge
    (x : UniversalSolenoid)
    (kappa : UniversalSolenoid.projection.ker) :
    ¬ Joined x (x + kappa.1) ↔
      QuotientAddGroup.mk'
        (AddSubgroup.zmultiples hiddenUnitOffset) kappa ≠ 0 := by
  have sameProjection :
      UniversalSolenoid.projection x =
        UniversalSolenoid.projection (x + kappa.1) := by
    rw [map_add, kappa.property, add_zero]
  have joined_iff_integer_offset :
      Joined x (x + kappa.1) ↔
        ∃ n : Int, kappa = n • hiddenUnitOffset := by
    rw [same_fiber_path_orbit_criterion x (x + kappa.1) sameProjection]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, Subtype.ext ?_⟩
      apply add_left_cancel (a := x)
      simpa [realFlow_int n, add_comm] using hn
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      simp [realFlow_int n, add_comm]
  have charge_zero_iff_integer_offset :
      QuotientAddGroup.mk'
          (AddSubgroup.zmultiples hiddenUnitOffset) kappa = 0 ↔
        ∃ n : Int, kappa = n • hiddenUnitOffset := by
    change
      (kappa : UniversalSolenoid.projection.ker ⧸
        AddSubgroup.zmultiples hiddenUnitOffset) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff]
    simpa [eq_comm] using
      (AddSubgroup.mem_zmultiples_iff :
        kappa ∈ AddSubgroup.zmultiples hiddenUnitOffset ↔
          ∃ n : Int, n • hiddenUnitOffset = kappa)
  exact not_congr
    (joined_iff_integer_offset.trans charge_zero_iff_integer_offset.symm)

#print axioms hidden_translation_component_charge

end D5.S3.Observer.MetricGeometryLaws.HiddenTranslationComponentCharge
