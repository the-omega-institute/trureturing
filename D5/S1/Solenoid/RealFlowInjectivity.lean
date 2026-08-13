/- GID: D5/S1/Solenoid/RealFlowInjectivity
   generality: I
   mirror-B: D5/B/S1/Solenoid/RealFlowInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The universal-solenoid real flow is faithful. -/

/- Library-search audit trail (2026-08-14):
   * `AddCircle.coe_eq_zero_iff`, `exists_nat_gt`, and
     `Int.abs_lt_one_iff` supply the coordinatewise kernel argument.
   * `injective_iff_map_eq_zero` turns the kernel criterion for the existing
     additive homomorphism into injectivity.
-/

import D5.S1.Dynamics.UniversalSolenoid

namespace D5.S1.Solenoid.RealFlowInjectivity

open D5.S1.Dynamics

/-- A real time maps to the zero point of the universal solenoid exactly when
the time itself is zero. -/
theorem realFlow_eq_zero_iff (t : ℝ) :
    UniversalSolenoid.realFlow t = 0 ↔ t = 0 := by
  constructor
  · intro hflow
    rcases exists_nat_gt |t| with ⟨n, hn⟩
    have hnpos : 0 < n := by
      exact_mod_cast (lt_of_le_of_lt (abs_nonneg t) hn)
    let m : ℕ+ := ⟨n, hnpos⟩
    have hcoordinate := congrArg (fun theta : UniversalSolenoid => theta.1 m) hflow
    change (((t / n : ℝ) : AddCircle (1 : ℝ)) = 0) at hcoordinate
    rcases (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoordinate with ⟨z, hz⟩
    have hzreal : (z : ℝ) = t / n := by
      simpa [zsmul_eq_mul] using hz
    have hzabs : |(z : ℝ)| < 1 := by
      have habsn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
      rw [hzreal, abs_div]
      rw [habsn]
      exact
        (div_lt_one (show (0 : ℝ) < n by positivity)).2 hn
    have hz0 : z = 0 := by
      apply Int.abs_lt_one_iff.mp
      exact_mod_cast hzabs
    rw [hz0, Int.cast_zero] at hzreal
    exact (div_eq_zero_iff.mp hzreal.symm).resolve_right (by positivity)
  · rintro rfl
    exact UniversalSolenoid.realFlow_zero

/-- The universal-solenoid real flow is faithful. -/
theorem realFlow_injective : Function.Injective UniversalSolenoid.realFlow := by
  apply (injective_iff_map_eq_zero UniversalSolenoid.realFlowHom).2
  intro t ht
  exact (realFlow_eq_zero_iff t).1 ht

example :
    UniversalSolenoid.realFlow (1 : ℝ) ≠ UniversalSolenoid.realFlow 0 := by
  intro h
  have : (1 : ℝ) = 0 := realFlow_injective h
  norm_num at this

end D5.S1.Solenoid.RealFlowInjectivity
