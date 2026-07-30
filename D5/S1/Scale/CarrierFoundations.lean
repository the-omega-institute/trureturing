/- GID: D5/S1/Scale/CarrierFoundations
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frozen proofs assemble conjugation, norm, units, and unique factorization. -/

import D5.S0.Carrier.PrincipalIdeal
import D5.S1.Scale.Units

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The conjugation, multiplicative norm, unit classification, and PID/UFD
structure of the golden integer carrier, assembled from their frozen proofs. -/
theorem golden_carrier_foundations :
    (Exists fun sigma : GoldenInt ≃+* GoldenInt =>
      (forall x, sigma x = conj x) ∧ forall x, sigma (sigma x) = x) ∧
    (forall x y : GoldenInt, norm (x * y) = norm x * norm y) ∧
    ((forall x : GoldenInt,
      IsUnit x ↔ Exists fun s : Bool => Exists fun n : Int =>
        x = signedPhiPower s n) ∧
      norm phi = -1) ∧
    (IsPrincipalIdealRing GoldenInt ∧ UniqueFactorizationMonoid GoldenInt) := by
  refine ⟨?_, norm_mul, ?_, ?_⟩
  · exact ⟨conjEquiv, fun _ => rfl, conj_involutive⟩
  · exact ⟨golden_units_eq_signed_phi_pow, norm_phi⟩
  · exact ⟨golden_int_is_pid, golden_int_is_ufd⟩

end D5.S1.Scale
