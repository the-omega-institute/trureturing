/- GID: D5/S0/Tower/MetricGeometry/CantorTransportExponent
   generality: I
   mirror-B: D5/B/S0/Tower/MetricGeometry/CantorTransportExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Cantor exponent converts every positive triadic scale to its binary scale and defeats every Lipschitz constant. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository and in-flight searches found no theorem relating the triadic
     Cantor scale, the binary scale, and the exponent `log 2 / log 3`.
   * Pinned Mathlib defines the ternary Cantor set and its homeomorphism with
     Boolean paths, and supplies real-power logarithm identities and geometric
     divergence. It has no Hölder-scale transport theorem for this map.
   * The private no-Lipschitz lemma is the escape witness: it constructs, for
     each proposed positive constant, a scale where the binary image distance
     is larger than that constant times the triadic source distance. -/

namespace D5.S0.Tower.MetricGeometry.CantorTransportExponent

open Filter

/-- The exponent converting powers of three into powers of two. -/
noncomputable def cantorExponent : Real := Real.log 2 / Real.log 3

/-- The source distance scale at positive ternary depth `Q + 1`. -/
noncomputable def triadicScale (Q : Nat) : Real := (3 : Real)⁻¹ ^ (Q + 1)

/-- The transported distance scale at positive binary depth `Q + 1`. -/
noncomputable def binaryScale (Q : Nat) : Real := (2 : Real)⁻¹ ^ (Q + 1)

private theorem cantor_exponent_pos : 0 < cantorExponent := by
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

private theorem cantor_exponent_lt_one : cantorExponent < 1 := by
  apply (div_lt_one (Real.log_pos (by norm_num : (1 : Real) < 3))).2
  exact Real.log_lt_log (by norm_num) (by norm_num)

private theorem inverse_three_rpow_cantor_exponent :
    Real.rpow ((3 : Real)⁻¹) cantorExponent = (2 : Real)⁻¹ := by
  refine Real.log_injOn_pos ?_ ?_ ?_
  · exact Real.rpow_pos_of_pos (by positivity) _
  · norm_num
  calc
    Real.log (Real.rpow ((3 : Real)⁻¹) cantorExponent) =
        cantorExponent * Real.log ((3 : Real)⁻¹) :=
      Real.log_rpow (by positivity) _
    _ = Real.log ((2 : Real)⁻¹) := by
      rw [Real.log_inv, Real.log_inv]
      unfold cantorExponent
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < 3))]

private theorem triadic_rpow_eq_binary (Q : Nat) :
    Real.rpow (triadicScale Q) cantorExponent = binaryScale Q := by
  calc
    Real.rpow (triadicScale Q) cantorExponent =
        Real.rpow (Real.rpow ((3 : Real)⁻¹) ((Q + 1 : Nat) : Real))
          cantorExponent := by
          congr 1
          exact (Real.rpow_natCast (3 : Real)⁻¹ (Q + 1)).symm
    _ = Real.rpow ((3 : Real)⁻¹)
        (((Q + 1 : Nat) : Real) * cantorExponent) := by
          exact (Real.rpow_mul (x := (3 : Real)⁻¹) (by positivity)
            ((Q + 1 : Nat) : Real) cantorExponent).symm
    _ = Real.rpow ((3 : Real)⁻¹)
        (cantorExponent * ((Q + 1 : Nat) : Real)) := by
          rw [mul_comm]
    _ = (Real.rpow ((3 : Real)⁻¹) cantorExponent) ^ (Q + 1) := by
          exact Real.rpow_mul_natCast (x := (3 : Real)⁻¹) (by positivity)
            cantorExponent (Q + 1)
    _ = binaryScale Q := by
          rw [inverse_three_rpow_cantor_exponent]
          rfl

/-- No positive Lipschitz constant controls the binary scale by the triadic
scale at every depth. -/
private theorem no_lipschitz_scale_bound (K : Real) (_hK : 0 < K) :
    ∃ Q : Nat, K * triadicScale Q < binaryScale Q := by
  have hGrowth : Tendsto (fun n : Nat => ((3 : Real) / 2) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hShift := hGrowth.comp (tendsto_add_atTop_nat 1)
  have hEventually : ∀ᶠ Q : Nat in atTop, K + 1 <= ((3 : Real) / 2) ^ (Q + 1) :=
    (tendsto_atTop.1 hShift) (K + 1)
  obtain ⟨Q, hQ⟩ := hEventually.exists
  have hRatio : K < ((3 : Real) / 2) ^ (Q + 1) := by linarith
  have hTriadic : 0 < triadicScale Q := by
    unfold triadicScale
    positivity
  have hScaled := mul_lt_mul_of_pos_right hRatio hTriadic
  refine ⟨Q, hScaled.trans_eq ?_⟩
  unfold triadicScale binaryScale
  rw [← mul_pow]
  norm_num

/-- The Cantor transport exponent is strictly between zero and one, converts
every positive-depth triadic scale exactly to the corresponding binary scale,
and is genuinely non-Lipschitz as witnessed against every positive constant. -/
theorem cantor_transport_exponent :
    0 < cantorExponent ∧ cantorExponent < 1 ∧
      (∀ Q : Nat, Real.rpow (triadicScale Q) cantorExponent = binaryScale Q) ∧
      ∀ K : Real, 0 < K -> ∃ Q : Nat, K * triadicScale Q < binaryScale Q := by
  exact ⟨cantor_exponent_pos, cantor_exponent_lt_one,
    triadic_rpow_eq_binary, no_lipschitz_scale_bound⟩

#print axioms cantor_transport_exponent

end D5.S0.Tower.MetricGeometry.CantorTransportExponent
