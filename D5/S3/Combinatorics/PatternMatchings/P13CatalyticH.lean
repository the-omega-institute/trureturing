/- GID: D5/S3/Combinatorics/PatternMatchings/P13CatalyticH
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13CatalyticH
   mirror-E: none(waiver:actual-catalytic-change-of-variables)
   anchors: []
   utility: none
   digest: The actual matching series satisfies the rational catalytic H equation. -/
import D5.S3.Combinatorics.PatternMatchings.P13Series
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace D5.S3.Combinatorics.PatternMatchings.P13
namespace CatalyticH

open PowerSeries PowerSeries.WithPiTopology
open scoped PowerSeries.WithPiTopology
local instance : UniformSpace ℚ := ⊥
local instance : UniformSpace (Polynomial ℚ) := ⊥

noncomputable section
abbrev S := PowerSeries (Polynomial ℚ)

def q : S := X
def t : S := C Polynomial.X
def Cq : S := 1 + q
def delta : S := (1 - q)^2
/-- The inverse of 1+q, from the existing negative-binomial unit. -/
def invCq : S := rescale (-1 : Polynomial ℚ) (invOneSubPow (Polynomial ℚ) 1).val
def zeta : S := q * invCq^2
/-- Unit inversion works for every inner marker, regardless of its constant term. -/
def inverseDenominator (v : S) : S := invOfUnit (1 - q * v) 1
/-- The concrete rational change of the polynomial coefficient variable. -/
def u (v : S) : S := Cq * (1 - v) * inverseDenominator v

private theorem inverse_unique {d a b : S} (ha : d * a = 1) (hb : d * b = 1) :
    a = b := by
  calc
    a = a * (d * b) := by rw [hb, mul_one]
    _ = (d * a) * b := by ring
    _ = b := by rw [ha, one_mul]

private theorem cancel_unit {a b d v : S} (hd : d * v = 1)
    (h : a * d = b * d) : a = b := by
  calc
    a = a * (d * v) := by rw [hd, mul_one]
    _ = (a * d) * v := by ring
    _ = (b * d) * v := by rw [h]
    _ = b * (d * v) := by ring
    _ = b := by rw [hd, mul_one]

private theorem invCq_unit : Cq * invCq = 1 := by
  have h := (invOneSubPow (Polynomial ℚ) 1).inv_val
  rw [invOneSubPow_inv_eq_one_sub_pow, pow_one] at h
  have hr := congrArg (rescale (-1 : Polynomial ℚ)) h
  simpa [invCq, Cq, q, map_mul, map_sub, rescale_X] using hr

private theorem denominator_unit (v : S) :
    (1 - q * v) * inverseDenominator v = 1 := by
  apply mul_invOfUnit
  simp [q]

private theorem denominator_square_unit (v : S) :
    (1 - q * v)^2 * (inverseDenominator v)^2 = 1 := by
  calc
    _ = ((1 - q * v) * inverseDenominator v)^2 := by ring
    _ = 1 := by rw [denominator_unit, one_pow]

private theorem zeta_Cq_sq : zeta * Cq^2 = q := by
  calc
    _ = q * (Cq * invCq)^2 := by unfold zeta; ring
    _ = q := by rw [invCq_unit]; ring

private theorem u_denominator (v : S) : u v * (1 - q * v) = Cq * (1 - v) := by
  calc
    _ = Cq * (1 - v) * ((1 - q * v) * inverseDenominator v) := by unfold u; ring
    _ = Cq * (1 - v) := by rw [denominator_unit, mul_one]

private theorem hasEval_zeta : HasEval zeta :=
  HasEval.mul_right (invCq^2) (HasEval.X (R := Polynomial ℚ))

private def coefficientEval (v : S) : Polynomial ℚ →+* S :=
  Polynomial.eval₂RingHom (C.comp Polynomial.C) v

private noncomputable def blockEval (v : S) : S →+* S :=
  eval₂Hom (show Continuous (coefficientEval v) from continuous_of_discreteTopology)
    (HasEval.X (R := Polynomial ℚ))

private theorem blockEval_eq_evaluateBlock (v : S) : blockEval v = evaluateBlock v := rfl

/-- Evaluate the polynomial coefficients at v and only the outer variable at a. -/
def jointEval (v a : S) (ha : HasEval a) : S →+* S :=
  eval₂Hom (show Continuous (coefficientEval v) from continuous_of_discreteTopology) ha

private theorem joint_X (v a : S) (ha : HasEval a) : jointEval v a ha X = a := by
  simp only [jointEval, coe_eval₂Hom, eval₂_X]
private theorem joint_C (v a : S) (ha : HasEval a) (p : Polynomial ℚ) :
    jointEval v a ha (C p) = coefficientEval v p := by
  simp only [jointEval, coe_eval₂Hom, eval₂_C]
private theorem joint_t (v a : S) (ha : HasEval a) : jointEval v a ha t = v := by
  rw [t, joint_C]
  simp [coefficientEval]
private theorem continuous_joint (v a : S) (ha : HasEval a) :
    Continuous (jointEval v a ha) := by
  simpa only [jointEval, coe_eval₂Hom] using
    continuous_eval₂ (show Continuous (coefficientEval v) from continuous_of_discreteTopology) ha

/-- This is F(u(t), zeta), with F from the literal completion carrier. -/
def H : S := jointEval (u t) zeta hasEval_zeta completionBivariate
/-- The original matching series A, embedded and evaluated at zeta. -/
def Aq : S := jointEval (u t) zeta hasEval_zeta (actualSeries.map Polynomial.C)
/-- The actual substitution t -> q*t, using the supplier's public polynomial evaluation. -/
def shift : S →+* S := blockEval (q * t)

private theorem shift_joint : shift = jointEval (q * t) X (HasEval.X (R := Polynomial ℚ)) := rfl
private theorem shift_X : shift X = X := by rw [shift_joint]; exact joint_X _ _ _
private theorem shift_q : shift q = q := shift_X
private theorem shift_t : shift t = q * t := by rw [shift_joint]; exact joint_t _ _ _
private theorem shift_Cq : shift Cq = Cq := by simp only [Cq, map_add, map_one, shift_q]
private theorem shift_invCq : shift invCq = invCq := by
  apply inverse_unique (d := Cq)
  · simpa only [map_mul, shift_Cq, map_one] using congrArg shift invCq_unit
  · exact invCq_unit
private theorem shift_zeta : shift zeta = zeta := by
  simp only [zeta, map_mul, map_pow, shift_q, shift_invCq]
private theorem shift_denominator : shift (inverseDenominator t) = inverseDenominator (q*t) := by
  apply inverse_unique (d := 1 - q*(q*t))
  · simpa only [map_mul, map_sub, map_one, shift_q, shift_t] using
      congrArg shift (denominator_unit t)
  · exact denominator_unit _
private theorem shift_u : shift (u t) = u (q*t) := by
  simp only [u, map_mul, map_sub, map_one, shift_Cq, shift_t, shift_denominator]

private theorem shift_H : shift H = jointEval (u (q*t)) zeta hasEval_zeta completionBivariate := by
  have hc := comp_eval₂
    (show Continuous (coefficientEval (u t)) from continuous_of_discreteTopology)
    hasEval_zeta (ε := shift) (by rw [shift_joint]; exact continuous_joint _ _ _)
  have hp : shift.comp (coefficientEval (u t)) = coefficientEval (u (q*t)) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [coefficientEval, shift_joint, jointEval, coe_eval₂Hom]
    · simp [coefficientEval, shift_u]
  have he := congrFun hc completionBivariate
  rw [hp, shift_zeta] at he
  simpa only [Function.comp_apply, H, jointEval, coe_eval₂Hom] using he

private theorem reciprocal_specialization :
    jointEval (u t) zeta hasEval_zeta reciprocalMarker = u (q*t) := by
  let J := jointEval (u t) zeta hasEval_zeta
  have hj : (1 - zeta * u t) * J reciprocalMarker = 1 := by
    have hunit := (completion_functional_equation).2.2.2.2.1
    have he := congrArg J hunit
    change J ((1 - X * C Polynomial.X) * reciprocalMarker) = J 1 at he
    simpa only [map_mul, map_sub, map_one, J, joint_X, joint_C,
      coefficientEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using he
  have hu := u_denominator t
  have hc := zeta_Cq_sq
  have hs : (1 - zeta * u t) * (Cq * (1-q*t)) = 1 - q*(q*t) := by
    calc
      _ = Cq * (1-q*t) - zeta * Cq * (u t * (1-q*t)) := by ring
      _ = Cq * (1-q*t) - zeta * Cq^2 * (1-t) := by rw [hu]; ring
      _ = Cq * (1-q*t) - q * (1-t) := by rw [hc]
      _ = 1 - q*(q*t) := by unfold Cq; ring
  have hsu : (1 - zeta * u t) * u (q*t) = 1 := by
    calc
      _ = ((1 - zeta * u t) * (Cq * (1-q*t))) * inverseDenominator (q*t) := by unfold u; ring
      _ = (1 - q*(q*t)) * inverseDenominator (q*t) := by rw [hs]
      _ = 1 := denominator_unit _
  exact inverse_unique hj hsu

private theorem evaluated_reciprocal :
    jointEval (u t) zeta hasEval_zeta (blockEval reciprocalMarker completionBivariate) =
      shift H := by
  let J := jointEval (u t) zeta hasEval_zeta
  have hc := comp_eval₂
    (show Continuous (coefficientEval reciprocalMarker) from continuous_of_discreteTopology)
    (HasEval.X (R := Polynomial ℚ)) (ε := J) (continuous_joint _ _ _)
  have hp : J.comp (coefficientEval reciprocalMarker) = coefficientEval (u (q*t)) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [coefficientEval, J, jointEval, coe_eval₂Hom]
    · simp [coefficientEval, J, reciprocal_specialization]
  have he := congrFun hc completionBivariate
  rw [hp, show J X = zeta from joint_X _ _ _] at he
  have he' : J (blockEval reciprocalMarker completionBivariate) =
      jointEval (u (q*t)) zeta hasEval_zeta completionBivariate := by
    simpa only [Function.comp_apply, blockEval, jointEval, coe_eval₂Hom] using he
  calc
    J (blockEval reciprocalMarker completionBivariate) =
        jointEval (u (q*t)) zeta hasEval_zeta completionBivariate := he'
    _ = shift H := shift_H.symm

private theorem zeta_u_clear :
    zeta * (u t)^2 * (1-q*t)^2 = q * (1-t)^2 := by
  calc
    _ = zeta * (u t * (1-q*t))^2 := by ring
    _ = zeta * (Cq * (1-t))^2 := by rw [u_denominator]
    _ = (zeta * Cq^2) * (1-t)^2 := by ring
    _ = q * (1-t)^2 := by rw [zeta_Cq_sq]

private theorem kernel_clear :
    (u t - 1 - zeta * (u t)^2) * (1-q*t)^2 = -delta*t := by
  calc
    _ = Cq*(1-t)*(1-q*t) - (1-q*t)^2 - q*(1-t)^2 := by
      linear_combination (1-q*t) * u_denominator t - zeta_u_clear
    _ = -delta*t := by unfold Cq delta; ring

private theorem kernel_identity :
    u t - 1 - zeta*(u t)^2 = -delta*t*(inverseDenominator t)^2 := by
  apply cancel_unit (denominator_square_unit t)
  rw [kernel_clear]
  calc
    -delta*t = (-delta*t) * ((1-q*t)^2 * (inverseDenominator t)^2) := by
      rw [denominator_square_unit, mul_one]
    _ = (-delta*t*(inverseDenominator t)^2) * (1-q*t)^2 := by ring

private theorem zeta_u_identity :
    zeta*(u t)^2 = q*(1-t)^2*(inverseDenominator t)^2 := by
  apply cancel_unit (denominator_square_unit t)
  rw [zeta_u_clear]
  calc
    q*(1-t)^2 = (q*(1-t)^2) * ((1-q*t)^2 * (inverseDenominator t)^2) := by
      rw [denominator_square_unit, mul_one]
    _ = (q*(1-t)^2*(inverseDenominator t)^2) * (1-q*t)^2 := by ring

/-- The actual H equation follows by continuous evaluation composition of public F.
No functional equation, support statement, or recurrence model is a premise. -/
theorem catalytic_H_equation :
    q*(1-t)^2*shift H + delta*t*H =
      Cq*(Aq-1)*(1+q*t^2) + (Cq^2-4*q*Aq)*t := by
  let J := jointEval (u t) zeta hasEval_zeta
  have hEq := (completion_functional_equation).2.2.2.2.2
  rw [← blockEval_eq_evaluateBlock reciprocalMarker] at hEq
  have he := congrArg J hEq
  have hmap : (u t - 1 - zeta*(u t)^2)*H =
      u t - (1+zeta*(u t)^2)*Aq + zeta*(u t)^2*shift H := by
    change J ((blockMarker-1-X*blockMarker^2)*completionBivariate) =
      J (blockMarker-(1+X*blockMarker^2)*actualSeries.map Polynomial.C +
        X*blockMarker^2*blockEval reciprocalMarker completionBivariate) at he
    simpa only [map_mul, map_sub, map_add, map_one, map_pow, J,
      show blockMarker = t from rfl, joint_t, joint_X, H, Aq,
      evaluated_reciprocal] using he
  have hclear : -delta*t*H = Cq*(1-t)*(1-q*t) -
      ((1-q*t)^2+q*(1-t)^2)*Aq + q*(1-t)^2*shift H := by
    calc
      _ = ((u t-1-zeta*(u t)^2)*(1-q*t)^2)*H := by rw [kernel_clear]
      _ = (u t - (1+zeta*(u t)^2)*Aq + zeta*(u t)^2*shift H) * (1-q*t)^2 := by
        linear_combination (1-q*t)^2 * hmap
      _ = Cq*(1-t)*(1-q*t) - ((1-q*t)^2+q*(1-t)^2)*Aq +
          q*(1-t)^2*shift H := by
        linear_combination (1-q*t)*u_denominator t - Aq*zeta_u_clear + shift H*zeta_u_clear
  calc
    _ = ((1-q*t)^2+q*(1-t)^2)*Aq - Cq*(1-t)*(1-q*t) := by
      calc
        q*(1-t)^2*shift H + delta*t*H =
            -(-delta*t*H) + q*(1-t)^2*shift H := by ring
        _ = ((1-q*t)^2+q*(1-t)^2)*Aq - Cq*(1-t)*(1-q*t) := by
          rw [hclear]
          ring
    _ = Cq*(Aq-1)*(1+q*t^2)+(Cq^2-4*q*Aq)*t := by unfold Cq; ring

/-- Units, reciprocal specialization, kernel identities and the concrete actual H equation. -/
theorem catalytic_H_bridge :
    Cq*invCq = 1 ∧
    (1-q*t)*inverseDenominator t = 1 ∧
    (1-q^2*t)*inverseDenominator (q*t) = 1 ∧
    jointEval (u t) zeta hasEval_zeta reciprocalMarker = u (q*t) ∧
    u t - 1 - zeta*(u t)^2 = -delta*t*(inverseDenominator t)^2 ∧
    zeta*(u t)^2 = q*(1-t)^2*(inverseDenominator t)^2 ∧
    q*(1-t)^2*shift H + delta*t*H =
      Cq*(Aq-1)*(1+q*t^2)+(Cq^2-4*q*Aq)*t := by
  refine ⟨invCq_unit, denominator_unit t, ?_, reciprocal_specialization,
    kernel_identity, zeta_u_identity, catalytic_H_equation⟩
  simpa only [pow_two, mul_assoc] using denominator_unit (q*t)

end
end CatalyticH
end D5.S3.Combinatorics.PatternMatchings.P13
