/- GID: D5/S3/Quantum/Dynamics/UnitaryDuhamelStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/UnitaryDuhamelStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct actual exponential unitary evolution, derive its noncommutative Duhamel interpolation, and prove dimension-free operator-norm stability. -/

import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
The exponential is the genuine norm-convergent Banach-algebra exponential.
The input Hamiltonians need not commute. The norm is the C-star operator
norm. No trace-norm ideal bound, relative-entropy inequality, or free-energy
bound is inferred merely from these operator estimates.

The convention below is U_H(t)=exp(i t H); substituting -t gives the usual
Schrodinger sign with exactly the same absolute-time stability bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Dynamics.UnitaryDuhamelStability

open NormedSpace Set
open scoped ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℂ A] [NormedAlgebra ℝ A] [IsScalarTower ℝ ℂ A]
  [StarModule ℂ A] [StarModule ℝ A] [CompleteSpace A]

/-- Actual exponential evolution, bundled with its proved unitarity. -/
def evolution (H : selfAdjoint A) (t : ℝ) : unitary A :=
  selfAdjoint.expUnitary (t • H)

@[simp] theorem evolution_coe (H : selfAdjoint A) (t : ℝ) :
    (evolution H t : A) = NormedSpace.exp (t • (Complex.I • (H : A))) := by
  simp only [evolution, selfAdjoint.expUnitary_coe, SetLike.val_smul]
  rw [smul_comm]

@[simp] theorem evolution_zero (H : selfAdjoint A) : evolution H 0 = 1 := by
  simp [evolution]

/-- Both derivative orders are supplied by the actual exponential power series. -/
theorem evolution_hasDerivAt (H : selfAdjoint A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolution H s : A))
      ((evolution H t : A) * (Complex.I • (H : A))) t := by
  simpa only [evolution_coe] using
    NormedSpace.hasDerivAt_exp_smul_const (Complex.I • (H : A)) t

theorem evolution_hasDerivAt' (H : selfAdjoint A) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolution H s : A))
      ((Complex.I • (H : A)) * (evolution H t : A)) t := by
  simpa only [evolution_coe] using
    NormedSpace.hasDerivAt_exp_smul_const' (Complex.I • (H : A)) t

/-- The two-generator interpolation, with no commutativity premise. -/
def bridge (H K : selfAdjoint A) (t s : ℝ) : A :=
  (evolution H (t - s) : A) * (evolution K s : A)

def bridgeDerivative (H K : selfAdjoint A) (t s : ℝ) : A :=
  (evolution H (t - s) : A) * (Complex.I • ((K : A) - (H : A))) *
    (evolution K s : A)

theorem bridge_hasDerivAt (H K : selfAdjoint A) (t s : ℝ) :
    HasDerivAt (bridge H K t) (bridgeDerivative H K t s) s := by
  have hleft := (evolution_hasDerivAt H (t - s)).comp s
    ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hright := evolution_hasDerivAt' K s
  convert hleft.mul hright using 1
  · rfl
  · simp only [bridgeDerivative, sub_zero, zero_sub, one_smul,
      neg_smul, smul_sub]
    noncomm_ring

/-- Unitary factors cancel in norm, so the derivative bound is independent
of the sizes of H and K, dimension, and the interpolation position. -/
theorem bridgeDerivative_norm (H K : selfAdjoint A) (t s : ℝ) :
    ‖bridgeDerivative H K t s‖ = ‖(K : A) - (H : A)‖ := by
  unfold bridgeDerivative
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    norm_smul, Complex.norm_I, one_mul]

/-- Duhamel's identity for the actual exponential unitaries. -/
theorem duhamel_identity (H K : selfAdjoint A) (t : ℝ) :
    (evolution K t : A) - (evolution H t : A) =
      ∫ s in (0 : ℝ)..t, bridgeDerivative H K t s := by
  have hc (L : selfAdjoint A) : Continuous (fun s : ℝ => (evolution L s : A)) :=
    continuous_iff_continuousAt.mpr (fun s => (evolution_hasDerivAt L s).continuousAt)
  have hg : Continuous (bridgeDerivative H K t) := by
    unfold bridgeDerivative
    exact ((hc H).comp (continuous_const.sub continuous_id)).mul continuous_const |>.mul (hc K)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => bridge_hasDerivAt H K t s) (hg.intervalIntegrable 0 t)
  simpa only [bridge, sub_self, sub_zero, evolution_zero, OneMemClass.coe_one,
    one_mul, mul_one] using h.symm

/-- The sharp unitary Duhamel Lipschitz constant in the C-star operator norm. -/
theorem evolution_stability (H K : selfAdjoint A) (t : ℝ) :
    ‖(evolution H t : A) - (evolution K t : A)‖ ≤ |t| * ‖(H : A) - (K : A)‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := bridge H K t) (f' := bridgeDerivative H K t)
    (fun s _ => (bridge_hasDerivAt H K t s).hasDerivWithinAt)
    (fun s _ => le_of_eq (bridgeDerivative_norm H K t s))
    convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  simpa only [bridge, sub_self, sub_zero, evolution_zero, OneMemClass.coe_one,
    one_mul, mul_one, Real.norm_eq_abs, norm_sub_rev, mul_comm] using h

/-- An observable conjugation estimate from an exact two-term telescoping identity. -/
theorem unitary_conjugation_stability (U V : unitary A) (X : A) :
    ‖(U : A) * X * star (U : A) - (V : A) * X * star (V : A)‖ ≤
      2 * ‖X‖ * ‖(U : A) - (V : A)‖ := by
  have hsplit : (U : A) * X * star (U : A) - (V : A) * X * star (V : A) =
      ((U : A) - (V : A)) * X * star (U : A) +
      (V : A) * (X * (star (U : A) - star (V : A))) := by noncomm_ring
  rw [hsplit]
  calc
    ‖((U : A) - (V : A)) * X * star (U : A) +
        (V : A) * (X * (star (U : A) - star (V : A)))‖ ≤
      ‖((U : A) - (V : A)) * X * star (U : A)‖ +
        ‖(V : A) * (X * (star (U : A) - star (V : A)))‖ := norm_add_le _ _
    _ = ‖((U : A) - (V : A)) * X‖ + ‖X * (star (U : A) - star (V : A))‖ := by
      rw [CStarRing.norm_mul_coe_unitary _ (star U), CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(U : A) - (V : A)‖ * ‖X‖ + ‖X‖ * ‖star (U : A) - star (V : A)‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖(U : A) - (V : A)‖ := by
      rw [← star_sub, norm_star]
      ring

theorem evolved_observable_stability (H K : selfAdjoint A) (X : A) (t : ℝ) :
    ‖(evolution H t : A) * X * star (evolution H t : A) -
      (evolution K t : A) * X * star (evolution K t : A)‖ ≤
        2 * ‖X‖ * |t| * ‖(H : A) - (K : A)‖ := by
  calc
    _ ≤ 2 * ‖X‖ * ‖(evolution H t : A) - (evolution K t : A)‖ :=
      unitary_conjugation_stability _ _ X
    _ ≤ 2 * ‖X‖ * (|t| * ‖(H : A) - (K : A)‖) :=
      mul_le_mul_of_nonneg_left (evolution_stability H K t) (by positivity)
    _ = _ := by ring

#print axioms bridge_hasDerivAt
#print axioms duhamel_identity
#print axioms evolution_stability
#print axioms evolved_observable_stability
end D5.S3.Quantum.Dynamics.UnitaryDuhamelStability
