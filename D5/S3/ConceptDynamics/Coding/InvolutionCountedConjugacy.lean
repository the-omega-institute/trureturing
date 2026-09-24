/- GID: D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative involution factors yield an exact one-step exchange
     with a matching lower bound. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy

open D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

noncomputable section
universe u
variable {H : Type u} [Group H] [Fintype H]

/-- Both endpoints are the original formulas, converted coefficientwise to naturals. -/
def sourceNat (s t : H) : NAlg H := toNat (source s t)
def targetNat (H : Type u) [Group H] [Fintype H] : NAlg H := toNat (target H)

/-- The actual natural coefficients satisfy both product identities. -/
theorem natural_factor_products (s t : H) (hs : s * s = 1) :
    toNat (leftFactor s t) * toNat (rightFactor s) = sourceNat s t ∧
    toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H := by
  have left_nonnegative (g : H) : 0 ≤ (leftFactor s t).coeff g := by
    classical
    have hcoeff : (leftFactor s t).coeff g =
        1 + (if t = g then 1 else 0) - (if s * t = g then 1 else 0) := by
      unfold leftFactor
      rw [sub_mul, one_mul]
      simp [uniform, basis, Finsupp.single_apply, add_sub_assoc]
    rw [hcoeff]
    by_cases ht : t = g
    · rw [if_pos ht]
      by_cases hst : s * t = g <;> simp [hst]
    · rw [if_neg ht]
      by_cases hst : s * t = g <;> simp [hst]
  have right_nonnegative (g : H) : 0 ≤ (rightFactor s).coeff g := by
    classical
    by_cases h1 : (1 : H) = g <;> by_cases hs' : s = g <;>
      simp [rightFactor, basis, MonoidAlgebra.one_def, h1, hs']
  have lift_toNat_local (p : ZAlg H) (hp : ∀ g : H, 0 ≤ p.coeff g) :
      liftNat H (toNat p) = p := by
    ext g
    simp [liftNat, toNat, Int.toNat_of_nonneg (hp g)]
  have hf : liftNat H (toNat (leftFactor s t) * toNat (rightFactor s)) = source s t := by
    rw [map_mul, lift_toNat_local _ left_nonnegative,
      lift_toNat_local _ right_nonnegative]
    exact factors_forward s t
  have hr : liftNat H (toNat (rightFactor s) * toNat (leftFactor s t)) = target H := by
    rw [map_mul, lift_toNat_local _ right_nonnegative,
      lift_toNat_local _ left_nonnegative]
    exact factors_reverse s t hs
  have toNat_lift_local (p : NAlg H) : toNat (liftNat H p) = p := by
    ext g
    simp [toNat, liftNat]
  constructor
  · simpa only [toNat_lift_local, sourceNat] using congrArg (toNat (H := H)) hf
  · simpa only [toNat_lift_local, targetNat] using congrArg (toNat (H := H)) hr

/-- Place a scalar group-ring element in its genuine one-vertex matrix. -/
def scalar (p : NAlg H) : GroupMat H 1 1 := fun _ _ => p

def sourceMatrix (s t : H) : GroupMat H 1 1 := scalar (sourceNat s t)
def targetMatrix (H : Type u) [Group H] [Fintype H] : GroupMat H 1 1 := scalar (targetNat H)

/-- A chain is constructed without assuming either an exchange or a conjugacy of the endpoints. -/
theorem involution_exchange (s t : H) (hs : s * s = 1) :
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 := by
  let U := scalar (toNat (leftFactor s t))
  let V := scalar (toNat (rightFactor s))
  have hUV : U * V = sourceMatrix s t := by
    ext i j
    simpa [U, V, sourceMatrix, scalar, Matrix.mul_apply] using
      (natural_factor_products s t hs).1
  have hVU : V * U = targetMatrix H := by
    ext i j
    simpa [U, V, targetMatrix, scalar, Matrix.mul_apply] using
      (natural_factor_products s t hs).2
  have c := ExchangeChain.cons U V (ExchangeChain.nil (V * U))
  simpa only [hUV, hVU] using c

/-- The exact minimum is one for noncommuting choices of the two group elements. -/
theorem involution_minimum_one (s t : H) (hs : s * s = 1)
    (hst : s * t ≠ t * s) :
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
    ¬ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 0 := by
  refine ⟨involution_exchange s t hs, ?_⟩
  intro c
  have zero_chain_same {A B : GroupMat H 1 1}
      (chain : ExchangeChain (NAlg H) A B 0) : A = B := by
    cases chain with
    | nil _ => rfl
  have hsame : sourceMatrix s t = targetMatrix H := zero_chain_same c
  have hmatrix := congrArg (fun M : GroupMat H 1 1 => M 0 0) hsame
  have hendpoints : sourceNat s t = targetNat H := by
    simpa [sourceMatrix, targetMatrix, scalar] using hmatrix
  have hsource : liftNat H (sourceNat s t) = source s t := by
    have left_nonnegative (g : H) : 0 ≤ (leftFactor s t).coeff g := by
      classical
      have hcoeff : (leftFactor s t).coeff g =
          1 + (if t = g then 1 else 0) - (if s * t = g then 1 else 0) := by
        unfold leftFactor
        rw [sub_mul, one_mul]
        simp [uniform, basis, Finsupp.single_apply, add_sub_assoc]
      rw [hcoeff]
      by_cases ht : t = g
      · rw [if_pos ht]
        by_cases hst' : s * t = g <;> simp [hst']
      · rw [if_neg ht]
        by_cases hst' : s * t = g <;> simp [hst']
    have right_nonnegative (g : H) : 0 ≤ (rightFactor s).coeff g := by
      classical
      by_cases h1 : (1 : H) = g <;> by_cases hs' : s = g <;>
        simp [rightFactor, basis, MonoidAlgebra.one_def, h1, hs']
    have lift_toNat_local (p : ZAlg H) (hp : ∀ g : H, 0 ≤ p.coeff g) :
        liftNat H (toNat p) = p := by
      ext g
      simp [liftNat, toNat, Int.toNat_of_nonneg (hp g)]
    rw [← (natural_factor_products s t hs).1, map_mul,
      lift_toNat_local _ left_nonnegative, lift_toNat_local _ right_nonnegative]
    exact factors_forward s t
  have htarget : liftNat H (targetNat H) = target H := by
    rw [← (natural_factor_products s t hs).2, map_mul,
      lift_toNat_local _ right_nonnegative, lift_toNat_local _ left_nonnegative]
    exact factors_reverse s t hs
  apply source_ne_target s t hs hst
  exact hsource.symm.trans ((congrArg (liftNat H) hendpoints).trans htarget)

#print axioms natural_factor_products
#print axioms involution_exchange
#print axioms involution_minimum_one

end
end D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
