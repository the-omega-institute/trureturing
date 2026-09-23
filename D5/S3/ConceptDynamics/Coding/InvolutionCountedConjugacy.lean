/- GID: D5/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/InvolutionCountedConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actual nonnegative involution factors yield a counted equivariant conjugacy and an exact one-step dihedral example. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
import Mathlib.GroupTheory.SpecificGroups.Dihedral

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy

open D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap

noncomputable section
universe u
variable {H : Type u} [Group H] [Fintype H]

private theorem toNat_lift (p : NAlg H) : toNat (liftNat H p) = p := by
  ext g
  simp [toNat, liftNat]

/-- Both endpoints are the original formulas, converted coefficientwise to naturals. -/
def sourceNat (s t : H) : NAlg H := toNat (source s t)
def targetNat (H : Type u) [Group H] [Fintype H] : NAlg H := toNat (target H)

/-- The actual natural coefficients satisfy both product identities. -/
theorem natural_factor_products (s t : H) (hs : s * s = 1) :
    toNat (leftFactor s t) * toNat (rightFactor s) = sourceNat s t ∧
    toNat (rightFactor s) * toNat (leftFactor s t) = targetNat H := by
  have hf : liftNat H (toNat (leftFactor s t) * toNat (rightFactor s)) = source s t := by
    rw [map_mul, lift_toNat _ (leftFactor_nonnegative s t),
      lift_toNat _ (rightFactor_nonnegative s)]
    exact factors_forward s t
  have hr : liftNat H (toNat (rightFactor s) * toNat (leftFactor s t)) = target H := by
    rw [map_mul, lift_toNat _ (rightFactor_nonnegative s),
      lift_toNat _ (leftFactor_nonnegative s t)]
    exact factors_reverse s t hs
  constructor
  · simpa only [toNat_lift, sourceNat] using congrArg (toNat (H := H)) hf
  · simpa only [toNat_lift, targetNat] using congrArg (toNat (H := H)) hr

theorem sourceNat_lift (s t : H) (hs : s * s = 1) :
    liftNat H (sourceNat s t) = source s t := by
  rw [← (natural_factor_products s t hs).1, map_mul,
    lift_toNat _ (leftFactor_nonnegative s t), lift_toNat _ (rightFactor_nonnegative s)]
  exact factors_forward s t

theorem targetNat_lift : liftNat H (targetNat H) = target H := by
  apply lift_toNat
  intro g
  simp [target]

theorem natural_endpoints_differ (s t : H) (hs : s * s = 1)
    (hst : s * t ≠ t * s) : sourceNat s t ≠ targetNat H := by
  intro h
  have hh := congrArg (liftNat H) h
  rw [sourceNat_lift s t hs, targetNat_lift] at hh
  exact source_ne_target s t hs hst hh

/-- Place a scalar group-ring element in its genuine one-vertex matrix. -/
def scalar (p : NAlg H) : GroupMat H 1 1 := fun _ _ => p

@[simp] theorem scalar_mul (p q : NAlg H) : scalar p * scalar q = scalar (p * q) := by
  ext i j
  simp [scalar, Matrix.mul_apply]

def sourceMatrix (s t : H) : GroupMat H 1 1 := scalar (sourceNat s t)
def targetMatrix (H : Type u) [Group H] [Fintype H] : GroupMat H 1 1 := scalar (targetNat H)

/-- A chain is constructed without assuming either an exchange or a conjugacy of the endpoints. -/
theorem involution_exchange (s t : H) (hs : s * s = 1) :
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 := by
  let U := scalar (toNat (leftFactor s t))
  let V := scalar (toNat (rightFactor s))
  have hUV : U * V = sourceMatrix s t := by
    simpa [U, V, sourceMatrix] using congrArg scalar (natural_factor_products s t hs).1
  have hVU : V * U = targetMatrix H := by
    simpa [U, V, targetMatrix] using congrArg scalar (natural_factor_products s t hs).2
  have c := ExchangeChain.cons U V (ExchangeChain.nil (V * U))
  simpa only [hUV, hVU] using c

private theorem chain_zero_same {a : ℕ} {A B : Mat (NAlg H) a a}
    (c : ExchangeChain (NAlg H) A B 0) : A = B := by
  cases c
  rfl

/-- The exact minimum is one for noncommuting choices of the two group elements. -/
theorem involution_minimum_one (s t : H) (hs : s * s = 1)
    (hst : s * t ≠ t * s) :
    ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 1 ∧
    ¬ExchangeChain (NAlg H) (sourceMatrix s t) (targetMatrix H) 0 := by
  refine ⟨involution_exchange s t hs, ?_⟩
  intro c
  have h := congrArg (fun M : GroupMat H 1 1 => M 0 0) (chain_zero_same c)
  exact natural_endpoints_differ s t hs hst h

/-- The counted path and group-coordinate constructors interpret the explicit factors. -/
theorem involution_actual_conjugacy [TopologicalSpace H] [IsTopologicalGroup H]
    (s t : H) (hs : s * s = 1) :
    Nonempty (GroupConjugacy (sourceMatrix s t) (targetMatrix H)) :=
  chain_has_group_conjugacy (involution_exchange s t hs)

abbrev D8 := DihedralGroup 4

def reflection : D8 := DihedralGroup.sr 0
def rotation : D8 := DihedralGroup.r 1

theorem reflection_square : reflection * reflection = 1 := by decide

theorem reflection_rotation_ne : reflection * rotation ≠ rotation * reflection := by decide

/-- The eight-element dihedral case has actual natural coefficients and exact length one. -/
theorem dihedral_exact_one :
    ExchangeChain (NAlg D8) (sourceMatrix reflection rotation) (targetMatrix D8) 1 ∧
    ¬ExchangeChain (NAlg D8) (sourceMatrix reflection rotation) (targetMatrix D8) 0 :=
  involution_minimum_one reflection rotation reflection_square reflection_rotation_ne

/-- The original one-step dihedral dynamics admits the constructed equivariant homeomorphism. -/
theorem dihedral_original_time_conjugacy [TopologicalSpace D8] [IsTopologicalGroup D8] :
    Nonempty (GroupConjugacy (sourceMatrix reflection rotation) (targetMatrix D8)) :=
  involution_actual_conjugacy reflection rotation reflection_square

#print axioms natural_factor_products
#print axioms involution_exchange
#print axioms involution_minimum_one
#print axioms involution_actual_conjugacy
#print axioms dihedral_exact_one
#print axioms dihedral_original_time_conjugacy

end
end D5.S3.ConceptDynamics.Coding.InvolutionCountedConjugacy
