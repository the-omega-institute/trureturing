/- GID: D5/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/FirstDifferencePowerLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discounted discrete prediction distance is the power of the first differing orbit readout. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.FirstDifferencePowerLaw

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation
open D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric

/- The source relation is equality of every readout along the update orbit. -/
def orbitReadoutRelation {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (y y' : Y) : Prop :=
  forall k : Nat, q ((tau^[k]) y) = q ((tau^[k]) y')

private theorem discrete_distance_mem_Icc
    {O : Type*} [DecidableEq O] (a b : O) :
    discreteOutputDistance a b ∈ Set.Icc (0 : Real) 1 := by
  by_cases h : a = b <;> simp [discreteOutputDistance, h]

private theorem discrete_terms_bddAbove
    {Y O : Type*} [DecidableEq O]
    (tau : Y -> Y) (q : Y -> O) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1) (y y' : Y) :
    BddAbove (Set.range fun k : Nat =>
      gamma ^ k * discreteOutputDistance (q ((tau^[k]) y)) (q ((tau^[k]) y'))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hdistance := discrete_distance_mem_Icc
    (q ((tau^[k]) y)) (q ((tau^[k]) y'))
  calc
    gamma ^ k * discreteOutputDistance (q ((tau^[k]) y)) (q ((tau^[k]) y')) ≤
        1 * discreteOutputDistance (q ((tau^[k]) y)) (q ((tau^[k]) y')) :=
      mul_le_mul_of_nonneg_right
        (pow_le_one₀ hgamma.1.le hgamma.2) hdistance.1
    _ = discreteOutputDistance (q ((tau^[k]) y)) (q ((tau^[k]) y')) := one_mul _
    _ ≤ 1 := hdistance.2

/- The first disagreement controls the supremum because all earlier terms vanish and
   later powers are no larger when the discount lies in (0,1]. -/
theorem first_difference_power_law
    {Y O : Type*} [DecidableEq O]
    (tau : Y -> Y) (q : Y -> O) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1) (y y' : Y) :
    (orbitReadoutRelation tau q y y' ->
      discountedPredictionDistance tau q discreteOutputDistance gamma y y' = 0) ∧
    (forall hsep : exists k : Nat,
        q ((tau^[k]) y) ≠ q ((tau^[k]) y'),
      discountedPredictionDistance tau q discreteOutputDistance gamma y y' =
        gamma ^ Nat.find hsep) := by
  have hterms :
      BddAbove (Set.range fun k : Nat =>
        gamma ^ k * discreteOutputDistance (q ((tau^[k]) y))
          (q ((tau^[k]) y'))) :=
    discrete_terms_bddAbove tau q gamma hgamma y y'
  constructor
  · intro hagree
    apply le_antisymm
    · unfold discountedPredictionDistance
      apply ciSup_le
      intro k
      simp [discreteOutputDistance, hagree k]
    · unfold discountedPredictionDistance
      calc
        0 = gamma ^ 0 * discreteOutputDistance (q y) (q y') := by
          have h0 : q y = q y' := by
            simpa [orbitReadoutRelation] using hagree 0
          simp [discreteOutputDistance, h0]
        _ ≤ ⨆ k : Nat, gamma ^ k * discreteOutputDistance
            (q ((tau^[k]) y)) (q ((tau^[k]) y')) := le_ciSup hterms 0
  · intro hsep
    have hspec :
        q ((tau^[Nat.find hsep]) y) ≠ q ((tau^[Nat.find hsep]) y') :=
      Nat.find_spec hsep
    apply le_antisymm
    · unfold discountedPredictionDistance
      apply ciSup_le
      intro k
      by_cases hk : q ((tau^[k]) y) = q ((tau^[k]) y')
      · simp [discreteOutputDistance, hk]
        exact pow_nonneg hgamma.1.le _
      · have hnk : Nat.find hsep ≤ k := Nat.find_min' hsep hk
        calc
          gamma ^ k * discreteOutputDistance (q ((tau^[k]) y))
              (q ((tau^[k]) y')) = gamma ^ k := by
                simp [discreteOutputDistance, hk]
          _ ≤ gamma ^ Nat.find hsep :=
            pow_le_pow_of_le_one hgamma.1.le hgamma.2 hnk
    · unfold discountedPredictionDistance
      have hlower := le_ciSup hterms (Nat.find hsep)
      simpa [discreteOutputDistance, hspec] using hlower

/- A concrete two-state witness keeps both branches of the public statement satisfiable. -/
example : orbitReadoutRelation (id : Bool -> Bool) id false false := by
  intro k
  rfl

example :
    exists k : Nat, (id : Bool -> Bool) ((id^[k]) false) ≠
      (id : Bool -> Bool) ((id^[k]) true) := by
  exact ⟨0, by decide⟩

#print axioms first_difference_power_law

end D5.S3.Observer.MetricGeometryLaws.FirstDifferencePowerLaw
