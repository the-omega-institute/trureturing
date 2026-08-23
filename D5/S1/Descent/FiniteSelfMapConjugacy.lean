/- GID: D5/S1/Descent/FiniteSelfMapConjugacy
   generality: G
   mirror-B: D5/B/S1/Descent/FiniteSelfMapConjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cycle counts classify permutations. General maps with attached trees are not covered. -/

import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'finite_self_map_conjugacy' D5 Golden/Frozen/accepted` had no hits.
   * Repository searches for `Conjugacy`, `SelfMap`, `FunctionalGraph`, `cycleType`, and
     `minimalPeriod` found the public rooted-tree classifier in
     `D5.S1.FixedPoints.RootedTransientTreeClassification` and the public diagonal-interface
     theorem in `D5.S3.Observer.Dynamics.DiagonalInterfaceConjugacy`, but neither classifies maps
     by cycle data. The private conjugacy helper in `DiagonalAlgebraSimilarityObstruction` is also
     not a cover.
   * Pinned Mathlib provides `Function.minimalPeriod_eq_minimalPeriod_iff` and
     `Equiv.Perm.isConj_iff_cycleType_eq`. The former reduces period preservation to iterated
     semiconjugacy; the latter is reused for the complete permutation case. No library theorem
     was found for decorated functional graphs of arbitrary finite self-maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Descent.FiniteSelfMapConjugacy

/-- A relabeling conjugates two self-maps when it intertwines their updates pointwise. -/
def Conjugates {Y Z : Type*} (tau : Y -> Y) (sigma : Z -> Z) (relabel : Y ≃ Z) : Prop :=
  ∀ y, relabel (tau y) = sigma (relabel y)

/-- The number of cycles of length `n`, obtained by dividing the number of points of minimal
period `n` by `n`. At `n = 0` the value is zero, so transient points are excluded. -/
noncomputable def cycleLengthMultiplicity {Y : Type*} [Fintype Y]
    (tau : Y -> Y) (n : Nat) : Nat := by
  classical
  exact ((Finset.univ.filter fun y => Function.minimalPeriod tau y = n).card) / n

/-- Conjugate finite self-maps have the same number of cycles of every length. -/
theorem finite_self_map_conjugacy
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (tau : Y -> Y) (sigma : Z -> Z) (relabel : Y ≃ Z)
    (hconj : Conjugates tau sigma relabel) :
    ∀ n, cycleLengthMultiplicity tau n = cycleLengthMultiplicity sigma n := by
  classical
  have hsemiconj : Function.Semiconj relabel tau sigma := by
    exact hconj
  have hperiod (y : Y) :
      Function.minimalPeriod tau y = Function.minimalPeriod sigma (relabel y) := by
    rw [Function.minimalPeriod_eq_minimalPeriod_iff]
    intro n
    constructor
    · intro hperiodic
      change (tau^[n]) y = y at hperiodic
      change (sigma^[n]) (relabel y) = relabel y
      calc
        (sigma^[n]) (relabel y) = relabel ((tau^[n]) y) :=
          (hsemiconj.iterate_right n y).symm
        _ = relabel y := congrArg relabel hperiodic
    · intro hperiodic
      change (sigma^[n]) (relabel y) = relabel y at hperiodic
      change (tau^[n]) y = y
      apply relabel.injective
      calc
        relabel ((tau^[n]) y) = (sigma^[n]) (relabel y) :=
          hsemiconj.iterate_right n y
        _ = relabel y := hperiodic
  intro n
  have hcard :
      (Finset.univ.filter fun y => Function.minimalPeriod tau y = n).card =
        (Finset.univ.filter fun z => Function.minimalPeriod sigma z = n).card := by
    apply Finset.card_equiv relabel
    intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hperiod y]
  simp only [cycleLengthMultiplicity]
  rw [hcard]

/-- For permutations, where no transient trees occur, cycle type is a complete conjugacy
invariant and explicitly produces an intertwining relabeling. -/
theorem permutation_cycle_type_complete
    {Y : Type*} [Fintype Y] [DecidableEq Y] (tau sigma : Equiv.Perm Y) :
    tau.cycleType = sigma.cycleType ↔
      ∃ relabel : Equiv.Perm Y, Conjugates tau sigma relabel := by
  constructor
  · intro htype
    obtain ⟨relabel, hrel⟩ :=
      isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr htype)
    refine ⟨relabel, fun y => ?_⟩
    have hintertwines : relabel * tau = sigma * relabel :=
      mul_inv_eq_iff_eq_mul.mp hrel
    exact congrArg (fun perm : Equiv.Perm Y => perm y) hintertwines
  · rintro ⟨relabel, hrel⟩
    apply Equiv.Perm.isConj_iff_cycleType_eq.mp
    rw [isConj_iff]
    refine ⟨relabel, mul_inv_eq_iff_eq_mul.mpr ?_⟩
    ext y
    exact hrel y

example : cycleLengthMultiplicity (id : Fin 3 -> Fin 3) 1 = 3 := by
  simp [cycleLengthMultiplicity]

#print axioms finite_self_map_conjugacy

end D5.S1.Descent.FiniteSelfMapConjugacy
