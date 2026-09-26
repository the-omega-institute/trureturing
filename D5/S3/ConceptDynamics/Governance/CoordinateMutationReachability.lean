/- GID: D5/S3/ConceptDynamics/Governance/CoordinateMutationReachability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/CoordinateMutationReachability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-coordinate paths are exactly finite differences outside protected coordinates. -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability

/-- One mutation may change a single unprotected coordinate. All coordinate
values are otherwise arbitrary; there is no cross-coordinate validity constraint. -/
def CoordinateStep {ι : Type*} {α : ι → Type*} (fixedKeys : Set ι)
    (x y : ∀ i, α i) : Prop :=
  ∃ i, i ∉ fixedKeys ∧ ∀ j, j ≠ i → x j = y j

/-- Finite mutation paths preserve the protected coordinates and change only
finitely many others. Conversely these two conditions suffice, even for an
infinite dependent product, by successively replacing the differing coordinates. -/
theorem coordinate_reachable_iff_finite_difference
    {ι : Type*} {α : ι → Type*} (fixedKeys : Set ι) (x y : ∀ i, α i) :
    Relation.ReflTransGen (CoordinateStep fixedKeys) x y ↔
      (∀ i ∈ fixedKeys, x i = y i) ∧ Set.Finite {i | x i ≠ y i} := by
  classical
  constructor
  · intro path
    induction path with
    | refl => exact ⟨fun _ _ => rfl, by simp⟩
    | @tail z w path step ih =>
      obtain ⟨i, hi, same⟩ := step
      constructor
      · intro j hj
        exact (ih.1 j hj).trans (same j (fun h => hi (h ▸ hj)))
      · apply (ih.2.union (Set.finite_singleton i)).subset
        intro j hj
        by_cases hji : j = i
        · exact Or.inr hji
        · exact Or.inl (fun equal => hj (equal.trans (same j hji)))
  · rintro ⟨fixed, finite⟩
    have construct : ∀ (s : Finset ι) (a b : ∀ i, α i),
        (∀ i ∈ fixedKeys, a i = b i) →
        (∀ i, a i ≠ b i → i ∈ s) →
        Relation.ReflTransGen (CoordinateStep fixedKeys) a b := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro a b _ cover
        have equal : a = b := by
          funext i
          by_contra differs
          exact Finset.notMem_empty i (cover i differs)
        subst b
        exact .refl
      | @insert i s absent ih =>
        intro a b fixed cover
        by_cases equal : a i = b i
        · apply ih a b fixed
          intro j differs
          exact (Finset.mem_insert.mp (cover j differs)).resolve_left
            (fun h => differs (h ▸ equal))
        · have outside : i ∉ fixedKeys := fun h => equal (fixed i h)
          let next := Function.update a i (b i)
          have step : CoordinateStep fixedKeys a next := by
            refine ⟨i, outside, ?_⟩
            intro j hji
            exact (Function.update_of_ne hji (b i) a).symm
          apply Relation.ReflTransGen.head step
          apply ih next b
          · intro j hj
            have hji : j ≠ i := fun h => outside (h ▸ hj)
            simpa only [next, Function.update_of_ne hji] using fixed j hj
          · intro j differs
            have hji : j ≠ i := by
              intro h
              subst j
              exact differs (Function.update_self i (b i) a)
            have original : a j ≠ b j := by
              simpa only [next, Function.update_of_ne hji] using differs
            exact (Finset.mem_insert.mp (cover j original)).resolve_left hji
    exact construct finite.toFinset x y fixed (fun i hi => finite.mem_toFinset.mpr hi)

#print axioms coordinate_reachable_iff_finite_difference

end D5.S3.ConceptDynamics.Governance.CoordinateMutationReachability
