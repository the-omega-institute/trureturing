/- GID: D5/S3/Geometry/Hyperideal/FlatCandidateAcyclicity
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatCandidateAcyclicity
   mirror-E: none(waiver:universal-real-inequality)
   anchors: []
   utility: none
   digest: Common positive lengths make the flat-candidate dependency graph acyclic. -/

import Mathlib.Tactic

/-! The shared positive-length potential obstruction for flat-candidate cycles. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FlatCandidateAcyclicity

/-- A candidate with ordered dependencies `a -> b` and `a -> c` contributes both directed edges. -/
def candidateEdge {Q : Type*} (candidate : Q → Q → Q → Prop) : Q → Q → Prop :=
  fun a b => ∃ c, candidate a b c ∨ candidate a c b

/-- A directed cycle is a nonempty transitive path returning to its starting point. -/
def HasDirectedCycle {Q : Type*} (r : Q → Q → Prop) : Prop :=
  ∃ a, Relation.TransGen r a a

private theorem transGen_strictly_decreases {Q R : Type*} [Preorder R]
    {r : Q → Q → Prop} {z : Q → R}
    (hdec : ∀ {a b}, r a b → z b < z a) :
    ∀ {a b}, Relation.TransGen r a b → z b < z a := by
  intro a b h
  induction h with
  | single hab => exact hdec hab
  | tail hab hbc ih => exact lt_trans (hdec hbc) ih

/-- A strict potential cannot support a directed cycle. -/
theorem no_directed_cycle_of_strict_decrease {Q R : Type*} [Preorder R]
    {r : Q → Q → Prop} {z : Q → R}
    (hdec : ∀ {a b}, r a b → z b < z a) :
    ¬ HasDirectedCycle r := by
  rintro ⟨a, hcycle⟩
  exact (lt_irrefl (z a))
    (transGen_strictly_decreases (r := r) (z := z) hdec hcycle)

/-- The positive-length flat-candidate inequality excludes every directed cycle. -/
theorem flat_candidate_cycle_exclusion {Q : Type*}
    (z : Q → ℝ) (candidate : Q → Q → Q → Prop)
    (hpositive : ∀ a, 1 < z a)
    (hpg : ∀ {a b c}, candidate a b c → z a ≥ 1 + z b + z c) :
    ¬ HasDirectedCycle (candidateEdge candidate) := by
  apply no_directed_cycle_of_strict_decrease (r := candidateEdge candidate) (z := z)
  intro a b hab
  rcases hab with ⟨c, h | h⟩
  · calc
      z b < 1 + z b + z c := by linarith [hpositive c]
      _ ≤ z a := hpg h
  · calc
      z b < 1 + z c + z b := by linarith [hpositive c]
      _ ≤ z a := hpg h

#print axioms flat_candidate_cycle_exclusion

end D5.S3.Geometry.Hyperideal.FlatCandidateAcyclicity
