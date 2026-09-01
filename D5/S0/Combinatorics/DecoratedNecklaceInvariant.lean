/- GID: D5/S0/Combinatorics/DecoratedNecklaceInvariant
   generality: G
   mirror-B: D5/B/S0/Combinatorics/DecoratedNecklaceInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Cycle]
   digest: Rotation classes retain length and multiplicity while distinguishing reflection. -/

import Mathlib.Data.List.Cycle

/- Library-search audit trail (2026-09-01):
   * Repository searches for `necklace`, list rotation setoids, cyclic-list quotients,
     periodic components, and multisets of cycles found the specialized definitions
     `PeriodicComponent`, `componentDecoration`, and `depthInvariant` in
     `D5.S1.FixedPoints.TransientTrees.DepthTruncatedClassification`; its receipt covers the
     later depth-truncation theorem, not this general rotation-invariant package.
   * Pinned Mathlib exact hits `List.IsRotated`, `List.IsRotated.setoid`, `Cycle`,
     `List.IsRotated.perm`, `Cycle.length`, and `Cycle.toMultiset` provide the relation,
     quotient, and invariant primitives used below. No competing setoid or quotient is defined.
   * A GitHub Lean-code search through NyxID returned `pending_auth` before any results. The
     exact pinned-Mathlib hits above already determine the canonical implementation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Combinatorics.DecoratedNecklaceInvariant

/-- The system invariant obtained by forgetting the chosen start of every component word while
retaining multiplicity across components. -/
def systemNecklaceInvariant {alpha : Type*}
    (componentWords : Multiset (List alpha)) : Multiset (Cycle alpha) :=
  componentWords.map fun word : List alpha => (word : Cycle alpha)

/-- Mathlib's rotation setoid is exactly the relation given by rotating the first list some
number of places. -/
theorem rotation_setoid_relation {alpha : Type*} (first second : List alpha) :
    (List.IsRotated.setoid alpha).r first second <->
      exists turns, second = first.rotate turns := by
  change (exists turns, first.rotate turns = second) <-> _
  constructor <;> rintro ⟨turns, equality⟩ <;> exact ⟨turns, equality.symm⟩

/-- Cyclic rotation preserves both word length and the multiset of decorations. -/
theorem rotation_preserves_length_and_multiset {alpha : Type*} {first second : List alpha}
    (rotation : (List.IsRotated.setoid alpha).r first second) :
    first.length = second.length ∧
      (first : Multiset alpha) = (second : Multiset alpha) := by
  have permutation : first.Perm second := List.IsRotated.perm rotation
  exact ⟨permutation.length_eq, Multiset.coe_eq_coe.mpr permutation⟩

/-- Rotating a representative does not change its necklace. -/
theorem rotate_same_cycle {alpha : Type*} (word : List alpha) (turns : Nat) :
    (word.rotate turns : Cycle alpha) = (word : Cycle alpha) := by
  exact Cycle.coe_eq_coe.mpr (List.IsRotated.forall word turns)

/-- Replacing one component word by a rotation leaves the system invariant unchanged. -/
theorem system_necklace_invariant_cons_rotate {alpha : Type*}
    (componentWords : Multiset (List alpha)) (word : List alpha) (turns : Nat) :
    systemNecklaceInvariant (word.rotate turns ::ₘ componentWords) =
      systemNecklaceInvariant (word ::ₘ componentWords) := by
  simp [systemNecklaceInvariant, rotate_same_cycle]

/-- The three rotations of a three-letter word determine the same necklace. -/
theorem three_word_rotations_same :
    (([1, 2, 3] : List Nat) : Cycle Nat) = ([2, 3, 1] : List Nat) ∧
      (([1, 2, 3] : List Nat) : Cycle Nat) = ([3, 1, 2] : List Nat) := by
  decide

/-- Reflection is not a cyclic rotation for the three-letter witness. -/
theorem three_word_reflection_distinct :
    (([1, 2, 3] : List Nat) : Cycle Nat) ≠ ([1, 3, 2] : List Nat) := by
  decide

/-- The reflection witness has the same decoration multiset, so that multiset is not a complete
necklace invariant. -/
theorem three_word_reflection_multiset_same :
    (([1, 2, 3] : List Nat) : Multiset Nat) = ([1, 3, 2] : List Nat) := by
  decide

/-- Cyclic words form Mathlib's rotation quotient, preserve length and decoration multiplicity,
and assemble componentwise into a multiset-valued system invariant. The concrete witness shows
that the decoration multiset is invariant but not complete. -/
theorem decorated_necklace_invariant :
    (∀ {alpha : Type*} (first second : List alpha),
      (List.IsRotated.setoid alpha).r first second <->
        exists turns, second = first.rotate turns) ∧
    (∀ {alpha : Type*} (first second : List alpha),
      (List.IsRotated.setoid alpha).r first second ->
        first.length = second.length ∧
          (first : Multiset alpha) = (second : Multiset alpha)) ∧
    (∀ {alpha : Type*} (componentWords : Multiset (List alpha))
        (word : List alpha) (turns : Nat),
      systemNecklaceInvariant (word.rotate turns ::ₘ componentWords) =
        systemNecklaceInvariant (word ::ₘ componentWords)) ∧
    ((([1, 2, 3] : List Nat) : Cycle Nat) = ([2, 3, 1] : List Nat) ∧
      (([1, 2, 3] : List Nat) : Cycle Nat) = ([3, 1, 2] : List Nat)) ∧
    (([1, 2, 3] : List Nat) : Cycle Nat) ≠ ([1, 3, 2] : List Nat) ∧
    (([1, 2, 3] : List Nat) : Multiset Nat) = ([1, 3, 2] : List Nat) := by
  exact ⟨rotation_setoid_relation,
    fun first second rotation => rotation_preserves_length_and_multiset rotation,
    system_necklace_invariant_cons_rotate,
    three_word_rotations_same,
    three_word_reflection_distinct,
    three_word_reflection_multiset_same⟩

#print axioms decorated_necklace_invariant

end D5.S0.Combinatorics.DecoratedNecklaceInvariant
