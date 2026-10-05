/- GID: D5/S3/Combinatorics/FreeGroups/NormalIndependenceDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FreeGroups/NormalIndependenceDefs
   mirror-E: none(waiver:koch-hyde-olive-problem-five-two-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Subgroup.Pointwise, mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.GroupTheory.FreeGroup.Reduce]
   utility: none
   digest: Koch-Hyde and Olive's Problem 5.2 on exponentially growing normally independent subsets of free groups. -/

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.FreeGroup.Reduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FreeGroups.NormalIndependenceDefs

/-! Fixed public statement: L. Koch-Hyde and É. Olive, *Two problems about bases and independent
    sets in free groups*, arXiv:2609.00382v2, Section 5: "Problem 5.2. Does there exist a set
    S ⊂ F_r such that: for all s ∈ S, s ∉ ⟪S − {s}⟫; S grows exponentially. That is,
    b^n ∈ O(g_S(n)) for some b > 1. We conjecture the answer to Problem 5.2 is 'No'."  Here `F_r`
    is free on a basis of size `r`, `⟪·⟫` is the normal closure in `F_r`, and
    `g_S(n) = |S ∩ B_n|` counts the elements of `S` of reduced length at most `n`
    (Definitions 1.1–1.2). -/

/-- The reduced length of an element of the free group on `Fin r`. -/
def wordLength {r : ℕ} (g : FreeGroup (Fin r)) : ℕ := (FreeGroup.toWord g).length

/-- Every element of `S` lies outside the normal closure of the other elements. -/
def NormallyIndependent {r : ℕ} (S : Set (FreeGroup (Fin r))) : Prop :=
  ∀ s ∈ S, s ∉ Subgroup.normalClosure (S \ {s})

/-- `S` grows exponentially: `b^n ∈ O(|S ∩ B_n|)` for some `b > 1`. -/
def GrowsExponentially {r : ℕ} (S : Set (FreeGroup (Fin r))) : Prop :=
  ∃ b : ℝ, 1 < b ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
    C * b ^ n ≤ ((S ∩ {g | wordLength g ≤ n}).ncard : ℝ)

/-- Problem 5.2, asked for every rank `r ≥ 2`. -/
def claim : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ S : Set (FreeGroup (Fin r)), NormallyIndependent S ∧ GrowsExponentially S

end D5.S3.Combinatorics.FreeGroups.NormalIndependenceDefs
