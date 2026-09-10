/- GID: D5/S0/Certificates/FiniteSublevelCover
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteSublevelCover
   mirror-E: none(waiver:proof-carrying-analytic-cover)
   anchors: []
   digest: A finite postordered family of locally proved enclosure steps covers every real sublevel point, without a finite-candidate assumption or a trusted external verdict. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/- The repository's FiniteExhaustion and FiniteBranchAtlas enumerate finite
   candidate types. Here only the proof-node index is finite; the candidate
   type X may be an uncountable phase space. Those finite-candidate results
   cannot be applied by declaring the observed roots exhaustive.

   Each constructor requires an actual Lean proof of its local premise.
   In particular, contract retains EVERY sublevel point of the parent, not
   only its exact roots. The strict postorder prevents cyclic justifications.
   This is proof assembly, not a parser or a verified interval evaluator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S0.Certificates.FiniteSublevelCover

universe u v

/-- One locally justified step in a finite postordered cover certificate.

The region and target are sets of actual candidates, not a sampled arena.
`covered` may enter a union of tubes directly. `excluded` supplies a real
residual enclosure separated from the permitted closed residual band.
`split` must retain the whole parent, including all shared boundaries.
`contract` must retain every small-residual point, with the same tolerance.
Its premise can be supplied by an actual Krawczyk/mean-value row theorem.

Numerical reports, node counts and hashes do not construct any of these proofs.
A complete numeric instance still has to supply all local proof terms. -/
inductive LocalStep {X : Type u} {Outcome : Type v} {n : ℕ}
    (region : Fin n → Set X) (target : Set X)
    (residual : X → Outcome → ℝ) (epsilon : ℝ) : Fin n → Prop where
  | covered {i : Fin n}
      (inside : region i ⊆ target) : LocalStep region target residual epsilon i
  | excluded {i : Fin n} (a : Outcome) (lower upper : ℝ)
      (encloses : ∀ x ∈ region i, lower ≤ residual x a ∧ residual x a ≤ upper)
      (separated : epsilon < lower ∨ upper < -epsilon) :
      LocalStep region target residual epsilon i
  | balancedExcluded {i : Fin n} (outcomes : Finset Outcome)
      (lower upper : Outcome → ℝ)
      (encloses : ∀ x ∈ region i, (∀ a, |residual x a| ≤ epsilon) →
        ∀ a ∈ outcomes, lower a ≤ residual x a ∧ residual x a ≤ upper a)
      (conserved : ∀ x ∈ region i, ∑ a ∈ outcomes, residual x a = 0)
      (separated : 0 < (∑ a ∈ outcomes, lower a) ∨ (∑ a ∈ outcomes, upper a) < 0) :
      LocalStep region target residual epsilon i
  | split {i : Fin n} (left right : Fin n)
      (leftEarlier : left.val < i.val) (rightEarlier : right.val < i.val)
      (retains : region i ⊆ region left ∪ region right) :
      LocalStep region target residual epsilon i
  | contract {i : Fin n} (child : Fin n) (earlier : child.val < i.val)
      (retains : ∀ x ∈ region i, (∀ a, |residual x a| ≤ epsilon) →
        x ∈ region child) : LocalStep region target residual epsilon i

/-- Every candidate in any root region with all residuals in the closed band
belongs to the target, provided every finite proof node is locally justified.

There is no assumed global cover, root count, uniqueness, compactness,
termination of an external program or finite cardinality of X. Termination of
proof descent follows from the checked strict child-index inequalities.
Shared subtrees and multiple chart roots are permitted. -/
theorem sublevel_mem_target_of_local_steps
    {X : Type u} {Outcome : Type v} {n : ℕ}
    (region : Fin n → Set X) (target : Set X)
    (residual : X → Outcome → ℝ) (epsilon : ℝ)
    (steps : ∀ i, LocalStep region target residual epsilon i)
    (root : Fin n) (x : X) (hx : x ∈ region root)
    (hresidual : ∀ a, |residual x a| ≤ epsilon) : x ∈ target := by
  have sound : ∀ k : ℕ, ∀ i : Fin n, i.val = k →
      ∀ z ∈ region i, (∀ a, |residual z a| ≤ epsilon) → z ∈ target := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik z hz hr
      cases steps i with
      | covered inside => exact inside hz
      | excluded a lower upper encloses separated =>
        have he := encloses z hz
        have hb := abs_le.mp (hr a)
        rcases separated with hlow | hhigh
        · exact False.elim (by linarith)
        · exact False.elim (by linarith)
      | balancedExcluded outcomes lower upper encloses conserved separated =>
        have hlow : (∑ a ∈ outcomes, lower a) ≤ ∑ a ∈ outcomes, residual z a := by
          apply Finset.sum_le_sum
          intro a ha
          exact (encloses z hz hr a ha).1
        have hhigh : (∑ a ∈ outcomes, residual z a) ≤ ∑ a ∈ outcomes, upper a := by
          apply Finset.sum_le_sum
          intro a ha
          exact (encloses z hz hr a ha).2
        rw [conserved z hz] at hlow hhigh
        rcases separated with hpos | hneg
        · exact False.elim (by linarith)
        · exact False.elim (by linarith)
      | split left right hleft hright retains =>
        rcases retains hz with hl | hrightMem
        · exact ih left.val (by simpa only [hik] using hleft) left rfl z hl hr
        · exact ih right.val (by simpa only [hik] using hright) right rfl z hrightMem hr
      | contract child hearlier retains =>
        exact ih child.val (by simpa only [hik] using hearlier) child rfl z
          (retains z hz hr) hr
  exact sound root.val root rfl x hx hresidual

#print axioms sublevel_mem_target_of_local_steps

end D5.S0.Certificates.FiniteSublevelCover
