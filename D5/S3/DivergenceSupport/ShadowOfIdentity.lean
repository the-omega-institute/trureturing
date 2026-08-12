/- GID: D5/S3/DivergenceSupport/ShadowOfIdentity
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/ShadowOfIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A shadow names the nonnegative remainder that equals an inequality's slack. -/

import D5.S3.QuantumBounds.LagrangeGramIdentity

/-!
# Shadows of identities

`IsShadow lhs rhs remainder` records both the exact slack identity
`rhs - lhs = remainder` and the nonnegativity of the named remainder.  The
generic extraction theorem then discards only that explicit remainder.

The source note's structural assertion that the statistical and kinematic
families descend respectively from normalization and positivity, and that
both reduce to one source, is not formalized here.  No physical or
information-theoretic interpretation is claimed.

The audited Gibbs theorem in `D5.S3.Divergence.GrandmotherTheorem` supplies
`0 <= KL`, but no separate frozen identity
whose explicit remainder is KL.  Declaring `IsShadow 0 KL KL` would merely
repackage Gibbs together with the tautology `KL - 0 = KL`; moreover, the
suggested identity `0 = 0 - (-KL)` would force `KL = 0`.  Consequently no
statistical shadow instance is claimed here.

Library-first audit trail (pinned mathlib, 2026-08-13): searches for
`IsShadow`, `shadow`, `slack`, and `remainder` found no generic notion for an
identity with a named nonnegative slack.  `Finset.shadow` is instead the
unrelated combinatorial shadow of a set family, while remainder definitions
are domain-specific.  The requested `inner_mul_le_norm_mul_norm` name is
absent; current inner-product variants include `norm_inner_le_norm`,
`re_inner_le_norm`, `abs_real_inner_le_norm`, and `real_inner_le_norm`.
-/

namespace D5.S3.DivergenceSupport.ShadowOfIdentity

open Finset

/-- The slack `rhs - lhs` is identified with a named nonnegative remainder. -/
def IsShadow (lhs rhs remainder : ℝ) : Prop :=
  rhs - lhs = remainder ∧ 0 ≤ remainder

/-- Discarding the named nonnegative remainder extracts the shadow inequality. -/
theorem is_shadow_le {lhs rhs remainder : ℝ} (h : IsShadow lhs rhs remainder) :
    lhs ≤ rhs := by
  fail_if_success ((try simp); done)
  exact sub_nonneg.mp (h.1.symm ▸ h.2)

/-- The Lagrange/Gram identity identifies the Cauchy-Schwarz slack with its
explicit double sum of squares. -/
theorem lagrange_gram_is_shadow {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    IsShadow
      ((∑ i ∈ s, u i * v i) ^ 2)
      ((∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2))
      ((∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2) / 2) := by
  fail_if_success ((try simp); done)
  refine ⟨D5.S3.QuantumBounds.LagrangeGramIdentity.lagrange_gram_identity s u v, ?_⟩
  exact div_nonneg
    (sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg (u i * v j - u j * v i))
    (by norm_num)

/-- Cauchy-Schwarz follows by extracting the inequality from the
Lagrange/Gram shadow. -/
theorem cauchy_schwarz_of_lagrange_gram {ι : Type*}
    (s : Finset ι) (u v : ι → ℝ) :
    (∑ i ∈ s, u i * v i) ^ 2 ≤
      (∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) := by
  fail_if_success ((try simp); done)
  exact is_shadow_le (lagrange_gram_is_shadow s u v)

#print axioms is_shadow_le
#print axioms lagrange_gram_is_shadow
#print axioms cauchy_schwarz_of_lagrange_gram

end D5.S3.DivergenceSupport.ShadowOfIdentity
