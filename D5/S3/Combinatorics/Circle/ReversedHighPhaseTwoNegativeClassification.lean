import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.HighPhaseTwoNegativeClassification
import D5.S3.Combinatorics.Circle.ReversedTwoBankCriterion

/-! UNCOMPILED source preparation. Apply HighPhasePhysicalGeneralization.patch
to the immutable owners only at future integration, after their readers join.
No elaboration, kernel, axiom-closure, fidelity-review, or official acceptance
is claimed. The physical and arithmetic predecessors are also candidates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ReversedHighPhaseTwoNegativeClassification
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Mask joint_implies_mask mask_implies_joint from
  D5.S3.Combinatorics.Circle.HighPhaseTwoNegativeClassification
open private dyadic_bounded_mask_iff from ReversedTwoBankCriterion

/-- On the full reverse domain, one original physical permutation and one
literal fresh insertion satisfy both complete OriginalOrders exactly outside
the forbidden wedge. Repeated numerical values retain distinct Fin labels. -/
theorem actualSource_reversed_high_phase_two_negative_joint_iff (a b : ℕ)
    (hb : 2 ≤ b) (hba : b < a) :
    (∃ sigma : List (Fin (a + b)), ∃ cut : ℕ, cut ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ (a + b - 1) + 2 ^ (b - 1)) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ (a + b - 1) + 2 ^ (b - 1)))
        (earWord (a + b) sigma cut)) ↔
      a = b + 1 ∨ 2 * b < a := by
  have ha : 2 ≤ a := by omega
  let p : ℤ := 2 ^ (b - 1)
  let L : ℤ := 2 ^ (a - 1)
  have hbank : 2 * p ≤ L := by
    calc
      2 * p = (2 : ℤ) ^ ((b - 1) + 1) := by
        dsimp only [p]
        rw [pow_succ]
        ring
      _ ≤ L := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show (b - 1) + 1 ≤ a - 1 by omega)
  have hm : Mask a b true ↔ a = b + 1 ∨ 2 * b < a := by
    simpa only [Mask, ↓reduceIte, ← mul_assoc,
      show (2 : ℤ) * 2 = 4 by norm_num] using
      (dyadic_bounded_mask_iff a b hb hba)
  constructor
  · rintro ⟨sigma, cut, hc, ho, hn⟩
    -- The owner extracts the first actual negative from arbitrary sigma.
    -- Its flag is true exactly when cut ≤ pre.length, including equality.
    exact hm.mp (joint_implies_mask a b ha hb true hbank sigma cut hc ho hn)
  · intro h
    -- The owner realizes every bounded mask with distinct physical labels,
    -- beta FIRST and alpha LAST, then inserts fresh at E.length (true) or
    -- (E ++ [beta] ++ F).length (false), proving both literal earWord identities.
    -- two_blocks and inStrip_prefix give every natural take; source_total
    -- supplies the old and inserted zero sums separately.
    exact mask_implies_joint a b ha hb true (hm.mpr h)

end D5.S3.Combinatorics.Circle.ReversedHighPhaseTwoNegativeClassification
