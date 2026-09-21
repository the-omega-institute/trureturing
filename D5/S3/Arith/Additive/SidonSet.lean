/- GID: D5/S3/Arith/Additive/SidonSet
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/SidonSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Prod, mathlib/module/Mathlib.Data.Fintype.Basic, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Sidon subsets of the natural interval from 1 to N satisfy the classical difference-counting cardinality bound -/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S3.Arith.Additive.SidonSet

/-- A Sidon set has unique representations of pairwise sums up to exchanging the summands,
including sums in which the two summands coincide. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Counting distinct nonzero differences bounds the size of a Sidon set in `[1, N]`. -/
theorem card_mul_card_sub_one_le (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hSidon : IsSidon (A : Set ℕ)) :
    A.card * (A.card - 1) ≤ 2 * (N - 1) := by
  let f : ℕ × ℕ → Bool × ℕ :=
    fun p => (decide (p.1 < p.2), p.2 - p.1 + (p.1 - p.2))
  have hcount := Finset.card_le_card_of_injOn f
    (s := A.offDiag) (t := Finset.univ ×ˢ Finset.Icc 1 (N - 1))
    (by
      intro p hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      have haN := Finset.mem_Icc.mp (hA ha)
      have hbN := Finset.mem_Icc.mp (hA hb)
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and,
        Finset.mem_Icc, f]
      omega)
    (by
      intro p hp q hq heq
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨hc, hd, _⟩ := Finset.mem_offDiag.mp hq
      have hsign : (p.1 < p.2) ↔ (q.1 < q.2) := by
        have := congrArg Prod.fst heq
        simpa only [f, decide_eq_decide] using this
      have hmag : p.2 - p.1 + (p.1 - p.2) = q.2 - q.1 + (q.1 - q.2) :=
        congrArg Prod.snd heq
      have hsum : p.1 + q.2 = q.1 + p.2 := by omega
      rcases hSidon ha hd hc hb hsum with h | h
      · exact Prod.ext h.1 h.2.symm
      · exact (hab h.1).elim)
  simpa [Finset.offDiag_card, Finset.card_product, Nat.mul_sub] using hcount

end D5.S3.Arith.Additive.SidonSet
