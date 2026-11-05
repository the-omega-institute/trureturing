import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.Domain
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail.PhysicalBanks

/-! Prepared residual construction.  Additional original-owner publications used directly:
   PacketNormalForm.Source: chainOf, weightedMask, packet_masses,
     base, newBase, oldValue, newValue;
   SecondPeakParityTail.PhysicalBanks: local_chain.
   Private implementation dependencies of those declarations remain at their
   original owners.  No source/centered-orbit proof is copied here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open scoped BigOperators
open PacketNormalForm

/-- Recover the exact mask from the actual physical labels in a bank.
The existing chain classifier and binary geometric-sum theorem supply the
two identifications; disjoint chain images justify the biUnion sum. -/
theorem physical_weighted_mask (a b c d : ℕ) (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain-1)
      (fun bank => M bank chain)) (bank r : Fin 4) :
    weightedMask b c d (physicalBank a b c d M bank) r = (M bank r : ℤ) := by
  classical
  have hbound (chain : Fin 4) (e : ℕ) (he : e ∈ bits (M bank chain)) :
      e < chainLength a b c d chain-1 :=
    SecondPeakHighD.bit_below (M bank chain) _ e ((hinv chain).capacity bank)
      ((mem_bits _ _).mp he)
  have hclass (chain : Fin 4) (e : ℕ) (he : e ∈ bits (M bank chain)) :
      chainOf b c d (chainStart b c d chain+e) = chain :=
    SecondPeakParityTail.local_chain a b c d chain e (hbound chain e he)
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 4)))
      (fun chain => (bits (M bank chain)).image (chainStart b c d chain + ·)) := by
    intro cr hcr cs hcs hne
    apply Finset.disjoint_left.mpr
    intro i hir his
    obtain ⟨er,her,hpr⟩ := Finset.mem_image.mp hir
    obtain ⟨es,hes,hps⟩ := Finset.mem_image.mp his
    exact hne (SecondPeakLowXTail.physical_chain_unique a b c d cr cs er es
      (hbound cr er her) (hbound cs es hes) (hpr.trans hps.symm))
  unfold weightedMask
  rw [physicalBank, Finset.sum_biUnion hdis]
  calc
    (∑ chain ∈ (Finset.univ : Finset (Fin 4)),
      ∑ i ∈ (bits (M bank chain)).image (chainStart b c d chain + ·),
        if chainOf b c d i = r then
          (2 : ℤ) ^ (i-chainStart b c d (chainOf b c d i)) else 0) =
        ∑ chain ∈ (Finset.univ : Finset (Fin 4)),
          if chain = r then (M bank chain : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro chain hchain
      rw [Finset.sum_image (by
        intro e he f hf hef
        exact Nat.add_left_cancel hef)]
      by_cases hcr : chain = r
      · subst chain
        simp only [ite_true]
        calc
          (∑ e ∈ bits (M bank r),
            if chainOf b c d (chainStart b c d r+e) = r then
              (2 : ℤ) ^ ((chainStart b c d r+e)-
                chainStart b c d (chainOf b c d (chainStart b c d r+e))) else 0) =
              ∑ e ∈ bits (M bank r), (2 : ℤ)^e := by
            apply Finset.sum_congr rfl
            intro e he
            rw [hclass r e he]
            simp
          _ = (M bank r : ℤ) := by
            exact_mod_cast (Finset.sum_toFinset_bitIndices_two_pow (M bank r))
      · simp only [hcr, ite_false]
        apply Finset.sum_eq_zero
        intro e he
        rw [hclass chain e he]
        simp only [hcr, ite_false]
    _ = (M bank r : ℤ) := by simp

/-- These are the actual old and matched-new masses.  In particular newBase
is the canonical [2A,2B-1,2L-z-1,2K-y(z+1)-1], not an alternative model. -/
theorem physical_masses (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (M : Fin 4 → Fin 4 → ℕ)
    (hinv : ∀ chain, MaskInventory (chainLength a b c d chain-1)
      (fun bank => M bank chain)) (bank : Fin 4) :
    (∑ i ∈ physicalBank a b c d M bank, oldValue a b c d i) =
      ∑ chain : Fin 4, base a b c d chain * (M bank chain : ℤ) ∧
    (∑ i ∈ physicalBank a b c d M bank, newValue a b c d i) =
      ∑ chain : Fin 4, newBase a b c d chain * (M bank chain : ℤ) := by
  have hp := PacketNormalForm.packet_masses a b c d ha hb hc hd
    (physicalBank a b c d M bank)
    (fun i hi => physical_labels a b c d ha hb hc hd M hinv bank i hi)
  simpa only [physical_weighted_mask a b c d M hinv bank] using hp

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
