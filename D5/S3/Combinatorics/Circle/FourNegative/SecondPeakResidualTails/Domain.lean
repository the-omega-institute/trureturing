import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.PhysicalLabels

/-! Prepared residual construction.  The original domain is unchanged.  The theorem in this file
   constructs label inventories and multiplicities only.  It does NOT assert
   either OriginalOrder, a joint strip theorem, or a Circle result.

   The still-required endpoint is, for every OriginalDomain a b c d, one
   sigma : List (Fin (a+b+c+d)) with both
     OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma
   and
     OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
       (earWord (a+b+c+d) sigma 0).
   Separate zero totals and every natural replicate/take are then to be
   obtained from the canonical zero_period_transport, without a copied proof.
   Original-owner publication also needed here: Structure.insertAt. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open PacketNormalForm

def OriginalDomain (a b c d : ℕ) : Prop :=
  d < b ∧ ((c = 2 ∧ a = 3 ∧ 4 ≤ d) ∨
    (3 ≤ c ∧ a = c+1 ∧ 2*c ≤ d) ∨ (c = 3 ∧ a = 5 ∧ 7 ≤ d))

def residualBanks (a b c d : ℕ) : Fin 4 → Fin 4 → ℕ :=
  if c = 2 then c2Banks (d-3) (b-d-1)
  else if a = c+1 then diagonalBanks c (d-2*c) (b-d-1)
  else c3Banks (d-5) (b-d-1)

def residualOrder (c d : ℕ) : Fin 4 → Fin 4 :=
  if c = 2 then c2Order (d-3) else normalOrder

def earSlot0 : Fin 4 := 0
def cut0 : ℕ := earSlot0.val

noncomputable def physicalEarWord (a b c d : ℕ) : List ℕ :=
  insertAt (size a b c d)
    (physicalWord a b c d (residualBanks a b c d) (residualOrder c d)) cut0

theorem residual_inventory (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    ∀ chain : Fin 4, MaskInventory (chainLength a b c d chain-1)
      (fun bank => residualBanks a b c d bank chain) := by
  obtain ⟨hb,hshape⟩ := hdom
  rcases hshape with h2 | hdiag | h3
  · obtain ⟨rfl,rfl,hd⟩ := h2
    have he : 1 ≤ d-3 := by omega
    intro chain
    have hi := c2_inventory (d-3) (b-d-1) he chain
    have hw : ((![d-3+2,1,(d-3)+(b-d-1)+3,2] : Fin 4 → ℕ) chain) =
        chainLength 3 b 2 d chain-1 := by
      fin_cases chain <;> simp [chainLength] <;> omega
    rw [hw] at hi
    simpa [residualBanks] using hi
  · obtain ⟨hc,rfl,hd⟩ := hdiag
    intro chain
    have hi := diagonal_inventory c (d-2*c) (b-d-1) hc chain
    have hw : ((![c+diagonalExponent c (d-2*c),c-1,
        diagonalExponent c (d-2*c)+(b-d-1)+(c+1),c] : Fin 4 → ℕ) chain) =
        chainLength (c+1) b c d chain-1 := by
      fin_cases chain <;> simp [chainLength, diagonalExponent] <;> omega
    rw [hw] at hi
    have hc2 : c ≠ 2 := by omega
    simpa [residualBanks, hc2] using hi
  · obtain ⟨rfl,rfl,hd⟩ := h3
    have he : 2 ≤ d-5 := by omega
    intro chain
    have hi := c3_inventory (d-5) (b-d-1) (by omega) chain
    have hw : ((![d-5+4,2,(d-5)+(b-d-1)+5,4] : Fin 4 → ℕ) chain) =
        chainLength 5 b 3 d chain-1 := by
      fin_cases chain <;> simp [chainLength] <;> omega
    rw [hw] at hi
    simpa [residualBanks] using hi

theorem residual_order_perm (c d : ℕ) :
    ([residualOrder c d 0,residualOrder c d 1,
      residualOrder c d 2,residualOrder c d 3] : List (Fin 4)).Perm [0,1,2,3] := by
  by_cases hc : c = 2
  · by_cases he : d-3 = 4 <;>
      simp only [residualOrder, hc, c2Order, he, ite_true, ite_false, normalOrder] <;> decide
  · simp only [residualOrder, hc, ite_false, normalOrder]
    decide

/-- This is the label part of the full original construction, over the full
original domain, including the exceptional c2 terminal schedule. -/
theorem original_physical_partition (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    (physicalWord a b c d (residualBanks a b c d) (residualOrder c d) : Multiset ℕ) =
      (List.range (size a b c d) : Multiset ℕ) := by
  have ha : 2 ≤ a := by rcases hdom.2 with h | h | h <;> omega
  have hb : 2 ≤ b := by rcases hdom.2 with h | h | h <;> have := hdom.1 <;> omega
  have hc : 2 ≤ c := by rcases hdom.2 with h | h | h <;> omega
  have hd : 2 ≤ d := by rcases hdom.2 with h | h | h <;> omega
  exact physical_partition a b c d ha hb hc hd (residualBanks a b c d)
    (residual_inventory a b c d hdom) (residualOrder c d) (residual_order_perm c d)

/-- The fresh physical label is inserted at the literal cut 0.  This remains
a multiplicity statement; the new centered-source strip is still required. -/
theorem original_ear_partition (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    (physicalEarWord a b c d : Multiset ℕ) =
      (List.range (size a b c d+1) : Multiset ℕ) := by
  have hp := original_physical_partition a b c d hdom
  simp only [physicalEarWord, cut0, earSlot0, insertAt, List.take_zero,
    List.drop_zero, List.nil_append, List.singleton_append]
  rw [← Multiset.cons_coe, hp]
  rw [List.range_succ, ← Multiset.coe_add]
  exact (Multiset.singleton_add _ _).symm.trans (add_comm _ _)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
