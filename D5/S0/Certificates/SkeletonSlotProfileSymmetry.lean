/- GID: D5/S0/Certificates/SkeletonSlotProfileSymmetry
   generality: G
   mirror-B: D5/B/S0/Certificates/SkeletonSlotProfileSymmetry
   mirror-E: none(waiver:proved-slot-renaming-symmetry)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Defs]
   digest: Slot renaming preserves the same skeleton, and sorting the two unanchored five-color profiles leaves a complete 168-case output cover. -/

import D5.S0.Certificates.SkeletonSlotGapConstraintTransport

/- The representation changes only names of slots. It does not merge states
   sharing an output, forbid self-loops, or require all slots to be used.
   The 168 count concerns normalized five-color output configurations; it is
   not a refutation of any of the remaining cases. Lean was not run here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SkeletonSlotProfileSymmetry

open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S0.Certificates.SkeletonSlotCNF
open D5.S0.Certificates.SkeletonSlotZeroResponse
open D5.S0.Certificates.SkeletonSlotGapConstraintTransport

variable {r s : Nat} {K : Skeleton (Fin 4) (Fin r)}

/-- Rename slots while retaining exactly the same Skeleton object. -/
def relabel (W : SlotWitness K s) (e : Equiv.Perm (Fin s)) : SlotWitness K s where
  zeroTarget := W.zeroTarget
  slotOf := fun q => e (W.slotOf q)
  returnTarget := fun t => W.returnTarget (e.symm t)
  transientOutput := fun t => W.transientOutput (e.symm t)
  zero_eq := W.zero_eq
  one_eq := by intro q; simpa using W.one_eq q

/-- Gap transition rows transform by conjugacy, including all self-loops. -/
theorem relabel_gap (W : SlotWitness K s) (e : Equiv.Perm (Fin s))
    (k : Nat) (t : Fin s) :
    gapSlot (relabel W e) k (e t) = e (gapSlot W k t) := by
  simp [gapSlot, advance, relabel]

/-- Both observed channels transform with the slot names. -/
theorem relabel_readout (W : SlotWitness K s) (e : Equiv.Perm (Fin s))
    (channel : TerminalChannel) (t : Fin s) :
    slotReadout (relabel W e) channel (e t) = slotReadout W channel t := by
  cases channel <;> simp [slotReadout, relabel]

/-- A joint output code orders profiles, without identifying equal profiles. -/
def profileCode (W : SlotWitness K s) (t : Fin s) : Nat :=
  4 * (W.transientOutput t).val + (K.zeroOutput (W.returnTarget t)).val

private def swapExtras : Equiv.Perm (Fin 5) := Equiv.swap 3 4

/-- Sort only the two slots not named by the three distinct-output observations. -/
def orderedFive (W : SlotWitness K 5) : SlotWitness K 5 :=
  if profileCode W 3 ≤ profileCode W 4 then W else relabel W swapExtras

private theorem swapped_profile (W : SlotWitness K 5) (t : Fin 5) :
    profileCode (relabel W swapExtras) t = profileCode W (swapExtras t) := by
  simp [profileCode, relabel, swapExtras]

/-- Every five-slot realization has an equivalent ordered profile presentation. -/
theorem orderedFive_profiles (W : SlotWitness K 5) :
    profileCode (orderedFive W) 3 ≤ profileCode (orderedFive W) 4 := by
  unfold orderedFive
  split_ifs with h
  · exact h
  · simpa [swapped_profile, swapExtras] using Nat.le_of_lt (Nat.lt_of_not_ge h)

/-- The output and return of each named anchor are unchanged. -/
theorem orderedFive_anchor (W : SlotWitness K 5) (i : Fin 3) :
    (orderedFive W).transientOutput ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ =
      W.transientOutput ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ ∧
    (orderedFive W).returnTarget ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ =
      W.returnTarget ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩ := by
  unfold orderedFive
  split_ifs
  · exact ⟨rfl,rfl⟩
  · fin_cases i <;> simp [relabel, swapExtras]

/-- Three anchored Boolean post-zero outputs and two ordered six-valued
extra profiles. The actual digit labels on each extra slot are 1,2,3. -/
def fiveOutputCases : Finset (Fin 8 × (Fin 6 × Fin 6)) :=
  Finset.univ.filter fun c => c.2.1 ≤ c.2.2

/-- Complete ordered output enumeration, not a sample-search result. -/
theorem fiveOutputCases_card : fiveOutputCases.card = 168 := by decide

/-- Either the extra profiles are already ordered or their interchange is. -/
theorem fiveOutputCases_cover (a : Fin 8) (p q : Fin 6) :
    (a,(p,q)) ∈ fiveOutputCases ∨ (a,(q,p)) ∈ fiveOutputCases := by
  rcases le_total p q with h | h
  · exact Or.inl (by simpa [fiveOutputCases] using h)
  · exact Or.inr (by simpa [fiveOutputCases] using h)

#print axioms relabel_gap
#print axioms orderedFive_profiles
#print axioms fiveOutputCases_card

end D5.S0.Certificates.SkeletonSlotProfileSymmetry
