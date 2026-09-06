/- GID: D5/S3/PrimeGaps/OptimalAdmissibleEightTuple
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/OptimalAdmissibleEightTuple
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the exact minimal admissible eight-tuple diameter by a complete modular obstruction. -/

import D5.S3.PrimeGaps.AdmissibleWindowFiniteSearch

/-! # The exact eight-tuple optimum

The new lower bound excludes every admissible eight-tuple of width below 26,
using normalization completeness and a kernel-checked finite residue-cover
bound. This supports the paper's optimization claim, beyond certification of
a single positive tuple. The numerical optimum is standard number theory;
the contribution here is its proof against the existing all-prime window API.
-/

namespace D5.S3.PrimeGaps.OptimalAdmissibleEightTuple

open D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
open D5.S3.PrimeGaps.AdmissibleWindowFiniteSearch

/-- Existence at width B and nonexistence at every smaller natural width. -/
def MinimalAdmissibleDiameter (k B : Nat) : Prop :=
  AdmissibleWindowWitness k B ∧
    ∀ C : Nat, C < B → ¬ AdmissibleWindowWitness k C

/-- A standard admissible eight-element tuple of width 26. -/
def optimalEightTuple : Finset Nat := {0, 2, 6, 8, 12, 18, 20, 26}

/-- The normalized offsets surviving specified omitted classes modulo 3, 5, and 7. -/
def eightObstructionSet (a : ZMod 3) (b : ZMod 5) (c : ZMod 7) : Finset Nat :=
  (Finset.range 26).filter (fun x => Even x ∧
    (x : ZMod 3) ≠ a ∧ (x : ZMod 5) ≠ b ∧ (x : ZMod 7) ≠ c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Every nonzero omitted-residue choice leaves at most seven normalized offsets.
This finite certificate is checked by kernel reduction, with no native oracle. -/
theorem eightObstructionSet_card_le_seven :
    ∀ (a : ZMod 3) (b : ZMod 5) (c : ZMod 7),
      a ≠ 0 → b ≠ 0 → c ≠ 0 → (eightObstructionSet a b c).card ≤ 7 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The upper bound supplies its own cardinality, all-prime admissibility, and width. -/
theorem admissibleWindowWitness_8_26 : AdmissibleWindowWitness 8 26 := by
  refine ⟨optimalEightTuple, by decide,
    (naturalTupleAdmissible_iff_small_primes _).mpr ?_, by decide⟩
  decide

/-- No eight-element admissible tuple fits in a window narrower than 26.
The universal negative result follows from the finite modular obstruction and
the general normalization theorem, without enumerating arbitrary tuples. -/
theorem no_admissibleWindowWitness_8_lt_26 {B : Nat} (hB : B < 26) :
    ¬ AdmissibleWindowWitness 8 B := by
  rintro ⟨H, hc, ha, hb⟩
  have hn : H.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hcard, hzero, hadm, hbound⟩ := normalizeNatTuple_spec H B hn ha hb
  obtain ⟨a, ha⟩ := hadm 3 (by norm_num)
  obtain ⟨b, hb⟩ := hadm 5 (by norm_num)
  obtain ⟨c, hcmod⟩ := hadm 7 (by norm_num)
  have ha0 : a ≠ 0 := Ne.symm (by simpa using ha 0 hzero)
  have hb0 : b ≠ 0 := Ne.symm (by simpa using hb 0 hzero)
  have hc0 : c ≠ 0 := Ne.symm (by simpa using hcmod 0 hzero)
  have hsub : normalizeNatTuple H ⊆ eightObstructionSet a b c := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · exact (hbound x hx).trans_lt hB
    · exact ⟨admissible_zero_even _ hzero hadm x hx, ha x hx, hb x hx, hcmod x hx⟩
  have hle := (Finset.card_le_card hsub).trans
    (eightObstructionSet_card_le_seven a b c ha0 hb0 hc0)
  omega

/-- The exact optimum for eight admissible offsets is 26. -/
theorem minimalAdmissibleDiameter_eight_26 : MinimalAdmissibleDiameter 8 26 :=
  ⟨admissibleWindowWitness_8_26, fun _ hB => no_admissibleWindowWitness_8_lt_26 hB⟩

/-- Completeness certifies the negative result of the executable width-25 search. -/
theorem admissibleWindowCheck_eight_25 : admissibleWindowCheck 8 25 = false := by
  cases h : admissibleWindowCheck 8 25 with
  | false => rfl
  | true =>
    exact False.elim (no_admissibleWindowWitness_8_lt_26 (by decide)
      ((admissibleWindowCheck_eq_true_iff 8 25 (by decide)).mp h))

/-- Soundness and completeness also certify success at the optimal width. -/
theorem admissibleWindowCheck_eight_26 : admissibleWindowCheck 8 26 = true :=
  (admissibleWindowCheck_eq_true_iff 8 26 (by decide)).mpr admissibleWindowWitness_8_26

end D5.S3.PrimeGaps.OptimalAdmissibleEightTuple
