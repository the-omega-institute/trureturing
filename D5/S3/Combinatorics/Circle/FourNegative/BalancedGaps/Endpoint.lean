/- GID: D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Endpoint
   mirror-E: none(waiver:balanced-physical-joint-lift)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete balanced four-independent-gap physical joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Certificate

/-! The complete balanced chamber; unrestricted four-gap physical J remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
open SourceWidth PeriodicShortening RunFirstEarTransport PacketNormalForm
open private offsets from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Arithmetic
open private balanced_certificate from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Certificate

/-- One actual old physical permutation and one literal ear cut for every balanced source. -/
theorem actualSource_balanced_gaps_joint_lift (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hbal : max (max a b) (max c d) ≤ min (min a b) (min c d)+1) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ cut : ℕ, cut≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut) := by
  apply (actual_four_packet_iff a b c d ha hb hc hd).mpr
  let s := min (min a b) (min c d)
  have hs : 2≤s := by dsimp [s]; omega
  have hsa : a=s ∨ a=s+1 := by dsimp [s]; omega
  have hsb : b=s ∨ b=s+1 := by dsimp [s]; omega
  have hsc : c=s ∨ c=s+1 := by dsimp [s]; omega
  have hsd : d=s ∨ d=s+1 := by dsimp [s]; omega
  rcases hsa with hea|hea <;> rcases hsb with heb|heb <;>
    rcases hsc with hec|hec <;> rcases hsd with hed|hed
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 0
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 1
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 2
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 3
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 4
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 5
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 6
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 7
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 8
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 9
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 10
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 11
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 12
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 13
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 14
  · simpa [offsets,hea,heb,hec,hed] using balanced_certificate s hs 15

#print axioms actualSource_balanced_gaps_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
