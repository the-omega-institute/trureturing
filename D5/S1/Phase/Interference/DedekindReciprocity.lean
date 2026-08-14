/- GID: D5/S1/Phase/Interference/DedekindReciprocity
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/DedekindReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dedekind reciprocity follows from finite residue sums and a lattice-point exchange. -/

/- Library-search audit trail (2026-08-14):
   * Exact local hit: `DedekindBhkCertificates.dedekindSum` and its rational
     sawtooth definition are the frozen phase-1 API used here.
   * Pinned-library hits: `Int.fract_div_natCast_eq_div_natCast_mod`,
     `Finset.sum_range_id_mul_two`, `Nat.ModEq.cancel_right_of_coprime`,
     and the `Finset` product/filter summation lemmas.
   * Searches in `D5` and pinned mathlib found no existing Dedekind
     reciprocity theorem or general coprime floor-sum theorem.
-/

import D5.S1.Phase.Interference.DedekindReciprocityLattice

namespace D5.S1.Phase.Interference.DedekindReciprocity

open D5.S1.Phase.Interference.DedekindBhkCertificates
open D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
open D5.S1.Phase.Interference.DedekindReciprocityLattice

/-- Euclidean division rewrites the residue cross term through the weighted
floor sum. -/
theorem residueCrossTerm_eq_weightedFloorSum (d c : Nat) :
    residueCrossTerm d c =
      (d : Rat) *
          (((c : Rat) - 1) * (c : Rat) * (2 * (c : Rat) - 1) / 6) -
        (c : Rat) * weightedFloorSum d c := by
  unfold residueCrossTerm weightedFloorSum
  calc
    (∑ k ∈ Finset.Ico 1 c,
        (k : Rat) * (((k * d) % c : Nat) : Rat)) =
      (Finset.Ico 1 c).sum (fun k ↦
        (d : Rat) * (k : Rat) ^ 2 -
          (c : Rat) *
            ((k : Rat) * (((k * d) / c : Nat) : Rat))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hdecomp :
          (((k * d) % c : Nat) : Rat) +
              (c : Rat) * (((k * d) / c : Nat) : Rat) =
            (k : Rat) * (d : Rat) := by
        exact_mod_cast Nat.mod_add_div (k * d) c
      nlinarith
    _ = (d : Rat) *
          (∑ k ∈ Finset.Ico 1 c, (k : Rat) ^ 2) -
        (c : Rat) *
          (∑ k ∈ Finset.Ico 1 c,
            (k : Rat) * (((k * d) / c : Nat) : Rat)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [sum_Ico_cast_sq]

/-- The normalized residue cross terms satisfy the symmetric identity needed
for reciprocity. -/
theorem normalized_residueCrossTerm_reciprocity {c d : Nat}
    (hc : 0 < c) (hd : 0 < d) (hcd : c.Coprime d) :
    residueCrossTerm d c / (c : Rat) ^ 2 +
        residueCrossTerm c d / (d : Rat) ^ 2 =
      ((c : Rat) / (d : Rat) + (d : Rat) / (c : Rat) +
          1 / ((c : Rat) * (d : Rat))) / 12 +
        ((c : Rat) + (d : Rat) - 3) / 4 := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  have hdRat : (d : Rat) ≠ 0 := by exact_mod_cast hd.ne'
  rw [residueCrossTerm_eq_weightedFloorSum,
    residueCrossTerm_eq_weightedFloorSum]
  calc
    ((d : Rat) *
              (((c : Rat) - 1) * (c : Rat) *
                (2 * (c : Rat) - 1) / 6) -
            (c : Rat) * weightedFloorSum d c) /
          (c : Rat) ^ 2 +
        ((c : Rat) *
              (((d : Rat) - 1) * (d : Rat) *
                (2 * (d : Rat) - 1) / 6) -
            (d : Rat) * weightedFloorSum c d) /
          (d : Rat) ^ 2 =
      (d : Rat) *
            (((c : Rat) - 1) * (c : Rat) *
              (2 * (c : Rat) - 1) / 6) /
          (c : Rat) ^ 2 +
        (c : Rat) *
            (((d : Rat) - 1) * (d : Rat) *
              (2 * (d : Rat) - 1) / 6) /
          (d : Rat) ^ 2 -
        ((d : Rat) * weightedFloorSum d c +
          (c : Rat) * weightedFloorSum c d) /
            ((c : Rat) * (d : Rat)) := by
      field_simp
      ring
    _ = _ := by
      rw [weightedFloorSum_exchange hc hd hcd,
        latticeDifference_closed hc hd hcd]
      field_simp
      ring

/-- Expanding the finite residue formula leaves the normalized cross term and
the elementary constant correction. -/
theorem dedekindSum_eq_residueCrossTerm {d c : Nat} (hc : 0 < c)
    (hdc : d.Coprime c) :
    dedekindSum d c =
      residueCrossTerm d c / (c : Rat) ^ 2 - ((c : Rat) - 1) / 4 := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  rw [dedekindSum_eq_mod_sum hc hdc]
  have hterm :
      (∑ k ∈ Finset.Ico 1 c,
          (((k % c : Nat) : Rat) / (c : Rat) - 1 / 2) *
            ((((k * d) % c : Nat) : Rat) / (c : Rat) - 1 / 2)) =
        (Finset.Ico 1 c).sum (fun k ↦
          (k : Rat) * (((k * d) % c : Nat) : Rat) / (c : Rat) ^ 2 -
            (k : Rat) / (2 * (c : Rat)) -
            (((k * d) % c : Nat) : Rat) / (2 * (c : Rat)) +
            1 / 4) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.mod_eq_of_lt (Finset.mem_Ico.mp hk).2]
    field_simp
    ring
  rw [hterm]
  unfold residueCrossTerm
  have hsumExpand :
      (Finset.Ico 1 c).sum (fun k ↦
          (k : Rat) * (((k * d) % c : Nat) : Rat) / (c : Rat) ^ 2 -
            (k : Rat) / (2 * (c : Rat)) -
            (((k * d) % c : Nat) : Rat) / (2 * (c : Rat)) +
            1 / 4) =
        (Finset.Ico 1 c).sum (fun k ↦
            (k : Rat) * (((k * d) % c : Nat) : Rat)) /
              (c : Rat) ^ 2 -
          (Finset.Ico 1 c).sum (fun k ↦ (k : Rat)) /
              (2 * (c : Rat)) -
          (Finset.Ico 1 c).sum (fun k ↦
              (((k * d) % c : Nat) : Rat)) /
                (2 * (c : Rat)) +
          (((Finset.Ico 1 c).card : Nat) : Rat) / 4 := by
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_const]
    simp only [nsmul_eq_mul, Finset.sum_mul]
    ring
  rw [hsumExpand, sum_Ico_cast, sum_mul_mod hc hdc, Nat.card_Ico]
  have hcOne : 1 ≤ c := hc
  push_cast [Nat.cast_sub hcOne]
  field_simp
  ring

/-- Dedekind reciprocity, proved entirely by the explicit finite-sum and
coprime lattice-point ladder. -/
theorem dedekind_reciprocity {c d : Nat}
    (hc : 0 < c) (hd : 0 < d) (hcd : c.Coprime d) :
    dedekindSum d c + dedekindSum c d =
      -(1 / 4) +
        ((c : Rat) / (d : Rat) + (d : Rat) / (c : Rat) +
          1 / ((c : Rat) * (d : Rat))) / 12 := by
  rw [dedekindSum_eq_residueCrossTerm hc hcd.symm,
    dedekindSum_eq_residueCrossTerm hd hcd]
  have hnormalized := normalized_residueCrossTerm_reciprocity hc hd hcd
  calc
    residueCrossTerm d c / (c : Rat) ^ 2 - ((c : Rat) - 1) / 4 +
        (residueCrossTerm c d / (d : Rat) ^ 2 - ((d : Rat) - 1) / 4) =
      (residueCrossTerm d c / (c : Rat) ^ 2 +
          residueCrossTerm c d / (d : Rat) ^ 2) -
        (((c : Rat) - 1) + ((d : Rat) - 1)) / 4 := by ring
    _ = _ := by rw [hnormalized]; ring

/-- Exact anti-vacuity check for the coprime pair `(3,4)`. -/
theorem dedekind_reciprocity_three_four :
    dedekindSum 3 4 + dedekindSum 4 3 = -(5 / 72) := by
  have h := dedekind_reciprocity (c := 4) (d := 3)
    (by norm_num) (by norm_num) (by decide)
  norm_num at h ⊢
  exact h

example : Nonempty Rat := inferInstance

example : (4 : Nat).Coprime 3 ∧ 0 < (4 : Nat) ∧ 0 < (3 : Nat) := by
  decide

#print axioms sawtooth_div_eq_mod
#print axioms sum_div_gauss
#print axioms weightedFloorSum_exchange
#print axioms dedekind_reciprocity
#print axioms dedekind_reciprocity_three_four

end D5.S1.Phase.Interference.DedekindReciprocity
