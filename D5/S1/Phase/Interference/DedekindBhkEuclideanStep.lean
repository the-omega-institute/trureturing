/- GID: D5/S1/Phase/Interference/DedekindBhkEuclideanStep
   generality: I
   mirror-B: D5/B/S1/Phase/Interference/DedekindBhkEuclideanStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The finite BHK base and reciprocity step hold, but the requested walk sign fails. -/

/- Library-search audit trail (2026-08-14):
   * `rg -n -i 'bhk|barkan|hickerson|knuth|IsNormalOddCF|12 \* dedekindSum'
     D5 .lake/packages/mathlib/Mathlib --glob '*.lean'` found only the frozen
     zero-walk certificates and `SeatTowerArithmetic.bhk_implies_w3_walk`,
     which assumes rather than proves the requested BHK formula.
   * `rg -n 'dedekind_reciprocity|s_mod|sum_Ico_cast_sq|alternatingWalk'
     D5 .lake/packages/mathlib/Mathlib --glob '*.lean'` found the exact frozen
     finite-sum, reciprocity, modular-reduction, and walk APIs used below.
   * Pinned mathlib provides `GenContFract` and continuant recurrences, but no
     BHK induction, Dedekind-sum definition, or theorem with the statements below.
-/

import D5.S1.Phase.Interference.DedekindReciprocity

namespace D5.S1.Phase.Interference.DedekindBhkEuclideanStep

open D5.S1.Phase.WalkFormula
open D5.S1.Phase.Interference.DedekindBhkCertificates
open D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
open D5.S1.Phase.Interference.DedekindReciprocity

/-- The one-coefficient continued-fraction base has the classical exact value. -/
theorem dedekind_sum_one_closed {c : Nat} (hc : 0 < c) :
    dedekindSum 1 c =
      ((c : Rat) - 1) * ((c : Rat) - 2) / (12 * (c : Rat)) := by
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  rw [dedekindSum_eq_mod_sum hc (Nat.coprime_one_left c)]
  have hreduce :
      (Finset.Ico 1 c).sum (fun k =>
          (((k % c : Nat) : Rat) / (c : Rat) - 1 / 2) *
            ((((k * 1) % c : Nat) : Rat) / (c : Rat) - 1 / 2)) =
        (Finset.Ico 1 c).sum (fun k =>
          ((k : Rat) / (c : Rat) - 1 / 2) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.mod_eq_of_lt (Finset.mem_Ico.mp hk).2, Nat.mul_one,
      Nat.mod_eq_of_lt (Finset.mem_Ico.mp hk).2]
    ring
  rw [hreduce]
  have hsumExpand :
      (Finset.Ico 1 c).sum (fun k =>
          ((k : Rat) / (c : Rat) - 1 / 2) ^ 2) =
        (Finset.Ico 1 c).sum (fun k => (k : Rat) ^ 2) / (c : Rat) ^ 2 -
          (Finset.Ico 1 c).sum (fun k => (k : Rat)) / (c : Rat) +
          (((Finset.Ico 1 c).card : Nat) : Rat) / 4 := by
    have hterm :
        (Finset.Ico 1 c).sum (fun k =>
            ((k : Rat) / (c : Rat) - 1 / 2) ^ 2) =
          (Finset.Ico 1 c).sum (fun k =>
            (k : Rat) ^ 2 / (c : Rat) ^ 2 -
              (k : Rat) / (c : Rat) + 1 / 4) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hterm]
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsumExpand, sum_Ico_cast_sq, sum_Ico_cast, Nat.card_Ico]
  have hcOne : 1 <= c := hc
  push_cast [Nat.cast_sub hcOne]
  field_simp [hcRat]
  ring

/-- The one-coefficient BHK base agrees with the frozen walk after correcting
the requested walk sign from minus to plus. -/
theorem bhk_plus_walk_single_coefficient {c : Nat} (hc : 0 < c) :
    12 * dedekindSum 1 c =
      -3 + (((1 + 1 : Nat) : Rat) / (c : Rat)) +
        (alternatingWalk [(c : Int)] : Rat) := by
  rw [dedekind_sum_one_closed hc]
  have hcRat : (c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [alternatingWalk, sub_zero, Int.cast_natCast]
  field_simp [hcRat]
  ring

/-- One Euclidean continued-fraction shift is exactly Dedekind reciprocity,
with the reversed numerator reduced modulo the new denominator. -/
theorem dedekind_reciprocity_cf_step {d c : Nat}
    (hc : 0 < c) (hd : 0 < d) (hcd : c.Coprime d) :
    12 * dedekindSum d c =
      -3 + (c : Rat) / (d : Rat) + (d : Rat) / (c : Rat) +
        1 / ((c : Rat) * (d : Rat)) -
          12 * dedekindSum (c % d) d := by
  rw [s_mod c d]
  calc
    12 * dedekindSum d c =
        12 * (dedekindSum d c + dedekindSum c d) -
          12 * dedekindSum c d := by ring
    _ = 12 *
          (-(1 / 4) +
            ((c : Rat) / (d : Rat) + (d : Rat) / (c : Rat) +
              1 / ((c : Rat) * (d : Rat))) / 12) -
            12 * dedekindSum c d := by
      rw [dedekind_reciprocity hc hd hcd]
    _ = _ := by ring

/-- The first nonzero-walk odd expansion exposes the sign obstruction in the
requested finale: the minus-walk equation fails, while the plus-walk equation holds. -/
theorem bhk_minus_walk_counterexample :
    (1 / (2 + 1 / (1 + 1 / 1)) : Rat) = 2 / 5 ∧
      ((3 * 2 : Nat) % 5 = 1) ∧
      alternatingWalk [2, 1, 1] = 2 ∧
      dedekindSum 2 5 = 0 ∧
      (12 * dedekindSum 2 5 : Rat) ≠
        -3 + (((3 + 2 : Nat) : Rat) / 5) -
          (alternatingWalk [2, 1, 1] : Rat) ∧
      (12 * dedekindSum 2 5 : Rat) =
        -3 + (((3 + 2 : Nat) : Rat) / 5) +
          (alternatingWalk [2, 1, 1] : Rat) := by
  norm_num [dedekindSum, Nat.Icc_eq_range', List.range', sawtooth,
    Int.fract_div_natCast_eq_div_natCast_mod, alternatingWalk]

example : (5 : Nat).Coprime 2 ∧ 0 < (5 : Nat) ∧ 0 < (2 : Nat) := by
  decide

example : Nonempty Rat := inferInstance

#print axioms dedekind_sum_one_closed
#print axioms bhk_plus_walk_single_coefficient
#print axioms dedekind_reciprocity_cf_step
#print axioms bhk_minus_walk_counterexample

end D5.S1.Phase.Interference.DedekindBhkEuclideanStep
