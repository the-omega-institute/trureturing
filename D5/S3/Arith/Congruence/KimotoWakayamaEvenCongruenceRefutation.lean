/- GID: D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.claim; result=D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.result; claim=D5/S3/Arith/Congruence/KimotoWakayamaEvenCongruenceRefutation.claim
   digest: The normalized even Kimoto-Wakayama ratio fails modulo nine at (3, 5, 2, 7). -/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega

/-! Kimoto and Wakayama, arXiv:1905.01775v2, normalized numbers in Section 3.4
and the even assertion of Conjecture 3.6. The index `s` denotes weight `2*s+2`;
the weight-zero row is identically zero, as in preregistration #25637. -/

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation

/-- The normalized number of weight `2*s+2`, evaluated by the source recurrence. -/
def normalizedEven (s j : ℕ) : ℚ :=
  ((Nat.rec
    ((List.replicate (s + 1) (0 : ℚ)),
      (List.range (s + 1)).map (fun t => if t = 0 then (1 : ℚ) else 0))
    (fun k rows =>
      if k = 0 then
        (rows.2, (List.range (s + 1)).map
          (fun t => if t = 0 then (3 / 4 : ℚ) else if t = 1 then 1 else 0))
      else
        (rows.2, (List.range (s + 1)).map (fun t =>
          (((8 * ((k + 1 : ℕ) : ℚ) ^ 2 - 8 * ((k + 1 : ℕ) : ℚ) + 3) *
              rows.2.getD t 0 - 4 * (k : ℚ) ^ 2 * rows.1.getD t 0 +
              4 * (if t = 0 then 0 else rows.2.getD (t - 1) 0)) /
            (4 * ((k + 1 : ℕ) : ℚ) ^ 2)))) j).2.getD s 0

/-- Congruence in the localization of the integers away from `p`. -/
def RatCongr (p n : ℕ) (x y : ℚ) : Prop :=
  ∃ a b : ℤ, ¬ (p : ℤ) ∣ b ∧ (x - y) * b = (p : ℚ) ^ n * a

/-- The even assertion of Conjecture 3.6, restricted to odd primes. -/
def claim : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ m n s : ℕ,
    0 < m → 0 < n → 0 < s → s ≤ m * p → s ≤ m * p ^ (n - 1) →
    RatCongr p n
      ((p : ℚ) ^ (2 * s * n) * normalizedEven s (m * p ^ n) /
        ((p : ℚ) ^ (2 * s) * normalizedEven s (m * p)))
      ((p : ℚ) ^ (2 * s * (n - 1)) * normalizedEven s (m * p ^ (n - 1)) /
        ((p : ℚ) ^ (2 * s) * normalizedEven s (m * p))) ∧
    ¬ RatCongr p n
      ((p : ℚ) ^ (2 * s * (n - 1)) * normalizedEven s (m * p ^ (n - 1)) /
        ((p : ℚ) ^ (2 * s) * normalizedEven s (m * p))) 0

private lemma value_fifteen : normalizedEven 7 15 =
    7333120509469805428121 / 355769406331851217305600000 := by
  sorry

private lemma value_forty_five : normalizedEven 7 45 =
    102790658465770739117540100122976721847176041588902154700374527298060572494857673559242663743632025784157718049052857 / 57561990252524346183252148053608130482118358853580167199822526442550512853169148312714991466237887774720000000000000000 := by
  sorry

private lemma left_value :
    (3 : ℚ) ^ 28 * normalizedEven 7 45 / ((3 : ℚ) ^ 14 * normalizedEven 7 15) =
      102790658465770739117540100122976721847176041588902154700374527298060572494857673559242663743632025784157718049052857 / 248060981949704625896344570711464099546609864372154310051109270678757921001761367078238673489100800000000000 := by
  rw [value_fifteen, value_forty_five]
  norm_num

private lemma right_value :
    (3 : ℚ) ^ 14 * normalizedEven 7 15 / ((3 : ℚ) ^ 14 * normalizedEven 7 15) = 1 := by
  rw [value_fifteen]
  norm_num

private lemma ratio_not_congruent : ¬ RatCongr 3 2
    (102790658465770739117540100122976721847176041588902154700374527298060572494857673559242663743632025784157718049052857 / 248060981949704625896344570711464099546609864372154310051109270678757921001761367078238673489100800000000000) 1 := by
  sorry

private lemma claim_instance (h : claim) : RatCongr 3 2
    ((3 : ℚ) ^ 28 * normalizedEven 7 45 / ((3 : ℚ) ^ 14 * normalizedEven 7 15))
    ((3 : ℚ) ^ 14 * normalizedEven 7 15 / ((3 : ℚ) ^ 14 * normalizedEven 7 15)) := by
  exact (h 3 (by decide) (by decide) 5 2 7
    (by decide) (by decide) (by decide) (by decide) (by decide)).1

/-- The registered odd-prime instance contradicts the even assertion. -/
theorem result : ¬ claim := by
  intro h
  have hc := claim_instance h
  rw [left_value, right_value] at hc
  exact ratio_not_congruent hc

end D5.S3.Arith.Congruence.KimotoWakayamaEvenCongruenceRefutation
