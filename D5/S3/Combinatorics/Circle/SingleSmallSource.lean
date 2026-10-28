/- GID: D5/S3/Combinatorics/Circle/SingleSmallSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SingleSmallSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: A unique physical SMALL forces odd period, exact amplitude, and forward half-width completion. -/
module
public import D5.S3.Combinatorics.Circle.MixedSuffixEnergy

/-! A single physical SMALL defect. Numerical ties and proper periods are not
excluded by hypotheses. This restricted completion does not settle Circle C3.1. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.SingleSmallSource
open SourceWidth ExpandingSourcePath MixedSuffixEnergy

private theorem phase_inj {k : ℕ} (hk : 0 < k) (a : Fin k)
    {i j : ℕ} (hi : i < k) (hj : j < k)
    (he : phase hk a i = phase hk a j) : i = j := by
  have hm : Nat.ModEq k (a.val + i) (a.val + j) := congrArg Fin.val he
  have hc := Nat.ModEq.add_left_cancel' a.val hm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hc

private theorem phase_period {k : ℕ} (hk : 0 < k) (a : Fin k) (j : ℕ) :
    phase hk a (j + k) = phase hk a j := by
  apply Fin.ext
  simp [phase, Nat.add_mod]

/-- The period-closing inference, with the sign and affine profile proved jointly. -/
private theorem closing_profile (k : ℕ) (hk : 3 ≤ k) (Q N C : ℤ)
    (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = 2 * Q - 1)
    (hpow : N = (2 : ℤ) ^ k - 1)
    (w : ℕ → ℤ) (hb : ∀ j, -C ≤ w j ∧ w j ≤ C)
    (hs : ∀ j < k, w (j + 1) = doubleStep N (w j))
    (hsmall : |w 0| < Q) (hlarge : ∀ j, 1 ≤ j → j < k → Q ≤ |w j|)
    (hpos : 0 < w 0) (hclose : w k = w 0) :
    k % 2 = 1 ∧ 3 * w 0 = C ∧
      ∀ j, 1 ≤ j → j ≤ k →
        (if j % 2 = 1 then 0 < w j else w j < 0) ∧
        3 * w j = (if j % 2 = 1 then N else -N) - (2 : ℤ) ^ (j - 1) := by
  have hfirst : w 1 = 2 * w 0 := by
    have ht := hs 0 (by omega)
    have ha' : w 0 < Q := by simpa [abs_of_pos hpos] using hsmall
    simpa only [zero_add, doubleStep, if_neg (show ¬ N < 4 * w 0 by omega),
      if_neg (show ¬ 4 * w 0 < -N by omega)] using ht
  let d := 6 * w 0 - N
  have hform : ∀ j, 1 ≤ j → j ≤ k →
      (if j % 2 = 1 then 0 < w j else w j < 0) ∧
      3 * w j = (if j % 2 = 1 then N else -N) + (2 : ℤ) ^ (j - 1) * d := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj hjk
      by_cases hj0 : j = 0
      · subst j
        norm_num only [Nat.zero_add, Nat.reduceMod, Nat.sub_self, pow_zero, one_mul]
        dsimp [d]
        constructor <;> omega
      · obtain ⟨hsgn, heq⟩ := ih (by omega) (by omega)
        have hl := hlarge j (by omega) (by omega)
        have hb' := hb j
        have ht := hs j (by omega)
        have hp : (2 : ℤ) ^ (j + 1 - 1) = 2 * (2 : ℤ) ^ (j - 1) := by
          rw [show j + 1 - 1 = (j - 1) + 1 by omega, pow_succ]
          ring
        by_cases he : j % 2 = 1
        · have he' : (j + 1) % 2 ≠ 1 := by omega
          simp only [he, ite_true] at hsgn heq
          rw [abs_of_pos hsgn] at hl
          rw [doubleStep, if_pos (show N < 4 * w j by omega)] at ht
          simp only [Nat.succ_eq_add_one, he', ite_false, hp]
          constructor <;> nlinarith
        · have he' : (j + 1) % 2 = 1 := by omega
          simp only [he, ite_false] at hsgn heq
          rw [abs_of_neg hsgn] at hl
          rw [doubleStep, if_neg (show ¬ N < 4 * w j by omega),
            if_pos (show 4 * w j < -N by omega)] at ht
          simp only [Nat.succ_eq_add_one, he', ite_true, hp]
          constructor <;> nlinarith
  have hkodd : k % 2 = 1 := by
    have ht := (hform k (by omega) (by omega)).1
    rw [hclose] at ht
    split_ifs at ht <;> omega
  have hlast := (hform k (by omega) (by omega)).2
  simp only [hkodd, ite_true, hclose] at hlast
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hNpos : 0 < N := by omega
  have hcancel : N * (3 * w 0 - C) = 0 := by dsimp [d] at hlast; nlinarith
  have hamp : 3 * w 0 = C := by
    have := (mul_eq_zero.mp hcancel).resolve_left (ne_of_gt hNpos)
    omega
  have hd : d = -1 := by dsimp [d]; omega
  refine ⟨hkodd, hamp, ?_⟩
  intro j hj hjk
  obtain ⟨hsgn, heq⟩ := hform j hj hjk
  refine ⟨hsgn, ?_⟩
  rw [hd] at heq
  omega

/-- Unique physical SMALL rigidity and the complete sign-oriented native profile. -/
theorem single_small_rigidity {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (a : Fin k)
    (ha : |actualSource k t a| < quarter k)
    (hL : ∀ i : Fin k, i ≠ a → Large k t i) :
    k % 2 = 1 ∧ 3 * |actualSource k t a| = half k ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k →
        let w := orient (decide (actualSource k t a < 0))
          (actualSource k t (phase (by omega) a j))
        (if j % 2 = 1 then 0 < w else w < 0) ∧
        3 * w = (if j % 2 = 1 then modulus k else -modulus k) -
          (2 : ℤ) ^ (j - 1) := by
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  let neg := decide (actualSource k t a < 0)
  let w := fun j => orient neg (actualSource k t (phase (by omega) a j))
  have hw0 : w 0 = |actualSource k t a| := by simp [w, neg, orient_choose]
  have hb : ∀ j, -half k ≤ w j ∧ w j ≤ half k := by
    intro j
    have ht := centered_bounds hNpos hodd ((2 : ℤ) ^ (phase (by omega) a j).val * t)
    change -half k ≤ actualSource k t (phase (by omega) a j) ∧
      actualSource k t (phase (by omega) a j) ≤ half k at ht
    dsimp [w]
    cases neg <;> simp only [orient, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hs : ∀ j < k, w (j + 1) = doubleStep (modulus k) (w j) := by
    intro j _
    have ht := phase_step hk t a j
    cases hn : neg
    · simpa [w, hn, orient] using ht
    · simpa [w, hn, orient, doubleStep_neg hNpos.le] using congrArg Neg.neg ht
  have hl : ∀ j, 1 ≤ j → j < k → quarter k ≤ |w j| := by
    intro j hj hjk
    have he : phase (by omega) a j ≠ a := by
      intro he
      have he' : phase (by omega) a j = phase (by omega) a 0 := by simpa using he
      have := phase_inj (by omega) a hjk (by omega) he'
      omega
    simpa [w, Large] using hL _ he
  have hpos : 0 < w 0 := by
    have hn := abs_nonneg (actualSource k t a)
    have ht := hs 0 (by omega)
    have hlarge := hl 1 (by omega) (by omega)
    have hsmall : w 0 < quarter k := by simpa [hw0] using ha
    by_contra h
    have hz : w 0 = 0 := by omega
    rw [hz] at ht
    simp [doubleStep, hNpos.not_gt, show ¬ (0 : ℤ) < -modulus k by omega] at ht
    rw [show 0 + 1 = 1 by omega, ht, abs_zero] at hlarge
    omega
  have hc : w k = w 0 := by
    dsimp [w]
    rw [show k = 0 + k by omega, phase_period]
  have ht := closing_profile k hk (quarter k) (modulus k) (half k)
    hQ hN hC rfl w hb hs (by simpa [hw0, abs_abs] using ha) hl hpos hc
  simpa only [w, neg, hw0] using ht

end D5.S3.Combinatorics.Circle.SingleSmallSource
