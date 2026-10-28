/- GID: D5/S3/Combinatorics/Circle/SingleSmallSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/SingleSmallSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: A unique physical SMALL forces odd period, exact amplitude, and forward completion. -/
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
    simpa only [zero_add, doubleStep, ite_eq_right (show ¬ N < 4 * w 0 by omega),
      ite_eq_right (show ¬ 4 * w 0 < -N by omega)] using ht
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
          rw [doubleStep, ite_eq_left (show N < 4 * w j by omega)] at ht
          simp only [he', ite_false, hp]
          constructor <;> nlinarith
        · have he' : (j + 1) % 2 = 1 := by omega
          simp only [he, ite_false] at hsgn heq
          rw [abs_of_neg hsgn] at hl
          rw [doubleStep, ite_eq_right (show ¬ N < 4 * w j by omega),
            ite_eq_left (show 4 * w j < -N by omega)] at ht
          simp only [he', ite_true, hp]
          constructor <;> nlinarith
  have hkodd : k % 2 = 1 := by
    have ht := (hform k (by omega) (by omega)).1
    rw [hclose] at ht
    split_ifs at ht <;> omega
  have hlast := (hform k (by omega) (by omega)).2
  simp only [hkodd, ite_true, hclose] at hlast
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
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
    simp [doubleStep, hNpos.not_gt] at ht
    rw [ht, abs_zero] at hlarge
    omega
  have hc : w k = w 0 := by
    dsimp [w]
    have he : phase (by omega) a k = phase (by omega) a 0 := by
      simpa only [zero_add] using phase_period (by omega) a 0
    rw [he]
  have ht := closing_profile k hk (quarter k) (modulus k) (half k)
    hQ hN hC rfl w hb hs (by simpa [hw0, abs_abs] using ha) hl hpos hc
  simpa only [w, neg, hw0] using ht


private theorem phase_surj {k : ℕ} (hk : 0 < k) (a x : Fin k) :
    ∃ j < k, phase hk a j = x := by
  obtain ⟨i, hi⟩ := (finCycle a).surjective x
  refine ⟨i.val, i.isLt, ?_⟩
  have he : phase hk a i.val = finCycle a i := by
    apply Fin.ext
    simp [phase, finCycle_apply, Fin.val_add, Nat.add_comm]
  exact he.trans hi

/-- The full forward physical cycle, with its start forced by the sign of the
unique SMALL. In particular no reversal or permutation of the LARGE cycle occurs. -/
theorem single_small_forward_completion {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (a : Fin k)
    (ha : |actualSource k t a| < quarter k)
    (hL : ∀ i : Fin k, i ≠ a → Large k t i) :
    let start := if 0 < actualSource k t a then a else phase (by omega) a 2
    let word := path (by omega) start k
    word.Perm (List.finRange k) ∧ word.Nodup ∧ word.toFinset = Finset.univ ∧
      InStrip (actualSource k t) (half k) 0 word ∧
      (∀ n : ℕ, 0 ≤ ((word.take n).map (actualSource k t)).sum ∧
        ((word.take n).map (actualSource k t)).sum ≤ half k) ∧
      (word.map (actualSource k t)).sum = 0 := by
  classical
  obtain ⟨hQ, hN, hC, hNpos, hodd⟩ := source_geometry hk
  obtain ⟨_, hamp, hprofile⟩ := single_small_rigidity hk t a ha hL
  let s := |actualSource k t a|
  let neg := decide (actualSource k t a < 0)
  let g := fun i : Fin k => orient neg (actualSource k t i)
  let v := fun i : Fin k => g i + if g i < 0 then modulus k else 0
  have hs : 3 * s = half k := hamp
  have hspos : 0 < s := by omega
  have hNs : modulus k = 6 * s + 1 := by omega
  have hpower : (2 : ℤ) ^ (k - 1) = half k + 1 := by
    have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
      ring
    have hn : modulus k = (2 : ℤ) ^ k - 1 := rfl
    omega
  have hga : g a = s := orient_choose _
  have hva : v a = s := by simp [v, hga, hspos.not_gt]
  have hvphase : ∀ j < k,
      s ≤ v (phase (by omega) a j) ∧ v (phase (by omega) a j) ≤ 4 * s := by
    intro j hj
    by_cases hz : j = 0
    · subst j
      simp only [phase_zero, hva]
      constructor <;> omega
    · have ht := hprofile j (by omega) (by omega)
      change (if j % 2 = 1 then 0 < g (phase (by omega) a j)
        else g (phase (by omega) a j) < 0) ∧
        3 * g (phase (by omega) a j) =
          (if j % 2 = 1 then modulus k else -modulus k) - (2 : ℤ) ^ (j - 1) at ht
      have hpmax := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show j - 1 ≤ k - 1 by omega)
      rw [hpower] at hpmax
      have hpmin : 1 ≤ (2 : ℤ) ^ (j - 1) := one_le_pow₀ (by norm_num)
      dsimp only [v]
      by_cases he : j % 2 = 1
      · simp only [he, ite_true] at ht
        rw [ite_eq_right ht.1.not_gt]
        constructor <;> nlinarith [ht.2]
      · simp only [he, ite_false] at ht
        rw [ite_eq_left ht.1]
        have hptwo : (2 : ℤ) ≤ (2 : ℤ) ^ (j - 1) := by
          simpa only [pow_one] using pow_le_pow_right₀
            (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ j - 1 by omega)
        constructor <;> nlinarith [ht.2]
  have hv : ∀ i, s ≤ v i ∧ v i ≤ 4 * s := by
    intro i
    obtain ⟨j, hj, rfl⟩ := phase_surj (by omega) a i
    exact hvphase j hj
  have hv2 : v (phase (by omega) a 2) = 4 * s := by
    have ht := hprofile 2 (by omega) (by omega)
    change (if 2 % 2 = 1 then 0 < g (phase (by omega) a 2)
      else g (phase (by omega) a 2) < 0) ∧
      3 * g (phase (by omega) a 2) =
        (if 2 % 2 = 1 then modulus k else -modulus k) - (2 : ℤ) ^ (2 - 1) at ht
    norm_num only [Nat.reduceMod, Nat.reduceSub, pow_one, ite_false] at ht
    dsimp only [v]
    rw [ite_eq_left ht.1]
    nlinarith [ht.2]
  have hgnz : ∀ i, g i ≠ 0 := by
    intro i
    obtain ⟨j, hj, rfl⟩ := phase_surj (by omega) a i
    by_cases hz : j = 0
    · subst j
      simpa only [phase_zero, hga] using ne_of_gt hspos
    · have ht := (hprofile j (by omega) (by omega)).1
      change (if j % 2 = 1 then 0 < g (phase (by omega) a j)
        else g (phase (by omega) a j) < 0) at ht
      split_ifs at ht
      · exact ne_of_gt ht
      · exact ne_of_lt ht
  let u := fun i : Fin k => actualSource k t i +
    if actualSource k t i < 0 then modulus k else 0
  have huv (i : Fin k) : u i = if neg then modulus k - v i else v i := by
    have hz := hgnz i
    cases hn : neg
    · simp [u, v, g, hn, orient]
    · dsimp only [u, v, g] at *
      simp only [hn, orient, ite_true] at *
      split_ifs <;> omega
  let start := if 0 < actualSource k t a then a else phase (by omega) a 2
  let word := path (by omega) start k
  have hheight : ∀ i, 0 ≤ u i - u start ∧ u i - u start ≤ half k := by
    intro i
    have ht := hv i
    by_cases hn : actualSource k t a < 0
    · have hn' : neg = true := by simp [neg, hn]
      have hstart : start = phase (by omega) a 2 := by simp [start, hn.not_gt]
      rw [hstart, huv, huv, hn', ite_true, ite_true, hv2]
      constructor <;> omega
    · have hpos : 0 < actualSource k t a := by
        have he : s = actualSource k t a := abs_of_nonneg (by omega)
        omega
      have hn' : neg = false := by simp [neg, hn]
      have hstart : start = a := by simp [start, hpos]
      rw [hstart, huv, huv, hn', ite_false, ite_false, hva]
      constructor <;> omega
  have hstep (j : ℕ) :
      actualSource k t (phase (by omega) start (j + 1)) =
        doubleStep (modulus k) (actualSource k t (phase (by omega) start j)) :=
    phase_step hk t start j
  have hpot (j : ℕ) :
      u (phase (by omega) start (j + 1)) - u (phase (by omega) start j) =
        actualSource k t (phase (by omega) start j) := by
    dsimp only [u]
    rw [hstep]
    exact unsigned_step hNpos hodd (centered_bounds hNpos hodd _)
  have hsum (m : ℕ) :
      ((path (by omega) start m).map (actualSource k t)).sum =
        u (phase (by omega) start m) - u start := by
    have hp := path_range (phase (by omega) start) m
      (fun j _ => hpot j) (fun j _ => hstep j)
    simpa only [path, phase_zero] using path_sum hp
  have hpre : ∀ n : ℕ, 0 ≤ ((word.take n).map (actualSource k t)).sum ∧
      ((word.take n).map (actualSource k t)).sum ≤ half k := by
    intro n
    have ht : word.take n = path (by omega) start (min n k) := by
      dsimp only [word, path]
      rw [← List.map_take, List.take_range]
    rw [ht, hsum]
    exact hheight _
  have hword : word = (List.finRange k).map (finCycle start) := by
    apply List.ext_getElem
    · simp [word]
    · intro i hi hi'
      simp only [word, path, List.getElem_map, List.getElem_range, List.getElem_finRange]
      apply Fin.ext
      simp [phase, finCycle_apply, Fin.val_add, Nat.add_comm]
  have hperm : word.Perm (List.finRange k) := by
    rw [hword]
    exact (finCycle start).map_finRange_perm
  have hnod : word.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange k)
  have hfull : word.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    exact List.mem_toFinset.mpr (hperm.mem_iff.mpr (List.mem_finRange i))
  refine ⟨hperm, hnod, hfull, ?_, hpre, ?_⟩
  · apply strip_of_all_prefixes word
    simpa only [zero_add, mass] using hpre
  · dsimp only [word]
    rw [hsum]
    have he : phase (by omega) start k = start := by
      simpa only [zero_add, phase_zero] using phase_period (by omega) start 0
    rw [he, sub_self]

#print axioms single_small_rigidity
#print axioms single_small_forward_completion

end D5.S3.Combinatorics.Circle.SingleSmallSource
