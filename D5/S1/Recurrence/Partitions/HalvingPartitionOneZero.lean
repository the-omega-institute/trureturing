/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionOneZero
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionOneZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive source-list lower bounds at binary inputs with one internal zero. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionProfile

/-! Alekseyev (2026), Corollary 15, supplies the antecedent exact one-zero
formula. Explicit distinct lists suffice for its fixed-digit lower bound.
No assertion of an exact global maximum is made. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- A scaled power word with one subtracted from precisely its first a entries.
Only the finite range l<=m is used. -/
def minusWord (b : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | 0, _, _ + 1 => []
  | m + 1, 0, l + 1 => b * 2 ^ m :: minusWord b m 0 l
  | m + 1, a + 1, l + 1 => (b * 2 ^ m - 1) :: minusWord b m a l

private theorem minusWord_length (b m a l : ℕ) (hl : l ≤ m) :
    (minusWord b m a l).length = l := by
  induction l generalizing m a with
  | zero => simp [minusWord]
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m => cases a <;> simp [minusWord, ih m _ (by omega)]

/-- The sum also recovers the subtracted-prefix parameter, hence injectivity. -/
private theorem minusWord_sum (b m a l : ℕ) (ha : a ≤ l) (hl : l ≤ m)
    (hb : 0 < b) :
    (minusWord b m a l).sum + a + b * 2 ^ (m - l) = b * 2 ^ m := by
  induction l generalizing m a with
  | zero =>
    have hz : a = 0 := by omega
    simp [minusWord, hz]
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hp : 0 < b * 2 ^ m := Nat.mul_pos hb (by positivity)
      cases a with
      | zero =>
        have h := ih m 0 (by omega) (by omega)
        simp only [minusWord, List.sum_cons, Nat.succ_sub_succ_eq_sub, pow_succ]
        nlinarith
      | succ a =>
        have h := ih m a (by omega) (by omega)
        simp only [minusWord, List.sum_cons, Nat.succ_sub_succ_eq_sub, pow_succ]
        nlinarith [Nat.sub_add_cancel (show 1 ≤ b * 2 ^ m by omega)]

private theorem minusWord_positive (b m a l : ℕ) (ha : a ≤ l) (hl : l ≤ m)
    (hb : 1 < b * 2 ^ (m - l)) : ∀ x ∈ minusWord b m a l, 0 < x := by
  induction l generalizing m a with
  | zero => simp [minusWord]
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hp : 1 ≤ (2 : ℕ) ^ l := Nat.one_le_pow l 2 (by decide)
      have hbase : 1 < b * 2 ^ m := by
        have hs : 2 ^ (m - l) ≤ (2 : ℕ) ^ m := pow_le_pow_right₀ (by decide) (by omega)
        have hb0 : 0 < b := by
          by_contra h
          have hz : b = 0 := by omega
          simp [hz] at hb
        simp only [Nat.succ_sub_succ_eq_sub] at hb
        nlinarith
      cases a with
      | zero =>
        simp only [minusWord, List.forall_mem_cons]
        exact ⟨by omega, ih m 0 (by omega) (by omega) (by simpa using hb)⟩
      | succ a =>
        simp only [minusWord, List.forall_mem_cons]
        exact ⟨by omega, ih m a (by omega) (by omega) (by simpa using hb)⟩

private theorem scaledWord_append (b m l : ℕ) (hl : l ≤ m) (q : List ℕ)
    (hq : Follows (b * 2 ^ (m - l)) q) :
    Follows (b * 2 ^ m) (minusWord b m 0 l ++ q) := by
  induction l generalizing m with
  | zero => simpa [minusWord] using hq
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [minusWord, List.cons_append, Follows]
      refine ⟨Or.inl ?_, ih m (by omega) (by simpa using hq)⟩
      rw [show b * 2 ^ (m + 1) = 2 * (b * 2 ^ m) by rw [pow_succ]; ring]
      omega

private theorem minusWord_append (b m a l : ℕ) (ha : a ≤ l) (hl : l ≤ m)
    (hb : 0 < b) (q : List ℕ)
    (hq : Follows (if a = l then b * 2 ^ (m - l) - 1 else b * 2 ^ (m - l)) q) :
    Follows (b * 2 ^ m - 1) (minusWord b m a l ++ q) := by
  induction l generalizing m a with
  | zero =>
    have hz : a = 0 := by omega
    simpa [minusWord, hz] using hq
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hp : 0 < b * 2 ^ m := Nat.mul_pos hb (by positivity)
      have hpow : b * 2 ^ (m + 1) = 2 * (b * 2 ^ m) := by rw [pow_succ]; ring
      cases a with
      | zero =>
        simp only [minusWord, List.cons_append, Follows]
        refine ⟨Or.inr (by omega), ?_⟩
        apply scaledWord_append b m l (by omega) q
        simpa using hq
      | succ a =>
        simp only [minusWord, List.cons_append, Follows]
        refine ⟨Or.inl (by omega), ?_⟩
        apply ih m a (by omega) (by omega)
        simpa only [Nat.succ_sub_succ_eq_sub, Nat.add_right_cancel_iff] using hq

private theorem follows_ones (n : ℕ) (hn : n = 1 ∨ n = 2) (l : ℕ) :
    Follows n (List.replicate l 1) := by
  induction l generalizing n with
  | zero => trivial
  | succ l ih =>
    simp only [List.replicate_succ, Follows]
    exact ⟨by rcases hn with rfl | rfl <;> norm_num [IsHalf], ih 1 (Or.inl rfl)⟩

/-- Two disjoint families of explicit paths. The second has no upper choice in
the low run, hence one fewer choice in the high run. -/
abbrev OneZeroCode (j k : ℕ) := (Fin j × Fin k) ⊕ Fin (k - 1)

def oneZeroList (j k : ℕ) : OneZeroCode j k → List ℕ
  | .inl ia =>
    minusWord (2 ^ k - 1) j ia.1.val j ++
      (minusWord 1 k ia.2.val (k - 1) ++ List.replicate (ia.1.val + ia.2.val) 1)
  | .inr a =>
    minusWord (2 ^ k - 1) j j j ++
      (2 ^ (k - 1) - 1) ::
        (minusWord 1 (k - 1) a.val (k - 2) ++ List.replicate (j + a.val + 1) 1)

private theorem oneZeroList_source (j k : ℕ) (hj : 1 ≤ j) (hk : 2 ≤ k)
    (c : OneZeroCode j k) :
    (∀ x ∈ oneZeroList j k c, 0 < x) ∧
      (oneZeroList j k c).sum = (2 ^ k - 1) * 2 ^ j - 1 ∧
      Follows ((2 ^ k - 1) * 2 ^ j - 1) (oneZeroList j k c) := by
  have hp : 4 ≤ (2 : ℕ) ^ k := by
    simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) hk)
  have hp1 : 2 ≤ (2 : ℕ) ^ (k - 1) := by
    simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) (show 1 ≤ k - 1 by omega))
  have he : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    ring
  have hb : 0 < 2 ^ k - 1 := by omega
  have hones (l : ℕ) : ∀ x ∈ List.replicate l 1, 0 < x := by simp
  rcases c with ia | a
  · have hi := ia.1.isLt
    have ha := ia.2.isLt
    have hs₀ := minusWord_sum (2 ^ k - 1) j ia.1.val j (by omega) le_rfl hb
    have hs₁ := minusWord_sum 1 k ia.2.val (k - 1) (by omega) (by omega) (by decide)
    have hpos₀ := minusWord_positive (2 ^ k - 1) j ia.1.val j (by omega) le_rfl
      (by simpa only [Nat.sub_self, pow_zero, mul_one] using (show 1 < 2 ^ k - 1 by omega))
    have hpos₁ := minusWord_positive 1 k ia.2.val (k - 1) (by omega) (by omega)
      (by rw [show k - (k - 1) = 1 by omega]; decide)
    constructor
    · simpa only [oneZeroList, List.forall_mem_append] using ⟨hpos₀, hpos₁, hones _⟩
    constructor
    · simp only [oneZeroList, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
      simp only [Nat.sub_self, pow_zero, mul_one, one_mul] at hs₀ hs₁
      rw [show k - (k - 1) = 1 by omega] at hs₁
      norm_num at hs₁
      omega
    · simp only [oneZeroList]
      apply minusWord_append _ _ _ _ (by omega) le_rfl hb
      simp only [show ia.1.val ≠ j by omega, ↓reduceIte, Nat.sub_self, pow_zero, mul_one]
      rw [← one_mul (2 ^ k)]
      apply minusWord_append 1 k ia.2.val (k - 1) (by omega) (by omega) (by decide)
      apply follows_ones
      · rw [show k - (k - 1) = 1 by omega]
        split_ifs <;> norm_num
  · have ha := a.isLt
    have hs₀ := minusWord_sum (2 ^ k - 1) j j j le_rfl le_rfl hb
    have hs₁ := minusWord_sum 1 (k - 1) a.val (k - 2) (by omega) (by omega) (by decide)
    have hpos₀ := minusWord_positive (2 ^ k - 1) j j j le_rfl le_rfl
      (by simpa only [Nat.sub_self, pow_zero, mul_one] using (show 1 < 2 ^ k - 1 by omega))
    have hpos₁ := minusWord_positive 1 (k - 1) a.val (k - 2) (by omega) (by omega)
      (by rw [show k - 1 - (k - 2) = 1 by omega]; decide)
    constructor
    · simp only [oneZeroList, List.forall_mem_append, List.forall_mem_cons]
      exact ⟨hpos₀, by omega, hpos₁, hones _⟩
    constructor
    · simp only [oneZeroList, List.sum_append, List.sum_cons, List.sum_replicate, smul_eq_mul, mul_one]
      simp only [Nat.sub_self, pow_zero, mul_one, one_mul] at hs₀ hs₁
      rw [show k - 1 - (k - 2) = 1 by omega] at hs₁
      norm_num at hs₁
      omega
    · simp only [oneZeroList]
      apply minusWord_append _ _ _ _ le_rfl le_rfl hb
      simp only [↓reduceIte, Nat.sub_self, pow_zero, mul_one, Follows]
      refine ⟨Or.inl ?_, ?_⟩
      · omega
      · rw [← one_mul (2 ^ (k - 1))]
        apply minusWord_append 1 (k - 1) a.val (k - 2) (by omega) (by omega) (by decide)
        apply follows_ones
        rw [show k - 1 - (k - 2) = 1 by omega]
        split_ifs <;> norm_num

private theorem oneZeroList_length (j k : ℕ) (hk : 2 ≤ k) (c : OneZeroCode j k) :
    (oneZeroList j k c).length =
      match c with
      | .inl ia => j + (k - 1) + ia.1.val + ia.2.val
      | .inr a => j + (k - 1) + j + a.val + 1 := by
  rcases c with ia | a
  · simp only [oneZeroList, List.length_append, List.length_replicate,
      minusWord_length _ j _ j le_rfl, minusWord_length 1 k _ (k - 1) (by omega)]
    omega
  · simp only [oneZeroList, List.length_append, List.length_cons, List.length_replicate,
      minusWord_length _ j _ j le_rfl,
      minusWord_length 1 (k - 1) _ (k - 2) (by omega)]
    omega

/-- The first-run prefix and total length recover both path parameters. -/
theorem oneZeroList_injective (j k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (oneZeroList j k) := by
  have hp : 0 < 2 ^ k - 1 := by
    have h : 4 ≤ (2 : ℕ) ^ k := by
      simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) hk)
    omega
  let first : OneZeroCode j k → ℕ := fun c => match c with | .inl ia => ia.1.val | .inr _ => j
  have htake (c : OneZeroCode j k) :
      ((oneZeroList j k c).take j).sum + first c + (2 ^ k - 1) =
        (2 ^ k - 1) * 2 ^ j := by
    have take_prefix (a : ℕ) (q : List ℕ) :
        (minusWord (2 ^ k - 1) j a j ++ q).take j = minusWord (2 ^ k - 1) j a j := by
      simpa only [minusWord_length _ j a j le_rfl] using
        (show (minusWord (2 ^ k - 1) j a j ++ q).take
          (minusWord (2 ^ k - 1) j a j).length = _ from List.take_left)
    rcases c with ia | a
    · simp only [oneZeroList, take_prefix, first]
      simpa only [Nat.sub_self, pow_zero, mul_one] using
        minusWord_sum (2 ^ k - 1) j ia.1.val j (by have := ia.1.isLt; omega) le_rfl hp
    · simp only [oneZeroList, take_prefix, first]
      simpa only [Nat.sub_self, pow_zero, mul_one] using
        minusWord_sum (2 ^ k - 1) j j j le_rfl le_rfl hp
  intro c d he
  have ht := congrArg (fun p : List ℕ => (p.take j).sum) he
  have hc := htake c
  have hd := htake d
  have hi : first c = first d := by omega
  have hl := congrArg List.length he
  rw [oneZeroList_length j k hk c, oneZeroList_length j k hk d] at hl
  rcases c with ⟨i, a⟩ | a <;> rcases d with ⟨i', a'⟩ | a' <;> dsimp only at hl
  · have hii : i = i' := Fin.ext hi
    have haa : a = a' := Fin.ext (by dsimp [first] at hi; omega)
    simp only [hii, haa]
  · have hh := i.isLt
    dsimp [first] at hi
    omega
  · have hh := i'.isLt
    dsimp [first] at hi
    omega
  · have haa : a = a' := Fin.ext (by omega)
    simp only [haa]

/-- At one-zero inputs, an explicit collection of actual lists gives the
quadratic lower bound used in the fixed-digit result. -/
theorem oneZero_count_lower (j k : ℕ) (hj : 1 ≤ j) (hk : 2 ≤ k) :
    j * k + (k - 1) ≤ count ((2 ^ k - 1) * 2 ^ j - 1) := by
  let f : OneZeroCode j k → SourceLists ((2 ^ k - 1) * 2 ^ j - 1) :=
    fun c => ⟨oneZeroList j k c, oneZeroList_source j k hj hk c⟩
  have hinj : Function.Injective f := by
    intro c d he
    exact oneZeroList_injective j k hk (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    count, Nat.card_eq_fintype_card] using hc

private theorem oneZero_digit_interval (j k : ℕ) (hj : 1 ≤ j) (hk : 2 ≤ k) :
    2 ^ (j + k - 1) ≤ (2 ^ k - 1) * 2 ^ j - 1 ∧
      (2 ^ k - 1) * 2 ^ j - 1 < 2 ^ (j + k) := by
  have ha : 2 ≤ (2 : ℕ) ^ j := by
    simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) hj)
  have hb : 2 ≤ (2 : ℕ) ^ (k - 1) := by
    simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide)
      (show 1 ≤ k - 1 by omega))
  have he : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
    ring
  have hfull : (2 : ℕ) ^ (j + k) = 2 ^ j * 2 ^ k := pow_add _ _ _
  have hhalf : (2 : ℕ) ^ (j + k - 1) = 2 ^ j * 2 ^ (k - 1) := by
    rw [show j + k - 1 = j + (k - 1) by omega, pow_add]
  have hc : 1 ≤ 2 ^ k - 1 := by omega
  have hprod : 1 ≤ (2 ^ k - 1) * 2 ^ j := by
    exact Nat.mul_pos (by omega) (by omega)
  have hs := Nat.sub_add_cancel (show 1 ≤ 2 ^ k by omega)
  have ht := Nat.sub_add_cancel hprod
  constructor <;> nlinarith

/-- Every binary digit length H>=3 contains an input whose actual list count
is at least floor((H+1)^2/4)-1. This is a lower bound, not an exact maximum. -/
theorem fixed_digit_count_lower (H : ℕ) (hH : 3 ≤ H) :
    ∃ n : ℕ, 2 ^ (H - 1) ≤ n ∧ n < 2 ^ H ∧
      (H + 1) ^ 2 / 4 - 1 ≤ count n := by
  let j := H / 2
  let k := H - j
  have hrem : H % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdiv := Nat.mod_add_div H 2
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hk : 2 ≤ k := by dsimp [k, j]; omega
  have hsum : j + k = H := by dsimp [k, j]; omega
  have hbound : (H + 1) ^ 2 / 4 - 1 = j * k + (k - 1) := by
    by_cases hp : H % 2 = 0
    · have hHj : H = 2 * j := by dsimp [j]; omega
      have hkj : k = j := by omega
      have he : (H + 1) ^ 2 = 4 * (j * k + k) + 1 := by rw [hHj, hkj]; ring
      omega
    · have hHj : H = 2 * j + 1 := by dsimp [j]; omega
      have hkj : k = j + 1 := by omega
      have he : (H + 1) ^ 2 = 4 * (j * k + k) := by rw [hHj, hkj]; ring
      omega
  refine ⟨(2 ^ k - 1) * 2 ^ j - 1, ?_, ?_, ?_⟩
  · simpa only [hsum] using (oneZero_digit_interval j k hj hk).1
  · simpa only [hsum] using (oneZero_digit_interval j k hj hk).2
  · rw [hbound]
    exact oneZero_count_lower j k hj hk

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
