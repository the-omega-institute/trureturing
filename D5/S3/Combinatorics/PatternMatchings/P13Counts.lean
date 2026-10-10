/- GID: D5/S3/Combinatorics/PatternMatchings/P13Counts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Counts
   mirror-E: none(waiver:concrete-first-closure-counts)
   anchors: []
   utility: none
   digest: First closures partition literal single-block completions by actual surviving blocks. -/

import D5.S3.Combinatorics.PatternMatchings.P13Completions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.P13

private theorem blocks_right (a : ℕ) : blocks a 0 = .S a := by
  by_cases ha : a = 0 <;> simp [blocks, ha]

/-- Bounded surviving block sizes at the first closure. -/
def FirstClosureData (m d : ℕ) :=
  Σ a : Fin d, Σ b : Fin d, {_v : Completion (blocks a.val b.val) (d - 1) // m ≤ a.val + 1}

private theorem first_transition (m a b : ℕ) (_hm : 0 < m) (ha : m ≤ a + 1) :
    Permitted (.S m) (a + b + 1 - m) a ∧
    afterClose (.S m) (a + b + 1 - m) a = blocks a b := by
  have hmk : m + (a + b + 1 - m) = a + b + 1 := by omega
  constructor
  · simp only [Permitted, Base.size, hmk]; omega
  · simp only [afterClose, Base.size, hmk]
    congr 1
    omega

private def firstCompletion (m d : ℕ) (hm : 0 < m) (x : FirstClosureData m d) :
    Completion (.S m) d := by
  let a := x.1.val
  let b := x.2.1.val
  let k := a + b + 1 - m
  have ht := first_transition m a b hm x.2.2.2
  refine ⟨openingRun k ++ .closing a :: x.2.2.1.1, ?_, ?_⟩
  · apply (accept_openingRun (.S m) 0 k _).mpr
    simp only [Nat.zero_add, AcceptFrom]
    exact ⟨ht.1, by rw [ht.2]; exact x.2.2.1.2.1⟩
  · rw [closingCount_append, openingRun_closingCount, closingCount, x.2.2.1.2.2]
    have hd := x.1.isLt
    omega

private theorem firstCompletion_injective (m d : ℕ) (hm : 0 < m) :
    Function.Injective (firstCompletion m d hm) := by
  rintro ⟨a, b, v⟩ ⟨a', b', v'⟩ h
  have hh := congrArg Subtype.val h
  change openingRun (a.val + b.val + 1 - m) ++ .closing a.val :: v.1.1 =
    openingRun (a'.val + b'.val + 1 - m) ++ .closing a'.val :: v'.1.1 at hh
  obtain ⟨hk, ha, hv⟩ := first_closure_unique _ _ _ _ _ _ hh
  have haa : a = a' := Fin.ext ha
  subst a'
  have hb : b = b' := Fin.ext (by have := v.2; have := v'.2; omega)
  subst b'
  have hvv : v = v' := Subtype.ext (Subtype.ext hv)
  subst v'
  rfl

private theorem firstCompletion_surjective (m d : ℕ) (hm : 0 < m) :
    Function.Surjective (firstCompletion m d hm) := by
  intro w
  have hpos : 0 < closingCount w.1 := by
    have hh := continuation_balance w.2.1
    change m + 0 + openingCount w.1 = closingCount w.1 at hh
    omega
  obtain ⟨k, r, v, hw⟩ := first_closure_exists hpos
  have hh := w.2.1
  rw [hw] at hh
  have hh := (accept_openingRun (.S m) 0 k _).mp hh
  simp only [Nat.zero_add, AcceptFrom] at hh
  let b := m + k - r - 1
  have hr : r < m + k ∧ m ≤ r + 1 := hh.1
  have he : afterClose (.S m) k r = blocks r b := rfl
  have hc : closingCount v = d - 1 := by
    have hc := w.2.2
    rw [hw, closingCount_append, openingRun_closingCount, closingCount] at hc
    omega
  have hv : AcceptFrom (blocks r b) 0 v := by simpa only [he] using hh.2
  have hs := continuation_balance hv
  have hs' := (blocks_spec r b).1
  have hb : r + b ≤ d - 1 := by omega
  have hd : 0 < d := by have := w.2.2; omega
  have hk : r + b + 1 - m = k := by dsimp [b]; omega
  refine ⟨⟨⟨r, by omega⟩, ⟨b, by omega⟩, ⟨⟨v, hv, hc⟩, hr.2⟩⟩, ?_⟩
  apply Subtype.ext
  change openingRun (r + b + 1 - m) ++ .closing r :: v = w.1
  rw [hk, ← hw]

/-- The first closure gives a unique legal rank and the two actual survivor blocks. -/
noncomputable def firstClosureEquiv (m d : ℕ) (hm : 0 < m) :
    FirstClosureData m d ≃ Completion (.S m) d :=
  Equiv.ofBijective (firstCompletion m d hm)
    ⟨firstCompletion_injective m d hm, firstCompletion_surjective m d hm⟩

/-- Finite first-closure count; impossible surviving blocks contribute zero. -/
theorem c_first_sum (m d : ℕ) (hm : 0 < m) :
    c m d = ∑ a ∈ Finset.range d, ∑ b ∈ Finset.range d,
      if m ≤ a + 1 then g a b (d - 1) else 0 := by
  unfold c
  rw [← Nat.card_congr (firstClosureEquiv m d hm)]
  unfold FirstClosureData
  rw [Nat.card_sigma]
  simp only [Nat.card_sigma]
  have hf (a b : Fin d) :
      Nat.card {_v : Completion (blocks a.val b.val) (d - 1) // m ≤ a.val + 1} =
      if m ≤ a.val + 1 then g a.val b.val (d - 1) else 0 := by
    by_cases ha : m ≤ a.val + 1
    · rw [if_pos ha]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => ha))
    · have : IsEmpty {_v : Completion (blocks a.val b.val) (d - 1) // m ≤ a.val + 1} :=
        ⟨fun v => ha v.2⟩
      simp [ha]
  simp_rw [hf]
  have hi (a : Fin d) :
      (∑ b : Fin d, if m ≤ a.val + 1 then g a.val b.val (d - 1) else 0) =
      ∑ b ∈ Finset.range d, if m ≤ a.val + 1 then g a.val b (d - 1) else 0 :=
    Fin.sum_univ_eq_sum_range (fun b => if m ≤ a.val + 1 then g a.val b (d - 1) else 0) d
  simp_rw [hi]
  exact Fin.sum_univ_eq_sum_range
    (fun a => ∑ b ∈ Finset.range d, if m ≤ a + 1 then g a b (d - 1) else 0) d

private theorem accept_zero_one (k : ℕ) (w : List Step) :
    AcceptFrom (.S 0) (k + 1) w ↔ AcceptFrom (.S 1) k w := by
  induction w generalizing k with
  | nil => simp [AcceptFrom, Base.size]
  | cons x w ih =>
    cases x with
    | opening => simpa only [AcceptFrom, Nat.add_assoc] using ih (k + 1)
    | closing r =>
      simp only [AcceptFrom, Permitted, Base.size, afterClose]
      have he : 0 + (k + 1) = 1 + k := by omega
      rw [he]
      simp

private def prependOpening (d : ℕ) (w : Completion (.S 1) d) : Completion (.S 0) d :=
  ⟨.opening :: w.1, (accept_zero_one 0 w.1).mpr w.2.1, w.2.2⟩

/-- For a positive closing count, the first opening identifies empty-base and one-block scans. -/
noncomputable def emptySingleEquiv (d : ℕ) (hd : 0 < d) :
    Completion (.S 1) d ≃ Completion (.S 0) d := by
  apply Equiv.ofBijective (prependOpening d)
  constructor
  · intro v w h
    exact Subtype.ext (List.cons.inj (congrArg Subtype.val h)).2
  · rintro ⟨w, hw, hc⟩
    cases w with
    | nil => simp [closingCount] at hc; omega
    | cons x w =>
      cases x with
      | opening =>
        refine ⟨⟨w, (accept_zero_one 0 w).mp hw, hc⟩, rfl⟩
      | closing r =>
        have hh := hw.1.1
        simp [Base.size] at hh

/-- Positive-degree empty-base counts equal one-block counts. -/
theorem c_empty_single (d : ℕ) (hd : 0 < d) : c 0 d = c 1 d :=
  (Nat.card_congr (emptySingleEquiv d hd)).symm

/-- The empty word is the sole zero-degree empty-base completion. -/
theorem c_zero_zero : c 0 0 = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨[], by simp [AcceptFrom, Base.size, closingCount]⟩, ?_⟩
  intro w
  apply Subtype.ext
  apply List.length_eq_zero_iff.mp
  have hh := (completion_bounds w).2.2.1
  simpa only [Base.size] using hh

/-- Single-block counts differ by the completions whose first rank is m-1. -/
theorem c_first_difference (m d : ℕ) (hm : 0 < m) (hmd : m ≤ d) :
    c m d = c (m + 1) d + ∑ b ∈ Finset.range d, g (m - 1) b (d - 1) := by
  rw [c_first_sum m d hm, c_first_sum (m + 1) d (by omega)]
  have ht (a b : ℕ) :
      (if m ≤ a + 1 then g a b (d - 1) else 0) =
      (if m + 1 ≤ a + 1 then g a b (d - 1) else 0) +
      (if a = m - 1 then g a b (d - 1) else 0) := by
    by_cases he : a = m - 1
    · subst a
      have h1 : m ≤ m - 1 + 1 := by omega
      have h2 : ¬m + 1 ≤ m - 1 + 1 := by omega
      simp [h1, h2]
    · have hiff : m ≤ a + 1 ↔ m + 1 ≤ a + 1 := by omega
      simp [he, hiff]
  simp_rw [ht, Finset.sum_add_distrib]
  congr 1
  have hi : m - 1 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single (m - 1)]
  · simp
  · intro a ha he
    simp [he]
  · exact fun h => (h hi).elim

private def descendingClosures : ℕ → List Step
  | 0 => []
  | m + 1 => .closing m :: descendingClosures m

private theorem diagonal_word (m : ℕ) :
    AcceptFrom (.S m) 0 (descendingClosures m) ∧ closingCount (descendingClosures m) = m := by
  induction m with
  | zero => simp [descendingClosures, AcceptFrom, Base.size, closingCount]
  | succ m ih =>
    have ht := first_transition (m + 1) m 0 (by omega) (by omega)
    have he : m + 0 + 1 - (m + 1) = 0 := by omega
    rw [he] at ht
    simp only [descendingClosures, AcceptFrom, closingCount]
    refine ⟨⟨ht.1, ?_⟩, by omega⟩
    rw [ht.2]
    simpa only [blocks_right] using ih.1

private theorem diagonal_unique (m : ℕ) (w : Completion (.S m) m) :
    w.1 = descendingClosures m := by
  induction m with
  | zero =>
    have hh := (completion_bounds w).2.2.1
    have he : w.1 = [] := List.length_eq_zero_iff.mp (by simpa [Base.size] using hh)
    exact he
  | succ m ih =>
    obtain ⟨w, hw, hc⟩ := w
    have ho : openingCount w = 0 := by
      have hh := continuation_balance hw
      change m + 1 + 0 + openingCount w = closingCount w at hh
      omega
    cases w with
    | nil => simp [closingCount] at hc
    | cons x w =>
      cases x with
      | opening => simp [openingCount] at ho
      | closing r =>
        have hr : r = m := by
          have hh := hw.1
          simp only [Permitted, Base.size] at hh
          omega
        subst r
        have ht := first_transition (m + 1) m 0 (by omega) (by omega)
        have he : m + 0 + 1 - (m + 1) = 0 := by omega
        rw [he] at ht
        have ha : AcceptFrom (.S m) 0 w := by
          have hh := hw.2
          rw [ht.2] at hh
          simpa only [blocks_right] using hh
        have hd : closingCount w = m := by simp only [closingCount] at hc; omega
        exact congrArg (Step.closing m :: ·) (ih ⟨w, ha, hd⟩)

/-- Closing all old survivors without new openings gives exactly one completion. -/
theorem c_diagonal (m : ℕ) : c m m = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨descendingClosures m, diagonal_word m⟩, ?_⟩
  intro w
  exact Subtype.ext (diagonal_unique m w)

private noncomputable def matchingCompletionEquiv (n : ℕ) :
    {m : TripleAvoidingMatchingsDefs.Matching n // Avoids m} ≃ Completion (.S 0) n :=
  (matchingEquiv n).trans {
    toFun := fun w => ⟨w.1, w.2.2, by
      have hb := continuation_balance w.2.2
      have hv := vertex_count w.1
      have hl := w.2.1
      simp only [Base.size] at hb
      omega⟩
    invFun := fun w => ⟨w.1, by
      have hh := (completion_bounds w).2.2.1
      simpa only [Base.size, Nat.sub_zero] using hh, w.2.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- The actual P13 perfect-matching count. -/
noncomputable def actualCount (n : ℕ) : ℕ :=
  Nat.card {m : TripleAvoidingMatchingsDefs.Matching n // Avoids m}

private theorem actualCount_eq_c (n : ℕ) : actualCount n = c 0 n :=
  Nat.card_congr (matchingCompletionEquiv n)

private theorem forced_double_sum (a K N : ℕ) (hKN : K ≤ N) :
    (∑ k ∈ Finset.range N, ∑ t ∈ Finset.range (N + 1),
      a.multichoose t * c (k + t + 1) K) =
    ∑ j ∈ Finset.range K, (a + j).choose a * c (j + 1) K := by
  classical
  rw [← Finset.sum_product (Finset.range N) (Finset.range (N + 1))
    (fun p : ℕ × ℕ => a.multichoose p.2 * c (p.1 + p.2 + 1) K)]
  have he :
      (∑ p ∈ (Finset.range N) ×ˢ (Finset.range (N + 1)),
        a.multichoose p.2 * c (p.1 + p.2 + 1) K) =
      ∑ p ∈ (Finset.range K).sigma (fun j => Finset.range (j + 1)),
        a.multichoose p.2 * c (p.1 + 1) K := by
    apply Finset.sum_bij_ne_zero (fun p _ _ => ⟨p.1 + p.2, p.2⟩)
    · intro p hp hn
      have hs : p.1 + p.2 + 1 ≤ K := by
        by_contra hh
        have hc := c_support (m := p.1 + p.2 + 1) (d := K) (by omega)
        simp only [hc, Nat.mul_zero, ne_eq, not_true_eq_false] at hn
      simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · intro p hp hn q hq hqn he
      have h1 : p.1 + p.2 = q.1 + q.2 := congrArg Sigma.fst he
      have h2 : p.2 = q.2 := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) he
      exact Prod.ext (by omega) h2
    · intro p hp hn
      obtain ⟨hj, ht⟩ := Finset.mem_sigma.mp hp
      have hj' := Finset.mem_range.mp hj
      have ht' := Finset.mem_range.mp ht
      refine ⟨(p.1 - p.2, p.2), ?_, ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]; omega
      · have hs : p.1 - p.2 + p.2 = p.1 := by omega
        simpa only [Prod.fst, Prod.snd, hs] using hn
      · apply Sigma.ext
        · change p.1 - p.2 + p.2 = p.1
          omega
        · rfl
    · intro p hp hn
      rfl
  refine he.trans ?_
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ t ∈ Finset.range (j + 1), a.multichoose t * c (j + 1) K) = _
  rw [← Finset.sum_mul, Nat.sum_range_multichoose]
  rw [Nat.add_comm j a]

/-- The exact finite triangular recurrence on concrete accepted continuations. -/
theorem c_triangular (m d : ℕ) (hm : 0 < m) (hmd : m ≤ d) :
    c m d = c (m + 1) d + c (m - 1) (d - 1) +
      ∑ j ∈ Finset.Icc 1 (d - m), (m + j - 2).choose (m - 1) * c j (d - m) := by
  by_cases hm1 : m = 1
  · subst m
    rw [c_first_difference 1 d (by omega) hmd]
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.one_mul]
    have hn (b : ℕ) : g 0 b (d - 1) = c b (d - 1) := by simp [g, c, blocks]
    simp_rw [hn]
    have hd : d = (d - 1) + 1 := by omega
    rw [show Finset.range d = Finset.range ((d - 1) + 1) by rw [← hd],
      Finset.sum_range_succ']
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    simp_rw [Nat.add_comm 1]
    omega
  have hd : d = (d - 1) + 1 := by omega
  have hsub : d - 1 - (m - 1) = d - m := by omega
  have hb0 : g (m - 1) 0 (d - 1) = c (m - 1) (d - 1) := by
    unfold g c
    rw [blocks_right]
  have hg :
      (∑ b ∈ Finset.range d, g (m - 1) b (d - 1)) =
      c (m - 1) (d - 1) +
        ∑ k ∈ Finset.range (d - 1), ∑ t ∈ Finset.range d,
          (m - 1).multichoose t * c (k + t + 1) (d - m) := by
    rw [show Finset.range d = Finset.range ((d - 1) + 1) by rw [← hd],
      Finset.sum_range_succ', hb0]
    conv_lhs => rw [Nat.add_comm]
    apply congrArg (c (m - 1) (d - 1) + ·)
    apply Finset.sum_congr rfl
    intro k hk
    rw [g_forced_sum (m - 1) (k + 1) (d - 1) (by omega), hsub]
    have hlen : d - 1 + 1 = d := by omega
    rw [hlen]
    simp_rw [← Nat.multichoose_eq]
    apply Finset.sum_congr rfl
    intro t ht
    congr 2
    omega
  have hdouble := forced_double_sum (m - 1) (d - m) (d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega] at hdouble
  rw [c_first_difference m d hm hmd, hg, hdouble, ← Nat.add_assoc]
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2 <;> omega

/-- Actual matching counts have the empty matching boundary and the concrete continuation law. -/
theorem actualCount_continuation :
    actualCount 0 = 1 ∧ ∀ d : ℕ, 0 < d →
      actualCount d = c 2 d + c 0 (d - 1) +
        ∑ j ∈ Finset.Icc 1 (d - 1), c j (d - 1) := by
  constructor
  · rw [actualCount_eq_c, c_zero_zero]
  · intro d hd
    rw [actualCount_eq_c, c_empty_single d hd,
      c_triangular 1 d (by omega) (by omega)]
    simp

end D5.S3.Combinatorics.PatternMatchings.P13
