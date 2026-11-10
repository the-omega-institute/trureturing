/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact halving-partition count admits no finite integral decimation family. -/

import D5.S1.Recurrence.BinaryDecimation

/-! Exact source carriers and the unrestricted regularity question. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- A value-set test: coincident lower and upper halves are not separate labels. -/
def IsHalf (previous next : ℕ) : Prop :=
  next = previous / 2 ∨ next = (previous + 1) / 2

instance (previous next : ℕ) : Decidable (IsHalf previous next) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The virtual predecessor is supplied separately; every finite length is allowed. -/
def Follows : ℕ → List ℕ → Prop
  | _, [] => True
  | previous, next :: rest => IsHalf previous next ∧ Follows next rest

instance (previous : ℕ) (parts : List ℕ) : Decidable (Follows previous parts) := by
  induction parts generalizing previous with
  | nil => exact isTrue trivial
  | cons next rest ih => exact @instDecidableAnd _ _ (inferInstance) (ih next)

/-- Independent source carrier: actual positive ordered lists of total n. -/
def SourceLists (n : ℕ) :=
  {parts : List ℕ // (∀ x ∈ parts, 0 < x) ∧ parts.sum = n ∧ Follows n parts}

/-- The existing finite composition carrier, filtered by the same halving condition. -/
def HalvingCompositions (n : ℕ) := {c : Composition n // Follows n c.blocks}

/-- The list is unchanged in both directions; no order or multiplicity is quotiented. -/
def sourceEquiv (n : ℕ) : SourceLists n ≃ HalvingCompositions n where
  toFun p := ⟨⟨p.1, fun h => p.2.1 _ h, p.2.2.1⟩, p.2.2.2⟩
  invFun c := ⟨c.1.blocks, ⟨fun _ h => c.1.blocks_pos h, c.1.blocks_sum, c.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv c := by cases c; rfl

instance (n : ℕ) : Fintype (HalvingCompositions n) := by
  unfold HalvingCompositions
  infer_instance

instance (n : ℕ) : Finite (SourceLists n) :=
  Finite.of_equiv (HalvingCompositions n) (sourceEquiv n).symm

/-- Counts the independently specified lists, without a recurrence or proposed formula. -/
noncomputable def count (n : ℕ) : ℕ := Nat.card (SourceLists n)

/-- Fixed integral matrices, all inputs, both digits, arbitrary positive dimension. -/
def MatrixFamily (a : ℕ → ℤ) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → ℤ,
    ∃ M0 M1 : Matrix (Fin d) (Fin d) ℤ,
      (∀ n, F n ⟨0, hd⟩ = a n) ∧
      (∀ n, F (2 * n) = M0.mulVec (F n)) ∧
      (∀ n, F (2 * n + 1) = M1.mulVec (F n))

/-- A finite indexed family, with no independence or basis assumption. -/
def ClosedFamily (a : ℕ → ℤ) : Prop :=
  ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → ℤ,
    ∃ c0 c1 : Fin d → Fin d → ℤ,
      (∀ n, b ⟨0, hd⟩ n = a n) ∧
      (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧
      (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

/-- The registered negative event for the independently defined source count. -/
def claim : Prop := ¬ MatrixFamily (fun n => (count n : ℤ))

/-- The deterministic positive chain starting from a power of two. -/
def powerWord : ℕ → ℕ → List ℕ
  | _, 0 => []
  | 0, l + 1 => 1 :: powerWord 0 l
  | m + 1, l + 1 => 2 ^ m :: powerWord m l

/-- The first j rounded-up values, followed by the deterministic lower branch. -/
def oddWord : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | 0, _, l + 1 => 1 :: powerWord 0 l
  | m + 1, 0, l + 1 => 2 ^ m :: powerWord m l
  | m + 1, j + 1, l + 1 => (2 ^ m + 1) :: oddWord m j l

theorem powerWord_length (m l : ℕ) : (powerWord m l).length = l := by
  induction l generalizing m with
  | zero => simp [powerWord]
  | succ l ih => cases m <;> simp [powerWord, ih]

theorem oddWord_length (m j l : ℕ) : (oddWord m j l).length = l := by
  induction l generalizing m j with
  | zero => simp [oddWord]
  | succ l ih => cases m <;> cases j <;> simp [oddWord, powerWord_length, ih]

private theorem half_power {m x : ℕ} (hx : 0 < x) :
    IsHalf (2 ^ m) x ↔ x = 2 ^ (m - 1) := by
  cases m with
  | zero => simp [IsHalf] at *; omega
  | succ m =>
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
    simp only [hp, IsHalf, Nat.add_sub_cancel]
    omega

private theorem half_odd_power (m x : ℕ) :
    IsHalf (2 ^ (m + 1) + 1) x ↔ x = 2 ^ m ∨ x = 2 ^ m + 1 := by
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  simp only [IsHalf, hp]
  omega

private theorem power_follows (m : ℕ) (p : List ℕ)
    (hp : ∀ x ∈ p, 0 < x) :
    Follows (2 ^ m) p ↔ p = powerWord m p.length := by
  induction p generalizing m with
  | nil => simp [Follows, powerWord]
  | cons x xs ih =>
    have hx := hp x (by simp)
    have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hp y (by simp [hy])
    cases m with
    | zero =>
      have hhalf : IsHalf (2 ^ 0) x ↔ x = 1 := by simpa using half_power hx (m := 0)
      simp only [Follows, hhalf, List.length_cons, powerWord]
      constructor
      · rintro ⟨rfl, h⟩
        exact congrArg (List.cons 1) ((ih 0 hxs).mp h)
      · intro h
        have he := List.cons.inj h
        refine ⟨he.1, ?_⟩
        rw [he.1]
        exact (ih 0 hxs).mpr he.2
    | succ m =>
      have hhalf : IsHalf (2 ^ (m + 1)) x ↔ x = 2 ^ m := by
        simpa using half_power hx (m := m + 1)
      simp only [Follows, hhalf, List.length_cons, powerWord]
      constructor
      · rintro ⟨rfl, h⟩
        exact congrArg (List.cons (2 ^ m)) ((ih m hxs).mp h)
      · intro h
        have he := List.cons.inj h
        refine ⟨he.1, ?_⟩
        rw [he.1]
        exact (ih m hxs).mpr he.2

theorem odd_follows (m : ℕ) (p : List ℕ)
    (hp : ∀ x ∈ p, 0 < x) :
    Follows (2 ^ m + 1) p ↔
      ∃ j, j ≤ m ∧ j ≤ p.length ∧ p = oddWord m j p.length := by
  induction p generalizing m with
  | nil => simp [Follows, oddWord]
  | cons x xs ih =>
    have hx := hp x (by simp)
    have hxs : ∀ y ∈ xs, 0 < y := fun y hy => hp y (by simp [hy])
    cases m with
    | zero =>
      have hhalf : IsHalf (2 ^ 0 + 1) x ↔ x = 1 := by norm_num [IsHalf]
      simp only [Follows, hhalf]
      constructor
      · rintro ⟨rfl, h⟩
        refine ⟨0, by omega, by omega, ?_⟩
        simp only [List.length_cons, oddWord]
        exact congrArg (List.cons 1) ((power_follows 0 xs hxs).mp h)
      · rintro ⟨j, hj, _, he⟩
        have hj0 : j = 0 := by omega
        subst j
        simp only [List.length_cons, oddWord] at he
        have he' := List.cons.inj he
        refine ⟨he'.1, ?_⟩
        rw [he'.1]
        exact (power_follows 0 xs hxs).mpr he'.2
    | succ m =>
      simp only [Follows, half_odd_power]
      constructor
      · rintro ⟨hx', hf⟩
        rcases hx' with rfl | rfl
        · refine ⟨0, by omega, by omega, ?_⟩
          simp only [List.length_cons, oddWord]
          exact congrArg (List.cons (2 ^ m)) ((power_follows m xs hxs).mp hf)
        · obtain ⟨j, hj, hjl, he⟩ := (ih m hxs).mp hf
          refine ⟨j + 1, by omega, by simpa using Nat.succ_le_succ hjl, ?_⟩
          simp only [List.length_cons, oddWord]
          exact congrArg (List.cons (2 ^ m + 1)) he
      · rintro ⟨j, hj, hjl, he⟩
        cases j with
        | zero =>
          simp only [List.length_cons, oddWord] at he
          have he' := List.cons.inj he
          refine ⟨Or.inl he'.1, ?_⟩
          rw [he'.1]
          exact (power_follows m xs hxs).mpr he'.2
        | succ j =>
          simp only [List.length_cons, oddWord] at he
          have he' := List.cons.inj he
          refine ⟨Or.inr he'.1, ?_⟩
          rw [he'.1]
          exact (ih m hxs).mpr ⟨j, by omega, by simpa using hjl, he'.2⟩

theorem powerWord_sum_short (m l : ℕ) (hl : l ≤ m) :
    (powerWord m l).sum + 2 ^ (m - l) = 2 ^ m := by
  induction l generalizing m with
  | zero => simp [powerWord]
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have h := ih m (by omega)
      simp only [powerWord, List.sum_cons, Nat.succ_sub_succ_eq_sub]
      rw [pow_succ]
      omega

theorem powerWord_sum_long (m l : ℕ) (hl : m ≤ l) :
    (powerWord m l).sum + 1 = 2 ^ m + (l - m) := by
  induction l generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    simp [powerWord]
  | succ l ih =>
    cases m with
    | zero =>
      have h := ih 0 (by omega)
      simp only [powerWord, List.sum_cons, pow_zero, Nat.sub_zero] at *
      omega
    | succ m =>
      have h := ih m (by omega)
      simp only [powerWord, List.sum_cons, Nat.succ_sub_succ_eq_sub]
      rw [pow_succ]
      omega

theorem oddWord_sum (m j l : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) :
    (oddWord m j l).sum = (powerWord m l).sum + j := by
  induction l generalizing m j with
  | zero =>
    have hj : j = 0 := by omega
    subst j
    simp [oddWord, powerWord]
  | succ l ih =>
    cases m with
    | zero =>
    have hj : j = 0 := by omega
    subst j
    simp [oddWord, powerWord]
    | succ m =>
      cases j with
      | zero => simp [oddWord, powerWord]
      | succ j =>
        simp only [oddWord, powerWord, List.sum_cons]
        rw [ih m j (by omega) (by omega)]
        omega

/-- Every source list at a dyadic successor has one rounded-up prefix, and its
length and prefix count satisfy the exact short/long total equations. -/
theorem dyadic_source_classification (m : ℕ) (p : SourceLists (2 ^ m + 1)) :
    ∃ j, j ≤ m ∧ j ≤ p.1.length ∧ p.1 = oddWord m j p.1.length ∧
      (p.1.length ≤ m → j = 2 ^ (m - p.1.length) + 1) ∧
      (m ≤ p.1.length → j + (p.1.length - m) = 2) := by
  obtain ⟨j, hjm, hjl, he⟩ := (odd_follows m p.1 p.2.1).mp p.2.2.2
  refine ⟨j, hjm, hjl, he, ?_, ?_⟩
  · intro hl
    have hs := powerWord_sum_short m p.1.length hl
    have ho := oddWord_sum m j p.1.length hjm hjl
    have ht := p.2.2.1
    rw [he] at ht
    omega
  · intro hl
    have hs := powerWord_sum_long m p.1.length hl
    have ho := oddWord_sum m j p.1.length hjm hjl
    have ht := p.2.2.1
    rw [he] at ht
    omega

private theorem powerWord_positive (m l : ℕ) :
    ∀ x ∈ powerWord m l, 0 < x := by
  induction l generalizing m with
  | zero => simp [powerWord]
  | succ l ih =>
    cases m with
    | zero =>
      rw [powerWord, List.forall_mem_cons]
      exact ⟨by decide, ih 0⟩
    | succ m =>
      rw [powerWord, List.forall_mem_cons]
      exact ⟨by positivity, ih m⟩

private theorem oddWord_positive (m j l : ℕ) :
    ∀ x ∈ oddWord m j l, 0 < x := by
  induction l generalizing m j with
  | zero => simp [oddWord]
  | succ l ih =>
    cases m with
    | zero =>
      rw [oddWord, List.forall_mem_cons]
      exact ⟨by decide, powerWord_positive 0 l⟩
    | succ m =>
      cases j with
      | zero =>
        rw [oddWord, List.forall_mem_cons]
        exact ⟨by positivity, powerWord_positive m l⟩
      | succ j =>
        rw [oddWord, List.forall_mem_cons]
        exact ⟨by positivity, ih m j⟩

theorem oddWord_prefix_injective (m l j k : ℕ)
    (hjm : j ≤ m) (hjl : j ≤ l) (hkm : k ≤ m) (hkl : k ≤ l)
    (he : oddWord m j l = oddWord m k l) : j = k := by
  induction l generalizing m j k with
  | zero => omega
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      cases j with
      | zero =>
        cases k with
        | zero => rfl
        | succ k => simp only [oddWord, List.cons.injEq] at he; omega
      | succ j =>
        cases k with
        | zero => simp only [oddWord, List.cons.injEq] at he; omega
        | succ k =>
          simp only [oddWord, List.cons.injEq] at he
          have := ih m j k (by omega) (by omega) (by omega) (by omega) he.2
          omega

abbrev Threshold (m : ℕ) :=
  {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}

abbrev DyadicCode (m : ℕ) := Fin 3 ⊕ Threshold m

def codeParams (m : ℕ) : DyadicCode m → ℕ × ℕ
  | .inl i => if i = 0 then (m, 2) else if i = 1 then (m + 1, 1) else (m + 2, 0)
  | .inr r => (m - r.1.val, 2 ^ r.1.val + 1)

theorem code_bounds (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
    (codeParams m c).2 ≤ m ∧ (codeParams m c).2 ≤ (codeParams m c).1 := by
  rcases c with i | r
  · fin_cases i <;> simp [codeParams] <;> omega
  · have hr := r.2
    simp only [codeParams]
    omega

private theorem code_total (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
    (oddWord m (codeParams m c).2 (codeParams m c).1).sum = 2 ^ m + 1 := by
  have hb := code_bounds m hm c
  rw [oddWord_sum m _ _ hb.1 hb.2]
  rcases c with i | r
  · fin_cases i
    · simp [codeParams]
      have := powerWord_sum_short m m (by omega)
      simp only [Nat.sub_self, pow_zero] at this
      omega
    · simp [codeParams]
      have := powerWord_sum_long m (m + 1) (by omega)
      omega
    · simp [codeParams]
      have := powerWord_sum_long m (m + 2) (by omega)
      omega
  · simp only [codeParams]
    have hr : r.1.val ≤ m := by omega
    have hs := powerWord_sum_short m (m - r.1.val) (by omega)
    have he : m - (m - r.1.val) = r.1.val := by omega
    rw [he] at hs
    omega

def codeSource (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
    SourceLists (2 ^ m + 1) := by
  let l := (codeParams m c).1
  let j := (codeParams m c).2
  have hb := code_bounds m hm c
  refine ⟨oddWord m j l, oddWord_positive m j l, code_total m hm c, ?_⟩
  apply (odd_follows m _ (oddWord_positive m j l)).mpr
  refine ⟨j, hb.1, ?_, ?_⟩
  · simpa only [oddWord_length] using hb.2
  · rw [oddWord_length]

private theorem codeParams_injective (m : ℕ) : Function.Injective (codeParams m) := by
  intro c d he
  rcases c with i | r <;> rcases d with k | s
  · have h := congrArg Prod.fst he
    fin_cases i <;> fin_cases k <;> simp [codeParams] at h ⊢
  · have h := congrArg Prod.fst he
    have hs := s.2
    fin_cases i <;> simp [codeParams] at h <;> omega
  · have h := congrArg Prod.fst he
    have hr := r.2
    fin_cases k <;> simp [codeParams] at h <;> omega
  · have h := congrArg Prod.fst he
    have hr := r.1.2
    have hs := s.1.2
    simp only [codeParams] at h
    have hv : r.1.val = s.1.val := by omega
    have : r = s := Subtype.ext (Fin.ext hv)
    subst s
    rfl

theorem codeSource_bijective (m : ℕ) (hm : 2 ≤ m) :
    Function.Bijective (codeSource m hm) := by
  constructor
  · intro c d he
    have he' := congrArg Subtype.val he
    change oddWord m (codeParams m c).2 (codeParams m c).1 =
      oddWord m (codeParams m d).2 (codeParams m d).1 at he'
    have hl := congrArg List.length he'
    simp only [oddWord_length] at hl
    apply codeParams_injective m
    apply Prod.ext hl
    have hc := code_bounds m hm c
    have hd := code_bounds m hm d
    rw [← hl] at he'
    exact oddWord_prefix_injective m _ _ _ hc.1 hc.2 hd.1 (by omega) he'
  · intro p
    obtain ⟨j, hjm, hjl, he, hs, ht⟩ := dyadic_source_classification m p
    have hex : ∃ c : DyadicCode m,
        codeParams m c = (p.1.length, j) := by
      by_cases hl : p.1.length < m
      · have hshort := hs (by omega)
        have hr : m - p.1.length < m + 1 := by omega
        have ht' : 2 ^ (m - p.1.length) + (m - p.1.length) + 1 ≤ m := by omega
        refine ⟨.inr ⟨⟨m - p.1.length, hr⟩, (show 1 ≤ m - p.1.length from by omega), ht'⟩, ?_⟩
        simp only [codeParams]
        exact Prod.ext (by omega) hshort.symm
      · have hlong := ht (by omega)
        have hl' : p.1.length = m ∨ p.1.length = m + 1 ∨ p.1.length = m + 2 := by omega
        rcases hl' with h | h | h
        · have hj : j = 2 := by omega
          exact ⟨.inl 0, by simp [codeParams, h, hj]⟩
        · have hj : j = 1 := by omega
          exact ⟨.inl 1, by simp [codeParams, h, hj]⟩
        · have hj : j = 0 := by omega
          exact ⟨.inl 2, by simp [codeParams, h, hj]⟩
    obtain ⟨c, hc⟩ := hex
    refine ⟨c, Subtype.ext ?_⟩
    change oddWord m (codeParams m c).2 (codeParams m c).1 = p.1
    rw [hc]
    exact he.symm

/-- The independent source count at every dyadic successor, including all tails of ones. -/
theorem dyadic_source_count (m : ℕ) (hm : 2 ≤ m) :
    count (2 ^ m + 1) = 3 +
      Fintype.card {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m} := by
  have e := Equiv.ofBijective (codeSource m hm) (codeSource_bijective m hm)
  unfold count
  rw [Nat.card_congr e.symm, Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_fin]

theorem threshold_mono {r s : ℕ} (h : r ≤ s) :
    2 ^ r + r + 1 ≤ 2 ^ s + s + 1 := by
  have hp : (2 : ℕ) ^ r ≤ 2 ^ s := pow_le_pow_right₀ (by decide) h
  omega

theorem dyadic_plateau (m r : ℕ) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (hlo : 2 ^ r + r + 1 ≤ m) (hhi : m < 2 ^ (r + 1) + (r + 1) + 1) :
    count (2 ^ m + 1) = 3 + r := by
  rw [dyadic_source_count m hm]
  have hpred (q : Fin (m + 1)) :
      (1 ≤ q.val ∧ 2 ^ q.val + q.val + 1 ≤ m) ↔ (1 ≤ q.val ∧ q.val ≤ r) := by
    constructor
    · rintro ⟨hq, ht⟩
      refine ⟨hq, ?_⟩
      by_contra hn
      have h := threshold_mono (r := r + 1) (s := q.val) (by omega)
      omega
    · rintro ⟨hq, hqr⟩
      have h := threshold_mono hqr
      exact ⟨hq, by omega⟩
  let f : Fin r → Threshold m := fun i =>
    ⟨⟨i.val + 1, by omega⟩, (hpred _).mpr ⟨(by change 1 ≤ i.val + 1; omega), (by change i.val + 1 ≤ r; omega)⟩⟩
  have hb : Function.Bijective f := by
    constructor
    · intro i j h
      have hv := congrArg (fun q : Threshold m => q.1.val) h
      apply Fin.ext
      change i.val + 1 = j.val + 1 at hv
      omega
    · intro q
      have hq := (hpred q.1).mp q.2
      refine ⟨⟨q.1.val - 1, by omega⟩, ?_⟩
      apply Subtype.ext
      apply Fin.ext
      change q.1.val - 1 + 1 = q.1.val
      omega
  have hc := Fintype.card_congr (Equiv.ofBijective f hb)
  simp only [Fintype.card_fin] at hc
  exact congrArg (fun t => 3 + t) hc.symm

/-- The actual list count is nonregular over every nonzero commutative ring.
The contradiction uses a monic forward recurrence and never divides. -/
theorem nonregularity_over (R : Type*) [CommRing R] [Nontrivial R] :
    ¬ BinaryDecimation.MatrixFamily (fun n => (count n : R)) := by
  intro ha
  obtain ⟨E, hd, hE⟩ := BinaryDecimation.dyadic_matrix_recurrence (fun n => (count n : R)) ha
  let u (n : ℕ) : R := (count (2 ^ (n + 2) + 1) : R)
  let c (n : ℕ) : R := u (n + 1) - u n
  have hc : E.IsSolution c := by
    simpa only [c, one_mul] using
      BinaryDecimation.shifted_sub_solution E u hE (1 : R)
  let r := E.order + 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hpow : E.order ≤ 2 ^ r := by
    have h : r < 2 ^ r := Nat.lt_two_pow_self
    dsimp [r] at *
    omega
  let start := 2 ^ r + r - 1
  have hzero (i : ℕ) (hi : i < E.order) : c (start + i) = 0 := by
    have hpow' : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; omega
    have hp : 0 < 2 ^ r := by positivity
    have h0 := dyadic_plateau (start + i + 2) r (by omega) hr (by dsimp [start]; omega)
      (by dsimp [start]; omega)
    have h1 := dyadic_plateau (start + i + 1 + 2) r (by omega) hr (by dsimp [start]; omega)
      (by dsimp [start]; omega)
    dsimp [c, u]
    rw [h0, h1]
    simp
  have hshift : E.IsSolution (fun n => c (start + n)) := by
    intro n
    simpa only [Nat.add_assoc] using hc (start + n)
  have hident : (fun n => c (start + n)) = (fun _ => (0 : R)) := by
    apply (E.eq_iff_eqOn_range_order _ _ hshift ?_).mpr
    · intro i hi
      exact hzero i (Finset.mem_range.mp hi)
    · intro n
      simp
  let jump := 2 ^ (r + 1) + (r + 1) - 2
  have hp : 0 < 2 ^ r := by positivity
  have hp' : 0 < 2 ^ (r + 1) := by positivity
  have hj : start ≤ jump := by
    have h := threshold_mono (r := r) (s := r + 1) (by omega)
    dsimp [start, jump]
    omega
  have h0 := dyadic_plateau (jump + 2) r (by omega) hr (by dsimp [jump]; omega)
    (by dsimp [jump]; omega)
  have h1 := dyadic_plateau (jump + 1 + 2) (r + 1) (by omega) (by omega)
    (by dsimp [jump]; omega) (by
      have h := threshold_mono (r := r + 1) (s := r + 2) (by omega)
      have hp2 : 2 ^ (r + 1) ≤ 2 ^ (r + 2) := pow_le_pow_right₀ (by decide) (by omega)
      dsimp [jump]
      omega)
  have hnonzero : c jump = 1 := by
    dsimp [c, u]
    rw [h0, h1]
    push_cast
    ring
  have hz := congrFun hident (jump - start)
  have hidx : start + (jump - start) = jump := by omega
  rw [hidx, hnonzero] at hz
  exact one_ne_zero hz

private theorem source_nonregularity : claim := by
  exact nonregularity_over ℤ

/-- A literal arbitrary finite indexed family, with a distinguished member a.
The indexing type is arbitrary; different indices may carry equal sequences. -/
def ArbitraryFamily (a : ℕ → ℤ) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι;
    ∃ (b : ι → ℕ → ℤ) (i0 : ι) (c0 c1 : ι → ι → ℤ),
      (∀ n, b i0 n = a n) ∧
      (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧
      (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

private theorem closed_matrix_iff (a : ℕ → ℤ) : ClosedFamily a ↔ MatrixFamily a := by
  exact BinaryDecimation.closed_matrix_iff a

private theorem arbitrary_matrix_iff (a : ℕ → ℤ) :
    ArbitraryFamily a ↔ MatrixFamily a := by
  exact BinaryDecimation.arbitrary_matrix_iff a


private theorem source_zero : count 0 = 1 := by
  let e : SourceLists 0 ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨[], by simp, rfl, trivial⟩
    left_inv := fun p => by
      apply Subtype.ext
      exact ((Composition.blocks_eq_nil (sourceEquiv 0 p).1).mpr rfl).symm
    right_inv := fun u => by cases u; rfl }
  unfold count
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_unit]

/-- The exact negative answer and both finite-family interfaces, with independent count transport. -/
theorem result :
    (¬ MatrixFamily (fun n => (count n : ℤ))) ∧
    (∀ a : ℕ → ℤ, ClosedFamily a ↔ MatrixFamily a) ∧
    (∀ a : ℕ → ℤ, ArbitraryFamily a ↔ MatrixFamily a) ∧
    (¬ ArbitraryFamily (fun n => (count n : ℤ))) ∧
    (∀ n, count n = Fintype.card (HalvingCompositions n)) ∧ count 0 = 1 := by
  refine ⟨source_nonregularity, closed_matrix_iff, arbitrary_matrix_iff, ?_, ?_, source_zero⟩
  · intro h
    exact source_nonregularity ((arbitrary_matrix_iff _).mp h)
  · classical
    intro n
    letI : Fintype (SourceLists n) := Fintype.ofFinite _
    unfold count
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (sourceEquiv n)

#print axioms result

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
