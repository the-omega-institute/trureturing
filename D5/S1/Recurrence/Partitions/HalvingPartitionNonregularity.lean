/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionNonregularity
   mirror-E: none(waiver:unbounded-symbolic-question)
   anchors: []
   utility: none
   digest: Exact ordered-list count and unrestricted binary matrix-family question. -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.LinearRecurrence
import Mathlib.SetTheory.Cardinal.Finite

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

/-- The registered negative event; no theorem asserting it is supplied here. -/
def claim : Prop := ¬ MatrixFamily (fun n => (count n : ℤ))

/-- The deterministic positive chain starting from a power of two. -/
private def powerWord : ℕ → ℕ → List ℕ
  | _, 0 => []
  | 0, l + 1 => 1 :: powerWord 0 l
  | m + 1, l + 1 => 2 ^ m :: powerWord m l

/-- The first j rounded-up values, followed by the deterministic lower branch. -/
private def oddWord : ℕ → ℕ → ℕ → List ℕ
  | _, _, 0 => []
  | 0, _, l + 1 => 1 :: powerWord 0 l
  | m + 1, 0, l + 1 => 2 ^ m :: powerWord m l
  | m + 1, j + 1, l + 1 => (2 ^ m + 1) :: oddWord m j l

private theorem powerWord_length (m l : ℕ) : (powerWord m l).length = l := by
  induction l generalizing m with
  | zero => simp [powerWord]
  | succ l ih => cases m <;> simp [powerWord, ih]

private theorem oddWord_length (m j l : ℕ) : (oddWord m j l).length = l := by
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

private theorem odd_follows (m : ℕ) (p : List ℕ)
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

private theorem powerWord_sum_short (m l : ℕ) (hl : l ≤ m) :
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

private theorem powerWord_sum_long (m l : ℕ) (hl : m ≤ l) :
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

private theorem oddWord_sum (m j l : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) :
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

private theorem oddWord_prefix_injective (m l j k : ℕ)
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

private abbrev Threshold (m : ℕ) :=
  {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}

private abbrev DyadicCode (m : ℕ) := Fin 3 ⊕ Threshold m

private def codeParams (m : ℕ) : DyadicCode m → ℕ × ℕ
  | .inl i => if i = 0 then (m, 2) else if i = 1 then (m + 1, 1) else (m + 2, 0)
  | .inr r => (m - r.1.val, 2 ^ r.1.val + 1)

private theorem code_bounds (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
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
  · simp only [codeParams, Prod.fst, Prod.snd]
    have hr : r.1.val ≤ m := by omega
    have hs := powerWord_sum_short m (m - r.1.val) (by omega)
    have he : m - (m - r.1.val) = r.1.val := by omega
    rw [he] at hs
    omega

private def codeSource (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
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
    fin_cases i <;> fin_cases k <;> simp [codeParams] at h ⊢ <;> omega
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

private theorem codeSource_bijective (m : ℕ) (hm : 2 ≤ m) :
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

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
