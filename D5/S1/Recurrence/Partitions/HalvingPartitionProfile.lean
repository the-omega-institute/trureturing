/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionProfile
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact length fibers and length enumerators for the actual halving lists at every dyadic successor. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
import Mathlib.Algebra.Polynomial.Derivative

/-! Length fibers and finite source enumerators. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

noncomputable instance sourceFintype (n : ℕ) : Fintype (SourceLists n) :=
  Fintype.ofFinite _

/-- The number of actual source lists of exactly the specified length. -/
noncomputable def lengthCount (n ell : ℕ) : ℕ :=
  Nat.card {p : SourceLists n // p.val.length = ell}

/-- The complete finite length polynomial of the actual lists. -/
noncomputable def lengthPolynomial (n : ℕ) : Polynomial ℕ :=
  ∑ p : SourceLists n, Polynomial.X ^ p.val.length

/-- The code preserves its literal list length. -/
theorem codeSource_length (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) :
    (codeSource m hm c).val.length = (codeParams m c).1 := by
  exact oddWord_length _ _ _

/-- At a fixed dyadic successor, length determines the actual ordered list. -/
theorem source_length_injective (m : ℕ) :
    Function.Injective (fun p : SourceLists (2 ^ m + 1) => p.val.length) := by
  intro p q hl
  change p.val.length = q.val.length at hl
  obtain ⟨j, hjm, hjl, hp, hps, hpl⟩ := dyadic_source_classification m p
  obtain ⟨k, hkm, hkl, hq, hqs, hql⟩ := dyadic_source_classification m q
  have hjk : j = k := by
    by_cases h : p.val.length ≤ m
    · have hs := hps h
      have ht := hqs (by omega)
      rw [← hl] at ht
      omega
    · have hs := hpl (by omega)
      have ht := hql (by omega)
      omega
  apply Subtype.ext
  rw [hp, hq, hl, hjk]

/-- Every original short and long endpoint is present, and no other length is. -/
theorem source_length_support (m ell : ℕ) (hm : 2 ≤ m) :
    (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔
      ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨
        ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r := by
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨c, rfl⟩ := (codeSource_bijective m hm).2 p
    rw [codeSource_length]
    rcases c with i | r
    · fin_cases i <;> simp [codeParams]
    · exact Or.inr (Or.inr (Or.inr ⟨r.val.val, r.prop.1, r.prop.2, rfl⟩))
  · intro h
    rcases h with h | h | h | ⟨r, hr, ht, h⟩
    · subst ell
      exact ⟨codeSource m hm (.inl 0), by simp [codeSource_length, codeParams]⟩
    · subst ell
      exact ⟨codeSource m hm (.inl 1), by simp [codeSource_length, codeParams]⟩
    · subst ell
      exact ⟨codeSource m hm (.inl 2), by simp [codeSource_length, codeParams]⟩
    · subst ell
      have hrm : r < m + 1 := by
        have hp : 0 < (2 : ℕ) ^ r := by positivity
        omega
      exact ⟨codeSource m hm (.inr ⟨⟨r, hrm⟩, hr, ht⟩),
        by simp [codeSource_length, codeParams]⟩

open Classical in
/-- Every supported length has one object, and every other length has zero. -/
theorem lengthCount_dyadic (m ell : ℕ) (hm : 2 ≤ m) :
    lengthCount (2 ^ m + 1) ell =
      if ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨
        (∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r)
      then 1 else 0 := by
  classical
  let fiber := {p : SourceLists (2 ^ m + 1) // p.val.length = ell}
  have hs : Subsingleton fiber := ⟨fun p q =>
    Subtype.ext (source_length_injective m (p.prop.trans q.prop.symm))⟩
  change Nat.card fiber = _
  split_ifs with h
  · exact Nat.card_eq_one_iff_unique.mpr
      ⟨hs, by obtain ⟨p, hp⟩ := (source_length_support m ell hm).mpr h; exact ⟨⟨p, hp⟩⟩⟩
  · have hi : IsEmpty fiber := ⟨fun p => h ((source_length_support m ell hm).mp ⟨p.val, p.prop⟩)⟩
    exact Nat.card_eq_zero.mpr (Or.inl hi)

/-- Reindexing uses the original exhaustive source bijection. -/
theorem sum_source_dyadic {A : Type*} [AddCommMonoid A]
    (m : ℕ) (hm : 2 ≤ m) (f : SourceLists (2 ^ m + 1) → A) :
    ∑ p, f p = ∑ c : DyadicCode m, f (codeSource m hm c) := by
  exact ((Equiv.ofBijective (codeSource m hm) (codeSource_bijective m hm)).sum_comp f).symm

/-- A polynomial identity retaining every source length, including terminal ones. -/
theorem lengthPolynomial_dyadic (m : ℕ) (hm : 2 ≤ m) :
    lengthPolynomial (2 ^ m + 1) =
      Polynomial.X ^ m * (1 + Polynomial.X + Polynomial.X ^ 2) +
        ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val) := by
  classical
  unfold lengthPolynomial
  rw [sum_source_dyadic m hm, Fintype.sum_sum_type]
  simp only [codeSource_length]
  rw [Fin.sum_univ_three]
  simp only [codeParams, ↓reduceIte, Fin.isValue, one_ne_zero, Fin.reduceEq]
  simp only [pow_succ]
  ring

/-- The original threshold count R_m; the finite bound loses no qualifying r. -/
def thresholdCount (m : ℕ) : ℕ := Fintype.card (Threshold m)

/-- The qualifying positive thresholds form exactly the initial interval 1,...,R_m. -/
theorem threshold_iff_le_count (m r : ℕ) :
    (1 ≤ r ∧ 2 ^ r + r + 1 ≤ m) ↔ (1 ≤ r ∧ r ≤ thresholdCount m) := by
  constructor
  · rintro ⟨hr, ht⟩
    refine ⟨hr, ?_⟩
    have hp : 0 < (2 : ℕ) ^ r := by positivity
    let f : Fin r → Threshold m := fun i =>
      ⟨⟨i.val + 1, by omega⟩, (by change 1 ≤ i.val + 1; omega),
        (threshold_mono (r := i.val + 1) (s := r) (by omega)).trans ht⟩
    have hinj : Function.Injective f := by
      intro i j h
      have hv := congrArg (fun q : Threshold m => q.val.val) h
      change i.val + 1 = j.val + 1 at hv
      exact Fin.ext (by omega)
    simpa only [Fintype.card_fin, thresholdCount] using Fintype.card_le_of_injective f hinj
  · rintro ⟨hr, hc⟩
    refine ⟨hr, ?_⟩
    by_contra hn
    have hlt (q : Threshold m) : q.val.val < r := by
      by_contra h
      have ht := threshold_mono (r := r) (s := q.val.val) (by omega)
      have hq := q.prop.2
      omega
    let f : Threshold m → Fin (r - 1) := fun q => ⟨q.val.val - 1,
      by have hq := q.prop.1; have hl := hlt q; omega⟩
    have hinj : Function.Injective f := by
      intro q t h
      have hv := congrArg Fin.val h
      have hq := q.prop.1
      have ht := t.prop.1
      apply Subtype.ext
      apply Fin.ext
      change q.val.val - 1 = t.val.val - 1 at hv
      omega
    have hcard := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hcard
    change thresholdCount m ≤ r - 1 at hcard
    omega

/-- The threshold interval stays strictly below m, including the empty case. -/
theorem thresholdCount_lt (m : ℕ) (hm : 2 ≤ m) : thresholdCount m < m := by
  by_cases hz : thresholdCount m = 0
  · omega
  · have ht := (threshold_iff_le_count m (thresholdCount m)).mpr ⟨by omega, le_rfl⟩
    have hp : 0 < (2 : ℕ) ^ thresholdCount m := by positivity
    omega

/-- The source's complete support is a consecutive interval, with all endpoints. -/
theorem source_length_interval (m ell : ℕ) (hm : 2 ≤ m) :
    (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔
      m - thresholdCount m ≤ ell ∧ ell ≤ m + 2 := by
  rw [source_length_support m ell hm]
  have hrm := thresholdCount_lt m hm
  constructor
  · rintro (h | h | h | ⟨r, hr, ht, h⟩)
    · omega
    · omega
    · omega
    · have hc := (threshold_iff_le_count m r).mp ⟨hr, ht⟩
      omega
  · rintro ⟨hlo, hhi⟩
    by_cases h : ell < m
    · right; right; right
      have hr : 1 ≤ m - ell ∧ m - ell ≤ thresholdCount m := by omega
      exact ⟨m - ell, hr.1, ((threshold_iff_le_count m _).mpr hr).2, by omega⟩
    · omega

/-- Increasing length is a genuine bijection between actual lists and the
integer interval of size R_m+3; it does not reorder any partition's entries. -/
noncomputable def lengthIntervalEquiv (m : ℕ) (hm : 2 ≤ m) :
    SourceLists (2 ^ m + 1) ≃ Fin (thresholdCount m + 3) := by
  let f : SourceLists (2 ^ m + 1) → Fin (thresholdCount m + 3) := fun p =>
    ⟨p.val.length - (m - thresholdCount m), by
      have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩
      have hr := thresholdCount_lt m hm
      omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply source_length_injective m
    change p.val.length = q.val.length
    have he := congrArg Fin.val h
    have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩
    have hq := (source_length_interval m q.val.length hm).mp ⟨q, rfl⟩
    change p.val.length - (m - thresholdCount m) =
      q.val.length - (m - thresholdCount m) at he
    omega
  · intro i
    have hr := thresholdCount_lt m hm
    have hi := i.isLt
    obtain ⟨p, hp⟩ := (source_length_interval m (m - thresholdCount m + i.val) hm).mpr
      ⟨by omega, by omega⟩
    refine ⟨p, Fin.ext ?_⟩
    change p.val.length - (m - thresholdCount m) = i.val
    omega

/-- Length readout of the interval equivalence. -/
theorem lengthIntervalEquiv_length (m : ℕ) (hm : 2 ≤ m)
    (p : SourceLists (2 ^ m + 1)) :
    p.val.length = m - thresholdCount m + (lengthIntervalEquiv m hm p).val := by
  change p.val.length = m - thresholdCount m + (p.val.length - (m - thresholdCount m))
  have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩
  omega

/-- Any observable of length can be summed over the exact consecutive interval. -/
theorem sum_source_lengths {A : Type*} [AddCommMonoid A]
    (m : ℕ) (hm : 2 ≤ m) (f : ℕ → A) :
    ∑ p : SourceLists (2 ^ m + 1), f p.val.length =
      ∑ i : Fin (thresholdCount m + 3), f (m - thresholdCount m + i.val) := by
  classical
  calc
    _ = ∑ p : SourceLists (2 ^ m + 1),
        f (m - thresholdCount m + (lengthIntervalEquiv m hm p).val) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← lengthIntervalEquiv_length m hm p]
    _ = _ := (lengthIntervalEquiv m hm).sum_comp
      (fun i : Fin (thresholdCount m + 3) => f (m - thresholdCount m + i.val))

/-- The total number of parts counts the lengths of the actual lists. -/
noncomputable def totalParts (n : ℕ) : ℕ := ∑ p : SourceLists n, p.val.length

/-- Total parts is the derivative at one of the actual length polynomial. -/
theorem totalParts_eq_derivative (n : ℕ) :
    totalParts n = (lengthPolynomial n).derivative.eval 1 := by
  classical
  simp [totalParts, lengthPolynomial,
    Polynomial.derivative_X_pow, Polynomial.eval_finsetSum]

private def thresholdIndexEquiv (m : ℕ) (hm : 2 ≤ m) :
    Threshold m ≃ Fin (thresholdCount m) where
  toFun r := ⟨r.val.val - 1, by
    have hs := ((threshold_iff_le_count m r.val.val).mp r.prop).2
    have hp := r.prop.1
    omega⟩
  invFun i := ⟨⟨i.val + 1, by have := thresholdCount_lt m hm; omega⟩,
    (threshold_iff_le_count m (i.val + 1)).mpr ⟨by omega, by omega⟩⟩
  left_inv r := by
    apply Subtype.ext
    apply Fin.ext
    change r.val.val - 1 + 1 = r.val.val
    have := r.prop.1
    omega
  right_inv i := by
    apply Fin.ext
    simp

/-- An integral identity before any subtraction or division. The length
polynomial is genuinely consumed through its derivative; the threshold sum
is reindexed by the literal positive threshold interval. -/
theorem totalParts_twice (m : ℕ) (hm : 2 ≤ m) :
    2 * totalParts (2 ^ m + 1) =
      (thresholdCount m + 3) * (2 * m + 2 - thresholdCount m) := by
  classical
  have hr := thresholdCount_lt m hm
  have hparts : totalParts (2 ^ m + 1) =
      3 * m + 3 + ∑ r : Threshold m, (m - r.val.val) := by
    rw [totalParts_eq_derivative, lengthPolynomial_dyadic m hm]
    simp [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow,
      Polynomial.eval_finsetSum]
    omega
  have hs : (∑ r : Threshold m, (m - r.val.val)) =
      ∑ i : Fin (thresholdCount m), (m - (i.val + 1)) := by
    have h := (thresholdIndexEquiv m hm).symm.sum_comp
      (fun r : Threshold m => m - r.val.val)
    change (∑ i : Fin (thresholdCount m), (m - (i.val + 1))) =
      ∑ r : Threshold m, (m - r.val.val) at h
    exact h.symm
  have hcancel : (∑ i : Fin (thresholdCount m), (m - (i.val + 1))) +
      (∑ i : Fin (thresholdCount m), (i.val + 1)) = thresholdCount m * m := by
    rw [← Finset.sum_add_distrib]
    have he : ∀ i : Fin (thresholdCount m), m - (i.val + 1) + (i.val + 1) = m := by
      intro i
      have := i.isLt
      omega
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have htri : 2 * (∑ i : Fin (thresholdCount m), (i.val + 1)) =
      thresholdCount m * (thresholdCount m + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1) (thresholdCount m),
      Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    have ht := Finset.sum_range_id_mul_two (thresholdCount m)
    by_cases hz : thresholdCount m = 0
    · simp [hz]
    · nlinarith [Nat.sub_add_cancel (show 1 ≤ thresholdCount m by omega)]
  rw [hparts, hs]
  have hsub : 2 * m + 2 - thresholdCount m + thresholdCount m = 2 * m + 2 := by omega
  have hmul := congrArg (fun x => (thresholdCount m + 3) * x) hsub
  nlinarith

/-- The manuscript formula uses exact natural subtraction and integer division. -/
theorem totalParts_dyadic (m : ℕ) (hm : 2 ≤ m) :
    totalParts (2 ^ m + 1) =
      (thresholdCount m + 3) * m + 3 - thresholdCount m * (thresholdCount m + 1) / 2 := by
  have ht := totalParts_twice m hm
  have hr := thresholdCount_lt m hm
  have he : 2 * (thresholdCount m * (thresholdCount m + 1) / 2) =
      thresholdCount m * (thresholdCount m + 1) := by
    rw [Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one _)]
  have hsub : 2 * m + 2 - thresholdCount m + thresholdCount m = 2 * m + 2 := by omega
  have hprod := congrArg (fun x => (thresholdCount m + 3) * x) hsub
  have hadd : totalParts (2 ^ m + 1) +
      thresholdCount m * (thresholdCount m + 1) / 2 = (thresholdCount m + 3) * m + 3 := by
    nlinarith
  omega

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
