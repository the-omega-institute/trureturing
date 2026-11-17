/- GID: D5/S3/Arith/Recurrence/A124056Occurrence
   generality: G
   mirror-B: D5/B/S3/Arith/Recurrence/A124056Occurrence
   mirror-E: none(waiver:open-full-occurrence-proof)
   anchors: []
   utility: none
   digest: Exact positive-integer divisibility recurrence with no zero sentinel. -/

import D5.S3.Arith.Divisors.DivisorSubpower
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic

/-!
The source sequence is indexed internally from zero only to make the finite
prefix available as a dependent tuple.  `term n` is exactly the source term
`a_(n+1)`; no value at a fictitious index participates in the recurrence.
-/

namespace D5.S3.Arith.Recurrence.A124056Occurrence

def values : (n : ℕ) → Fin (n + 1) → ℕ
  | 0, _ => 1
  | n + 1, i =>
      let previous := values n
      let next := ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun j => previous j ∣ previous (Fin.last n))).card
      Fin.snoc (α := fun _ => ℕ) previous next i

def term (n : ℕ) : ℕ := values n (Fin.last n)

private theorem term_zero : term 0 = 1 := by
  simp [term, values]

private theorem term_succ (n : ℕ) :
    term (n + 1) =
      ((Finset.univ : Finset (Fin (n + 1))).filter
        (fun j => values n j ∣ term n)).card := by
  change (Fin.snoc (α := fun _ => ℕ) (values n) _ (Fin.last (n + 1))) = _
  exact Fin.snoc_last _ _

private theorem term_one : term 1 = 1 := by
  simp [term, values, Fin.snoc]

private theorem term_two : term 2 = 2 := by
  norm_num [term, values, Fin.snoc]

private theorem values_eq_term (n : ℕ) (i : Fin (n + 1)) : values n i = term i.val := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      rfl
  | succ n ih =>
      by_cases hi : i.val < n + 1
      · have hi' : i = (⟨i.val, hi⟩ : Fin (n + 1)).castSucc := Fin.ext rfl
        rw [hi']
        change Fin.snoc (α := fun _ => ℕ) (values n) _ _ = _
        rw [Fin.snoc_castSucc]
        exact ih _
      · have hi' : i = Fin.last (n + 1) := Fin.ext (by simp; omega)
        subst i
        rfl

def divisorIndices (t v : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => term i ∣ v)

private theorem recurrence (n : ℕ) :
    term (n + 1) = (divisorIndices (n + 1) (term n)).card := by
  rw [term_succ]
  unfold divisorIndices
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,
      by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, values_eq_term]
        using hi⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩, ?_, rfl⟩
    simpa [Finset.mem_filter, values_eq_term] using (Finset.mem_filter.mp hj).2

private theorem term_pos (n : ℕ) : 0 < term n := by
  cases n with
  | zero => simp [term_zero]
  | succ n =>
      rw [recurrence]
      apply Finset.card_pos.mpr
      exact ⟨n, by simp [divisorIndices]⟩

private theorem source_recurrence (n : ℕ) (hn : 0 < n) :
    term n = ((Finset.Icc 1 n).filter
      (fun i => term (i - 1) ∣ term (n - 1))).card := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [recurrence]
  apply Finset.card_bij (fun i _ => i + 1)
  · intro i hi
    simpa [divisorIndices, Finset.mem_filter, Finset.mem_Icc] using hi
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij
  · intro j hj
    refine ⟨j - 1, ?_, by have := (Finset.mem_filter.mp hj).1; simp at this; omega⟩
    have hj' := Finset.mem_filter.mp hj
    simp only [Finset.mem_Icc] at hj'
    simpa [divisorIndices, Finset.mem_filter, Finset.mem_range] using
      And.intro (show j - 1 < m + 1 by omega) hj'.2

private theorem successor_strict_of_repeat {i j : ℕ} (hij : i < j)
    (hvalue : term i = term j) : term (i + 1) < term (j + 1) := by
  rw [recurrence, recurrence, ← hvalue]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro k hk
    simp only [divisorIndices, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2⟩
  · intro heq
    have hj : j ∈ divisorIndices (j + 1) (term i) := by
      simp [divisorIndices, hvalue]
    rw [← heq] at hj
    simp only [divisorIndices, Finset.mem_filter, Finset.mem_range] at hj
    omega

private theorem pair_injective : Function.Injective (fun n => (term n, term (n + 1))) := by
  intro i j h
  have hv : term i = term j := congrArg Prod.fst h
  have hs : term (i + 1) = term (j + 1) := congrArg Prod.snd h
  rcases lt_trichotomy i j with hij | hij | hij
  · have := successor_strict_of_repeat hij hv
    omega
  · exact hij
  · have := successor_strict_of_repeat hij hv.symm
    omega

private theorem unbounded (B : ℕ) : ∃ n : ℕ, B < term n := by
  classical
  by_contra! hB
  let f : ℕ → Fin (B + 1) × Fin (B + 1) :=
    fun n => (⟨term n, by have := hB n; omega⟩,
      ⟨term (n + 1), by have := hB (n + 1); omega⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply pair_injective
    have h1 := congrArg (fun x : Fin (B + 1) × Fin (B + 1) => x.1.val) hij
    have h2 := congrArg (fun x : Fin (B + 1) × Fin (B + 1) => x.2.val) hij
    exact Prod.ext h1 h2
  exact not_injective_infinite_finite f hf

private theorem term_ge_two {n : ℕ} (hn : 2 ≤ n) : 2 ≤ term n := by
  by_cases hn2 : n = 2
  · subst n
    exact term_two.ge
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [recurrence]
      have hsub : ({0, 1} : Finset ℕ) ⊆ divisorIndices (m + 1) (term m) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simp [divisorIndices, term_zero]
        · simp [divisorIndices, term_one, show 1 < m + 1 by omega]
      have hc := Finset.card_le_card hsub
      simpa using hc

private theorem term_ge_three {n : ℕ} (hn : 3 ≤ n) : 3 ≤ term n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [recurrence]
  have hsub : ({0, 1, m} : Finset ℕ) ⊆ divisorIndices (m + 1) (term m) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp [divisorIndices, term_zero]
    · simp [divisorIndices, term_one, show 1 < m + 1 by omega]
    · simp [divisorIndices]
  have hc := Finset.card_le_card hsub
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simpa [hm0, hm1, Ne.symm hm0, Ne.symm hm1] using hc

private theorem term_eq_one_iff (n : ℕ) : term n = 1 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    by_contra! hn
    by_cases hn2 : n = 2
    · subst n
      rw [term_two] at h
      omega
    have := term_ge_three (n := n) (by omega)
    omega
  · rintro (rfl | rfl)
    · exact term_zero
    · exact term_one

def sourceTerm (n : ℕ) : ℕ := term (n - 1)

theorem source_specification : sourceTerm 1 = 1 ∧
    ∀ n : ℕ, 0 < n → sourceTerm (n + 1) =
      ((Finset.Icc 1 n).filter (fun i => sourceTerm i ∣ sourceTerm n)).card := by
  constructor
  · exact term_zero
  · intro n hn
    change term n = ((Finset.Icc 1 n).filter
      (fun i => term (i - 1) ∣ term (n - 1))).card
    exact source_recurrence n hn

def count (t d : ℕ) : ℕ :=
  ((Finset.range t).filter (fun i => term i = d)).card

private theorem count_mono {t u : ℕ} (htu : t ≤ u) (d : ℕ) : count t d ≤ count u d := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 htu, hi.2⟩

private theorem divisor_count_eq_sum (t v : ℕ) (hv : v ≠ 0) :
    (divisorIndices t v).card = ∑ d ∈ v.divisors, count t d := by
  symm
  rw [show (∑ d ∈ v.divisors, count t d) =
      ((Finset.range t).filter (fun i => term i ∈ v.divisors)).card from
    Finset.sum_card_fiberwise_eq_card_filter _ _ term]
  congr 1
  ext i
  simp [divisorIndices, Nat.mem_divisors, hv]

/-- The maximum-time step of the ordinary proof: any uniform sublinear prefix
multiplicity bound forces a bound independent of the prefix length. -/
private theorem maximum_bound_of_count_bound (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ N M : ℕ,
      (∀ i : ℕ, i ≤ N → term i ≤ M) →
      (∃ j : ℕ, j ≤ N ∧ term j = M) →
      (∀ d : ℕ, 0 < d → (count N d : ℝ) ≤ C * (M : ℝ) ^ (1 - δ)) →
      (M : ℝ) ≤ K := by
  obtain ⟨D, hD, hdiv⟩ :=
    D5.S3.Arith.Divisors.DivisorSubpower.card_divisors_subpower (δ / 2) (by linarith)
  refine ⟨max 1 ((C * D) ^ (δ / 2)⁻¹), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro N M hbound hattain hcount
  by_cases hM : M ≤ 1
  · exact le_trans (by exact_mod_cast hM) (le_max_left _ _)
  · obtain ⟨j, hjN, hjM⟩ := hattain
    have hj0 : j ≠ 0 := by
      intro hj
      subst j
      rw [term_zero] at hjM
      omega
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hiN : i ≤ N := by omega
    have hpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have hsum : (M : ℝ) ≤ C * (M : ℝ) ^ (1 - δ) *
        ((term i).divisors.card : ℝ) := by
      calc
        (M : ℝ) = ∑ d ∈ (term i).divisors, (count (i + 1) d : ℝ) := by
          rw [← Nat.cast_sum, ← divisor_count_eq_sum _ _ (term_pos i).ne',
            ← recurrence, hjM]
        (∑ d ∈ (term i).divisors, (count (i + 1) d : ℝ)) ≤
            ∑ _d ∈ (term i).divisors, C * (M : ℝ) ^ (1 - δ) := by
          apply Finset.sum_le_sum
          intro d hd
          exact le_trans (by exact_mod_cast count_mono hjN d)
            (hcount d (Nat.pos_of_mem_divisors hd))
        _ = _ := by simp; ring
    have hpow : (term i : ℝ) ^ (δ / 2) ≤ (M : ℝ) ^ (δ / 2) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hbound i hiN)
        (by linarith)
    have hmain : (M : ℝ) ≤ C * (M : ℝ) ^ (1 - δ) *
        (D * (M : ℝ) ^ (δ / 2)) :=
      hsum.trans (mul_le_mul_of_nonneg_left
        ((hdiv _ (term_pos i).ne').trans (mul_le_mul_of_nonneg_left hpow hD.le))
        (by positivity))
    have hcollapse : C * (M : ℝ) ^ (1 - δ) * (D * (M : ℝ) ^ (δ / 2)) =
        (C * D) * (M : ℝ) ^ (1 - δ / 2) := by
      rw [show (1 - δ / 2) = (1 - δ) + δ / 2 by ring,
        Real.rpow_add hpos]
      ring
    rw [hcollapse] at hmain
    have hcancel : (M : ℝ) ^ (δ / 2) ≤ C * D := by
      have hfactor : (M : ℝ) = (M : ℝ) ^ (δ / 2) *
          (M : ℝ) ^ (1 - δ / 2) := by
        rw [← Real.rpow_add hpos]
        simp
      have hmul : (M : ℝ) ^ (δ / 2) * (M : ℝ) ^ (1 - δ / 2) ≤
          (C * D) * (M : ℝ) ^ (1 - δ / 2) := hfactor.symm.trans_le hmain
      exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos _)).mp hmul
    apply le_trans _ (le_max_right _ _)
    exact (Real.le_rpow_inv_iff_of_pos hpos.le (mul_pos hC hD).le
      (by linarith : 0 < δ / 2)).mpr hcancel

def prefixMax (N : ℕ) : ℕ := (Finset.range (N + 1)).sup term

theorem no_uniform_sublinear_count_bound :
    ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ N d : ℕ, 0 < d →
      (count N d : ℝ) ≤ C * (prefixMax N : ℝ) ^ (1 - δ) := by
  rintro ⟨C, δ, hC, hδ, hcount⟩
  obtain ⟨K, hK, hmax⟩ := maximum_bound_of_count_bound C δ hC hδ
  obtain ⟨B, hB⟩ := exists_nat_gt K
  obtain ⟨n, hn⟩ := unbounded B
  have hbound (i : ℕ) (hi : i ≤ n) : term i ≤ prefixMax n :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup
    (Finset.range (n + 1)) (by simp) term
  have hMn : (prefixMax n : ℝ) ≤ K :=
    hmax n (prefixMax n) hbound
      ⟨j, by have := Finset.mem_range.mp hj; omega, heq.symm⟩ (hcount n)
  have hterm := hbound n le_rfl
  have htermR : (B : ℝ) < prefixMax n := by exact_mod_cast lt_of_lt_of_le hn hterm
  linarith

private theorem count_succ (t d : ℕ) :
    count (t + 1) d = count t d + if term t = d then 1 else 0 := by
  classical
  by_cases h : term t = d <;>
    simp [count, Finset.range_add_one, Finset.filter_insert, h,
      show t ∉ (Finset.range t).filter (fun i => term i = d) by simp]

private theorem count_one {t : ℕ} (ht : 2 ≤ t) : count t 1 = 2 := by
  have hfilter : (Finset.range t).filter (fun i => term i = 1) = {0, 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, term_eq_one_iff,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  simp [count, hfilter]

private theorem successor_of_three {n : ℕ} (hn : term n = 3) :
    term (n + 1) = 2 + count (n + 1) 3 := by
  have hn2 : 2 ≤ n + 1 := by
    by_contra! hh
    have : n = 0 := by omega
    subst n
    rw [term_zero] at hn
    omega
  rw [recurrence, hn, divisor_count_eq_sum _ _ (by decide)]
  norm_num [Nat.prime_three.divisors, count_one hn2]

/-- This is only the final implication in the full occurrence proof; the
infinitely-many-threes premise is not assumed by an unconditional result. -/
theorem full_occurrence_of_infinite_three
    (hthree : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ term n = 3) :
    ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ sourceTerm n = k := by
  have hunbounded : ∀ k : ℕ, ∃ t : ℕ, k ≤ count t 3 := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨n, htn, hn⟩ := hthree t
        refine ⟨n + 1, ?_⟩
        rw [count_succ, ite_eq_left hn]
        have := count_mono htn 3
        omega
  intro k hk
  by_cases hk1 : k = 1
  · subst k
    exact ⟨1, by decide, term_zero⟩
  by_cases hk2 : k = 2
  · subst k
    exact ⟨3, by decide, term_two⟩
  have hkp : 0 < k - 2 := by omega
  let t := Nat.find (hunbounded (k - 2))
  have ht : k - 2 ≤ count t 3 := Nat.find_spec (hunbounded (k - 2))
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp [count] at ht
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero ht0
  have hmin : count n 3 < k - 2 := by
    exact Nat.lt_of_not_ge (Nat.find_min (hunbounded (k - 2))
      (show n < t by omega))
  rw [hn, count_succ] at ht
  have hval : term n = 3 := by
    split_ifs at ht with h
    · exact h
    · omega
  have hcount : count (n + 1) 3 = k - 2 := by
    rw [ite_eq_left hval] at ht
    rw [count_succ, ite_eq_left hval]
    omega
  refine ⟨n + 2, by omega, ?_⟩
  change term (n + 1) = k
  rw [successor_of_three hval, hcount]
  omega

def seeds : Set ℕ := {i | 2 ≤ i ∧ ∀ j : ℕ, 2 ≤ j → j < i → ¬ term j ∣ term i}

private theorem seed_iff_successor_three {i : ℕ} (hi : 2 ≤ i) :
    i ∈ seeds ↔ term (i + 1) = 3 := by
  have hsub : ({0, 1, i} : Finset ℕ) ⊆ divisorIndices (i + 1) (term i) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · simp [divisorIndices, term_zero]
    · simp [divisorIndices, term_one, show 1 < i + 1 by omega]
    · simp [divisorIndices]
  have hc : ({0, 1, i} : Finset ℕ).card = 3 := by
    simp [show 0 ≠ i by omega, show 1 ≠ i by omega]
  constructor
  · intro hseed
    rw [recurrence]
    have heq : divisorIndices (i + 1) (term i) = {0, 1, i} := by
      apply Finset.Subset.antisymm _ hsub
      intro j hj
      simp only [divisorIndices, Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra! hne
      exact hseed.2 j (by omega) (by omega) hj.2
    rw [heq, hc]
  · intro hs
    refine ⟨hi, ?_⟩
    intro j hj hji hd
    have heq : ({0, 1, i} : Finset ℕ) = divisorIndices (i + 1) (term i) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [← recurrence, hs, hc])
    have hjmem : j ∈ divisorIndices (i + 1) (term i) := by
      simp [divisorIndices, show j < i + 1 by omega, hd]
    rw [← heq] at hjmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
    omega

private theorem finite_seeds_of_finite_three (hthree : Set.Finite {n : ℕ | term n = 3}) :
    seeds.Finite := by
  apply Set.Finite.of_injOn (f := fun i => i + 1) (t := {n : ℕ | term n = 3})
  · intro i hi
    exact (seed_iff_successor_three hi.1).mp hi
  · intro i hi j hj hij
    exact Nat.add_right_cancel hij
  · exact hthree

private theorem common_seed_divisor (n : ℕ) (hn : 2 ≤ n) :
    ∃ i : ℕ, i ∈ seeds ∧ term i ∣ term n := by
  have hex : ∃ i : ℕ, 2 ≤ i ∧ i ≤ n ∧ term i ∣ term n :=
    ⟨n, hn, le_rfl, dvd_rfl⟩
  let i := Nat.find hex
  have hi : 2 ≤ i ∧ i ≤ n ∧ term i ∣ term n := Nat.find_spec hex
  refine ⟨i, ⟨hi.1, ?_⟩, hi.2.2⟩
  intro j hj hji hd
  exact Nat.find_min hex hji ⟨hj, by omega, dvd_trans hd hi.2.2⟩

private theorem fixed_lcm_of_finite_three (hthree : Set.Finite {n : ℕ | term n = 3}) :
    ∃ q : ℕ, 2 ≤ q ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ d : ℕ, 2 ≤ d ∧ d ∣ q ∧ d ∣ term n := by
  classical
  have hs := finite_seeds_of_finite_three hthree
  let s := hs.toFinset
  let q := s.lcm term
  have hqpos : 0 < q := by
    apply Nat.pos_of_ne_zero
    rw [show q = s.lcm term from rfl, Finset.lcm_ne_zero_iff]
    intro i hi
    exact (term_pos i).ne'
  have htwoSeed : 2 ∈ seeds := by
    refine ⟨le_rfl, ?_⟩
    intro j hj hji
    omega
  have htwoDvd : 2 ∣ q := by
    have hh : term 2 ∣ q := Finset.dvd_lcm (by simpa [s] using htwoSeed)
    simpa only [term_two] using hh
  refine ⟨q, Nat.le_of_dvd hqpos htwoDvd, ?_⟩
  intro n hn
  obtain ⟨i, hi, hin⟩ := common_seed_divisor n hn
  exact ⟨term i, term_ge_two hi.1, Finset.dvd_lcm (by simpa [s] using hi), hin⟩

theorem missing_residue_of_finite_three
    (hthree : Set.Finite {n : ℕ | term n = 3}) :
    ∃ q : ℕ, 2 ≤ q ∧ ∀ n : ℕ, 1 < term n → term n % q ≠ 1 := by
  obtain ⟨q, hq, hcommon⟩ := fixed_lcm_of_finite_three hthree
  refine ⟨q, hq, ?_⟩
  intro n hn hmod
  have hn2 : 2 ≤ n := by
    by_contra! h
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · rw [term_zero] at hn
      omega
    · rw [term_one] at hn
      omega
  obtain ⟨d, hd, hdq, hdn⟩ := hcommon n hn2
  have hdm : d ∣ term n % q := Nat.dvd_mod_iff hdq |>.mpr hdn
  rw [hmod] at hdm
  have := Nat.le_of_dvd Nat.zero_lt_one hdm
  omega

/-- The prefix includes every successor of an index less than `t`. -/
def AvoidsResidue (q N : ℕ) : Prop :=
  ∀ i : ℕ, i ≤ N → 1 < term i → term i % q ≠ 1

private theorem divisor_card_succ (t v : ℕ) :
    (divisorIndices (t + 1) v).card = (divisorIndices t v).card +
      if term t ∣ v then 1 else 0 := by
  classical
  by_cases h : term t ∣ v <;>
    simp [divisorIndices, Finset.range_add_one, Finset.filter_insert, h,
      show t ∉ divisorIndices t v by simp [divisorIndices]]

/-- The ranks congruent to one must be proper-divisor contributors.  The
induction retains their spacing without constructing a sorted contributor list. -/
theorem contributor_rank_bound (q N t v : ℕ) (hq : 2 ≤ q)
    (havoid : AvoidsResidue q N) (ht : t ≤ N) (hv : 2 ≤ v) :
    (divisorIndices t v).card ≤ q * ∑ d ∈ v.properDivisors, count t d := by
  classical
  induction t with
  | zero => simp [divisorIndices, count]
  | succ t ih =>
    have htN : t ≤ N := by omega
    have hi := ih htN
    rw [divisor_card_succ]
    by_cases hd : term t ∣ v
    · rw [if_pos hd]
      by_cases he : term t = v
      · have hproper : ∑ d ∈ v.properDivisors, count (t + 1) d =
            ∑ d ∈ v.properDivisors, count t d := by
          apply Finset.sum_congr rfl
          intro d hmem
          rw [count_succ, if_neg]
          · omega
          · have := (Nat.mem_properDivisors.mp hmem).2
            omega
        rw [hproper]
        by_contra! hbad
        have hrank : (divisorIndices t v).card + 1 =
            q * ∑ d ∈ v.properDivisors, count t d + 1 := by omega
        have htpos : 0 < t := by
          by_contra! hz
          have : t = 0 := by omega
          subst t
          rw [term_zero] at he
          omega
        have hnonempty : 0 < (divisorIndices t v).card := by
          apply Finset.card_pos.mpr
          exact ⟨0, by simp [divisorIndices, htpos, term_zero]⟩
        have hs : term (t + 1) = (divisorIndices t v).card + 1 := by
          rw [recurrence, he, divisor_card_succ, he, if_pos (dvd_refl v)]
        have hmod := havoid (t + 1) ht (by omega)
        rw [hs, hrank] at hmod
        have : (q * ∑ d ∈ v.properDivisors, count t d + 1) % q = 1 := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < q by omega)]
        exact hmod this
      · have hp : term t ∈ v.properDivisors :=
          Nat.mem_properDivisors.mpr ⟨hd,
            lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) he⟩
        have hsum : (∑ d ∈ v.properDivisors, count t d) + 1 =
            ∑ d ∈ v.properDivisors, count (t + 1) d := by
          simp_rw [count_succ, Finset.sum_add_distrib]
          simp [hp]
        rw [← hsum, Nat.mul_add, Nat.mul_one]
        omega
    · rw [if_neg hd, Nat.add_zero]
      exact hi.trans (Nat.mul_le_mul_left q (Finset.sum_le_sum
        (fun d _ => count_mono (Nat.le_succ t) d)))

/- The fractional Dirichlet moment and the uniform missing-residue multiplicity
estimate are not established here. -/

end D5.S3.Arith.Recurrence.A124056Occurrence
