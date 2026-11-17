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
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.Basic
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
    simp [divisorIndices, Finset.range_add_one, Finset.filter_insert, h]

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
    · rw [ite_eq_left hd]
      by_cases he : term t = v
      · have hproper : ∑ d ∈ v.properDivisors, count (t + 1) d =
            ∑ d ∈ v.properDivisors, count t d := by
          apply Finset.sum_congr rfl
          intro d hmem
          rw [count_succ, ite_eq_right]
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
          rw [recurrence, he, divisor_card_succ, he, ite_eq_left (dvd_refl v)]
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
    · rw [ite_eq_right hd, Nat.add_zero]
      exact hi.trans (Nat.mul_le_mul_left q (Finset.sum_le_sum
        (fun d _ => count_mono (Nat.le_succ t) d)))

/-- Distinct prime words, including the empty word for one. -/
def primeWords (v : ℕ) : Finset (List ℕ) := v.primeFactorsList.permutations.toFinset

abbrev omega (v : ℕ) : ℕ := v.primeFactorsList.length

def primeWordCount (v : ℕ) : ℕ := (primeWords v).card

def primeWordWeight (A v : ℕ) : ℕ := A ^ omega v * primeWordCount v

private theorem mem_primeWords {v : ℕ} (hv : v ≠ 0) (w : List ℕ) :
    w ∈ primeWords v ↔ w.prod = v ∧ ∀ p ∈ w, Nat.Prime p := by
  simp only [primeWords, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.prod_eq.trans (Nat.prod_primeFactorsList hv),
      fun p hp => Nat.prime_of_mem_primeFactorsList (h.mem_iff.mp hp)⟩
  · rintro ⟨hp, hprime⟩
    exact Nat.primeFactorsList_unique hp hprime

private theorem primeWord_length {v : ℕ} {w : List ℕ} (hw : w ∈ primeWords v) :
    w.length = omega v := by
  exact (List.mem_permutations.mp (List.mem_toFinset.mp hw)).length_eq

private theorem primeWordCount_pos (v : ℕ) : 0 < primeWordCount v := by
  apply Finset.card_pos.mpr
  exact ⟨v.primeFactorsList, by simp [primeWords]⟩

/-- Splitting a prime word at a fixed position is a bijection with a pair of
words whose first product is a divisor of that factor-count rank. -/
theorem prime_word_split (v j : ℕ) (hv : 0 < v) (hj : j ≤ omega v) :
    (∑ d ∈ v.divisors.filter (fun d => omega d = j),
      primeWordCount d * primeWordCount (v / d)) = primeWordCount v := by
  classical
  let S := (v.divisors.filter (fun d => omega d = j)).sigma
    (fun d => (primeWords d) ×ˢ (primeWords (v / d)))
  have hcard : S.card = ∑ d ∈ v.divisors.filter (fun d => omega d = j),
      primeWordCount d * primeWordCount (v / d) := by
    simp [S, primeWordCount]
  rw [← hcard]
  apply Finset.card_bij (fun x _ => x.2.1 ++ x.2.2)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hd, hw⟩
    have hdv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hd0 := ne_zero_of_dvd_ne_zero hv.ne' hdv
    have hquot : v / x.1 ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd hv hdv) (Nat.pos_of_ne_zero hd0)).ne'
    have h1 := (mem_primeWords hd0 x.2.1).mp (Finset.mem_product.mp hw).1
    have h2 := (mem_primeWords hquot x.2.2).mp (Finset.mem_product.mp hw).2
    apply (mem_primeWords hv.ne' _).mpr
    refine ⟨by rw [List.prod_append, h1.1, h2.1, Nat.mul_div_cancel' hdv], ?_⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h1.2 p hp
    · exact h2.2 p hp
  · intro x hx y hy heq
    rcases Finset.mem_sigma.mp hx with ⟨hxd, hxw⟩
    rcases Finset.mem_sigma.mp hy with ⟨hyd, hyw⟩
    have hxl : x.2.1.length = j :=
      (primeWord_length (Finset.mem_product.mp hxw).1).trans (Finset.mem_filter.mp hxd).2
    have hyl : y.2.1.length = j :=
      (primeWord_length (Finset.mem_product.mp hyw).1).trans (Finset.mem_filter.mp hyd).2
    have hu : x.2.1 = y.2.1 := by
      have := congrArg (List.take j) heq
      simpa [hxl, hyl] using this
    have hw : x.2.2 = y.2.2 := by
      have := congrArg (List.drop j) heq
      simpa [hxl, hyl] using this
    have hxd0 := ne_zero_of_dvd_ne_zero hv.ne'
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hxd).1)
    have hyd0 := ne_zero_of_dvd_ne_zero hv.ne'
      (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hyd).1)
    have hd : x.1 = y.1 :=
      ((mem_primeWords hxd0 _).mp (Finset.mem_product.mp hxw).1).1.symm.trans
        ((congrArg List.prod hu).trans
          ((mem_primeWords hyd0 _).mp (Finset.mem_product.mp hyw).1).1)
    cases x with | mk xd xw =>
      cases y with | mk yd yw =>
        dsimp at hd hu hw
        subst yd
        exact congrArg (Sigma.mk xd) (Prod.ext hu hw)
  · intro w hw
    have hwp := (mem_primeWords hv.ne' w).mp hw
    let u := w.take j
    let z := w.drop j
    let d := u.prod
    have hdv : d ∣ v := ⟨z.prod, by
      simpa [d, u, z] using ((List.prod_take_mul_prod_drop w j).trans hwp.1).symm⟩
    have hd0 := ne_zero_of_dvd_ne_zero hv.ne' hdv
    have huprime : ∀ p ∈ u, Nat.Prime p :=
      fun p hp => hwp.2 p (List.mem_of_mem_take hp)
    have hzprime : ∀ p ∈ z, Nat.Prime p :=
      fun p hp => hwp.2 p (List.mem_of_mem_drop hp)
    have hu : u ∈ primeWords d := (mem_primeWords hd0 _).mpr ⟨rfl, huprime⟩
    have hul : omega d = j := by
      have hh := primeWord_length hu
      dsimp [u] at hh
      rw [List.length_take, primeWord_length hw, Nat.min_eq_left hj] at hh
      exact hh.symm
    have hzprod : z.prod = v / d := by
      apply (Nat.eq_div_iff_mul_eq_left hd0 hdv).mpr
      simpa [mul_comm, d, u, z] using
        ((List.prod_take_mul_prod_drop w j).trans hwp.1).symm
    have hz0 : v / d ≠ 0 := by
      exact (Nat.div_pos (Nat.le_of_dvd hv hdv) (Nat.pos_of_ne_zero hd0)).ne'
    refine ⟨⟨d, u, z⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv, hv.ne'⟩, hul⟩, ?_⟩
      exact Finset.mem_product.mpr ⟨hu, (mem_primeWords hz0 _).mpr ⟨hzprod, hzprime⟩⟩
    · exact List.take_append_drop j w

private theorem omega_lt_of_proper {v d : ℕ} (hv : v ≠ 0)
    (hd : d ∈ v.properDivisors) : omega d < omega v := by
  have hsub := Nat.primeFactorsList_sublist_of_dvd (Nat.mem_properDivisors.mp hd).1 hv
  apply lt_of_le_of_ne hsub.length_le
  intro heq
  have hlist := hsub.eq_of_length heq
  have hd0 := ne_zero_of_dvd_ne_zero hv (Nat.mem_properDivisors.mp hd).1
  have hdv : d = v := by
    rw [← Nat.prod_primeFactorsList hd0, hlist, Nat.prod_primeFactorsList hv]
  exact (Nat.mem_properDivisors.mp hd).2.ne hdv

private theorem prime_word_layer_bound (v j : ℕ) (hv : 0 < v) (hj : j < omega v) :
    (∑ d ∈ v.properDivisors.filter (fun d => omega d = j), primeWordCount d) ≤
      primeWordCount v := by
  calc
    _ ≤ ∑ d ∈ v.divisors.filter (fun d => omega d = j),
        primeWordCount d * primeWordCount (v / d) := by
      apply le_trans (Finset.sum_le_sum (fun d _ =>
        Nat.le_mul_of_pos_right _ (primeWordCount_pos (v / d))))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have h := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(Nat.mem_properDivisors.mp h.1).1, hv.ne'⟩, h.2⟩
      · intros; exact Nat.zero_le _
    _ = _ := prime_word_split v j hv hj.le

/-- The geometric layer sum absorbs every proper divisor with `A=q+1`. -/
theorem prime_word_weight_bound (q v : ℕ) (hv : 0 < v) :
    q * (∑ d ∈ v.properDivisors, primeWordWeight (q + 1) d) ≤
      primeWordWeight (q + 1) v := by
  classical
  have hlayers : (∑ d ∈ v.properDivisors, primeWordWeight (q + 1) d) =
      ∑ j ∈ Finset.range (omega v),
        (q + 1) ^ j *
          ∑ d ∈ v.properDivisors.filter (fun d => omega d = j), primeWordCount d := by
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    simp [omega_lt_of_proper hv.ne' hd, primeWordWeight]
  rw [hlayers]
  have hsum : (∑ j ∈ Finset.range (omega v),
      (q + 1) ^ j * ∑ d ∈ v.properDivisors.filter (fun d => omega d = j),
        primeWordCount d) ≤
      (∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (prime_word_layer_bound v j hv (Finset.mem_range.mp hj))
  have hgeom (k : ℕ) : q * (∑ j ∈ Finset.range k, (q + 1) ^ j) + 1 = (q + 1) ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, Nat.mul_add, pow_succ]; nlinarith
  calc
    _ ≤ q * ((∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v) :=
      Nat.mul_le_mul_left q hsum
    _ = (q * ∑ j ∈ Finset.range (omega v), (q + 1) ^ j) * primeWordCount v := by ring
    _ ≤ (q + 1) ^ omega v * primeWordCount v :=
      Nat.mul_le_mul_right _ (by have := hgeom (omega v); omega)
    _ = _ := rfl

private theorem count_le_divisor_card (t d : ℕ) : count t d ≤ (divisorIndices t d).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  simp [divisorIndices, hi.1, hi.2]

private theorem divisor_card_one (t : ℕ) : (divisorIndices t 1).card ≤ 2 := by
  apply le_trans (Finset.card_le_card (s := divisorIndices t 1) (t := {0, 1}) ?_)
  · simp
  · intro i hi
    have hd := (Finset.mem_filter.mp hi).2
    have he : term i = 1 := Nat.dvd_one.mp hd
    simpa using (term_eq_one_iff i).mp he

/-- A pointwise majorant for the actual recurrence under finite-prefix residue
avoidance.  The time range includes exactly the available successors. -/
theorem divisor_card_le_prime_word_weight (q N t v : ℕ) (hq : 2 ≤ q)
    (havoid : AvoidsResidue q N) (ht : t ≤ N) (hv : 0 < v) :
    (divisorIndices t v).card ≤ 2 * primeWordWeight (q + 1) v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    by_cases hv1 : v = 1
    · subst v
      have hw : primeWordWeight (q + 1) 1 = 1 := by
        simp [primeWordWeight, primeWordCount, primeWords, omega]
      rw [hw]
      simpa using divisor_card_one t
    have hv2 : 2 ≤ v := by omega
    calc
      _ ≤ q * ∑ d ∈ v.properDivisors, count t d :=
        contributor_rank_bound q N t v hq havoid ht hv2
      _ ≤ q * ∑ d ∈ v.properDivisors, 2 * primeWordWeight (q + 1) d := by
        apply Nat.mul_le_mul_left
        apply Finset.sum_le_sum
        intro d hd
        exact (count_le_divisor_card t d).trans
          (ih d (Nat.mem_properDivisors.mp hd).2
            (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hv.ne'
              (Nat.mem_properDivisors.mp hd).1)))
      _ = 2 * (q * ∑ d ∈ v.properDivisors, primeWordWeight (q + 1) d) := by
        rw [← Finset.mul_sum]; ring
      _ ≤ _ := Nat.mul_le_mul_left 2 (prime_word_weight_bound q v hv)

/-- Actual occurrences inject into distinct predecessor values in the indicated
prime-word level set.  Together with the pointwise count bound this is the
finite input to the subsequent moment and threshold estimates. -/
theorem count_le_prime_word_bounds (q N t d : ℕ) (hq : 2 ≤ q)
    (havoid : AvoidsResidue q N) (ht : t ≤ N) (hd : 2 ≤ d) :
    count t d ≤ 2 * primeWordWeight (q + 1) d ∧
    count t d ≤ ((Finset.range (prefixMax N + 1)).filter
      (fun v => 0 < v ∧ d ≤ 2 * primeWordWeight (q + 1) v)).card := by
  classical
  refine ⟨(count_le_divisor_card t d).trans
    (divisor_card_le_prime_word_weight q N t d hq havoid ht (by omega)), ?_⟩
  apply Finset.card_le_card_of_injOn (fun i => term (i - 1))
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hit : i < t := Finset.mem_range.mp hi'.1
    have hi0 : i ≠ 0 := by
      intro hz
      subst i
      rw [term_zero] at hi'
      omega
    have hieq : i - 1 + 1 = i := by omega
    have hrec : d = (divisorIndices i (term (i - 1))).card := by
      have hh := recurrence (i - 1)
      rw [hieq, hi'.2] at hh
      exact hh
    have hb : term (i - 1) ≤ prefixMax N :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hb), term_pos _, ?_⟩
    rw [hrec]
    exact divisor_card_le_prime_word_weight q N i (term (i - 1))
      hq havoid (by omega) (term_pos _)
  · intro i hi j hj hij
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    have hi0 : i ≠ 0 := by
      intro hz
      subst i
      rw [term_zero] at hi'
      omega
    have hj0 : j ≠ 0 := by
      intro hz
      subst j
      rw [term_zero] at hj'
      omega
    have hp : (term (i - 1), term (i - 1 + 1)) =
        (term (j - 1), term (j - 1 + 1)) := by
      apply Prod.ext hij
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i),
        Nat.sub_add_cancel (by omega : 1 ≤ j), hi'.2, hj'.2]
    have := pair_injective hp
    omega

private theorem omega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    omega (m * n) = omega m + omega n := by
  exact (Nat.perm_primeFactorsList_mul hm hn).length_eq.trans (List.length_append ..)

private theorem omega_eq_one_iff_prime {n : ℕ} (hn : n ≠ 0) :
    omega n = 1 ↔ Nat.Prime n := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
    have hprod := Nat.prod_primeFactorsList hn
    rw [hp] at hprod
    simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
    have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactorsList (n := n) (by rw [hp]; simp)
    exact hprod ▸ hprime
  · intro h
    simp [omega, Nat.primeFactorsList_prime h]

/-- Removing the first prime gives the exact weighted first-letter recurrence. -/
theorem prime_word_first_letter (A v : ℕ) (hv : 1 < v) :
    primeWordWeight A v =
      A * ∑ p ∈ v.primeFactors, primeWordWeight A (v / p) := by
  classical
  have hv0 : v ≠ 0 := by omega
  have hk : 1 ≤ omega v := by
    have := (Nat.primeFactorsList_ne_nil v).mpr hv
    exact List.length_pos_iff.mpr this
  have hset : v.divisors.filter (fun d => omega d = 1) = v.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hd, _⟩, hl⟩
      exact ⟨(omega_eq_one_iff_prime (ne_zero_of_dvd_ne_zero hv0 hd)).mp hl, hd, hv0⟩
    · rintro ⟨hp, hd, _⟩
      exact ⟨⟨hd, hv0⟩, (omega_eq_one_iff_prime hp.ne_zero).mpr hp⟩
  have hsplit := prime_word_split v 1 (by omega) hk
  rw [hset] at hsplit
  have hcount : primeWordCount v = ∑ p ∈ v.primeFactors, primeWordCount (v / p) := by
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    simp [primeWordCount, primeWords, Nat.primeFactorsList_prime hprime, List.permutations]
  unfold primeWordWeight
  rw [hcount, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hquot : v / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hprime.pos).ne'
  have heq : omega v = omega (v / p) + 1 := by
    have h := omega_mul hprime.ne_zero hquot
    rw [Nat.mul_div_cancel' hd] at h
    simpa [omega, Nat.primeFactorsList_prime hprime, Nat.add_comm] using h
  rw [heq, pow_succ]
  ring

/-- A finite prime-sum hypothesis controls every actual prime-word weight. -/
theorem prime_word_pointwise (C : ℕ) (r : ℝ)
    (hprime : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-r) ≤ 1) :
    ∀ v : ℕ, 0 < v → (primeWordWeight C v : ℝ) ≤ (v : ℝ) ^ r := by
  intro v
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro hv
    by_cases hv1 : v = 1
    · subst v
      simp [primeWordWeight, primeWordCount, primeWords, omega]
    have hv2 : 1 < v := by omega
    rw [prime_word_first_letter C v hv2, Nat.cast_mul, Nat.cast_sum]
    calc
      _ ≤ (C : ℝ) * ∑ p ∈ v.primeFactors, ((v / p : ℕ) : ℝ) ^ r := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg C)
        apply Finset.sum_le_sum
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        exact ih _ (Nat.div_lt_self hv hprime.one_lt)
          (Nat.div_pos (Nat.le_of_dvd hv hd) hprime.pos)
      _ = (v : ℝ) ^ r * ((C : ℝ) * ∑ p ∈ v.primeFactors, (p : ℝ) ^ (-r)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        rw [Nat.cast_div hd (by exact_mod_cast hprime.ne_zero : (p : ℝ) ≠ 0), Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          Real.rpow_neg (Nat.cast_nonneg _)]
        ring
      _ ≤ _ := by
        simpa using mul_le_mul_of_nonneg_left
          (hprime v.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp))
          (Real.rpow_nonneg (Nat.cast_nonneg v) r)

private theorem prime_sum_parameter (C : ℕ) :
    ∃ r : ℝ, 1 < r ∧ ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-r) ≤ 1 := by
  classical
  let Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 1 / ((C : ℝ) * Z + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(k : ℝ) + 2, by have := Nat.cast_nonneg (α := ℝ) k; linarith, ?_⟩
  intro T hT
  have hp (p : ℕ) (hp : p ∈ T) :
      (p : ℝ) ^ (-((k : ℝ) + 2)) ≤ (1 / 2 : ℝ) ^ k * (p : ℝ) ^ (-2 : ℝ) := by
    have hpp : (2 : ℝ) ≤ p := by exact_mod_cast (hT p hp).two_le
    have hp0 : (0 : ℝ) < p := by positivity
    rw [show -((k : ℝ) + 2) = -(k : ℝ) + (-2) by ring, Real.rpow_add hp0,
      Real.rpow_neg hp0.le, Real.rpow_natCast, ← inv_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num) hpp)) k)
      (Real.rpow_nonneg hp0.le _)
  have hsum : ∑ p ∈ T, (p : ℝ) ^ (-((k : ℝ) + 2)) ≤ (1 / 2 : ℝ) ^ k * Z := by
    calc
      _ ≤ ∑ p ∈ T, (1 / 2 : ℝ) ^ k * (p : ℝ) ^ (-2 : ℝ) := Finset.sum_le_sum hp
      _ = (1 / 2 : ℝ) ^ k * ∑ p ∈ T, (p : ℝ) ^ (-2 : ℝ) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hs.sum_le_tsum T (fun n _ => by positivity)) (by positivity)
  have hk' : (1 / 2 : ℝ) ^ k * ((C : ℝ) * Z + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hk
  have hk0 : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
  have hC : (C : ℝ) * (∑ p ∈ T, (p : ℝ) ^ (-((k : ℝ) + 2))) ≤
      (C : ℝ) * ((1 / 2 : ℝ) ^ k * Z) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg C)
  nlinarith

/-- The exponent is chosen using only the weight parameter, uniformly in v. -/
theorem prime_word_polynomial_bound (A : ℕ) :
    ∃ r : ℝ, 1 < r ∧ ∀ v : ℕ, 0 < v →
      (primeWordWeight (2 * A) v : ℝ) ≤ (v : ℝ) ^ r := by
  obtain ⟨r, hr, hp⟩ := prime_sum_parameter (2 * A)
  exact ⟨r, hr, prime_word_pointwise (2 * A) r hp⟩

def roughPrefix (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n => 0 < n ∧ ∀ p ∈ n.primeFactors, p ∉ S)

/-- The weighted rough first moment is bounded by absorption of a finite
first-letter sum; no infinite rearrangement is used. -/
theorem rough_prime_word_sum (C : ℕ) (σ : ℝ) (S : Finset ℕ)
    (htail : ∀ T : Finset ℕ, (∀ p ∈ T, Nat.Prime p) → Disjoint T S →
      (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ) ≤ 1 / 2) (X : ℕ) :
    (∑ n ∈ roughPrefix S X, (primeWordWeight C n : ℝ) * (n : ℝ) ^ (-σ)) ≤ 2 := by
  classical
  let G := roughPrefix S X
  let T := (Finset.range (X + 1)).filter (fun p => Nat.Prime p ∧ p ∉ S)
  let f : ℕ → ℝ := fun n => (primeWordWeight C n : ℝ) * (n : ℝ) ^ (-σ)
  let R : ℝ := ∑ n ∈ G, f n
  have hf (n : ℕ) : 0 ≤ f n := by dsimp [f]; positivity
  have hG {n : ℕ} (hn : n ∈ G) :
      n ≤ X ∧ 0 < n ∧ ∀ p ∈ n.primeFactors, p ∉ S := by
    have h := Finset.mem_filter.mp hn
    exact ⟨by have := Finset.mem_range.mp h.1; omega, h.2⟩
  have hpG {n p : ℕ} (hn : n ∈ G) (hp : p ∈ n.primeFactors) : p ∈ T ∧ n / p ∈ G := by
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hn' := hG hn
    have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn'.2.1 hd) hprime.pos
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by have := Nat.le_of_dvd hn'.2.1 hd; omega), hprime, hn'.2.2 p hp⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by have := Nat.div_le_self n p; omega), hquot, ?_⟩
      intro l hl
      apply hn'.2.2 l
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hl,
        dvd_trans (Nat.dvd_of_mem_primeFactors hl) (Nat.div_dvd_of_dvd hd), hn'.2.1.ne'⟩
  have hrec (n : ℕ) (hn : n ∈ G.erase 1) :
      f n = ∑ p ∈ n.primeFactors, (C : ℝ) * (p : ℝ) ^ (-σ) * f (n / p) := by
    have hn' := Finset.mem_erase.mp hn
    have hnpos := (hG hn'.2).2.1
    dsimp [f]
    rw [prime_word_first_letter C n (by omega), Nat.cast_mul, Nat.cast_sum,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have heq : (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hd).symm
    rw [heq, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  let pairs := (G.erase 1).sigma (fun n => n.primeFactors)
  have hpair : (∑ n ∈ G.erase 1, f n) ≤
      ∑ z ∈ T ×ˢ G, (C : ℝ) * (z.1 : ℝ) ^ (-σ) * f z.2 := by
    calc
      _ = ∑ n ∈ G.erase 1, ∑ p ∈ n.primeFactors,
          (C : ℝ) * (p : ℝ) ^ (-σ) * f (n / p) :=
        Finset.sum_congr rfl hrec
      _ ≤ _ := by
        rw [Finset.sum_sigma']
        apply Finset.sum_le_sum_of_injOn (fun x : Sigma (fun _ : ℕ => ℕ) => (x.2, x.1 / x.2))
        · intro x hx y hy heq
          have hxp := (Finset.mem_sigma.mp hx).2
          have hyp := (Finset.mem_sigma.mp hy).2
          have hp : x.2 = y.2 := congrArg Prod.fst heq
          have hq : x.1 / x.2 = y.1 / y.2 := congrArg Prod.snd heq
          have hn : x.1 = y.1 := by
            calc
              x.1 = x.2 * (x.1 / x.2) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hxp)).symm
              _ = y.2 * (y.1 / y.2) := by rw [hq, hp]
              _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hyp)
          exact Sigma.ext hn (by simpa using hp)
        · intro z hz
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
          have h := Finset.mem_sigma.mp hx
          exact Finset.mem_product.mpr (hpG (Finset.mem_erase.mp h.1).2 h.2)
        · intro x hx
          rfl
        · intro z hz _
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hf _)
  have hproduct : (∑ z ∈ T ×ˢ G, (C : ℝ) * (z.1 : ℝ) ^ (-σ) * f z.2) =
      ((C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ)) * R := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have ht : (C : ℝ) * ∑ p ∈ T, (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
    apply htail T
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    · apply Finset.disjoint_left.mpr
      intro p hp hs
      exact (Finset.mem_filter.mp hp).2.2 hs
  have hsplit : R ≤ 1 + ∑ n ∈ G.erase 1, f n := by
    by_cases h1 : 1 ∈ G
    · have h := Finset.sum_erase_add G f h1
      have hf1 : f 1 = 1 := by simp [f, primeWordWeight, primeWordCount, primeWords, omega]
      dsimp [R]
      rw [← h, hf1]
      linarith
    · simp [R, Finset.erase_eq_of_notMem h1]
  have hR : 0 ≤ R := Finset.sum_nonneg (fun n _ => hf n)
  rw [hproduct] at hpair
  have := mul_le_mul_of_nonneg_right ht hR
  change R ≤ 2
  linarith

private theorem prime_word_weight_mono (A B v : ℕ) (hAB : A ≤ B) :
    primeWordWeight A v ≤ primeWordWeight B v := by
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hAB)

/-- The doubled weight controls splitting a product into any two positive
factors, without a multiplicativity assumption. -/
theorem prime_word_product_bound (A m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    primeWordWeight A (m * n) ≤
      primeWordWeight (2 * A) m * primeWordWeight (2 * A) n := by
  classical
  have main : ∀ k m n : ℕ, m + n = k → 0 < m → 0 < n →
      primeWordWeight A (m * n) ≤
        primeWordWeight (2 * A) m * primeWordWeight (2 * A) n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hsum hm hn
      by_cases hm1 : m = 1
      · subst m
        simpa [primeWordWeight, primeWordCount, primeWords, omega] using
          prime_word_weight_mono A (2 * A) n (by omega)
      by_cases hn1 : n = 1
      · subst n
        simpa [primeWordWeight, primeWordCount, primeWords, omega] using
          prime_word_weight_mono A (2 * A) m (by omega)
      have hm2 : 1 < m := by omega
      have hn2 : 1 < n := by omega
      let f : ℕ → ℕ := fun p => primeWordWeight A (m * n / p)
      have hunion : (∑ p ∈ m.primeFactors ∪ n.primeFactors, f p) ≤
          (∑ p ∈ m.primeFactors, f p) + ∑ p ∈ n.primeFactors, f p := by
        have := Finset.sum_union_inter m.primeFactors n.primeFactors f
        omega
      have hleft : (∑ p ∈ m.primeFactors, f p) ≤
          ∑ p ∈ m.primeFactors, primeWordWeight (2 * A) (m / p) * primeWordWeight (2 * A) n := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hquot : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hd) hprime.pos
        have hlt := Nat.div_lt_self hm hprime.one_lt
        dsimp [f]
        rw [show m * n / p = (m / p) * n by
          simpa [mul_comm] using Nat.mul_div_assoc n hd]
        exact ih (m / p + n) (by omega) (m / p) n rfl hquot hn
      have hright : (∑ p ∈ n.primeFactors, f p) ≤
          ∑ p ∈ n.primeFactors, primeWordWeight (2 * A) m * primeWordWeight (2 * A) (n / p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hd := Nat.dvd_of_mem_primeFactors hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hprime.pos
        have hlt := Nat.div_lt_self hn hprime.one_lt
        dsimp [f]
        rw [Nat.mul_div_assoc m hd]
        exact ih (m + n / p) (by omega) m (n / p) rfl hm hquot
      calc
        _ = A * ∑ p ∈ m.primeFactors ∪ n.primeFactors, f p := by
          rw [prime_word_first_letter A (m * n) (by nlinarith), Nat.primeFactors_mul hm.ne' hn.ne']
        _ ≤ A * ((∑ p ∈ m.primeFactors, f p) + ∑ p ∈ n.primeFactors, f p) :=
          Nat.mul_le_mul_left A hunion
        _ ≤ A * ((∑ p ∈ m.primeFactors, primeWordWeight (2 * A) (m / p) *
            primeWordWeight (2 * A) n) + ∑ p ∈ n.primeFactors,
            primeWordWeight (2 * A) m * primeWordWeight (2 * A) (n / p)) :=
          Nat.mul_le_mul_left A (Nat.add_le_add hleft hright)
        _ = _ := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          rw [prime_word_first_letter (2 * A) m hm2, prime_word_first_letter (2 * A) n hn2]
          ring
  exact main (m + n) m n rfl hm hn

/- The fixed fractional moment and uniform multiplicity estimate remain open. -/

end D5.S3.Arith.Recurrence.A124056Occurrence
