/- GID: D5/S3/Arith/Additive/PlasticTailStability
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticTailStability
   mirror-E: none(waiver:integer-template-tail-stability)
   anchors: []
   utility: none
   digest: Right-endpoint defects control gaps and long consecutive tails. -/

import D5.S3.Arith.Additive.PlasticExtremal

/-! Defect accounting and actual consecutive intervals in arbitrary signed exponent sets. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticTailStability
open Finset
open PlasticExtremal

def completed (E : Finset ℤ) (t : ℤ) : ℕ :=
  (if t-1 ∈ E ∧ t-2 ∈ E ∧ t-4 ∈ E then 1 else 0) +
  (if t-1 ∈ E ∧ t-3 ∈ E ∧ t-6 ∈ E then 1 else 0) +
  (if t-2 ∈ E ∧ t-7 ∈ E then 1 else 0) +
  (if t-1 ∈ E ∧ t-4 ∈ E ∧ t-9 ∈ E then 1 else 0)

private theorem completed_le (E : Finset ℤ) (t : ℤ) : completed E t ≤ 4 := by
  unfold completed
  split_ifs <;> omega

private theorem count_sum (E : Finset ℤ) : count E = ∑ t ∈ E, completed E t := by
  classical
  change (E.filter (fun t => ∀ a ∈ ({1,2,4}:Finset ℤ), t-a ∈ E)).card +
    (E.filter (fun t => ∀ a ∈ ({1,3,6}:Finset ℤ), t-a ∈ E)).card +
    (E.filter (fun t => ∀ a ∈ ({2,7}:Finset ℤ), t-a ∈ E)).card +
    (E.filter (fun t => ∀ a ∈ ({1,4,9}:Finset ℤ), t-a ∈ E)).card = _
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Finset.card_eq_sum_ones, Finset.sum_filter, completed, Finset.sum_add_distrib]

def prefixSet (x : ℕ → ℤ) (k : ℕ) : Finset ℤ := (Finset.range k).image x

private theorem prefix_card (x : ℕ → ℤ) (n k : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hk : k ≤ n) : (prefixSet x k).card = k := by
  rw [prefixSet,Finset.card_image_of_injOn]
  · exact Finset.card_range k
  · intro i hi j hj hij
    exact hx.injOn (by simpa using lt_of_lt_of_le (Finset.mem_range.1 hi) hk)
      (by simpa using lt_of_lt_of_le (Finset.mem_range.1 hj) hk) hij

private theorem predecessor_mem (x : ℕ → ℤ) (n k i : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hk : k ≤ n) (hi : i < k)
    (d : ℤ) (hd : 0 < d) : x i-d ∈ prefixSet x k ↔ x i-d ∈ prefixSet x i := by
  constructor
  · rintro h
    obtain ⟨j,hj,hj'⟩ := Finset.mem_image.1 h
    apply Finset.mem_image.2
    refine ⟨j,Finset.mem_range.2 ?_,hj'⟩
    have hji : x j < x i := by omega
    by_contra hn
    have hie : i ≤ j := by omega
    have hmono := hx.monotoneOn (show i ∈ Set.Iio n by simpa using lt_of_lt_of_le hi hk)
      (show j ∈ Set.Iio n by simpa using lt_of_lt_of_le (Finset.mem_range.1 hj) hk) hie
    omega
  · intro h
    exact Finset.image_subset_image (f := x) (Finset.range_mono (by omega)) h

private theorem completed_prefix (x : ℕ → ℤ) (n k i : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hk : k ≤ n) (hi : i < k) :
    completed (prefixSet x k) (x i) = completed (prefixSet x i) (x i) := by
  unfold completed
  simp only [predecessor_mem x n k i hx hk hi 1 (by omega),
      predecessor_mem x n k i hx hk hi 2 (by omega),
      predecessor_mem x n k i hx hk hi 3 (by omega),
      predecessor_mem x n k i hx hk hi 4 (by omega),
      predecessor_mem x n k i hx hk hi 6 (by omega),
      predecessor_mem x n k i hx hk hi 7 (by omega),
      predecessor_mem x n k i hx hk hi 9 (by omega)]

private theorem count_prefix (x : ℕ → ℤ) (n k : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hk : k ≤ n) :
    count (prefixSet x k) = ∑ i ∈ Finset.range k, completed (prefixSet x i) (x i) := by
  rw [count_sum]
  unfold prefixSet
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    exact completed_prefix x n k i hx hk (Finset.mem_range.1 hi)
  · intro i hi j hj hij
    exact hx.injOn (by simpa using lt_of_lt_of_le (Finset.mem_range.1 hi) hk)
      (by simpa using lt_of_lt_of_le (Finset.mem_range.1 hj) hk) hij

private theorem gap_missing (x : ℕ → ℤ) (n i : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hi : i < n) (hpos : 0 < i)
    (d : ℤ) (hd : d < x i - x (i - 1)) : x i-d ∉ prefixSet x i := by
  rintro h
  obtain ⟨j,hj,hj'⟩ := Finset.mem_image.1 h
  have hjle : j ≤ i-1 := by have := Finset.mem_range.1 hj; omega
  have hmono := hx.monotoneOn (show j ∈ Set.Iio n by have := Finset.mem_range.1 hj; simp; omega)
    (show i-1 ∈ Set.Iio n by simp; omega) hjle
  omega

private theorem gap_defect (x : ℕ → ℤ) (n i : ℕ)
    (hx : StrictMonoOn x (Set.Iio n)) (hi : i < n) (hpos : 0 < i) :
    (if x i-x (i-1)=2 then 3 else 0) + (if 3 ≤ x i-x (i-1) then 4 else 0)
      ≤ 4-completed (prefixSet x i) (x i) := by
  by_cases h2 : x i-x (i-1)=2
  · have h1 := gap_missing x n i hx hi hpos 1 (by omega)
    simp only [h2, ite_true, show ¬ (3:ℤ) ≤ 2 by omega, ite_false, add_zero]
    unfold completed
    simp only [h1,false_and,ite_false,zero_add,add_zero]
    split_ifs <;> omega
  · by_cases h3 : 3 ≤ x i-x (i-1)
    · have h1 := gap_missing x n i hx hi hpos 1 (by omega)
      have h2' := gap_missing x n i hx hi hpos 2 (by omega)
      simp only [h2,ite_false,h3,ite_true,zero_add]
      unfold completed
      simp [h1,h2']
    · simp [h2,h3]

private theorem defect_accounting (x : ℕ → ℤ) (n : ℕ)
    (hn : 10 ≤ n) (hx : StrictMonoOn x (Set.Iio n)) :
    let c := fun i => completed (prefixSet x i) (x i)
    let δ := 4*n-26-count (prefixSet x n)
    count (prefixSet x n) ≤ 4*n-26 ∧
    δ = 14-count (prefixSet x 10) + ∑ i ∈ Finset.Ico 10 n, (4-c i) ∧
    ((Finset.Ico 10 n).filter (fun i => c i < 4)).card ≤ δ ∧
    3*((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)).card +
    4*((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))).card ≤ δ := by
  classical
  let c := fun i => completed (prefixSet x i) (x i)
  let δ := 4*n-26-count (prefixSet x n)
  have hbound := count_bound (prefixSet x n) (by rw [prefix_card x n n hx le_rfl]; exact hn)
  rw [prefix_card x n n hx le_rfl] at hbound
  have hten := count_bound (prefixSet x 10) (by rw [prefix_card x n 10 hx hn])
  rw [prefix_card x n 10 hx hn] at hten
  have hsplit : count (prefixSet x 10) + ∑ i ∈ Finset.Ico 10 n, c i = count (prefixSet x n) := by
    rw [count_prefix x n 10 hx hn,count_prefix x n n hx le_rfl]
    exact Finset.sum_range_add_sum_Ico c hn
  have hbalance : (∑ i ∈ Finset.Ico 10 n, c i) + (∑ i ∈ Finset.Ico 10 n, (4-c i)) = 4*(n-10) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i ∈ Finset.Ico 10 n, (4:ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have := completed_le (prefixSet x i) (x i)
        dsimp [c]; omega
      _ = _ := by simp [Nat.mul_comm]
  have hident : δ = 14-count (prefixSet x 10) + ∑ i ∈ Finset.Ico 10 n, (4-c i) := by
    dsimp [δ]; omega
  have hbad : ((Finset.Ico 10 n).filter (fun i => c i < 4)).card ≤
      ∑ i ∈ Finset.Ico 10 n, (4-c i) := by
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i hi
    have := completed_le (prefixSet x i) (x i)
    dsimp [c] at *
    split_ifs <;> omega
  have hw := Finset.sum_le_sum (s:=Finset.Ico 10 n) (fun i hi =>
    gap_defect x n i hx (Finset.mem_Ico.1 hi).2 (by have := (Finset.mem_Ico.1 hi).1; omega))
  have hw' : 3*((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)).card +
      4*((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))).card ≤
      ∑ i ∈ Finset.Ico 10 n, (4-c i) := by
    simpa only [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,
      smul_eq_mul,Nat.mul_comm] using hw
  dsimp only [c,δ] at hident hbad hw' ⊢
  exact ⟨by omega,hident,by omega,by omega⟩

private theorem tail_eq_image (x : ℕ → ℤ) (n : ℕ)
    (hn : 10 ≤ n) (hx : StrictMonoOn x (Set.Iio n)) :
    prefixSet x n \ prefixSet x 10 = (Finset.Ico 10 n).image x := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 ht).1
    exact Finset.mem_image.2 ⟨i,Finset.mem_Ico.2 ⟨by
      by_contra h
      exact (Finset.mem_sdiff.1 ht).2 (Finset.mem_image.2 ⟨i,Finset.mem_range.2 (by omega),rfl⟩),
      Finset.mem_range.1 hi⟩,rfl⟩
  · rintro ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 ht
    refine Finset.mem_sdiff.2
      ⟨Finset.mem_image.2 ⟨i,Finset.mem_range.2 (Finset.mem_Ico.1 hi).2,rfl⟩, ?_⟩
    rintro hp
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.1 hp
    have := hx.injOn (by have := Finset.mem_range.1 hj; simp; omega)
      (show i ∈ Set.Iio n by exact (Finset.mem_Ico.1 hi).2) hji
    have := Finset.mem_range.1 hj
    have := (Finset.mem_Ico.1 hi).1
    omega

private theorem tail_starts_bound (x : ℕ → ℤ) (n : ℕ)
    (hn : 10 ≤ n) (hx : StrictMonoOn x (Set.Iio n)) :
    let T := prefixSet x n \ prefixSet x 10
    (T.filter (fun t => t-1 ∉ T)).card ≤
      1 + ((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)).card +
      ((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))).card := by
  classical
  let T := prefixSet x n \ prefixSet x 10
  let B := (Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2 ∨ 3 ≤ x i-x (i-1))
  have hT : T = (Finset.Ico 10 n).image x := tail_eq_image x n hn hx
  have hsub : T.filter (fun t => t-1 ∉ T) ⊆ insert (x 10) (B.image x) := by
    intro t ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 (hT ▸ (Finset.mem_filter.1 ht).1)
    by_cases he : i=10
    · subst i; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.2
      refine ⟨i,Finset.mem_filter.2 ⟨hi,?_⟩,rfl⟩
      have hip : 10 ≤ i-1 := by have := (Finset.mem_Ico.1 hi).1; omega
      have hin := (Finset.mem_Ico.1 hi).2
      have hlt := hx (show i-1 ∈ Set.Iio n by simp; omega)
        (show i ∈ Set.Iio n from hin) (by omega : i - 1 < i)
      have hne : x i-x (i-1) ≠ 1 := by
        intro hgap
        have hprev : x i-1 ∈ T := by
          rw [hT]
          exact Finset.mem_image.2 ⟨i-1,Finset.mem_Ico.2 ⟨hip,by omega⟩,by omega⟩
        exact (Finset.mem_filter.1 ht).2 hprev
      omega
  have hB : B = ((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)) ∪
      ((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))) := by
    ext i
    simp only [B,Finset.mem_filter,Finset.mem_union]
    tauto
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have himage : (B.image x).card ≤ B.card := Finset.card_image_le
  have hb := Finset.card_union_le
    ((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2))
    ((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1)))
  rw [← hB] at hb
  dsimp only [T] at hcard ⊢
  omega

private theorem small_defect_steps (x : ℕ → ℤ) (n : ℕ)
    (hn : 10 ≤ n) (hx : StrictMonoOn x (Set.Iio n))
    (hsmall : 4 * n - 26 - count (prefixSet x n) ≤ 2) :
    ∀ i ∈ Finset.Ico 10 n, x i-x (i-1)=1 := by
  have hw := (defect_accounting x n hn hx).2.2.2
  intro i hi
  have hin := (Finset.mem_Ico.1 hi).2
  have hlow := (Finset.mem_Ico.1 hi).1
  have hlt := hx (show i-1 ∈ Set.Iio n by simp; omega)
    (show i ∈ Set.Iio n from hin) (by omega : i - 1 < i)
  have hne2 : x i-x (i-1) ≠ 2 := by
    intro he
    have hc : 0 < ((Finset.Ico 10 n).filter (fun j => x j-x (j-1)=2)).card :=
      Finset.card_pos.2 ⟨i,Finset.mem_filter.2 ⟨hi,he⟩⟩
    omega
  have hng3 : ¬ 3 ≤ x i-x (i-1) := by
    intro he
    have hc : 0 < ((Finset.Ico 10 n).filter (fun j => 3 ≤ x j-x (j-1))).card :=
      Finset.card_pos.2 ⟨i,Finset.mem_filter.2 ⟨hi,he⟩⟩
    omega
  omega


private noncomputable def integerRun (T : Finset ℤ) (s : ℤ) : Finset ℤ := by
  classical
  exact T.filter (fun t => s ≤ t ∧ Finset.Icc s t ⊆ T)

private theorem mem_integerRun_self (T : Finset ℤ) (s : ℤ) (hs : s ∈ T) :
    s ∈ integerRun T s := by
  classical
  apply Finset.mem_filter.2
  refine ⟨hs, le_rfl, ?_⟩
  intro t ht
  have ht := Finset.mem_Icc.1 ht
  have : t = s := by omega
  simpa [this] using hs

private theorem integerRun_interval (T : Finset ℤ) (s : ℤ) (hs : s ∈ T) :
    ∃ b : ℤ, s ≤ b ∧ integerRun T s = Finset.Icc s b := by
  classical
  have hn : (integerRun T s).Nonempty := ⟨s, mem_integerRun_self T s hs⟩
  let b := (integerRun T s).max' hn
  have hb : b ∈ integerRun T s := Finset.max'_mem _ hn
  have hbp := (Finset.mem_filter.1 hb).2
  refine ⟨b, hbp.1, ?_⟩
  ext t
  constructor
  · intro ht
    exact Finset.mem_Icc.2 ⟨(Finset.mem_filter.1 ht).2.1,
      Finset.le_max' _ t ht⟩
  · intro ht
    have ht' := Finset.mem_Icc.1 ht
    apply Finset.mem_filter.2
    refine ⟨hbp.2 ht, ht'.1, ?_⟩
    intro u hu
    have hu' := Finset.mem_Icc.1 hu
    apply hbp.2
    exact Finset.mem_Icc.2 ⟨hu'.1, le_trans hu'.2 ht'.2⟩

private theorem integerRun_cover (T : Finset ℤ) (t : ℤ) (ht : t ∈ T) :
    ∃ s ∈ T.filter (fun s => s-1 ∉ T), t ∈ integerRun T s := by
  classical
  let Q := T.filter (fun s => s ≤ t ∧ Finset.Icc s t ⊆ T)
  have hqt : t ∈ Q := by
    apply Finset.mem_filter.2
    refine ⟨ht, le_rfl, ?_⟩
    intro u hu
    have hu' := Finset.mem_Icc.1 hu
    have : u = t := by omega
    simpa [this] using ht
  have hqn : Q.Nonempty := ⟨t, hqt⟩
  let s := Q.min' hqn
  have hsq : s ∈ Q := Finset.min'_mem _ hqn
  have hs := Finset.mem_filter.1 hsq
  have hstart : s-1 ∉ T := by
    intro hp
    have hpq : s-1 ∈ Q := by
      apply Finset.mem_filter.2
      refine ⟨hp, by omega, ?_⟩
      intro u hu
      have hu' := Finset.mem_Icc.1 hu
      by_cases he : u = s-1
      · simpa [he] using hp
      · exact hs.2.2 (Finset.mem_Icc.2 ⟨by omega, hu'.2⟩)
    have hh : s ≤ s-1 := Finset.min'_le Q (s-1) hpq
    omega
  refine ⟨s, Finset.mem_filter.2 ⟨hs.1, hstart⟩, ?_⟩
  exact Finset.mem_filter.2 ⟨ht, hs.2⟩

/-- Every finite integer set is the union of one nonempty interval per run start. -/
private theorem integer_runs (T : Finset ℤ) :
    ∃ R : Finset (Finset ℤ),
      R.biUnion id = T ∧
      R.card = (T.filter (fun t => t-1 ∉ T)).card ∧
      ∀ J ∈ R, ∃ a b : ℤ, a ≤ b ∧ J = Finset.Icc a b := by
  classical
  let S := T.filter (fun t => t-1 ∉ T)
  let R := S.image (integerRun T)
  refine ⟨R, ?_, ?_, ?_⟩
  · ext t
    constructor
    · intro ht
      obtain ⟨J, hJ, htJ⟩ := Finset.mem_biUnion.1 ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hJ
      exact (Finset.mem_filter.1 htJ).1
    · intro ht
      obtain ⟨s, hs, hts⟩ := integerRun_cover T t ht
      exact Finset.mem_biUnion.2 ⟨integerRun T s,
        Finset.mem_image.2 ⟨s, hs, rfl⟩, hts⟩
  · apply Finset.card_image_of_injOn
    intro s hs u hu he
    have hsT := (Finset.mem_filter.1 hs).1
    have huT := (Finset.mem_filter.1 hu).1
    have hsu : s ∈ integerRun T u := he ▸ mem_integerRun_self T s hsT
    have hus : u ∈ integerRun T s := he.symm ▸ mem_integerRun_self T u huT
    have h1 := (Finset.mem_filter.1 hsu).2.1
    have h2 := (Finset.mem_filter.1 hus).2.1
    omega
  · intro J hJ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hJ
    obtain ⟨b, hb, he⟩ := integerRun_interval T s (Finset.mem_filter.1 hs).1
    exact ⟨s, b, hb, he⟩

/-- A bound on the number of run starts supplies the sharp rounded-up longest-run bound. -/
private theorem integer_long_run (T : Finset ℤ) (hT : T.Nonempty)
    (K : ℕ) (hK : 0 < K) (hstarts : (T.filter (fun t => t - 1 ∉ T)).card ≤ K) :
    ∃ a b : ℤ, Finset.Icc a b ⊆ T ∧ a ≤ b ∧
      (T.card+K-1)/K ≤ (Finset.Icc a b).card := by
  classical
  obtain ⟨R, hcover, hcard, hintervals⟩ := integer_runs T
  have hR : R.Nonempty := by
    obtain ⟨t, ht⟩ := hT
    rw [← hcover] at ht
    obtain ⟨J, hJ, _⟩ := Finset.mem_biUnion.1 ht
    exact ⟨J, hJ⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image R Finset.card hR
  obtain ⟨a, b, hab, rfl⟩ := hintervals J hJ
  have hbound : T.card ≤ K * (Finset.Icc a b).card := by
    have h := Finset.card_biUnion_le_card_mul R id (Finset.Icc a b).card hmax
    rw [hcover] at h
    exact h.trans (Nat.mul_le_mul_right _ (by omega))
  refine ⟨a, b, ?_, hab, ?_⟩
  · intro t ht
    rw [← hcover]
    exact Finset.mem_biUnion.2 ⟨Finset.Icc a b, hJ, ht⟩
  · apply (Nat.div_le_iff_le_mul_add_pred hK).2
    omega

/-- Unit successive gaps fill the entire integer interval, including a singleton tail. -/
private theorem consecutive_image (x : ℕ → ℤ) (n m : ℕ) (hm : m < n)
    (_hx : StrictMonoOn x (Set.Iio n))
    (hstep : ∀ i ∈ Finset.Ico (m + 1) n, x i - x (i - 1) = 1) :
    (Finset.Ico m n).image x = Finset.Icc (x m) (x (n-1)) := by
  classical
  have hformula : ∀ i, m ≤ i → i < n → x i = x m + ((i-m : ℕ) : ℤ) := by
    intro i hmi
    induction i, hmi using Nat.le_induction with
    | base => intro _; simp
    | succ i hmi ih =>
      intro hin
      have hip : i < n := by omega
      have hi := ih hip
      have hs := hstep (i+1) (Finset.mem_Ico.2 ⟨by omega, hin⟩)
      rw [show i+1-1 = i by omega] at hs
      have he : i+1-m = (i-m)+1 := by omega
      rw [he, Nat.cast_add, Nat.cast_one]
      omega
  have hlast := hformula (n-1) (by omega) (by omega)
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    have hi' := Finset.mem_Ico.1 hi
    have hf := hformula i hi'.1 hi'.2
    apply Finset.mem_Icc.2
    constructor <;> omega
  · intro ht
    have ht' := Finset.mem_Icc.1 ht
    let d : ℕ := (t-x m).toNat
    have hd : (d : ℤ) = t-x m := by
      exact Int.toNat_of_nonneg (by omega)
    have hid : m+d < n := by omega
    refine Finset.mem_image.2 ⟨m+d, Finset.mem_Ico.2 ⟨by omega, hid⟩, ?_⟩
    have hf := hformula (m+d) (by omega) hid
    rw [show m+d-m = d by omega] at hf
    omega

/-- Right-endpoint losses control all deficient endpoints, weighted gaps and actual consecutive tails. -/
theorem whole_theorem_three_three (n : ℕ) (hn : 10 ≤ n) (x : ℕ → ℤ)
    (hx : StrictMonoOn x (Set.Iio n)) :
    let E := prefixSet x n
    let P := prefixSet x 10
    let T := E \ P
    let c := fun i => completed (prefixSet x i) (x i)
    let δ := 4*n-26-count E
    let K := 1+δ/3
    count E ≤ 4*n-26 ∧
    δ = 14-count P + ∑ i ∈ Finset.Ico 10 n, (4-c i) ∧
    ((Finset.Ico 10 n).filter (fun i => c i < 4)).card ≤ δ ∧
    3*((Finset.Ico 10 n).filter (fun i => x i-x (i-1)=2)).card +
    4*((Finset.Ico 10 n).filter (fun i => 3 ≤ x i-x (i-1))).card ≤ δ ∧
    (10 < n →
      (∃ R : Finset (Finset ℤ), R.biUnion id = T ∧ R.card ≤ K ∧
        ∀ J ∈ R, ∃ a b : ℤ, a ≤ b ∧ J=Finset.Icc a b) ∧
      (∃ a b : ℤ, Finset.Icc a b ⊆ T ∧ a ≤ b ∧
        (n-10+K-1)/K ≤ (Finset.Icc a b).card)) ∧
    (δ ≤ 2 → (Finset.Ico 9 n).image x = Finset.Icc (x 9) (x (n-1))) := by
  classical
  dsimp only
  have hd := defect_accounting x n hn hx
  refine ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,?_,?_⟩
  · intro hgt
    let T := prefixSet x n \ prefixSet x 10
    let δ := 4*n-26-count (prefixSet x n)
    let K := 1+δ/3
    have hstarts := tail_starts_bound x n hn hx
    have hw := hd.2.2.2
    have hbound : (T.filter (fun t => t-1 ∉ T)).card ≤ K := by
      dsimp [T,K,δ]
      dsimp only at hstarts hw
      omega
    have hTcard : T.card=n-10 := by
      dsimp [T]
      have hsub : prefixSet x 10 ⊆ prefixSet x n :=
        Finset.image_subset_image (Finset.range_mono hn)
      rw [Finset.card_sdiff_of_subset hsub,
        prefix_card x n n hx le_rfl,prefix_card x n 10 hx hn]
    have hT : T.Nonempty := Finset.card_pos.1 (by omega)
    have hK : 0<K := by dsimp [K]; omega
    obtain ⟨R,hR,hcard,hinterval⟩ := integer_runs T
    obtain ⟨a,b,hab,hlt,hlong⟩ := integer_long_run T hT K hK hbound
    refine ⟨⟨R,hR,by omega,hinterval⟩,a,b,hab,hlt,?_⟩
    simpa only [hTcard] using hlong
  · intro hsmall
    exact consecutive_image x n 9 (by omega) hx (small_defect_steps x n hn hx hsmall)

end D5.S3.Arith.Additive.PlasticTailStability
