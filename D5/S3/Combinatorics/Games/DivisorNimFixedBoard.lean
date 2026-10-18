/- GID: D5/S3/Combinatorics/Games/DivisorNimFixedBoard
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimFixedBoard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact fixed-board options with zero omission and occurrence-selected legal moves. -/

import D5.S3.Combinatorics.Games.DivisorNimGcdSixSource
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

/-- A varying heap of size zero is omitted. -/
def adjoinHeap (A : Position) (n : ℕ) : Position :=
  if n = 0 then A else n ::ₘ A

/-- The actual SG sequence, including its zero argument. -/
noncomputable def fixedSequence (A : Position) (n : ℕ) : ℕ :=
  grundy (adjoinHeap A n)

/-- Omitting the zero heap preserves exactly the eventual periods. -/
theorem tail_period_iff_fixed_sequence {A : Position} {T : ℕ} :
    HasTailPeriod A T ↔
      ∃ N, ∀ n, N ≤ n → fixedSequence A (n + T) = fixedSequence A n := by
  constructor <;> rintro ⟨N, hN⟩ <;> refine ⟨N + 1, ?_⟩ <;> intro n hn
  · simpa only [fixedSequence, adjoinHeap, if_neg (show n ≠ 0 by omega),
      if_neg (show n + T ≠ 0 by omega)] using hN n (by omega)
  · have he := hN n (by omega)
    simpa only [fixedSequence, adjoinHeap, if_neg (show n ≠ 0 by omega),
      if_neg (show n + T ≠ 0 by omega)] using he

/-- Selected fixed heap sizes and removed amounts; erasure selects one occurrence. -/
noncomputable def fixedMoveData (A : Position) : Finset (ℕ × ℕ) := by
  classical
  exact A.toFinset.biUnion fun h =>
    ((Finset.Icc 1 h).filter (legal A h)).image fun d => (h, d)

/-- All fixed options, including deletion of the last fixed heap. -/
noncomputable def fixedMoveValues (A : Position) (n : ℕ) : Finset ℕ := by
  classical
  exact ((fixedMoveData A).filter fun p => p.2 ∣ n).image fun p =>
    fixedSequence (successor A p.1 p.2) n

theorem mem_fixedMoveData {A : Position} {h d : ℕ} :
    (h, d) ∈ fixedMoveData A ↔ h ∈ A ∧ legal A h d := by
  classical
  simp only [fixedMoveData, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Prod.mk.injEq, Multiset.mem_toFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, b, ⟨_, hb⟩, rfl, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨hh, hd⟩
    exact ⟨h, hh, d, ⟨⟨hd.1, hd.2.1⟩, hd⟩, rfl, rfl⟩

private theorem adjoin_positive {A : Position} (hp : Positive A) (n : ℕ) :
    Positive (adjoinHeap A n) := by
  by_cases hn : n = 0
  · simpa [adjoinHeap, hn] using hp
  · intro h hh
    simp only [adjoinHeap, if_neg hn, Multiset.mem_cons] at hh
    rcases hh with rfl | hh
    · omega
    · exact hp h hh

private theorem gcd_positive {A : Position} (hp : Positive A) (ha : A ≠ 0) :
    0 < A.gcd := by
  obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
  exact Nat.pos_of_ne_zero ((Multiset.gcd_ne_zero_iff A).mpr
    ⟨h, hh, Nat.ne_of_gt (hp h hh)⟩)

/-- Both inclusions are equality of actual follower values. The last fixed
heap may disappear, and subtraction from the varying heap may leave zero. -/
theorem fixed_board_recurrence {A : Position} (hp : Positive A) (ha : A ≠ 0)
    {n : ℕ} (hn : A.gcd ≤ n) :
    (moves (adjoinHeap A n)).image grundy =
      (A.gcd.divisors.image fun d => fixedSequence A (n - d)) ∪ fixedMoveValues A n := by
  classical
  have hD := gcd_positive hp ha
  have hn0 : n ≠ 0 := by omega
  have hvar : ∀ d, 0 < d → d ≤ n →
      successor (n ::ₘ A) n d = adjoinHeap A (n - d) := by
    intro d hd hdn
    by_cases hz : n - d = 0
    · simp [successor, adjoinHeap, hz]
    · simp only [successor, adjoinHeap, if_neg hz, Multiset.erase_cons_head]
      rw [Multiset.add_comm, Multiset.singleton_add]
  have hfix : ∀ h ∈ A, ∀ d,
      successor (n ::ₘ A) h d = n ::ₘ successor A h d := by
    intro h hh d
    rw [successor, Multiset.erase_cons_tail_of_mem hh]
    simp only [successor, Multiset.cons_add]
  rw [adjoinHeap, if_neg hn0]
  ext v
  constructor
  · intro hv
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
    rcases Multiset.mem_cons.mp hh with rfl | hh
    · have hdD : d ∣ A.gcd := Multiset.dvd_gcd.mpr (by
        simpa only [dividesAll, Multiset.erase_cons_head] using hd.2.2)
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨d, Nat.mem_divisors.mpr ⟨hdD, by omega⟩, ?_⟩
      exact congrArg grundy (hvar d hd.1 hd.2.1).symm
    · have hdn : d ∣ n := hd.2.2 n (by
        rw [Multiset.erase_cons_tail_of_mem hh]; simp)
      have hdA : legal A h d := ⟨hd.1, hd.2.1, fun x hx =>
        hd.2.2 x (by rw [Multiset.erase_cons_tail_of_mem hh]; simp [hx])⟩
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨(h, d),
        Finset.mem_filter.mpr ⟨mem_fixedMoveData.mpr ⟨hh, hdA⟩, hdn⟩, ?_⟩
      simp only [fixedSequence, adjoinHeap, if_neg hn0, hfix h hh d]
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
      have hdD := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdD hD
      have hdn : d ≤ n := (Nat.le_of_dvd hD hdD).trans hn
      have hlegal : legal (n ::ₘ A) n d :=
        ⟨hd0, hdn, by simpa [dividesAll] using
          fun h hh => hdD.trans (Multiset.gcd_dvd hh)⟩
      refine Finset.mem_image.mpr ⟨successor (n ::ₘ A) n d,
        successor_is_move (by simp) hlegal, ?_⟩
      exact congrArg grundy (hvar d hd0 hdn)
    · obtain ⟨⟨h, d⟩, hd, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hdata, hdn⟩ := Finset.mem_filter.mp hd
      obtain ⟨hh, hdA⟩ := mem_fixedMoveData.mp hdata
      have hlegal : legal (n ::ₘ A) h d := by
        refine ⟨hdA.1, hdA.2.1, ?_⟩
        rw [Multiset.erase_cons_tail_of_mem hh]
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hdn
        · exact hdA.2.2 x hx
      refine Finset.mem_image.mpr ⟨successor (n ::ₘ A) h d,
        successor_is_move (by simp [hh]) hlegal, ?_⟩
      simp only [fixedSequence, adjoinHeap, if_neg hn0, hfix h hh d]

private theorem fixedSequence_bound {A : Position} (hp : Positive A) (ha : A ≠ 0)
    {n : ℕ} (hn : A.sum < n) : fixedSequence A n ≤ 2 * A.sum := by
  classical
  have hne : A.toFinset.Nonempty := by
    obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
    exact ⟨h, Multiset.mem_toFinset.mpr hh⟩
  let m := A.toFinset.min' hne
  have hm : m ∈ A := Multiset.mem_toFinset.mp (Finset.min'_mem _ hne)
  have hmle : ∀ h ∈ adjoinHeap A n, m ≤ h := by
    intro h hh
    simp only [adjoinHeap, if_neg (show n ≠ 0 by omega), Multiset.mem_cons] at hh
    rcases hh with rfl | hh
    · exact (Multiset.le_sum_of_mem hm).trans (by omega)
    · exact Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hh)
  have hnon : adjoinHeap A n ≠ 0 := by simp [adjoinHeap, show n ≠ 0 by omega]
  have hmem : m ∈ adjoinHeap A n := by simp [adjoinHeap, show n ≠ 0 by omega, hm]
  exact (result _ (adjoin_positive hp n) hnon m hmem hmle).trans
    (Nat.mul_le_mul_left 2 (Multiset.le_sum_of_mem hm))

/-- The empty fixed successor remains an actual option of value n. On the
tail this exceeds the uniform bound and therefore does not change the mex. -/
private theorem fixed_tail_recurrence {A : Position} (hp : Positive A) (ha : A ≠ 0)
    {n : ℕ} (hn : 2 * A.sum < n) :
    fixedSequence A n = mex
      ((A.gcd.divisors.image fun d => fixedSequence A (n - d)) ∪ fixedValues A n) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hg : A.gcd ≤ n := by
    obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
    have := Nat.le_of_dvd (hp h hh) (Multiset.gcd_dvd hh)
    have := Multiset.le_sum_of_mem hh
    omega
  let L := A.gcd.divisors.image fun d => fixedSequence A (n - d)
  let F := fixedValues A n
  have hsub : F ⊆ fixedMoveValues A n := by
    intro v hv
    simp only [F, fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨h, hh, d, ⟨_, hd, hdn, _⟩, rfl⟩ := hv
    refine Finset.mem_image.mpr ⟨(h, d), Finset.mem_filter.mpr
      ⟨mem_fixedMoveData.mpr ⟨Multiset.mem_toFinset.mp hh, hd⟩, hdn⟩, ?_⟩
    simp [fixedSequence, adjoinHeap, hn0]
  have hcover : fixedMoveValues A n ⊆ F ∪ {n} := by
    intro v hv
    obtain ⟨⟨h, d⟩, hd, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hdata, hdn⟩ := Finset.mem_filter.mp hd
    obtain ⟨hh, hd⟩ := mem_fixedMoveData.mp hdata
    by_cases he : successor A h d = 0
    · apply Finset.mem_union_right
      simp only [fixedSequence, adjoinHeap, if_neg hn0, he, Multiset.cons_zero,
        singleton_grundy n (by omega), Finset.mem_singleton]
    · apply Finset.mem_union_left
      simp only [F, fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      refine ⟨h, Multiset.mem_toFinset.mpr hh, d,
        ⟨Finset.mem_Icc.mpr ⟨hd.1, hd.2.1⟩, hd, hdn, he⟩, ?_⟩
      simp [fixedSequence, adjoinHeap, hn0]
  have heq := fixed_board_recurrence hp ha hg
  have hreal : L ∪ F ⊆ (moves (adjoinHeap A n)).image grundy := by
    rw [heq]
    exact Finset.union_subset_union_right hsub
  have hall : ∀ v < fixedSequence A n, v ∈ L ∪ F := by
    intro v hv
    have hfull := follower_mem_of_lt (adjoinHeap A n) hv
    rw [heq] at hfull
    rcases Finset.mem_union.mp hfull with hl | hf
    · exact Finset.mem_union_left _ hl
    · rcases Finset.mem_union.mp (hcover hf) with hf | hf
      · exact Finset.mem_union_right _ hf
      · have he : v = n := Finset.mem_singleton.mp hf
        have hb := fixedSequence_bound hp ha (show A.sum < n by omega)
        omega
  have hnot : fixedSequence A n ∉ L ∪ F := fun hv =>
    grundy_not_follower _ (hreal hv)
  change fixedSequence A n = mex (L ∪ F)
  apply Nat.le_antisymm
  · by_contra h
    exact (mex_spec _).1 (hall _ (by omega))
  · by_contra h
    exact hnot ((mex_spec _).2 _ (by omega))

private theorem tail_period_multiple {A : Position} {T : ℕ}
    (hT : HasTailPeriod A T) (k : ℕ) : HasTailPeriod A (T * k) := by
  obtain ⟨N, hN⟩ := hT
  refine ⟨N, ?_⟩
  intro n hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hN (n + T * k) (by omega), ih]

private theorem fixed_values_tail {A : Position} (hp : Positive A)
    {H T : ℕ} (hH : H ∈ A)
    (hJT : (Finset.Icc 1 H).lcm id ∣ T)
    (htail : ∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q T) :
    ∃ N, ∀ n, N ≤ n → fixedValues A (n + T) = fixedValues A n := by
  classical
  have hex : ∀ Q : Position, ∃ N, ∀ n, N ≤ n → Q ∈ moves A → Q ≠ 0 →
      grundy ((n + T) ::ₘ Q) = grundy (n ::ₘ Q) := by
    intro Q
    by_cases hQ : Q ∈ moves A
    · by_cases hne : Q ≠ 0
      · obtain ⟨N, hN⟩ := htail Q hQ hne
        exact ⟨N, fun n hn _ _ => hN n hn⟩
      · exact ⟨0, fun _ _ _ hn => (hne hn).elim⟩
    · exact ⟨0, fun _ _ hn _ => (hQ hn).elim⟩
  choose start hstart using hex
  refine ⟨(moves A).sup start, ?_⟩
  intro n hn
  have hdT : ∀ h ∈ A, ∀ d, legal A h d → d ∣ T := by
    intro h hh d hd
    have hdH := removal_le_reference hp hH le_rfl hd
    exact (Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hd.1, hdH⟩)).trans hJT
  have hleg : ∀ h ∈ A, ∀ d, legal A h d → (d ∣ n + T ↔ d ∣ n) := by
    intro h hh d hd
    exact (Nat.dvd_add_iff_left (hdT h hh d hd)).symm
  have hval : ∀ h ∈ A, ∀ d, legal A h d → successor A h d ≠ 0 →
      grundy ((n + T) ::ₘ successor A h d) = grundy (n ::ₘ successor A h d) := by
    intro h hh d hd hne
    have hQ := successor_is_move hh hd
    exact hstart _ n ((Finset.le_sup hQ).trans hn) hQ hne
  ext v
  simp only [fixedValues, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨h, hh, d, ⟨hI, hd, hdn, hne⟩, hv⟩
    refine ⟨h, hh, d, ⟨hI, hd, (hleg h (Multiset.mem_toFinset.mp hh) d hd).mp hdn, hne⟩, ?_⟩
    exact (hval h (Multiset.mem_toFinset.mp hh) d hd hne).symm.trans hv
  · rintro ⟨h, hh, d, ⟨hI, hd, hdn, hne⟩, hv⟩
    refine ⟨h, hh, d, ⟨hI, hd, (hleg h (Multiset.mem_toFinset.mp hh) d hd).mpr hdn, hne⟩, ?_⟩
    exact (hval h (Multiset.mem_toFinset.mp hh) d hd hne).trans hv

/-- Every nonempty positive fixed board has an eventual period. The finite
state is a full gcd-length block of actual SG values at a common signal phase. -/
theorem fixed_board_eventually_periodic {A : Position} (hp : Positive A) (ha : A ≠ 0) :
    ∃ T, 0 < T ∧ ∃ N, ∀ n, N ≤ n → fixedSequence A (n + T) = fixedSequence A n := by
  classical
  have main : ∀ s, ∀ A : Position, A.sum = s → Positive A → A ≠ 0 →
      ∃ T, 0 < T ∧ HasTailPeriod A T := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro A hs hp ha
      have hne : A.toFinset.Nonempty := by
        obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
        exact ⟨h, Multiset.mem_toFinset.mpr hh⟩
      let H := A.toFinset.min' hne
      have hH : H ∈ A := Multiset.mem_toFinset.mp (Finset.min'_mem _ hne)
      have hex : ∀ Q : Position, ∃ p, 0 < p ∧
          (Q ∈ moves A → Q ≠ 0 → HasTailPeriod Q p) := by
        intro Q
        by_cases hQ : Q ∈ moves A
        · by_cases hnQ : Q ≠ 0
          · have hpQ : Positive Q := by
              obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
              exact successor_positive hp hh hd
            obtain ⟨p, hp, hper⟩ := ih Q.sum (by rw [← hs]; exact move_sum_lt hQ)
              Q rfl hpQ hnQ
            exact ⟨p, hp, fun _ _ => hper⟩
          · exact ⟨1, by omega, fun _ hn => (hnQ hn).elim⟩
        · exact ⟨1, by omega, fun hn _ => (hQ hn).elim⟩
      choose period hperiodpos hperiod using hex
      let J := (Finset.Icc 1 H).lcm id
      let C := (moves A).lcm period
      let T := J * C
      have hJ : 0 < J := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (by
        intro x hx
        have := (Finset.mem_Icc.mp hx).1
        change x ≠ 0
        omega))
      have hC : 0 < C := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
        (fun Q _ => Nat.ne_of_gt (hperiodpos Q)))
      have hT : 0 < T := Nat.mul_pos hJ hC
      have htail : ∀ Q ∈ moves A, Q ≠ 0 → HasTailPeriod Q T := by
        intro Q hQ hnQ
        have hd : period Q ∣ T := (Finset.dvd_lcm hQ).trans (dvd_mul_left C J)
        obtain ⟨k, hk⟩ := hd
        rw [hk]
        exact tail_period_multiple (hperiod Q hQ hnQ) k
      obtain ⟨N₀, hN₀⟩ := fixed_values_tail hp hH (dvd_mul_right J C) htail
      let N := N₀ + 2 * A.sum + A.gcd + 1
      have hD : 0 < A.gcd := gcd_positive hp ha
      have hsignal : ∀ n, N ≤ n → ∀ k,
          fixedValues A (n + T * k) = fixedValues A n := by
        intro n hn k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, hN₀ (n + T * k) (by dsimp [N] at hn; omega), ih]
      let state (i : ℕ) : Fin A.gcd → Fin (2 * A.sum + 1) := fun k =>
        ⟨fixedSequence A (N + T * i + k.val), by
          have hb := fixedSequence_bound hp ha (show A.sum < N + T * i + k.val by
            dsimp [N]; omega)
          omega⟩
      obtain ⟨i, j, hneij, heq⟩ := Finite.exists_ne_map_eq_of_infinite state
      have collision : ∃ i j, i < j ∧ state i = state j := by
        rcases lt_or_gt_of_ne hneij with hij | hji
        · exact ⟨i, j, hij, heq⟩
        · exact ⟨j, i, hji, heq.symm⟩
      obtain ⟨i, j, hij, heq⟩ := collision
      have propagate : ∀ t,
          fixedSequence A (N + T * j + t) = fixedSequence A (N + T * i + t) := by
        apply mex_forced_block_propagation A.gcd A.gcd.divisors
          (fun d hd => ⟨Nat.pos_of_mem_divisors hd,
            Nat.le_of_dvd hD (Nat.mem_divisors.mp hd).1⟩)
          (fun t => fixedSequence A (N + T * j + t))
          (fun t => fixedSequence A (N + T * i + t))
          (fun t => fixedValues A (N + T * i + t))
        · intro t ht
          exact congrArg (fun v : Fin (2 * A.sum + 1) => v.val)
            (congrFun heq ⟨t, ht⟩).symm
        · intro t ht
          rw [fixed_tail_recurrence hp ha
            (show 2 * A.sum < N + T * j + t by dsimp [N]; omega)]
          have hF : fixedValues A (N + T * j + t) = fixedValues A (N + T * i + t) := by
            have h₁ := hsignal (N + t) (by omega) j
            have h₂ := hsignal (N + t) (by omega) i
            simpa only [Nat.add_right_comm] using h₁.trans h₂.symm
          rw [hF, Finset.union_comm]
          congr 2
          apply Finset.image_congr
          intro d hd
          have hdD := Nat.le_of_dvd hD (Nat.mem_divisors.mp hd).1
          simp only [Nat.add_sub_assoc (show d ≤ t by omega)]
        · intro t ht
          rw [fixed_tail_recurrence hp ha
            (show 2 * A.sum < N + T * i + t by dsimp [N]; omega)]
          rw [Finset.union_comm]
          congr 2
          apply Finset.image_congr
          intro d hd
          have hdD := Nat.le_of_dvd hD (Nat.mem_divisors.mp hd).1
          simp only [Nat.add_sub_assoc (show d ≤ t by omega)]
      refine ⟨T * (j - i), Nat.mul_pos hT (by omega), N + T * i, ?_⟩
      intro n hn
      have hstep := propagate (n - (N + T * i))
      have he : N + T * j + (n - (N + T * i)) = n + T * (j - i) := by
        have hmul : T * j = T * i + T * (j - i) := by
          rw [← Nat.mul_add, Nat.add_sub_of_le (by omega : i ≤ j)]
        omega
      have he' : N + T * i + (n - (N + T * i)) = n := Nat.add_sub_of_le hn
      rw [he, he'] at hstep
      have hn0 : n ≠ 0 := by dsimp [N] at hn; omega
      have hnp0 : n + T * (j - i) ≠ 0 := by omega
      simpa only [fixedSequence, adjoinHeap, if_neg hn0, if_neg hnp0] using hstep
  obtain ⟨T, hT, hperiod⟩ := main A.sum A rfl hp ha
  exact ⟨T, hT, tail_period_iff_fixed_sequence.mp hperiod⟩

/-- The least positive eventual period, or zero if none exists. -/
noncomputable def leastTailPeriod (A : Position) : ℕ := by
  classical
  exact if h : ∃ T, 0 < T ∧ HasTailPeriod A T then Nat.find h else 0

private theorem tail_period_sub {A : Position} {p q : ℕ}
    (hp : HasTailPeriod A p) (hq : HasTailPeriod A q) (hpq : p ≤ q) :
    HasTailPeriod A (q - p) := by
  obtain ⟨Np, hNp⟩ := hp
  obtain ⟨Nq, hNq⟩ := hq
  refine ⟨Np + Nq + p, ?_⟩
  intro n hn
  have h₁ := hNq (n - p) (by omega)
  have h₂ := hNp (n - p) (by omega)
  have he : n - p + q = n + (q - p) := by omega
  have he' : n - p + p = n := by omega
  rw [he] at h₁
  rw [he'] at h₂
  exact h₁.trans h₂.symm

/-- Least means divisibility into every eventual period, not only minimality
among a chosen finite collection of shifts. -/
theorem fixed_board_least_period {A : Position} (hp : Positive A) (ha : A ≠ 0) :
    0 < leastTailPeriod A ∧ HasTailPeriod A (leastTailPeriod A) ∧
      ∀ T, HasTailPeriod A T → leastTailPeriod A ∣ T := by
  classical
  have hex : ∃ T, 0 < T ∧ HasTailPeriod A T := by
    obtain ⟨T, hT, hperiod⟩ := fixed_board_eventually_periodic hp ha
    exact ⟨T, hT, tail_period_iff_fixed_sequence.mpr hperiod⟩
  rw [leastTailPeriod, dif_pos hex]
  have hQ := Nat.find_spec hex
  refine ⟨hQ.1, hQ.2, ?_⟩
  intro T hT
  let Q := Nat.find hex
  have hsmall : Q * (T / Q) ≤ T := Nat.mul_div_le T Q
  have hrem := tail_period_sub (tail_period_multiple hQ.2 (T / Q)) hT hsmall
  have he : T - Q * (T / Q) = T % Q := by
    have := Nat.mod_add_div T Q
    omega
  rw [he] at hrem
  have hz : T % Q = 0 := by
    by_contra hn
    have hm : Q ≤ T % Q := Nat.find_min' hex ⟨by omega, hrem⟩
    have hlt := Nat.mod_lt T (show 0 < Q from hQ.1)
    omega
  exact Nat.dvd_of_mod_eq_zero hz

/-- The minimum fixed heap; the empty board is assigned zero. -/
noncomputable def fixedMinimum (A : Position) : ℕ :=
  if h : A.toFinset.Nonempty then A.toFinset.min' h else 0

/-- Tyagi's comparison spacing uses actual least successor periods. -/
noncomputable def comparisonSpacing (A : Position) : ℕ := by
  classical
  exact Nat.lcm ((Finset.Icc 1 (fixedMinimum A)).lcm id)
    (((moves A).filter fun Q => Q ≠ 0).lcm leastTailPeriod)

theorem fixed_minimum_spec {A : Position} (ha : A ≠ 0) :
    fixedMinimum A ∈ A ∧ ∀ x ∈ A, fixedMinimum A ≤ x := by
  classical
  have hne : A.toFinset.Nonempty := by
    obtain ⟨h, hh⟩ := Multiset.exists_mem_of_ne_zero ha
    exact ⟨h, Multiset.mem_toFinset.mpr hh⟩
  simp only [fixedMinimum, dif_pos hne]
  exact ⟨Multiset.mem_toFinset.mp (Finset.min'_mem _ hne),
    fun x hx => Finset.min'_le _ _ (Multiset.mem_toFinset.mpr hx)⟩

/-- The exact spacing is positive, contains every successor's least period,
and repeats the complete nonempty fixed-option value set on a tail. -/
theorem comparison_spacing_signal {A : Position} (hp : Positive A) (ha : A ≠ 0) :
    0 < comparisonSpacing A ∧
    (Finset.Icc 1 (fixedMinimum A)).lcm id ∣ comparisonSpacing A ∧
    (∀ Q ∈ moves A, Q ≠ 0 → leastTailPeriod Q ∣ comparisonSpacing A) ∧
    ∃ N, ∀ n, N ≤ n →
      fixedValues A (n + comparisonSpacing A) = fixedValues A n := by
  classical
  obtain ⟨hH, _⟩ := fixed_minimum_spec ha
  let S := (moves A).filter fun Q => Q ≠ 0
  have hpQ : ∀ Q ∈ moves A, Positive Q := by
    intro Q hQ
    obtain ⟨h, hh, d, hd, rfl⟩ := moves_spec hQ
    exact successor_positive hp hh hd
  have hJ : 0 < (Finset.Icc 1 (fixedMinimum A)).lcm id :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (by
      intro x hx
      have := (Finset.mem_Icc.mp hx).1
      change x ≠ 0
      omega))
  have hS : 0 < S.lcm leastTailPeriod :=
    Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (by
      intro Q hQ
      obtain ⟨hQA, hne⟩ := Finset.mem_filter.mp hQ
      exact Nat.ne_of_gt (fixed_board_least_period (hpQ Q hQA) hne).1))
  have hJdiv : (Finset.Icc 1 (fixedMinimum A)).lcm id ∣ comparisonSpacing A :=
    Nat.dvd_lcm_left _ _
  have hQdiv : ∀ Q ∈ moves A, Q ≠ 0 → leastTailPeriod Q ∣ comparisonSpacing A := by
    intro Q hQ hnQ
    exact (Finset.dvd_lcm (Finset.mem_filter.mpr ⟨hQ, hnQ⟩)).trans
      (Nat.dvd_lcm_right _ _)
  refine ⟨Nat.lcm_pos hJ hS, hJdiv, hQdiv, ?_⟩
  apply fixed_values_tail hp hH hJdiv
  intro Q hQ hnQ
  obtain ⟨k, hk⟩ := hQdiv Q hQ hnQ
  rw [hk]
  exact tail_period_multiple (fixed_board_least_period (hpQ Q hQ) hnQ).2.1 k

end D5.S3.Combinatorics.Games.DivisorNimGrundy
