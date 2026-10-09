/- GID: D5/S1/Words/Compositions/ZeroSumWordCount
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/ZeroSumWordCount
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [D5/S1/Words/Compositions/PhiTailEncoding]
   utility: none
   digest: Zero-sum words have factorial bounds and asymptotically negligible nonnegative excess. -/

import D5.S1.Words.Compositions.PhiTailEncoding
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Rotate
import Mathlib.Data.Finset.Powerset

import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Max
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BigOperators Topology

namespace D5.S1.Words.Compositions.ZeroSumWordCount

/-- All orderings of a finite integer alphabet. -/
noncomputable def orderings (S : Finset ℤ) : Finset (List ℤ) := by
  classical
  exact S.toList.permutations.toFinset

/-- Every prefix, including the full word, has nonnegative sum. -/
def Nonnegative (w : List ℤ) : Prop := ∀ k : ℕ, 0 ≤ (w.take k).sum

/-- Every nonempty proper prefix has positive sum. -/
def StrictPositive (w : List ℤ) : Prop :=
  ∀ k : ℕ, 0 < k → k < w.length → 0 < (w.take k).sum

noncomputable def weakWords (S : Finset ℤ) : Finset (List ℤ) := by
  classical
  exact (orderings S).filter Nonnegative

noncomputable def strictWords (S : Finset ℤ) : Finset (List ℤ) := by
  classical
  exact (orderings S).filter StrictPositive

noncomputable def weakCount (S : Finset ℤ) : ℕ := (weakWords S).card

noncomputable def strictCount (S : Finset ℤ) : ℕ := (strictWords S).card

theorem mem_orderings {S : Finset ℤ} {w : List ℤ} :
    w ∈ orderings S ↔ w.Perm S.toList := by
  classical
  simp [orderings, List.mem_permutations]

theorem orderings_card (S : Finset ℤ) : (orderings S).card = S.card.factorial := by
  classical
  rw [orderings, List.toFinset_card_of_nodup
    (List.nodup_permutations _ (Finset.nodup_toList _)), List.length_permutations]
  simp

private theorem prefix_segment_sum (w : List ℤ) (j k : ℕ) :
    (w.take j).sum + ((w.drop j).take k).sum = (w.take (j + k)).sum := by
  have h : w.take j ++ (w.drop j).take k = w.take (j + k) := by
    rw [List.take_drop]
    have ht := List.take_append_drop j (w.take (j + k))
    simpa [List.take_take, Nat.min_eq_left (Nat.le_add_right j k)] using ht
  simpa only [List.sum_append] using congrArg List.sum h

/-- Cutting after a minimum prefix sum produces a nonnegative zero-sum rotation. -/
theorem nonnegative_rotate_of_minimum {w : List ℤ} (hw : w.sum = 0) {j : ℕ}
    (hj : j ≤ w.length)
    (hmin : ∀ k ≤ w.length, (w.take j).sum ≤ (w.take k).sum) :
    Nonnegative (w.rotate j) := by
  intro k
  have hsplit := congrArg List.sum (List.take_append_drop j w)
  simp only [List.sum_append] at hsplit
  rw [List.rotate_eq_drop_append_take hj, List.take_append, List.sum_append]
  by_cases hk : k ≤ w.length - j
  · have hz : k - (w.drop j).length = 0 := by simp only [List.length_drop]; omega
    rw [hz, List.take_zero, List.sum_nil, add_zero]
    have hseg := prefix_segment_sum w j k
    have hm := hmin (j + k) (by omega)
    omega
  · have hd : (w.drop j).length ≤ k := by simp only [List.length_drop]; omega
    rw [List.take_of_length_le hd]
    have ht : k - (w.drop j).length ≤ j ∨ j ≤ k - (w.drop j).length := le_total _ _
    rw [List.take_take]
    have hm := hmin (min (k - (w.drop j).length) j) (by omega)
    omega

/-- Every zero-sum word has a rotation with nonnegative prefix sums. -/
theorem exists_nonnegative_rotation (w : List ℤ) (hw : w.sum = 0) :
    ∃ j ≤ w.length, Nonnegative (w.rotate j) := by
  classical
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.range (w.length + 1))
    (fun k => (w.take k).sum) ⟨0, by simp⟩
  have hj' : j ≤ w.length := by simp only [Finset.mem_range] at hj; omega
  exact ⟨j, hj', nonnegative_rotate_of_minimum hw hj'
    (fun k hk => hmin k (Finset.mem_range.mpr (by omega)))⟩

/-- A strictly positive zero-sum word has no other strictly positive proper rotation. -/
theorem strict_rotation_unique {w : List ℤ} (hw : w.sum = 0)
    (hp : StrictPositive w) {j : ℕ} (hj : j < w.length)
    (hr : StrictPositive (w.rotate j)) : j = 0 := by
  by_contra hj0
  have hjpos : 0 < j := by omega
  have hs := hp j hjpos hj
  have hdpos : 0 < w.length - j := by omega
  have hdlt : w.length - j < (w.rotate j).length := by
    rw [List.length_rotate]
    omega
  have ht := hr (w.length - j) hdpos hdlt
  have hsplit := congrArg List.sum (List.take_append_drop j w)
  simp only [List.sum_append] at hsplit
  rw [List.rotate_eq_drop_append_take hj.le, List.take_append] at ht
  simp only [List.length_drop, Nat.sub_self, List.take_zero,
    List.append_nil] at ht
  rw [List.take_of_length_le (by simp only [List.length_drop]; omega)] at ht
  omega

/-- Two strictly positive zero-sum words in the same rotation class coincide. -/
theorem strict_isRotated_eq {v w : List ℤ} (hv : v.sum = 0)
    (hpv : StrictPositive v) (hpw : StrictPositive w) (hrot : v.IsRotated w) : v = w := by
  obtain ⟨j, rfl⟩ := hrot
  by_cases hnil : v = []
  · simp [hnil]
  have hlen : 0 < v.length := List.length_pos_iff.mpr hnil
  have hr : StrictPositive (v.rotate (j % v.length)) := by simpa using hpw
  have hz := strict_rotation_unique hv hpv (Nat.mod_lt j hlen) hr
  rw [← List.rotate_mod, hz, List.rotate_zero]

/-- Words with one prescribed initial letter give one representative per rotation class. -/
noncomputable def anchoredWords (S : Finset ℤ) (a : ℤ) : Finset (List ℤ) := by
  classical
  exact (orderings (S.erase a)).image (List.cons a)

theorem anchoredWords_card (S : Finset ℤ) (a : ℤ) (ha : a ∈ S) :
    (anchoredWords S a).card = (S.card - 1).factorial := by
  classical
  rw [anchoredWords, Finset.card_image_of_injective _ (fun _ _ h => List.cons_injective h),
    orderings_card, Finset.card_erase_of_mem ha]

theorem mem_anchoredWords_iff {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) {w : List ℤ} :
    w ∈ anchoredWords S a ↔ w ∈ orderings S ∧ w.head? = some a := by
  classical
  have hS : S.toList.Perm (a :: (S.erase a).toList) := by
    simpa only [Finset.insert_erase ha] using
      Finset.toList_insert (Finset.notMem_erase a S)
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨mem_orderings.mpr (((mem_orderings.mp hv).cons a).trans hS.symm), rfl⟩
  · rintro ⟨hw, hh⟩
    cases w with
    | nil => simp at hh
    | cons b v =>
      have hb : b = a := by simpa using hh
      subst b
      exact Finset.mem_image.mpr ⟨v,
        mem_orderings.mpr ((mem_orderings.mp hw).trans hS).cons_inv, rfl⟩

private theorem ordering_sum {S : Finset ℤ} {w : List ℤ} (hw : w ∈ orderings S) :
    w.sum = ∑ a ∈ S, a := by
  rw [(mem_orderings.mp hw).sum_eq]
  exact Finset.sum_toList S

private theorem ordering_nodup {S : Finset ℤ} {w : List ℤ} (hw : w ∈ orderings S) :
    w.Nodup := (mem_orderings.mp hw).nodup_iff.mpr (Finset.nodup_toList S)

/-- Rotating an ordering until a prescribed letter occurs first yields an anchored word. -/
theorem rotate_idxOf_mem_anchoredWords {S : Finset ℤ} {a : ℤ} (ha : a ∈ S)
    {w : List ℤ} (hw : w ∈ orderings S) :
    w.rotate (w.idxOf a) ∈ anchoredWords S a := by
  have haw : a ∈ w := (mem_orderings.mp hw).mem_iff.mpr (Finset.mem_toList.mpr ha)
  apply (mem_anchoredWords_iff ha).mpr
  constructor
  · exact mem_orderings.mpr ((List.rotate_perm w _).trans (mem_orderings.mp hw))
  · rw [List.head?_rotate (List.idxOf_lt_length_of_mem haw), List.getElem?_idxOf haw]

/-- Equal initial letters determine equal rotations of a word with distinct letters. -/
theorem nodup_isRotated_eq_of_head {v w : List ℤ} (hv : v.Nodup)
    (hne : v ≠ []) (hh : v.head? = w.head?) (hrot : v.IsRotated w) : v = w := by
  obtain ⟨j, hj⟩ := hrot
  have hlen : 0 < v.length := List.length_pos_iff.mpr hne
  have hmod : j % v.length < v.length := Nat.mod_lt _ hlen
  have hhead := congrArg List.head? hj
  rw [← List.rotate_mod, List.head?_rotate hmod, ← hh] at hhead
  have hh0 : v.head? = v[0]? := by cases v <;> rfl
  rw [hh0] at hhead
  have hz : j % v.length = 0 := (List.getElem?_inj hmod hv).mp hhead
  rw [← hj, ← List.rotate_mod, hz, List.rotate_zero]

/-- Strictly positive words inject into the orderings with one prescribed initial letter. -/
theorem strictCount_le_factorial {S : Finset ℤ} (hS : ∑ a ∈ S, a = 0)
    (hne : S.Nonempty) : strictCount S ≤ (S.card - 1).factorial := by
  classical
  obtain ⟨a, ha⟩ := hne
  rw [← anchoredWords_card S a ha]
  apply Finset.card_le_card_of_injOn (fun w : List ℤ => w.rotate (w.idxOf a))
  · intro w hw
    exact rotate_idxOf_mem_anchoredWords ha (Finset.mem_filter.mp hw).1
  · intro v hv w hw heq
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    apply strict_isRotated_eq ((ordering_sum hv'.1).trans hS) hv'.2 hw'.2
    apply (List.IsRotated.forall v (v.idxOf a)).symm.trans
    change v.rotate (v.idxOf a) = w.rotate (w.idxOf a) at heq
    rw [heq]
    exact List.IsRotated.forall w (w.idxOf a)

/-- The anchored representative is constant along each rotation class. -/
theorem anchored_rotation_eq {S : Finset ℤ} {a : ℤ} (ha : a ∈ S)
    {u v : List ℤ} (hu : u ∈ orderings S) (hv : v ∈ orderings S)
    (hrot : u.IsRotated v) :
    u.rotate (u.idxOf a) = v.rotate (v.idxOf a) := by
  have hu' := (mem_anchoredWords_iff ha).mp (rotate_idxOf_mem_anchoredWords ha hu)
  have hv' := (mem_anchoredWords_iff ha).mp (rotate_idxOf_mem_anchoredWords ha hv)
  apply nodup_isRotated_eq_of_head (ordering_nodup hu'.1)
    (by intro hn; simp [hn] at hu') (hu'.2.trans hv'.2.symm)
  exact (List.IsRotated.forall u (u.idxOf a)).trans
    (hrot.trans (List.IsRotated.forall v (v.idxOf a)).symm)

private theorem anchor_surjective {S : Finset ℤ} (hS : ∑ a ∈ S, a = 0)
    {a : ℤ} (ha : a ∈ S) :
    Set.SurjOn (fun w : List ℤ => w.rotate (w.idxOf a)) (weakWords S) (anchoredWords S a) := by
  classical
  intro w hw
  have hw' := (mem_anchoredWords_iff ha).mp hw
  obtain ⟨j, _, hj⟩ := exists_nonnegative_rotation w ((ordering_sum hw'.1).trans hS)
  have hv : w.rotate j ∈ orderings S := mem_orderings.mpr
    ((List.rotate_perm w j).trans (mem_orderings.mp hw'.1))
  refine ⟨w.rotate j, Finset.mem_filter.mpr ⟨hv, hj⟩, ?_⟩
  have hv' := (mem_anchoredWords_iff ha).mp (rotate_idxOf_mem_anchoredWords ha hv)
  exact nodup_isRotated_eq_of_head (ordering_nodup hv'.1)
    (by intro hn; simp [hn] at hv') (hv'.2.trans hw'.2.symm)
    ((List.IsRotated.forall _ _).trans (List.IsRotated.forall _ _))

/-- Every rotation class supplies a nonnegative word, giving the factorial lower bound. -/
theorem factorial_le_weakCount {S : Finset ℤ} (hS : ∑ a ∈ S, a = 0)
    (hne : S.Nonempty) : (S.card - 1).factorial ≤ weakCount S := by
  classical
  obtain ⟨a, ha⟩ := hne
  rw [← anchoredWords_card S a ha]
  exact Finset.card_le_card_of_surjOn _ (anchor_surjective hS ha)

/-- Two distinct nonnegative words in one rotation class force strict excess. -/
theorem factorial_lt_weakCount_of_two_rotations {S : Finset ℤ}
    (hS : ∑ a ∈ S, a = 0) (hne : S.Nonempty)
    {u v : List ℤ} (hu : u ∈ weakWords S) (hv : v ∈ weakWords S)
    (hneuv : u ≠ v) (hrot : u.IsRotated v) :
    (S.card - 1).factorial < weakCount S := by
  classical
  obtain ⟨a, ha⟩ := hne
  rw [← anchoredWords_card S a ha]
  apply lt_of_not_ge
  intro hcard
  have hinj := Finset.injOn_of_surjOn_of_card_le (fun w : List ℤ => w.rotate (w.idxOf a))
    (fun w hw => rotate_idxOf_mem_anchoredWords ha (Finset.mem_filter.mp hw).1)
    (anchor_surjective hS ha) hcard
  exact hneuv (hinj hu hv (anchored_rotation_eq ha
    (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 hrot))

/-- Omitting the prefix restrictions yields the elementary factorial upper bound. -/
theorem weakCount_le_factorial (S : Finset ℤ) : weakCount S ≤ S.card.factorial := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (orderings_card S)



/-- Zero-sum subalphabets with prescribed cardinality. -/
def zeroSubsets (S : Finset ℤ) (k : ℕ) : Finset (Finset ℤ) :=
  (S.powersetCard k).filter (fun A => ∑ a ∈ A, a = 0)

/-- Removing a marked letter determines that letter from the zero-sum condition. -/
theorem marked_erase_injective (S : Finset ℤ) (k : ℕ) :
    Set.InjOn (fun x : (_A : Finset ℤ) × ℤ => x.1.erase x.2)
      ↑((zeroSubsets S k).sigma fun A => A) := by
  intro x hx y hy hxy
  change x.1.erase x.2 = y.1.erase y.2 at hxy
  obtain ⟨hxA, hxa⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hyA, hya⟩ := Finset.mem_sigma.mp hy
  have hxsum := (Finset.mem_filter.mp hxA).2
  have hysum := (Finset.mem_filter.mp hyA).2
  have ex := Finset.sum_erase_add x.1 (fun a : ℤ => a) hxa
  have ey := Finset.sum_erase_add y.1 (fun a : ℤ => a) hya
  have hab : x.2 = y.2 := by
    rw [hxsum] at ex
    rw [hysum, ← hxy] at ey
    omega
  have hAB : x.1 = y.1 := by
    rw [← Finset.insert_erase hxa, ← Finset.insert_erase hya, hxy, hab]
  cases x
  cases y
  simp_all

/-- Marked zero-sum subsets inject into subsets with one fewer letter. -/
theorem zeroSubsets_marked_bound (S : Finset ℤ) (k : ℕ) :
    k * (zeroSubsets S k).card ≤ S.card.choose (k - 1) := by
  have hm : Set.MapsTo (fun x : (A : Finset ℤ) × ℤ => x.1.erase x.2)
      ↑((zeroSubsets S k).sigma fun A => A) ↑(S.powersetCard (k - 1)) := by
    intro x hx
    obtain ⟨hxA, hxa⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hxs, hxk⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hxA).1
    exact Finset.mem_powersetCard.mpr
      ⟨(Finset.erase_subset _ _).trans hxs, by rw [Finset.card_erase_of_mem hxa, hxk]⟩
  have hc := Finset.card_le_card_of_injOn _ hm (marked_erase_injective S k)
  rw [Finset.card_powersetCard, Finset.card_sigma] at hc
  have hs : (∑ A ∈ zeroSubsets S k, A.card) = k * (zeroSubsets S k).card := by
    calc
      (∑ A ∈ zeroSubsets S k, A.card) = ∑ _A ∈ zeroSubsets S k, k := by
        apply Finset.sum_congr rfl
        intro A hA
        exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
      _ = _ := by simp [Nat.mul_comm]
  rwa [hs] at hc

/-- Complementation preserves zero sum and exchanges subset sizes. -/
theorem zeroSubsets_complement (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0)
    (k : ℕ) (hk : k ≤ S.card) :
    (zeroSubsets S k).card = (zeroSubsets S (S.card - k)).card := by
  have map_complement (j : ℕ) (A : Finset ℤ) (hA : A ∈ zeroSubsets S j) :
      S \ A ∈ zeroSubsets S (S.card - j) := by
    obtain ⟨hAs, hAj⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1
    have hAz := (Finset.mem_filter.mp hA).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,
      by rw [Finset.card_sdiff_of_subset hAs, hAj]⟩, ?_⟩
    have he := Finset.sum_sdiff hAs (f := fun a : ℤ => a)
    rw [hS, hAz] at he
    omega
  apply Finset.card_nbij' (fun A => S \ A) (fun A => S \ A)
  · exact fun A hA => map_complement k A hA
  · intro A hA
    have h := map_complement (S.card - k) A hA
    simpa [Nat.sub_sub_self hk] using h
  · intro A hA
    exact Finset.sdiff_sdiff_eq_self
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).1
  · intro A hA
    exact Finset.sdiff_sdiff_eq_self
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).1

/-- The density of zero-sum k-subsets is at most the reciprocal of m-k+1. -/
theorem zeroSubsets_density_one_side (S : Finset ℤ) (k : ℕ)
    (hk : 1 ≤ k) (hkm : k ≤ S.card) :
    (S.card - k + 1) * (zeroSubsets S k).card ≤ S.card.choose k := by
  have h := zeroSubsets_marked_bound S k
  have he := Nat.choose_succ_right_eq S.card (k - 1)
  have he' : S.card.choose k * k =
      S.card.choose (k - 1) * (S.card - k + 1) := by
    have hk' : k - 1 + 1 = k := by omega
    have hm' : S.card - (k - 1) = S.card - k + 1 := by omega
    rwa [hk', hm'] at he
  have hh := Nat.mul_le_mul_right (S.card - k + 1) h
  nlinarith

/-- Both deletion and complementation bound the density of zero-sum subsets. -/
theorem zeroSubsets_density (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < S.card) :
    (S.card + 2) * (zeroSubsets S k).card ≤ 2 * S.card.choose k := by
  have hleft := zeroSubsets_density_one_side S k hk (Nat.le_of_lt hkm)
  have hright := zeroSubsets_density_one_side S (S.card - k) (by omega)
    (Nat.sub_le _ _)
  rw [← zeroSubsets_complement S hS k (Nat.le_of_lt hkm),
    Nat.sub_sub_self (Nat.le_of_lt hkm), Nat.choose_symm (Nat.le_of_lt hkm)] at hright
  nlinarith [Nat.sub_add_cancel (Nat.le_of_lt hkm)]

/-- The factorial weight of zero-sum subalphabets has a harmonic majorant. -/
theorem zeroSubsets_weight_bound (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0)
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < S.card) :
    ((zeroSubsets S k).card : ℝ) * ((k - 1).factorial : ℝ) *
      ((S.card - k - 1).factorial : ℝ) ≤
      2 * ((S.card - 1).factorial : ℝ) / ((k : ℝ) * (S.card - k : ℕ)) := by
  have hd : ((S.card + 2 : ℕ) : ℝ) * (zeroSubsets S k).card ≤
      2 * (S.card.choose k : ℝ) := by
    exact_mod_cast zeroSubsets_density S hS k hk hkm
  have hm : 1 ≤ S.card := by omega
  have hl : 1 ≤ S.card - k := by omega
  have hfac (a : ℕ) (ha : 1 ≤ a) :
      (a.factorial : ℝ) = (a : ℝ) * ((a - 1).factorial : ℝ) := by
    have he : a - 1 + 1 = a := by omega
    exact_mod_cast (he ▸ Nat.factorial_succ (a - 1))
  have he : (S.card.choose k : ℝ) * (k.factorial : ℝ) *
      ((S.card - k).factorial : ℝ) = (S.card.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt hkm)
  rw [hfac k hk, hfac (S.card - k) hl, hfac S.card hm] at he
  have hz : (0 : ℝ) ≤ (zeroSubsets S k).card * ((k - 1).factorial : ℝ) *
      ((S.card - k - 1).factorial : ℝ) := by positivity
  have hp : (0 : ℝ) < (k : ℝ) * (S.card - k : ℕ) := by positivity
  apply (le_div_iff₀ hp).mpr
  have hw := mul_le_mul_of_nonneg_right hd
    (show (0 : ℝ) ≤ ((k - 1).factorial : ℝ) *
      ((S.card - k - 1).factorial : ℝ) * (k : ℝ) * (S.card - k : ℕ) by positivity)
  have hmpos : (0 : ℝ) < S.card := by positivity
  push_cast at hd hw
  nlinarith

/-- Nonempty proper zero-sum subalphabets. -/
def properZeroSubsets (S : Finset ℤ) : Finset (Finset ℤ) :=
  S.powerset.filter (fun A => (∑ a ∈ A, a) = 0 ∧ 0 < A.card ∧ A.card < S.card)

/-- Grouping subalphabets by cardinality. -/
theorem properZeroSubsets_sum (S : Finset ℤ) (f : ℕ → ℝ) :
    (∑ A ∈ properZeroSubsets S, f A.card) =
      ∑ k ∈ Finset.Ico 1 S.card, ((zeroSubsets S k).card : ℝ) * f k := by
  have he := Finset.sum_fiberwise_eq_sum_filter'
    (S.powerset.filter (fun A => (∑ a ∈ A, a) = 0))
    (Finset.Ico 1 S.card) Finset.card f
  have hright : ((S.powerset.filter (fun A => (∑ a ∈ A, a) = 0)).filter
      (fun A => A.card ∈ Finset.Ico 1 S.card)) = properZeroSubsets S := by
    ext A
    simp only [properZeroSubsets, Finset.mem_filter, Finset.mem_powerset, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hAs, hz⟩, hk, hkm⟩
      exact ⟨hAs, hz, by omega, hkm⟩
    · rintro ⟨hAs, hz, hk, hkm⟩
      exact ⟨⟨hAs, hz⟩, by omega, hkm⟩
  rw [hright] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro k hk
  have hf : ((S.powerset.filter (fun A => (∑ a ∈ A, a) = 0)).filter
      (fun A => A.card = k)) = zeroSubsets S k := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, zeroSubsets, Finset.mem_powersetCard]
    tauto
  rw [hf]
  simp

/-- The whole subalphabet error is bounded by a harmonic convolution. -/
theorem properZeroSubsets_weight_bound (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0) :
    (∑ A ∈ properZeroSubsets S,
      ((A.card - 1).factorial : ℝ) * ((S.card - A.card - 1).factorial : ℝ)) ≤
      ((S.card - 1).factorial : ℝ) *
        ∑ k ∈ Finset.Ico 1 S.card, 2 / ((k : ℝ) * (S.card - k : ℕ)) := by
  rw [properZeroSubsets_sum S
    (fun k => ((k - 1).factorial : ℝ) * ((S.card - k - 1).factorial : ℝ))]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨hkl, hku⟩ := Finset.mem_Ico.mp hk
  have hb := zeroSubsets_weight_bound S hS k hkl hku
  calc
    _ = ((zeroSubsets S k).card : ℝ) * ((k - 1).factorial : ℝ) *
      ((S.card - k - 1).factorial : ℝ) := by ring
    _ ≤ _ := hb
    _ = _ := by ring




def zeroPrefixes (S : Finset ℤ) : Finset (Finset ℤ) :=
  S.powerset.filter (fun A => (∑ a ∈ A, a) = 0 ∧ A ≠ S)

theorem last_zero_split (S : Finset ℤ) (hS : 1 ≤ S.card)
    (w : List ℤ) (hw : w ∈ weakWords S) :
    ∃ A ∈ zeroPrefixes S, ∃ u ∈ weakWords A, ∃ v ∈ strictWords (S \ A), w = u ++ v := by
  classical
  obtain ⟨hwperm, hwgood⟩ := Finset.mem_filter.mp hw
  have hp := mem_orderings.mp hwperm
  have hn : w.Nodup := hp.nodup_iff.mpr (Finset.nodup_toList S)
  have hlen : w.length = S.card := hp.length_eq.trans (Finset.length_toList S)
  have hwset : w.toFinset = S := by simpa using List.toFinset_eq_of_perm _ _ hp
  let Z := (Finset.range w.length).filter (fun j => (w.take j).sum = 0)
  have hZ : Z.Nonempty := ⟨0, by simp [Z]; omega⟩
  let j := Z.max' hZ
  have hjZ : j ∈ Z := Finset.max'_mem Z hZ
  have hj : j < w.length := Finset.mem_range.mp (Finset.mem_filter.mp hjZ).1
  have hjzero : (w.take j).sum = 0 := (Finset.mem_filter.mp hjZ).2
  have hjmax : ∀ i < w.length, (w.take i).sum = 0 → i ≤ j := by
    intro i hi hiz
    exact Finset.le_max' Z i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hiz⟩)
  let u := w.take j
  let v := w.drop j
  let A := u.toFinset
  have hsplit : w = u ++ v := (List.take_append_drop j w).symm
  have hu : u.Nodup := hn.take
  have hv : v.Nodup := hn.drop
  have hudis : List.Disjoint u v := by rw [hsplit] at hn; exact hn.disjoint
  have hAs : A ⊆ S := by
    intro x hx
    rw [← hwset]
    exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hx))
  have hAc : A.card = j := by
    rw [List.toFinset_card_of_nodup hu]
    exact List.length_take_of_le hj.le
  have hAz : (∑ a ∈ A, a) = 0 := by
    have he := List.sum_toFinset (fun a : ℤ => a) hu
    calc
      _ = u.sum := by simpa [A] using he
      _ = 0 := hjzero
  have hAne : A ≠ S := by intro he; have := congrArg Finset.card he; omega
  have hvset : v.toFinset = S \ A := by
    ext x
    simp only [Finset.mem_sdiff, A, List.mem_toFinset]
    rw [← hwset]
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      exact ⟨List.mem_of_mem_drop hx, fun hxu => hudis hxu hx⟩
    · rintro ⟨hxw, hxu⟩
      rw [hsplit, List.mem_append] at hxw
      exact hxw.resolve_left hxu
  have hup : u ∈ orderings A := by
    apply mem_orderings.mpr
    exact List.perm_of_nodup_nodup_toFinset_eq hu (Finset.nodup_toList A)
      (by simp [A])
  have hvp : v ∈ orderings (S \ A) := by
    apply mem_orderings.mpr
    exact List.perm_of_nodup_nodup_toFinset_eq hv (Finset.nodup_toList _)
      (by simpa using hvset)
  refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAs, hAz, hAne⟩,
    u, Finset.mem_filter.mpr ⟨hup, ?_⟩, v, Finset.mem_filter.mpr ⟨hvp, ?_⟩, hsplit⟩
  · intro k
    dsimp [u]
    rw [List.take_take]
    exact hwgood _
  · intro k hk hkv
    have hkj : j + k < w.length := by dsimp [v] at hkv; rw [List.length_drop] at hkv; omega
    have hsum : (v.take k).sum = (w.take (j + k)).sum := by
      have he := congrArg List.sum (List.take_add (l := w) (i := j) (j := k))
      simp only [List.sum_append] at he
      dsimp [v]
      omega
    rw [hsum]
    have hnonneg := hwgood (j+k)
    have hne : (w.take (j+k)).sum ≠ 0 := by
      intro hzero
      have := hjmax (j+k) hkj hzero
      omega
    omega


theorem last_zero_count_bound (S : Finset ℤ) (hS : 1 ≤ S.card) :
    weakCount S ≤ ∑ A ∈ zeroPrefixes S, weakCount A * strictCount (S \ A) := by
  classical
  let F := fun A : Finset ℤ => ((weakWords A) ×ˢ (strictWords (S \ A))).image
    (fun p => p.1 ++ p.2)
  have hsub : weakWords S ⊆ (zeroPrefixes S).biUnion F := by
    intro w hw
    obtain ⟨A, hA, u, hu, v, hv, he⟩ := last_zero_split S hS w hw
    apply Finset.mem_biUnion.mpr
    refine ⟨A, hA, Finset.mem_image.mpr ?_⟩
    exact ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, he.symm⟩
  apply (Finset.card_le_card hsub).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro A hA
  exact Finset.card_image_le.trans (by rw [Finset.card_product]; rfl)




lemma harmonic_convolution (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 1 m, (2 : ℝ) / ((k:ℝ) * (m-k:ℕ)) =
      4 * (harmonic (m-1) : ℝ) / m := by
  classical
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have heq : Finset.Ico 1 m = Finset.Icc 1 (m-1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hsum : ∑ k ∈ Finset.Ico 1 m, (k:ℝ)⁻¹ = (harmonic (m-1):ℝ) := by
    rw [heq, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hmirror : ∑ k ∈ Finset.Ico 1 m, ((m-k:ℕ):ℝ)⁻¹ =
      ∑ k ∈ Finset.Ico 1 m, (k:ℝ)⁻¹ := by
    apply Finset.sum_bij (fun k _ => m-k)
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Ico] at ha hb
      omega
    · intro b hb
      refine ⟨m-b, ?_, ?_⟩
      · simp only [Finset.mem_Ico] at hb ⊢
        omega
      · simp only [Finset.mem_Ico] at hb
        omega
    · intro k hk
      rfl
  calc
    _ = ∑ k ∈ Finset.Ico 1 m, 2 / (m:ℝ) * ((k:ℝ)⁻¹ + ((m-k:ℕ):ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk'.1)
      have hmk0 : ((m-k:ℕ):ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_ne_zero_of_lt hk'.2)
      rw [Nat.cast_sub hk'.2.le]
      have hmk0' : (m:ℝ)-(k:ℝ) ≠ 0 := by simpa [Nat.cast_sub hk'.2.le] using hmk0
      field_simp
      ring
    _ = 2 / (m:ℝ) * ((harmonic (m-1):ℝ) + harmonic (m-1)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hmirror, hsum]
    _ = _ := by ring



lemma harmonic_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  unfold harmonic
  exact_mod_cast Finset.sum_nonneg
    (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg (i+1) : (0:ℚ) ≤ _))

lemma harmonic_mono {a b : ℕ} (h : a ≤ b) : (harmonic a : ℝ) ≤ harmonic b := by
  unfold harmonic
  exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun i _ _ => inv_nonneg.mpr (Nat.cast_nonneg (i+1) : (0:ℚ) ≤ _))

lemma harmonic_div_tendsto :
    Tendsto (fun m : ℕ => (harmonic (m-1) : ℝ) / m) atTop (𝓝 0) := by
  have hconst : Tendsto (fun m : ℕ => (1:ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun m : ℕ => Real.log m / (m:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun m : ℕ => (1 + Real.log m) / (m:ℝ)) atTop (𝓝 0) := by
    simpa [add_div] using hconst.add hlog
  apply squeeze_zero (fun m => div_nonneg (harmonic_nonneg _) (Nat.cast_nonneg _)) _ hupper
  intro m
  exact div_le_div_of_nonneg_right ((harmonic_mono (Nat.sub_le _ _)).trans
    (harmonic_le_one_add_log m)) (Nat.cast_nonneg _)

lemma coefficient_tendsto :
    Tendsto (fun m : ℕ => 4 * (harmonic (m-1) : ℝ) / m) atTop (𝓝 0) := by
  simpa [mul_div_assoc] using harmonic_div_tendsto.const_mul 4

lemma uniform_bound {α : Type*} (size : α → ℕ) (R : α → ℝ)
    (htrivial : ∀ s, 1 ≤ size s → R s ≤ size s)
    (hrecurrence : ∀ (s : α) (C : ℝ), 1 ≤ size s → 0 ≤ C →
      (∀ t, 1 ≤ size t → size t < size s → R t ≤ C) →
      R s ≤ 1 + C * (4 * (harmonic (size s - 1) : ℝ) / size s)) :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ s, 1 ≤ size s → R s ≤ C := by
  have hevent : ∀ᶠ m : ℕ in atTop, 4 * (harmonic (m-1) : ℝ) / m < (1/2:ℝ) :=
    coefficient_tendsto.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let C : ℝ := max 2 N
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCN : (N:ℝ) ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC2
  refine ⟨C, hC2, ?_⟩
  have hbound : ∀ m : ℕ, ∀ s, size s = m → 1 ≤ m → R s ≤ C := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro s hs hm
      by_cases hsmall : m < N
      · calc R s ≤ (size s : ℝ) := htrivial s (hs ▸ hm)
             _ = (m:ℝ) := by rw [hs]
             _ ≤ (N:ℝ) := by exact_mod_cast Nat.le_of_lt hsmall
             _ ≤ C := hCN
      · have hmN : N ≤ m := Nat.le_of_not_gt hsmall
        have hbelow : ∀ t, 1 ≤ size t → size t < size s → R t ≤ C := by
          intro t ht hlt
          exact ih (size t) (hs ▸ hlt) t rfl ht
        have hr := hrecurrence s C (hs ▸ hm) hC0 hbelow
        rw [hs] at hr
        have hc := hN m hmN
        have hmul : C * (4 * (harmonic (m-1) : ℝ) / m) ≤ C / 2 := by
          calc _ ≤ C * (1/2) := mul_le_mul_of_nonneg_left hc.le hC0
               _ = C / 2 := by ring
        linarith
  intro s hs
  exact hbound (size s) s rfl hs

lemma recurrence_tendsto {α : Type*} (size : α → ℕ) (R : α → ℝ)
    (htrivial : ∀ s, 1 ≤ size s → R s ≤ size s)
    (hlower : ∀ s, 1 ≤ size s → 1 ≤ R s)
    (hrecurrence : ∀ (s : α) (C : ℝ), 1 ≤ size s → 0 ≤ C →
      (∀ t, 1 ≤ size t → size t < size s → R t ≤ C) →
      R s ≤ 1 + C * (4 * (harmonic (size s - 1) : ℝ) / size s))
    (s : ℕ → α) (hsize : Tendsto (fun n => size (s n)) atTop atTop) :
    Tendsto (fun n => R (s n)) atTop (𝓝 1) := by
  obtain ⟨C, hC, hbound⟩ := uniform_bound size R htrivial hrecurrence
  have hpos : ∀ᶠ n in atTop, 1 ≤ size (s n) := hsize.eventually (eventually_ge_atTop 1)
  have hupper : Tendsto (fun n => 1 + C * (4 * (harmonic (size (s n)-1) : ℝ) / size (s n)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add ((coefficient_tendsto.comp hsize).const_mul C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [hpos] with n hn using hlower (s n) hn
  · filter_upwards [hpos] with n hn
    exact hrecurrence (s n) C hn (by linarith)
      (fun t ht _ => hbound t ht)



lemma ratio_trivial {L m : ℕ} (hm : 1 ≤ m) (hL : L ≤ m.factorial) :
    (L : ℝ) / ((m-1).factorial : ℝ) ≤ m := by
  have hf : (0:ℝ) < ((m-1).factorial : ℝ) := by positivity
  apply (div_le_iff₀ hf).2
  have he : m.factorial = m * (m-1).factorial :=
    (Nat.mul_factorial_pred (by omega)).symm
  exact_mod_cast he ▸ hL


/-- The normalized number of nonnegative orderings. -/
noncomputable def wordRatio (S : Finset ℤ) : ℝ :=
  (weakCount S : ℝ) / ((S.card - 1).factorial : ℝ)

theorem zeroPrefixes_eq_insert (S : Finset ℤ) (hS : 1 ≤ S.card) :
    zeroPrefixes S = insert ∅ (properZeroSubsets S) := by
  ext A
  simp only [zeroPrefixes, properZeroSubsets, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_insert]
  constructor
  · rintro ⟨hAs, hz, hne⟩
    by_cases ha : A = ∅
    · exact Or.inl ha
    · exact Or.inr ⟨hAs, hz, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha),
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAs, hne⟩)⟩
  · rintro (rfl | ⟨hAs, hz, hpos, hlt⟩)
    · refine ⟨Finset.empty_subset _, by simp, ?_⟩
      intro he
      have := congrArg Finset.card he
      simp at this
      omega
    · exact ⟨hAs, hz, fun he => by rw [he] at hlt; omega⟩

/-- Last-zero decomposition and sparse subalphabets bound the normalized excess. -/
theorem wordRatio_recurrence (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0)
    (hm : 1 ≤ S.card) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ A : Finset ℤ, (∑ a ∈ A, a) = 0 → 1 ≤ A.card →
      A.card < S.card → wordRatio A ≤ C) :
    wordRatio S ≤ 1 + C * (4 * (harmonic (S.card - 1) : ℝ) / S.card) := by
  classical
  have hnat := last_zero_count_bound S hm
  rw [zeroPrefixes_eq_insert S hm, Finset.sum_insert (by simp [properZeroSubsets])] at hnat
  have he : weakCount (∅ : Finset ℤ) = 1 := by
    have hem : Nonnegative ([] : List ℤ) := by intro k; simp
    have hew : weakWords (∅ : Finset ℤ) = {[]} := by
      ext w
      simp only [weakWords, Finset.mem_filter, orderings]
      simp only [Finset.toList_empty, List.permutations_nil, List.toFinset_cons,
        List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false,
        Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hem⟩⟩
    rw [weakCount, hew, Finset.card_singleton]
  rw [he, one_mul, Finset.sdiff_empty] at hnat
  have hreal : (weakCount S : ℝ) ≤ (strictCount S : ℝ) +
      ∑ A ∈ properZeroSubsets S, (weakCount A : ℝ) * (strictCount (S \ A) : ℝ) := by
    exact_mod_cast hnat
  have hsbound : (strictCount S : ℝ) ≤ ((S.card - 1).factorial : ℝ) := by
    exact_mod_cast strictCount_le_factorial hS (Finset.card_pos.mp hm)
  have herr : (∑ A ∈ properZeroSubsets S,
      (weakCount A : ℝ) * (strictCount (S \ A) : ℝ)) ≤
      C * ((S.card - 1).factorial : ℝ) *
        (4 * (harmonic (S.card - 1) : ℝ) / S.card) := by
    calc
      _ ≤ ∑ A ∈ properZeroSubsets S,
          C * (((A.card - 1).factorial : ℝ) * ((S.card - A.card - 1).factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro A hA
        obtain ⟨hAs, hz, hpos, hlt⟩ := Finset.mem_filter.mp hA
        have hsubset := Finset.mem_powerset.mp hAs
        have hR := hbound A hz hpos hlt
        have hf : (0 : ℝ) < ((A.card - 1).factorial : ℝ) := by positivity
        have hw : (weakCount A : ℝ) ≤ C * ((A.card - 1).factorial : ℝ) :=
          (div_le_iff₀ hf).mp hR
        have hdcard : (S \ A).card = S.card - A.card := Finset.card_sdiff_of_subset hsubset
        have hdpos : (S \ A).Nonempty := by apply Finset.card_pos.mp; rw [hdcard]; omega
        have hdz : (∑ a ∈ S \ A, a) = 0 := by
          have he := Finset.sum_sdiff hsubset (f := fun a : ℤ => a)
          rw [hS, hz] at he
          omega
        have hd : (strictCount (S \ A) : ℝ) ≤ ((S.card - A.card - 1).factorial : ℝ) := by
          exact_mod_cast hdcard ▸ strictCount_le_factorial hdz hdpos
        have hh := mul_le_mul hw hd (by positivity : (0 : ℝ) ≤ strictCount (S \ A))
          (mul_nonneg hC hf.le)
        simpa only [mul_assoc] using hh
      _ = C * ∑ A ∈ properZeroSubsets S,
          ((A.card - 1).factorial : ℝ) * ((S.card - A.card - 1).factorial : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ C * (((S.card - 1).factorial : ℝ) *
          ∑ k ∈ Finset.Ico 1 S.card, 2 / ((k : ℝ) * (S.card - k : ℕ))) :=
        mul_le_mul_of_nonneg_left (properZeroSubsets_weight_bound S hS) hC
      _ = _ := by rw [harmonic_convolution S.card hm]; ring
  unfold wordRatio
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((S.card - 1).factorial : ℝ))).mpr
  nlinarith



lemma factorial_lt_weakCount_of_zero (S : Finset ℤ) (hS : ∑ a ∈ S, a = 0)
    (hzero : 0 ∈ S) (hsize : 2 ≤ S.card) :
    (S.card-1).factorial < weakCount S := by
  classical
  have he : ∑ a ∈ S.erase 0, a = 0 := by
    simpa using (Finset.sum_erase_add S (fun a : ℤ => a) hzero).trans hS
  have hcard : 0 < (S.erase 0).card := by
    have hh := Finset.card_erase_add_one hzero
    omega
  have hpos : 0 < (weakWords (S.erase 0)).card :=
    (Nat.factorial_pos ((S.erase 0).card-1)).trans_le
      (factorial_le_weakCount he (Finset.card_pos.mp hcard))
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  obtain ⟨hperm, hn⟩ := Finset.mem_filter.mp hw
  have hp := mem_orderings.mp hperm
  have hnone : 0 ∉ w := by
    intro hz
    have hz' := hp.mem_iff.mp hz
    simp at hz'
  have hne : w ≠ [] := by
    have hl := hp.length_eq
    simp only [Finset.length_toList] at hl
    intro hz
    simp [hz] at hl
    omega
  have hs : S.toList.Perm (0 :: (S.erase 0).toList) := by
    simpa only [Finset.insert_erase hzero] using
      (Finset.toList_insert (Finset.notMem_erase 0 S))
  have hu : (0 :: w) ∈ weakWords S := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_orderings.mpr ((hp.cons 0).trans hs.symm), ?_⟩
    intro k
    cases k with
    | zero => simp
    | succ k => simpa using hn k
  have hv : (w ++ [0]) ∈ weakWords S := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_orderings.mpr ((List.perm_append_comm).trans ((hp.cons 0).trans hs.symm)), ?_⟩
    intro k
    rw [List.take_append, List.sum_append]
    have hz : (([0] : List ℤ).take (k-w.length)).sum = 0 := by
      cases k-w.length <;> simp
    rw [hz, add_zero]
    exact hn k
  have hneq : (0 :: w) ≠ w ++ [0] := by
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons a w =>
      intro hh
      have ha : 0 = a := (List.cons.inj hh).1
      exact hnone (by simp [ha])
  exact factorial_lt_weakCount_of_two_rotations hS ⟨0, hzero⟩ hu hv hneq
    ⟨1, by simp⟩


end D5.S1.Words.Compositions.ZeroSumWordCount
