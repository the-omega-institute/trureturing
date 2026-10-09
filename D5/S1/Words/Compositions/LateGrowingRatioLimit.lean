/- GID: D5/S1/Words/Compositions/LateGrowingRatioLimit
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/LateGrowingRatioLimit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [D5/S1/Words/Compositions/PhiTailEncoding]
   utility: none
   digest: Zero-sum subset sparsity controls the excess of nonnegative word counts. -/

import D5.S1.Words.Compositions.ZeroSumWordCount
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped BigOperators Topology
open D5.S1.Words.Compositions.PhiTailEncoding
open D5.S1.Words.Compositions.ZeroSumWordCount

namespace D5.S1.Words.Compositions.LateGrowingRatioLimit
noncomputable def alphabet (n : ℕ) : Finset ℤ := Finset.Icc (1 - (n : ℤ)) (n - 1)

def reverseIndex {n : ℕ} (hn : 1 ≤ n) (j : Fin (2*n-1)) : Fin (2*n) :=
  ⟨2*n-1-j.val, by omega⟩

theorem tailWord_prefix (n k : ℕ) (p : Equiv.Perm (Fin (2*n))) (hn : 1 ≤ n)
    (hk : k < 2*n) : (tailWord n p hn |>.take k).sum = suffixBudget n k p := by
  classical
  change ((List.ofFn fun j : Fin (2*n-1) => ((p (reverseIndex hn j)).val : ℤ) - n).take k).sum = _
  rw [List.sum_take_ofFn]
  simp only [suffixBudget, ← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => reverseIndex hn j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    dsimp [reverseIndex]
    omega
  · intro i hi j hj he
    apply Fin.ext
    have h := congrArg Fin.val he
    dsimp [reverseIndex] at h
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨2*n-1-i.val, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · apply Fin.ext
      dsimp [reverseIndex]
      omega
  · intro i hi
    rfl

theorem tailWord_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (fun p : {p : Equiv.Perm (Fin (2*n)) //
      ∀ i : Fin (2*n), i.val = 0 → (p i).val = 0} => tailWord n p.val hn) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ he
  apply Subtype.ext
  change p = q
  apply Equiv.ext
  intro i
  by_cases hi : i.val = 0
  · apply Fin.ext
    rw [hp i hi, hq i hi]
  · have hef := List.ofFn_injective he
    have hj : 2*n-1-i.val < 2*n-1 := by omega
    have h := congrFun hef ⟨2*n-1-i.val, hj⟩
    have hrev : reverseIndex hn ⟨2*n-1-i.val, hj⟩ = i := by
      apply Fin.ext
      dsimp [reverseIndex]
      omega
    change ((p (reverseIndex hn ⟨2*n-1-i.val, hj⟩)).val : ℤ) - n =
      ((q (reverseIndex hn ⟨2*n-1-i.val, hj⟩)).val : ℤ) - n at h
    rw [hrev] at h
    apply Fin.ext
    omega

theorem tailWord_nodup (n : ℕ) (p : Equiv.Perm (Fin (2*n))) (hn : 1 ≤ n) :
    (tailWord n p hn).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  have hp : p (reverseIndex hn i) = p (reverseIndex hn j) := by
    apply Fin.ext
    change ((p (reverseIndex hn i)).val : ℤ) - n =
      ((p (reverseIndex hn j)).val : ℤ) - n at hij
    omega
  have hidx := congrArg Fin.val (p.injective hp)
  apply Fin.ext
  dsimp [reverseIndex] at hidx
  omega

theorem tailWord_mem_alphabet (n : ℕ) (p : Equiv.Perm (Fin (2*n))) (hn : 1 ≤ n)
    (hp : ∀ i : Fin (2*n), i.val = 0 → (p i).val = 0) (x : ℤ) :
    x ∈ tailWord n p hn ↔ x ∈ alphabet n := by
  classical
  change x ∈ List.ofFn (fun j : Fin (2*n-1) => ((p (reverseIndex hn j)).val : ℤ) - n) ↔ _
  rw [List.mem_ofFn]
  simp only [alphabet, Finset.mem_Icc]
  constructor
  · rintro ⟨j, rfl⟩
    have hidx : (reverseIndex hn j).val ≠ 0 := by dsimp [reverseIndex]; omega
    have hval : (p (reverseIndex hn j)).val ≠ 0 := by
      intro hz
      let z : Fin (2*n) := ⟨0, by omega⟩
      have hpz : p z = z := Fin.ext (hp z rfl)
      have he : p (reverseIndex hn j) = z := Fin.ext hz
      have hij := congrArg Fin.val (p.injective (he.trans hpz.symm))
      exact hidx hij
    have hv := (p (reverseIndex hn j)).isLt
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    have hy : 0 < x + (n : ℤ) ∧ x + (n : ℤ) < 2*n := by omega
    let y : Fin (2*n) := ⟨(x + (n : ℤ)).toNat, by omega⟩
    let i := p.symm y
    have hpi : p i = y := p.apply_symm_apply y
    have hi : i.val ≠ 0 := by
      intro hi
      have hz := hp i hi
      have hv := congrArg Fin.val hpi
      dsimp [y] at hv
      omega
    refine ⟨⟨2*n-1-i.val, by omega⟩, ?_⟩
    have hr : reverseIndex hn ⟨2*n-1-i.val, by omega⟩ = i := by
      apply Fin.ext; dsimp [reverseIndex]; omega
    rw [hr, hpi]
    dsimp [y]
    omega

theorem tailWord_perm_alphabet (n : ℕ) (p : Equiv.Perm (Fin (2*n))) (hn : 1 ≤ n)
    (hp : ∀ i : Fin (2*n), i.val = 0 → (p i).val = 0) :
    (tailWord n p hn).Perm (alphabet n).toList := by
  apply (List.perm_ext_iff_of_nodup (tailWord_nodup n p hn) (Finset.nodup_toList _)).mpr
  intro x
  simp only [Finset.mem_toList]
  exact tailWord_mem_alphabet n p hn hp x

theorem alphabet_card (n : ℕ) (hn : 1 ≤ n) : (alphabet n).card = 2*n-1 := by
  rw [alphabet, Int.card_Icc]
  omega

def wordPermutation {n : ℕ} (hn : 1 ≤ n) (w : List ℤ)
    (hw : w.Perm (alphabet n).toList) : Fin (2*n) → Fin (2*n) := fun i =>
  if hi : i.val = 0 then ⟨0, by omega⟩ else
    let j : Fin w.length := ⟨2*n-1-i.val, by
      have hlen := hw.length_eq
      rw [Finset.length_toList, alphabet_card n hn] at hlen
      omega⟩
    ⟨(w.get j + (n : ℤ)).toNat, by
      have hm := hw.mem_iff.mp (List.get_mem w j)
      simp only [Finset.mem_toList, alphabet, Finset.mem_Icc] at hm
      omega⟩

theorem wordPermutation_injective {n : ℕ} (hn : 1 ≤ n) (w : List ℤ)
    (hw : w.Perm (alphabet n).toList) : Function.Injective (wordPermutation hn w hw) := by
  have hlen := hw.length_eq
  rw [Finset.length_toList, alphabet_card n hn] at hlen
  have hnodup := hw.nodup_iff.mpr (Finset.nodup_toList (alphabet n))
  intro i j he
  have hv := congrArg Fin.val he
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · apply Fin.ext; omega
  · simp [wordPermutation, hi, hj] at hv
    have hm := hw.mem_iff.mp (List.get_mem w ⟨2*n-1-j.val, by omega⟩)
    simp only [Finset.mem_toList, alphabet, Finset.mem_Icc, List.get_eq_getElem] at hm
    omega
  · simp [wordPermutation, hi, hj] at hv
    have hm := hw.mem_iff.mp (List.get_mem w ⟨2*n-1-i.val, by omega⟩)
    simp only [Finset.mem_toList, alphabet, Finset.mem_Icc, List.get_eq_getElem] at hm
    omega
  · simp [wordPermutation, hi, hj] at hv
    have hmi := hw.mem_iff.mp (List.get_mem w ⟨2*n-1-i.val, by omega⟩)
    have hmj := hw.mem_iff.mp (List.get_mem w ⟨2*n-1-j.val, by omega⟩)
    simp only [Finset.mem_toList, alphabet, Finset.mem_Icc, List.get_eq_getElem] at hmi hmj
    have hh : w.get ⟨2*n-1-i.val, by omega⟩ = w.get ⟨2*n-1-j.val, by omega⟩ := by simpa only [List.get_eq_getElem] using (show w[2*n-1-i.val] = w[2*n-1-j.val] from by omega)
    have hij := congrArg Fin.val (hnodup.injective_get hh)
    change 2*n-1-i.val = 2*n-1-j.val at hij
    apply Fin.ext
    omega

noncomputable def decodeWord {n : ℕ} (hn : 1 ≤ n) (w : List ℤ)
    (hw : w.Perm (alphabet n).toList) : Equiv.Perm (Fin (2*n)) :=
  Equiv.ofBijective (wordPermutation hn w hw)
    ⟨wordPermutation_injective hn w hw,
      Finite.surjective_of_injective (wordPermutation_injective hn w hw)⟩

theorem decodeWord_fixed {n : ℕ} (hn : 1 ≤ n) (w : List ℤ)
    (hw : w.Perm (alphabet n).toList) :
    ∀ i : Fin (2*n), i.val = 0 → ((decodeWord hn w hw) i).val = 0 := by
  intro i hi
  change (wordPermutation hn w hw i).val = 0
  simp [wordPermutation, hi]

theorem tailWord_decodeWord {n : ℕ} (hn : 1 ≤ n) (w : List ℤ)
    (hw : w.Perm (alphabet n).toList) : tailWord n (decodeWord hn w hw) hn = w := by
  have hlen := hw.length_eq
  rw [Finset.length_toList, alphabet_card n hn] at hlen
  apply List.ext_getElem
  · rw [tailWord_length, hlen]
  · intro j hj hjw
    have hj' : j < 2*n-1 := by rw [tailWord_length] at hj; exact hj
    simp only [tailWord, List.getElem_ofFn]
    change (((decodeWord hn w hw) (reverseIndex hn ⟨j, hj'⟩)).val : ℤ) - n = w[j]
    have hidx : (reverseIndex hn ⟨j, hj'⟩).val ≠ 0 := by dsimp [reverseIndex]; omega
    have hh : 2*n-1-(reverseIndex hn ⟨j, hj'⟩).val = j := by dsimp [reverseIndex]; omega
    have hm := hw.mem_iff.mp (List.getElem_mem hjw)
    simp only [Finset.mem_toList, alphabet, Finset.mem_Icc] at hm
    change ((wordPermutation hn w hw (reverseIndex hn ⟨j, hj'⟩)).val : ℤ) - n = w[j]
    simp [wordPermutation, hidx, hh]
    omega

theorem alphabet_sum (n : ℕ) : ∑ x ∈ alphabet n, x = 0 := by
  classical
  have he : (∑ x ∈ alphabet n, x) = ∑ x ∈ alphabet n, -x := by
    apply Finset.sum_bij (fun x _ => -x)
    · intro x hx
      simp only [alphabet, Finset.mem_Icc] at *
      constructor <;> omega
    · intro x hx y hy hxy
      omega
    · intro y hy
      refine ⟨-y, ?_, by simp⟩
      simp only [alphabet, Finset.mem_Icc] at *
      constructor <;> omega
    · intro x hx
      simp
  rw [Finset.sum_neg_distrib] at he
  omega

theorem tailWord_nonnegative_iff (n : ℕ) (p : Equiv.Perm (Fin (2*n)))
    (hn : 1 ≤ n) : ZeroSumWordCount.Nonnegative (tailWord n p hn) ↔
      ∀ k ∈ Finset.Ico 1 (2*n), 0 ≤ suffixBudget n k p := by
  constructor
  · intro h k hk
    rw [← tailWord_prefix n k p hn (Finset.mem_Ico.mp hk).2]
    exact h k
  · intro h k
    by_cases hk : k < 2*n
    · by_cases hk0 : k = 0
      · subst k; simp
      · rw [tailWord_prefix n k p hn hk]
        exact h k (Finset.mem_Ico.mpr ⟨by omega, hk⟩)
    · have hlen : (tailWord n p hn).length ≤ k := by rw [tailWord_length]; omega
      rw [List.take_of_length_le hlen]
      have hm := h (2*n-1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      rw [← tailWord_prefix n (2*n-1) p hn (by omega)] at hm
      simpa only [← tailWord_length n p hn, List.take_length] using hm

theorem phi_card_eq_weakCount (n : ℕ) (hn : 1 ≤ n) :
    (phi n).card = ZeroSumWordCount.weakCount (alphabet n) := by
  classical
  unfold ZeroSumWordCount.weakCount
  apply Finset.card_bij (fun p _ => tailWord n p hn)
  · intro p hp
    have hadm : admissible n p := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    exact ⟨ZeroSumWordCount.mem_orderings.mpr
      (tailWord_perm_alphabet n p hn hadm.1),
      (tailWord_nonnegative_iff n p hn).mpr hadm.2⟩
  · intro p hp q hq he
    have hp0 := ((Finset.mem_filter.mp hp).2 : admissible n p).1
    have hq0 := ((Finset.mem_filter.mp hq).2 : admissible n q).1
    have hh : (⟨p, hp0⟩ : {p : Equiv.Perm (Fin (2*n)) //
      ∀ i : Fin (2*n), i.val = 0 → (p i).val = 0}) = ⟨q, hq0⟩ :=
      tailWord_injective n hn he
    exact congrArg Subtype.val hh
  · intro w hw
    have hperm := ZeroSumWordCount.mem_orderings.mp (Finset.mem_filter.mp hw).1
    have hnonneg := (Finset.mem_filter.mp hw).2
    refine ⟨decodeWord hn w hperm, ?_, tailWord_decodeWord hn w hperm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, decodeWord_fixed hn w hperm, ?_⟩
    apply (tailWord_nonnegative_iff n (decodeWord hn w hperm) hn).mp
    simpa only [tailWord_decodeWord] using hnonneg




/-- The Shah–Kiselev ratio converges from above. -/
def claim : Prop :=
  Filter.Tendsto (fun n : ℕ => ((phi n).card : ℝ) / ((2 * n - 2).factorial : ℝ))
    Filter.atTop (nhds 1) ∧
      ∀ n : ℕ, 2 ≤ n → (2 * n - 2).factorial < (phi n).card

/-- Convergence and strict excess of the admissible permutation ratio. -/
theorem result : claim := by
  let size := fun S : {S : Finset ℤ // (∑ a ∈ S, a) = 0} => S.val.card
  let R := fun S : {S : Finset ℤ // (∑ a ∈ S, a) = 0} => wordRatio S.val
  have htrivial : ∀ S, 1 ≤ size S → R S ≤ size S := by
    intro S hS
    exact ratio_trivial hS (weakCount_le_factorial S.val)
  have hlower : ∀ S, 1 ≤ size S → 1 ≤ R S := by
    intro S hS
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((S.val.card-1).factorial : ℝ))).mpr
    simp only [one_mul]
    exact_mod_cast factorial_le_weakCount S.property (Finset.card_pos.mp hS)
  have hrecurrence : ∀ S C, 1 ≤ size S → 0 ≤ C →
      (∀ T, 1 ≤ size T → size T < size S → R T ≤ C) →
      R S ≤ 1 + C * (4 * (harmonic (size S - 1) : ℝ) / size S) := by
    intro S C hm hC hbelow
    apply wordRatio_recurrence S.val S.property hm C hC
    intro A hz hpos hlt
    exact hbelow ⟨A, hz⟩ hpos hlt
  let family := fun n : ℕ => (⟨alphabet n, alphabet_sum n⟩ :
    {S : Finset ℤ // (∑ a ∈ S, a) = 0})
  have hsize : Tendsto (fun n => size (family n)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with n hn
    change n ≤ (alphabet n).card
    rw [alphabet_card n hn]
    omega
  constructor
  · have hlim := recurrence_tendsto size R htrivial hlower hrecurrence family hsize
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    change wordRatio (alphabet n) = _
    rw [wordRatio, alphabet_card n hn, phi_card_eq_weakCount n hn]
    congr 2
  · intro n hn
    rw [phi_card_eq_weakCount n (by omega)]
    have hz : (0 : ℤ) ∈ alphabet n := by simp only [alphabet, Finset.mem_Icc]; omega
    have hs : 2 ≤ (alphabet n).card := by rw [alphabet_card n (by omega)]; omega
    have h := factorial_lt_weakCount_of_zero (alphabet n) (alphabet_sum n) hz hs
    rwa [alphabet_card n (by omega), show 2*n-1-1 = 2*n-2 by omega] at h


end D5.S1.Words.Compositions.LateGrowingRatioLimit
