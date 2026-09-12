/- GID: D5/S3/Quantum/StationaryPreparation/PaddingMemory
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite padding memories have exact product-minus-head cardinality and normalized transition probabilities. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit


set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingMemory

open D5.S1.Ledger.BoundedTimeSlice

variable {I : Type*} [Fintype I]

def zeroTail (c : I → ℕ) : TailBox c := fun _ => ⟨0, Nat.zero_lt_succ _⟩

abbrev PositiveTail (c : I → ℕ) := {b : TailBox c // b ≠ zeroTail c}

instance positiveTailFintype (c : I → ℕ) : Fintype (PositiveTail c) :=
  Fintype.ofFinite _

abbrev PaddingMemory (H : ℕ) (c : I → ℕ) := Option (PositiveTail c × Fin (H + 1))

theorem tail_sum_eq_zero_iff (c : I → ℕ) (b : TailBox c) :
    tailSum b = 0 ↔ b = zeroTail c := by
  constructor
  · intro h
    have hz : ∀ i, (b i).val = 0 := by
      simpa only [tailSum, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
        using h
    funext i
    exact Fin.ext (hz i)
  · rintro rfl
    simp [tailSum, zeroTail]

theorem positive_tail_sum (c : I → ℕ) (b : PositiveTail c) :
    0 < tailSum b.val :=
  Nat.pos_of_ne_zero (fun h => b.property ((tail_sum_eq_zero_iff c b.val).mp h))

theorem positive_tail_card (c : I → ℕ) :
    Fintype.card (PositiveTail c) = (∏ i, (c i + 1)) - 1 := by
  classical
  simpa [PositiveTail, TailBox, Fintype.card_pi] using
    Fintype.card_subtype_compl (fun b : TailBox c => b = zeroTail c)

theorem padding_memory_card (H : ℕ) (c : I → ℕ) :
    Fintype.card (PaddingMemory H c) = (H + 1) * (∏ i, (c i + 1)) - H := by
  classical
  have hp : 1 ≤ ∏ i, (c i + 1) := Finset.one_le_prod fun _ _ => by omega
  have hmul := Nat.mul_le_mul_left (H + 1) hp
  simp only [PaddingMemory, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, positive_tail_card]
  rw [Nat.mul_comm (_ - 1), Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev TailAlphabet (head : A) := {i : A // i ≠ head}

abbrev OccupationMemory (a : Multiset A) (head : A) :=
  PaddingMemory (a.count head) (fun i : TailAlphabet head => a.count i.val)

theorem occupation_memory_card (a : Multiset A) (head : A) :
    Fintype.card (OccupationMemory a head) =
      (∏ i : A, (a.count i + 1)) - a.count head := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i : A => a.count i + 1) head]
  exact padding_memory_card _ _

theorem maximal_head_exists [Nonempty A] (a : Multiset A) :
    ∃ head : A, a.count head = Finset.univ.sup a.count := by
  have h := Finset.sup_mem_of_nonempty (f := a.count)
    (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
  obtain ⟨head, _, hh⟩ := h
  exact ⟨head, hh⟩

def occupationMemoryEquiv (a : Multiset A) (head : A)
    (hh : a.count head = Finset.univ.sup a.count) :
    OccupationMemory a head ≃
      Fin ((∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count) :=
  (Fintype.equivFin _).trans (finCongr (by rw [occupation_memory_card, hh]))

theorem proposed_dimension_pos [Nonempty A] (a : Multiset A) :
    0 < (∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count := by
  obtain ⟨head, hh⟩ := maximal_head_exists a
  rw [← hh, ← occupation_memory_card a head]
  exact Fintype.card_pos_iff.mpr ⟨none⟩

end D5.S3.Quantum.StationaryPreparation.PaddingMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingMemory

open D5.S1.Ledger.BoundedTimeSlice

variable {I : Type*} [Fintype I] [DecidableEq I]

def decrement (c : I → ℕ) (b : TailBox c) (i : I) : TailBox c :=
  Function.update b i ⟨(b i).val - 1,
    lt_of_le_of_lt (Nat.sub_le _ _) (b i).isLt⟩

@[simp] theorem decrement_same (c : I → ℕ) (b : TailBox c) (i : I) :
    (decrement c b i i).val = (b i).val - 1 := by simp [decrement]

@[simp] theorem decrement_other (c : I → ℕ) (b : TailBox c) (i j : I) (hji : j ≠ i) :
    decrement c b i j = b j := by simp [decrement, hji]

theorem decrement_sum (c : I → ℕ) (b : TailBox c) (i : I) (hi : 0 < (b i).val) :
    tailSum (decrement c b i) + 1 = tailSum b := by
  have he (j : I) : (decrement c b i j).val + (if j = i then 1 else 0) = (b j).val := by
    by_cases h : j = i
    · subst j
      simp only [decrement_same, if_pos rfl]
      exact Nat.sub_add_cancel hi
    · simp [decrement_other, h]
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun j _ => he j)
  simpa [Finset.sum_add_distrib, tailSum] using hs

theorem decrement_injective (c : I → ℕ) (b e : TailBox c) (i : I)
    (hb : 0 < (b i).val) (he : 0 < (e i).val)
    (h : decrement c b i = decrement c e i) : b = e := by
  funext j
  apply Fin.ext
  have hh := congrArg (fun d : TailBox c => (d j).val) h
  by_cases hji : j = i
  · subst j
    simp only [decrement_same] at hh
    omega
  · simpa [decrement_other, hji] using hh

def decrementPositive (c : I → ℕ) (b : PositiveTail c) (i : I)
    (hi : 0 < (b.val i).val) (hR : 1 < tailSum b.val) : PositiveTail c :=
  ⟨decrement c b.val i, by
    intro hz
    have hzero := (tail_sum_eq_zero_iff c _).mpr hz
    have hs := decrement_sum c b.val i hi
    omega⟩

def headPredecessor {H : ℕ} (h : Fin (H + 1)) : Fin (H + 1) :=
  ⟨h.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) h.isLt⟩

def paddingNext (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → PaddingMemory H c
  | none, _ => none
  | some (b, h), none => some (b, headPredecessor h)
  | some (b, h), some i =>
      if hi : 0 < (b.val i).val then
        if hR : 1 < tailSum b.val then some (decrementPositive c b i hi hR, h)
        else none
      else none

theorem tail_coordinate_le_sum (c : I → ℕ) (b : TailBox c) (i : I) :
    (b i).val ≤ tailSum b :=
  Finset.single_le_sum (f := fun j => (b j).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem sum_one_coordinate (c : I → ℕ) (b : TailBox c)
    (hs : tailSum b = 1) (i : I) (hi : 0 < (b i).val) :
    ∀ j, (b j).val = if j = i then 1 else 0 := by
  have hbi : (b i).val = 1 := by have := tail_coordinate_le_sum c b i; omega
  intro j
  by_cases hji : j = i
  · subst j
    simp [hbi]
  · have hsum : (b i).val + (b j).val ≤ tailSum b := by
      have hm : ({i, j} : Finset I) ⊆ Finset.univ := Finset.subset_univ _
      have hh := Finset.sum_le_sum_of_subset_of_nonneg hm
        (fun k _ _ => Nat.zero_le ((b k).val))
      simpa [Finset.sum_pair (Ne.symm hji), tailSum] using hh
    simp only [if_neg hji]
    omega

theorem sum_one_unique (c : I → ℕ) (b e : TailBox c)
    (hb : tailSum b = 1) (he : tailSum e = 1) (i : I)
    (hbi : 0 < (b i).val) (hei : 0 < (e i).val) : b = e := by
  funext j
  apply Fin.ext
  rw [sum_one_coordinate c b hb i hbi j, sum_one_coordinate c e he i hei j]

end D5.S3.Quantum.StationaryPreparation.PaddingMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.PaddingMemory

/-- For R>=2 these are the exact head and tail probabilities of padding. -/
def headProbability (h R : ℕ) : ℝ := (h : ℝ) / ((h : ℝ) + R - 1)

def tailProbability (h R d : ℕ) : ℝ :=
  (d : ℝ) * ((R : ℝ) - 1) / ((R : ℝ) * ((h : ℝ) + R - 1))

theorem padding_probabilities_sum {I : Type*} [Fintype I]
    (d : I → ℕ) (h : ℕ) (hR : 2 ≤ ∑ i, d i) :
    headProbability h (∑ i, d i) + ∑ i, tailProbability h (∑ i, d i) (d i) = 1 := by
  let R := ∑ i, d i
  have hpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hden : (0 : ℝ) < (h : ℝ) + R - 1 := by
    have hr : (2 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  change (h : ℝ) / ((h : ℝ) + R - 1) +
    ∑ i, (d i : ℝ) * ((R : ℝ) - 1) /
      ((R : ℝ) * ((h : ℝ) + R - 1)) = 1
  rw [← Finset.sum_div, ← Finset.sum_mul, ← Nat.cast_sum]
  change (h : ℝ) / ((h : ℝ) + R - 1) +
    (R : ℝ) * ((R : ℝ) - 1) / ((R : ℝ) * ((h : ℝ) + R - 1)) = 1
  field_simp
  <;> nlinarith

end D5.S3.Quantum.StationaryPreparation.PaddingMemory
