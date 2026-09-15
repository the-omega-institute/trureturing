/- GID: D5/S3/Quantum/StationaryPreparation/PaddingTransition
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingTransition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recoverable last-tail padding transition. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PaddingTransition

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v w

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

abbrev Box (a : Multiset σ) := TailBox a.count

abbrev TailAlphabet (head : σ) := {i : σ // i ≠ head}

abbrev Tail (a : Multiset σ) (head : σ) :=
  TailBox (fun i : TailAlphabet head => a.count i.val)

abbrev PositiveTail (a : Multiset σ) (head : σ) := {b : Tail a head // b ≠ 0}

abbrev K (a : Multiset σ) (head : σ) :=
  Option (PositiveTail a head × Fin (a.count head + 1))

instance memoryDecidableEq (a : Multiset σ) (head : σ) : DecidableEq (K a head) :=
  Classical.decEq _

def N (a : Multiset σ) : ℕ :=
  (∏ i : σ, (a.count i + 1)) - Finset.univ.sup a.count

end

section
variable {I : Type u} [Fintype I] [DecidableEq I]

abbrev zeroTail (c : I → ℕ) : TailBox c := 0

abbrev PaddingTail (c : I → ℕ) := {b : TailBox c // b ≠ zeroTail c}

abbrev PaddingMemory (H : ℕ) (c : I → ℕ) := Option (PaddingTail c × Fin (H + 1))

end

section
variable {A : Type u} [Fintype A] [DecidableEq A]

def occupationMemoryEquiv (a : Multiset A) (head : A)
    (hh : a.count head = Finset.univ.sup a.count) :
    K a head ≃
      Fin ((∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count) := by
  have positive_tail_card {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) :
      Fintype.card (PaddingTail c) = (∏ i, (c i + 1)) - 1 := by
    classical
    simpa [PaddingTail, TailBox, Fintype.card_pi] using
      Fintype.card_subtype_compl (fun b : TailBox c => b = zeroTail c)
  have padding_memory_card {I : Type u} [Fintype I] [DecidableEq I] (H : ℕ) (c : I → ℕ) :
      Fintype.card (PaddingMemory H c) = (H + 1) * (∏ i, (c i + 1)) - H := by
    classical
    have hp : 1 ≤ ∏ i, (c i + 1) := Finset.one_le_prod fun _ _ => by omega
    have hmul := Nat.mul_le_mul_left (H + 1) hp
    simp only [PaddingMemory, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, positive_tail_card]
    rw [Nat.mul_comm (_ - 1), Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  have occupation_memory_card {A : Type u} [Fintype A] [DecidableEq A] (a : Multiset A) (head : A) :
      Fintype.card (K a head) =
        (∏ i : A, (a.count i + 1)) - a.count head := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i : A => a.count i + 1) head]
    exact padding_memory_card _ _

  exact (Fintype.equivFin _).trans (finCongr (by rw [occupation_memory_card, hh]))

end

section
variable {I : Type u} [Fintype I] [DecidableEq I]

def decrement (c : I → ℕ) (b : TailBox c) (i : I) : TailBox c :=
  Function.update b i ⟨(b i).val - 1,
    lt_of_le_of_lt (Nat.sub_le _ _) (b i).isLt⟩

def decrementPositive (c : I → ℕ) (b : PaddingTail c) (i : I)
    (hi : 0 < (b.val i).val) (hR : 1 < tailSum b.val) : PaddingTail c := by
  have tail_sum_eq_zero_iff {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) :
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
  have decrement_same {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i : I) :
      (decrement c b i i).val = (b i).val - 1 := by simp [decrement]
  have decrement_other {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i j : I) (hji : j ≠ i) :
      decrement c b i j = b j := by simp [decrement_same, decrement, hji]
  have decrement_sum {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i : I) (hi : 0 < (b i).val) :
      tailSum (decrement c b i) + 1 = tailSum b := by
    have he (j : I) : (decrement c b i j).val + (if j = i then 1 else 0) = (b j).val := by
      by_cases h : j = i
      · subst j
        simp only [decrement_same, if_pos rfl]
        exact Nat.sub_add_cancel hi
      · simp [decrement_same, decrement_other, decrement_other, h]
    have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun j _ => he j)
    simpa [decrement_same, decrement_other, Finset.sum_add_distrib, tailSum] using hs

  exact ⟨decrement c b.val i, by
      intro hz
      have hzero := (tail_sum_eq_zero_iff c _).mpr hz
      have hs := decrement_sum c b.val i hi
      omega⟩

end

def headPredecessor {H : ℕ} (h : Fin (H + 1)) : Fin (H + 1) :=
  ⟨h.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) h.isLt⟩

section
variable {I : Type u} [Fintype I] [DecidableEq I]

def paddingNext (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → PaddingMemory H c
  | none, _ => none
  | some (b, h), none => some (b, headPredecessor h)
  | some (b, h), some i =>
      if hi : 0 < (b.val i).val then
        if hR : 1 < tailSum b.val then some (decrementPositive c b i hi hR, h)
        else none
      else none

end

def headProbability (h R : ℕ) : ℝ := (h : ℝ) / ((h : ℝ) + R - 1)

def tailProbability (h R d : ℕ) : ℝ :=
  (d : ℝ) * ((R : ℝ) - 1) / ((R : ℝ) * ((h : ℝ) + R - 1))

section
variable {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K]

def weightedMatrix (next : K → A → K) (p : K → A → ℝ) : Matrix (A × K) K ℂ :=
  fun q j => if next j q.1 = q.2 then (Real.sqrt (p j q.1) : ℂ) else 0

end

section
variable {I : Type u} [Fintype I] [DecidableEq I]

def paddingProbability (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → ℝ
  | none, none => 1
  | none, some _ => 0
  | some (b, h), none =>
      if tailSum b.val = 1 then (if h.val = 0 then 0 else 1)
      else headProbability h.val (tailSum b.val)
  | some (b, h), some i =>
      if tailSum b.val = 1 then (if h.val = 0 then ((b.val i).val : ℝ) else 0)
      else tailProbability h.val (tailSum b.val) (b.val i).val

private theorem padding_predecessor_unique (H : ℕ) (c : I → ℕ) :
    ∀ s t i, paddingProbability H c s i ≠ 0 → paddingProbability H c t i ≠ 0 →
      paddingNext H c s i = paddingNext H c t i → s = t := by
  have tail_sum_eq_zero_iff (b : TailBox c) :
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
  have positive_tail_sum (b : PaddingTail c) :
      0 < tailSum b.val :=
    Nat.pos_of_ne_zero (fun h => b.property ((tail_sum_eq_zero_iff b.val).mp h))
  have decrement_same (b : TailBox c) (i : I) :
      (decrement c b i i).val = (b i).val - 1 := by simp [decrement]
  have decrement_other (b : TailBox c) (i j : I) (hji : j ≠ i) :
      decrement c b i j = b j := by simp [decrement_same, decrement, hji]
  have decrement_injective (b e : TailBox c) (i : I)
      (hb : 0 < (b i).val) (he : 0 < (e i).val)
      (h : decrement c b i = decrement c e i) : b = e := by
    funext j
    apply Fin.ext
    have hh := congrArg (fun d : TailBox c => (d j).val) h
    by_cases hji : j = i
    · subst j
      simp only [decrement_same] at hh
      omega
    · simpa [decrement_same, decrement_other, decrement_other, hji] using hh
  have tail_coordinate_le_sum (b : TailBox c) (i : I) :
      (b i).val ≤ tailSum b :=
    Finset.single_le_sum (f := fun j => (b j).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have sum_one_coordinate (b : TailBox c)
      (hs : tailSum b = 1) (i : I) (hi : 0 < (b i).val) :
      ∀ j, (b j).val = if j = i then 1 else 0 := by
    have hbi : (b i).val = 1 := by have := tail_coordinate_le_sum b i; omega
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
  have sum_one_unique (b e : TailBox c)
      (hb : tailSum b = 1) (he : tailSum e = 1) (i : I)
      (hbi : 0 < (b i).val) (hei : 0 < (e i).val) : b = e := by
    funext j
    apply Fin.ext
    rw [sum_one_coordinate b hb i hbi j, sum_one_coordinate e he i hei j]
  have positive_head_of_probability
      (b : PaddingTail c) (h : Fin (H + 1))
      (hp : paddingProbability H c (some (b, h)) none ≠ 0) : 0 < h.val := by
    by_contra! hn
    have hh : h.val = 0 := by omega
    simp [paddingProbability, headProbability, hh] at hp
  have positive_tail_of_probability
      (b : PaddingTail c) (h : Fin (H + 1)) (i : I)
      (hp : paddingProbability H c (some (b, h)) (some i) ≠ 0) :
      0 < (b.val i).val ∧ (tailSum b.val = 1 → h.val = 0) := by
    constructor
    · by_contra! hn
      have hz : (b.val i).val = 0 := by omega
      simp [paddingProbability, tailProbability, hz] at hp
    · intro hr
      by_contra hh
      simp [paddingProbability, hr, hh] at hp

  intro s t i hs ht heq
  cases i with
  | none =>
    cases s with
    | none => cases t <;> simp_all [paddingNext]
    | some s =>
      cases t with
      | none => simp [paddingNext] at heq
      | some t =>
        rcases s with ⟨b, h⟩
        rcases t with ⟨e, g⟩
        have hh := positive_head_of_probability b h hs
        have hg := positive_head_of_probability e g ht
        have hp := Option.some.inj heq
        have hb : b = e := congrArg Prod.fst hp
        have hv := congrArg (fun p : PaddingTail c × Fin (H + 1) => p.2.val) hp
        have hhg : h = g := by
          apply Fin.ext
          change h.val - 1 = g.val - 1 at hv
          omega
        simp [hb, hhg]
  | some i =>
    cases s with
    | none => exact False.elim (hs rfl)
    | some s =>
      cases t with
      | none => exact False.elim (ht rfl)
      | some t =>
        rcases s with ⟨b, h⟩
        rcases t with ⟨e, g⟩
        obtain ⟨hbi, hbh⟩ := positive_tail_of_probability b h i hs
        obtain ⟨hei, heh⟩ := positive_tail_of_probability e g i ht
        have hbpos := positive_tail_sum b
        have hepos := positive_tail_sum e
        simp only [paddingNext, dif_pos hbi, dif_pos hei] at heq
        by_cases hbR : 1 < tailSum b.val
        · rw [dif_pos hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · rw [dif_pos heR] at heq
            have hp := Option.some.inj heq
            have hhg : h = g := congrArg Prod.snd hp
            have hdec := congrArg (fun p : PaddingTail c × Fin (H + 1) => p.1.val) hp
            have hbe : b = e := Subtype.ext (decrement_injective b.val e.val i hbi hei hdec)
            simp [hbe, hhg]
          · simp [heR] at heq
        · rw [dif_neg hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · simp [heR] at heq
          · have hb1 : tailSum b.val = 1 := by omega
            have he1 : tailSum e.val = 1 := by omega
            have hbe : b = e := Subtype.ext (sum_one_unique b.val e.val hb1 he1 i hbi hei)
            have hhg : h = g := Fin.ext ((hbh hb1).trans (heh he1).symm)
            simp [hbe, hhg]

end

section
variable {I : Type u} [Fintype I] [DecidableEq I] {A : Type v} [Fintype A] [DecidableEq A] {K : Type w} [Fintype K] [DecidableEq K]

def relabelNext (H : ℕ) (c : I → ℕ) (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) :
    K → A → K := fun j i => eK (paddingNext H c (eK.symm j) (eA.symm i))

def relabelProbability (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : K → A → ℝ :=
  fun j i => paddingProbability H c (eK.symm j) (eA.symm i)

def relabelMatrix (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : Matrix (A × K) K ℂ :=
  weightedMatrix (relabelNext H c eA eK) (relabelProbability H c eA eK)

end

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def W (a : Multiset σ) (head : σ) : Matrix (σ × K a head) (K a head) ℂ :=
  relabelMatrix (a.count head) (fun i : TailAlphabet head => a.count i.val)
    (Equiv.optionSubtypeNe head) (Equiv.refl _)

theorem W_gram (a : Multiset σ) (head : σ) :
    (W a head).conjTranspose * W a head = 1 := by
  let H := a.count head
  let c := fun i : TailAlphabet head => a.count i.val

  have sqrt_gram (r : ℝ) (hr : 0 ≤ r) :
      star (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt hr]
  have weighted_matrix_gram (next : (K a head) → σ → (K a head)) (p : (K a head) → σ → ℝ)
      (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1)
      (hinj : ∀ j l i, p j i ≠ 0 → p l i ≠ 0 → next j i = next l i → j = l) :
      (weightedMatrix next p).conjTranspose * weightedMatrix next p = 1 := by
    ext j l
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hjl : j = l
    · subst l
      simp only [if_pos rfl, Fintype.sum_prod_type]
      have hterm (i : σ) (k : (K a head)) :
          star (weightedMatrix next p (i, k) j) * weightedMatrix next p (i, k) j =
            if next j i = k then (p j i : ℂ) else 0 := by
        by_cases h : next j i = k
        · simp only [weightedMatrix, if_pos h]
          exact sqrt_gram _ (hp j i)
        · simp [weightedMatrix, h]
      simp_rw [hterm]
      simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Complex.ofReal_sum,
        hsum, Complex.ofReal_one]
    · rw [if_neg hjl]
      apply Finset.sum_eq_zero
      rintro ⟨i, k⟩ _
      by_cases hpj : p j i = 0
      · simp [weightedMatrix, hpj]
      by_cases hpl : p l i = 0
      · simp [weightedMatrix, hpl]
      by_cases hj : next j i = k
      · have hl : next l i ≠ k := fun hl => hjl (hinj j l i hpj hpl (hj.trans hl.symm))
        simp [weightedMatrix, hl]
      · simp [weightedMatrix, hj]
  have tail_sum_eq_zero_iff (b : TailBox c) :
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
  have positive_tail_sum (b : PaddingTail c) :
      0 < tailSum b.val :=
    Nat.pos_of_ne_zero (fun h => b.property ((tail_sum_eq_zero_iff b.val).mp h))
  have padding_probability_nonneg :
      ∀ s i, 0 ≤ paddingProbability H c s i := by
    intro s i
    cases s with
    | none => cases i <;> simp [paddingProbability]
    | some s =>
      rcases s with ⟨b, h⟩
      have hR := positive_tail_sum b
      by_cases hr : tailSum b.val = 1
      · cases i <;> simp only [paddingProbability, if_pos hr] <;> split <;> positivity
      · have hR2 : (2 : ℝ) ≤ tailSum b.val := by exact_mod_cast (by omega : 2 ≤ tailSum b.val)
        have hden : (0 : ℝ) < (h.val : ℝ) + tailSum b.val - 1 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) h.val]
        cases i with
        | none =>
          simp only [paddingProbability, if_neg hr, headProbability]
          exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
        | some i =>
          change 0 ≤ if tailSum b.val = 1 then _ else _
          rw [if_neg hr]
          unfold tailProbability
          apply div_nonneg
          · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
          · exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
  have padding_probabilities_sum
      (d : (TailAlphabet head) → ℕ) (h : ℕ) (hR : 2 ≤ ∑ i, d i) :
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
  have padding_probability_sum :
      ∀ s, ∑ i, paddingProbability H c s i = 1 := by
    intro s
    cases s with
    | none => simp [Fintype.sum_option, paddingProbability]
    | some s =>
      rcases s with ⟨b, h⟩
      have hR := positive_tail_sum b
      rw [Fintype.sum_option]
      by_cases hr : tailSum b.val = 1
      · by_cases hh : h.val = 0
        · simp only [paddingProbability, if_pos hr, if_pos hh, zero_add]
          rw [← Nat.cast_sum]
          change (tailSum b.val : ℝ) = 1
          exact_mod_cast hr
        · simp [paddingProbability, hr, hh]
      · simp only [paddingProbability, if_neg hr]
        apply padding_probabilities_sum (fun i => (b.val i).val) h.val
        change 2 ≤ tailSum b.val
        omega
  have relabel_matrix_gram
      (eA : Option (TailAlphabet head) ≃ σ) (eK : PaddingMemory H c ≃ K a head) :
      (relabelMatrix H c eA eK).conjTranspose * relabelMatrix H c eA eK = 1 := by
    apply weighted_matrix_gram
    · intro j i
      exact padding_probability_nonneg _ _
    · intro j
      rw [← eA.sum_comp]
      simpa only [relabelProbability, Equiv.symm_apply_apply] using
        padding_probability_sum (eK.symm j)
    · intro j l i hj hl heq
      apply eK.symm.injective
      apply padding_predecessor_unique H c (eK.symm j) (eK.symm l) (eA.symm i) hj hl
      exact eK.injective heq

  exact relabel_matrix_gram _ _

end

end D5.S3.Quantum.StationaryPreparation.PaddingTransition
