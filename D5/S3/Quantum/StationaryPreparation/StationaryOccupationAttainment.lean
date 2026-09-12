/- GID: D5/S3/Quantum/StationaryPreparation/StationaryOccupationAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/StationaryOccupationAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationary occupation attainment by the exact last-tail padding Gram. -/

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

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationAttainment

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

abbrev Box (a : Multiset σ) := TailBox a.count
abbrev TailAlphabet (head : σ) := {i : σ // i ≠ head}
abbrev Tail (a : Multiset σ) (head : σ) :=
  TailBox (fun i : TailAlphabet head => a.count i.val)
abbrev PositiveTail (a : Multiset σ) (head : σ) := {b : Tail a head // b ≠ 0}
abbrev K (a : Multiset σ) (head : σ) :=
  Option (PositiveTail a head × Fin (a.count head + 1))

private instance memoryDecidableEq (a : Multiset σ) (head : σ) : DecidableEq (K a head) :=
  Classical.decEq _

def N (a : Multiset σ) : ℕ :=
  (∏ i : σ, (a.count i + 1)) - Finset.univ.sup a.count

def occ (a : Multiset σ) (r : Box a) : Multiset σ :=
  ∑ i : σ, Multiset.replicate (r i).val i

def tailOcc (head : σ) (r : Multiset σ) : Multiset σ :=
  r.filter (fun i => i ≠ head)

def tailIndex (a : Multiset σ) (head : σ) (r : Box a) : Tail a head :=
  fun i => r i.val

def tailWord (a : Multiset σ) (head : σ) (b : Tail a head) : Multiset σ :=
  ∑ i : TailAlphabet head, Multiset.replicate (b i).val i.val

def slice (a : Multiset σ) (head : σ) (b : Tail a head) (j : ℕ) : Multiset σ :=
  Multiset.replicate j head + tailWord a head b

def M (r : Multiset σ) : ℕ := multiplicity r.card r

def m (a : Multiset σ) (head : σ) (b : Tail a head) (j : ℕ) : ℝ :=
  (M (slice a head b j) : ℝ)

def delta (a : Multiset σ) (head : σ) (b : Tail a head) (j : ℕ) : ℝ :=
  if j = 0 then m a head b 0 else m a head b j - m a head b (j - 1)

def lastTail (head : σ) (r : Multiset σ) : ℝ :=
  ((tailOcc head r).card : ℝ) * (M r : ℝ) / (r.card : ℝ)

def z (head : σ) (r : Multiset σ) : ℂ := if tailOcc head r = 0 then 1 else 0

def G (a : Multiset σ) (head : σ) : Matrix (Box a) (Box a) ℂ := fun r s =>
  if occ a s ≤ occ a r then
    (Real.sqrt (((M (occ a s) : ℝ) * (M (occ a r - occ a s) : ℝ)) /
      (M (occ a r) : ℝ)) : ℂ) * z head (occ a r - occ a s)
  else if occ a r ≤ occ a s then
    star ((Real.sqrt (((M (occ a r) : ℝ) * (M (occ a s - occ a r) : ℝ)) /
      (M (occ a s) : ℝ)) : ℂ) * z head (occ a s - occ a r))
  else 0

def D (a : Multiset σ) : Matrix (Box a) (Box a) ℂ :=
  Matrix.diagonal (fun r => (Real.sqrt (M (occ a r) : ℝ) : ℂ))

def block (a : Multiset σ) (head : σ) (b : Tail a head) :
    Matrix (Fin (a.count head + 1)) (Fin (a.count head + 1)) ℂ :=
  fun j k => (m a head b (min j.val k.val) : ℂ)

def L (A : ℕ) : Matrix (Fin (A + 1)) (Fin (A + 1)) ℂ :=
  fun j k => if k ≤ j then 1 else 0

def B (a : Multiset σ) (head : σ) : Matrix (Box a) (Box a) ℂ := fun r s =>
  if tailIndex a head r = tailIndex a head s then
    block a head (tailIndex a head r) (r head) (s head) else 0

def padding (a : Multiset σ) (head : σ) (r : Multiset σ) : Space (K a head) :=
  WithLp.toLp 2 (fun q => match q with
    | none => if r ≤ a ∧ tailOcc head r = 0 then 1 else 0
    | some (b, j) =>
        if r ≤ a ∧ tailOcc head r = tailWord a head b.val ∧ j.val ≤ r.count head then
          (Real.sqrt (lastTail head (slice a head b.val j.val)) : ℂ) else 0)

def phi (a : Multiset σ) (head : σ) (r : Multiset σ) : Space (K a head) :=
  (Real.sqrt (M r : ℝ) : ℂ)⁻¹ • padding a head r

def image (a : Multiset σ) (head : σ) (r : Multiset σ) :
    Space σ ⊗[ℂ] Space (K a head) :=
  if r = 0 then (basis head : Space σ) ⊗ₜ[ℂ] phi a head 0
  else ∑ i : σ, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
    ((basis i : Space σ) ⊗ₜ[ℂ] phi a head (r.erase i))

def phiFin (a : Multiset σ) (head : σ) (e : K a head ≃ Fin (N a))
    (r : Multiset σ) : Space (Fin (N a)) :=
  coordinateEmbedding e.toEmbedding (phi a head r)

def tensorCoordinates (n : ℕ) :
    Space (σ × Fin n) ≃ₗᵢ[ℂ] (Space σ ⊗[ℂ] Space (Fin n)) :=
  ((EuclideanSpace.basisFun σ ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin n) ℂ)).repr.symm

def blankEmbed (n : ℕ) (head : σ) : Space (Fin n) →ₗᵢ[ℂ] Space (σ × Fin n) :=
  coordinateEmbedding (blankInjection head (Function.Embedding.refl (Fin n)))


section
variable {I : Type*} [Fintype I] [DecidableEq I]

private abbrev zeroTail (c : I → ℕ) : TailBox c := 0

private abbrev PaddingTail (c : I → ℕ) := {b : TailBox c // b ≠ zeroTail c}

private abbrev PaddingMemory (H : ℕ) (c : I → ℕ) := Option (PaddingTail c × Fin (H + 1))

private theorem tail_sum_eq_zero_iff (c : I → ℕ) (b : TailBox c) :
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

private theorem positive_tail_sum (c : I → ℕ) (b : PaddingTail c) :
    0 < tailSum b.val :=
  Nat.pos_of_ne_zero (fun h => b.property ((tail_sum_eq_zero_iff c b.val).mp h))

private theorem positive_tail_card (c : I → ℕ) :
    Fintype.card (PaddingTail c) = (∏ i, (c i + 1)) - 1 := by
  classical
  simpa [PaddingTail, TailBox, Fintype.card_pi] using
    Fintype.card_subtype_compl (fun b : TailBox c => b = zeroTail c)

private theorem padding_memory_card (H : ℕ) (c : I → ℕ) :
    Fintype.card (PaddingMemory H c) = (H + 1) * (∏ i, (c i + 1)) - H := by
  classical
  have hp : 1 ≤ ∏ i, (c i + 1) := Finset.one_le_prod fun _ _ => by omega
  have hmul := Nat.mul_le_mul_left (H + 1) hp
  simp only [PaddingMemory, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, positive_tail_card]
  rw [Nat.mul_comm (_ - 1), Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

variable {A : Type*} [Fintype A] [DecidableEq A]
private abbrev OccupationMemory (a : Multiset A) (head : A) :=
  PaddingMemory (a.count head) (fun i : TailAlphabet head => a.count i.val)

private theorem occupation_memory_card (a : Multiset A) (head : A) :
    Fintype.card (OccupationMemory a head) =
      (∏ i : A, (a.count i + 1)) - a.count head := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i : A => a.count i + 1) head]
  exact padding_memory_card _ _

private def occupationMemoryEquiv (a : Multiset A) (head : A)
    (hh : a.count head = Finset.univ.sup a.count) :
    OccupationMemory a head ≃
      Fin ((∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count) :=
  (Fintype.equivFin _).trans (finCongr (by rw [occupation_memory_card, hh]))


end

section
variable {I : Type*} [Fintype I] [DecidableEq I]

private def decrement (c : I → ℕ) (b : TailBox c) (i : I) : TailBox c :=
  Function.update b i ⟨(b i).val - 1,
    lt_of_le_of_lt (Nat.sub_le _ _) (b i).isLt⟩

@[simp] private theorem decrement_same (c : I → ℕ) (b : TailBox c) (i : I) :
    (decrement c b i i).val = (b i).val - 1 := by simp [decrement]

@[simp] private theorem decrement_other (c : I → ℕ) (b : TailBox c) (i j : I) (hji : j ≠ i) :
    decrement c b i j = b j := by simp [decrement, hji]

private theorem decrement_sum (c : I → ℕ) (b : TailBox c) (i : I) (hi : 0 < (b i).val) :
    tailSum (decrement c b i) + 1 = tailSum b := by
  have he (j : I) : (decrement c b i j).val + (if j = i then 1 else 0) = (b j).val := by
    by_cases h : j = i
    · subst j
      simp only [decrement_same, if_pos rfl]
      exact Nat.sub_add_cancel hi
    · simp [decrement_other, h]
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset I)) rfl (fun j _ => he j)
  simpa [Finset.sum_add_distrib, tailSum] using hs

private theorem decrement_injective (c : I → ℕ) (b e : TailBox c) (i : I)
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

private def decrementPositive (c : I → ℕ) (b : PaddingTail c) (i : I)
    (hi : 0 < (b.val i).val) (hR : 1 < tailSum b.val) : PaddingTail c :=
  ⟨decrement c b.val i, by
    intro hz
    have hzero := (tail_sum_eq_zero_iff c _).mpr hz
    have hs := decrement_sum c b.val i hi
    omega⟩

private def headPredecessor {H : ℕ} (h : Fin (H + 1)) : Fin (H + 1) :=
  ⟨h.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) h.isLt⟩

private def paddingNext (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → PaddingMemory H c
  | none, _ => none
  | some (b, h), none => some (b, headPredecessor h)
  | some (b, h), some i =>
      if hi : 0 < (b.val i).val then
        if hR : 1 < tailSum b.val then some (decrementPositive c b i hi hR, h)
        else none
      else none

private theorem tail_coordinate_le_sum (c : I → ℕ) (b : TailBox c) (i : I) :
    (b i).val ≤ tailSum b :=
  Finset.single_le_sum (f := fun j => (b j).val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem sum_one_coordinate (c : I → ℕ) (b : TailBox c)
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

private theorem sum_one_unique (c : I → ℕ) (b e : TailBox c)
    (hb : tailSum b = 1) (he : tailSum e = 1) (i : I)
    (hbi : 0 < (b i).val) (hei : 0 < (e i).val) : b = e := by
  funext j
  apply Fin.ext
  rw [sum_one_coordinate c b hb i hbi j, sum_one_coordinate c e he i hei j]


end

section
private def headProbability (h R : ℕ) : ℝ := (h : ℝ) / ((h : ℝ) + R - 1)

private def tailProbability (h R d : ℕ) : ℝ :=
  (d : ℝ) * ((R : ℝ) - 1) / ((R : ℝ) * ((h : ℝ) + R - 1))

private theorem padding_probabilities_sum {I : Type*} [Fintype I]
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


end

section
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq K]

private def weightedMatrix (next : K → A → K) (p : K → A → ℝ) : Matrix (A × K) K ℂ :=
  fun q j => if next j q.1 = q.2 then (Real.sqrt (p j q.1) : ℂ) else 0

private theorem sqrt_gram (r : ℝ) (hr : 0 ≤ r) :
    star (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt hr]

/-- A deterministic transition with uniquely recoverable predecessors is an isometry. -/
private theorem weighted_matrix_gram (next : K → A → K) (p : K → A → ℝ)
    (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    (hinj : ∀ j l i, p j i ≠ 0 → p l i ≠ 0 → next j i = next l i → j = l) :
    (weightedMatrix next p).conjTranspose * weightedMatrix next p = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hjl : j = l
  · subst l
    simp only [if_pos rfl, Fintype.sum_prod_type]
    have hterm (i : A) (k : K) :
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


end

section
variable {I : Type*} [Fintype I] [DecidableEq I]

private def paddingProbability (H : ℕ) (c : I → ℕ) : PaddingMemory H c → Option I → ℝ
  | none, none => 1
  | none, some _ => 0
  | some (b, h), none =>
      if tailSum b.val = 1 then (if h.val = 0 then 0 else 1)
      else headProbability h.val (tailSum b.val)
  | some (b, h), some i =>
      if tailSum b.val = 1 then (if h.val = 0 then ((b.val i).val : ℝ) else 0)
      else tailProbability h.val (tailSum b.val) (b.val i).val

private theorem padding_probability_nonneg (H : ℕ) (c : I → ℕ) :
    ∀ s i, 0 ≤ paddingProbability H c s i := by
  intro s i
  cases s with
  | none => cases i <;> simp [paddingProbability]
  | some s =>
    rcases s with ⟨b, h⟩
    have hR := positive_tail_sum c b
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

private theorem padding_probability_sum (H : ℕ) (c : I → ℕ) :
    ∀ s, ∑ i, paddingProbability H c s i = 1 := by
  intro s
  cases s with
  | none => simp [Fintype.sum_option, paddingProbability]
  | some s =>
    rcases s with ⟨b, h⟩
    have hR := positive_tail_sum c b
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

private theorem positive_head_of_probability (H : ℕ) (c : I → ℕ)
    (b : PaddingTail c) (h : Fin (H + 1))
    (hp : paddingProbability H c (some (b, h)) none ≠ 0) : 0 < h.val := by
  by_contra! hn
  have hh : h.val = 0 := by omega
  simp [paddingProbability, headProbability, hh] at hp

private theorem positive_tail_of_probability (H : ℕ) (c : I → ℕ)
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

private theorem padding_predecessor_unique (H : ℕ) (c : I → ℕ) :
    ∀ s t i, paddingProbability H c s i ≠ 0 → paddingProbability H c t i ≠ 0 →
      paddingNext H c s i = paddingNext H c t i → s = t := by
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
        have hh := positive_head_of_probability H c b h hs
        have hg := positive_head_of_probability H c e g ht
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
        obtain ⟨hbi, hbh⟩ := positive_tail_of_probability H c b h i hs
        obtain ⟨hei, heh⟩ := positive_tail_of_probability H c e g i ht
        have hbpos := positive_tail_sum c b
        have hepos := positive_tail_sum c e
        simp only [paddingNext, dif_pos hbi, dif_pos hei] at heq
        by_cases hbR : 1 < tailSum b.val
        · rw [dif_pos hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · rw [dif_pos heR] at heq
            have hp := Option.some.inj heq
            have hhg : h = g := congrArg Prod.snd hp
            have hdec := congrArg (fun p : PaddingTail c × Fin (H + 1) => p.1.val) hp
            have hbe : b = e := Subtype.ext (decrement_injective c b.val e.val i hbi hei hdec)
            simp [hbe, hhg]
          · simp [heR] at heq
        · rw [dif_neg hbR] at heq
          by_cases heR : 1 < tailSum e.val
          · simp [heR] at heq
          · have hb1 : tailSum b.val = 1 := by omega
            have he1 : tailSum e.val = 1 := by omega
            have hbe : b = e := Subtype.ext (sum_one_unique c b.val e.val hb1 he1 i hbi hei)
            have hhg : h = g := Fin.ext ((hbh hb1).trans (heh he1).symm)
            simp [hbe, hhg]

end

section
variable {I : Type*} [Fintype I] [DecidableEq I]

variable {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

private def relabelNext (H : ℕ) (c : I → ℕ) (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) :
    K → A → K := fun j i => eK (paddingNext H c (eK.symm j) (eA.symm i))

private def relabelProbability (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : K → A → ℝ :=
  fun j i => paddingProbability H c (eK.symm j) (eA.symm i)

private def relabelMatrix (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) : Matrix (A × K) K ℂ :=
  weightedMatrix (relabelNext H c eA eK) (relabelProbability H c eA eK)

private theorem relabel_matrix_gram (H : ℕ) (c : I → ℕ)
    (eA : Option I ≃ A) (eK : PaddingMemory H c ≃ K) :
    (relabelMatrix H c eA eK).conjTranspose * relabelMatrix H c eA eK = 1 := by
  apply weighted_matrix_gram
  · intro j i
    exact padding_probability_nonneg H c _ _
  · intro j
    rw [← eA.sum_comp]
    simpa only [relabelProbability, Equiv.symm_apply_apply] using
      padding_probability_sum H c (eK.symm j)
  · intro j l i hj hl heq
    apply eK.symm.injective
    apply padding_predecessor_unique H c (eK.symm j) (eK.symm l) (eA.symm i) hj hl
    exact eK.injective heq


end

section
variable {A : Type*} [Fintype A] [DecidableEq A]

private def tailCount (head : A) (b : Multiset A) : ℕ :=
  ∑ i : {i : A // i ≠ head}, b.count i.val

private theorem head_add_tail_count (head : A) (b : Multiset A) :
    b.count head + tailCount head b = b.card := by
  unfold tailCount
  rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
  exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)

private theorem tail_count_erase_head (head : A) (b : Multiset A) :
    tailCount head (b.erase head) = tailCount head b := by
  apply Finset.sum_congr rfl
  intro i _
  exact Multiset.count_erase_of_ne i.property b

private theorem tail_count_erase_tail (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) :
    tailCount head (b.erase i) + 1 = tailCount head b := by
  have h1 := head_add_tail_count head b
  have h2 := head_add_tail_count head (b.erase i)
  have hc : (b.erase i).count head = b.count head :=
    Multiset.count_erase_of_ne (Ne.symm hi) b
  have hn : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hib)
  omega

/-- The ordinary last-tail weight, expressed using actual occupation-word multiplicity. -/
private def lastTailMass (head : A) (b : Multiset A) : ℝ :=
  (tailCount head b : ℝ) * (multiplicity b.card b : ℝ) / (b.card : ℝ)

private theorem last_tail_mass_pos (head : A) (b : Multiset A) (hR : 0 < tailCount head b) :
    0 < lastTailMass head b := by
  have hn : 0 < b.card := by have := head_add_tail_count head b; omega
  unfold lastTailMass
  exact div_pos (mul_pos (by exact_mod_cast hR)
    (by exact_mod_cast multiplicity_pos b rfl)) (by exact_mod_cast hn)

private theorem erase_multiplicity_real (b : Multiset A) (i : A) (hi : i ∈ b) :
    (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
      (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
  have hn : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hi)
  have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
  rw [hn] at hm
  exact_mod_cast hm

private theorem last_tail_mass_erase_head (head : A) (b : Multiset A)
    (hi : head ∈ b) (hR : 0 < tailCount head b) :
    lastTailMass head (b.erase head) =
      headProbability (b.count head) (tailCount head b) * lastTailMass head b := by
  have hsum := head_add_tail_count head b
  have hc : (b.erase head).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hi)
  have hb : 0 < b.count head := Multiset.count_pos.mpr hi
  have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
  have he : (0 : ℝ) < (b.erase head).card := by
    exact_mod_cast (by omega : 0 < (b.erase head).card)
  have hcR : ((b.erase head).card : ℝ) + 1 = b.card := by exact_mod_cast hc
  have hsR : (b.count head : ℝ) + tailCount head b = b.card := by exact_mod_cast hsum
  have hm := erase_multiplicity_real b head hi
  unfold lastTailMass headProbability
  rw [tail_count_erase_head]
  have hd : (b.count head : ℝ) + tailCount head b - 1 = (b.erase head).card := by linarith
  rw [hd]
  field_simp [hn.ne', he.ne']
  nlinarith [congrArg (fun x : ℝ => (tailCount head b : ℝ) * x) hm]

private theorem last_tail_mass_erase_tail (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ tailCount head b) :
    lastTailMass head (b.erase i) =
      tailProbability (b.count head) (tailCount head b) (b.count i) * lastTailMass head b := by
  have hsum := head_add_tail_count head b
  have hc : (b.erase i).card + 1 = b.card := by
    simpa using congrArg Multiset.card (Multiset.cons_erase hib)
  have ht := tail_count_erase_tail head b i hi hib
  have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
  have he : (0 : ℝ) < (b.erase i).card := by
    exact_mod_cast (by omega : 0 < (b.erase i).card)
  have hr : (0 : ℝ) < tailCount head b := by exact_mod_cast (by omega : 0 < tailCount head b)
  have hcR : ((b.erase i).card : ℝ) + 1 = b.card := by exact_mod_cast hc
  have hsR : (b.count head : ℝ) + tailCount head b = b.card := by exact_mod_cast hsum
  have htR : (tailCount head (b.erase i) : ℝ) + 1 = tailCount head b := by exact_mod_cast ht
  have hm := erase_multiplicity_real b i hib
  unfold lastTailMass tailProbability
  have hd : (b.count head : ℝ) + tailCount head b - 1 = (b.erase i).card := by linarith
  rw [hd, show (tailCount head (b.erase i) : ℝ) = tailCount head b - 1 by linarith]
  field_simp [hn.ne', he.ne', hr.ne']
  nlinarith [congrArg (fun x : ℝ => ((tailCount head b : ℝ) - 1) * x) hm]

private theorem last_tail_mass_singleton (head i : A) (hi : i ≠ head) :
    lastTailMass head ({i} : Multiset A) = 1 := by
  have hs := head_add_tail_count head ({i} : Multiset A)
  have ht : tailCount head ({i} : Multiset A) = 1 := by simpa [hi, Ne.symm hi] using hs
  have hm : multiplicity ({i} : Multiset A).card ({i} : Multiset A) = 1 := by
    rw [multiplicity_eq_factorial _ rfl]
    have hp : (∏ z : A, (({i} : Multiset A).count z).factorial) = 1 := by
      apply Finset.prod_eq_one
      intro z _
      by_cases hz : z = i <;> simp [hz]
    simp [hp]
  unfold lastTailMass
  rw [ht, hm]
  simp

private theorem last_tail_mass_one (head : A) (b : Multiset A)
    (hR : tailCount head b = 1) : lastTailMass head b = 1 := by
  induction hn : b.card using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases hh : head ∈ b
    · have he : (b.erase head).card < n := by
        rw [Multiset.card_erase_of_mem hh, hn]
        have : b.card ≠ 0 := by
          intro hz
          have hb := Multiset.card_eq_zero.mp hz
          simpa [hb] using hh
        exact Nat.pred_lt (by simpa [hn] using this)
      have hr : tailCount head (b.erase head) = 1 := by
        rw [tail_count_erase_head, hR]
      have hm := ih _ he (b.erase head) hr rfl
      have hp : headProbability (b.count head) (tailCount head b) = 1 := by
        have hc : (b.count head : ℝ) ≠ 0 := by
          exact_mod_cast (Multiset.count_pos.mpr hh).ne'
        simp [headProbability, hR, hc]
      rw [last_tail_mass_erase_head head b hh (by omega), hp, one_mul] at hm
      exact hm
    · have hc : b.card = 1 := by
        simpa [Multiset.count_eq_zero.mpr hh, hR] using
          (head_add_tail_count head b).symm
      obtain ⟨i, rfl⟩ := Multiset.card_eq_one.mp hc
      apply last_tail_mass_singleton
      simpa [eq_comm] using hh

private theorem last_tail_head_amplitude (head : A) (b : Multiset A)
    (hi : head ∈ b) (hR : 0 < tailCount head b) :
    (Real.sqrt (headProbability (b.count head) (tailCount head b)) : ℂ) *
      (Real.sqrt (lastTailMass head b) : ℂ) =
      (Real.sqrt (lastTailMass head (b.erase head)) : ℂ) := by
  have hr : (1 : ℝ) ≤ tailCount head b := by exact_mod_cast hR
  have hp : 0 ≤ headProbability (b.count head) (tailCount head b) := by
    unfold headProbability
    exact div_nonneg (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
  rw [last_tail_mass_erase_head head b hi hR, Real.sqrt_mul hp, Complex.ofReal_mul]

private theorem last_tail_tail_amplitude (head : A) (b : Multiset A) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ tailCount head b) :
    (Real.sqrt (tailProbability (b.count head) (tailCount head b) (b.count i)) : ℂ) *
      (Real.sqrt (lastTailMass head b) : ℂ) =
      (Real.sqrt (lastTailMass head (b.erase i)) : ℂ) := by
  have hr : (2 : ℝ) ≤ tailCount head b := by exact_mod_cast hR
  have hp : 0 ≤ tailProbability (b.count head) (tailCount head b) (b.count i) := by
    unfold tailProbability
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    · exact mul_nonneg (Nat.cast_nonneg _)
        (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
  rw [last_tail_mass_erase_tail head b i hi hib hR, Real.sqrt_mul hp, Complex.ofReal_mul]


end

section
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Replace only the head count; the tail occupation is unchanged. -/
private def headSlice (head : A) (b : Multiset A) (h : ℕ) : Multiset A :=
  Multiset.replicate h head + b.filter (fun i => i ≠ head)

@[simp] private theorem head_slice_count_head (head : A) (b : Multiset A) (h : ℕ) :
    (headSlice head b h).count head = h := by
  simp [headSlice, Multiset.count_filter]

private theorem head_slice_count_tail (head : A) (b : Multiset A) (h : ℕ)
    (i : A) (hi : i ≠ head) : (headSlice head b h).count i = b.count i := by
  simp [headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]

private theorem head_slice_tail_count (head : A) (b : Multiset A) (h : ℕ) :
    tailCount head (headSlice head b h) = tailCount head b := by
  apply Finset.sum_congr rfl
  intro i _
  exact head_slice_count_tail head b h i.val i.property

private theorem head_slice_card (head : A) (b : Multiset A) (h : ℕ) :
    (headSlice head b h).card = h + tailCount head b := by
  rw [← head_add_tail_count head, head_slice_count_head, head_slice_tail_count]

private theorem head_slice_self (head : A) (b : Multiset A) :
    headSlice head b (b.count head) = b := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i; exact head_slice_count_head head b _
  · exact head_slice_count_tail head b _ i hi

private theorem head_slice_erase_head (head : A) (b : Multiset A) (h : ℕ) :
    (headSlice head b h).erase head = headSlice head b (h - 1) := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i
    simp
  · rw [Multiset.count_erase_of_ne hi,
      head_slice_count_tail head b h i hi, head_slice_count_tail head b (h - 1) i hi]

private theorem head_slice_erase_tail (head : A) (b : Multiset A) (h : ℕ)
    (i : A) (hi : i ≠ head) :
    (headSlice head b h).erase i = headSlice head (b.erase i) h := by
  apply Multiset.ext.mpr
  intro j
  by_cases hj : j = head
  · subst j
    rw [Multiset.count_erase_of_ne (Ne.symm hi)]
    simp
  · by_cases hji : j = i
    · subst j
      simp [head_slice_count_tail head _ _ i hi]
    · rw [Multiset.count_erase_of_ne hji,
        head_slice_count_tail head b h j hj,
        head_slice_count_tail head (b.erase i) h j hj,
        Multiset.count_erase_of_ne hji]

private theorem head_slice_erase_head_source (head : A) (b : Multiset A) (h : ℕ) :
    headSlice head (b.erase head) h = headSlice head b h := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i; simp
  · rw [head_slice_count_tail head _ _ i hi, head_slice_count_tail head _ _ i hi,
      Multiset.count_erase_of_ne hi]

private def residualTail (head : A) (a b : Multiset A) (hb : b ≤ a) :
    TailBox (fun i : TailAlphabet head => a.count i.val) :=
  fun i => ⟨b.count i.val, Nat.lt_succ_of_le (Multiset.le_iff_count.mp hb i.val)⟩

private def residualPaddingTail (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount head b) : PaddingTail (fun i : TailAlphabet head => a.count i.val) :=
  ⟨residualTail head a b hb, by
    intro hz
    have hh := (tail_sum_eq_zero_iff _ _).mpr hz
    change tailCount head b = 0 at hh
    omega⟩

private def residualHeadIndex (head : A) (a b : Multiset A) (hb : b ≤ a)
    (h : Fin (b.count head + 1)) : Fin (a.count head + 1) :=
  ⟨h.val, lt_of_lt_of_le h.isLt (Nat.add_le_add_right (Multiset.le_iff_count.mp hb head) 1)⟩

/-- Unnormalized residual amplitudes encode every possible last-tail position. -/
private def paddingResidual (head : A) (a b : Multiset A) : Space (OccupationMemory a head) :=
  if hb : b ≤ a then
    if hr : 0 < tailCount head b then
      ∑ h : Fin (b.count head + 1),
        (Real.sqrt (lastTailMass head (headSlice head b h.val)) : ℂ) •
          basis (some (residualPaddingTail head a b hb hr, residualHeadIndex head a b hb h))
    else basis none
  else 0

private theorem padding_residual_tail_free (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : tailCount head b = 0) : paddingResidual head a b = basis none := by
  simp [paddingResidual, hb, hr]

private theorem padding_residual_zero (head : A) (a : Multiset A) :
    paddingResidual head a 0 = basis none := by
  apply padding_residual_tail_free head a 0 (Multiset.zero_le _)
  simp [tailCount]


end

section
variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem head_slice_head_amplitude (head : A) (b : Multiset A) (h : ℕ)
    (hh : 0 < h) (hr : 0 < tailCount head b) :
    (Real.sqrt (headProbability h (tailCount head b)) : ℂ) *
      (Real.sqrt (lastTailMass head (headSlice head b h)) : ℂ) =
      (Real.sqrt (lastTailMass head (headSlice head b (h - 1))) : ℂ) := by
  have hm : head ∈ headSlice head b h := by
    apply Multiset.count_pos.mp
    simpa using hh
  simpa only [head_slice_count_head, head_slice_tail_count, head_slice_erase_head] using
    last_tail_head_amplitude head (headSlice head b h) hm (by rwa [head_slice_tail_count])

private theorem head_slice_tail_amplitude (head : A) (b : Multiset A) (h : ℕ) (i : A)
    (hi : i ≠ head) (hib : i ∈ b) (hr : 2 ≤ tailCount head b) :
    (Real.sqrt (tailProbability h (tailCount head b) (b.count i)) : ℂ) *
      (Real.sqrt (lastTailMass head (headSlice head b h)) : ℂ) =
      (Real.sqrt (lastTailMass head (headSlice head (b.erase i) h)) : ℂ) := by
  have hm : i ∈ headSlice head b h := by
    apply Multiset.count_pos.mp
    rw [head_slice_count_tail head b h i hi]
    exact Multiset.count_pos.mpr hib
  simpa only [head_slice_count_head, head_slice_tail_count,
    head_slice_count_tail head b h i hi, head_slice_erase_tail head b h i hi] using
    last_tail_tail_amplitude head (headSlice head b h) i hi hm
      (by rwa [head_slice_tail_count])

private theorem head_slice_one_amplitude (head : A) (b : Multiset A) (h : ℕ)
    (hr : tailCount head b = 1) :
    (Real.sqrt (lastTailMass head (headSlice head b h)) : ℂ) = 1 := by
  rw [last_tail_mass_one head _ (by rwa [head_slice_tail_count])]
  simp

private theorem tail_count_zero_iff (head : A) (b : Multiset A) :
    tailCount head b = 0 ↔ ∀ i, i ≠ head → b.count i = 0 := by
  simp only [tailCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩
  · intro h i
    exact h i.val i.property

private theorem tail_free_membership (head : A) (b : Multiset A)
    (hr : tailCount head b = 0) (hb : b ≠ 0) (i : A) : i ∈ b ↔ i = head := by
  have ht := (tail_count_zero_iff head b).mp hr
  constructor
  · intro hi
    by_contra hne
    exact (Multiset.count_pos.mpr hi).ne' (ht i hne)
  · intro hi
    subst i
    have hn : b.card ≠ 0 := fun hz => hb (Multiset.card_eq_zero.mp hz)
    have hs := head_add_tail_count head b
    apply Multiset.count_pos.mp
    omega


end
private def residualScale (r : Multiset σ) : ℝ := Real.sqrt (multiplicity r.card r : ℝ)

private theorem scale_pos (r : Multiset σ) : 0 < residualScale r := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)

private theorem scale_sq (r : Multiset σ) : residualScale r ^ 2 = (multiplicity r.card r : ℝ) := by
  exact Real.sq_sqrt (Nat.cast_nonneg _)

private theorem scale_ne_zero (r : Multiset σ) : (residualScale r : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (scale_pos r).ne'

private theorem capacities_multiset_echo (c : σ → ℕ) :
    (∀ i : σ, (∑ j : σ, Multiset.replicate (c j) j).count i = c i) ∧
      (∑ j : σ, Multiset.replicate (c j) j).card = ∑ j : σ, c j := by
  have hc (i : σ) : (∑ j : σ, Multiset.replicate (c j) j).count i = c i := by
    simp [Multiset.count_sum', Multiset.count_replicate]
  refine ⟨hc, ?_⟩
  rw [← Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)]
  simp_rw [hc]

@[simp] private theorem occ_count (a : Multiset σ) (r : Box a) (i : σ) :
    (occ a r).count i = (r i).val :=
  (capacities_multiset_echo (fun j => (r j).val)).1 i

private theorem box_occupation_le (a : Multiset σ) (r : Box a) : occ a r ≤ a := by
  apply Multiset.le_iff_count.mpr
  intro i
  rw [occ_count]
  exact Nat.le_of_lt_succ (r i).isLt


section
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Last-tail weights are the consecutive multiplicity increments, with the
initial multiplicity at head count zero. -/
private theorem last_tail_mass_head_slice (head : A) (b : Multiset A)
    (hr : 0 < tailCount head b) (j : ℕ) :
    lastTailMass head (headSlice head b j) =
      if j = 0 then
        (multiplicity (headSlice head b 0).card (headSlice head b 0) : ℝ)
      else
        (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ) -
        (multiplicity (headSlice head b (j - 1)).card (headSlice head b (j - 1)) : ℝ) := by
  have hn : (0 : ℝ) < (headSlice head b j).card := by
    exact_mod_cast (show 0 < (headSlice head b j).card by rw [head_slice_card]; omega)
  by_cases hj : j = 0
  · subst j
    simp only [ite_true, lastTailMass, head_slice_tail_count, head_slice_card, zero_add]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')
  · rw [if_neg hj]
    have hm := erase_multiplicity_real (headSlice head b j) head
      (Multiset.count_pos.mp (by simpa using Nat.pos_of_ne_zero hj))
    rw [head_slice_erase_head, head_slice_count_head] at hm
    have hs : ((headSlice head b j).card : ℝ) = j + (tailCount head b : ℝ) := by
      exact_mod_cast head_slice_card head b j
    unfold lastTailMass
    rw [head_slice_tail_count, div_eq_iff hn.ne']
    nlinarith [congrArg (fun x : ℝ =>
      x * (multiplicity (headSlice head b j).card (headSlice head b j) : ℝ)) hs]

private theorem sum_last_tail_mass (head : A) (b : Multiset A)
    (hr : 0 < tailCount head b) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), lastTailMass head (headSlice head b j)) =
      (multiplicity (headSlice head b n).card (headSlice head b n) : ℝ) := by
  simp_rw [last_tail_mass_head_slice head b hr]
  exact (Finset.eq_sum_range_sub' _ n).symm

private theorem tail_filter_eq_zero (head : A) (b : Multiset A) :
    b.filter (fun i => i ≠ head) = 0 ↔ tailCount head b = 0 := by
  rw [tail_count_zero_iff]
  constructor
  · intro h i hi
    have := congrArg (Multiset.count i) h
    simpa [Multiset.count_filter, hi] using this
  · intro h
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · simp [hi, h i hi]

private theorem tail_free_multiplicity (head : A) (b : Multiset A)
    (hr : tailCount head b = 0) (n : ℕ) :
    multiplicity (headSlice head b n).card (headSlice head b n) = 1 := by
  have hf := (tail_filter_eq_zero head b).mpr hr
  simp only [headSlice, hf, add_zero, Multiset.card_replicate]
  rw [multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
  simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
  simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
  exact Nat.div_self (Nat.factorial_pos n)

private theorem residual_tail_eq_iff (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
    residualPaddingTail head a b hb hr = residualPaddingTail head a c hc hs ↔
      b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
  constructor
  · intro h
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · have he := congrArg (fun t : PaddingTail (fun i : TailAlphabet head => a.count i.val) =>
        (t.val ⟨i, hi⟩).val) h
      simpa [residualPaddingTail, residualTail, Multiset.count_filter, hi] using he
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he := congrArg (Multiset.count i.val) h
    simpa [residualPaddingTail, residualTail, Multiset.count_filter, i.property] using he

private theorem padding_residual_none (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : 0 < tailCount head b) : paddingResidual head a b none = 0 := by
  simp [paddingResidual, hb, hr, WithLp.ofLp_sum, Finset.sum_apply,
    basis_apply]

private theorem padding_residual_coordinates (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : 0 < tailCount head b)
    (t : PaddingTail (fun i : TailAlphabet head => a.count i.val))
    (k : Fin (a.count head + 1)) :
    paddingResidual head a b (some (t, k)) =
      if t = residualPaddingTail head a b hb hr ∧ k.val ≤ b.count head then
        (Real.sqrt (lastTailMass head (headSlice head b k.val)) : ℂ) else 0 := by
  classical
  rw [paddingResidual, dif_pos hb, dif_pos hr]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    basis_apply, Option.some.injEq, Prod.mk.injEq]
  by_cases ht : t = residualPaddingTail head a b hb hr
  · subst t
    by_cases hk : k.val ≤ b.count head
    · rw [if_pos ⟨rfl, hk⟩]
      let j : Fin (b.count head + 1) := ⟨k.val, Nat.lt_succ_of_le hk⟩
      rw [Finset.sum_eq_single j]
      · simp [j, residualHeadIndex]
      · intro i _ hij
        have hi : k ≠ residualHeadIndex head a b hb i := by
          intro he
          apply hij
          exact Fin.ext (congrArg Fin.val he).symm
        simp [hi]
      · simp
    · rw [if_neg (by simp [hk])]
      apply Finset.sum_eq_zero
      intro i _
      have hi : k ≠ residualHeadIndex head a b hb i := by
        intro he
        have := congrArg Fin.val he
        have := i.isLt
        simp only [residualHeadIndex] at *
        omega
      simp [hi]
  · simp [ht]

private theorem sum_bounded_mass (head : A) (a b : Multiset A)
    (hr : 0 < tailCount head b) (n : ℕ) (hn : n ≤ a.count head) :
    (∑ k : Fin (a.count head + 1),
      if k.val ≤ n then (lastTailMass head (headSlice head b k.val) : ℂ) else 0) =
      (multiplicity (headSlice head b n).card (headSlice head b n) : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0)]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        if k ≤ n then (lastTailMass head (headSlice head b k) : ℂ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
      intro k _ hk
      have : ¬ k ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
      simp [this]
    _ = ∑ k ∈ Finset.range (n + 1),
        (lastTailMass head (headSlice head b k) : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    _ = _ := by exact_mod_cast sum_last_tail_mass head b hr n

private theorem padding_residual_inner_positive (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) (hr : 0 < tailCount head b) (hs : 0 < tailCount head c) :
    inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  classical
  have hg : inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      ∑ x, star (paddingResidual head a b x) * paddingResidual head a c x := by
    calc
      _ = inner ℂ (∑ x, paddingResidual head a b x • basis x)
          (∑ x, paddingResidual head a c x • basis x) :=
        congrArg₂ (inner ℂ) (basis_expansion _) (basis_expansion _)
      _ = _ := (EuclideanSpace.basisFun (OccupationMemory a head) ℂ).orthonormal.inner_sum
        (paddingResidual head a b) (paddingResidual head a c) Finset.univ
  rw [hg, Fintype.sum_option, padding_residual_none head a b hb hr, star_zero,
    zero_mul, zero_add, Fintype.sum_prod_type]
  by_cases ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head)
  · rw [if_pos ht]
    have htt := (residual_tail_eq_iff head a b c hb hc hr hs).mpr ht
    have hslice (j : ℕ) : headSlice head c j = headSlice head b j := by
      simp only [headSlice, ht]
    have hterm (t : PaddingTail (fun i : TailAlphabet head => a.count i.val))
        (k : Fin (a.count head + 1)) :
        star (paddingResidual head a b (some (t, k))) *
          paddingResidual head a c (some (t, k)) =
        if t = residualPaddingTail head a b hb hr ∧
            k.val ≤ min (b.count head) (c.count head) then
          (lastTailMass head (headSlice head b k.val) : ℂ) else 0 := by
      rw [padding_residual_coordinates head a b hb hr,
        padding_residual_coordinates head a c hc hs, ← htt, hslice]
      have hm := (last_tail_mass_pos head (headSlice head b k.val)
        (by simpa only [head_slice_tail_count] using hr)).le
      by_cases htb : t = residualPaddingTail head a b hb hr <;>
        by_cases hkb : k.val ≤ b.count head <;> by_cases hkc : k.val ≤ c.count head <;>
        simp [htb, hkb, hkc, ← Complex.ofReal_mul,
          Real.mul_self_sqrt hm]
    simp_rw [hterm]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact sum_bounded_mass head a b hr _
      (le_trans (min_le_left _ _) (Multiset.le_iff_count.mp hb head))
  · rw [if_neg ht]
    have htt : residualPaddingTail head a b hb hr ≠ residualPaddingTail head a c hc hs :=
      fun h => ht ((residual_tail_eq_iff head a b c hb hc hr hs).mp h)
    apply Finset.sum_eq_zero
    intro t _
    apply Finset.sum_eq_zero
    intro k _
    rw [padding_residual_coordinates head a b hb hr,
      padding_residual_coordinates head a c hc hs]
    by_cases htb : t = residualPaddingTail head a b hb hr
    · have htc : t ≠ residualPaddingTail head a c hc hs := by simpa [htb] using htt
      simp [htc]
    · simp [htb]

/-- The Gram entry of the actual padding vectors is the minimum-head
multiplicity when their entire tails coincide, and is zero otherwise. -/
private theorem padding_residual_inner (head : A) (a b c : Multiset A)
    (hb : b ≤ a) (hc : c ≤ a) :
    inner ℂ (paddingResidual head a b) (paddingResidual head a c) =
      if b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) then
        let q := headSlice head b (min (b.count head) (c.count head))
        (multiplicity q.card q : ℂ)
      else 0 := by
  classical
  by_cases hr : tailCount head b = 0
  · rw [padding_residual_tail_free head a b hb hr]
    by_cases hs : tailCount head c = 0
    · have ht : b.filter (fun i => i ≠ head) = c.filter (fun i => i ≠ head) := by
        rw [(tail_filter_eq_zero head b).mpr hr, (tail_filter_eq_zero head c).mpr hs]
      rw [padding_residual_tail_free head a c hc hs, if_pos ht]
      dsimp only
      rw [tail_free_multiplicity head b hr]
      simp [basis]
    · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
        intro h
        apply hs
        apply (tail_filter_eq_zero head c).mp
        rw [← h, (tail_filter_eq_zero head b).mpr hr]
      rw [if_neg ht]
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a c hc (Nat.pos_of_ne_zero hs)
  · by_cases hs : tailCount head c = 0
    · have ht : b.filter (fun i => i ≠ head) ≠ c.filter (fun i => i ≠ head) := by
        intro h
        apply hr
        apply (tail_filter_eq_zero head b).mp
        rw [h, (tail_filter_eq_zero head c).mpr hs]
      rw [padding_residual_tail_free head a c hc hs, if_neg ht]
      apply inner_eq_zero_symm.mp
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a b hb (Nat.pos_of_ne_zero hr)
    · exact padding_residual_inner_positive head a b c hb hc
        (Nat.pos_of_ne_zero hr) (Nat.pos_of_ne_zero hs)



/-- The actual padding residual normalized by its positive word-count scale. -/
private def normalizedPadding (head : A) (a b : Multiset A) : Space (OccupationMemory a head) :=
  (residualScale b : ℂ)⁻¹ • paddingResidual head a b

/-- Source moments with the actual common sink, in the source's inner-product order. -/
private def paddingMoment (head : A) (a b : Multiset A) : ℂ :=
  inner ℂ (normalizedPadding head a b) (basis none)

private theorem normalized_padding_norm (head : A) (a b : Multiset A) (hb : b ≤ a) :
    ‖normalizedPadding head a b‖ = 1 := by
  have hi := padding_residual_inner head a b b hb hb
  simp only [ite_true, min_self, head_slice_self] at hi
  have hn : ‖paddingResidual head a b‖ = residualScale b := by
    have hh : ‖paddingResidual head a b‖ ^ 2 = (multiplicity b.card b : ℝ) := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hi]
      rfl
    nlinarith [scale_sq b, scale_pos b, norm_nonneg (paddingResidual head a b)]
  rw [normalizedPadding, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scale_pos b), hn, inv_mul_cancel₀ (scale_pos b).ne']

private theorem normalized_padding_tail_free (head : A) (a b : Multiset A)
    (hb : b ≤ a) (hr : tailCount head b = 0) : normalizedPadding head a b = basis none := by
  have hm : multiplicity b.card b = 1 := by
    simpa only [head_slice_self] using tail_free_multiplicity head b hr (b.count head)
  simp [normalizedPadding, padding_residual_tail_free head a b hb hr, residualScale, hm]

@[simp] private theorem normalized_padding_zero (head : A) (a : Multiset A) :
    normalizedPadding head a 0 = basis none := by
  apply normalized_padding_tail_free head a 0 (Multiset.zero_le _)
  simp [tailCount]

private theorem padding_moment (head : A) (a b : Multiset A) (hb : b ≤ a) :
    paddingMoment head a b = if tailCount head b = 0 then 1 else 0 := by
  classical
  by_cases hr : tailCount head b = 0
  · simp [paddingMoment, normalized_padding_tail_free head a b hb hr, hr,
      basis]
  · rw [paddingMoment, normalizedPadding, inner_smul_left, if_neg hr]
    have hz : inner ℂ (paddingResidual head a b) (basis none) = 0 := by
      apply inner_eq_zero_symm.mp
      simpa only [basis, EuclideanSpace.basisFun_inner] using
        padding_residual_none head a b hb (Nat.pos_of_ne_zero hr)
    rw [hz, mul_zero]

private theorem normalized_padding_axis (head : A) (a : Multiset A) (j : ℕ)
    (hj : j ≤ a.count head) :
    normalizedPadding head a (Multiset.replicate j head) = basis none := by
  apply normalized_padding_tail_free
  · apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : head = i
    · subst i; simpa only [Multiset.count_replicate_self] using hj
    · simp only [Multiset.count_replicate, if_neg hi]; exact Nat.zero_le _
  · apply (tail_count_zero_iff head _).mpr
    intro i hi
    simp only [Multiset.count_replicate, if_neg (Ne.symm hi)]

end

private theorem diagonal_det_ne_zero (a : Multiset σ) : (D a).det ≠ 0 := by
  rw [D, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun r _ => scale_ne_zero (occ a r))

section
variable {A : Type*} [Fintype A] [DecidableEq A]

private def occupationSplit (head : A) (a : Multiset A) :
    TailBox a.count ≃ Fin (a.count head + 1) ×
      TailBox (fun i : TailAlphabet head => a.count i.val) := Equiv.piSplitAt head _

private def blockOccupation (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : Multiset A :=
  headSlice head (occ a ((occupationSplit head a).symm (0, b))) j

private theorem block_occupation_index (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (j : Fin (a.count head + 1)) : blockOccupation head a b j.val =
      occ a ((occupationSplit head a).symm (j, b)) := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i
    simp [blockOccupation, occupationSplit, Equiv.piSplitAt]
  · simp [blockOccupation, head_slice_count_tail, hi, occupationSplit, Equiv.piSplitAt]

private theorem block_occupation_tail (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) :
    tailCount head (blockOccupation head a b j) = tailSum b := by
  rw [blockOccupation, head_slice_tail_count]
  unfold tailCount tailSum
  apply Finset.sum_congr rfl
  intro i _
  simp [occupationSplit, Equiv.piSplitAt, i.property]

private theorem block_occupation_slice (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j k : ℕ) :
    headSlice head (blockOccupation head a b j) k = blockOccupation head a b k := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i; simp [blockOccupation]
  · simp [blockOccupation, head_slice_count_tail, hi]

private theorem block_filter_eq_iff (head : A) (a : Multiset A)
    (b c : TailBox (fun i : TailAlphabet head => a.count i.val)) (j k : ℕ) :
    (blockOccupation head a b j).filter (fun i => i ≠ head) =
      (blockOccupation head a c k).filter (fun i => i ≠ head) ↔ b = c := by
  constructor
  · intro h
    funext i
    apply Fin.ext
    have hc := congrArg (Multiset.count i.val) h
    simpa [blockOccupation, Multiset.count_filter, i.property,
      head_slice_count_tail, occupationSplit, Equiv.piSplitAt] using hc
  · rintro rfl
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp
    · simp [blockOccupation, head_slice_count_tail, hi]

private def blockMass (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : ℝ :=
  multiplicity (blockOccupation head a b j).card (blockOccupation head a b j)

private def blockDifference (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (j : ℕ) : ℝ :=
  if j = 0 then blockMass head a b 0 else blockMass head a b j - blockMass head a b (j - 1)

/-- The prescribed factor has literal ones on and below its diagonal. -/
private def lowerOnes (H : ℕ) : Matrix (Fin (H + 1)) (Fin (H + 1)) ℂ :=
  fun j k => if k ≤ j then 1 else 0

private def paddingBlock (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    Matrix (Fin (a.count head + 1)) (Fin (a.count head + 1)) ℂ :=
  Matrix.gram ℂ (fun j => paddingResidual head a (blockOccupation head a b j.val))

private def paddingGram (head : A) (a : Multiset A) : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => paddingResidual head a (occ a r))

private def normalizedPaddingGram (head : A) (a : Multiset A) :
    Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => normalizedPadding head a (occ a r))

private theorem padding_gram_eq_diagonal (head : A) (a : Multiset A) : paddingGram head a =
    D a * normalizedPaddingGram head a *
      D a := by
  classical
  ext r s
  simp only [paddingGram, normalizedPaddingGram, D,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply,
    normalizedPadding, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
  simp only [M]
  field_simp [scale_ne_zero (occ a r), scale_ne_zero (occ a s)]
  dsimp only [residualScale]
  ring

private theorem padding_gram_rank_eq (head : A) (a : Multiset A) :
    (paddingGram head a).rank = (normalizedPaddingGram head a).rank := by
  classical
  rw [padding_gram_eq_diagonal,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (diagonal_det_ne_zero a),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (diagonal_det_ne_zero a)]

private theorem padding_block_entry (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (j k : Fin (a.count head + 1)) :
    paddingBlock head a b j k = (blockMass head a b (min j.val k.val) : ℂ) := by
  have hj : blockOccupation head a b j.val ≤ a := by
    rw [block_occupation_index]; exact box_occupation_le a _
  have hk : blockOccupation head a b k.val ≤ a := by
    rw [block_occupation_index]; exact box_occupation_le a _
  rw [paddingBlock, Matrix.gram_apply, padding_residual_inner head a _ _ hj hk,
    if_pos ((block_filter_eq_iff head a b b j.val k.val).mpr rfl)]
  have hjc : (blockOccupation head a b j.val).count head = j.val := by
    simp [blockOccupation]
  have hkc : (blockOccupation head a b k.val).count head = k.val := by
    simp [blockOccupation]
  simp only [hjc, hkc, block_occupation_slice, blockMass, Complex.ofReal_natCast]

private theorem padding_gram_blocks (head : A) (a : Multiset A) :
    (paddingGram head a).reindex (occupationSplit head a) (occupationSplit head a) =
      Matrix.blockDiagonal (paddingBlock head a) := by
  classical
  ext ⟨j,b⟩ ⟨k,c⟩
  change inner ℂ (paddingResidual head a (occ a ((occupationSplit head a).symm (j,b))))
    (paddingResidual head a (occ a ((occupationSplit head a).symm (k,c)))) = _
  rw [← block_occupation_index, ← block_occupation_index, Matrix.blockDiagonal_apply']
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl]
    rfl
  · rw [if_neg hbc, padding_residual_inner head a _ _]
    · rw [if_neg (fun h => hbc ((block_filter_eq_iff head a b c j.val k.val).mp h))]
    all_goals rw [block_occupation_index]; exact box_occupation_le a _

private theorem lower_ones_det (H : ℕ) : (lowerOnes H).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    exact if_neg (not_le.mpr hij))]
  simp [lowerOnes]

private theorem padding_block_factorization (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    paddingBlock head a b = lowerOnes (a.count head) *
      Matrix.diagonal (fun j : Fin (a.count head + 1) => (blockDifference head a b j.val : ℂ)) *
        (lowerOnes (a.count head)).transpose := by
  ext j k
  rw [padding_block_entry]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  let m := min j.val k.val
  have hm : m + 1 ≤ a.count head + 1 := by dsimp [m]; omega
  have ht : (∑ l : Fin (a.count head + 1), lowerOnes (a.count head) j l *
      (blockDifference head a b l.val : ℂ) * lowerOnes (a.count head) k l) =
      ∑ l ∈ Finset.range (a.count head + 1),
        if l ≤ m then (blockDifference head a b l : ℂ) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hjl : l ≤ j
    · by_cases hkl : l ≤ k
      · have hl : l.val ≤ m := le_min hjl hkl
        simp only [lowerOnes, if_pos hjl, if_pos hkl, if_pos hl, one_mul, mul_one]
      · have hl : ¬l.val ≤ m := by dsimp [m]; intro h; exact hkl (le_trans h (min_le_right _ _))
        simp only [lowerOnes, if_pos hjl, if_neg hkl, if_neg hl, mul_zero]
    · have hl : ¬l.val ≤ m := by dsimp [m]; intro h; exact hjl (le_trans h (min_le_left _ _))
      simp only [lowerOnes, if_neg hjl, if_neg hl, zero_mul]
  rw [ht]
  symm
  calc
    _ = ∑ l ∈ Finset.range (m + 1),
        if l ≤ m then (blockDifference head a b l : ℂ) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hm)
      intro l _ hl
      rw [if_neg (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)]
    _ = ∑ l ∈ Finset.range (m + 1), (blockDifference head a b l : ℂ) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [if_pos (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl)]
    _ = (blockMass head a b m : ℂ) := by
      simp only [blockDifference, apply_ite (Complex.ofReal), Complex.ofReal_sub]
      exact (Finset.eq_sum_range_sub' (fun n => (blockMass head a b n : ℂ)) m).symm

private theorem block_difference_pos (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (hb : b ≠ zeroTail _) (j : ℕ) : 0 < blockDifference head a b j := by
  have hr : 0 < tailCount head (blockOccupation head a b 0) := by
    rw [block_occupation_tail]
    exact positive_tail_sum _ ⟨b, hb⟩
  have h := last_tail_mass_head_slice head (blockOccupation head a b 0) hr j
  rw [block_occupation_slice, block_occupation_slice, block_occupation_slice] at h
  change lastTailMass head (blockOccupation head a b j) = blockDifference head a b j at h
  rw [← h]
  apply last_tail_mass_pos
  rw [block_occupation_tail]
  exact positive_tail_sum _ ⟨b, hb⟩

private theorem block_mass_strict (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val))
    (hb : b ≠ zeroTail _) (j : ℕ) (hj : 0 < j) :
    blockMass head a b (j - 1) < blockMass head a b j := by
  have h := block_difference_pos head a b hb j
  simpa only [blockDifference, if_neg (Nat.ne_of_gt hj), sub_pos] using h

private theorem block_difference_zero_tail (head : A) (a : Multiset A) (j : ℕ) :
    blockDifference head a (zeroTail _) j = if j=0 then 1 else 0 := by
  have hm (n : ℕ) : blockMass head a (zeroTail _) n = 1 := by
    have hv : blockOccupation head a (zeroTail _) n = Multiset.replicate n head := by
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp [blockOccupation]
      · simp [blockOccupation, head_slice_count_tail, hi, occupationSplit,
          Equiv.piSplitAt, zeroTail, Multiset.count_replicate, Ne.symm hi]
    rw [blockMass, hv, Multiset.card_replicate,
      multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
    simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
    simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Nat.div_self (Nat.factorial_pos n), Nat.cast_one]
  simp [blockDifference, hm]


end

section
variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem block_rank_diagonal (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) :
    (paddingBlock head a b).rank =
      (Matrix.diagonal (fun j : Fin (a.count head + 1) =>
        (blockDifference head a b j.val : ℂ))).rank := by
  rw [padding_block_factorization,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by
      rw [Matrix.det_transpose, lower_ones_det]
      norm_num),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by rw [lower_ones_det]; norm_num)]

private theorem padding_block_rank_zero (head : A) (a : Multiset A) :
    (paddingBlock head a (zeroTail _)).rank = 1 := by
  classical
  rw [block_rank_diagonal, Matrix.rank_diagonal]
  have hn (j : Fin (a.count head + 1)) :
      (blockDifference head a (zeroTail _) j.val : ℂ) ≠ 0 ↔ j = 0 := by
    simp [block_difference_zero_tail]
  simp only [hn]
  exact Fintype.card_subtype_eq (0 : Fin (a.count head + 1))

private theorem padding_block_rank_positive (head : A) (a : Multiset A)
    (b : TailBox (fun i : TailAlphabet head => a.count i.val)) (hb : b ≠ zeroTail _) :
    (paddingBlock head a b).rank = a.count head + 1 := by
  classical
  rw [block_rank_diagonal, Matrix.rank_diagonal]
  have hn (j : Fin (a.count head + 1)) : (blockDifference head a b j.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (block_difference_pos head a b hb j.val).ne'
  simp [hn]

private theorem difference_zero_iff (head : A) (a : Multiset A)
    (p : Fin (a.count head + 1) × TailBox (fun i : TailAlphabet head => a.count i.val)) :
    (blockDifference head a p.2 p.1.val : ℂ) = 0 ↔ p.2 = zeroTail _ ∧ p.1 ≠ 0 := by
  by_cases hb : p.2 = zeroTail _
  · rw [hb, block_difference_zero_tail]
    simp
  · have hn := Complex.ofReal_ne_zero.mpr (block_difference_pos head a p.2 hb p.1.val).ne'
    simp [hb, hn]

/-- The actual occupation matrix is transported to its tail blocks, then to the
prescribed diagonal. Its only zero pivots are the nonzero pure-head indices. -/
private theorem padding_gram_rank (head : A) (a : Multiset A) :
    (paddingGram head a).rank = (∏ i : A, (a.count i + 1)) - a.count head := by
  classical
  let T := TailBox (fun i : TailAlphabet head => a.count i.val)
  let P := Fin (a.count head + 1) × T
  let L : Matrix P P ℂ := Matrix.blockDiagonal (fun _ : T => lowerOnes (a.count head))
  let w : P → ℂ := fun p => blockDifference head a p.2 p.1.val
  have hf : Matrix.blockDiagonal (paddingBlock head a) = L * Matrix.diagonal w * L.transpose := by
    change Matrix.blockDiagonal (fun b : T => paddingBlock head a b) = _
    simp_rw [padding_block_factorization]
    rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_diagonal]
    rw [← Matrix.blockDiagonal_transpose]
  have hL : L.det ≠ 0 := by
    dsimp [L]
    rw [Matrix.det_blockDiagonal]
    simp [lower_ones_det]
  have hr : (paddingGram head a).rank = Fintype.card {p : P // w p ≠ 0} := by
    rw [← Matrix.rank_reindex (occupationSplit head a) (occupationSplit head a),
      padding_gram_blocks, hf,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by rwa [Matrix.det_transpose]),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hL, Matrix.rank_diagonal]
  have hz : Fintype.card {p : P // w p = 0} = a.count head := by
    let e : {p : P // w p = 0} ≃ {j : Fin (a.count head + 1) // j ≠ 0} :=
      { toFun := fun p => ⟨p.val.1, ((difference_zero_iff head a p.val).mp p.property).2⟩
        invFun := fun j => ⟨(j.val, zeroTail _),
          (difference_zero_iff head a _).mpr ⟨rfl, j.property⟩⟩
        left_inv := by
          intro p
          apply Subtype.ext
          change (p.val.1, zeroTail _) = p.val
          have hb := ((difference_zero_iff head a p.val).mp p.property).1
          exact congrArg (fun b : T => (p.val.1, b)) hb.symm
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun j : Fin (a.count head + 1) => j=0)]
    simp
  rw [hr, Fintype.card_subtype_compl (fun p : P => w p = 0), hz]
  congr 1
  calc
    Fintype.card P = Fintype.card (TailBox a.count) :=
      (Fintype.card_congr (occupationSplit head a)).symm
    _ = ∏ i : A, (a.count i + 1) := by simp [TailBox, Fintype.card_pi]

private theorem normalized_padding_gram_rank (head : A) (a : Multiset A) :
    (normalizedPaddingGram head a).rank = (∏ i : A, (a.count i + 1)) - a.count head := by
  rw [← padding_gram_rank_eq, padding_gram_rank]

private theorem maximal_padding_gram_rank (head : A) (a : Multiset A)
    (hh : a.count head = Finset.univ.sup a.count) :
    (normalizedPaddingGram head a).rank =
      (∏ i : A, (a.count i + 1)) - Finset.univ.sup a.count := by
  rw [normalized_padding_gram_rank, hh]

end

def W (a : Multiset σ) (head : σ) : Matrix (σ × K a head) (K a head) ℂ :=
  relabelMatrix (a.count head) (fun i : TailAlphabet head => a.count i.val)
    (Equiv.optionSubtypeNe head) (Equiv.refl _)

private theorem W_gram (a : Multiset σ) (head : σ) :
    (W a head).conjTranspose * W a head = 1 :=
  relabel_matrix_gram _ _ _ _

private def emitLinear (a : Multiset σ) (head : σ) :
    Space (K a head) →ₗ[ℂ] Space (σ × K a head) := (W a head).toEuclideanLin

private theorem emit_linear_basis (a : Multiset σ) (head : σ) (s : K a head)
    (i : σ) (k : K a head) : emitLinear a head (basis s) (i, k) = W a head (i, k) s := by
  exact matrix_isometry_basis (W a head) (W_gram a head) s (i, k)

private theorem W_sink (a : Multiset σ) (head i : σ) (k : K a head) :
    W a head (i, k) none = if i = head ∧ k = none then 1 else 0 := by
  change (if paddingNext (a.count head) (fun j : TailAlphabet head => a.count j.val)
      none ((Equiv.optionSubtypeNe head).symm i) = k then
    (Real.sqrt (paddingProbability (a.count head)
      (fun j : TailAlphabet head => a.count j.val) none
      ((Equiv.optionSubtypeNe head).symm i)) : ℂ) else 0) = _
  by_cases hi : i = head
  · subst i
    rw [Equiv.optionSubtypeNe_symm_self]
    simp only [paddingNext, paddingProbability, Real.sqrt_one, Complex.ofReal_one,
      true_and]
    congr 1
    exact propext eq_comm
  · rw [Equiv.optionSubtypeNe_symm_of_ne hi]
    simp only [paddingNext, paddingProbability, Real.sqrt_zero, Complex.ofReal_zero,
      ite_self, hi, false_and, if_false]

private theorem emit_linear_sink (a : Multiset σ) (head : σ) :
    emitLinear a head (basis none) = basis (head, none) := by
  ext ⟨i, k⟩
  rw [emit_linear_basis, W_sink]
  simpa only [Prod.mk.injEq] using (basis_apply (head, none) (i, k)).symm

private def residualMemoryIndex (head : σ) (a b : Multiset σ) (hb : b ≤ a)
    (hr : 0 < tailCount head b) (h : Fin (b.count head + 1)) : K a head :=
  some (residualPaddingTail head a b hb hr, residualHeadIndex head a b hb h)

private theorem residual_linear_formula (head : σ) (a b : Multiset σ) (hb : b ≤ a)
    (hr : 0 < tailCount head b) (i : σ) (k : K a head) :
    emitLinear a head (paddingResidual head a b) (i, k) =
      ∑ h : Fin (b.count head + 1),
        (Real.sqrt (lastTailMass head (headSlice head b h.val)) : ℂ) *
          W a head (i, k) (residualMemoryIndex head a b hb hr h) := by
  rw [paddingResidual, dif_pos hb, dif_pos hr]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, emit_linear_basis]
  rfl

private theorem residual_linear_tail_free (head : σ) (a b : Multiset σ)
    (hb : b ≤ a) (hb0 : b ≠ 0) (hr : tailCount head b = 0) (i : σ) (k : K a head) :
    emitLinear a head (paddingResidual head a b) (i, k) =
      if i ∈ b then paddingResidual head a (b.erase i) k else 0 := by
  rw [padding_residual_tail_free head a b hb hr, emit_linear_sink]
  have hi := tail_free_membership head b hr hb0 i
  by_cases hih : i = head
  · subst i
    rw [if_pos (hi.mpr rfl), padding_residual_tail_free head a (b.erase head)
      ((Multiset.erase_le _ _).trans hb) (by rwa [tail_count_erase_head])]
    rw [basis_apply (head, none) (head, k), basis_apply none k]
    simp only [Prod.mk.injEq, true_and]
  · rw [if_neg (fun hib => hih (hi.mp hib))]
    rw [basis_apply (head, none) (i, k)]
    simp only [Prod.mk.injEq, hih, false_and, if_false]


section
variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem residual_matrix_absent (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount head b) (i : A) (hi : i ∉ b)
    (k : K a head) (h : Fin (b.count head + 1)) :
    W a head (i, k) (residualMemoryIndex head a b hb hr h) = 0 := by
  have hc : b.count i = 0 := Multiset.count_eq_zero.mpr hi
  by_cases hih : i = head
  · subst i
    have hh : h.val = 0 := by have := h.isLt; omega
    simp [W, relabelMatrix, weightedMatrix, relabelProbability,
      residualMemoryIndex, Equiv.optionSubtypeNe_symm_self, paddingProbability,
      residualHeadIndex, hh, headProbability]
  · simp [W, relabelMatrix, weightedMatrix, relabelProbability,
      residualMemoryIndex, Equiv.optionSubtypeNe_symm_of_ne hih, paddingProbability,
      residualPaddingTail, residualTail, tailProbability, hc]

private theorem residual_linear_absent (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hb0 : b ≠ 0) (i : A) (hi : i ∉ b) (k : K a head) :
    emitLinear a head (paddingResidual head a b) (i, k) = 0 := by
  by_cases hr : 0 < tailCount head b
  · rw [residual_linear_formula head a b hb hr]
    simp only [residual_matrix_absent head a b hb hr i hi k, mul_zero, Finset.sum_const_zero]
  · simpa only [if_neg hi] using residual_linear_tail_free head a b hb hb0 (by omega) i k

/-- Legal emissions from residuals with positive tail count. -/
private theorem residual_tail_erase (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : TailAlphabet head) :
    decrement (fun j : TailAlphabet head => a.count j.val)
      (residualTail head a b hb) i =
      residualTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) := by
  funext j
  apply Fin.ext
  by_cases hji : j = i
  · subst j
    simp [residualTail]
  · have hval : j.val ≠ i.val := fun h => hji (Subtype.ext h)
    simp [decrement_other, hji, residualTail, Multiset.count_erase_of_ne hval]

private theorem residual_positive_tail_erase (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : TailAlphabet head) (hi : i.val ∈ b) (hr : 2 ≤ tailCount head b)
    (he : 0 < tailCount head (b.erase i.val)) :
    decrementPositive (fun j : TailAlphabet head => a.count j.val)
      (residualPaddingTail head a b hb (by omega)) i (Multiset.count_pos.mpr hi)
      (by exact hr) =
      residualPaddingTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) he := by
  apply Subtype.ext
  exact residual_tail_erase head a b hb i

private theorem residual_tail_matrix (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : A) (hi : i ≠ head) (hib : i ∈ b)
    (hr : 2 ≤ tailCount head b)
    (he : 0 < tailCount head (b.erase i))
    (h : Fin (b.count head + 1)) (k : K a head) :
    W a head (i, k) (residualMemoryIndex head a b hb (by omega) h) =
      (Real.sqrt (tailProbability h.val (tailCount head b) (b.count i)) : ℂ) *
        basis ((Equiv.refl (K a head)) (some
          (residualPaddingTail head a (b.erase i)
            ((Multiset.erase_le _ _).trans hb) he,
           residualHeadIndex head a b hb h))) k := by
  have hd := residual_positive_tail_erase head a b hb ⟨i, hi⟩ hib hr he
  have hc : 0 < b.count i := Multiset.count_pos.mpr hib
  have hp : paddingProbability (a.count head)
      (fun j : TailAlphabet head => a.count j.val)
      (some (residualPaddingTail head a b hb (by omega),
        residualHeadIndex head a b hb h)) (some ⟨i, hi⟩) =
      tailProbability h.val (tailCount head b) (b.count i) := by
    change (if tailCount head b = 1 then _ else _) = _
    rw [if_neg (by omega)]
    rfl
  have hn : paddingNext (a.count head)
      (fun j : TailAlphabet head => a.count j.val)
      (some (residualPaddingTail head a b hb (by omega),
        residualHeadIndex head a b hb h)) (some ⟨i, hi⟩) =
      some (residualPaddingTail head a (b.erase i)
        ((Multiset.erase_le _ _).trans hb) he,
        residualHeadIndex head a b hb h) := by
    dsimp only [paddingNext]
    rw [dif_pos (show 0 < ((residualPaddingTail head a b hb (by omega)).val
        ⟨i, hi⟩).val from hc)]
    rw [dif_pos (show 1 < tailSum
        (residualPaddingTail head a b hb (by omega)).val from hr), hd]
  simp only [W, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.refl_symm,
    Equiv.optionSubtypeNe_symm_of_ne hi]
  rw [hp, hn]
  simp [basis_apply, eq_comm]

private theorem residual_linear_tail (head : A) (a b : Multiset A) (hb : b ≤ a)
    (i : A) (hi : i ≠ head) (hib : i ∈ b)
    (hr : 2 ≤ tailCount head b) (k : K a head) :
    emitLinear a head (paddingResidual head a b) (i, k) =
      paddingResidual head a (b.erase i) k := by
  have he : 0 < tailCount head (b.erase i) := by
    have := tail_count_erase_tail head b i hi hib
    omega
  have hbe : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
  have hh : (b.erase i).count head = b.count head :=
    Multiset.count_erase_of_ne (Ne.symm hi) b
  rw [residual_linear_formula head a b hb (by omega)]
  simp_rw [residual_tail_matrix head a b hb i hi hib hr he]
  rw [paddingResidual, dif_pos hbe, dif_pos he]
  simp only [WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul]
  have hs := head_slice_tail_amplitude head b
  simp_rw [← mul_assoc, mul_comm _ (Real.sqrt (tailProbability _ _ _) : ℂ),
    hs _ i hi hib hr]
  apply Fintype.sum_equiv (finCongr (congrArg (fun n => n + 1) hh.symm))
  intro h
  rfl

private theorem residual_linear_head (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hr : 0 < tailCount head b) (hh : head ∈ b)
    (k : K a head) :
      emitLinear a head (paddingResidual head a b)
        (head, k) =
      paddingResidual head a (b.erase head) k := by
  rw [residual_linear_formula head a b hb hr]
  have hbe : b.erase head ≤ a :=
    (Multiset.erase_le _ _).trans hb
  have hre : 0 < tailCount head (b.erase head) := by
    simpa only [tail_count_erase_head] using hr
  rw [paddingResidual, dif_pos hbe, dif_pos hre]
  simp only [WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have hc : (b.erase head).count head + 1 =
      b.count head := by
    have hbc := congrArg (Multiset.count head)
      (Multiset.cons_erase hh)
    simp only [Multiset.count_cons_self] at hbc
    rw [hbc]
  rw [Fin.sum_univ_succ]
  let e : Fin (b.count head) ≃
      Fin ((b.erase head).count head + 1) := finCongr hc.symm
  have hzero : (Real.sqrt (lastTailMass head
      (headSlice head b 0)) : ℂ) *
      W a head (head, k)
        (residualMemoryIndex head a b hb hr 0) = 0 := by
    simp [W, relabelMatrix, weightedMatrix, relabelProbability,
      paddingProbability, residualMemoryIndex,
      residualHeadIndex, headProbability]
  have hzero' : (Real.sqrt (lastTailMass head
      (headSlice head b (↑(0 : Fin (b.count head + 1))))) : ℂ) *
      W a head (head, k)
        (residualMemoryIndex head a b hb hr (0 : Fin (b.count head + 1))) = 0 := by
    exact hzero
  rw [hzero', zero_add]
  apply Fintype.sum_equiv e
  intro c
  have htail : residualPaddingTail head a b hb hr =
      residualPaddingTail head a (b.erase head) hbe hre := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp [residualPaddingTail, residualTail, Multiset.count_erase_of_ne i.property]
  have hhead : headPredecessor
      (residualHeadIndex head a b hb c.succ) =
      residualHeadIndex head a (b.erase head) hbe (e c) := by
    apply Fin.ext
    change c.val + 1 - 1 = c.val
    exact Nat.add_sub_cancel _ _
  have hp : paddingProbability (a.count head)
      (fun j : TailAlphabet head => a.count j.val)
      (some (residualPaddingTail head a b hb hr,
        residualHeadIndex head a b hb c.succ)) none =
      headProbability c.succ.val (tailCount head b) := by
    change (if tailCount head b = 1 then _ else _) = _
    by_cases hR : tailCount head b = 1
    · have hidxval : (residualHeadIndex head a b hb c.succ).val ≠ 0 :=
        Nat.succ_ne_zero c.val
      rw [if_pos hR, if_neg hidxval]
      simp only [headProbability, hR, Nat.cast_one, add_sub_cancel_right]
      have hpos : (0 : ℝ) < (c.val : ℝ) + 1 := by positivity
      simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using (div_self hpos.ne').symm
    · rw [if_neg hR]
      rfl
  have hn : paddingNext (a.count head)
      (fun j : TailAlphabet head => a.count j.val)
      (some (residualPaddingTail head a b hb hr,
        residualHeadIndex head a b hb c.succ)) none =
      some (residualPaddingTail head a (b.erase head) hbe hre,
        residualHeadIndex head a (b.erase head) hbe (e c)) := by
    dsimp only [paddingNext]
    rw [htail, hhead]
  simp only [W, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.refl_symm,
    Equiv.optionSubtypeNe_symm_self]
  rw [hp, hn]
  by_cases hmem : ((Equiv.refl (K a head)))
      (some (residualPaddingTail head a (b.erase head) hbe hre,
        residualHeadIndex head a (b.erase head) hbe (e c))) = k
  · change some _ = k at hmem
    rw [if_pos hmem]
    simp only [basis_apply, if_pos hmem.symm, mul_one]
    have ha := head_slice_head_amplitude head b c.succ.val
      (Nat.succ_pos c.val) hr
    rw [head_slice_erase_head_source head b ((e c).val)]
    have hec : (e c).val = c.val := rfl
    rw [hec]
    simpa only [Fin.val_succ, Nat.add_sub_cancel] using (mul_comm _ _).trans ha
  · change some _ ≠ k at hmem
    rw [if_neg hmem]
    simp only [basis_apply, if_neg (Ne.symm hmem), mul_zero]

private theorem residual_linear_one_tail (head : A) (a b : Multiset A) (hb : b ≤ a)
    (hr : tailCount head b = 1) (i : A) (hib : i ∈ b)
    (hi : i ≠ head) (k : K a head) :
    emitLinear a head (paddingResidual head a b) (i, k) =
      paddingResidual head a (b.erase i) k := by
  rw [residual_linear_formula head a b hb (by omega) i k]
  simp_rw [head_slice_one_amplitude head b _ hr]
  have htail : tailSum (residualTail head a b hb) = 1 := by
    exact hr
  have hbi : 0 < (residualTail head a b hb ⟨i, hi⟩).val := by
    simpa [residualTail] using (Multiset.count_pos.mpr hib)
  have hcoords := sum_one_coordinate
    (fun j : TailAlphabet head => a.count j.val)
    (residualTail head a b hb) htail ⟨i, hi⟩ hbi
  have hcount : b.count i = 1 := by
    simpa [residualTail] using hcoords ⟨i, hi⟩
  have herase : tailCount head (b.erase i) = 0 := by
    have ht := tail_count_erase_tail head b i hi hib
    omega
  have hberase : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
  have hsum : ∑ x : Fin (b.count head + 1),
      (Real.sqrt (if x = 0 then (1 : ℝ) else 0) : ℂ) = 1 := by
    rw [Fin.sum_univ_succ]
    simp
  rw [padding_residual_tail_free head a (b.erase i) hberase herase]
  simp [W, relabelMatrix, weightedMatrix, relabelNext,
    relabelProbability, paddingNext, paddingProbability, residualMemoryIndex,
    residualPaddingTail, residualTail, hcount, htail, hi,
    residualHeadIndex, hsum]
  simp only [basis_apply, eq_comm]


end

private theorem residual_linear_step (a : Multiset σ) (head : σ)
    (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : K a head) :
    emitLinear a head (paddingResidual head a r) (i, k) =
      if i ∈ r then paddingResidual head a (r.erase i) k else 0 := by
  by_cases ht : 0 < tailCount head r
  · by_cases hi : i ∈ r
    · rw [if_pos hi]
      by_cases hh : i = head
      · subst i
        exact residual_linear_head head a r hr ht hi k
      · by_cases hR : tailCount head r = 1
        · exact residual_linear_one_tail head a r hr hR i hi hh k
        · exact residual_linear_tail head a r hr i hh hi (by omega) k
    · rw [if_neg hi]
      exact residual_linear_absent head a r hr hr0 i hi k
  · exact residual_linear_tail_free head a r hr hr0 (by omega) i k

@[simp] private theorem tail_word_count_head (a : Multiset σ) (head : σ)
    (b : Tail a head) : (tailWord a head b).count head = 0 := by
  simp only [tailWord, Multiset.count_sum', Multiset.count_replicate]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg i.property

@[simp] private theorem tail_word_count (a : Multiset σ) (head : σ)
    (b : Tail a head) (i : TailAlphabet head) :
    (tailWord a head b).count i.val = (b i).val := by
  simp only [tailWord, Multiset.count_sum', Multiset.count_replicate, Subtype.val_inj]
  simpa only [Finset.mem_univ, if_true] using
    Finset.sum_ite_eq' Finset.univ i (fun j => (b j).val)

private theorem tail_word_injective (a : Multiset σ) (head : σ) :
    Function.Injective (tailWord a head) := by
  intro b c h
  funext i
  apply Fin.ext
  simpa only [tail_word_count] using congrArg (Multiset.count i.val) h

@[simp] private theorem tail_word_zero (a : Multiset σ) (head : σ) :
    tailWord a head 0 = 0 := by
  simp [tailWord]

private theorem tail_word_ne_zero (a : Multiset σ) (head : σ)
    (b : PositiveTail a head) : tailWord a head b.val ≠ 0 := by
  intro h
  apply b.property
  apply tail_word_injective a head
  simpa only [tail_word_zero] using h

private theorem tail_word_residual (a : Multiset σ) (head : σ)
    (r : Multiset σ) (hr : r ≤ a) :
    tailWord a head (residualTail head a r hr) = tailOcc head r := by
  apply Multiset.ext.mpr
  intro i
  by_cases hi : i = head
  · subst i
    simp [tailOcc]
  · rw [show i = (⟨i, hi⟩ : TailAlphabet head).val from rfl, tail_word_count]
    simp [residualTail, tailOcc, hi]

private theorem tail_occ_card (head : σ) (r : Multiset σ) :
    (tailOcc head r).card = tailCount head r := by
  have h := head_add_tail_count head (tailOcc head r)
  have ht : tailCount head (tailOcc head r) = tailCount head r := by
    apply Finset.sum_congr rfl
    intro i _
    simp [tailOcc, Multiset.count_filter, i.property]
  rw [ht] at h
  simpa [tailOcc] using h.symm

private theorem last_tail_eq_mass (head : σ) (r : Multiset σ) :
    lastTail head r = lastTailMass head r := by
  rw [lastTail, tail_occ_card]
  rfl

private theorem slice_eq_head_slice (a : Multiset σ) (head : σ)
    (r : Multiset σ) (hr : r ≤ a) (j : ℕ) :
    slice a head (residualTail head a r hr) j = headSlice head r j := by
  rw [slice, tail_word_residual]
  rfl

private theorem padding_eq_residual (a : Multiset σ) (head : σ) (r : Multiset σ) :
    padding a head r = paddingResidual head a r := by
  by_cases hr : r ≤ a
  · by_cases ht : 0 < tailCount head r
    · have hf : tailOcc head r ≠ 0 := by
        intro h
        have := (tail_filter_eq_zero head r).mp h
        omega
      ext q
      cases q with
      | none => simp [padding, hr, hf, padding_residual_none head a r hr ht]
      | some q =>
        rcases q with ⟨b, j⟩
        rw [padding_residual_coordinates head a r hr ht]
        have he : tailOcc head r = tailWord a head b.val ↔
            b = residualPaddingTail head a r hr ht := by
          rw [← tail_word_residual a head r hr]
          constructor
          · intro h
            exact Subtype.ext ((tail_word_injective a head h).symm)
          · rintro rfl
            rfl
        change (if r ≤ a ∧ tailOcc head r = tailWord a head b.val ∧ j.val ≤ r.count head
          then (Real.sqrt (lastTail head (slice a head b.val j.val)) : ℂ) else 0) = _
        simp only [hr, true_and, he]
        by_cases hb : b = residualPaddingTail head a r hr ht
        · subst b
          simp only [true_and, residualPaddingTail, slice_eq_head_slice, last_tail_eq_mass]
        · simp only [hb, false_and, if_false]
    · have hz : tailCount head r = 0 := by omega
      have hf : tailOcc head r = 0 := (tail_filter_eq_zero head r).mpr hz
      rw [padding_residual_tail_free head a r hr hz]
      ext q
      cases q with
      | none => simp [padding, hr, hf]
      | some q =>
        rcases q with ⟨b, j⟩
        have hn := tail_word_ne_zero a head b
        simp [padding, hr, hf, Ne.symm hn, basis_apply]
  · ext q
    cases q <;> simp [padding, paddingResidual, hr]

private theorem phi_eq_normalized (a : Multiset σ) (head : σ) (r : Multiset σ) :
    phi a head r = normalizedPadding head a r := by
  rw [phi, padding_eq_residual]
  rfl

private theorem padding_residual_intertwining_all_heads (a : Multiset σ) (head : σ)
    (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : K a head) :
    (W a head).mulVec (fun s : K a head => padding a head r s) (i, k) =
      if i ∈ r then padding a head (r.erase i) k else 0 := by
  simp only [padding_eq_residual]
  exact residual_linear_step a head r hr hr0 i k

private theorem padding_residual_intertwining [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r : Multiset σ) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : σ) (k : K a head) :
    (W a head).mulVec (fun s : K a head => padding a head r s) (i, k) =
      if i ∈ r then padding a head (r.erase i) k else 0 :=
  padding_residual_intertwining_all_heads a head r hr hr0 i k

private theorem block_occupation_eq_slice (a : Multiset σ) (head : σ)
    (b : Tail a head) (j : ℕ) : blockOccupation head a b j = slice a head b j := by
  let r := (occupationSplit head a).symm (0, b)
  have h : residualTail head a (occ a r) (box_occupation_le a r) = b := by
    funext i
    apply Fin.ext
    simp [residualTail, r, occupationSplit, Equiv.piSplitAt, i.property]
  have hs := slice_eq_head_slice a head (occ a r) (box_occupation_le a r) j
  rw [h] at hs
  exact hs.symm

private theorem block_mass_eq (a : Multiset σ) (head : σ) (b : Tail a head) (j : ℕ) :
    blockMass head a b j = m a head b j := by
  simp only [blockMass, m, M, block_occupation_eq_slice]

private theorem block_difference_eq (a : Multiset σ) (head : σ)
    (b : Tail a head) (j : ℕ) : blockDifference head a b j = delta a head b j := by
  simp only [blockDifference, delta, block_mass_eq]

private theorem padding_block_eq (a : Multiset σ) (head : σ) (b : Tail a head) :
    paddingBlock head a b = block a head b := by
  ext j k
  rw [padding_block_entry, block_mass_eq]
  rfl

private theorem padding_gram_eq_B (a : Multiset σ) (head : σ) :
    paddingGram head a = B a head := by
  ext r s
  have h := congrFun (congrFun (padding_gram_blocks head a)
    ((occupationSplit head a) r)) ((occupationSplit head a) s)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at h
  change paddingGram head a r s = Matrix.blockDiagonal (paddingBlock head a)
    (r head, tailIndex a head r) (s head, tailIndex a head s) at h
  rw [Matrix.blockDiagonal_apply'] at h
  simp_rw [padding_block_eq] at h
  exact h

private theorem memory_card (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) : Fintype.card (K a head) = N a := by
  rw [N, ← hmax]
  exact occupation_memory_card a head

private theorem block_factorization (a : Multiset σ) (head : σ) (b : Tail a head) :
    block a head b = L (a.count head) *
      Matrix.diagonal (fun j : Fin (a.count head + 1) => (delta a head b j.val : ℂ)) *
        (L (a.count head)).transpose := by
  have h := padding_block_factorization head a b
  rw [padding_block_eq] at h
  simp_rw [block_difference_eq] at h
  exact h

private theorem block_rank (a : Multiset σ) (head : σ) (b : Tail a head) :
    (block a head b).rank = if b = 0 then 1 else a.count head + 1 := by
  rw [← padding_block_eq]
  by_cases hb : b = 0
  · subst b
    rw [if_pos rfl]
    exact padding_block_rank_zero head a
  · rw [if_neg hb]
    exact padding_block_rank_positive head a b hb

private theorem delta_zero (a : Multiset σ) (head : σ) (j : ℕ) :
    delta a head 0 j = if j = 0 then 1 else 0 := by
  rw [← block_difference_eq]
  exact block_difference_zero_tail head a j

private theorem delta_pos (a : Multiset σ) (head : σ) (b : Tail a head)
    (hb : b ≠ 0) (j : ℕ) : 0 < delta a head b j := by
  rw [← block_difference_eq]
  exact block_difference_pos head a b hb j

private theorem last_tail_delta (a : Multiset σ) (head : σ) (b : Tail a head)
    (hb : b ≠ 0) (j : ℕ) : lastTail head (slice a head b j) = delta a head b j := by
  have hr : 0 < tailCount head (blockOccupation head a b 0) := by
    rw [block_occupation_tail]
    exact positive_tail_sum _ ⟨b, hb⟩
  have h := last_tail_mass_head_slice head (blockOccupation head a b 0) hr j
  simp only [block_occupation_slice] at h
  change lastTailMass head (blockOccupation head a b j) = blockDifference head a b j at h
  simpa only [last_tail_eq_mass, ← block_occupation_eq_slice, ← block_difference_eq] using h

private theorem block_ratio (a : Multiset σ) (head : σ) (b : Tail a head)
    (j : ℕ) (hj : 1 ≤ j) :
    m a head b j / m a head b (j - 1) =
      ((j : ℝ) + ((tailWord a head b).card : ℝ)) / (j : ℝ) := by
  let r := blockOccupation head a b j
  have hh : r.count head = j := head_slice_count_head head _ j
  have hmem : head ∈ r := Multiset.count_pos.mp (by rw [hh]; exact hj)
  have he : r.erase head = blockOccupation head a b (j - 1) := by
    exact head_slice_erase_head head _ j
  have hc : r.card = j + (tailWord a head b).card := by
    rw [show r = slice a head b j from block_occupation_eq_slice a head b j]
    simp only [slice, Multiset.card_add, Multiset.card_replicate]
  have hm := erase_multiplicity_real r head hmem
  rw [he, hh] at hm
  have hp : m a head b (j - 1) ≠ 0 := by
    dsimp only [m, M]
    exact_mod_cast (multiplicity_pos (slice a head b (j - 1)) rfl).ne'
  apply (div_eq_div_iff hp (by exact_mod_cast Nat.ne_of_gt hj)).mpr
  calc
    m a head b j * (j : ℝ) = (r.card : ℝ) * m a head b (j - 1) := by
      simpa only [r, block_occupation_eq_slice, m, M, mul_comm] using hm.symm
    _ = ((j : ℝ) + ((tailWord a head b).card : ℝ)) * m a head b (j - 1) := by
      rw [hc, Nat.cast_add]

private theorem block_ratio_strict (a : Multiset σ) (head : σ) (b : Tail a head)
    (hb : b ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
    1 < m a head b j / m a head b (j - 1) := by
  apply (one_lt_div₀ (show (0 : ℝ) < m a head b (j - 1) by
    dsimp only [m, M]
    exact_mod_cast multiplicity_pos (slice a head b (j - 1)) rfl)).mpr
  simpa only [block_mass_eq] using block_mass_strict head a b hb j hj

private theorem same_tail_count (head : σ) (r s : Multiset σ)
    (h : tailOcc head r = tailOcc head s) (i : σ) (hi : i ≠ head) :
    r.count i = s.count i := by
  simpa [tailOcc, Multiset.count_filter, hi] using congrArg (Multiset.count i) h

private theorem same_tail_le (head : σ) (r s : Multiset σ)
    (h : tailOcc head r = tailOcc head s) : r ≤ s ↔ r.count head ≤ s.count head := by
  constructor
  · intro hrs
    exact Multiset.le_iff_count.mp hrs head
  · intro hh
    apply Multiset.le_iff_count.mpr
    intro i
    by_cases hi : i = head
    · simpa only [hi] using hh
    · exact (same_tail_count head r s h i hi).le

private theorem tail_sub_zero_iff (head : σ) (r s : Multiset σ) (h : s ≤ r) :
    tailOcc head (r - s) = 0 ↔ tailOcc head r = tailOcc head s := by
  have hle : tailOcc head s ≤ tailOcc head r := Multiset.filter_le_filter _ h
  rw [tailOcc, Multiset.filter_sub, tsub_eq_zero_iff_le]
  exact ⟨fun h' => le_antisymm h' hle, fun h' => h'.le⟩

private theorem head_only_M (head : σ) (r : Multiset σ) (h : tailOcc head r = 0) :
    M r = 1 := by
  have hz := (tail_filter_eq_zero head r).mp h
  simpa only [head_slice_self, M] using tail_free_multiplicity head r hz (r.count head)

private theorem normalized_scalar (r s : Multiset σ) :
    (residualScale r : ℂ)⁻¹ * ((residualScale s : ℂ)⁻¹ * (M s : ℂ)) =
      (Real.sqrt ((M s : ℝ) / (M r : ℝ)) : ℂ) := by
  have h : (residualScale r)⁻¹ * ((residualScale s)⁻¹ * (M s : ℝ)) =
      Real.sqrt ((M s : ℝ) / (M r : ℝ)) := by
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
    change (residualScale r)⁻¹ * ((residualScale s)⁻¹ * (M s : ℝ)) =
      residualScale s / residualScale r
    field_simp [(scale_pos r).ne', (scale_pos s).ne']
    simpa only [pow_two, M] using (scale_sq s).symm
  exact_mod_cast h

private theorem phi_inner_of_le (a : Multiset σ) (head : σ) (r s : Multiset σ)
    (hr : r ≤ a) (hs : s ≤ a) (hle : s ≤ r) :
    inner ℂ (phi a head r) (phi a head s) =
      (Real.sqrt (((M s : ℝ) * (M (r - s) : ℝ)) / (M r : ℝ)) : ℂ) * z head (r - s) := by
  rw [phi_eq_normalized, phi_eq_normalized]
  simp only [normalizedPadding, inner_smul_left, inner_smul_right, map_inv₀,
    Complex.conj_ofReal]
  rw [padding_residual_inner head a r s hr hs]
  change (residualScale s : ℂ)⁻¹ * ((residualScale r : ℂ)⁻¹ *
    (if tailOcc head r = tailOcc head s then
      (M (headSlice head r (min (r.count head) (s.count head))) : ℂ) else 0)) = _
  by_cases ht : tailOcc head r = tailOcc head s
  · rw [if_pos ht]
    have hz := (tail_sub_zero_iff head r s hle).mpr ht
    have hm := head_only_M head (r - s) hz
    have hh := Multiset.le_iff_count.mp hle head
    have hslice : headSlice head r (s.count head) = s := by
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i
        exact head_slice_count_head head r _
      · rw [head_slice_count_tail head r _ i hi]
        exact same_tail_count head r s ht i hi
    simp only [min_eq_right hh, hslice, z, hz, if_true, hm, Nat.cast_one,
      mul_one]
    simpa only [mul_left_comm] using normalized_scalar r s
  · have hz : tailOcc head (r - s) ≠ 0 := fun h => ht ((tail_sub_zero_iff head r s hle).mp h)
    simp only [if_neg ht, z, if_neg hz, mul_zero]

private theorem phi_gram (a : Multiset σ) (head : σ) :
    Matrix.gram ℂ (fun r : Box a => phi a head (occ a r)) = G a head := by
  ext r s
  change inner ℂ (phi a head (occ a r)) (phi a head (occ a s)) = G a head r s
  rw [G]
  by_cases hsr : occ a s ≤ occ a r
  · rw [if_pos hsr]
    exact phi_inner_of_le a head _ _ (box_occupation_le a r) (box_occupation_le a s) hsr
  · rw [if_neg hsr]
    by_cases hrs : occ a r ≤ occ a s
    · rw [if_pos hrs]
      have h := congrArg star (phi_inner_of_le a head _ _
        (box_occupation_le a s) (box_occupation_le a r) hrs)
      simpa only [← starRingEnd_apply, inner_conj_symm] using h
    · rw [if_neg hrs, phi_eq_normalized, phi_eq_normalized]
      have ht : tailOcc head (occ a r) ≠ tailOcc head (occ a s) := by
        intro he
        rcases le_total ((occ a r).count head) ((occ a s).count head) with h | h
        · exact hrs ((same_tail_le head _ _ he).mpr h)
        · exact hsr ((same_tail_le head _ _ he.symm).mpr h)
      dsimp only [tailOcc] at ht
      simp only [normalizedPadding, inner_smul_left, inner_smul_right,
        padding_residual_inner head a _ _ (box_occupation_le a r) (box_occupation_le a s),
        if_neg ht, mul_zero]

private theorem normalized_gram_eq_G (a : Multiset σ) (head : σ) :
    normalizedPaddingGram head a = G a head := by
  have h := phi_gram a head
  simpa only [phi_eq_normalized, normalizedPaddingGram] using h

private theorem gram_congruence (a : Multiset σ) (head : σ) : D a * G a head * D a = B a head := by
  rw [← normalized_gram_eq_G, ← padding_gram_eq_diagonal, padding_gram_eq_B]

private theorem phi_norm (a : Multiset σ) (head : σ) (r : Multiset σ) (hr : r ≤ a) :
    ‖phi a head r‖ = 1 := by
  rw [phi_eq_normalized]
  exact normalized_padding_norm head a r hr

private theorem phi_zero (a : Multiset σ) (head : σ) : phi a head 0 = basis none := by
  rw [phi_eq_normalized, normalized_padding_zero]

private theorem phi_axis (a : Multiset σ) (head : σ) (j : ℕ) (hj : j ≤ a.count head) :
    phi a head (Multiset.replicate j head) = basis none := by
  rw [phi_eq_normalized]
  exact normalized_padding_axis head a j hj

private theorem phi_moment (a : Multiset σ) (head : σ) (r : Multiset σ) (hr : r ≤ a) :
    inner ℂ (phi a head r) (phi a head 0) = z head r := by
  rw [phi_zero, phi_eq_normalized]
  have h := padding_moment head a r hr
  change inner ℂ (normalizedPadding head a r) (basis none) = _ at h
  rw [h]
  change (if tailCount head r = 0 then 1 else 0) = if tailOcc head r = 0 then 1 else 0
  simp only [show tailOcc head r = 0 ↔ tailCount head r = 0 from tail_filter_eq_zero head r]

private theorem erasure_normalization (r : Multiset σ) (i : σ) (hi : i ∈ r) :
    (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) *
      (residualScale (r.erase i) : ℂ)⁻¹ = (residualScale r : ℂ)⁻¹ := by
  have hc : (0 : ℝ) < r.card := by
    have hr0 : r ≠ 0 := by
      intro h
      simpa [h] using hi
    exact_mod_cast Multiset.card_pos.mpr hr0
  have hm := erase_multiplicity_real r i hi
  have he : (M (r.erase i) : ℝ) = ((r.count i : ℝ) / (r.card : ℝ)) * (M r : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hc.ne').mpr
    simpa only [M, mul_comm] using hm
  have hs : residualScale (r.erase i) =
      Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) * residualScale r := by
    change Real.sqrt (M (r.erase i) : ℝ) = _
    rw [he, Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hc.le)]
    rfl
  apply (mul_inv_eq_iff_eq_mul₀ (scale_ne_zero (r.erase i))).mpr
  rw [hs, Complex.ofReal_mul]
  field_simp [scale_ne_zero r]

private theorem image_coordinates [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r : Multiset σ) (hr : r ≤ a) :
    ((EuclideanSpace.basisFun σ ℂ).tensorProduct
      (EuclideanSpace.basisFun (K a head) ℂ)).repr (image a head r) =
        emitLinear a head (phi a head r) := by
  by_cases hz : r = 0
  · subst r
    rw [image, if_pos rfl, phi_zero, emit_linear_sink]
    ext ⟨i, k⟩
    simp only [OrthonormalBasis.tensorProduct_repr_tmul_apply,
      EuclideanSpace.basisFun_repr, basis_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  · rw [image, if_neg hz]
    ext ⟨i, k⟩
    simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
      basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have hstep := padding_residual_intertwining a head hmax r hr hz i k
    simp only [phi, map_smul, PiLp.smul_apply, smul_eq_mul]
    change _ = (residualScale r : ℂ)⁻¹ *
      (W a head).mulVec (fun s => padding a head r s) (i, k)
    rw [hstep]
    by_cases hi : i ∈ r
    · rw [if_pos hi]
      change _ * ((residualScale (r.erase i) : ℂ)⁻¹ * padding a head (r.erase i) k) = _
      rw [← mul_assoc, erasure_normalization r i hi]
    · rw [if_neg hi, Multiset.count_eq_zero.mpr hi]
      simp

private theorem prescribed_image_gram [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r s : Multiset σ)
    (hr : r ≤ a) (hs : s ≤ a) :
    inner ℂ (image a head r) (image a head s) = inner ℂ (phi a head r) (phi a head s) := by
  let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (K a head) ℂ)
  rw [← b.repr.inner_map_map, image_coordinates a head hmax r hr,
    image_coordinates a head hmax s hs]
  exact (matrixIsometry (W a head) (W_gram a head)).inner_map_map _ _

private theorem prescribed_dependencies [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count)
    (J : Type v) [Fintype J] (r : J → Multiset σ) (c : J → ℂ)
    (hr : ∀ j, r j ≤ a) (hdep : (∑ j : J, c j • phi a head (r j)) = 0) :
    (∑ j : J, c j • image a head (r j)) = 0 := by
  letI : NormedAddCommGroup (Space σ ⊗[ℂ] Space (K a head)) := inferInstance
  letI : InnerProductSpace ℂ (Space σ ⊗[ℂ] Space (K a head)) := inferInstance
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    inner ℂ (∑ j, c j • image a head (r j)) (∑ j, c j • image a head (r j)) =
      inner ℂ (∑ j, c j • phi a head (r j)) (∑ j, c j • phi a head (r j)) := by
        simp only [sum_inner, inner_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [inner_smul_right, inner_smul_left]
        rw [prescribed_image_gram a head hmax (r k) (r j) (hr k) (hr j),
          inner_smul_right, inner_smul_left]
    _ = 0 := by rw [hdep, inner_zero_left]

private theorem residual_gram_recurrence (a : Multiset σ) (head : σ) (r s : Multiset σ)
    (hr : r ≤ a) (hs : s ≤ a) (hr0 : r ≠ 0) (hs0 : s ≠ 0) :
    inner ℂ (paddingResidual head a r) (paddingResidual head a s) =
      ∑ i : σ, if i ∈ r ∧ i ∈ s then
        inner ℂ (paddingResidual head a (r.erase i)) (paddingResidual head a (s.erase i))
      else 0 := by
  have h := (matrixIsometry (W a head) (W_gram a head)).inner_map_map
    (paddingResidual head a r) (paddingResidual head a s)
  change inner ℂ (emitLinear a head (paddingResidual head a r))
    (emitLinear a head (paddingResidual head a s)) = _ at h
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  change (∑ q : σ × K a head,
    emitLinear a head (paddingResidual head a s) q *
      star (emitLinear a head (paddingResidual head a r) q)) = _ at h
  rw [Fintype.sum_prod_type] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [residual_linear_step a head r hr hr0 i,
    residual_linear_step a head s hs hs0 i]
  by_cases hir : i ∈ r <;> by_cases his : i ∈ s
  · simp only [hir, his, and_self, if_true]
    rfl
  all_goals simp [hir, his]

private def lowerBox (a : Multiset σ) (r : Box a) (i : σ) : Box a :=
  fun j => ⟨(r j).val - if j = i then 1 else 0,
    lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩

private theorem lower_occ (a : Multiset σ) (r : Box a) (i : σ) :
    occ a (lowerBox a r i) = (occ a r).erase i := by
  apply Multiset.ext.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simp only [occ_count, lowerBox, if_true, Multiset.count_erase_self]
  · simp only [occ_count, lowerBox, if_neg hji, Nat.sub_zero,
      Multiset.count_erase_of_ne hji]

private theorem B_recurrence (a : Multiset σ) (head : σ) (r s : Box a)
    (hr : occ a r ≠ 0) (hs : occ a s ≠ 0) :
    B a head r s = ∑ i : σ, if 0 < (r i).val ∧ 0 < (s i).val then
      B a head (lowerBox a r i) (lowerBox a s i) else 0 := by
  simp only [← padding_gram_eq_B, paddingGram, Matrix.gram_apply, lower_occ]
  rw [residual_gram_recurrence a head _ _ (box_occupation_le a r)
    (box_occupation_le a s) hr hs]
  simp only [← Multiset.count_pos, occ_count]

private theorem phi_span (a : Multiset σ) (head : σ) :
    Submodule.span ℂ {v : Space (K a head) |
      ∃ r : Multiset σ, r ≤ a ∧ v = phi a head r} = ⊤ := by
  let S := Submodule.span ℂ {v : Space (K a head) |
    ∃ r : Multiset σ, r ≤ a ∧ v = phi a head r}
  let f : Box a → S := fun r =>
    ⟨phi a head (occ a r), Submodule.subset_span ⟨occ a r, box_occupation_le a r, rfl⟩⟩
  have hg : Matrix.gram ℂ f = G a head := by
    rw [← phi_gram]
    ext r s
    exact (Submodule.coe_inner S (f r) (f s)).symm
  have hb : (Matrix.gram ℂ f).rank ≤ Module.finrank ℂ S := by
    rw [Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℂ S) f]
    exact (Matrix.rank_mul_le_right _ _).trans (by
      simpa using Matrix.rank_le_card_height
        (Matrix.of fun i r => (stdOrthonormalBasis ℂ S).repr (f r) i))
  rw [hg, ← normalized_gram_eq_G, normalized_padding_gram_rank] at hb
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le S)
  rw [finrank_euclideanSpace]
  exact (occupation_memory_card a head).le.trans hb

private theorem phi_nonterminal (a : Multiset σ) (head : σ) (hh : 0 < a.count head) :
    phi a head 0 = phi a head (Multiset.replicate 1 head) ∧
      Submodule.span ℂ {v : Space (K a head) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phi a head r} = ⊤ := by
  have heq : phi a head 0 = phi a head (Multiset.replicate 1 head) := by
    rw [phi_zero, phi_axis a head 1 hh]
  refine ⟨heq, ?_⟩
  rw [← top_le_iff, ← phi_span a head]
  apply Submodule.span_le.mpr
  rintro v ⟨r, hr, rfl⟩
  apply Submodule.subset_span
  by_cases hz : r = 0
  · refine ⟨Multiset.replicate 1 head, ?_, by simp, hz ▸ heq⟩
    simpa only [Multiset.replicate_one, Multiset.singleton_le] using Multiset.count_pos.mp hh
  · exact ⟨r, hr, hz, rfl⟩

private theorem zero_memory (head : σ) : N (0 : Multiset σ) = 1 ∧
    Nonempty (Space (K (0 : Multiset σ) head) ≃ₗᵢ[ℂ] ℂ) := by
  have hc : Fintype.card (K (0 : Multiset σ) head) = 1 := by
    simpa using occupation_memory_card (0 : Multiset σ) head
  have hz : Finset.univ.sup (fun _ : σ => 0) = 0 := by
    apply le_antisymm (Finset.sup_le (fun _ _ => le_rfl)) (Nat.zero_le _)
  have hn : N (0 : Multiset σ) = 1 := by simp [N, hz]
  let e : K (0 : Multiset σ) head ≃ Fin 1 :=
    (Fintype.equivFin _).trans (finCongr hc)
  exact ⟨hn, ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).trans
    (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm⟩⟩


section
variable {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

private def blankMemory (blank : A) : Space K →ₗᵢ[ℂ] Space (A × K) :=
  coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))

private theorem blank_memory_apply (blank : A) (x : Space K) (i : A) (k : K) :
    blankMemory blank x (i, k) = if i = blank then x k else 0 := by
  by_cases hi : i = blank
  · subst i
    simpa [blankMemory, blankInjection] using
      (coordinate_embedding_apply (blankInjection blank (Function.Embedding.refl K)) x k)
  · rw [if_neg hi]
    apply coordinate_embedding_off_range
    rintro ⟨j, hj⟩
    exact hi (congrArg Prod.fst hj).symm

private theorem initialized_apply_all (blank : A) (n : ℕ) (x : Space K)
    (w : Fin n → A) (k : K) :
    initialized blank n x (w, k) = if w = (fun _ => blank) then x k else 0 := by
  classical
  conv_lhs => rw [basis_expansion x]
  simp only [map_sum, map_smul, initialize_basis]
  by_cases hw : w = (fun _ => blank) <;>
    simp [blankState, basis_apply, Prod.mk.injEq, hw]

private theorem first_gate_initialized (blank : A) (n : ℕ) (U : Unitary (A × K))
    (x : Space K) (w : Fin (n + 1) → A) (k : K) :
    firstGate n U (initialized blank (n + 1) x) (w, k) =
      if Fin.tail w = (fun _ => blank) then U (blankMemory blank x) (w 0, k) else 0 := by
  rw [first_gate_apply]
  have hc (i : A) (u : Fin n → A) :
      Fin.cons i u = (fun _ => blank) ↔ i = blank ∧ u = (fun _ => blank) := by
    simp [funext_iff, Fin.forall_fin_succ]
  have hv : (WithLp.toLp 2 (fun p : A × K =>
      initialized blank (n + 1) x (Fin.cons p.1 (Fin.tail w), p.2))) =
      if Fin.tail w = (fun _ => blank) then blankMemory blank x else 0 := by
    ext p
    rcases p with ⟨i, j⟩
    by_cases ht : Fin.tail w = (fun _ => blank) <;>
      simp [initialized_apply_all, hc, ht, blank_memory_apply]
  rw [hv]
  split <;> simp_all

/-- Actual unitary circuit recursion on an arbitrary pure initial memory. -/
private theorem circuit_initialized_step (blank : A) (U : ℕ → Unitary (A × K))
    (n t : ℕ) (x : Space K) (w : Fin (n + 1) → A) (k : K) :
    circuit U (n + 1) t (initialized blank (n + 1) x) (w, k) =
      circuit U n (t + 1)
        (initialized blank n (WithLp.toLp 2
          (fun j : K => U t (blankMemory blank x) (w 0, j)))) (Fin.tail w, k) := by
  simp only [circuit, LinearIsometryEquiv.trans_apply, tail_gate_apply]
  have hv : (WithLp.toLp 2 (fun p : Register A K n =>
      firstGate n (U t) (initialized blank (n + 1) x) (Fin.cons (w 0) p.1, p.2))) =
      initialized blank n (WithLp.toLp 2
        (fun j : K => U t (blankMemory blank x) (w 0, j))) := by
    ext p
    rcases p with ⟨u, j⟩
    simp [first_gate_initialized, initialized_apply_all]
  rw [hv]

private theorem occupation_cons_eq {n : ℕ} (i : A) (w : Word A n) :
    occupation (Fin.cons i w) = i ::ₘ occupation w := by
  simp only [occupation, List.ofFn_cons]
  rfl

private theorem occupation_head_tail_iff {n : ℕ} (w : Word A (n + 1)) (b : Multiset A) :
    occupation w = b ↔ w 0 ∈ b ∧ occupation (Fin.tail w) = b.erase (w 0) := by
  conv_lhs => rw [← Fin.cons_self_tail w, occupation_cons_eq]
  rw [← Multiset.singleton_add, add_comm ({w 0} : Multiset A),
    Multiset.add_singleton_eq_iff]

/-- Local residual equations imply every coefficient of the actual repeated circuit.
The local equations are construction obligations, not an assumed output theorem. -/
private theorem circuit_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ n t b, b.card = n → b ≤ a → ∀ (w : Word A n) k,
      circuit (fun _ => U) n t (initialized blank n (r b)) (w, k) =
        if occupation w = b then f k else 0 := by
  intro n
  induction n with
  | zero =>
    intro t b hb hba w k
    have hb0 : b = 0 := Multiset.card_eq_zero.mp hb
    subst b
    have hw : w = (fun _ => blank) := Subsingleton.elim _ _
    simp [circuit, initialized_apply_all, hzero, hw, occupation]
  | succ n ih =>
    intro t b hb hba w k
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb
    rw [circuit_initialized_step]
    have hv : (WithLp.toLp 2
        (fun j : K => U (blankMemory blank (r b)) (w 0, j))) =
        if w 0 ∈ b then r (b.erase (w 0)) else 0 := by
      ext j
      by_cases hi : w 0 ∈ b <;> simp [hstep b hba hb0, hi]
    rw [hv]
    by_cases hi : w 0 ∈ b
    · rw [if_pos hi]
      have hcard : (b.erase (w 0)).card = n := by
        simp [Multiset.card_erase_of_mem hi, hb]
      rw [ih (t + 1) (b.erase (w 0)) hcard ((Multiset.erase_le _ _).trans hba)]
      simp only [occupation_head_tail_iff w b, hi, true_and]
    · have hw : occupation w ≠ b := fun h => hi ((occupation_head_tail_iff w b).mp h).1
      simp [hi, hw]

private theorem normalized_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ w k, circuit (fun _ => U) a.card 0
      (initialized blank a.card ((Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ • r a))
      (w, k) = sectorVector a.card a w * f k := by
  intro w k
  simp only [map_smul]
  change (Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ *
    circuit (fun _ => U) a.card 0 (initialized blank a.card (r a)) (w, k) = _
  rw [circuit_output_of_residuals blank U a r f hzero hstep a.card 0 a rfl le_rfl]
  by_cases hw : occupation w = a <;> simp [sectorVector, sectorWords, hw]


end

private def memoryCoordinates (a : Multiset σ) (head : σ) (e : K a head ≃ Fin (N a)) :
    Space (K a head) ≃ₗᵢ[ℂ] Space (Fin (N a)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

private theorem memory_coordinates_eq_embedding (a : Multiset σ) (head : σ)
    (e : K a head ≃ Fin (N a)) (x : Space (K a head)) :
    memoryCoordinates a head e x = coordinateEmbedding e.toEmbedding x := by
  ext k
  obtain ⟨j, rfl⟩ := e.surjective k
  change x (e.symm (e j)) = coordinateEmbedding e.toEmbedding x (e.toEmbedding j)
  rw [e.symm_apply_apply]
  exact (coordinate_embedding_apply e.toEmbedding x j).symm

private theorem memory_coordinates_apply (a : Multiset σ) (head : σ)
    (e : K a head ≃ Fin (N a)) (x : Space (K a head)) (k : K a head) :
    memoryCoordinates a head e x (e k) = x k := by
  change x (e.symm (e k)) = x k
  rw [e.symm_apply_apply]

private theorem phiFin_eq_coordinates (a : Multiset σ) (head : σ)
    (e : K a head ≃ Fin (N a)) (r : Multiset σ) :
    phiFin a head e r = memoryCoordinates a head e (phi a head r) := by
  rw [memory_coordinates_eq_embedding]
  rfl

private def emissionCoordinates (a : Multiset σ) (head : σ) (e : K a head ≃ Fin (N a)) :
    Space (Fin (N a)) →ₗᵢ[ℂ] Space (σ × Fin (N a)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr (Equiv.refl σ) e)).toLinearIsometry.comp
      ((matrixIsometry (W a head) (W_gram a head)).comp
        (memoryCoordinates a head e).symm.toLinearIsometry)

private theorem emission_coordinates_apply (a : Multiset σ) (head : σ)
    (e : K a head ≃ Fin (N a)) (x : Space (K a head)) (i : σ) (k : K a head) :
    emissionCoordinates a head e (memoryCoordinates a head e x) (i, e k) =
      emitLinear a head x (i, k) := by
  change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr (Equiv.refl σ) e)
    (matrixIsometry (W a head) (W_gram a head)
      ((memoryCoordinates a head e).symm (memoryCoordinates a head e x)))) (i, e k) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  change emitLinear a head x (i, e.symm (e k)) = _
  rw [e.symm_apply_apply]

private theorem normalized_emit_step [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r : Multiset σ) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : σ) (k : K a head) :
    emitLinear a head (phi a head r) (i, k) =
      (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) * phi a head (r.erase i) k := by
  have h := congrArg (fun x : Space (σ × K a head) => x (i, k))
    (image_coordinates a head hmax r hr)
  simp only [image, if_neg hr0, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply,
    EuclideanSpace.basisFun_repr, basis_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h.symm

private theorem phiFin_gram (a : Multiset σ) (head : σ) (e : K a head ≃ Fin (N a)) :
    Matrix.gram ℂ (fun r : Box a => phiFin a head e (occ a r)) = G a head := by
  rw [← phi_gram]
  ext r s
  exact (coordinateEmbedding e.toEmbedding).inner_map_map _ _

private theorem phiFin_nonterminal (a : Multiset σ) (head : σ)
    (e : K a head ≃ Fin (N a)) (hh : 0 < a.count head) :
    phiFin a head e 0 = phiFin a head e (Multiset.replicate 1 head) ∧
      Submodule.span ℂ {v : Space (Fin (N a)) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phiFin a head e r} = ⊤ := by
  have h := phi_nonterminal a head hh
  constructor
  · exact congrArg (coordinateEmbedding e.toEmbedding) h.1
  · let E := memoryCoordinates a head e
    let S := {v : Space (K a head) |
      ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phi a head r}
    have hs : {v : Space (Fin (N a)) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phiFin a head e r} = E '' S := by
      ext v
      constructor
      · rintro ⟨r, hr, hr0, rfl⟩
        exact ⟨phi a head r, ⟨r, hr, hr0, rfl⟩, (phiFin_eq_coordinates a head e r).symm⟩
      · rintro ⟨x, ⟨r, hr, hr0, rfl⟩, rfl⟩
        exact ⟨r, hr, hr0, (phiFin_eq_coordinates a head e r).symm⟩
    rw [hs]
    change Submodule.span ℂ (E.toLinearEquiv.toLinearMap '' S) = ⊤
    rw [← Submodule.map_span, show Submodule.span ℂ S = ⊤ from h.2,
      Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective]

private theorem fixed_attainment [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) :
    ∃ (e : K a head ≃ Fin (N a))
      (V : Space (Fin (N a)) →ₗᵢ[ℂ] (Space σ ⊗[ℂ] Space (Fin (N a))))
      (U : Unitary (σ × Fin (N a))),
      Matrix.gram ℂ (fun r : Box a => phiFin a head e (occ a r)) = G a head ∧
      (0 < a.count head → phiFin a head e 0 = phiFin a head e (Multiset.replicate 1 head) ∧
        Submodule.span ℂ {v : Space (Fin (N a)) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phiFin a head e r} = ⊤) ∧
      (∀ x : Space (Fin (N a)), V x = tensorCoordinates (N a) (U (blankEmbed (N a) head x))) ∧
      (∀ r : Multiset σ, r ≤ a → r ≠ 0 → V (phiFin a head e r) =
        ∑ i : σ, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
          ((basis i : Space σ) ⊗ₜ[ℂ] phiFin a head e (r.erase i))) ∧
      V (phiFin a head e 0) = (basis head : Space σ) ⊗ₜ[ℂ] phiFin a head e 0 ∧
      ‖phiFin a head e a‖ = 1 ∧ ‖phiFin a head e 0‖ = 1 ∧
      (∀ (w : Fin a.card → σ) (k : Fin (N a)),
        circuit (fun _ => U) a.card 0 (initialized head a.card (phiFin a head e a)) (w, k) =
          (if occupation w = a then (Real.sqrt (M a : ℝ) : ℂ)⁻¹ else 0) * phiFin a head e 0 k) := by
  let e : K a head ≃ Fin (N a) := occupationMemoryEquiv a head hmax
  let E := memoryCoordinates a head e
  let T := emissionCoordinates a head e
  let V := (tensorCoordinates (σ := σ) (N a)).toLinearIsometry.comp T
  obtain ⟨U, hU⟩ := exists_unitary_agree (blankEmbed (N a) head) T
  have hcoord (x : Space (K a head)) (i : σ) (k : K a head) :
      T (E x) (i, e k) = emitLinear a head x (i, k) :=
    emission_coordinates_apply a head e x i k
  refine ⟨e, V, U, phiFin_gram a head e, phiFin_nonterminal a head e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change tensorCoordinates (N a) (T x) = tensorCoordinates (N a) (U (blankEmbed (N a) head x))
    rw [hU]
  · intro r hr hr0
    let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (Fin (N a)) ℂ)
    apply b.repr.injective
    change b.repr (b.repr.symm (T (phiFin a head e r))) = _
    rw [b.repr.apply_symm_apply, phiFin_eq_coordinates]
    ext ⟨i, k⟩
    obtain ⟨k, rfl⟩ := e.surjective k
    rw [hcoord, normalized_emit_step a head hmax r hr hr0 i k]
    simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      b, OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
      basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [phiFin_eq_coordinates, memory_coordinates_apply]
  · let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (Fin (N a)) ℂ)
    apply b.repr.injective
    change b.repr (b.repr.symm (T (phiFin a head e 0))) = _
    rw [b.repr.apply_symm_apply, phiFin_eq_coordinates]
    ext ⟨i, k⟩
    obtain ⟨k, rfl⟩ := e.surjective k
    rw [hcoord, phi_zero, emit_linear_sink]
    simp only [b, OrthonormalBasis.tensorProduct_repr_tmul_apply,
      EuclideanSpace.basisFun_repr, memory_coordinates_apply, basis_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  · rw [phiFin_eq_coordinates, LinearIsometryEquiv.norm_map]
    exact phi_norm a head a le_rfl
  · rw [phiFin_eq_coordinates, LinearIsometryEquiv.norm_map]
    exact phi_norm a head 0 (Multiset.zero_le _)
  · let R : Multiset σ → Space (Fin (N a)) := fun r => E (padding a head r)
    have hz : R 0 = phiFin a head e 0 := by
      rw [phiFin_eq_coordinates, phi_zero]
      change E (padding a head 0) = E (basis none)
      rw [padding_eq_residual, padding_residual_zero]
    have hstep (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : Fin (N a)) :
        U (blankMemory head (R r)) (i, k) = if i ∈ r then R (r.erase i) k else 0 := by
      change U (blankEmbed (N a) head (R r)) (i, k) = _
      rw [hU]
      obtain ⟨k, rfl⟩ := e.surjective k
      rw [hcoord]
      change (W a head).mulVec (fun s => padding a head r s) (i, k) = _
      rw [padding_residual_intertwining a head hmax r hr hr0 i k]
      by_cases hi : i ∈ r
      · rw [if_pos hi, if_pos hi]
        exact (memory_coordinates_apply a head e (padding a head (r.erase i)) k).symm
      · simp only [if_neg hi]
    have ho := normalized_output_of_residuals head U a R (phiFin a head e 0) hz hstep
    have hx : (Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ • R a = phiFin a head e a := by
      rw [phiFin_eq_coordinates, phi, map_smul]
      rfl
    rw [hx] at ho
    intro w k
    rw [ho]
    simp only [sectorVector, sectorWords, Finset.mem_filter, Finset.mem_univ, true_and, M]

private theorem zero_block_mass (a : Multiset σ) (head : σ) : m a head 0 0 = 1 := by
  simpa [delta] using delta_zero a head 0

private theorem B_zero_zero (a : Multiset σ) (head : σ) : B a head 0 0 = 1 := by
  change (if (0 : Tail a head) = 0 then (m a head 0 0 : ℂ) else 0) = 1
  rw [if_pos rfl, zero_block_mass, Complex.ofReal_one]

private theorem B_rank (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) : (B a head).rank = N a := by
  rw [← padding_gram_eq_B, padding_gram_rank, hmax]
  rfl

private theorem B_rank_blocks (a : Multiset σ) (head : σ) :
    (B a head).rank = 1 + (Fintype.card (Tail a head) - 1) * (a.count head + 1) := by
  rw [← padding_gram_eq_B, padding_gram_rank, ← occupation_memory_card a head]
  change Fintype.card (K a head) = _
  have ht : Fintype.card (PositiveTail a head) = Fintype.card (Tail a head) - 1 := by
    simpa only [Fintype.card_unique] using
      Fintype.card_subtype_compl (fun b : Tail a head => b = 0)
  simp only [K, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, ht]
  omega

/-- Exact stationary attainment for every finite nonempty alphabet and all capacities.
The prescribed images preserve Gram entries and every finite dependence before the
fixed tensor isometry and its same-memory unitary extension are constructed. -/
theorem stationary_attainment_full [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) :
    (∀ r : Multiset σ, M r = r.card.factorial / ∏ i : σ, (r.count i).factorial) ∧
    z head 0 = 1 ∧
    (∀ h : ℕ, 1 ≤ h → h ≤ a.count head → z head (Multiset.replicate h head) = 1) ∧
    (∀ r : Multiset σ, r ≤ a → tailOcc head r ≠ 0 → z head r = 0) ∧
    Function.Bijective (fun r : Box a => (tailIndex a head r, r head)) ∧
    (∀ b : Tail a head,
      block a head b = L (a.count head) *
        Matrix.diagonal (fun j : Fin (a.count head + 1) => (delta a head b j.val : ℂ)) *
          (L (a.count head)).transpose ∧
      (block a head b).rank = (if b = 0 then 1 else a.count head + 1) ∧
      (b = 0 → m a head b 0 = 1 ∧ ∀ j : ℕ, delta a head b j = if j = 0 then 1 else 0) ∧
      (b ≠ 0 → (∀ j : Fin (a.count head + 1), 0 < delta a head b j.val) ∧
        (∀ j : Fin (a.count head + 1),
          lastTail head (slice a head b j.val) = delta a head b j.val)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ a.count head →
        m a head b j / m a head b (j - 1) =
          ((j : ℝ) + ((tailWord a head b).card : ℝ)) / (j : ℝ) ∧
        (b ≠ 0 → 1 < m a head b j / m a head b (j - 1)))) ∧
    Fintype.card (K a head) = N a ∧
    (∀ r : Multiset σ, r ≤ a → ‖phi a head r‖ = 1) ∧
    Matrix.gram ℂ (fun r : Box a => phi a head (occ a r)) = G a head ∧
    (∀ r : Multiset σ, r ≤ a → inner ℂ (phi a head r) (phi a head 0) = z head r) ∧
    (G a head).PosSemidef ∧ (B a head).PosSemidef ∧
    D a * G a head * D a = B a head ∧
    (B a head) 0 0 = 1 ∧
    (G a head).rank = N a ∧ (B a head).rank = N a ∧
    (B a head).rank = 1 + (Fintype.card (Tail a head) - 1) * (a.count head + 1) ∧
    (∀ r s : Box a, occ a r ≠ 0 → occ a s ≠ 0 →
      (B a head) r s = ∑ i : σ, if 0 < (r i).val ∧ 0 < (s i).val then
        (B a head)
          (fun j => ⟨(r j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩)
          (fun j => ⟨(s j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (s j).isLt⟩)
      else 0) ∧
    (∀ r s : Multiset σ, r ≤ a → s ≤ a →
      inner ℂ (image a head r) (image a head s) = inner ℂ (phi a head r) (phi a head s)) ∧
    (∀ (J : Type v) [Fintype J] (r : J → Multiset σ) (c : J → ℂ), (∀ j, r j ≤ a) →
      (∑ j : J, c j • phi a head (r j)) = 0 → (∑ j : J, c j • image a head (r j)) = 0) ∧
    (0 < a.count head → phi a head 0 = phi a head (Multiset.replicate 1 head) ∧
      Submodule.span ℂ {v : Space (K a head) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phi a head r} = ⊤) ∧
    (a = 0 → N a = 1 ∧ Nonempty (Space (K a head) ≃ₗᵢ[ℂ] ℂ)) ∧
    ∃ (e : K a head ≃ Fin (N a))
      (V : Space (Fin (N a)) →ₗᵢ[ℂ] (Space σ ⊗[ℂ] Space (Fin (N a))))
      (U : Unitary (σ × Fin (N a))),
      Matrix.gram ℂ (fun r : Box a => phiFin a head e (occ a r)) = G a head ∧
      (0 < a.count head → phiFin a head e 0 = phiFin a head e (Multiset.replicate 1 head) ∧
        Submodule.span ℂ {v : Space (Fin (N a)) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = phiFin a head e r} = ⊤) ∧
      (∀ x : Space (Fin (N a)),
        V x = tensorCoordinates (N a) (U (blankEmbed (N a) head x))) ∧
      (∀ r : Multiset σ, r ≤ a → r ≠ 0 → V (phiFin a head e r) =
        ∑ i : σ, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
          ((basis i : Space σ) ⊗ₜ[ℂ] phiFin a head e (r.erase i))) ∧
      V (phiFin a head e 0) = (basis head : Space σ) ⊗ₜ[ℂ] phiFin a head e 0 ∧
      ‖phiFin a head e a‖ = 1 ∧ ‖phiFin a head e 0‖ = 1 ∧
      (∀ (w : Fin a.card → σ) (k : Fin (N a)),
        circuit (fun _ => U) a.card 0 (initialized head a.card (phiFin a head e a)) (w, k) =
          (if occupation w = a then (Real.sqrt (M a : ℝ) : ℂ)⁻¹ else 0) * phiFin a head e 0 k) := by
  refine ⟨(fun r => multiplicity_eq_factorial r rfl), ?_, ?_, ?_, ?_, ?_,
    memory_card a head hmax, phi_norm a head, phi_gram a head, phi_moment a head,
    ?_, ?_, gram_congruence a head, B_zero_zero a head, ?_, B_rank a head hmax,
    B_rank_blocks a head, B_recurrence a head, prescribed_image_gram a head hmax,
    prescribed_dependencies a head hmax, phi_nonterminal a head, ?_,
    fixed_attainment a head hmax⟩
  · simp [z, tailOcc]
  · intro h _ _
    simp [z, tailOcc, Multiset.mem_replicate]
  · intro r _ hr
    exact if_neg hr
  · exact ((occupationSplit head a).trans (Equiv.prodComm _ _)).bijective
  · intro b
    refine ⟨block_factorization a head b, block_rank a head b, ?_, ?_, ?_⟩
    · rintro rfl
      exact ⟨zero_block_mass a head, delta_zero a head⟩
    · intro hb
      exact ⟨fun j => delta_pos a head b hb j.val,
        fun j => last_tail_delta a head b hb j.val⟩
    · intro j hj _
      exact ⟨block_ratio a head b j hj, fun hb => block_ratio_strict a head b hb j hj⟩
  · rw [← phi_gram]
    exact Matrix.posSemidef_gram _ _
  · rw [← padding_gram_eq_B]
    exact Matrix.posSemidef_gram _ _
  · rw [← normalized_gram_eq_G]
    exact maximal_padding_gram_rank head a hmax
  · rintro rfl
    exact zero_memory head

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationAttainment
