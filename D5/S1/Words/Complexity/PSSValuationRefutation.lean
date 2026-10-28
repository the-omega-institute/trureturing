/- GID: D5/S1/Words/Complexity/PSSValuationRefutation
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/PSSValuationRefutation
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Complexity/PSSValuationRefutation.claim; result=D5/S1/Words/Complexity/PSSValuationRefutation.result; claim=D5/S1/Words/Complexity/PSSValuationRefutation.claim
   digest: One fixed ternary infinite word defeats every natural valuation in the equality of additive and abelian complexities. -/

import D5.S1.Words.Complexity.MorseHedlund
import Mathlib.Logic.Equiv.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-! Natural valuations and the original-symbol Parikh vectors of contiguous factors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PSSValuationRefutation

open D5.S1.Words.Complexity

/-- The original-symbol Parikh vector of a finite word. -/
noncomputable def parikh {A : Type*} (u : List A) : A → ℕ := by
  classical
  exact fun a => u.count a

/-- Scalar evaluation of a Parikh vector at natural letter weights. -/
def weightedSum {A : Type*} [Fintype A] (v : A → ℕ) (p : A → ℕ) : ℕ :=
  ∑ a, v a * p a

/-- The finite set of Parikh vectors of actual contiguous length-n factors. -/
noncomputable def parikhSet {A : Type*} [Fintype A] (w : ℕ → A) (n : ℕ) :
    Finset (A → ℕ) := by
  classical
  exact (wordFactorSet w n).image (fun u => parikh (List.ofFn u))

/-- Original-symbol abelian complexity. -/
noncomputable def abelianComplexity {A : Type*} [Fintype A] (w : ℕ → A) (n : ℕ) : ℕ :=
  (parikhSet w n).card

/-- The finite set of natural sums of actual contiguous length-n factors. -/
noncomputable def sumSet {A : Type*} [Fintype A] (w : ℕ → A) (v : A → ℕ) (n : ℕ) :
    Finset ℕ := by
  classical
  exact (wordFactorSet w n).image (fun u => ((List.ofFn u).map v).sum)

/-- Additive complexity for the valuation v, without changing the symbolic alphabet. -/
noncomputable def additiveComplexity {A : Type*} [Fintype A] (w : ℕ → A)
    (v : A → ℕ) (n : ℕ) : ℕ := (sumSet w v n).card

/-- The full general valuation-existence assertion, at every natural length. -/
def claim : Prop :=
  ∀ (A : Type) [Fintype A] (w : ℕ → A),
    ∃ v : A → ℕ, ∀ n : ℕ, additiveComplexity w v n = abelianComplexity w n

private def block (k : ℕ) : List (Fin 3) :=
  (Encodable.decode (α := List (Fin 3)) k).getD [] ++ [0]

private def boundary : ℕ → ℕ
  | 0 => 0
  | k + 1 => boundary k + (block k).length

private theorem boundary_strict : StrictMono boundary := by
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [boundary, block, List.length_append, List.length_singleton]
  omega

private theorem boundary_ge (k : ℕ) : k ≤ boundary k := by
  induction k with
  | zero => simp [boundary]
  | succ k ih =>
    have := boundary_strict (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at *
    omega

private theorem has_boundary (i : ℕ) : ∃ k, i < boundary (k + 1) :=
  ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (boundary_ge (i + 1))⟩

/-- Concatenate all decoded ternary finite words, each followed by a zero.
The least enclosing boundary defines each natural-indexed letter independently of valuations. -/
def universalWord (i : ℕ) : Fin 3 :=
  let k := Nat.find (has_boundary i)
  (block k).getD (i - boundary k) 0

private theorem universalWord_at (k j : ℕ) (hj : j < (block k).length) :
    universalWord (boundary k + j) = (block k).getD j 0 := by
  have hfind : Nat.find (has_boundary (boundary k + j)) = k := by
    apply (Nat.find_eq_iff _).mpr
    constructor
    · simp only [boundary]; omega
    · intro m hm
      have hle := boundary_strict.monotone (show m + 1 ≤ k by omega)
      omega
  simp [universalWord, hfind]

private theorem universal_occurrence (u : List (Fin 3)) :
    ∃ i, List.ofFn (wordFactor universalWord u.length i) = u := by
  let k := Encodable.encode u
  have hb : block k = u ++ [0] := by simp [block, k, Encodable.encodek]
  refine ⟨boundary k, ?_⟩
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_ofFn, wordFactor]
    rw [universalWord_at k j (by simp [hb]; omega), hb]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h₂]

private theorem sum_eq_weighted {A : Type*} [Fintype A] (v : A → ℕ) (u : List A) :
    (u.map v).sum = weightedSum v (parikh u) := by
  classical
  induction u with
  | nil => simp [weightedSum, parikh]
  | cons a u ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [weightedSum, parikh, List.count_cons, mul_add, Finset.sum_add_distrib]
    simp [Nat.add_comm]

private theorem sums_image {A : Type*} [Fintype A] (w : ℕ → A) (v : A → ℕ) (n : ℕ) :
    sumSet w v n = (parikhSet w n).image (weightedSum v) := by
  classical
  simp only [sumSet, parikhSet, Finset.image_image, Function.comp_def,
    sum_eq_weighted]

private theorem parikh_occurs (u : List (Fin 3)) :
    parikh u ∈ parikhSet universalWord u.length := by
  classical
  obtain ⟨i, hi⟩ := universal_occurrence u
  apply Finset.mem_image.mpr
  refine ⟨wordFactor universalWord u.length i, mem_wordFactorSet.mpr ⟨i, rfl⟩, ?_⟩
  rw [hi]

private def runs (a b c : ℕ) : List (Fin 3) :=
  List.replicate a 0 ++ List.replicate b 1 ++ List.replicate c 2

private theorem runs_parikh (a b c : ℕ) : parikh (runs a b c) = ![a,b,c] := by
  classical
  funext i
  fin_cases i <;>
    simp only [parikh, runs, List.count_append, List.count_replicate, beq_iff_eq]
    <;> norm_num

private theorem runs_length (a b c : ℕ) : (runs a b c).length = a + b + c := by
  simp [runs, Nat.add_assoc]

private theorem collision (v : Fin 3 → ℕ) :
    ∃ n, 0 < n ∧ ∃ p ∈ parikhSet universalWord n,
      ∃ q ∈ parikhSet universalWord n, p ≠ q ∧ weightedSum v p = weightedSum v q := by
  classical
  by_cases h : v 0 = v 1 ∧ v 1 = v 2
  · refine ⟨1, by omega, parikh [0], ?_, parikh [1], ?_, ?_, ?_⟩
    · exact parikh_occurs [0]
    · exact parikh_occurs [1]
    · intro hp
      have := congrFun hp 0
      simp [parikh] at this
    · simp [weightedSum, parikh, Fin.sum_univ_three, h.1]
  · let a := v 0
    let b := v 1
    let c := v 2
    have hpos : 0 < a + b + c := by
      by_contra hz
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      have hc : c = 0 := by omega
      exact h ⟨by change a = b; omega, by change b = c; omega⟩
    refine ⟨a + b + c, hpos, parikh (runs b c a), ?_,
      parikh (runs c a b), ?_, ?_, ?_⟩
    · rw [← show (runs b c a).length = a + b + c from by rw [runs_length]; omega]
      exact parikh_occurs (runs b c a)
    · rw [← show (runs c a b).length = a + b + c from by rw [runs_length]; omega]
      exact parikh_occurs (runs c a b)
    · rw [runs_parikh, runs_parikh]
      intro hp
      have h₀ := congrFun hp 0
      have h₁ := congrFun hp 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h₀ h₁
      apply h
      constructor <;> dsimp [a,b,c] at * <;> omega
    · rw [runs_parikh, runs_parikh]
      simp [weightedSum, Fin.sum_univ_three, a, b, c]
      ring

private theorem universal_failure (v : Fin 3 → ℕ) :
    ∃ n, 0 < n ∧ additiveComplexity universalWord v n < abelianComplexity universalWord n := by
  classical
  obtain ⟨n, hn, p, hp, q, hq, hne, heq⟩ := collision v
  refine ⟨n, hn, ?_⟩
  rw [additiveComplexity, abelianComplexity, sums_image]
  apply lt_of_le_of_ne (Finset.card_image_le) ?_
  intro he
  have hinj := Finset.card_image_iff.mp he
  exact hne (hinj hp hq heq)

/-- Popoli--Shallit--Stipulanti Question 31 has a negative answer in its full generality. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨v, hv⟩ := h (Fin 3) universalWord
  obtain ⟨n, _, hn⟩ := universal_failure v
  exact (Nat.ne_of_lt hn) (hv n)

end D5.S1.Words.Complexity.PSSValuationRefutation
