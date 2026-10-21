/- GID: D5/S3/Arith/InterlaceFan/Fourier
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Fourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic, mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Roots, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cosine evaluation isomorphism and the closed faces of the interlace fan. -/

import D5.S3.Arith.InterlaceFan.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

noncomputable section
open Finset Polynomial
open D5.S3.Arith.InterlaceFan.Defs

namespace D5.S3.Arith.InterlaceFan.Fourier

private def cosine (n j k : ℕ) : ℝ := Real.cos (2 * Real.pi * j * k / n)

private def evaluation (n : ℕ) :
    (Fin (n / 2 + 1) → ℝ) →ₗ[ℝ] (Fin (n / 2 + 1) → ℝ) where
  toFun a j := ∑ k : Fin (n / 2 + 1), cosine n j k * a k
  map_add' a b := by ext j; simp [mul_add, sum_add_distrib]
  map_smul' c a := by ext j; simp [mul_left_comm, ← mul_sum]

private lemma cosine_nodes_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (fun j : Fin (n / 2 + 1) => cosine n j 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hb (j : Fin (n / 2 + 1)) :
      0 ≤ 2 * Real.pi * (j : ℕ) / n ∧ 2 * Real.pi * (j : ℕ) / n ≤ Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).mpr
      have hj : (2 : ℝ) * (j : ℕ) ≤ n := by exact_mod_cast (by omega : 2 * (j : ℕ) ≤ n)
      nlinarith [Real.pi_pos]
  intro i j hij
  have he : 2 * Real.pi * (i : ℕ) / n = 2 * Real.pi * (j : ℕ) / n :=
    Real.strictAntiOn_cos.injOn (hb i) (hb j) (by simpa [cosine] using hij)
  have hv : (i : ℕ) = (j : ℕ) := by
    have hr : ((i : ℕ) : ℝ) = (j : ℕ) := by
      apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
      exact (div_left_inj' hnR.ne').mp he
    exact_mod_cast hr
  exact Fin.ext hv

private lemma evaluation_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (evaluation n) := by
  intro a b hab
  let p : ℝ[X] := ∑ k : Fin (n / 2 + 1),
    (a k - b k) • Polynomial.Chebyshev.T ℝ (k : ℕ)
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
      (cosine_nodes_injective n hn)
    · intro j
      have hj := sub_eq_zero.mpr (congrFun hab j)
      simpa [p, evaluation, cosine, Polynomial.eval_finsetSum,
        Polynomial.eval_smul, Polynomial.Chebyshev.T_real_cos, mul_comm,
        mul_left_comm, mul_assoc, mul_div_assoc, mul_sub, sub_mul, sum_sub_distrib] using hj
    · have hd : p.natDegree ≤ n / 2 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro k hk
        exact (Polynomial.natDegree_smul_le _ _).trans (by
          simp only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
          omega)
      simpa using (Nat.lt_succ_of_le hd)
  have hli := (Polynomial.Chebyshev.chebyshevTSequence ℝ).linearIndependent.comp
    (fun k : Fin (n / 2 + 1) => (k : ℕ)) Fin.val_injective
  have he := (Fintype.linearIndependent_iff.mp hli) (fun k => a k - b k) hp
  funext k
  exact sub_eq_zero.mp (he k)

/-- If all certificate values agree, the sigma-coordinate vector is zero. -/
theorem eq_zero_of_I_const (n : ℕ) (hn : 2 ≤ n) (x : Fin (n / 2) → ℝ)
    (c : ℝ) (h : ∀ j ∈ certIdx n, I n j x = c) : x = 0 := by
  let a : Fin (n / 2 + 1) → ℝ := Fin.cons (-c) (fun k => -x k)
  have ha : evaluation n a = evaluation n 0 := by
    ext j
    have hj := h j (by simp [certIdx]; omega)
    simpa [evaluation, a, Fin.sum_univ_succ, cosine, I, Fin.cons_zero,
      Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one,
      mul_neg, sum_neg_distrib, sub_eq_add_neg, add_comm] using sub_eq_zero.mpr hj
  have hz := evaluation_injective n hn ha
  funext k
  have hk := congrFun hz k.succ
  simpa [a] using hk

/-- Enlarging a required certificate set gives a smaller closed face. -/
theorem face_antitone (n : ℕ) {S T : Finset ℕ} (hST : S ⊆ T) :
    face n T ⊆ face n S := by
  intro x hx s hs j hj
  exact hx s (hST hs) j hj

/-- Multiplicity of a certificate in the full period. -/
def certWeight (n j : ℕ) : ℝ := if j = 0 ∨ n = 2 * j then 1 else 2

private lemma fold_sum (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℝ)
    (hf : ∀ j, 0 < j → j < n → f (n - j) = f j) :
    ∑ j ∈ range n, f j = ∑ j ∈ range (n / 2 + 1), certWeight n j * f j := by
  let m := n / 2
  let l := n - (m + 1)
  have hlm : l ≤ m := by dsimp [l, m]; omega
  have he : n = (m + 1) + l := by dsimp [l, m]; omega
  have hr : (∑ i ∈ range l, f (m + 1 + i)) = ∑ i ∈ range l, f (i + 1) := by
    rw [← sum_range_reflect (fun i => f (m + 1 + i)) l]
    apply sum_congr rfl
    intro i hi
    have hi' : i < l := mem_range.mp hi
    rw [show m + 1 + (l - 1 - i) = n - (i + 1) by omega]
    exact hf (i + 1) (by omega) (by omega)
  have ht : (∑ i ∈ range m, if i < l then f (i + 1) else 0) =
      ∑ i ∈ range l, f (i + 1) := by
    calc
      _ = ∑ i ∈ range l, if i < l then f (i + 1) else 0 := by
        symm
        apply sum_subset (range_mono hlm)
        intro i hi hni
        simp only [mem_range] at hni
        simp only [hni, ite_false]
      _ = _ := sum_congr rfl (fun i hi => ite_eq_left (mem_range.mp hi))
  have hw : ∀ i ∈ range m, certWeight n (i + 1) * f (i + 1) =
      f (i + 1) + if i < l then f (i + 1) else 0 := by
    intro i hi
    have him : i < m := mem_range.mp hi
    by_cases hil : i < l
    · have hne : ¬ (i + 1 = 0 ∨ n = 2 * (i + 1)) := by dsimp [l, m] at *; omega
      rw [certWeight, ite_eq_right hne, ite_eq_left hil]
      ring
    · have heq : n = 2 * (i + 1) := by dsimp [l, m] at *; omega
      simp [certWeight, heq, hil]
  have hw' := sum_congr rfl hw
  calc
    _ = (∑ i ∈ range (m + 1), f i) + ∑ i ∈ range l, f (i + 1) := by
      conv_lhs => rw [he, sum_range_add, hr]
    _ = _ := by
      change _ = ∑ j ∈ range (m + 1), certWeight n j * f j
      rw [sum_range_succ', sum_range_succ', hw', sum_add_distrib, ht]
      simp only [certWeight, true_or, ite_true, one_mul]
      ring

private lemma cosine_reflect (n j k : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    cosine n (n - j) k = cosine n j k := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold cosine
  rw [Nat.cast_sub hj]
  rw [show 2 * Real.pi * ((n : ℝ) - j) * k / n =
      (k : ℝ) * (2 * Real.pi) - 2 * Real.pi * j * k / n by field_simp]
  exact Real.cos_nat_mul_two_pi_sub _ _

private lemma sum_cosine (n k : ℕ) (hn : 2 ≤ n) (hk : 0 < k) (hkn : k < n) :
    ∑ j ∈ range n, cosine n j k = 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : Real.sin (Real.pi * k / n) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
      apply (div_lt_iff₀ hnR).mpr
      nlinarith [Real.pi_pos]))
  have h := Real.sin_mul_sum_cos n (2 * Real.pi * k / n) 0
  rw [show (n : ℝ) * (2 * Real.pi * k / n) / 2 = (k : ℝ) * Real.pi by field_simp,
    Real.sin_nat_mul_pi, zero_mul,
    show 2 * Real.pi * (k : ℝ) / n / 2 = Real.pi * k / n by ring] at h
  have hz := (mul_eq_zero.mp h).resolve_left hs
  convert hz using 1
  apply sum_congr rfl
  intro j hj
  unfold cosine
  congr 1
  ring

private lemma cosine_weighted_sum (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n / 2) :
    ∑ j ∈ certIdx n, certWeight n j * cosine n j k = if k = 0 then (n : ℝ) else 0 := by
  change (∑ j ∈ range (n / 2 + 1), certWeight n j * cosine n j k) = _
  rw [← fold_sum n hn (fun j => cosine n j k)
    (fun j hj hjn => cosine_reflect n j k (by omega) (by omega))]
  by_cases hz : k = 0
  · simp [hz, cosine]
  · rw [ite_eq_right hz]
    exact sum_cosine n k hn (by omega) (by omega)

private lemma evaluation_mean (n : ℕ) (hn : 2 ≤ n) (a : Fin (n / 2 + 1) → ℝ) :
    (∑ j : Fin (n / 2 + 1), certWeight n j * evaluation n a j) = n * a 0 := by
  calc
    _ = ∑ k : Fin (n / 2 + 1),
        (∑ j : Fin (n / 2 + 1), certWeight n j * cosine n j k) * a k := by
      simp only [evaluation, LinearMap.coe_mk, AddHom.coe_mk, mul_sum, sum_mul, mul_assoc]
      rw [sum_comm]
    _ = ∑ k : Fin (n / 2 + 1), (if (k : ℕ) = 0 then (n : ℝ) else 0) * a k := by
      apply sum_congr rfl
      intro k hk
      congr 1
      simpa [certIdx, sum_range] using cosine_weighted_sum n k hn (by omega)
    _ = _ := by
      simp only [ite_mul, zero_mul]
      simp

/-- The weighted certificate values have zero mean. The endpoints have weight
one, and all other indices have weight two. -/
theorem I_weighted_sum (n : ℕ) (hn : 2 ≤ n) (x : Fin (n / 2) → ℝ) :
    ∑ j ∈ certIdx n, certWeight n j * I n j x = 0 := by
  have hm := evaluation_mean n hn (Fin.cons 0 (fun k => -x k))
  have he (j : Fin (n / 2 + 1)) :
      evaluation n (Fin.cons 0 (fun k => -x k)) j = I n j x := by
    simp [evaluation, Fin.sum_univ_succ, cosine, I, Fin.val_succ,
      mul_neg, neg_mul, sum_neg_distrib]
  simp_rw [he] at hm
  simpa [certIdx, sum_range] using hm

/-- Every family of certificate values with weighted mean zero is realized by
sigma coordinates. -/
theorem exists_of_I_values (n : ℕ) (hn : 2 ≤ n) (y : ℕ → ℝ)
    (hy : ∑ j ∈ certIdx n, certWeight n j * y j = 0) :
    ∃ x : Fin (n / 2) → ℝ, ∀ j ∈ certIdx n, I n j x = y j := by
  obtain ⟨a, ha⟩ := LinearMap.surjective_of_injective (evaluation_injective n hn)
    (fun j => y j)
  have hm := evaluation_mean n hn a
  have hz : a 0 = 0 := by
    have h0 : (∑ j : Fin (n / 2 + 1), certWeight n j * evaluation n a j) = 0 := by
      rw [ha]
      simpa [certIdx, sum_range] using hy
    rw [h0] at hm
    exact (mul_eq_zero.mp hm.symm).resolve_left (by exact_mod_cast (by omega : n ≠ 0))
  refine ⟨fun k => -a k.succ, fun j hj => ?_⟩
  let i : Fin (n / 2 + 1) := ⟨j, by simpa [certIdx] using hj⟩
  have hi := congrFun ha i
  simpa [evaluation, Fin.sum_univ_succ, cosine, I, Fin.val_succ, hz,
    neg_mul_neg, i] using hi

/-- Every proper nonempty certificate set is exactly the maximizing set of a
nonzero point of its closed face. -/
theorem exists_face_exact (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ certIdx n) (hSne : S.Nonempty) (hSproper : S ≠ certIdx n) :
    ∃ x ∈ face n S, x ≠ 0 ∧
      (∀ j ∈ certIdx n, I n j x = interlaceNumber n x ↔ j ∈ S) ∧
      (∀ j ∈ certIdx n \ S, I n j x < interlaceNumber n x) := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hw : (∑ j ∈ certIdx n, certWeight n j) = (n : ℝ) := by
    simpa [cosine] using cosine_weighted_sum n 0 hn (by omega)
  let z : ℕ → ℝ := fun j => if j ∈ S then 1 else 0
  let c : ℝ := (∑ j ∈ certIdx n, certWeight n j * z j) / n
  have hy : (∑ j ∈ certIdx n, certWeight n j * (z j - c)) = 0 := by
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
    rw [hw]
    dsimp [c]
    field_simp
    ring
  obtain ⟨x, hx⟩ := exists_of_I_values n hn (fun j => z j - c) hy
  obtain ⟨s, hs⟩ := hSne
  have hsJ := hS hs
  have hM : interlaceNumber n x = 1 - c := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro j hj
      rw [hx j hj]
      dsimp [z]
      split_ifs <;> linarith
    · have hle := Finset.le_sup' (fun j => I n j x) hsJ
      change I n s x ≤ interlaceNumber n x at hle
      rw [hx s hsJ] at hle
      simpa [z, hs] using hle
  have ht : ∃ t ∈ certIdx n, t ∉ S := by
    by_contra h
    push Not at h
    exact hSproper (Subset.antisymm hS h)
  obtain ⟨t, htJ, htS⟩ := ht
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    rw [hx i (hS hi), hx j hj]
    dsimp [z]
    simp only [hi, ite_true]
    split_ifs <;> linarith
  · intro h0
    have hsx := hx s hsJ
    have htx := hx t htJ
    simp [h0, I, z, hs, htS] at hsx htx
    linarith
  · intro j hj
    rw [hx j hj, hM]
    dsimp [z]
    by_cases hjS : j ∈ S
    · simp [hjS]
    · simp only [hjS, ite_false, zero_sub, iff_false]
      linarith
  · intro j hj
    obtain ⟨hjJ, hjS⟩ := mem_sdiff.mp hj
    rw [hx j hjJ, hM]
    simp [z, hjS]

end D5.S3.Arith.InterlaceFan.Fourier
