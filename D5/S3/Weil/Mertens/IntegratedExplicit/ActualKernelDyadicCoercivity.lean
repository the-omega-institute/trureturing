/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelDyadicCoercivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelDyadicCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic conditioning of finite local Gram matrices of the complete arithmetic kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import D5.S3.Analytic.Interpolation.AveragedBoxEnergy
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Norm
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ComplexOrder

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelDyadicCoercivity

namespace WideTentCoercivity
open Finset Matrix

/-- The prefix before the index `k`. -/
private def partialSum (c : ℕ → ℂ) (k : ℕ) : ℂ := ∑ i ∈ range k, c i

private lemma normSq_sub_le (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  have h := Complex.normSq_nonneg (z + w)
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at h ⊢
  nlinarith

private lemma path_difference_energy_bound (z : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, Complex.normSq (z (i + 1) - z i)) ≤
      2 * Complex.normSq (z 0) + 2 * Complex.normSq (z N) +
        4 * ∑ k ∈ Ico 1 N, Complex.normSq (z k) := by
  by_cases hN : N = 0
  · subst N
    have he : (Ico 1 0 : Finset ℕ) = ∅ := by decide
    simp only [range_zero, sum_empty, he, mul_zero, add_zero]
    nlinarith [Complex.normSq_nonneg (z 0)]
  have hN0 : 0 < N := Nat.pos_of_ne_zero hN
  have hbound := sum_le_sum (s := range N) (fun i _ => normSq_sub_le (z (i + 1)) (z i))
  have hleft : (∑ i ∈ range N, Complex.normSq (z i)) =
      Complex.normSq (z 0) + ∑ k ∈ Ico 1 N, Complex.normSq (z k) :=
    sum_range_eq_add_Ico (fun k => Complex.normSq (z k)) hN0
  have hright : (∑ i ∈ range N, Complex.normSq (z (i + 1))) =
      (∑ k ∈ Ico 1 N, Complex.normSq (z k)) + Complex.normSq (z N) := by
    calc
      (∑ i ∈ range N, Complex.normSq (z (i + 1))) =
          ∑ i ∈ Ico 1 (N + 1), Complex.normSq (z i) := by
        simpa only [range_eq_Ico, zero_add] using
          (sum_Ico_add' (fun i => Complex.normSq (z i)) 0 N 1)
      _ = _ := sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hN)
        (fun i => Complex.normSq (z i))
  simp only [sum_add_distrib, ← mul_sum] at hbound
  rw [hleft, hright] at hbound
  linarith

/-- A finite coefficient family is controlled by its total mass and centered
interior prefixes. This is a consumed finite-difference estimate. -/
private theorem centered_prefix_energy_bound (c : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, Complex.normSq (c i)) ≤
      Complex.normSq (partialSum c N) +
        4 * ∑ k ∈ Ico 1 N, Complex.normSq (partialSum c k - partialSum c N / 2) := by
  let S := partialSum c N
  let z : ℕ → ℂ := fun k => partialSum c k - S / 2
  have hincr (i : ℕ) : z (i + 1) - z i = c i := by
    dsimp [z, partialSum]
    rw [sum_range_succ]
    ring
  have hzero : z 0 = -S / 2 := by simp [z, partialSum, S]; ring
  have hlast : z N = S / 2 := by dsimp [z, S]; ring
  have hend : 2 * Complex.normSq (z 0) + 2 * Complex.normSq (z N) =
      Complex.normSq S := by
    rw [hzero, hlast]
    norm_num [Complex.normSq_div, Complex.normSq_neg] <;> ring
  have h := path_difference_energy_bound z N
  simp_rw [hincr] at h
  rw [hend] at h
  exact h

/-- Positive gaps and a wide endpoint coefficient turn centered-prefix control
into a `g/2` lower bound for the centered gap expression. -/
private theorem centered_gap_coercivity (c : ℕ → ℂ) (N : ℕ) (d : ℕ → ℝ)
    {g D L : ℝ} (hg : 0 < g) (hgD : g ≤ D) (hDL : D ≤ L)
    (hd : ∀ k ∈ range (N + 1), g ≤ d k) :
    (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
      (L - D / 2) * Complex.normSq (partialSum c (N + 2)) +
        2 * ∑ k ∈ range (N + 1), d k *
          Complex.normSq (partialSum c (k + 1) - partialSum c (N + 2) / 2) := by
  let S := partialSum c (N + 2)
  let Y : ℕ → ℝ := fun k => Complex.normSq (partialSum c (k + 1) - S / 2)
  have hshift : (∑ k ∈ Ico 1 (N + 2),
      Complex.normSq (partialSum c k - S / 2)) = ∑ k ∈ range (N + 1), Y k := by
    simpa only [range_eq_Ico, zero_add, Nat.add_assoc] using
      (sum_Ico_add' (fun k => Complex.normSq (partialSum c k - S / 2)) 0 (N + 1) 1).symm
  have hc := centered_prefix_energy_bound c (N + 2)
  change (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
    Complex.normSq S + 4 * ∑ k ∈ Ico 1 (N + 2),
      Complex.normSq (partialSum c k - S / 2) at hc
  rw [hshift] at hc
  have hweighted : g * (∑ k ∈ range (N + 1), Y k) ≤
      ∑ k ∈ range (N + 1), d k * Y k := by
    rw [mul_sum]
    exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hd k hk)
      (Complex.normSq_nonneg _))
  have hbase : (g / 2) * Complex.normSq S ≤ (L - D / 2) * Complex.normSq S :=
    mul_le_mul_of_nonneg_right (by linarith) (Complex.normSq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ g / 2 by positivity)
  change (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
    (L - D / 2) * Complex.normSq S + 2 * ∑ k ∈ range (N + 1), d k * Y k
  nlinarith


private def cutSign (k i : ℕ) : ℝ := if i ≤ k then 1 / 2 else -(1 / 2)

private lemma cutSign_product_of_le {i j : ℕ} (hij : i ≤ j) (k : ℕ) :
    cutSign k i * cutSign k j =
      1 / 4 - (if i ≤ k ∧ k < j then 1 / 2 else 0) := by
  by_cases hi : i ≤ k <;> by_cases hj : j ≤ k
  · simp [cutSign, hi, hj, show ¬ k < j by omega]
    <;> norm_num
  · simp [cutSign, hi, hj, show k < j by omega]
    <;> norm_num
  · omega
  · simp [cutSign, hi, hj]
    <;> norm_num

private lemma sum_crossing_gap (x : ℕ → ℝ) {m i j : ℕ}
    (hij : i ≤ j) (hjm : j ≤ m) :
    (∑ k ∈ range m, if i ≤ k ∧ k < j then (x (k + 1) - x k) else 0) =
      x j - x i := by
  have hf : (range m).filter (fun k => i ≤ k ∧ k < j) = Ico i j := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  calc
    (∑ k ∈ range m, if i ≤ k ∧ k < j then (x (k + 1) - x k) else 0) =
        ∑ k ∈ (range m).filter (fun k => i ≤ k ∧ k < j), (x (k + 1) - x k) := by
      rw [sum_filter]
    _ = ∑ k ∈ Ico i j, (x (k + 1) - x k) := by rw [hf]
    _ = x j - x i := sum_Ico_sub x hij

private lemma kernel_feature_eq_of_le (x : ℕ → ℝ) (L : ℝ) {m i j : ℕ}
    (hij : i ≤ j) (hjm : j ≤ m) (horder : x i ≤ x j) :
    L - |x i - x j| = L - (x m - x 0) / 2 +
      2 * ∑ k ∈ range m, (x (k + 1) - x k) * cutSign k i * cutSign k j := by
  have hterm (k : ℕ) :
      (x (k + 1) - x k) * cutSign k i * cutSign k j =
        (x (k + 1) - x k) / 4 -
          (if i ≤ k ∧ k < j then (x (k + 1) - x k) else 0) / 2 := by
    rw [mul_assoc, cutSign_product_of_le hij]
    split_ifs <;> ring
  simp_rw [hterm]
  rw [sum_sub_distrib, ← sum_div, ← sum_div,
    sum_range_sub, sum_crossing_gap x hij hjm,
    abs_of_nonpos (sub_nonpos.mpr horder)]
  ring

private lemma kernel_feature_eq (x : ℕ → ℝ) (L : ℝ) (m : ℕ)
    (hmono : MonotoneOn x (Set.Iic m)) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    L - |x i - x j| = L - (x m - x 0) / 2 +
      2 * ∑ k ∈ range m, (x (k + 1) - x k) * cutSign k i * cutSign k j := by
  rcases le_total i j with hij | hji
  · exact kernel_feature_eq_of_le x L hij hj (hmono hi hj hij)
  · have h := kernel_feature_eq_of_le x L hji hi (hmono hj hi hji)
    rw [abs_sub_comm] at h
    have hs : (∑ k ∈ range m, (x (k + 1) - x k) * cutSign k j * cutSign k i) =
        ∑ k ∈ range m, (x (k + 1) - x k) * cutSign k i * cutSign k j := by
      apply sum_congr rfl
      intro k _
      ring
    rw [hs] at h
    exact h

private lemma cut_feature_eq_prefix (c : ℕ → ℂ) {N k : ℕ} (hk : k + 1 ≤ N) :
    (∑ i ∈ range N, (cutSign k i : ℂ) * c i) =
      partialSum c (k + 1) - partialSum c N / 2 := by
  have hsign (i : ℕ) : cutSign k i = (if i < k + 1 then (1 : ℝ) else 0) - 1 / 2 := by
    by_cases hi : i ≤ k <;> simp [cutSign, hi, show (i < k + 1) ↔ i ≤ k by omega]
      <;> norm_num
  have hf : (range N).filter (fun i => i < k + 1) = range (k + 1) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  simp_rw [hsign, Complex.ofReal_sub, sub_mul, sum_sub_distrib]
  have hfirst : (∑ i ∈ range N, ((if i < k + 1 then (1 : ℝ) else 0) : ℂ) * c i) =
      partialSum c (k + 1) := by
    simp_rw [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero,
      ite_mul, one_mul, zero_mul]
    rw [← sum_filter, hf]
    rfl
  rw [hfirst, ← mul_sum]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  dsimp [partialSum]
  ring

private def realQuadratic (N : ℕ) (K : ℕ → ℕ → ℝ) (c : ℕ → ℂ) : ℝ :=
  ∑ i ∈ range N, ∑ j ∈ range N,
    (star (c i) * (K i j : ℂ) * c j).re

private lemma realQuadratic_add (N : ℕ) (K H : ℕ → ℕ → ℝ) (c : ℕ → ℂ) :
    realQuadratic N (fun i j => K i j + H i j) c =
      realQuadratic N K c + realQuadratic N H c := by
  simp only [realQuadratic, Complex.ofReal_add, mul_add, add_mul, Complex.add_re,
    sum_add_distrib]

private lemma realQuadratic_scale (N : ℕ) (K : ℕ → ℕ → ℝ) (c : ℕ → ℂ) (a : ℝ) :
    realQuadratic N (fun i j => a * K i j) c = a * realQuadratic N K c := by
  unfold realQuadratic
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  push_cast
  rw [show star (c i) * ((a : ℂ) * (K i j : ℂ)) * c j =
    (a : ℂ) * (star (c i) * (K i j : ℂ) * c j) by ring]
  exact Complex.re_ofReal_mul _ _

private lemma realQuadratic_sum (N : ℕ) (s : Finset ℕ)
    (K : ℕ → ℕ → ℕ → ℝ) (c : ℕ → ℂ) :
    realQuadratic N (fun i j => ∑ k ∈ s, K k i j) c =
      ∑ k ∈ s, realQuadratic N (K k) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realQuadratic]
  | @insert k s hk ih =>
    simp only [sum_insert hk]
    rw [realQuadratic_add, ih]

private lemma realQuadratic_rankOne (N : ℕ) (r : ℕ → ℝ) (c : ℕ → ℂ) :
    realQuadratic N (fun i j => r i * r j) c =
      Complex.normSq (∑ i ∈ range N, (r i : ℂ) * c i) := by
  have h : (∑ i ∈ range N, ∑ j ∈ range N,
      star (c i) * ((r i * r j : ℝ) : ℂ) * c j) =
      (Complex.normSq (∑ i ∈ range N, (r i : ℂ) * c i) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply, Complex.conj_ofReal]
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    push_cast
    ring
  have hh := congrArg Complex.re h
  simpa only [Complex.re_sum, Complex.ofReal_re] using hh

private lemma realQuadratic_const (N : ℕ) (a : ℝ) (c : ℕ → ℂ) :
    realQuadratic N (fun _ _ => a) c = a * Complex.normSq (partialSum c N) := by
  have h := realQuadratic_scale N (fun _ _ => (1 : ℝ)) c a
  simp only [mul_one] at h
  rw [h]
  have hunit := realQuadratic_rankOne N (fun _ => (1 : ℝ)) c
  simpa only [one_mul, Complex.ofReal_one, partialSum] using congrArg (a * ·) hunit

/-- The exact centered ordered-gap identity for the wide, untruncated tent. -/
private theorem ordered_tent_identity (x : ℕ → ℝ) (c : ℕ → ℂ) (L : ℝ) (N : ℕ)
    (hmono : MonotoneOn x (Set.Iic (N + 1))) :
    realQuadratic (N + 2) (fun i j => L - |x i - x j|) c =
      (L - (x (N + 1) - x 0) / 2) * Complex.normSq (partialSum c (N + 2)) +
        2 * ∑ k ∈ range (N + 1), (x (k + 1) - x k) *
          Complex.normSq (partialSum c (k + 1) - partialSum c (N + 2) / 2) := by
  have hq : realQuadratic (N + 2) (fun i j => L - |x i - x j|) c =
      realQuadratic (N + 2) (fun i j => L - (x (N + 1) - x 0) / 2 +
        2 * ∑ k ∈ range (N + 1),
          (x (k + 1) - x k) * cutSign k i * cutSign k j) c := by
    unfold realQuadratic
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [kernel_feature_eq x L (N + 1) hmono
      (by have := mem_range.mp hi; omega) (by have := mem_range.mp hj; omega)]
  rw [hq, realQuadratic_add, realQuadratic_const, realQuadratic_scale,
    realQuadratic_sum]
  congr 2
  apply sum_congr rfl
  intro k hk
  rw [show (fun i j => (x (k + 1) - x k) * cutSign k i * cutSign k j) =
      (fun i j => (x (k + 1) - x k) * (cutSign k i * cutSign k j)) by
        funext i j; ring,
    realQuadratic_scale, realQuadratic_rankOne,
    cut_feature_eq_prefix c (by have := mem_range.mp hk; omega)]


private lemma ordered_wide_tent_lower_bound (x : ℕ → ℝ) (c : ℕ → ℂ) (N : ℕ)
    {g L : ℝ} (hg : 0 < g) (hmono : MonotoneOn x (Set.Iic (N + 1)))
    (hgap : ∀ k ∈ range (N + 1), g ≤ x (k + 1) - x k)
    (hgD : g ≤ x (N + 1) - x 0) (hDL : x (N + 1) - x 0 ≤ L) :
    (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
      realQuadratic (N + 2) (fun i j => max (L - |x i - x j|) 0) c := by
  have hmax {i j : ℕ} (hi : i ∈ range (N + 2)) (hj : j ∈ range (N + 2)) :
      max (L - |x i - x j|) 0 = L - |x i - x j| := by
    have hi' : i ≤ N + 1 := by have := mem_range.mp hi; omega
    have hj' : j ≤ N + 1 := by have := mem_range.mp hj; omega
    have hi0 := hmono (show 0 ∈ Set.Iic (N + 1) by simp) hi' (Nat.zero_le i)
    have hj0 := hmono (show 0 ∈ Set.Iic (N + 1) by simp) hj' (Nat.zero_le j)
    have hi1 := hmono hi' (show N + 1 ∈ Set.Iic (N + 1) by simp) hi'
    have hj1 := hmono hj' (show N + 1 ∈ Set.Iic (N + 1) by simp) hj'
    exact max_eq_left (sub_nonneg.mpr (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩))
  calc
    (g / 2) * (∑ i ∈ range (N + 2), Complex.normSq (c i)) ≤
        (L - (x (N + 1) - x 0) / 2) * Complex.normSq (partialSum c (N + 2)) +
          2 * ∑ k ∈ range (N + 1), (x (k + 1) - x k) *
            Complex.normSq (partialSum c (k + 1) - partialSum c (N + 2) / 2) :=
      centered_gap_coercivity c N (fun k => x (k + 1) - x k) hg hgD hDL hgap
    _ = realQuadratic (N + 2) (fun i j => L - |x i - x j|) c :=
      (ordered_tent_identity x c L N hmono).symm
    _ = _ := by
      unfold realQuadratic
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [hmax hi hj]

private lemma realQuadratic_fin (x : ℕ → ℝ) (c : ℕ → ℂ) (N : ℕ) (L : ℝ) :
    realQuadratic N (fun i j => max (L - |x i - x j|) 0) c =
      (star (fun i : Fin N => c i) ⬝ᵥ
        ((fun i j : Fin N => ((max (L - |x i - x j|) 0 : ℝ) : ℂ)) *ᵥ
          (fun i : Fin N => c i))).re := by
  symm
  calc
    (star (fun i : Fin N => c i) ⬝ᵥ
        ((fun i j : Fin N => ((max (L - |x i - x j|) 0 : ℝ) : ℂ)) *ᵥ
          (fun i : Fin N => c i))).re =
        ∑ i : Fin N, ∑ j : Fin N,
          (star (c i) * ((max (L - |x i - x j|) 0 : ℝ) : ℂ) * c j).re := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, mul_sum,
        Complex.re_sum, mul_assoc]
    _ = ∑ i : Fin N, ∑ j ∈ range N,
          (star (c i) * ((max (L - |x i - x j|) 0 : ℝ) : ℂ) * c j).re := by
      apply sum_congr rfl
      intro i _
      exact Fin.sum_univ_eq_sum_range _ N
    _ = realQuadratic N (fun i j => max (L - |x i - x j|) 0) c :=
      Fin.sum_univ_eq_sum_range _ N

private lemma tent_quadratic_reindex {n : ℕ} (e : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (c : Fin n → ℂ) (L : ℝ) :
    (star (c ∘ e) ⬝ᵥ
        ((fun i j : Fin n => ((max (L - |x (e i) - x (e j)|) 0 : ℝ) : ℂ)) *ᵥ
          (c ∘ e))).re =
      (star c ⬝ᵥ ((fun i j : Fin n => ((max (L - |x i - x j|) 0 : ℝ) : ℂ)) *ᵥ c)).re := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Function.comp_apply, mul_sum,
    Complex.re_sum, mul_assoc]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      (star (c (e i)) * (((max (L - |x (e i) - x (e j)|) 0 : ℝ) : ℂ) * c (e j))).re) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c (e i)) * (((max (L - |x (e i) - x j|) 0 : ℝ) : ℂ) * c j)).re := by
      apply sum_congr rfl
      intro i _
      exact e.sum_comp _
    _ = _ := e.sum_comp _

/-- A tent at least as wide as a separated finite configuration has the
uniform complex Gram lower bound `g/2`. -/
private theorem wide_tent_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) (c : Fin n → ℂ) {g L : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (hdiam : ∀ i j, |x i - x j| ≤ L) :
    (g / 2) * (∑ i, Complex.normSq (c i)) ≤
      (star c ⬝ᵥ ((fun i j => ((max (L - |x i - x j|) 0 : ℝ) : ℂ)) *ᵥ c)).re := by
  classical
  obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = N + 2 := by omega
  subst n
  have hx : Function.Injective x := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, abs_zero] at h
    linarith
  let s : Finset ℝ := univ.image x
  have hs : s.card = N + 2 := by
    dsimp [s]
    rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]
  let f : Fin (N + 2) → s := fun i => ⟨x i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hx
      exact congrArg Subtype.val hij
    · intro y
      rcases mem_image.mp y.property with ⟨i, _, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  let e₀ : Fin (N + 2) ≃ s := Equiv.ofBijective f hf
  let o : Fin (N + 2) ≃o s := s.orderIsoOfFin hs
  let e : Equiv.Perm (Fin (N + 2)) := o.toEquiv.trans e₀.symm
  have hsort (i : Fin (N + 2)) : x (e i) = (o i : ℝ) := by
    exact congrArg Subtype.val (e₀.apply_symm_apply (o i))
  let X : ℕ → ℝ := fun k => if hk : k < N + 2 then x (e ⟨k, hk⟩) else 0
  let C : ℕ → ℂ := fun k => if hk : k < N + 2 then c (e ⟨k, hk⟩) else 0
  have hX (i : Fin (N + 2)) : X i.val = x (e i) := by simp [X, i.isLt]
  have hC (i : Fin (N + 2)) : C i.val = c (e i) := by simp [C, i.isLt]
  have hmono : MonotoneOn X (Set.Iic (N + 1)) := by
    intro i hi j hj hij
    have hi' : i < N + 2 := by change i ≤ N + 1 at hi; omega
    have hj' : j < N + 2 := by change j ≤ N + 1 at hj; omega
    rw [show X i = x (e ⟨i, hi'⟩) from hX ⟨i, hi'⟩,
      show X j = x (e ⟨j, hj'⟩) from hX ⟨j, hj'⟩, hsort, hsort]
    exact o.monotone (show (⟨i, hi'⟩ : Fin (N + 2)) ≤ ⟨j, hj'⟩ from hij)
  have hgap : ∀ k ∈ range (N + 1), g ≤ X (k + 1) - X k := by
    intro k hk
    have hk' : k < N + 1 := mem_range.mp hk
    let i : Fin (N + 2) := ⟨k, by omega⟩
    let j : Fin (N + 2) := ⟨k + 1, by omega⟩
    have hne : e i ≠ e j := by
      intro hij
      have h := congrArg Fin.val (e.injective hij)
      dsimp [i, j] at h
      omega
    have hh := hsep (e i) (e j) hne
    rw [← hX i, ← hX j] at hh
    change g ≤ |X k - X (k + 1)| at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono (by omega) (by omega) (by omega)))] at hh
    linarith
  let i₀ : Fin (N + 2) := ⟨0, by omega⟩
  let i₁ : Fin (N + 2) := ⟨N + 1, by omega⟩
  have hne : e i₀ ≠ e i₁ := by
    intro hij
    have h := congrArg Fin.val (e.injective hij)
    dsimp [i₀, i₁] at h
    omega
  have hspan : |x (e i₀) - x (e i₁)| = X (N + 1) - X 0 := by
    rw [← hX i₀, ← hX i₁]
    change |X 0 - X (N + 1)| = X (N + 1) - X 0
    rw [abs_of_nonpos (sub_nonpos.mpr (hmono (by simp) (by simp) (by omega)))]
    ring
  have hgD : g ≤ X (N + 1) - X 0 := by
    rw [← hspan]
    exact hsep (e i₀) (e i₁) hne
  have hDL : X (N + 1) - X 0 ≤ L := by
    rw [← hspan]
    exact hdiam (e i₀) (e i₁)
  have h := ordered_wide_tent_lower_bound X C N hg hmono hgap hgD hDL
  have henergy : (∑ i ∈ range (N + 2), Complex.normSq (C i)) =
      ∑ i : Fin (N + 2), Complex.normSq (c i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => Complex.normSq (C i)) (N + 2)]
    simp_rw [hC]
    exact e.sum_comp _
  rw [henergy, realQuadratic_fin X C (N + 2) L] at h
  change (g / 2) * (∑ i, Complex.normSq (c i)) ≤
    (star (fun i : Fin (N + 2) => C i.val) ⬝ᵥ
      ((fun i j : Fin (N + 2) => ((max (L - |X i.val - X j.val|) 0 : ℝ) : ℂ)) *ᵥ
        (fun i : Fin (N + 2) => C i.val))).re at h
  simp_rw [hC, hX] at h
  exact h.trans_eq (tent_quadratic_reindex e x c L)


end WideTentCoercivity

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

private def quadratic {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, (star (c i) * c j).re * f (x i - x j)

private lemma re_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

private lemma quadratic_eq_re {n : ℕ} (f : ℝ → ℝ)
    (x : Fin n → ℝ) (c : Fin n → ℂ) :
    quadratic f x c =
      (star c ⬝ᵥ ((fun i j => (f (x i - x j) : ℂ)) *ᵥ c)).re := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
    re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private def tentEnergy {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  quadratic (fun t => max (s - |t|) 0) x c

private lemma tentEnergy_continuous {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Continuous (tentEnergy x c) := by
  unfold tentEnergy quadratic
  fun_prop

private lemma tentEnergy_eq_integral {n : ℕ} (x : Fin n → ℝ)
    (c : Fin n → ℂ) (s : ℝ) :
    tentEnergy x c s = ∫ u : ℝ,
      Complex.normSq (D5.S3.Analytic.Interpolation.AveragedBoxEnergy.boxSum x c s u) := by
  classical
  have hsum (u : ℝ) :
      D5.S3.Analytic.Interpolation.AveragedBoxEnergy.boxSum x c s u =
        ∑ i, intervalVector s (x i) u * c i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u ∈ Icc (x i) (x i + s) <;> simp [intervalVector, hi]
  rw [tentEnergy, quadratic_eq_re, ← (triangle_quadratic s x c).2,
    integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  exact integral_congr_ae (ae_of_all _ (fun u => congrArg Complex.normSq (hsum u).symm))

private lemma tentEnergy_nonneg {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) :
    0 ≤ tentEnergy x c s := by
  rw [tentEnergy_eq_integral]
  exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

private lemma tentEnergy_average {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    {g a : ℝ} (hg : 0 < g) (hga : g ≤ a)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) :
    a * g / 16 * (∑ i, Complex.normSq (c i)) ≤
      ∫ s : ℝ in Ioc a (2 * a), tentEnergy x c s := by
  have h := D5.S3.Analytic.Interpolation.AveragedBoxEnergy.averaged_box_energy_lower_bound
    x c hg hga hsep
  rw [integral_Icc_eq_integral_Ioc] at h
  simpa only [← tentEnergy_eq_integral] using h

/-- The original density is bounded below on a smaller window; the representer window
and its positive wide atom are retained. -/
private lemma density_lower_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
      ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s := by
  have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), (1 / 4 : ℝ) < s * D2 s :=
    weighted_D2_limit.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  refine ⟨min δ ε, lt_min hδ hε, min_le_left _ _, ?_⟩
  intro s hs
  have hquarter := (hall ⟨hs.1, hs.2.trans (min_le_right _ _)⟩).le
  apply (div_le_iff₀ (show (0 : ℝ) < 4 * s by positivity)).mpr
  nlinarith

/-- Each contained dyadic band uses only the lower density inherited from the
original representer. -/
private lemma density_lower_band {η g a : ℝ}
    (hη : ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s)
    (hg : 0 < g) (hga : g ≤ a) (haη : 2 * a ≤ η)
    {s : ℝ} (hs : s ∈ Icc a (2 * a)) :
    1 / (8 * a) ≤ D2 s := by
  have ha : 0 < a := hg.trans_le hga
  have hs0 : 0 < s := ha.trans_le hs.1
  calc
    1 / (8 * a) ≤ 1 / (4 * s) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hs.2]
    _ ≤ D2 s := hη s ⟨hs0, hs.2.trans haη⟩

/-- Half-open bands are disjoint at their shared dyadic endpoints. -/
private lemma dyadic_mixture_lower_bound
    (E : ℝ → ℝ) (hE : Continuous E) {δ η g C : ℝ}
    (hηδ : η ≤ δ) (hg : 0 < g)
    (hpos : ∀ s ∈ Ioc 0 δ, 0 < D2 s)
    (hEpos : ∀ s : ℝ, 0 ≤ E s)
    (hi : IntegrableOn (fun s => E s * D2 s) (Ioc 0 δ))
    (hη : ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s)
    (haverage : ∀ a : ℝ, g ≤ a → 2 * a ≤ η →
      a * g / 16 * C ≤ ∫ s : ℝ in Ioc a (2 * a), E s)
    (J : ℕ) (hJ : (2 : ℝ) ^ J * g ≤ η) :
    (J : ℝ) * g / 128 * C ≤ ∫ s : ℝ in Ioc 0 δ, E s * D2 s := by
  have hband (a : ℝ) (hga : g ≤ a) (haη : 2 * a ≤ η) :
      g / 128 * C ≤ ∫ s : ℝ in Ioc a (2 * a), E s * D2 s := by
    have ha : 0 < a := hg.trans_le hga
    have hiE : IntegrableOn E (Ioc a (2 * a)) :=
      hE.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hiED : IntegrableOn (fun s => E s * D2 s) (Ioc a (2 * a)) :=
      hi.mono_set (fun s hs => ⟨ha.trans hs.1, hs.2.trans (haη.trans hηδ)⟩)
    have hmono : (1 / (8 * a)) * (∫ s : ℝ in Ioc a (2 * a), E s) ≤
        ∫ s : ℝ in Ioc a (2 * a), E s * D2 s := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on (hiE.const_mul _) hiED measurableSet_Ioc
      intro s hs
      have hd := density_lower_band hη hg hga haη ⟨hs.1.le, hs.2⟩
      nlinarith [mul_le_mul_of_nonneg_left hd (hEpos s)]
    have hscaled := mul_le_mul_of_nonneg_left (haverage a hga haη)
      (show 0 ≤ 1 / (8 * a) by positivity)
    have heq : (1 / (8 * a)) * (a * g / 16 * C) = g / 128 * C := by
      field_simp [ha.ne']
      <;> ring
    exact heq ▸ hscaled.trans hmono
  have hrun : ∀ j : ℕ, (2 : ℝ) ^ j * g ≤ η →
      (j : ℝ) * g / 128 * C ≤
        ∫ s : ℝ in Ioc g ((2 : ℝ) ^ j * g), E s * D2 s := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hpow : (2 : ℝ) ^ (j + 1) * g = 2 * ((2 : ℝ) ^ j * g) := by
        rw [pow_succ]
        ring
      have ha : 0 < (2 : ℝ) ^ j * g := by positivity
      have hga : g ≤ (2 : ℝ) ^ j * g := by
        nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)]
      have haj : (2 : ℝ) ^ j * g ≤ η := by rw [hpow] at hj; linarith
      have hjband : 2 * ((2 : ℝ) ^ j * g) ≤ η := by rwa [← hpow]
      have hinc : (2 : ℝ) ^ j * g ≤ (2 : ℝ) ^ (j + 1) * g := by
        rw [hpow]; linarith
      have hi₁ : IntegrableOn (fun s => E s * D2 s)
          (Ioc g ((2 : ℝ) ^ j * g)) :=
        hi.mono_set (fun s hs => ⟨hg.trans hs.1, hs.2.trans (haj.trans hηδ)⟩)
      have hi₂ : IntegrableOn (fun s => E s * D2 s)
          (Ioc ((2 : ℝ) ^ j * g) ((2 : ℝ) ^ (j + 1) * g)) :=
        hi.mono_set (fun s hs => ⟨ha.trans hs.1, hs.2.trans (hj.trans hηδ)⟩)
      have hunion := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl _))
        measurableSet_Ioc hi₁ hi₂
      rw [Ioc_union_Ioc_eq_Ioc hga hinc] at hunion
      have hb := hband ((2 : ℝ) ^ j * g) hga hjband
      rw [← hpow] at hb
      rw [hunion]
      push_cast
      nlinarith [ih haj, hb]
  have hmono : (∫ s : ℝ in Ioc g ((2 : ℝ) ^ J * g), E s * D2 s) ≤
      ∫ s : ℝ in Ioc 0 δ, E s * D2 s := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (hEpos s) (hpos s hs).le
    · exact ae_of_all _ (fun s hs => ⟨hg.trans hs.1, hs.2.trans (hJ.trans hηδ)⟩)
  exact (hrun J hJ).trans hmono

private lemma quadratic_representation {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    {δ r L : ℝ}
    (hrep : ∀ t : ℝ, |t| ≤ δ →
      IntegrableOn (fun s : ℝ => max (s - |t|) 0 * D2 s) (Ioc 0 δ) ∧
      K t = (∫ s : ℝ in Ioc 0 δ, max (s - |t|) 0 * D2 s) + r * max (L - |t|) 0)
    (hdiam : ∀ i j, |x i - x j| ≤ δ) :
    IntegrableOn (fun s => tentEnergy x c s * D2 s) (Ioc 0 δ) ∧
    quadratic K x c = (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) +
      r * tentEnergy x c L := by
  have hi (i j : Fin n) : IntegrableOn (fun s : ℝ =>
      (star (c i) * c j).re * (max (s - |x i - x j|) 0 * D2 s)) (Ioc 0 δ) :=
    ((hrep (x i - x j) (hdiam i j)).1).const_mul _
  have he : (fun s => tentEnergy x c s * D2 s) = fun s =>
      ∑ i, ∑ j, (star (c i) * c j).re * (max (s - |x i - x j|) 0 * D2 s) := by
    funext s
    simp only [tentEnergy, quadratic, Finset.sum_mul, mul_assoc]
  have his : IntegrableOn (fun s => tentEnergy x c s * D2 s) (Ioc 0 δ) := by
    rw [he]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  have hint : (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) =
      ∑ i, ∑ j, (star (c i) * c j).re *
        (∫ s : ℝ in Ioc 0 δ, max (s - |x i - x j|) 0 * D2 s) := by
    rw [he, integral_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]
  refine ⟨his, ?_⟩
  rw [hint]
  simp only [tentEnergy, quadratic]
  simp_rw [(hrep _ (hdiam _ _)).2]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma inverse_entry_bound {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) {λ : ℝ}
    (hλ : 0 < λ)
    (hcoercive : ∀ v : Fin n → ℝ,
      λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v))
    (i j : Fin n) : |H⁻¹ i j| ≤ 1 / λ := by
  classical
  let e : Fin n → ℝ := Pi.single j 1
  let v : Fin n → ℝ := H⁻¹ *ᵥ e
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHv : H *ᵥ v = e := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
  have hv (k : Fin n) : v k = H⁻¹ k j := by
    simp only [v, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have hquad : λ * (∑ k, (v k) ^ 2) ≤ v j := by
    simpa only [hHv, e, dotProduct_single, mul_one] using hcoercive v
  have hcoord (k : Fin n) : (v k) ^ 2 ≤ ∑ l, (v l) ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (v l)) (Finset.mem_univ k)
  have hdiag : v j ≤ 1 / λ := by
    have hj : λ * (v j) ^ 2 ≤ v j :=
      (mul_le_mul_of_nonneg_left (hcoord j) hλ.le).trans hquad
    by_contra h
    have hvj : 1 / λ < v j := lt_of_not_ge h
    have hvj0 : 0 < v j := (one_div_pos.mpr hλ).trans hvj
    have hprod : 1 < λ * v j := by
      have := (div_lt_iff₀ hλ).mp hvj
      nlinarith
    have hstrict := mul_pos (sub_pos.mpr hprod) hvj0
    nlinarith
  have hi : λ * (v i) ^ 2 ≤ 1 / λ :=
    ((mul_le_mul_of_nonneg_left (hcoord i) hλ.le).trans hquad).trans hdiag
  have hisq : (v i) ^ 2 ≤ (1 / λ) ^ 2 := by
    calc
      (v i) ^ 2 ≤ (1 / λ) / λ := (le_div_iff₀ hλ).mpr (by nlinarith [hi])
      _ = (1 / λ) ^ 2 := by ring
  rw [← hv i]
  apply (sq_le_sq₀ (abs_nonneg _) (one_div_pos.mpr hλ).le).mp
  simpa only [sq_abs] using hisq

private lemma inverse_budget_bound {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) {λ : ℝ}
    (hλ : 0 < λ)
    (hcoercive : ∀ v : Fin n → ℝ,
      λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v)) :
    1 + ∑ i, ∑ j, |H⁻¹ i j| ≤ 1 + (n : ℝ) ^ 2 / λ := by
  have hsum : (∑ i, ∑ j, |H⁻¹ i j|) ≤ ∑ _i : Fin n, ∑ _j : Fin n, 1 / λ :=
    Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => inverse_entry_bound H hH hλ hcoercive i j))
  have hconstant : (∑ _i : Fin n, ∑ _j : Fin n, 1 / λ) = (n : ℝ) ^ 2 / λ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [hsum.trans_eq hconstant]

/-- One fixed arithmetic window has a dyadically improving coercivity margin and
the corresponding entrywise inverse budget for every finite separated family. -/
theorem exists_window_dyadic_conditioning : ∃ δ η r : ℝ,
    0 < δ ∧ δ < Real.log 2 ∧ 0 < η ∧ η ≤ δ ∧ 0 < r ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (x : Fin n → ℝ) (g : ℝ), 0 < g →
      (∀ i j, i ≠ j → g ≤ |x i - x j|) →
      (∀ i j, |x i - x j| ≤ δ) →
      ∀ (J : ℕ), (2 : ℝ) ^ J * g ≤ η →
      let λ := g * (r / 2 + (J : ℝ) / 128)
      let H : Matrix (Fin n) (Fin n) ℝ := fun i j => K (x i - x j)
      (∀ c : Fin n → ℂ, λ * (∑ i, Complex.normSq (c i)) ≤
        (star c ⬝ᵥ ((fun i j => (K (x i - x j) : ℂ)) *ᵥ c)).re) ∧
      (∀ i j : Fin n, |H⁻¹ i j| ≤ 1 / λ) ∧
      1 + (∑ i, ∑ j, |H⁻¹ i j|) ≤ 1 + (n : ℝ) ^ 2 / λ := by
  classical
  obtain ⟨δ, r, L, hδ, hδ2, hr, hL, hpos, _hi, hrep⟩ := actual_positive_representer
  obtain ⟨η, hη, hηδ, hdensity⟩ := density_lower_window hδ
  refine ⟨δ, η, r, hδ, hδ2, hη, hηδ, hr, ?_⟩
  intro n hn x g hg hsep hdiam J hJ
  let λ := g * (r / 2 + (J : ℝ) / 128)
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => K (x i - x j)
  have hλ : 0 < λ := by
    dsimp [λ]
    exact mul_pos hg (add_pos_of_pos_of_nonneg (by positivity) (by positivity))
  have hcomplex (c : Fin n → ℂ) :
      λ * (∑ i, Complex.normSq (c i)) ≤
        (star c ⬝ᵥ ((fun i j => (K (x i - x j) : ℂ)) *ᵥ c)).re := by
    obtain ⟨hmi, hqrep⟩ := quadratic_representation x c hrep hdiam
    have hmix := dyadic_mixture_lower_bound (tentEnergy x c)
      (tentEnergy_continuous x c) hηδ hg hpos (tentEnergy_nonneg x c) hmi hdensity
      (fun a hga _haη => tentEnergy_average x c hg hga hsep) J hJ
    have hwide : g / 2 * (∑ i, Complex.normSq (c i)) ≤ tentEnergy x c L := by
      rw [tentEnergy, quadratic_eq_re]
      exact WideTentCoercivity.wide_tent_lower_bound
        hn x c hg hsep (fun i j => (hdiam i j).trans hL.le)
    calc
      λ * (∑ i, Complex.normSq (c i)) =
          (J : ℝ) * g / 128 * (∑ i, Complex.normSq (c i)) +
            r * (g / 2 * (∑ i, Complex.normSq (c i))) := by dsimp [λ]; ring
      _ ≤ (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) +
            r * tentEnergy x c L :=
        add_le_add hmix (mul_le_mul_of_nonneg_left hwide hr.le)
      _ = quadratic K x c := hqrep.symm
      _ = _ := quadratic_eq_re K x c
  have hreal (v : Fin n → ℝ) : λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v) := by
    have hc := hcomplex (fun k => (v k : ℂ))
    rw [← quadratic_eq_re] at hc
    have hnorm : (∑ k, Complex.normSq ((v k : ℝ) : ℂ)) = ∑ k, (v k) ^ 2 := by
      simp only [Complex.normSq_ofReal, pow_two]
    rw [hnorm] at hc
    convert hc using 1
    simp only [H, quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hHermitian : H.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [H, star_trivial, K, abs_sub_comm]
  have hH : H.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian
    intro v hv
    have hsum : 0 < ∑ k, (v k) ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun l _ => sq_nonneg (v l))
        ⟨k, Finset.mem_univ _, sq_pos_of_ne_zero hk⟩
    simpa only [star_trivial] using (mul_pos hλ hsum).trans_le (hreal v)
  exact ⟨hcomplex, inverse_entry_bound H hH hλ hreal,
    inverse_budget_bound H hH hλ hreal⟩

#print axioms exists_window_dyadic_conditioning

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelDyadicCoercivity
