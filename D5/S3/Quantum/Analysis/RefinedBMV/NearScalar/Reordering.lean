/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/Reordering
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Proof component of the four-copy refined BMV comparison near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMV44
import Mathlib.Algebra.BigOperators.Ring.List

/-!
The reordering step of the uniform near-scalar spectral theorem for the
four-factor bound in refined-bmv-uniform-window-comparator-proof-20261125.txt.
The two-commutator trace bound enters as a hypothesis.
-/

open Matrix

noncomputable section

namespace RefinedBMV
namespace NearScalarReordering

open Algebra44 (realTrace)
open private evalWord_reverse from D5.S3.Quantum.Analysis.RefinedBMV44
open private evalWord_append43 evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev Swap := List Bool × List Bool

private def prepend (letter : Bool) (s : Swap) : Swap :=
  (letter :: s.1, s.2)

/-- Insert a leading B across a block of `a` H letters followed by `b` B letters.
Each pair records the prefix and suffix around the exchanged pair. -/
private def insertB (a b : ℕ) : List Swap :=
  match a with
  | 0 => []
  | a + 1 => ([], List.replicate a true ++ List.replicate b false) ::
      (insertB a b).map (prepend true)

/-- Sort the tail first, then insert the leading letter. Every exchange
replaces BH by HB, so the matrix expansion has a common sign. -/
private def sortingSwaps : List Bool → List Swap
  | [] => []
  | true :: w => (sortingSwaps w).map (prepend true)
  | false :: w => (sortingSwaps w).map (prepend false) ++
      insertB (w.count true) (w.count false)

private theorem insertB_length (a b : ℕ) : (insertB a b).length = a := by
  induction a with
  | zero => rfl
  | succ a ih => simp [insertB, ih]

private theorem sortingSwaps_length_le (w : List Bool) :
    (sortingSwaps w).length ≤ w.count true * w.count false := by
  induction w with
  | nil => simp [sortingSwaps]
  | cons letter w ih =>
    cases letter
    · simpa [sortingSwaps, insertB_length, Nat.mul_succ] using
        Nat.add_le_add_right ih (w.count true)
    · simp only [sortingSwaps, List.length_map, List.count_cons_self,
        List.count_cons_of_ne (Ne.symm Bool.false_ne_true), Nat.succ_mul]
      exact ih.trans (Nat.le_add_right _ _)

private theorem insertB_counts (a b : ℕ) (s : Swap) (hs : s ∈ insertB a b) :
    (s.1 ++ s.2).count true + 1 = a ∧ (s.1 ++ s.2).count false = b := by
  induction a generalizing s with
  | zero => simp [insertB] at hs
  | succ a ih =>
    simp only [insertB, List.mem_cons, List.mem_map] at hs
    rcases hs with rfl | ⟨t, ht, rfl⟩
    · simp [List.count_append, List.count_replicate]
    · obtain ⟨hH, hB⟩ := ih t ht
      simp only [prepend, List.cons_append, List.count_cons_self,
        List.count_cons_of_ne (Ne.symm Bool.false_ne_true)]
      exact ⟨congrArg Nat.succ hH, hB⟩

private theorem sortingSwaps_counts (w : List Bool) (s : Swap)
    (hs : s ∈ sortingSwaps w) :
    (s.1 ++ s.2).count true + 1 = w.count true ∧
      (s.1 ++ s.2).count false + 1 = w.count false := by
  induction w generalizing s with
  | nil => simp [sortingSwaps] at hs
  | cons letter w ih =>
    cases letter
    · simp only [sortingSwaps, List.mem_append, List.mem_map] at hs
      rcases hs with ⟨t, ht, rfl⟩ | ht
      · obtain ⟨hH, hB⟩ := ih t ht
        simp only [prepend, List.cons_append, List.count_cons_self,
          List.count_cons_of_ne Bool.false_ne_true]
        exact ⟨hH, congrArg Nat.succ hB⟩
      · obtain ⟨hH, hB⟩ := insertB_counts _ _ s ht
        simpa only [List.count_cons_self, List.count_cons_of_ne Bool.false_ne_true]
          using And.intro hH (congrArg (· + 1) hB)
    · simp only [sortingSwaps, List.mem_map] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      obtain ⟨hH, hB⟩ := ih t ht
      simp only [prepend, List.cons_append, List.count_cons_self,
        List.count_cons_of_ne (Ne.symm Bool.false_ne_true)]
      exact ⟨congrArg Nat.succ hH, hB⟩

private def swapValue (H B : Matrix n n ℂ) (s : Swap) : Matrix n n ℂ :=
  evalWord H B s.1 * (H * B - B * H) * evalWord H B s.2

private theorem prepend_sum (H B : Matrix n n ℂ) (letter : Bool) (swaps : List Swap) :
    ((swaps.map (prepend letter)).map (swapValue H B)).sum =
      (if letter then H else B) * (swaps.map (swapValue H B)).sum := by
  have h (s : Swap) : swapValue H B (prepend letter s) =
      (if letter then H else B) * swapValue H B s := by
    cases letter <;> simp [swapValue, prepend, evalWord, mul_assoc]
  simp only [List.map_map, Function.comp_def, h, List.sum_map_mul_left]

private theorem eval_replicate_false (H B : Matrix n n ℂ) (b : ℕ) :
    evalWord H B (List.replicate b false) = B ^ b := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [List.replicate_succ, evalWord, ih, pow_succ']

private theorem insertB_expansion (H B : Matrix n n ℂ) (a b : ℕ) :
    ((insertB a b).map (swapValue H B)).sum =
      H ^ a * B ^ (b + 1) - B * (H ^ a * B ^ b) := by
  induction a with
  | zero => simp [insertB, pow_succ']
  | succ a ih =>
    simp only [insertB, List.map_cons, List.sum_cons, prepend_sum, ite_true, ih]
    rw [show swapValue H B ([], List.replicate a true ++ List.replicate b false) =
      (H * B - B * H) * (H ^ a * B ^ b) by
        simp only [swapValue, evalWord, one_mul, evalWord_block43, eval_replicate_false]]
    simp only [pow_succ' H a, pow_succ' B b, sub_mul, mul_sub, mul_assoc]
    abel

private theorem sorting_expansion (H B : Matrix n n ℂ) (w : List Bool) :
    H ^ w.count true * B ^ w.count false - evalWord H B w =
      ((sortingSwaps w).map (swapValue H B)).sum := by
  induction w with
  | nil => simp [sortingSwaps, evalWord]
  | cons letter w ih =>
    cases letter
    · simp only [sortingSwaps, List.map_append, List.sum_append, prepend_sum,
        Bool.false_eq_true, ite_false, insertB_expansion, ← ih, evalWord,
        List.count_cons_self, List.count_cons_of_ne Bool.false_ne_true, mul_sub]
      abel
    · simp only [sortingSwaps, prepend_sum, ite_true, ← ih, evalWord,
        List.count_cons_self, List.count_cons_of_ne (Ne.symm Bool.false_ne_true), pow_succ']
      rw [mul_sub, mul_assoc]

/-- Apply real trace after left multiplication to the matrix sorting expansion. -/
private theorem realTrace_sorting_expansion (H B D : Matrix n n ℂ) (w : List Bool) :
    realTrace (D * (H ^ w.count true * B ^ w.count false)) -
        realTrace (D * evalWord H B w) =
      ((sortingSwaps w).map fun s => realTrace (D * swapValue H B s)).sum := by
  let f : Matrix n n ℂ →+ ℝ :=
    (Complex.reAddGroupHom.comp (Matrix.traceAddMonoidHom n ℂ)).comp (AddMonoidHom.mulLeft D)
  have hf_apply (X : Matrix n n ℂ) : f X = realTrace (D * X) := rfl
  have hf := congrArg f (sorting_expansion H B w)
  simp only [map_sub, map_list_sum, List.map_map, Function.comp_def] at hf
  simpa only [hf_apply] using hf

omit [DecidableEq n] in
private theorem realTrace_adjoint (X : Matrix n n ℂ) : realTrace Xᴴ = realTrace X := by
  rw [realTrace, trace_conjTranspose]
  rfl

omit [DecidableEq n] in
private theorem realTrace_mul_comm (X Y : Matrix n n ℂ) :
    realTrace (X * Y) = realTrace (Y * X) :=
  congrArg Complex.re (trace_mul_comm X Y)

omit [DecidableEq n] in
/-- Cyclicity and skew-adjointness give twice the real trace as a difference. -/
private theorem twice_realTrace_skew (C Z : Matrix n n ℂ) (hC : Cᴴ = -C) :
    2 * realTrace (C * Z) = realTrace (C * Z) - realTrace (C * Zᴴ) := by
  have h : realTrace (C * Z) = -realTrace (C * Zᴴ) := by
    calc
      realTrace (C * Z) = realTrace (C * Z)ᴴ := (realTrace_adjoint _).symm
      _ = realTrace (Zᴴ * -C) := by rw [conjTranspose_mul, hC]
      _ = realTrace (-C * Zᴴ) := realTrace_mul_comm _ _
      _ = -realTrace (C * Zᴴ) := by
        simp only [neg_mul, realTrace, trace_neg, Complex.neg_re]
  linarith only [h]

/-- The two sorting sums have the same sorted baseline. Each summand
contains the initial commutator and the commutator of its exchange. -/
private theorem two_commutator_expansion (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (w : List Bool) :
    let C := H * B - B * H
    2 * realTrace (C * evalWord H B w) =
      ((sortingSwaps w.reverse).map fun s => realTrace (C * swapValue H B s)).sum -
      ((sortingSwaps w).map fun s => realTrace (C * swapValue H B s)).sum := by
  let C := H * B - B * H
  have hC : Cᴴ = -C := by
    simp only [C, conjTranspose_sub, conjTranspose_mul, hH.eq, hB.eq, neg_sub]
  have h := twice_realTrace_skew C (evalWord H B w) hC
  rw [← evalWord_reverse H B hH hB w] at h
  have hf := realTrace_sorting_expansion H B C w
  have hr := realTrace_sorting_expansion H B C w.reverse
  simp only [List.count_reverse] at hr
  change 2 * realTrace (C * evalWord H B w) =
    ((sortingSwaps w.reverse).map fun s => realTrace (C * swapValue H B s)).sum -
    ((sortingSwaps w).map fun s => realTrace (C * swapValue H B s)).sum
  linarith only [h, hf, hr]

private theorem abs_map_sum_le {α : Type*} (l : List α) (f : α → ℝ) (K : ℝ)
    (h : ∀ v ∈ l, |f v| ≤ K) :
    |(l.map f).sum| ≤ (l.length : ℝ) * K := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have hv := h v (List.mem_cons_self)
    have hl := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (by linarith only [hv, hl])

private theorem one_commutator_bound (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (w : List Bool) (K : ℝ)
    (hK : 0 ≤ K)
    (hbound : ∀ u v : List Bool,
      (u ++ v).count true + 1 = w.count true →
      (u ++ v).count false + 1 = w.count false →
      |realTrace ((H * B - B * H) * evalWord H B u *
        (H * B - B * H) * evalWord H B v)| ≤ K) :
    |realTrace ((H * B - B * H) * evalWord H B w)| ≤
      ((w.count true * w.count false : ℕ) : ℝ) * K := by
  let C := H * B - B * H
  let f : Swap → ℝ := fun s => realTrace (C * swapValue H B s)
  have hterm : ∀ v : List Bool, v.count true = w.count true →
      v.count false = w.count false → ∀ s ∈ sortingSwaps v, |f s| ≤ K := by
    intro v hvH hvB s hs
    obtain ⟨hsH, hsB⟩ := sortingSwaps_counts v s hs
    simpa only [f, swapValue, C, mul_assoc] using
      hbound s.1 s.2 (hsH.trans hvH) (hsB.trans hvB)
  have hforward := abs_map_sum_le (sortingSwaps w) f K (hterm w rfl rfl)
  have hreverse := abs_map_sum_le (sortingSwaps w.reverse) f K
    (hterm w.reverse List.count_reverse List.count_reverse)
  have hlen : ((sortingSwaps w).length : ℝ) ≤
      ((w.count true * w.count false : ℕ) : ℝ) := by
    exact_mod_cast sortingSwaps_length_le w
  have hlenRevNat : (sortingSwaps w.reverse).length ≤ w.count true * w.count false := by
    simpa only [List.count_reverse] using sortingSwaps_length_le w.reverse
  have hlenRev : ((sortingSwaps w.reverse).length : ℝ) ≤
      ((w.count true * w.count false : ℕ) : ℝ) := by
    exact_mod_cast hlenRevNat
  have hexp := two_commutator_expansion H B hH hB w
  change 2 * realTrace (C * evalWord H B w) =
    ((sortingSwaps w.reverse).map f).sum - ((sortingSwaps w).map f).sum at hexp
  change |realTrace (C * evalWord H B w)| ≤ _
  have habs := congrArg (abs : ℝ → ℝ) hexp
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] at habs
  have htriangle :
      |((sortingSwaps w.reverse).map f).sum - ((sortingSwaps w).map f).sum| ≤
        |((sortingSwaps w.reverse).map f).sum| + |((sortingSwaps w).map f).sum| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ((sortingSwaps w.reverse).map f).sum (-((sortingSwaps w).map f).sum)
  linarith only [habs, htriangle, hforward, hreverse,
    mul_le_mul_of_nonneg_right hlen hK, mul_le_mul_of_nonneg_right hlenRev hK]

/-- For a word with m H letters and four B letters, K bounds the absolute
real trace of every word with two commutators, m - 2 H letters and two B
letters. Cyclically starting those words at a commutator gives the two
ordinary word segments in hbound. -/
theorem abs_realTrace_sub_sorted_le (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.IsHermitian) (w : List Bool) (m : ℕ)
    (hm : w.count true = m) (hb : w.count false = 4) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u v : List Bool, (u ++ v).count true = m - 2 →
      (u ++ v).count false = 2 →
      |realTrace ((H * B - B * H) * evalWord H B u *
        (H * B - B * H) * evalWord H B v)| ≤ K) :
    |realTrace (evalWord H B w) - realTrace (H ^ m * B ^ 4)| ≤
      12 * (m : ℝ) * ((m - 1 : ℕ) : ℝ) * K := by
  let C := H * B - B * H
  have hterm : ∀ s ∈ sortingSwaps w,
      |realTrace (swapValue H B s)| ≤ ((m - 1 : ℕ) : ℝ) * 3 * K := by
    intro s hs
    obtain ⟨hsH, hsB⟩ := sortingSwaps_counts w s hs
    let z := s.2 ++ s.1
    have hzH : z.count true = m - 1 := by
      simp only [z, List.count_append]
      simp only [List.count_append, hm] at hsH
      omega
    have hzB : z.count false = 3 := by
      simp only [z, List.count_append]
      simp only [List.count_append, hb] at hsB
      omega
    have hrotate : realTrace (swapValue H B s) = realTrace (C * evalWord H B z) := by
      calc
        realTrace (swapValue H B s) =
            realTrace (evalWord H B s.1 * (C * evalWord H B s.2)) := by
          simp only [swapValue, C, mul_assoc]
        _ = realTrace ((C * evalWord H B s.2) * evalWord H B s.1) :=
          realTrace_mul_comm _ _
        _ = realTrace (C * evalWord H B z) := by
          simp only [z, evalWord_append43, mul_assoc]
    rw [hrotate]
    have hinner := one_commutator_bound H B hH hB z K hK (by
      intro u v huvH huvB
      apply hbound u v
      · omega
      · omega)
    simpa only [hzH, hzB, Nat.cast_mul, Nat.cast_ofNat, C] using hinner
  have hsum := abs_map_sum_le (sortingSwaps w)
    (fun s => realTrace (swapValue H B s)) _ hterm
  have hlenNat : (sortingSwaps w).length ≤ m * 4 := by
    simpa only [hm, hb] using sortingSwaps_length_le w
  have hlen : ((sortingSwaps w).length : ℝ) ≤ ((m * 4 : ℕ) : ℝ) := by
    exact_mod_cast hlenNat
  have hexp := realTrace_sorting_expansion H B (1 : Matrix n n ℂ) w
  simp only [one_mul, hm, hb] at hexp
  rw [abs_sub_comm, hexp]
  calc
    _ ≤ ((sortingSwaps w).length : ℝ) * (((m - 1 : ℕ) : ℝ) * 3 * K) := hsum
    _ ≤ ((m * 4 : ℕ) : ℝ) * (((m - 1 : ℕ) : ℝ) * 3 * K) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring

end NearScalarReordering
end RefinedBMV
