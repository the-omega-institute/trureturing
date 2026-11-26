/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SeventeenFour
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/SeventeenFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV product and exponential lower bounds at bidegree (17,4). -/

import D5.S3.Quantum.Analysis.RefinedBMV67
import D5.S3.Quantum.Analysis.RefinedBMV84
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Analysis.RefinedBMV.SeventeenFourGram
import D5.S3.Quantum.Analysis.RefinedBMV.SeventeenFourFactors

/-! # Four-copy refined BMV at degree 17

An A-weighted rational Gram matrix compares the word mean with the trace
of the integer-gap word (5, 4, 4, 4). Two trace comparisons then bound the
fractional product by that integer-gap word.
-/

open Matrix NormedSpace
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV

namespace WeightedGram67

open private gramTerms scaleTerms
  weightedSum weightedSum_append weightedSum_scale traceWord
  eval_gramTerms weightedGram_nonneg_of_ldl orderedTraceSum_re
  real_rat_mul from D5.S3.Quantum.Analysis.RefinedBMV67

open private Algebra84.ldlChecks Algebra84.ldlChecks_sound
  from D5.S3.Quantum.Analysis.RefinedBMV84

open private Word Terms weightedSum_eq_map
  from D5.S3.Quantum.Analysis.RefinedBMV67

open private FourCopyGap.gapTrace FourCopyGap.sum_gaps_nested FourCopyGap.word_count
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43

private def mergeAdjacent : Terms → Terms
  | [] => []
  | u :: us =>
    match mergeAdjacent us with
    | [] => [u]
    | v :: vs =>
      if u.2 = v.2 then (u.1 + v.1, u.2) :: vs else u :: v :: vs

private theorem weightedSum_mergeAdjacent (f : Word → ℂ) (terms : Terms) :
    weightedSum f (mergeAdjacent terms) = weightedSum f terms := by
  induction terms with
  | nil => rfl
  | cons u us ih =>
    rw [mergeAdjacent]
    cases h : mergeAdjacent us with
    | nil =>
      rw [h] at ih
      simp only [weightedSum] at ih ⊢
      rw [← ih]
    | cons v vs =>
      rw [h] at ih
      change weightedSum f (if u.2 = v.2 then (u.1 + v.1, u.2) :: vs else u :: v :: vs) =
        weightedSum f (u :: us)
      by_cases huv : u.2 = v.2
      · rw [ite_eq_left huv]
        simp only [weightedSum] at ih ⊢
        rw [← ih, Rat.cast_add, add_smul, huv, add_assoc]
      · rw [ite_eq_right huv]
        simp only [weightedSum] at ih ⊢
        rw [ih]

/-- Use binary codes to select the rotation before constructing its list of letters. -/
private def cyclicWord (word : Word) : Word :=
  let length := word.length
  let modulus := 2 ^ length
  let highBit := 2 ^ (length - 1)
  let code := word.foldl (fun value letter => 2 * value + letter.toNat) 0
  let (index, _, _) := (List.range length).foldl (fun (index, best, current) rotation =>
    let next := (2 * current + current / highBit) % modulus
    if current < best then (rotation, current, next) else (index, best, next)) (0, code, code)
  word.rotate index

/-- Stable binary radix sort of the first `bits` letters of each word. -/
private def radixSort : ℕ → Terms → Terms
  | 0, terms => terms
  | bits + 1, terms =>
    let sorted := radixSort bits terms
    let buckets := sorted.partition fun t => !(t.2[bits]?.getD false)
    buckets.1 ++ buckets.2

private theorem radixSort_perm (bits : ℕ) (terms : Terms) : (radixSort bits terms).Perm terms := by
  induction bits with
  | zero => exact List.Perm.refl _
  | succ bits ih =>
    simp only [radixSort, List.partition_eq_filter_filter, Function.comp_def]
    exact (List.filter_append_perm _ _).trans ih

private def sortedCoefficients (terms : Terms) : Terms :=
  mergeAdjacent (radixSort 21 (terms.map fun (c, w) => (c, cyclicWord w)))

private theorem weightedSum_sortedCoefficients (f : Word → ℂ)
    (hf : ∀ w, f (cyclicWord w) = f w) (terms : Terms) :
    weightedSum f (sortedCoefficients terms) = weightedSum f terms := by
  rw [sortedCoefficients, weightedSum_mergeAdjacent]
  simp only [weightedSum_eq_map]
  rw [((radixSort_perm _ _).map _).sum_eq]
  simp only [List.map_map, Function.comp_def, hf]

private def sortedCoefficientsVanish (terms : Terms) : Bool :=
  (sortedCoefficients terms).all fun t => decide (t.1 = 0)

private theorem sortedCoefficients_sound (f : Word → ℂ)
    (hf : ∀ w, f (cyclicWord w) = f w) (terms : Terms)
    (h : sortedCoefficientsVanish terms = true) : weightedSum f terms = 0 := by
  rw [← weightedSum_sortedCoefficients f hf]
  have hz : ∀ t ∈ sortedCoefficients terms, t.1 = 0 := fun t ht =>
    of_decide_eq_true (List.all_eq_true.mp h t ht)
  generalize sortedCoefficients terms = coefficients at hz ⊢
  induction coefficients with
  | nil => rfl
  | cons t ts ih =>
    simp only [weightedSum, hz t List.mem_cons_self, Rat.cast_zero, zero_smul, zero_add]
    exact ih fun s hs => hz s (List.mem_cons_of_mem _ hs)

local notation "𝔞" => true
local notation "𝔟" => false

private def words174 : Fin 45 → List Bool :=
  ![[𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟],
    [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟]]

private def comparator174 : List Bool :=
  [𝔞, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔞, 𝔞, 𝔞, 𝔞, 𝔟]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
-- Check all entries of the rational factorization.
private theorem ldl174 : Algebra84.ldlChecks G174 d174 F174 = true := by
  decide +kernel

private def features174 (i : Fin 45) : List (ℚ × List Bool) := [(1, words174 i)]

private def gapWord (g : FourCopyGap.Gap) : Word :=
  List.replicate g.1 true ++ [false] ++
    List.replicate g.2.1 true ++ [false] ++
    List.replicate g.2.2.1 true ++ [false] ++
    List.replicate g.2.2.2 true ++ [false]

private def fourGapWords (p : ℕ) : List Word :=
  (List.range (p + 1)).flatMap fun i =>
    (List.range (p - i + 1)).flatMap fun j =>
      (List.range (p - i - j + 1)).map fun k => gapWord (i, j, k, p - i - j - k)

private def fourGapTerms (p : ℕ) (c : ℚ) (target : Word) : Terms :=
  scaleTerms (1 / 4) ((fourGapWords p).map fun w => (1, w)) ++ [(-c, target)]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 32000000 in
-- Normalize and compare the complete cyclic coefficient list.
private theorem coefficients174 :
    sortedCoefficientsVanish
      (scaleTerms 355741693384780800000000 (fourGapTerms 17 (1140 / 4) comparator174) ++
        scaleTerms (-1) (gramTerms G174 [𝔞] [] features174)) = true := by
  decide +kernel

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem traceWord_cyclicWord (A B : Mat) (w : Word) :
    traceWord A B (cyclicWord w) = traceWord A B w :=
  evalWord_rotate_trace43 _ _ _ _

private theorem traceWord_gapWord (A B : Mat) (g : FourCopyGap.Gap) :
    traceWord A B (gapWord g) = FourCopyGap.gapTrace A B g := by
  obtain ⟨i, j, k, l⟩ := g
  simp only [traceWord, gapWord, FourCopyGap.gapTrace, List.append_assoc,
    List.singleton_append, List.cons_append, List.nil_append, evalWord_block43, evalWord, mul_one, mul_assoc]

private theorem sum_range_list (p : ℕ) (f : ℕ → ℂ) :
    ((List.range p).map f).sum = ∑ i ∈ Finset.range p, f i := by
  rfl

private theorem sum_flatMap_map {α β : Type*} (xs : List α) (f : α → List β)
    (g : β → ℂ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

private theorem sum_fourGapWords (A B : Mat) (p : ℕ) :
    ((fourGapWords p).map (traceWord A B)).sum =
      ∑ g ∈ FourCopyGap.gaps p, FourCopyGap.gapTrace A B g := by
  rw [FourCopyGap.sum_gaps_nested]
  simp only [fourGapWords, sum_flatMap_map, List.map_map, Function.comp_def,
    traceWord_gapWord, sum_range_list]

private theorem eval_fourGapTerms174 (A B : Mat) (c : ℚ) (target : Word) :
    weightedSum (traceWord A B) (fourGapTerms 17 c target) =
      ((1 / 21 : ℚ) : ℂ) * orderedTraceSum A B 17 -
        (c : ℂ) * traceWord A B target := by
  have hwordCount : (balancedWords 17 4).length = 5985 :=
    (FourCopyGap.word_count 17 4).trans (by decide)
  have hgapCount : (FourCopyGap.gaps 17).card = 1140 :=
    (FourCopyGap.gaps_card 17).trans (by decide)
  have h := FourCopyGap.wordMean_eq_gaps 17 A B
  simp only [FourCopyGap.wordMean, hwordCount, hgapCount] at h
  change orderedTraceSum A B 17 / ((5985 : ℕ) : ℂ) = _ at h
  have scaleMean (ordered gaps : ℂ)
      (hmean : ordered / ((5985 : ℕ) : ℂ) = gaps / ((1140 : ℕ) : ℂ)) :
      ((1 / 4 : ℚ) : ℂ) * gaps = ((1 / 21 : ℚ) : ℂ) * ordered := by
    norm_num at hmean ⊢
    linear_combination -285 * hmean
  have hscaled := scaleMean _ _ h
  rw [fourGapTerms, weightedSum_append, weightedSum_scale]
  simp only [weightedSum_eq_map, List.map_map, Function.comp_def,
    smul_eq_mul, Rat.cast_one, one_mul, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Rat.cast_neg, neg_mul, sub_eq_add_neg]
  rw [sum_fourGapWords, hscaled]

private theorem comparator174_eval (A B : Mat) :
    traceWord A B comparator174 = trace ((A ^ 5 * B) * (A ^ 4 * B) ^ 3) := by
  simp only [traceWord, comparator174, evalWord, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]

private theorem trace_gap174 (A B : Mat) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((355741693384780800000000 : ℚ) : ℂ) * (((1 / 21 : ℚ) : ℂ) * orderedTraceSum A B 17 -
      ((1140 / 4 : ℚ) : ℂ) * trace ((A ^ 5 * B) * (A ^ 4 * B) ^ 3)) =
      weightedGram G174 (fun i => weightedSum (evalWord A B) (features174 i)) A 1 := by
  have h := sortedCoefficients_sound (traceWord A B) (traceWord_cyclicWord A B) _ coefficients174
  apply eq_of_sub_eq_zero
  simp only [weightedSum_append, weightedSum_scale, eval_fourGapTerms174,
    eval_gramTerms A B hA hB, comparator174_eval, Rat.cast_neg, Rat.cast_one,
    evalWord, mul_one, sub_eq_add_neg] at h ⊢
  norm_num at h ⊢
  exact h

private theorem balanced_bound174 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    5985 * (trace ((A ^ 5 * B) * (A ^ 4 * B) ^ 3)).re ≤
      ((balancedWords 17 4).map fun w => (trace (evalWord A B w)).re).sum := by
  obtain ⟨hd, hG⟩ := Algebra84.ldlChecks_sound ldl174
  let d : Fin (28 + 17) → ℚ := Fin.addCases d174 (fun _ => 0)
  let F : Matrix (Fin 45) (Fin (28 + 17)) ℚ :=
    fun i => Fin.addCases (F174 i) (fun _ => 0)
  have hd' (t : Fin (28 + 17)) : 0 ≤ d t := by
    induction t using Fin.addCases with
    | left i => simpa only [d, Fin.addCases_left] using hd i
    | right i => simp only [d, Fin.addCases_right, le_refl]
  have hG' (i j : Fin 45) : G174 i j = ∑ t, d t * (F i t * F j t) := by
    rw [Fin.sum_univ_add]
    simpa only [d, F, Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero,
      add_zero] using hG i j
  have hgram := weightedGram_nonneg_of_ldl G174
    (fun i => weightedSum (evalWord A B) (features174 i)) A 1
    hA Matrix.PosSemidef.one d F hd' hG'
  have h := congrArg Complex.re (trace_gap174 A B hA.isHermitian hB)
  simp only [Complex.sub_re, real_rat_mul, orderedTraceSum_re] at h
  norm_num at h
  linarith only [h, hgram]

end

end WeightedGram67

open private fourth_trace_le_gram_square fourthWordTraceSum fourthRoot_rpow fourthRoot_four
  exponentialLowerOfRoot from D5.S3.Quantum.Analysis.RefinedBMV67
open private re_trace_sq_le_gram44 from D5.S3.Quantum.Analysis.RefinedBMV44
open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower

noncomputable section

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

set_option maxHeartbeats 1000000 in
-- The power identities in the three cyclic rewrites use noncommutative normalization.
private theorem balanced174_of_root (X B : Mat) (hX : X.IsHermitian) (hB : B.IsHermitian) :
    (trace ((X ^ 17 * B) ^ 4)).re ≤ (trace ((X ^ 20 * B) * (X ^ 16 * B) ^ 3)).re := by
  let M := X ^ 8 * B * X ^ 9
  let Q := X ^ 8 * B * X ^ 16 * B * X ^ 10
  have ht : trace ((X ^ 17 * B) ^ 4) = trace (M ^ 4) := by
    calc
      _ = trace ((X ^ 9 * (X ^ 8 * B)) ^ 4) := congrArg trace (by noncomm_ring)
      _ = _ := trace_cycle_power _ _ _
  have hg : trace ((Mᴴ * M) ^ 2) = trace (Q ^ 2) := by
    simp only [M, Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X * (X ^ 8 * B * X ^ 16 * B * X ^ 9)) ^ 2) :=
        congrArg trace (by noncomm_ring)
      _ = trace (((X ^ 8 * B * X ^ 16 * B * X ^ 9) * X) ^ 2) :=
        trace_cycle_power _ _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have hq : trace (Qᴴ * Q) = trace ((X ^ 20 * B) * (X ^ 16 * B) ^ 3) := by
    simp only [Q, conjTranspose_mul, conjTranspose_pow, hX.eq, hB.eq]
    calc
      _ = trace ((X ^ 10 * B * X ^ 16 * B * X ^ 16 * B * X ^ 16 * B) * X ^ 10) :=
        congrArg trace (by noncomm_ring)
      _ = trace (X ^ 10 * (X ^ 10 * B * X ^ 16 * B * X ^ 16 * B * X ^ 16 * B)) :=
        trace_mul_comm _ _
      _ = _ := congrArg trace (by noncomm_ring)
  have h := fourth_trace_le_gram_square M
  rw [trace_cycle_power M Mᴴ 2, hg] at h
  rw [ht, ← hq]
  exact h.trans (re_trace_sq_le_gram44 Q)

private theorem bound174_root (X B : Mat) (hX : X.PosSemidef) (hB : B.IsHermitian) :
    5985 * (trace ((X ^ 17 * B) ^ 4)).re ≤ fourthWordTraceSum 17 (X ^ 4) B := by
  have h := balanced174_of_root X B hX.isHermitian hB
  have hg := WeightedGram67.balanced_bound174 (X ^ 4) B (hX.pow 4) hB
  rw [← pow_mul X 4 4, ← pow_mul X 4 5] at hg
  exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans hg

/-- The product lower bound at (17,4) in every finite complex dimension. -/
theorem product_bound174 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    5985 * (trace (((A ^ (17 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 17 4).map fun w => (trace (evalWord A B w)).re).sum := by
  have hX : 0 ≤ A ^ (1 / 4 : ℝ) := CFC.rpow_nonneg
  simpa only [fourthRoot_four A hA, fourthRoot_rpow A hA, Nat.cast_ofNat, fourthWordTraceSum]
    using bound174_root (A ^ (1 / 4 : ℝ)) B hX.posSemidef hB

/-- The exponential lower bound at (17,4) in every finite complex dimension. -/
theorem exponential_bound174 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    5985 * (trace (exp ((17 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 17 4).map fun w => (trace (evalWord (exp H) (exp K) w)).re).sum := by
  simpa only [Nat.cast_ofNat, fourthWordTraceSum] using
    exponentialLowerOfRoot 17 5985 H K hH hK
      (fun X B hX hB => bound174_root X B hX hB.isHermitian)

end

end RefinedBMV
