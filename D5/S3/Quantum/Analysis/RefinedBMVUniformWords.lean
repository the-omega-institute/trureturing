/- GID: D5/S3/Quantum/Analysis/RefinedBMVUniformWords
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cyclic three-gap trace expansion at every first degree. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThree
import D5.S3.Quantum.Analysis.RefinedBMVUniformCorner
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Research candidate for the three-B word mean at arbitrary first degree.
The first A-run is removed at each B. After the third B, cyclicity merges
the surviving A-run with the first one. -/

open Matrix
open scoped BigOperators

noncomputable section

namespace RefinedBMV.DimThree

private abbrev GapTriple := ℕ × ℕ × ℕ

private def nextGap (g : GapTriple) : GapTriple := (g.2.1, g.2.2, g.1)

private def runBeforeB (i : ℕ) (w : List Bool) : List Bool :=
  (List.replicate i true ++ [false]) ++ w

/-- The remaining first degree increases, so the initial run lengths occur in descending order. -/
theorem balancedWords_firstRun (p b : ℕ) :
    balancedWords p (b + 1) =
      (List.range (p + 1)).flatMap fun r =>
        (balancedWords r b).map (runBeforeB (p - r)) := by
  induction p with
  | zero => simp [balancedWords, runBeforeB]
  | succ p ih =>
    rw [balancedWords, ih, List.range_succ (n := p + 1), List.flatMap_append,
      List.map_flatMap]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.sub_self,
      List.map_map]
    congr 1
    apply List.flatMap_congr
    intro r hr
    have hr' := List.mem_range.mp hr
    have hs : p + 1 - r = (p - r) + 1 := by omega
    rw [hs]
    rfl

private theorem balancedWords_zeroB (p : ℕ) :
    balancedWords p 0 = [List.replicate p true] := by
  induction p with
  | zero => simp [balancedWords]
  | succ p ih => simp [balancedWords, ih, List.replicate_succ]

private theorem sum_flatMap_values {α β M : Type*} [AddMonoid M]
    (l : List α) (f : α → List β) (v : β → M) :
    ((l.flatMap f).map v).sum = (l.map fun a => ((f a).map v).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem sum_list_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

private theorem sum_balancedWords_firstRun (p b : ℕ) (v : List Bool → ℂ) :
    ((balancedWords p (b + 1)).map v).sum =
      ∑ i ∈ Finset.range (p + 1), ((balancedWords (p - i) b).map (v ∘ runBeforeB i)).sum := by
  rw [balancedWords_firstRun, sum_flatMap_values, sum_list_range]
  simp only [List.map_map]
  conv_rhs =>
    rw [← Finset.sum_flip (n := p)
      (fun i => ((balancedWords (p - i) b).map (v ∘ runBeforeB i)).sum)]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  have h : p - (p - r) = r := by omega
  rw [h]

private theorem gaps_cycle_next (p : ℕ) : ((gaps p).map nextGap).Perm (gaps p) :=
  gaps_cycle_all p

private theorem sum_gaps (p : ℕ) (f : GapTriple → ℂ) :
    ((gaps p).map f).sum =
      ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1), f (j, k, p - j - k) := by
  rw [gaps, sum_flatMap_values, sum_list_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have h : p + 1 - j = p - j + 1 := by omega
  simp only [List.map_map, Function.comp_apply, sum_list_range, h]

/-- After the outer runs are merged, their possible splits contribute
the last gap length plus one. -/
private theorem sum_words_weighted (p : ℕ) (v : List Bool → ℂ) (F : GapTriple → ℂ)
    (hcut : ∀ i j k l, v (runBeforeB i (runBeforeB j (runBeforeB k
      (List.replicate l true)))) = F (j, k, l + i)) :
    ((balancedWords p 3).map v).sum =
      ((gaps p).map fun g => (g.2.2 + 1 : ℂ) * F g).sum := by
  rw [sum_gaps]
  calc
    _ = ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p - i + 1),
          ∑ k ∈ Finset.range (p - i - j + 1), F (j, k, p - j - k) := by
      rw [sum_balancedWords_firstRun (b := 2)]
      simp_rw [sum_balancedWords_firstRun (b := 1), sum_balancedWords_firstRun (b := 0),
        balancedWords_zeroB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Function.comp_apply, hcut]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
        Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hi hj hk
      rw [show p - i - j - k + i = p - j - k by omega]
    _ = ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (p - j + 1),
          ∑ k ∈ Finset.range (p - i - j + 1), F (j, k, p - j - k) := by
      apply Finset.sum_comm'
      intro i j
      simp only [Finset.mem_range]
      omega
    _ = ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
          ∑ i ∈ Finset.range (p - j - k + 1), F (j, k, p - j - k) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      apply Finset.sum_comm'
      intro i k
      simp only [Finset.mem_range] at hj ⊢
      omega
    _ = _ := by simp [nsmul_eq_mul]

/-- The three cyclic weights add up to the word length. This also applies to
the constant-one function, which counts the words. -/
private theorem sum_words_cyclic (p : ℕ) (v : List Bool → ℂ) (F : GapTriple → ℂ)
    (hcut : ∀ i j k l, v (runBeforeB i (runBeforeB j (runBeforeB k
      (List.replicate l true)))) = F (j, k, l + i))
    (hcycle : ∀ g, F (nextGap g) = F g) :
    3 * ((balancedWords p 3).map v).sum = (p + 3 : ℂ) * ((gaps p).map F).sum := by
  let w₁ (g : GapTriple) := (g.1 + 1 : ℂ) * F g
  let w₂ (g : GapTriple) := (g.2.1 + 1 : ℂ) * F g
  let w₃ (g : GapTriple) := (g.2.2 + 1 : ℂ) * F g
  have h₁ : w₃ ∘ nextGap = w₁ := by
    funext g
    change (g.1 + 1 : ℂ) * F (nextGap g) = (g.1 + 1 : ℂ) * F g
    rw [hcycle]
  have h₂ : w₁ ∘ nextGap = w₂ := by
    funext g
    change (g.2.1 + 1 : ℂ) * F (nextGap g) = (g.2.1 + 1 : ℂ) * F g
    rw [hcycle]
  have e₁ : ((gaps p).map w₁).sum = ((gaps p).map w₃).sum := by
    rw [← h₁, ← List.map_map]
    exact ((gaps_cycle_next p).map w₃).sum_eq
  have e₂ : ((gaps p).map w₂).sum = ((gaps p).map w₁).sum := by
    rw [← h₂, ← List.map_map]
    exact ((gaps_cycle_next p).map w₁).sum_eq
  rw [sum_words_weighted p v F hcut]
  change 3 * ((gaps p).map w₃).sum = _
  calc
    _ = ((gaps p).map w₁).sum + ((gaps p).map w₂).sum + ((gaps p).map w₃).sum := by
      rw [e₂, e₁]
      ring
    _ = ((gaps p).map fun g => (p + 3 : ℂ) * F g).sum := by
      rw [← List.sum_map_add, ← List.sum_map_add]
      apply congrArg List.sum
      refine List.map_congr_left fun g hg => ?_
      have htotal := (mem_gaps_iff_total p g).mp hg
      have hcast : (g.1 : ℂ) + g.2.1 + g.2.2 = (p : ℂ) := by exact_mod_cast htotal
      dsimp only [w₁, w₂, w₃]
      linear_combination F g * hcast
    _ = _ := List.sum_map_mul_left ..

theorem word_counts_all (p : ℕ) :
    0 < (balancedWords p 3).length ∧ 0 < (gaps p).length ∧
      3 * (balancedWords p 3).length = (p + 3) * (gaps p).length := by
  have h := sum_words_cyclic p (fun _ => 1) (fun _ => 1) (fun _ _ _ _ => rfl) (fun _ => rfl)
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at h
  have hc : 3 * (balancedWords p 3).length = (p + 3) * (gaps p).length := by
    exact_mod_cast h
  have hg : 0 < (gaps p).length := by
    apply List.length_pos_iff_exists_mem.mpr
    exact ⟨(p, 0, 0), (mem_gaps_iff_total p _).mpr (by simp)⟩
  have hp : 0 < (p + 3) * (gaps p).length := Nat.mul_pos (by omega) hg
  have hw : 0 < (balancedWords p 3).length := by
    by_contra hh
    have hz : (balancedWords p 3).length = 0 := by omega
    rw [hz, mul_zero] at hc
    omega
  exact ⟨hw, hg, hc⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem trace_merge_runs (A B : Matrix n n ℂ) (i j k l : ℕ) :
    trace (evalWord A B (runBeforeB i (runBeforeB j (runBeforeB k
      (List.replicate l true))))) = traceGaps43 A B (j, k, l + i) := by
  let u := List.replicate i true ++ [false]
  let v := runBeforeB j (runBeforeB k (List.replicate l true))
  have h := evalWord_rotate_trace43 A B (u ++ v) u.length
  rw [List.rotate_append_length_eq] at h
  have hv : v ++ u = gapWord43 (j, k, l + i) := by
    have hm : List.replicate l true ++ (List.replicate i true ++ [false]) =
        List.replicate (l + i) true ++ [false] := by
      rw [← List.append_assoc, List.replicate_append_replicate]
    simp only [u, v, runBeforeB, gapWord43, List.append_assoc, hm]
  rw [hv, evalWord_gap_trace43] at h
  exact h.symm

/-- The ordered word mean agrees with the mean over three gaps for every first degree. -/
theorem wordMean_eq_gaps_all (p : ℕ) (A B : Matrix n n ℂ) :
    wordMean p A B = ((gaps p).map (traceGaps43 A B)).sum / (gaps p).length := by
  have hcycle (g : GapTriple) : traceGaps43 A B (nextGap g) = traceGaps43 A B g := by
    simpa only [nextGap, traceGaps43, mul_assoc] using
      trace_mul_comm (A ^ g.2.1 * (B * (A ^ g.2.2 * B))) (A ^ g.1 * B)
  have h := sum_words_cyclic p (fun w => trace (evalWord A B w)) (traceGaps43 A B)
    (trace_merge_runs A B) hcycle
  obtain ⟨hw, hg, hc⟩ := word_counts_all p
  have hcast : 3 * ((balancedWords p 3).length : ℂ) =
      (p + 3 : ℂ) * ((gaps p).length : ℂ) := by exact_mod_cast hc
  unfold wordMean
  apply (div_eq_div_iff (by exact_mod_cast hw.ne') (by exact_mod_cast hg.ne')).2
  linear_combination (((gaps p).length : ℂ) / 3) * h -
    ((List.map (traceGaps43 A B) (gaps p)).sum / 3) * hcast

/-- The existing trace-to-walk identity with the first degree unrestricted. -/
theorem trace_gap_all (p : ℕ) (a : n → ℝ) (B : Matrix n n ℂ) :
    ((gaps p).length : ℂ) *
      (wordMean p ((diagonal fun i => (a i : ℂ)) ^ 3) B -
        trace (((diagonal fun i => (a i : ℂ)) ^ p * B) ^ 3)) =
      walk B (fun i j k => ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) := by
  let d : n → ℂ := fun i => a i
  let f (g : GapTriple) (i j k : n) : ℂ :=
    (d i ^ 3) ^ g.1 * (d j ^ 3) ^ g.2.1 * (d k ^ 3) ^ g.2.2
  have htrace : traceGaps43 ((diagonal d) ^ 3) B = fun g => walk B (f g) := by
    funext g
    simpa only [traceGaps43, f, pow_mul, mul_assoc] using
      trace_pow_walk B d (3 * g.1) (3 * g.2.1) (3 * g.2.2)
  have hcube : trace (((diagonal d) ^ p * B) ^ 3) =
      walk B (fun i j k => d i ^ p * d j ^ p * d k ^ p) := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using trace_pow_walk B d p p p
  have hlen : ((gaps p).length : ℂ) ≠ 0 := by
    exact_mod_cast (word_counts_all p).2.1.ne'
  change ((gaps p).length : ℂ) *
    (wordMean p ((diagonal d) ^ 3) B - trace (((diagonal d) ^ p * B) ^ 3)) = _
  rw [mul_sub, wordMean_eq_gaps_all, mul_div_cancel₀ _ hlen, htrace, sum_walk43 B, hcube]
  change walk B _ - ((gaps p).length : ℂ) • walk B _ = _
  rw [← map_smul, ← map_sub]
  congr 1
  funext i j k
  change _ = Complex.ofRealHom (defect p (a i) (a j) (a k))
  simp only [defect, map_sub, map_list_sum, map_pow, map_mul, map_natCast, List.map_map,
    Function.comp_def, Complex.ofRealHom_eq_coe, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    f, d, mul_pow]

end RefinedBMV.DimThree
