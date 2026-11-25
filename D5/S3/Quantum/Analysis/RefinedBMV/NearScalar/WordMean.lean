/- GID: D5/S3/Quantum/Analysis/RefinedBMV/NearScalar/WordMean
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/NearScalar/WordMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension-free quantitative refined BMV comparison for four copies near a scalar. -/

import D5.S3.Quantum.Analysis.RefinedBMVUniformWords
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Product
import Batteries.Tactic.OpenPrivate

/-! The uniform four-gap composition mean equals the mean over the ordered words. -/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

namespace D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordMean

open RefinedBMV (balancedWords evalWord)
open RefinedBMV.DimThree (balancedWords_firstRun)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarTaylor (orderedProd)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarQuadratic (compositionMean)

open private runBeforeB balancedWords_zeroB sum_flatMap_values sum_list_range from
  D5.S3.Quantum.Analysis.RefinedBMVUniformWords
open private evalWord_block43 from D5.S3.Quantum.Analysis.RefinedBMV43
open private orderedProd_four from D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Quadratic

private theorem sum_balancedWords_firstRun_real (p b : ℕ) (v : List Bool → ℝ) :
    ((balancedWords p (b + 1)).map v).sum =
      ∑ i ∈ Finset.range (p + 1),
        ((balancedWords (p - i) b).map (v ∘ runBeforeB i)).sum := by
  rw [balancedWords_firstRun, sum_flatMap_values, sum_list_range]
  simp only [List.map_map]
  conv_rhs =>
    rw [← Finset.sum_flip (n := p)
      (fun i => ((balancedWords (p - i) b).map (v ∘ runBeforeB i)).sum)]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  rw [show p - (p - r) = r by omega]

private theorem sum_tuple_list (k p : ℕ) (f : (Fin k → ℕ) → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple k p, f r) =
      ((List.Nat.antidiagonalTuple k p).map f).sum := by
  rw [Finset.sum_eq_multiset_sum]
  change (Multiset.map f (↑(List.Nat.antidiagonalTuple k p) : Multiset _)).sum = _
  rw [Multiset.map_coe, Multiset.sum_coe]

private theorem sum_tuple_succ (k p : ℕ) (f : (Fin (k + 1) → ℕ) → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple (k + 1) p, f r) =
      ∑ i ∈ Finset.range (p + 1),
        ∑ r ∈ Finset.Nat.antidiagonalTuple k (p - i), f (Fin.cons i r) := by
  simp only [sum_tuple_list, List.Nat.antidiagonalTuple, sum_flatMap_values,
    List.Nat.antidiagonal, List.map_map, Function.comp_def, sum_list_range]

private theorem sum_tuple_four (p : ℕ) (f : (Fin 4 → ℕ) → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, f r) =
      ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
        ∑ l ∈ Finset.range (p - j - k + 1), f ![j, k, l, p - j - k - l] := by
  simp only [sum_tuple_succ 3, sum_tuple_succ 2, sum_tuple_succ 1,
    Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton] <;> rfl

/-- Merging the initial and terminal A-runs gives a weight equal to the
number of ways to split the last gap. -/
private theorem sum_words_weighted (p : ℕ) (v : List Bool → ℝ) (F : (Fin 4 → ℕ) → ℝ)
    (hcut : ∀ i j k l m, v (runBeforeB i (runBeforeB j (runBeforeB k (runBeforeB l
      (List.replicate m true))))) = F ![j, k, l, m + i]) :
    ((balancedWords p 4).map v).sum =
      ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, ((r 3 : ℝ) + 1) * F r := by
  rw [sum_tuple_four]
  calc
    _ = ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (p - i + 1),
          ∑ k ∈ Finset.range (p - i - j + 1),
            ∑ l ∈ Finset.range (p - i - j - k + 1), F ![j, k, l, p - j - k - l] := by
      rw [sum_balancedWords_firstRun_real (b := 3)]
      simp_rw [sum_balancedWords_firstRun_real (b := 2),
        sum_balancedWords_firstRun_real (b := 1), sum_balancedWords_firstRun_real (b := 0),
        balancedWords_zeroB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Function.comp_apply, hcut]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
        Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
      simp only [Finset.mem_range] at hi hj hk hl
      rw [show p - i - j - k - l + i = p - j - k - l by omega]
    _ = ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (p - j + 1),
          ∑ k ∈ Finset.range (p - i - j + 1),
            ∑ l ∈ Finset.range (p - i - j - k + 1), F ![j, k, l, p - j - k - l] := by
      apply Finset.sum_comm'
      intro i j
      simp only [Finset.mem_range]
      omega
    _ = ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
          ∑ i ∈ Finset.range (p - j - k + 1),
            ∑ l ∈ Finset.range (p - i - j - k + 1), F ![j, k, l, p - j - k - l] := by
      refine Finset.sum_congr rfl fun j hj => ?_
      apply Finset.sum_comm'
      intro i k
      simp only [Finset.mem_range] at hj ⊢
      omega
    _ = ∑ j ∈ Finset.range (p + 1), ∑ k ∈ Finset.range (p - j + 1),
          ∑ l ∈ Finset.range (p - j - k + 1),
            ∑ i ∈ Finset.range (p - j - k - l + 1), F ![j, k, l, p - j - k - l] := by
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
      apply Finset.sum_comm'
      intro i l
      simp only [Finset.mem_range] at hj hk ⊢
      omega
    _ = _ := by
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk =>
        Finset.sum_congr rfl fun l hl => ?_
      change (∑ _ ∈ Finset.range (p - j - k - l + 1), F ![j, k, l, p - j - k - l]) =
        (((p - j - k - l : ℕ) : ℝ) + 1) * F ![j, k, l, p - j - k - l]
      simp [nsmul_eq_mul]

private def nextGap (r : Fin 4 → ℕ) : Fin 4 → ℕ := ![r 1, r 2, r 3, r 0]

private def prevGap (r : Fin 4 → ℕ) : Fin 4 → ℕ := ![r 3, r 0, r 1, r 2]

private theorem sum_nextGap (p : ℕ) (F : (Fin 4 → ℕ) → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, F (nextGap r)) =
      ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, F r := by
  refine Finset.sum_nbij' nextGap prevGap ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro r hr
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_four] at hr ⊢
    change r 1 + r 2 + r 3 + r 0 = p
    omega
  · intro r hr
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_four] at hr ⊢
    change r 3 + r 0 + r 1 + r 2 = p
    omega
  · intro r hr
    funext i
    fin_cases i <;> rfl
  · intro r hr
    funext i
    fin_cases i <;> rfl

/-- Averaging the four cyclic choices of the distinguished B gives the
constant weight p + 4. This identity also applies to the constant function 1. -/
private theorem sum_words_cyclic (p : ℕ) (v : List Bool → ℝ) (F : (Fin 4 → ℕ) → ℝ)
    (hcut : ∀ i j k l m, v (runBeforeB i (runBeforeB j (runBeforeB k (runBeforeB l
      (List.replicate m true))))) = F ![j, k, l, m + i])
    (hcycle : ∀ r, F (nextGap r) = F r) :
    4 * ((balancedWords p 4).map v).sum =
      ((p : ℝ) + 4) * ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, F r := by
  let w₀ (r : Fin 4 → ℕ) := ((r 0 : ℝ) + 1) * F r
  let w₁ (r : Fin 4 → ℕ) := ((r 1 : ℝ) + 1) * F r
  let w₂ (r : Fin 4 → ℕ) := ((r 2 : ℝ) + 1) * F r
  let w₃ (r : Fin 4 → ℕ) := ((r 3 : ℝ) + 1) * F r
  have h₀ : (fun r => w₃ (nextGap r)) = w₀ := by
    funext r
    change ((r 0 : ℝ) + 1) * F (nextGap r) = ((r 0 : ℝ) + 1) * F r
    rw [hcycle]
  have h₁ : (fun r => w₀ (nextGap r)) = w₁ := by
    funext r
    change ((r 1 : ℝ) + 1) * F (nextGap r) = ((r 1 : ℝ) + 1) * F r
    rw [hcycle]
  have h₂ : (fun r => w₁ (nextGap r)) = w₂ := by
    funext r
    change ((r 2 : ℝ) + 1) * F (nextGap r) = ((r 2 : ℝ) + 1) * F r
    rw [hcycle]
  have e₀ := sum_nextGap p w₃
  have e₁ := sum_nextGap p w₀
  have e₂ := sum_nextGap p w₁
  rw [h₀] at e₀
  rw [h₁] at e₁
  rw [h₂] at e₂
  rw [sum_words_weighted p v F hcut]
  change 4 * (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, w₃ r) = _
  calc
    _ = (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, w₀ r) +
        (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, w₁ r) +
        (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, w₂ r) +
        (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, w₃ r) := by
      rw [e₂, e₁, e₀]
      ring
    _ = ∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, ((p : ℝ) + 4) * F r := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      have htotal := Finset.Nat.mem_antidiagonalTuple.mp hr
      rw [Fin.sum_univ_four] at htotal
      have hcast : (r 0 : ℝ) + r 1 + r 2 + r 3 = (p : ℝ) := by exact_mod_cast htotal
      dsimp only [w₀, w₁, w₂, w₃]
      linear_combination F r * hcast
    _ = _ := by rw [Finset.mul_sum]

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem evalWord_runBeforeB (A B : Matrix n n ℂ) (i : ℕ) (w : List Bool) :
    evalWord A B (runBeforeB i w) = (A ^ i * B) * evalWord A B w := by
  rw [runBeforeB, List.append_assoc, evalWord_block43]
  simp [evalWord, mul_assoc]

private theorem trace_merge_runs (A B : Matrix n n ℂ) (i j k l m : ℕ) :
    (trace (evalWord A B (runBeforeB i (runBeforeB j (runBeforeB k (runBeforeB l
      (List.replicate m true))))))).re =
      (trace (orderedProd fun t : Fin 4 => A ^ (![j, k, l, m + i] t) * B)).re := by
  have hm : evalWord A B (List.replicate m true) = A ^ m := by
    simpa only [List.append_nil, evalWord, mul_one] using evalWord_block43 A B m []
  simp only [evalWord_runBeforeB, hm, orderedProd_four]
  change (trace ((A ^ i * B) * ((A ^ j * B) * ((A ^ k * B) * ((A ^ l * B) * A ^ m))))).re =
    (trace ((A ^ j * B) * (A ^ k * B) * (A ^ l * B) * (A ^ (m + i) * B))).re
  simpa only [pow_add, mul_assoc] using congrArg Complex.re
    (trace_mul_comm (A ^ i * B) ((A ^ j * B) * ((A ^ k * B) * ((A ^ l * B) * A ^ m))))

private theorem trace_nextGap (A B : Matrix n n ℂ) (r : Fin 4 → ℕ) :
    (trace (orderedProd fun t => A ^ (nextGap r t) * B)).re =
      (trace (orderedProd fun t => A ^ (r t) * B)).re := by
  simp only [orderedProd_four]
  change (trace ((A ^ r 1 * B) * (A ^ r 2 * B) * (A ^ r 3 * B) * (A ^ r 0 * B))).re =
    (trace ((A ^ r 0 * B) * (A ^ r 1 * B) * (A ^ r 2 * B) * (A ^ r 3 * B))).re
  simpa only [mul_assoc] using congrArg Complex.re
    (trace_mul_comm ((A ^ r 1 * B) * (A ^ r 2 * B) * (A ^ r 3 * B)) (A ^ r 0 * B))

/-- The actual balanced-word mean of the real traces agrees with the uniform
four-part composition mean, for every first degree and every finite matrix pair. -/
theorem wordMean_eq_compositionMean (p : ℕ) (A B : Matrix n n ℂ) :
    ((balancedWords p 4).map fun w => (trace (evalWord A B w)).re).sum /
        ((balancedWords p 4).length : ℝ) =
      compositionMean p (fun r => (trace (orderedProd fun t => A ^ r t * B)).re) := by
  let v (w : List Bool) := (trace (evalWord A B w)).re
  let F (r : Fin 4 → ℕ) := (trace (orderedProd fun t => A ^ r t * B)).re
  have h := sum_words_cyclic p v F (trace_merge_runs A B) (trace_nextGap A B)
  have hc := sum_words_cyclic p (fun _ => 1) (fun _ => 1)
    (fun _ _ _ _ _ => rfl) (fun _ => rfl)
  simp only [List.map_const', List.sum_replicate, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hg : 0 < (Finset.Nat.antidiagonalTuple 4 p).card := by
    apply Finset.card_pos.mpr
    refine ⟨![p, 0, 0, 0], Finset.Nat.mem_antidiagonalTuple.mpr ?_⟩
    rw [Fin.sum_univ_four]
    change p + 0 + 0 + 0 = p
    omega
  have hg' : ((Finset.Nat.antidiagonalTuple 4 p).card : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hw : ((balancedWords p 4).length : ℝ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hc
    exact (mul_ne_zero (by positivity) hg') hc.symm
  change ((balancedWords p 4).map v).sum / ((balancedWords p 4).length : ℝ) =
    (∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, F r) / ((Finset.Nat.antidiagonalTuple 4 p).card : ℝ)
  apply (div_eq_div_iff hw hg').2
  linear_combination (((Finset.Nat.antidiagonalTuple 4 p).card : ℝ) / 4) * h -
    ((∑ r ∈ Finset.Nat.antidiagonalTuple 4 p, F r) / 4) * hc


open scoped Matrix.Norms.L2Operator MatrixOrder in
private theorem exp_smul_eq_rpow (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    NormedSpace.exp (t • H) = (NormedSpace.exp H) ^ t := by
  let : NormedAlgebra ℝ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℝ ℂ (Matrix n n ℂ)
  have hself := hH.isSelfAdjoint
  have hscaled := (IsSelfAdjoint.all t).smul hself
  calc
    _ = cfc Real.exp (t • H) := (CFC.real_exp_eq_normedSpace_exp hscaled).symm
    _ = cfc (fun x : ℝ => Real.exp (t * x)) H :=
      (cfc_comp_const_mul t Real.exp H Real.continuous_exp.continuousOn hself).symm
    _ = cfc (fun x : ℝ => Real.exp x ^ t) H := by
      congr 1
      funext x
      simpa only [mul_comm t x] using Real.exp_mul x t
    _ = _ := by
      rw [← CFC.cfc_rpow (fun x _ => Real.exp_pos x) Real.continuous_exp.continuousOn hself,
        CFC.real_exp_eq_normedSpace_exp hself]

open scoped MatrixOrder Matrix.Norms.Frobenius in
/-- A quantitative four-copy refined BMV lower bound in a dimension-free
neighborhood of the scalar matrix, expressed with the actual ordered words. -/
theorem wordMean_sub_balanced_ge (p : ℕ) (H B : Matrix n n ℂ)
    (hH : H.IsHermitian) (hB : B.PosSemidef)
    (hx : (p : ℝ) * ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ ≤ 1 / 100000) :
    (p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2 / 25 ≤
      ((balancedWords p 4).map
        (fun w => (trace (evalWord (NormedSpace.exp H) B w)).re)).sum /
        ((balancedWords p 4).length : ℝ) -
      (trace (((NormedSpace.exp H) ^ ((p : ℝ) / 4) * B) ^ 4)).re := by
  rw [wordMean_eq_compositionMean]
  have hconstant (X : Matrix n n ℂ) : orderedProd (fun _ : Fin 4 => X) = X ^ 4 := by
    rw [orderedProd_four]
    simp only [pow_succ, pow_zero, one_mul]
  simpa only [RefinedBMVNearScalarProduct.exp_natCast_smul,
    exp_smul_eq_rpow H hH ((p : ℝ) / 4), hconstant] using
    RefinedBMVNearScalarProduct.compositionMean_sub_balanced_ge p H B hH hB hx

end D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordMean
