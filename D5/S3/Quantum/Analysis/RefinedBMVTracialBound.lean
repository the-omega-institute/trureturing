/- GID: D5/S3/Quantum/Analysis/RefinedBMVTracialBound
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transmission of the three-factor refined BMV product bound to tracial C*-algebras. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose
import D5.S3.Quantum.Analysis.RefinedBMVTracialMoments
import D5.S3.Quantum.Analysis.RefinedBMVTracialKernel
import D5.S3.Quantum.Analysis.RefinedBMVExtremeAnalytic

/-! Transmission of the three-factor refined BMV product bound to tracial C*-algebras. -/

open Filter
open scoped ComplexOrder Topology

namespace RefinedBMV.Tracial

open DimThree (defect gaps)

/-- A cyclic decomposition into finite PSD centered kernels implies the
unnormalized three-factor composition trace bound. -/
theorem compositionTrace_ge_of_centeredKernel
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (X B : A) (hX : 0 ≤ X) (hB : 0 ≤ B)
    (p : ℕ) (K : ℝ → ℝ → ℝ → ℝ)
    (hD : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      defect p a b c = K a b c + K b c a + K c a b)
    (hK : ∀ (m : ℕ) (x : Fin m → ℝ), (∀ i, 0 ≤ x i) →
      ∀ i, (Matrix.of (fun j k : Fin m => K (x i) (x j) (x k)) :
        Matrix (Fin m) (Fin m) ℝ).PosSemidef) :
    ((gaps p).length : ℂ) * τ ((X ^ p * B) ^ 3) ≤
      ((gaps p).map fun g =>
        τ ((X ^ 3) ^ g.1 * B * (X ^ 3) ^ g.2.1 * B * (X ^ 3) ^ g.2.2 * B)).sum := by
  classical
  let E : Finset ℕ :=
    insert p ((gaps p).flatMap fun g => [3 * g.1, 3 * g.2.1, 3 * g.2.2]).toFinset
  have hpE : p ∈ E := Finset.mem_insert_self _ _
  have hE (g : ℕ × ℕ × ℕ) (hg : g ∈ gaps p) (k : ℕ)
      (hk : k ∈ [3 * g.1, 3 * g.2.1, 3 * g.2.2]) : k ∈ E := by
    apply Finset.mem_insert_of_mem
    exact List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨g, hg, hk⟩)

  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hApprox (n : ℕ) :
      ∃ (m : ℕ) (x : Fin m → ℝ) (P : Fin m → A),
        (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ P i) ∧
          ∀ k ∈ E, ‖moment x P k - X ^ k‖ ≤ ε n := by
    have hεn : 0 < ε n := Nat.one_div_pos_of_nat
    obtain ⟨m, x, P, _, hx, hP, _, hclose⟩ :=
      exists_positive_moment_approximation X hX E (ε n) hεn
    refine ⟨m, x, P, hx, hP, ?_⟩
    intro k hk
    have hMoment : moment x P k = ∑ i : Fin m, (x i ^ k) • P i := by
      unfold moment
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (x i ^ k) (P i)).symm
    rw [hMoment]
    exact hclose k hk
  choose m x P hx hP hclose using hApprox
  let M (n k : ℕ) : A := moment (x n) (P n) k

  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hM (k : ℕ) (hk : k ∈ E) :
      Tendsto (fun n => M n k) atTop (𝓝 (X ^ k)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg (M n k - X ^ k))
      (fun n => hclose n k hk) hε

  have hτc : Continuous (fun a : A => τ a) :=
    τ.toContinuousLinearMap.continuous
  have hBlim : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
  let term (g : ℕ × ℕ × ℕ) (n : ℕ) : ℂ :=
    τ (M n (3 * g.1) * B * M n (3 * g.2.1) * B * M n (3 * g.2.2) * B)
  let termLimit (g : ℕ × ℕ × ℕ) : ℂ :=
    τ ((X ^ 3) ^ g.1 * B * (X ^ 3) ^ g.2.1 * B * (X ^ 3) ^ g.2.2 * B)
  have hterm (g : ℕ × ℕ × ℕ) (hg : g ∈ gaps p) :
      Tendsto (term g) atTop (𝓝 (termLimit g)) := by
    have h₁ := hM (3 * g.1) (hE g hg _ (by simp))
    have h₂ := hM (3 * g.2.1) (hE g hg _ (by simp))
    have h₃ := hM (3 * g.2.2) (hE g hg _ (by simp))
    have hfirst := (h₁.mul hBlim).mul h₂
    have hproduct := ((hfirst.mul hBlim).mul h₃).mul hBlim
    simpa only [term, termLimit, Function.comp_def, pow_mul] using
      (hτc.tendsto _).comp hproduct
  have hsum :
      Tendsto (fun n => ((gaps p).map fun g => term g n).sum) atTop
        (𝓝 (((gaps p).map termLimit).sum)) :=
    tendsto_list_sum (f := term) (a := termLimit) (gaps p) hterm
  have hcube :
      Tendsto (fun n => τ ((M n p * B) ^ 3)) atTop (𝓝 (τ ((X ^ p * B) ^ 3))) :=
    (hτc.tendsto ((X ^ p * B) ^ 3)).comp (((hM p hpE).mul hBlim).pow 3)

  let c : ℂ := ((gaps p).length : ℂ)
  have hcount : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hlim := hsum.sub (hcount.mul hcube)
  have hnonneg (n : ℕ) :
      0 ≤ ((gaps p).map fun g => term g n).sum - c * τ ((M n p * B) ^ 3) := by
    let centered (i : Fin (m n)) : Matrix (Fin (m n)) (Fin (m n)) ℝ :=
      Matrix.of fun j k => K (x n i) (x n j) (x n k)
    refine momentTrace_defect_nonneg τ hτ (P n) B (hP n) hB p (x n) centered ?_ ?_
    · intro i j k
      simpa only [centered, Matrix.of_apply] using
        hD (x n i) (x n j) (x n k) (hx n i) (hx n j) (hx n k)
    · exact hK (m n) (x n) (hx n)

  have hcone : IsClosed (Set.Ici (0 : ℂ)) := isClosed_Ici
  have hnonnegLimit :
      0 ≤ ((gaps p).map termLimit).sum - c * τ ((X ^ p * B) ^ 3) :=
    hcone.mem_of_tendsto hlim (Eventually.of_forall hnonneg)
  exact sub_nonneg.mp hnonnegLimit


open private ExtremeWalk.centered_posSemidef from
  D5.S3.Quantum.Analysis.RefinedBMVExtremeWalk

private theorem weightedKernel_posSemidef {m : ℕ} (a : Fin m → ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) :
    (Matrix.of fun j k => a j * a k * G j k).PosSemidef := by
  classical
  convert hG.mul_mul_conjTranspose_same (Matrix.diagonal a) using 1
  ext j k
  simp only [Matrix.of_apply, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, star_trivial]
  ring

/-- The three-factor product inequality in a tracial C*-algebra,
with the same scalar condition in the large degrees as in the matrix proof. -/
theorem compositionTrace_ge_all
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (X B : A) (hX : 0 ≤ X) (hB : 0 ≤ B)
    (p : ℕ) (hp : 3 ≤ p)
    (hLarge : ∀ q : ℕ, 11 ≤ q → ExtremeWalk.UpperPSD.{0} q) :
    ((gaps p).length : ℂ) * τ ((X ^ p * B) ^ 3) ≤
      ((gaps p).map fun g =>
        τ ((X ^ 3) ^ g.1 * B * (X ^ 3) ^ g.2.1 * B * (X ^ 3) ^ g.2.2 * B)).sum := by
  classical
  have hUpper (q : ℕ) (hq : 5 ≤ q) : ExtremeWalk.UpperPSD.{0} q := by
    by_cases h : 11 ≤ q
    · exact hLarge q h
    have hq' : q ≤ 10 := by omega
    interval_cases q
    · exact Extreme.upperPSD_five
    · exact Extreme.upperPSD_six
    · exact Extreme.upperPSD_seven
    · exact Extreme.upperPSD_eight
    · exact Extreme.upperPSD_nine
    · exact Extreme.upperPSD_ten
  by_cases h : 5 ≤ p
  · apply compositionTrace_ge_of_centeredKernel τ hτ X B hX hB p
      (ExtremeWalk.centeredKernel p)
    · exact ExtremeWalk.defect_eq_cyclic_all p
    · intro m x hx i
      exact ExtremeWalk.centered_posSemidef (hUpper p h) (x i) (hx i) x
  have hp' : p ≤ 4 := by omega
  interval_cases p
  · apply compositionTrace_ge_of_centeredKernel τ hτ X B hX hB 3
      (fun x y z => (y ^ 3 - x ^ 3) * (z ^ 3 - x ^ 3) *
        symmetricKernel (x ^ 3) (y ^ 3) (z ^ 3))
    · intro x y z _ _ _
      have hGaps : gaps 3 = [(0,0,3), (0,1,2), (0,2,1), (0,3,0),
          (1,0,2), (1,1,1), (1,2,0), (2,0,1), (2,1,0), (3,0,0)] := rfl
      have he : defect 3 x y z = cubicDefect (x ^ 3) (y ^ 3) (z ^ 3) := by
        norm_num [defect, hGaps, cubicDefect]
        ring
      rw [he]
      exact cubicDefect_eq_cyclic_symmetric (x ^ 3) (y ^ 3) (z ^ 3)
    · intro m x hx i
      exact weightedKernel_posSemidef (fun j => x j ^ 3 - x i ^ 3) _
        (symmetricKernel_psd (x i ^ 3) (pow_nonneg (hx i) _)
          (fun j => x j ^ 3) (fun j => pow_nonneg (hx j) _))
  · apply compositionTrace_ge_of_centeredKernel τ hτ X B hX hB 4
      (fun x y z => (x - y) * (x - z) * centeredKernel43 x y z)
    · intro x y z hx hy hz
      have hGaps : gaps 4 = [(0,0,4), (0,1,3), (0,2,2), (0,3,1), (0,4,0),
          (1,0,3), (1,1,2), (1,2,1), (1,3,0), (2,0,2), (2,1,1),
          (2,2,0), (3,0,1), (3,1,0), (4,0,0)] := rfl
      have he : defect 4 x y z = defect43 x y z := by
        norm_num [defect, hGaps, defect43, gaps43, gapOrbits43]
        ring
      rw [he]
      exact defect43_eq_cyclic x y z hx hy hz
    · intro m x hx i
      exact weightedKernel_posSemidef (fun j => x i - x j) _
        (centeredKernel43_psd (x i) (hx i) x hx)


/-- The normalized three-factor product comparison in a tracial C*-algebra. -/
theorem productTrace_ge_all
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : ℕ) (hp : 3 ≤ p)
    (hLarge : ∀ q : ℕ, 11 ≤ q → ExtremeWalk.UpperPSD.{0} q) :
    τ (((a ^ ((p : ℝ) / 3)) * b) ^ 3) ≤
      ((gaps p).map fun g => τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)).sum /
        ((gaps p).length : ℂ) := by
  let X := a ^ (1 / 3 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = a ^ ((1 / 3 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg a (1 / 3) k (by norm_num) (by positivity) ha
  have hX3 : X ^ (3 : ℕ) = a := by
    rw [hpow, show ((1 / 3 : ℝ) * (↑(3 : ℕ) : ℝ)) = 1 by norm_num,
      CFC.rpow_one a ha]
  have hXp : X ^ p = a ^ ((p : ℝ) / 3) := by
    rw [hpow]
    congr 1
    ring
  have hCount : (0 : ℂ) < ((gaps p).length : ℂ) := by
    exact_mod_cast (DimThree.word_counts_all p).2.1
  apply (le_div_iff₀' hCount).mpr
  simpa only [hX3, hXp] using compositionTrace_ge_all τ hτ X b hX hb p hp hLarge


open private DimThree.sum_words_cyclic DimThree.runBeforeB DimThree.nextGap from
  D5.S3.Quantum.Analysis.RefinedBMVUniformWords

/-- The normalized composition trace is the mean over all ordered words. -/
theorem productTrace_ge_wordMean
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : ℕ) (hp : 3 ≤ p)
    (hLarge : ∀ q : ℕ, 11 ≤ q → ExtremeWalk.UpperPSD.{0} q) :
    τ (((a ^ ((p : ℝ) / 3)) * b) ^ 3) ≤
      ((balancedWords p 3).map fun w =>
        τ ((w.map fun letter => if letter then a else b).prod)).sum /
        ((balancedWords p 3).length : ℂ) := by
  let v (w : List Bool) : ℂ := τ ((w.map fun letter => if letter then a else b).prod)
  let F (g : ℕ × ℕ × ℕ) : ℂ := τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)
  have hCut (i j k l : ℕ) :
      v (DimThree.runBeforeB i (DimThree.runBeforeB j (DimThree.runBeforeB k
        (List.replicate l true)))) = F (j, k, l + i) := by
    simpa only [v, F, DimThree.runBeforeB, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, Bool.false_eq_true, if_false, if_true,
      List.prod_append, List.prod_replicate, List.prod_cons, List.prod_nil,
      mul_one, pow_add, mul_assoc] using
        hτ (a ^ i * b) (a ^ j * b * a ^ k * b * a ^ l)
  have hCycle (g : ℕ × ℕ × ℕ) : F (DimThree.nextGap g) = F g := by
    simpa only [F, DimThree.nextGap, mul_assoc] using
      hτ (a ^ g.2.1 * b * a ^ g.2.2 * b) (a ^ g.1 * b)
  have hSums := DimThree.sum_words_cyclic p v F hCut hCycle
  obtain ⟨hw, hg, hc⟩ := DimThree.word_counts_all p
  have hCast : 3 * ((balancedWords p 3).length : ℂ) =
      (p + 3 : ℂ) * ((gaps p).length : ℂ) := by exact_mod_cast hc
  have hAvg : ((balancedWords p 3).map v).sum / ((balancedWords p 3).length : ℂ) =
      ((gaps p).map F).sum / ((gaps p).length : ℂ) := by
    apply (div_eq_div_iff (by exact_mod_cast hw.ne') (by exact_mod_cast hg.ne')).2
    linear_combination (((gaps p).length : ℂ) / 3) * hSums -
      (((gaps p).map F).sum / 3) * hCast
  change _ ≤ ((balancedWords p 3).map v).sum / ((balancedWords p 3).length : ℂ)
  rw [hAvg]
  exact productTrace_ge_all τ hτ a b ha hb p hp hLarge

#print axioms productTrace_ge_wordMean

#print axioms productTrace_ge_all

#print axioms compositionTrace_ge_all

end RefinedBMV.Tracial
