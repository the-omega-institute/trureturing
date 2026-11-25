/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/Bound
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/Tracial/Bound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV product bound and a quantitative degree-three gap for finite traces. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Moments
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.Kernel
import D5.S3.Quantum.Analysis.RefinedBMVExtremeAnalytic

/-! Transmission of the three-factor refined BMV product bound to tracial C*-algebras. -/

open Filter
open scoped BigOperators ComplexOrder Topology

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

private noncomputable def cubicFeature (x y : ℝ) : ℝ :=
  Real.sqrt x * ((x - y) * ((x + 3 * y) / (x + y)))

private theorem cubicFeature_pair (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * cubicFeature x y + Real.sqrt y * cubicFeature y x = (x - y) ^ 2 := by
  unfold cubicFeature
  rw [← mul_assoc, ← mul_assoc (Real.sqrt y), Real.mul_self_sqrt hx, Real.mul_self_sqrt hy]
  by_cases h : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · rw [add_comm y x]
    field_simp [h]
    <;> ring

private theorem cubicGaps :
    gaps 3 = [(0,0,3), (0,1,2), (0,2,1), (0,3,0), (1,0,2), (1,1,1),
      (1,2,0), (2,0,1), (2,1,0), (3,0,0)] := rfl

open private weighted_cauchy_psd from D5.S3.Quantum.Analysis.RefinedBMVKernel

private theorem cubicFeature_remainder_psd {m : ℕ} (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i)
    (c : ℝ) (hc : 0 ≤ c) :
    (Matrix.of fun j k => (c - x j) * (c - x k) * symmetricKernel c (x j) (x k) -
      cubicFeature c (x j) * cubicFeature c (x k)).PosSemidef := by
  classical
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [cubicFeature, Real.sqrt_zero, zero_mul, sub_zero, Matrix.of_apply] using
      weightedKernel_posSemidef (fun j => 0 - x j) _ (symmetricKernel_psd 0 le_rfl x hx)
  · let w (j : Fin m) : ℝ := x j ^ 2 / (c + x j)
    have hw (j : Fin m) (hj : x j = 0) : w j = 0 := by simp [w, hj]
    have hCauchy := (weighted_cauchy_psd x w hx hw).smul (show (0 : ℝ) ≤ 8 by norm_num)
    convert weightedKernel_posSemidef (fun j => c - x j) _ hCauchy using 1
    ext j k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [symmetricKernel_pos c (x j) (x k) hc (hx j) (hx k)]
    have hRank :
        cubicFeature c (x j) * cubicFeature c (x k) =
          (c - x j) * (c - x k) * (c * ((c + 3 * x j) / (c + x j)) *
            ((c + 3 * x k) / (c + x k))) := by
      unfold cubicFeature
      linear_combination ((c - x j) * (c - x k) * ((c + 3 * x j) / (c + x j)) *
        ((c + 3 * x k) / (c + x k))) * Real.mul_self_sqrt hc.le
    simp only [hRank, w, div_eq_mul_inv]
    ring

section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem cubicFeature_trace_pair {m : ℕ}
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (x : Fin m → ℝ) (P : Fin m → A) (B : A)
    (hx : ∀ i, 0 ≤ x i) (hPsum : ∑ i, P i = 1) :
    (∑ i, Real.sqrt (x i) *
      (τ (P i * B * (∑ j, (cubicFeature (x i) (x j) : ℂ) • P j) * B)).re) =
      (τ (moment x P 2 * B ^ 2) - τ ((moment x P 1 * B) ^ 2)).re := by
  classical
  let q (i j : Fin m) : ℝ := (τ (P i * B * P j * B)).re
  let pair (f : Fin m → Fin m → ℝ) : ℝ := ∑ i, ∑ j, f i j * q i j
  have hq (i j : Fin m) : q i j = q j i := by
    simpa only [q, mul_assoc] using congrArg Complex.re (hτ (P i * B) (P j * B))
  have hflip (f : Fin m → Fin m → ℝ) : pair (fun i j => f j i) = pair f := by
    unfold pair
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hq j i]
  have hadd (f g : Fin m → Fin m → ℝ) :
      pair (fun i j => f i j + g i j) = pair f + pair g := by
    simp only [pair, add_mul, Finset.sum_add_distrib]
  have hsub (f g : Fin m → Fin m → ℝ) :
      pair (fun i j => f i j - g i j) = pair f - pair g := by
    simp only [pair, sub_mul, Finset.sum_sub_distrib]
  have hcross :
      (∑ i, Real.sqrt (x i) *
        (τ (P i * B * (∑ j, (cubicFeature (x i) (x j) : ℂ) • P j) * B)).re) =
        pair (fun i j => Real.sqrt (x i) * cubicFeature (x i) (x j)) := by
    simp only [pair, q, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
      map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul, mul_assoc]
  have hmoment (r s : ℕ) :
      (τ ((moment x P r * B) * (moment x P s * B))).re =
        pair (fun i j => x i ^ r * x j ^ s) := by
    have hMB (k : ℕ) :
        moment x P k * B = ∑ i, (↑(x i ^ k) : ℂ) • (P i * B) := by
      simp only [moment, Finset.sum_mul, smul_mul_assoc]
    rw [hMB r, hMB s, Finset.sum_mul]
    simp only [pair, q, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← Complex.ofReal_mul, map_sum, map_smul, smul_eq_mul, Complex.re_sum,
      Complex.re_ofReal_mul, mul_left_comm, mul_assoc]
  have hzero : moment x P 0 = 1 := by simpa only [moment, pow_zero, Complex.ofReal_one,
    one_smul] using hPsum
  have hsecond : (τ (moment x P 2 * B ^ 2)).re = pair (fun i _ => x i ^ 2) := by
    simpa only [hzero, one_mul, pow_zero, mul_one, pow_two, mul_assoc] using hmoment 2 0
  have hfirst : (τ ((moment x P 1 * B) ^ 2)).re = pair (fun i j => x i * x j) := by
    simpa only [pow_two, pow_one] using hmoment 1 1
  rw [hcross, Complex.sub_re, hsecond, hfirst]
  have hpair (i j : Fin m) := cubicFeature_pair (x i) (x j) (hx i) (hx j)
  have hsym :
      pair (fun i j => Real.sqrt (x i) * cubicFeature (x i) (x j)) +
        pair (fun i j => Real.sqrt (x i) * cubicFeature (x i) (x j)) =
        pair (fun i j => (x i - x j) ^ 2) := by
    calc
      _ = pair (fun i j =>
          Real.sqrt (x i) * cubicFeature (x i) (x j) +
          Real.sqrt (x j) * cubicFeature (x j) (x i)) := by
        rw [hadd, hflip]
      _ = _ := by simp only [hpair]
  have hsquare :
      pair (fun i j => (x i - x j) ^ 2) =
        pair (fun i _ => x i ^ 2) + pair (fun i _ => x i ^ 2) -
          (pair (fun i j => x i * x j) + pair (fun i j => x i * x j)) := by
    calc
      _ = pair (fun i j => x i ^ 2 + x j ^ 2 - (x i * x j + x i * x j)) := by
        congr 1
        funext i j
        ring
      _ = _ := by
        rw [hsub, hadd, hadd, hflip (fun i _ => x i ^ 2)]
  linarith only [hsym, hsquare]

private noncomputable def cubicMomentDefect (τ : A →P[ℂ] ℂ) (B : A) (M : ℕ → A) : ℂ :=
  ((gaps 3).map fun g => τ (M g.1 * B * M g.2.1 * B * M g.2.2 * B)).sum -
    10 * τ ((M 1 * B) ^ 3)

private theorem cubicMomentDefect_gap {m : ℕ}
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (x : Fin m → ℝ) (P : Fin m → A) (B : A)
    (hx : ∀ i, 0 ≤ x i) (hP : ∀ i, 0 ≤ P i) (hPsum : ∑ i, P i = 1) (hB : 0 ≤ B) :
    3 * (τ (moment x P 2 * B ^ 2) - τ ((moment x P 1 * B) ^ 2)).re ^ 2 ≤
      (τ (moment x P 1 * B)).re * (cubicMomentDefect τ B (moment x P)).re := by
  classical
  let z (i j : Fin m) := cubicFeature (x i) (x j)
  let Z (i : Fin m) : A := ∑ j, (z i j : ℂ) • P j
  let C (i j k : Fin m) :=
    (x i - x j) * (x i - x k) * symmetricKernel (x i) (x j) (x k)
  let walk (f : Fin m → Fin m → Fin m → ℝ) : ℂ :=
    ∑ i, ∑ j, ∑ k, (f i j k : ℂ) * τ (P i * B * P j * B * P k * B)
  have hcycle (f : Fin m → Fin m → Fin m → ℝ) :
      walk (fun i j k => f j k i) = walk f := by
    unfold walk
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simpa only [mul_assoc] using hτ (P i * B) (P j * B * P k * B)
  have hcubic : cubicMomentDefect τ B (moment x P) =
      walk (fun i j k => cubicDefect (x i) (x j) (x k)) := by
    have hcube : τ ((moment x P 1 * B) ^ 3) =
        τ (moment x P 1 * B * moment x P 1 * B * moment x P 1 * B) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    simp only [cubicMomentDefect, cubicGaps, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, hcube, mixedMomentTrace τ P B x, walk, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    push_cast [cubicDefect]
    ring
  have hdecomp (i j k : Fin m) : cubicDefect (x i) (x j) (x k) =
      C i j k + C j k i + C k i j := by
    rw [cubicDefect_eq_cyclic_symmetric]
    simp only [C]
    ring
  have hsplit (f g : Fin m → Fin m → Fin m → ℝ) :
      walk (fun i j k => f i j k - g i j k) = walk f - walk g := by
    simp only [walk, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  have hdefect : cubicMomentDefect τ B (moment x P) = 3 * walk C := by
    rw [hcubic]
    have hadd : walk (fun i j k => cubicDefect (x i) (x j) (x k)) =
        walk C + walk (fun i j k => C j k i) + walk (fun i j k => C k i j) := by
      simp only [walk, hdecomp, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
    rw [hadd, hcycle (fun i j k => C j k i), hcycle C]
    ring
  have hrem : 0 ≤ walk (fun i j k => C i j k - z i j * z i k) := by
    exact centeredCubicTrace_nonneg τ hτ P B hP hB
      (fun i => Matrix.of fun j k => C i j k - z i j * z i k)
      (fun i => cubicFeature_remainder_psd x hx (x i) (hx i))
  rw [hsplit] at hrem
  let R (i : Fin m) : A := CFC.sqrt (P i)
  let S : A := CFC.sqrt B
  have hR (i : Fin m) : star (R i) = R i := (CFC.sqrt_nonneg (P i)).star_eq
  have hS : star S = S := (CFC.sqrt_nonneg B).star_eq
  have hRsq (i : Fin m) : R i * R i = P i := CFC.sqrt_mul_sqrt_self _ (hP i)
  have hSsq : S * S = B := CFC.sqrt_mul_sqrt_self B hB
  have hPstar (j : Fin m) : star (P j) = P j := (hP j).star_eq
  have hZ (i : Fin m) : star (Z i) = Z i := by
    simp only [Z, star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, hPstar]
  have hinner (i : Fin m) (T W : A) :
      τ (star (S * T * R i) * (S * W * R i)) = τ (P i * star T * B * W) := by
    have hproduct :
        star (S * T * R i) * (S * W * R i) = R i * (star T * (S * S) * W) * R i := by
      simp only [star_mul, hS, hR, mul_assoc]
    rw [hproduct, hSsq, hτ (R i * (star T * B * W)) (R i), ← mul_assoc, hRsq]
    simp only [mul_assoc]
  let U (i : Fin m) : A := (Real.sqrt (x i) : ℂ) • (S * 1 * R i)
  let V (i : Fin m) : A := S * (Z i * B) * R i
  let u (i : Fin m) := (τ (star (U i) * U i)).re
  let v (i : Fin m) := (τ (star (V i) * V i)).re
  let uv (i : Fin m) := (τ (star (U i) * V i)).re
  have hsqrt (i : Fin m) := Real.mul_self_sqrt (hx i)
  have hunit (i : Fin m) :
      τ (star (S * R i) * (S * R i)) = τ (P i * B) := by
    simpa only [mul_one, star_one, one_mul] using hinner i 1 1
  have hcrossUnit (i : Fin m) :
      τ (star (S * R i) * (S * (Z i * B) * R i)) = τ (P i * B * (Z i * B)) := by
    simpa only [mul_one, star_one, one_mul] using hinner i 1 (Z i * B)
  have hu : (∑ i, u i) = (τ (moment x P 1 * B)).re := by
    simp only [u, U, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc,
      mul_smul_comm, smul_smul, ← Complex.ofReal_mul, hsqrt, mul_one, hunit,
      moment, pow_one, Finset.sum_mul, map_sum, map_smul, smul_eq_mul,
      Complex.re_sum, Complex.re_ofReal_mul]
  have huv : (∑ i, uv i) =
      (τ (moment x P 2 * B ^ 2) - τ ((moment x P 1 * B) ^ 2)).re := by
    simp only [uv, U, V, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc,
      mul_one, hcrossUnit, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    simpa only [mul_assoc, Z, z] using cubicFeature_trace_pair τ hτ x P B hx hPsum
  have hv : (∑ i, v i) = (walk (fun i j k => z i j * z i k)).re := by
    simp only [walk, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hZB : Z i * B = ∑ j, (z i j : ℂ) • (P j * B) := by
      simp only [Z, Finset.sum_mul, smul_mul_assoc]
    change (τ (star (S * (Z i * B) * R i) * (S * (Z i * B) * R i))).re = _
    rw [hinner, star_mul, hZ, hB.star_eq]
    have hproduct :
        P i * (B * Z i) * B * (Z i * B) = (P i * B) * (Z i * B) * (Z i * B) := by
      simp only [mul_assoc]
    have hfirst :
        (P i * B) * (Z i * B) = ∑ j, (z i j : ℂ) • ((P i * B) * (P j * B)) := by
      rw [hZB, Finset.mul_sum]
      simp only [mul_smul_comm]
    rw [hproduct, hfirst, hZB, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul,
      smul_eq_mul, Complex.re_sum, Complex.ofReal_mul, mul_left_comm, mul_assoc]
  have hnonneg (a : A) : 0 ≤ τ (star a * a) := τ.map_nonneg (star_mul_self_nonneg a)
  have hnorm (a : A) : ‖τ (star a * a)‖ = (τ (star a * a)).re := by
    simpa only [Complex.ofReal_re] using
      (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hnonneg a))).symm
  have hCS : (∑ i, uv i) ^ 2 ≤ (∑ i, u i) * ∑ i, v i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · exact fun i _ => (hnonneg (U i)).1
    · exact fun i _ => (hnonneg (V i)).1
    · intro i _
      have h := PositiveLinearMap.norm_map_star_mul_sq_le τ (U i) (V i)
      rw [hnorm, hnorm] at h
      have hre := Complex.sq_norm_sub_sq_re (τ (star (U i) * V i))
      exact (by linarith only [hre, sq_nonneg (τ (star (U i) * V i)).im] :
        (τ (star (U i) * V i)).re ^ 2 ≤ ‖τ (star (U i) * V i)‖ ^ 2).trans h
  have henergy : 3 * (∑ i, v i) ≤ (cubicMomentDefect τ B (moment x P)).re := by
    rw [hv, hdefect]
    have hre := hrem.1
    simp only [Complex.sub_re, Complex.zero_re] at hre
    rw [show (3 : ℂ) = ↑(3 : ℝ) by norm_num, Complex.re_ofReal_mul]
    linarith only [hre]
  have hmass : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => (hnonneg (U i)).1
  rw [← hu, ← huv]
  calc
    _ ≤ 3 * ((∑ i, u i) * ∑ i, v i) := mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ = (∑ i, u i) * (3 * ∑ i, v i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy hmass

end

/-- The three-factor product inequality in a tracial C*-algebra,
with the same scalar condition in the large degrees as in the matrix proof. -/
theorem compositionTrace_ge_all
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (X B : A) (hX : 0 ≤ X) (hB : 0 ≤ B)
    (p : ℕ) (hp : 3 ≤ p)
    (hLarge : 11 ≤ p → ExtremeWalk.UpperPSD.{0} p) :
    ((gaps p).length : ℂ) * τ ((X ^ p * B) ^ 3) ≤
      ((gaps p).map fun g =>
        τ ((X ^ 3) ^ g.1 * B * (X ^ 3) ^ g.2.1 * B * (X ^ 3) ^ g.2.2 * B)).sum := by
  classical
  by_cases h : 5 ≤ p
  · have hUpper : ExtremeWalk.UpperPSD.{0} p := by
      by_cases hl : 11 ≤ p
      · exact hLarge hl
      have hp' : p ≤ 10 := by omega
      interval_cases p
      · exact Extreme.upperPSD_five
      · exact Extreme.upperPSD_six
      · exact Extreme.upperPSD_seven
      · exact Extreme.upperPSD_eight
      · exact Extreme.upperPSD_nine
      · exact Extreme.upperPSD_ten
    apply compositionTrace_ge_of_centeredKernel τ hτ X B hX hB p
      (ExtremeWalk.centeredKernel p)
    · exact ExtremeWalk.defect_eq_cyclic_all p
    · intro m x hx i
      exact ExtremeWalk.centered_posSemidef hUpper (x i) (hx i) x
  have hp' : p ≤ 4 := by omega
  interval_cases p
  · apply compositionTrace_ge_of_centeredKernel τ hτ X B hX hB 3
      (fun x y z => (y ^ 3 - x ^ 3) * (z ^ 3 - x ^ 3) *
        symmetricKernel (x ^ 3) (y ^ 3) (z ^ 3))
    · intro x y z _ _ _
      have he : defect 3 x y z = cubicDefect (x ^ 3) (y ^ 3) (z ^ 3) := by
        norm_num [defect, cubicGaps, cubicDefect]
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
    (hLarge : 11 ≤ p → ExtremeWalk.UpperPSD.{0} p) :
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

private theorem wordMean_eq_gapMean
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (p : ℕ) :
    ((balancedWords p 3).map fun w =>
        τ ((w.map fun letter => if letter then a else b).prod)).sum /
        ((balancedWords p 3).length : ℂ) =
      ((gaps p).map fun g => τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)).sum /
        ((gaps p).length : ℂ) := by
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
  change ((balancedWords p 3).map v).sum / ((balancedWords p 3).length : ℂ) =
    ((gaps p).map F).sum / ((gaps p).length : ℂ)
  apply (div_eq_div_iff (by exact_mod_cast hw.ne') (by exact_mod_cast hg.ne')).2
  linear_combination (((gaps p).length : ℂ) / 3) * hSums -
    (((gaps p).map F).sum / 3) * hCast

/-- The normalized composition trace is the mean over all ordered words. -/
theorem productTrace_ge_wordMean
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (p : ℕ) (hp : 3 ≤ p)
    (hLarge : 11 ≤ p → ExtremeWalk.UpperPSD.{0} p) :
    τ (((a ^ ((p : ℝ) / 3)) * b) ^ 3) ≤
      ((balancedWords p 3).map fun w =>
        τ ((w.map fun letter => if letter then a else b).prod)).sum /
        ((balancedWords p 3).length : ℂ) := by
  rw [wordMean_eq_gapMean τ hτ a b p]
  exact productTrace_ge_all τ hτ a b ha hb p hp hLarge

/-- The degree-three word mean has a quantitative gap controlled by the
squared trace of the commutator's star-square. -/
theorem wordMean_three_trace_gap
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3 * (τ (star (a * b - b * a) * (a * b - b * a))).re ^ 2 ≤
      40 * (τ (a * b)).re *
        (((balancedWords 3 3).map fun w =>
          τ ((w.map fun letter => if letter then a else b).prod)).sum /
          ((balancedWords 3 3).length : ℂ) - τ ((a * b) ^ 3)).re := by
  classical
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hApprox (n : ℕ) :
      ∃ (m : ℕ) (x : Fin m → ℝ) (P : Fin m → A),
        (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ P i) ∧ (∑ i, P i) = 1 ∧
          ∀ k ≤ 3, ‖moment x P k - a ^ k‖ ≤ ε n := by
    have hεn : 0 < ε n := Nat.one_div_pos_of_nat
    obtain ⟨m, x, P, _, hx, hP, hPsum, hclose⟩ :=
      exists_positive_moment_approximation a ha (Finset.range 4) (ε n) hεn
    refine ⟨m, x, P, hx, hP, hPsum, fun k hk => ?_⟩
    have hMoment : moment x P k = ∑ i : Fin m, (x i ^ k) • P i := by
      unfold moment
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (x i ^ k) (P i)).symm
    rw [hMoment]
    exact hclose k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  choose m x P hx hP hPsum hclose using hApprox
  let M (n k : ℕ) := moment (x n) (P n) k
  have hM (k : ℕ) (hk : k ≤ 3) : Tendsto (fun n => M n k) atTop (𝓝 (a ^ k)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [dist_eq_norm]
    exact squeeze_zero (fun n => norm_nonneg (M n k - a ^ k))
      (fun n => hclose n k hk) tendsto_one_div_add_atTop_nhds_zero_nat
  have hτc : Continuous (fun a : A => τ a) := τ.toContinuousLinearMap.continuous
  have hbLim : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
  have habLim : Tendsto (fun n => M n 1 * b) atTop (𝓝 (a * b)) := by
    simpa only [pow_one] using (hM 1 (by decide)).mul hbLim
  have hmassLim : Tendsto (fun n => (τ (M n 1 * b)).re) atTop (𝓝 (τ (a * b)).re) :=
    (Complex.continuous_re.tendsto _).comp ((hτc.tendsto _).comp habLim)
  have hcrossLim :
      Tendsto (fun n => (τ (M n 2 * b ^ 2) - τ ((M n 1 * b) ^ 2)).re) atTop
        (𝓝 (τ (a ^ 2 * b ^ 2) - τ ((a * b) ^ 2)).re) :=
    (Complex.continuous_re.tendsto _).comp
      (((hτc.tendsto _).comp ((hM 2 (by decide)).mul (hbLim.pow 2))).sub
        ((hτc.tendsto _).comp (habLim.pow 2)))
  have hdefectLim :
      Tendsto (fun n => (cubicMomentDefect τ b (M n)).re) atTop
        (𝓝 (cubicMomentDefect τ b (fun k => a ^ k)).re) := by
    let term (g : ℕ × ℕ × ℕ) (n : ℕ) : ℂ :=
      τ (M n g.1 * b * M n g.2.1 * b * M n g.2.2 * b)
    let limit (g : ℕ × ℕ × ℕ) : ℂ :=
      τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)
    have hterm (g : ℕ × ℕ × ℕ) (hg : g ∈ gaps 3) :
        Tendsto (term g) atTop (𝓝 (limit g)) := by
      have htotal := (DimThree.mem_gaps_iff_total 3 g).mp hg
      have h₁ := hM g.1 (by omega)
      have h₂ := hM g.2.1 (by omega)
      have h₃ := hM g.2.2 (by omega)
      exact (hτc.tendsto _).comp (((((h₁.mul hbLim).mul h₂).mul hbLim).mul h₃).mul hbLim)
    have hsum := tendsto_list_sum (f := term) (a := limit) (gaps 3) hterm
    have hcube := (hτc.tendsto ((a * b) ^ 3)).comp (habLim.pow 3)
    apply (Complex.continuous_re.tendsto _).comp
    simpa only [cubicMomentDefect, term, limit, pow_one, Function.comp_apply] using
      hsum.sub (hcube.const_mul 10)
  have hgap := le_of_tendsto_of_tendsto' ((hcrossLim.pow 2).const_mul 3)
    (hmassLim.mul hdefectLim) (fun n => cubicMomentDefect_gap τ hτ (x n) (P n) b
      (hx n) (hP n) (hPsum n) hb)
  have hcomm :
      (τ (star (a * b - b * a) * (a * b - b * a))).re =
        2 * (τ (a ^ 2 * b ^ 2) - τ ((a * b) ^ 2)).re := by
    have hexpand : star (a * b - b * a) * (a * b - b * a) =
        (b * a * a * b - b * a * b * a) - (a * b * a * b - a * b * b * a) := by
      simp only [star_sub, star_mul, ha.star_eq, hb.star_eq]
      noncomm_ring
    have h₁ : τ (b * a * a * b) = τ (a ^ 2 * b ^ 2) := by
      simpa only [pow_two, mul_assoc] using hτ b (a * a * b)
    have h₂ : τ (b * a * b * a) = τ ((a * b) ^ 2) := by
      simpa only [pow_two, mul_assoc] using hτ b (a * b * a)
    have h₃ : τ (a * b * a * b) = τ ((a * b) ^ 2) := by
      simp only [pow_two, mul_assoc]
    have h₄ : τ (a * b * b * a) = τ (a ^ 2 * b ^ 2) := by
      simpa only [pow_two, mul_assoc] using hτ (a * b * b) a
    simp only [hexpand, map_sub, h₁, h₂, h₃, h₄, Complex.sub_re]
    ring
  have hCount : ((gaps 3).length : ℂ) = 10 := by norm_num [cubicGaps]
  have hnormalized :
      (cubicMomentDefect τ b (fun k => a ^ k)).re =
        10 * (((gaps 3).map fun g => τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)).sum /
          (10 : ℂ) - τ ((a * b) ^ 3)).re := by
    have heq : cubicMomentDefect τ b (fun k => a ^ k) =
        10 * (((gaps 3).map fun g => τ (a ^ g.1 * b * a ^ g.2.1 * b * a ^ g.2.2 * b)).sum /
          (10 : ℂ) - τ ((a * b) ^ 3)) := by
      simp only [cubicMomentDefect, pow_one]
      ring
    rw [heq, show (10 : ℂ) = ↑(10 : ℝ) by norm_num, Complex.re_ofReal_mul]
  rw [hcomm, wordMean_eq_gapMean τ hτ a b 3, hCount]
  rw [hnormalized] at hgap
  nlinarith only [hgap]

#print axioms wordMean_three_trace_gap

#print axioms productTrace_ge_wordMean

#print axioms productTrace_ge_all

#print axioms compositionTrace_ge_all

end RefinedBMV.Tracial
