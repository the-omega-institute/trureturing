/- GID: D5/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/GroupedFourThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV (4,3) mean dominates the grouped trace for arbitrary PSD spectra. -/

import D5.S3.Quantum.Analysis.RefinedBMV43
import D5.S3.Quantum.Analysis.RefinedBMV43Kernel
import Batteries.Tactic.OpenPrivate

/-! # The grouped trace comparison at bidegree (4,3) -/

open private weighted_cauchy_psd from D5.S3.Quantum.Analysis.RefinedBMVKernel
open private sum_traceGaps43 mean43_map from D5.S3.Quantum.Analysis.RefinedBMV43

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section

namespace RefinedBMV

private def groupedDefect43 (x y z : ℝ) : ℝ :=
  (gaps43.map fun g ↦ x ^ g.1 * y ^ g.2.1 * z ^ g.2.2).sum -
    5 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)

private def groupedGram43 (x y z : ℝ) : ℝ :=
  x ^ 2 * (x + 3 * y) * (x + 3 * z)

private def groupedNumerator43 (x y z : ℝ) : ℝ :=
  8 * x * y ^ 2 * z ^ 2

-- Both numerator terms vanish at a zero center. At y = z = 0 the Cauchy term vanishes.
private def groupedKernel43 (x y z : ℝ) : ℝ :=
  (groupedGram43 x y z + groupedNumerator43 x y z / (y + z)) / ((x + y) * (x + z))

private def groupedCentered43 (x y z : ℝ) : ℝ :=
  (x - y) * (x - z) * groupedKernel43 x y z

set_option maxHeartbeats 800000 in
-- Normalize the polynomial after clearing the three denominators.
private theorem groupedPolynomial43 (x y z : ℝ) :
    (x - y) * (x - z) * ((y + z) * groupedGram43 x y z + groupedNumerator43 x y z) +
    (y - z) * (y - x) * ((z + x) * groupedGram43 y z x + groupedNumerator43 y z x) +
    (z - x) * (z - y) * ((x + y) * groupedGram43 z x y + groupedNumerator43 z x y) =
      (x + y) * (y + z) * (z + x) * groupedDefect43 x y z := by
  simp only [groupedDefect43, gaps43, gapOrbits43, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, groupedGram43, groupedNumerator43]
  ring

private theorem clear_groupedKernel43 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y) * (y + z) * (z + x) * groupedKernel43 x y z =
      (y + z) * groupedGram43 x y z + groupedNumerator43 x y z := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [groupedKernel43, groupedGram43, groupedNumerator43]
  · have hxy : x + y ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hx hy)
    have hxz : x + z ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hx hz)
    rw [groupedKernel43,
      show (x + y) * (y + z) * (z + x) = (y + z) * ((x + y) * (x + z)) by ring,
      mul_assoc, mul_div_cancel₀ _ (mul_ne_zero hxy hxz), mul_add]
    by_cases hyz : y + z = 0
    · have hy₀ : y = 0 := by linarith
      have hz₀ : z = 0 := by linarith
      simp [hy₀, hz₀, groupedNumerator43]
    · rw [mul_div_cancel₀ _ hyz]

private theorem groupedKernel43_at_zeros (x : ℝ) (hx : 0 ≤ x) :
    groupedKernel43 x 0 0 = x ^ 2 := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [groupedKernel43, groupedGram43, groupedNumerator43]
  · simp [groupedKernel43, groupedGram43, groupedNumerator43]
    field_simp [hx.ne']

private theorem groupedDefect43_at_zeros (x : ℝ) (hx : 0 ≤ x) :
    groupedDefect43 x 0 0 =
      groupedCentered43 x 0 0 + groupedCentered43 0 0 x + groupedCentered43 0 x 0 := by
  simp [groupedCentered43, groupedKernel43_at_zeros x hx, groupedDefect43, gaps43,
    gapOrbits43]
  ring

private theorem groupedDefect43_rotate (x y z : ℝ) :
    groupedDefect43 y z x = groupedDefect43 x y z := by
  simp only [groupedDefect43, gaps43, gapOrbits43, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

private theorem groupedDefect43_eq_cyclic (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    groupedDefect43 x y z =
      groupedCentered43 x y z + groupedCentered43 y z x + groupedCentered43 z x y := by
  by_cases hxy : x + y = 0
  · have hx₀ : x = 0 := by linarith
    have hy₀ : y = 0 := by linarith
    subst x y
    rw [groupedDefect43_rotate z 0 0, groupedDefect43_at_zeros z hz]
    ring
  by_cases hyz : y + z = 0
  · have hy₀ : y = 0 := by linarith
    have hz₀ : z = 0 := by linarith
    subst y z
    exact groupedDefect43_at_zeros x hx
  by_cases hzx : z + x = 0
  · have hx₀ : x = 0 := by linarith
    have hz₀ : z = 0 := by linarith
    subst x z
    rw [← groupedDefect43_rotate 0 y 0, groupedDefect43_at_zeros y hy]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hxy hyz) hzx)
  calc
    _ = (x - y) * (x - z) * ((x + y) * (y + z) * (z + x) * groupedKernel43 x y z) +
        (y - z) * (y - x) * ((y + z) * (z + x) * (x + y) * groupedKernel43 y z x) +
        (z - x) * (z - y) * ((z + x) * (x + y) * (y + z) * groupedKernel43 z x y) := by
          rw [clear_groupedKernel43 x y z hx hy hz, clear_groupedKernel43 y z x hy hz hx,
            clear_groupedKernel43 z x y hz hx hy]
          exact (groupedPolynomial43 x y z).symm
    _ = _ := by simp only [groupedCentered43]; ring

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem groupedKernel43_psd {ι : Type*} [Finite ι] (x : ℝ) (hx : 0 ≤ x)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (Matrix.of fun i j ↦ groupedKernel43 x (a i) (a j) : Matrix ι ι ℝ).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι
  rcases hx.eq_or_lt with rfl | hx
  · convert (PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef) using 1
    ext i j
    simp [groupedKernel43, groupedGram43, groupedNumerator43]
  · let u (i : ι) := x * (x + 3 * a i) / (x + a i)
    let w (i : ι) := a i ^ 2 / (x + a i)
    have hRank := posSemidef_vecMulVec_self_star u
    have hCauchy := (weighted_cauchy_psd a w ha (by intro i hi; simp [w, hi])).smul
      (show 0 ≤ 8 * x by positivity)
    convert hRank.add hCauchy using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      star_trivial, smul_eq_mul, groupedKernel43, groupedGram43, groupedNumerator43, u, w,
      div_eq_mul_inv, mul_inv]
    ring

omit [DecidableEq n] in
private theorem walk_cyclic_sum43 (R : Matrix n n ℂ) (f : n → n → n → ℂ) :
    walk R (f + (fun i j k ↦ f j k i) + (fun i j k ↦ f k i j)) = 3 * walk R f := by
  classical
  rw [map_add, map_add, walk_rotate R (fun i j k ↦ f j k i), walk_rotate R f]
  ring

set_option maxHeartbeats 1600000 in
-- Normalize the fifteen gap compositions and the three cyclic paired terms.
private theorem groupedTraceGap43 (a : n → ℝ) (R : Matrix n n ℂ) :
    15 * (mean43 (diagonal fun i ↦ (a i : ℂ)) R -
      trace (R ^ 2 * (diagonal fun i ↦ (a i : ℂ)) ^ 2 * R *
        (diagonal fun i ↦ (a i : ℂ)) ^ 2)) =
      walk R (fun i j k ↦ (groupedDefect43 (a i) (a j) (a k) : ℂ)) := by
  let d : n → ℂ := fun i ↦ a i
  let D : Matrix n n ℂ := diagonal d
  let f (g : ℕ × ℕ × ℕ) (i j k : n) : ℂ :=
    d i ^ g.1 * d j ^ g.2.1 * d k ^ g.2.2
  let paired : n → n → n → ℂ := fun i j _ ↦ d i ^ 2 * d j ^ 2
  have htrace : traceGaps43 D R = fun g ↦ walk R (f g) := by
    funext g
    simpa only [D, traceGaps43, f, mul_assoc] using trace_pow_walk R d g.1 g.2.1 g.2.2
  have hpaired : walk R paired = trace (R ^ 2 * D ^ 2 * R * D ^ 2) := by
    symm
    calc
      trace (R ^ 2 * D ^ 2 * R * D ^ 2) =
          trace (R ^ 2 * (D ^ 2 * R * D ^ 2)) := by
            rw [← mul_assoc (R ^ 2) (D ^ 2 * R) (D ^ 2),
              ← mul_assoc (R ^ 2) (D ^ 2) R]
      _ = trace ((D ^ 2 * R * D ^ 2) * R ^ 2) :=
        trace_mul_comm (R ^ 2) (D ^ 2 * R * D ^ 2)
      _ = walk R paired := by
        have hw := trace_pow_walk R d 2 2 0
        change trace (D ^ 2 * R * D ^ 2 * R * D ^ 0 * R) = _ at hw
        rw [pow_zero, mul_one, mul_assoc (D ^ 2 * R * D ^ 2) R R, ← pow_two R] at hw
        simpa only [paired, pow_zero, mul_one] using hw
  have hpairedSum :
      5 * walk R (paired + (fun i j k ↦ paired j k i) + (fun i j k ↦ paired k i j)) =
        15 * trace (R ^ 2 * D ^ 2 * R * D ^ 2) := by
    rw [walk_cyclic_sum43, hpaired, ← mul_assoc]
    norm_num
  change 15 * (mean43 D R - trace (R ^ 2 * D ^ 2 * R * D ^ 2)) = _
  rw [mul_sub, ← sum_traceGaps43, htrace, sum_walk43 R gaps43 f, ← hpairedSum]
  change walk R _ - (5 : ℂ) • walk R _ = _
  rw [← map_smul, ← map_sub]
  congr 1
  funext i j k
  simp only [groupedDefect43, f, paired, d, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, gaps43, gapOrbits43, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast <;> ring

private def groupedWeight43 (a : n → ℝ) (i j k : n) : ℂ :=
  (groupedCentered43 (a i) (a j) (a k) : ℝ)

omit [DecidableEq n] in
private theorem walk_groupedDefect43 (a : n → ℝ) (ha : ∀ i, 0 ≤ a i) (R : Matrix n n ℂ) :
    walk R (fun i j k ↦ (groupedDefect43 (a i) (a j) (a k) : ℂ)) =
      3 * walk R (groupedWeight43 a) := by
  have h : (fun i j k ↦ (groupedDefect43 (a i) (a j) (a k) : ℂ)) =
      groupedWeight43 a + (fun i j k ↦ groupedWeight43 a j k i) +
        (fun i j k ↦ groupedWeight43 a k i j) := by
    funext i j k
    simp only [Pi.add_apply, groupedWeight43]
    exact_mod_cast groupedDefect43_eq_cyclic (a i) (a j) (a k) (ha i) (ha j) (ha k)
  rw [h, walk_cyclic_sum43]

omit [DecidableEq n] in
private theorem groupedCenteredForm43 (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (R : Matrix n n ℂ) (hR : R.PosSemidef) (i : n) :
    0 ≤ ∑ j, ∑ k, R i j * R j k * R k i * groupedWeight43 a i j k := by
  classical
  let G : Matrix n n ℝ := Matrix.of fun j k ↦ groupedKernel43 (a i) (a j) (a k)
  have hG : G.PosSemidef := groupedKernel43_psd (a i) (ha i) a ha
  have hGc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G hG
  let v : n → ℂ := fun j ↦ ((a i - a j : ℝ) : ℂ) * R j i
  have hp : (R ⊙ G.map Complex.ofReal).PosSemidef := hR.hadamard hGc
  convert hp.dotProduct_mulVec_nonneg v using 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hstar : star (R j i) = R i j := congrFun (congrFun hR.isHermitian i) j
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [groupedWeight43, groupedCentered43, Pi.star_apply, v, star_mul, hreal, hstar,
    hadamard_apply, Matrix.map_apply, G, Matrix.of_apply, Complex.ofReal_mul]
  ring

private theorem grouped43_diagonal (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (R : Matrix n n ℂ) (hR : R.PosSemidef) :
    (trace (R ^ 2 * (diagonal fun i ↦ (a i : ℂ)) ^ 2 * R *
      (diagonal fun i ↦ (a i : ℂ)) ^ 2)).re ≤
      (mean43 (diagonal fun i ↦ (a i : ℂ)) R).re := by
  have h := groupedTraceGap43 a R
  rw [walk_groupedDefect43 a ha R] at h
  have hn : 0 ≤ walk R (groupedWeight43 a) :=
    Finset.sum_nonneg fun i _ ↦ groupedCenteredForm43 a ha R hR i
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.sub_re] at hre
  have hnre := (Complex.nonneg_iff.mp hn).1
  linarith

set_option maxHeartbeats 1200000 in
-- Transport the full matrix product through the unitary algebra equivalence.
/-- The refined BMV mean for four copies of `C` and three copies of `R`
dominates the grouped trace for every finite-dimensional PSD pair. -/
theorem grouped43_all (R C : Matrix n n ℂ) (hR : R.PosSemidef) (hC : C.PosSemidef) :
    (trace (R ^ 2 * C ^ 2 * R * C ^ 2)).re ≤ (mean43 C R).re := by
  let U := hC.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  let d : n → ℂ := RCLike.ofReal ∘ hC.isHermitian.eigenvalues
  have hd : f C = diagonal d := hC.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hR' : (f R).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) R).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hR.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have h := grouped43_diagonal _ hC.eigenvalues_nonneg (f R) hR'
  change (trace ((f R) ^ 2 * (diagonal d) ^ 2 * f R * (diagonal d) ^ 2)).re ≤
    (mean43 (diagonal d) (f R)).re at h
  rw [← hd] at h
  have htr : trace ((f R) ^ 2 * (f C) ^ 2 * f R * (f C) ^ 2) =
      trace (R ^ 2 * C ^ 2 * R * C ^ 2) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul]
    exact trace_conjugation (star U) (R ^ 2 * C ^ 2 * R * C ^ 2)
  rw [htr] at h
  change _ ≤ (mean43 (f.toAlgEquiv C) (f.toAlgEquiv R)).re at h
  simpa only [mean43_map f.toAlgEquiv (trace_conjugation (star U))] using h

#print axioms grouped43_all

end RefinedBMV
