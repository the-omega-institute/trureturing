/- GID: D5/S3/Quantum/Analysis/RefinedBMVExtremeWalk
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered Schur walks for the unrestricted refined BMV comparison. -/

import D5.S3.Quantum.Analysis.RefinedBMVThreeSpectrumReduction

/-! # Centered Schur walks for the refined BMV comparison

The upper kernel is the unnormalized block above the center. Its finite
positive semidefiniteness is the hypothesis of the matrix comparison.
The block below the center is an outer product, and entries across the
two sides or at the center vanish.
-/

open Matrix NormedSpace
open scoped ComplexOrder BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.ExtremeWalk

open DimThree (defect gaps mean_map trace_gap_all word_counts_all)
open UniformThreeSpectrum (defect_cycle_all defect_diag_all defect_nonneg_all)

universe u

/-- The unnormalized symmetric kernel for the block above the center. -/
def upperKernel (p : ℕ) (a x y : ℝ) : ℝ :=
  defect p a (min x y) (max x y) -
    √(defect p a a (max x y) * defect p (min x y) (min x y) (max x y))

/-- The centered coefficient for the cubic walk. -/
def centeredKernel (p : ℕ) (a x y : ℝ) : ℝ :=
  if a < x ∧ a < y then upperKernel p a x y
  else if x < a ∧ y < a then √(defect p x x a) * √(defect p y y a)
  else 0

/-- The condition on finite samples strictly above each nonnegative center. -/
def UpperPSD (p : ℕ) : Prop :=
  ∀ (a : ℝ), 0 ≤ a → ∀ {ι : Type u} [Fintype ι] (x : ι → ℝ),
    (∀ i, a < x i) → (Matrix.of fun i j ↦ upperKernel p a (x i) (x j)).PosSemidef

private theorem centeredKernel_comm (p : ℕ) (a x y : ℝ) :
    centeredKernel p a x y = centeredKernel p a y x := by
  simp only [centeredKernel, upperKernel, min_comm x y, max_comm x y,
    and_comm, mul_comm (√(defect p x x a))]

private theorem defect_last_swap (p : ℕ) (a x y : ℝ) :
    defect p a y x = defect p a x y := by
  calc
    defect p a y x = defect p y x a := (defect_cycle_all p a y x).symm
    _ = defect p x y a := DividedDifference.defect_swap_general p x y a
    _ = defect p a x y := defect_cycle_all p a x y

private theorem cyclic_ordered (p : ℕ)
    {a x y : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    defect p a x y = centeredKernel p a x y + centeredKernel p x y a +
      centeredKernel p y a x := by
  rcases hax.eq_or_lt with rfl | hax
  · rcases hxy.eq_or_lt with rfl | hay
    · simp [centeredKernel, defect_diag_all]
    · simp [centeredKernel, hay, not_lt_of_ge hay.le,
        Real.mul_self_sqrt (defect_nonneg_all p _ _ _ ha ha (ha.trans hay.le))]
  · rcases hxy.eq_or_lt with rfl | hxy
    · simp [centeredKernel, upperKernel, hax, not_lt_of_ge hax.le, defect_diag_all]
    · have hay := hax.trans hxy
      simp [centeredKernel, upperKernel, hax, hxy, hay, not_lt_of_ge hax.le,
        not_lt_of_ge hxy.le, not_lt_of_ge hay.le, min_eq_left hxy.le, max_eq_right hxy.le,
        Real.sqrt_mul (defect_nonneg_all p a a y ha ha (ha.trans hay.le))]

/-- The centered kernels sum to the exact coefficient at every degree, including all ties. -/
theorem defect_eq_cyclic_all (p : ℕ)
    (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    defect p a x y = centeredKernel p a x y + centeredKernel p x y a +
      centeredKernel p y a x := by
  have rotate {a x y : ℝ}
      (h : defect p a x y = centeredKernel p a x y + centeredKernel p x y a +
        centeredKernel p y a x) :
      defect p x y a = centeredKernel p x y a + centeredKernel p y a x +
        centeredKernel p a x y := by
    rw [defect_cycle_all p a x y, h]
    ac_rfl
  have flip {a x y : ℝ}
      (h : defect p a x y = centeredKernel p a x y + centeredKernel p x y a +
        centeredKernel p y a x) :
      defect p a y x = centeredKernel p a y x + centeredKernel p y x a +
        centeredKernel p x a y := by
    rw [defect_last_swap p a x y, h, centeredKernel_comm p a y x,
      centeredKernel_comm p y x a, centeredKernel_comm p x a y]
    ac_rfl
  rcases le_total a x with hax | hxa
  · rcases le_total x y with hxy | hyx
    · exact cyclic_ordered p ha hax hxy
    · rcases le_total a y with hay | hya
      · exact flip (cyclic_ordered p ha hay hyx)
      · exact rotate (cyclic_ordered p hy hya hax)
  · rcases le_total a y with hay | hya
    · exact flip (rotate (cyclic_ordered p hx hxa hay))
    · rcases le_total x y with hxy | hyx
      · exact rotate (rotate (cyclic_ordered p hx hxy hya))
      · exact rotate (flip (cyclic_ordered p hy hyx hxa))

/-- Extend the actual upper block by zero and add the rank-one lower block. -/
theorem centered_posSemidef {n : Type u} [Finite n] {p : ℕ} (a : ℝ) (x : n → ℝ)
    (hUpper : (Matrix.of fun i j : {i // a < x i} ↦
      upperKernel p a (x i) (x j)).PosSemidef) :
    (Matrix.of fun i j ↦ centeredKernel p a (x i) (x j)).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  let Above := {i // a < x i}
  let M : Matrix Above Above ℝ := Matrix.of fun i j ↦ upperKernel p a (x i) (x j)
  let E : Matrix n Above ℝ := Matrix.of fun i j ↦ if i = j.val then 1 else 0
  let v (i : n) : ℝ := if x i < a then √(defect p (x i) (x i) a) else 0
  have hsum_above (g : Above → ℝ) (i : n) :
      ∑ k, E i k * g k = if hi : a < x i then g ⟨i, hi⟩ else 0 := by
    split_ifs with hi
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : Above)]
      · simp [E]
      · intro k _ hk
        have hne : i ≠ k.val := fun h ↦ hk (Subtype.ext h.symm)
        simp [E, hne]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      have hne : i ≠ k.val := fun h ↦ hi (h ▸ k.property)
      simp [E, hne]
  have hmul (C : Matrix Above n ℝ) (i j : n) :
      (E * C) i j = if hi : a < x i then C ⟨i, hi⟩ j else 0 :=
    hsum_above (fun k ↦ C k j) i
  have hright (i : Above) (j : n) :
      (M * Eᴴ) i j = if hj : a < x j then M i ⟨j, hj⟩ else 0 := by
    simpa only [mul_apply, conjTranspose_apply, star_trivial, mul_comm] using
      hsum_above (fun k ↦ M i k) j
  have hsum := (hUpper.mul_mul_conjTranspose_same E).add
    (posSemidef_vecMulVec_self_star v)
  change (E * M * Eᴴ + vecMulVec v (star v)).PosSemidef at hsum
  convert hsum using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_assoc, hmul, hright,
    vecMulVec_apply, star_trivial]
  by_cases hi : a < x i
  · by_cases hj : a < x j
    · simp [centeredKernel, hi, hj, M, v, not_lt_of_ge hi.le]
    · simp [centeredKernel, hi, hj, v, not_lt_of_ge hi.le]
  · by_cases hj : a < x j
    · simp [centeredKernel, hi, hj, v, not_lt_of_ge hj.le]
    · by_cases hli : x i < a <;> by_cases hlj : x j < a <;>
        simp [centeredKernel, hi, hj, hli, hlj, v]

variable {n : Type u} [Fintype n]

private theorem walk_defect_nonneg {p : ℕ}
    (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hCentered : ∀ i, (Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)).PosSemidef)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    0 ≤ walk B (fun i j k ↦ ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) := by
  classical
  let g : n → n → n → ℂ := fun i j k ↦ centeredKernel p (a i) (a j) (a k)
  have hg : 0 ≤ walk B g := by
    change 0 ≤ ∑ i, ∑ j, ∑ k, B i j * B j k * B k i * g i j k
    apply Finset.sum_nonneg
    intro i _
    let G : Matrix n n ℝ := Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)
    have hc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G
      (hCentered i)
    have hSchur : (B ⊙ G.map Complex.ofReal).PosSemidef := hB.hadamard hc
    let v : n → ℂ := fun j ↦ B j i
    convert hSchur.dotProduct_mulVec_nonneg v using 1
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    have hstar : star (B j i) = B i j := congrFun (congrFun hB.isHermitian i) j
    simp only [Pi.star_apply, v, hstar, hadamard_apply, Matrix.map_apply, G,
      Matrix.of_apply, g]
    ring
  have h : (fun i j k ↦ ((defect p (a i) (a j) (a k) : ℝ) : ℂ)) =
      g + (fun i j k ↦ g j k i) + (fun i j k ↦ g k i j) := by
    funext i j k
    simp only [Pi.add_apply, g]
    exact_mod_cast defect_eq_cyclic_all p (a i) (a j) (a k) (ha i) (ha j) (ha k)
  rw [h, map_add, map_add, walk_rotate B (fun i j k ↦ g j k i), walk_rotate B g]
  exact add_nonneg (add_nonneg hg hg) hg

variable [DecidableEq n]

/-- Centered positivity on the given diagonal sample suffices for the trace-word comparison. -/
theorem diagonal_bound {p : ℕ}
    (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hCentered : ∀ i, (Matrix.of fun j k ↦ centeredKernel p (a i) (a j) (a k)).PosSemidef)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a i : ℂ)) ^ p * B) ^ 3) ≤
      DimThree.wordMean p ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B := by
  have hn := walk_defect_nonneg a ha hCentered B hB
  rw [← trace_gap_all p] at hn
  have hlen : (0 : ℝ) < (gaps p).length := by exact_mod_cast (word_counts_all p).2.1
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hlen).mp hre),
    (sub_eq_zero.mp (mul_eq_zero.mp him.symm |>.resolve_left hlen.ne')).symm⟩

private theorem cubeRoot_bound {p : ℕ}
    (hUpper : UpperPSD.{u} p) (X B : Matrix n n ℂ) (hX : X.PosSemidef)
    (hB : B.PosSemidef) :
    trace ((X ^ p * B) ^ 3) ≤ DimThree.wordMean p (X ^ 3) B := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · let : _ := hempty
    simp [DimThree.wordMean, RefinedBMV.wordMean, trace_eq_zero_of_isEmpty]
  let : _ := hne
  let U := hX.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have h := diagonal_bound _ hX.eigenvalues_nonneg (fun i ↦
    centered_posSemidef _ _ (hUpper _ (hX.eigenvalues_nonneg i)
      (fun j : {j // hX.isHermitian.eigenvalues i < hX.isHermitian.eigenvalues j} ↦
        hX.isHermitian.eigenvalues j) Subtype.property)) (f B) hB'
  change trace (((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ p * f B) ^ 3) ≤
    DimThree.wordMean p ((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ 3) (f B) at h
  have hd : f X = diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues) :=
    hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  rw [← hd, ← map_pow f, ← map_mul f, ← map_pow f, ← map_pow f, trace_conjugation] at h
  exact h.trans_eq (mean_map p f.toAlgEquiv (trace_conjugation (star U)) (X ^ 3) B)

/-- The refined BMV product bound at every degree, given upper-block positivity. -/
theorem product_bound_all {p : ℕ}
    (hUpper : UpperPSD.{u} p) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  let X := A ^ (1 / 3 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = A ^ ((1 / 3 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg A (1 / 3) k (by norm_num) (by positivity) hA.nonneg
  have h3 : X ^ (3 : ℕ) = A := by
    rw [hpow, show (1 / 3 : ℝ) * (↑(3 : ℕ) : ℝ) = 1 by norm_num, CFC.rpow_one A hA.nonneg]
  have hp' : X ^ p = A ^ ((p : ℝ) / 3) := by
    rw [hpow]
    congr 1
    ring
  simpa only [h3, hp'] using cubeRoot_bound hUpper X B hX.posSemidef hB

/-- The refined BMV exponential bound at every degree, given upper-block positivity. -/
theorem exponential_bound_all {p : ℕ}
    (hUpper : UpperPSD.{u} p) (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  let T : Matrix n n ℂ := (1 / 3 : ℝ) • H
  let X := exp T
  have hT : T.IsHermitian := hH.smul (by simp : star (1 / 3 : ℝ) = 1 / 3)
  have hpow (k : ℕ) : X ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h3 : X ^ (3 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have h := cubeRoot_bound hUpper X (exp K)
    hT.isSelfAdjoint.exp_nonneg.posSemidef hK.isSelfAdjoint.exp_nonneg.posSemidef
  rw [h3, hpow p] at h
  have ht := ThreeSpectralValues.trace_exp_le_cube ((p : ℝ) • T) K
    (hT.smul (by simp : star (p : ℝ) = p)) hK
  have hScale : (3 : ℝ) • ((p : ℝ) • T) = (p : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hScale] at ht
  exact ht.trans h

section Compatibility

-- Keep the named degree argument for callers of the original theorems.
set_option linter.unusedVariables false

/-- The centered kernels sum to the exact coefficient, including all ties. -/
theorem defect_eq_cyclic {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (a x y : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    defect p a x y = centeredKernel p a x y + centeredKernel p x y a +
      centeredKernel p y a x :=
  defect_eq_cyclic_all p a x y ha hx hy

/-- The refined BMV product bound given the upper-block positivity condition. -/
theorem product_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (hUpper : UpperPSD.{u} p) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B :=
  product_bound_all hUpper A B hA hB

/-- The refined BMV exponential bound given the upper-block positivity condition. -/
theorem exponential_bound {p : ℕ} (hp : p = 5 ∨ p = 6 ∨ p = 7)
    (hUpper : UpperPSD.{u} p) (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) :=
  exponential_bound_all hUpper H K hH hK

end Compatibility

#print axioms defect_eq_cyclic_all
#print axioms product_bound_all
#print axioms exponential_bound_all

end RefinedBMV.ExtremeWalk
