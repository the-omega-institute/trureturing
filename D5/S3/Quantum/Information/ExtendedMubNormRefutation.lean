/- GID: D5/S3/Quantum/Information/ExtendedMubNormRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ExtendedMubNormRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ExtendedMubNormRefutation.claim; result=D5/S3/Quantum/Information/ExtendedMubNormRefutation.result; claim=D5/S3/Quantum/Information/ExtendedMubNormRefutation.claim
   digest: A three-dimensional mixed norm exceeds the extended MUB prediction. -/

/-
proof_shape: result: bind-only (sorted characteristic-polynomial roots, finite-dimensional
  continuity and operator-norm bounds, exact rational arithmetic and power normalization)
escape_witness: none
admission_basis: open-problem-resolution (#11781; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Tactic.NormNum.RealSqrt

/-! Ordinary real matrix mixed norms and the extended MUB conjecture. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
open scoped Matrix BigOperators
open Matrix WithLp

namespace D5.S3.Quantum.Information.ExtendedMubNormRefutation

/-- Nonnegative entries and all row and column sums equal to one. -/
def DoublyStochastic {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  C ∈ doublyStochastic ℝ (Fin d)

/-- The second eigenvalue of the Gram matrix in descending order, including
multiplicity, followed by its nonnegative square root. The zero extension is
irrelevant to the claim, which assumes `2 ≤ d`. -/
def sigma2 {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : 1 < d then
    Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self C).eigenvalues₀
      ⟨1, by simpa using h⟩)
  else 0

/-- Ordinary finite-dimensional real ℓ_p norm for positive finite p. -/
def lpNorm {d : ℕ} (p : ℝ) (x : Fin d → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- All nonzero-vector norm ratios; signs of vectors are unrestricted. -/
def ratios {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (p q : ℝ) : Set ℝ :=
  {r | ∃ x : Fin d → ℝ, x ≠ 0 ∧ r = lpNorm q (C *ᵥ x) / lpNorm p x}

/-- Operator norm from ℓ_p to ℓ_q, as the supremum over nonzero vectors. -/
def opNorm {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (p q : ℝ) : ℝ :=
  sSup (ratios C p q)

/-- The extended MUB norm statement of Conjecture 1 in arXiv:2303.11382v1. -/
def claim : Prop :=
  ∀ (d : ℕ) (C : Matrix (Fin d) (Fin d) ℝ) (μ lam : ℝ),
    2 ≤ d → DoublyStochastic C → 0 < μ → μ < 1 → 0 < lam → lam < 1 →
    sigma2 C ^ 2 ≤ ((1 - μ) / μ) * ((1 - lam) / lam) →
    opNorm C (1 / μ) (1 / (1 - lam)) = (d : ℝ) ^ (1 - lam - μ)

/-- The prescribed witness I/2 + J/6. -/
private def witnessC : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => (if i = j then 1 / 2 else 0) + 1 / 6

private def witnessX : Fin 3 → ℝ := ![4, 1, 1]

/-- The extended MUB conjecture is false: the matrix I/2 + J/6 and x = (4,1,1)
at mu = lambda = 2/3 give a norm ratio whose cube is 27/80 > 1/3. -/
theorem result : ¬ claim := by
  have witness_stochastic : DoublyStochastic witnessC := by
    rw [DoublyStochastic, mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      dsimp [witnessC, Matrix.of_apply]
      split_ifs <;> norm_num
    · intro i
      fin_cases i <;> simp [Matrix.of_apply, witnessC, Fin.sum_univ_three] <;> norm_num
    · intro j
      fin_cases j <;> simp [Matrix.of_apply, witnessC, Fin.sum_univ_three] <;> norm_num
  have witness_gram : witnessCᴴ * witnessC =
      (Matrix.of fun i j : Fin 3 => (if i = j then (1 : ℝ) / 4 else 0) + 1 / 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.of_apply, witnessC, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  have witness_action : witnessC *ᵥ witnessX = ![3, 3 / 2, 3 / 2] := by
    ext i
    fin_cases i <;> simp [Matrix.of_apply, witnessC, witnessX, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  have lpNorm_eq_piLp {d : ℕ} (p : ℝ) (hp : 0 < p) (x : Fin d → ℝ) :
      lpNorm p x = ‖toLp (ENNReal.ofReal p) x‖ := by
    rw [PiLp.norm_eq_sum (by simpa [ENNReal.toReal_ofReal hp.le] using hp)]
    simp [lpNorm, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  have witness_charpoly : (witnessCᴴ * witnessC).charpoly =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (1 / 4 : ℝ)) ^ 2 := by
    apply Polynomial.funext
    intro t
    rw [Matrix.eval_charpoly, witness_gram, Matrix.det_fin_three]
    dsimp [Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.sub_apply, Pi.sub_apply]
    norm_num
    ring
  have witness_eigenvalues :
      List.ofFn (Matrix.isHermitian_conjTranspose_mul_self witnessC).eigenvalues₀ =
        [1, 1 / 4, 1 / 4] := by
    rw [← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀, witness_charpoly]
    have hne : (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C (1 / 4 : ℝ)) ^ 2 ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
    rw [Polynomial.roots_mul hne, Polynomial.roots_pow, Polynomial.roots_X_sub_C,
      Polynomial.roots_X_sub_C]
    have hm : ({1} + 2 • ({1 / 4} : Multiset ℝ)) =
        ([1, 1 / 4, 1 / 4] : List ℝ) := by
      change ({1} : Multiset ℝ) + 2 • {1 / 4} = {1} + ({1 / 4} + {1 / 4})
      rw [two_nsmul]
    rw [hm, Multiset.map_coe, Multiset.coe_sort]
    exact List.mergeSort_eq_self (fun a b : ℝ => b ≤ a) (by norm_num [List.pairwise_cons])
  have witness_sigma : sigma2 witnessC = 1 / 2 := by
    have h := congrArg (fun l : List ℝ => l[1]!) witness_eigenvalues
    simp only [one_div] at h
    unfold sigma2
    rw [dif_pos (by norm_num)]
    have hh : (Matrix.isHermitian_conjTranspose_mul_self witnessC).eigenvalues₀
        (⟨1, by norm_num⟩ : Fin (Fintype.card (Fin 3))) = 1 / 4 := by
      convert h using 1
      · congr 1
      · norm_num
    rw [hh]
    norm_num
  have ratios_bddAbove {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ)
      (p q : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q) : BddAbove (ratios C p q) := by
    have : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by simpa using ENNReal.ofReal_le_ofReal hq⟩
    let T := (Matrix.toLpLin (ENNReal.ofReal p) (ENNReal.ofReal q) C).toContinuousLinearMap
    refine ⟨‖T‖, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hxp : 0 < ‖toLp (ENNReal.ofReal p) x‖ := norm_pos_iff.mpr (by simpa using hx)
    rw [lpNorm_eq_piLp p (by linarith), lpNorm_eq_piLp q (by linarith)]
    apply (div_le_iff₀ hxp).mpr
    simpa [T, LinearMap.coe_toContinuousLinearMap', Matrix.toLpLin_apply] using
      T.le_opNorm (toLp (ENNReal.ofReal p) x)
  have norm_cube {d : ℕ} (x : Fin d → ℝ) :
      lpNorm 3 x ^ 3 = ∑ i, |x i| ^ (3 : ℕ) := by
    unfold lpNorm
    rw [← Real.rpow_mul_natCast (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))]
    norm_num [Real.rpow_natCast]
  have four_three_halves : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
    norm_num
  have witness_input_cube : lpNorm (3 / 2) witnessX ^ 3 = 100 := by
    have hs : (∑ i, |witnessX i| ^ (3 / 2 : ℝ)) = 10 := by
      simp [witnessX, Fin.sum_univ_three, four_three_halves]
      norm_num
    unfold lpNorm
    rw [hs, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num [Real.rpow_two]
  have witness_output_cube : lpNorm 3 (witnessC *ᵥ witnessX) ^ 3 = 135 / 4 := by
    rw [norm_cube, witness_action]
    simp [Fin.sum_univ_three]
    norm_num
  have witness_ratio_cube :
      (lpNorm 3 (witnessC *ᵥ witnessX) / lpNorm (3 / 2) witnessX) ^ 3 = 27 / 80 := by
    rw [div_pow, witness_input_cube, witness_output_cube]
    norm_num
  have prediction_cube : ((3 : ℝ) ^ (-1 / 3 : ℝ)) ^ 3 = 1 / 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [Real.rpow_neg_one]
  -- The prescribed norm ratio exceeds the MUB prediction.
  have witness_ratio_gt : (3 : ℝ) ^ (-1 / 3 : ℝ) <
      lpNorm 3 (witnessC *ᵥ witnessX) / lpNorm (3 / 2) witnessX := by
    apply lt_of_pow_lt_pow_left₀ 3
    · apply div_nonneg <;> unfold lpNorm <;> positivity
    · rw [prediction_cube, witness_ratio_cube]
      norm_num
  intro h
  have hcond : sigma2 witnessC ^ 2 ≤
      ((1 - (2 / 3 : ℝ)) / (2 / 3)) * ((1 - (2 / 3 : ℝ)) / (2 / 3)) := by
    rw [witness_sigma]
    norm_num
  have heq := h 3 witnessC (2 / 3) (2 / 3) (by norm_num) witness_stochastic
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcond
  have hvalue : opNorm witnessC (3 / 2) 3 = (3 : ℝ) ^ (-1 / 3 : ℝ) := by
    convert heq using 1 <;> norm_num
  have hx : witnessX ≠ 0 := by
    intro hz
    have := congrFun hz 0
    norm_num [witnessX] at this
  have hle : lpNorm 3 (witnessC *ᵥ witnessX) / lpNorm (3 / 2) witnessX ≤
      opNorm witnessC (3 / 2) 3 :=
    le_csSup (ratios_bddAbove witnessC (3 / 2) 3 (by norm_num) (by norm_num))
      ⟨witnessX, hx, rfl⟩
  rw [hvalue] at hle
  exact (not_le_of_gt witness_ratio_gt) hle
end D5.S3.Quantum.Information.ExtendedMubNormRefutation
