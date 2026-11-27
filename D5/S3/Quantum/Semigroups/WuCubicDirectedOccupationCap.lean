/- GID: D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxationClaim; result=D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxation_refuted; claim=D5/S3/Quantum/Semigroups/WuCubicDirectedOccupationCap.strengthenedRelaxationClaim
   digest: Directed CAR occupation bounds exclude a negative cubic deficit allowed by the scalar relaxation. -/

import D5.S3.Quantum.Semigroups.WuCubicSpectralCertificate
import Mathlib.Analysis.Normed.Lp.ProdLp
import OmegaBuild.Commands

/-!
# Directed occupation cap for the Wu cubic inequality

The two CAR lowering amplitudes split into transitions from the odd sector to the
empty state and from the full state to the odd sector. The resulting directed
bound excludes a table admitted by the scalar relaxation with a marginal cap.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker Matrix

namespace D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

open WuCubicOccupationEnvelope (CARConstraints edgeSum orientationMoment scaledCubicEnergy
  spectrumOf sym)
open WuCubicSpectralCertificate (ascendingIndex)
open WuModularEdgeSpectral (edgeWeight)

abbrev Mat := Matrix (Fin 4) (Fin 4) ℂ

private abbrev occupationBasis : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

private theorem basis_zero : occupationBasis.symm 0 = (0, 0) := rfl
private theorem basis_one : occupationBasis.symm 1 = (0, 1) := rfl
private theorem basis_two : occupationBasis.symm 2 = (1, 0) := rfl
private theorem basis_three : occupationBasis.symm 3 = (1, 1) := rfl

/-- The two physical lowering jumps in the order used by the repository.
The second is the negative of the convention \(E_{01}-E_{23}\), which
has the same squared weight. -/
def lowering (k : Fin 2) : Mat :=
  Matrix.reindex occupationBasis occupationBasis (TwistedTwoModeOUComparison.modeJump k)

private theorem lowering_zero :
    lowering 0 = !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  change Matrix.reindex occupationBasis occupationBasis
    ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis_zero, basis_one, basis_two, basis_three, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply]

private theorem lowering_one :
    lowering 1 = !![0, -1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] := by
  change Matrix.reindex occupationBasis occupationBasis
    (diagonal (![-1, 1] : Fin 2 → ℂ) ⊗ₖ
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [basis_zero, basis_one, basis_two, basis_three, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply]

def emptyProbability (x : Fin 4 → ℂ) : ℝ := Complex.normSq (x 0)

def fullProbability (x : Fin 4 → ℂ) : ℝ := Complex.normSq (x 3)

def oddProbability (x : Fin 4 → ℂ) : ℝ := Complex.normSq (x 1) + Complex.normSq (x 2)

def evenProbability (x : Fin 4 → ℂ) : ℝ := emptyProbability x + fullProbability x

/-- The first vector is the target of the jumps. -/
def jumpWeight (x y : Fin 4 → ℂ) : ℝ :=
  ∑ k : Fin 2, Complex.normSq ((lowering k *ᵥ y) ⬝ᵥ star x)

private theorem lowering_amplitudes (x y : Fin 4 → ℂ) :
    ((lowering 0 *ᵥ y) ⬝ᵥ star x) = star (x 0) * y 2 + star (x 1) * y 3 ∧
    ((lowering 1 *ᵥ y) ⬝ᵥ star x) = -(star (x 0) * y 1) + star (x 2) * y 3 := by
  constructor
  · rw [lowering_zero]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply]
    ring
  · rw [lowering_one]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply]
    ring

/-- The squared Euclidean triangle inequality applied to the two occupation blocks.
The vectors are arbitrary complex vectors, with no normalization or orthogonality premise. -/
private theorem jumpWeight_le_sqrt (x y : Fin 4 → ℂ) :
    jumpWeight x y ≤
      (Real.sqrt (emptyProbability x * oddProbability y) +
        Real.sqrt (oddProbability x * fullProbability y)) ^ 2 := by
  let X : WithLp 2 (ℂ × ℂ) :=
    WithLp.toLp 2 (star (x 0) * y 2, -(star (x 0) * y 1))
  let Y : WithLp 2 (ℂ × ℂ) :=
    WithLp.toLp 2 (star (x 1) * y 3, star (x 2) * y 3)
  have hX : ‖X‖ ^ 2 = emptyProbability x * oddProbability y := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [X, WithLp.toLp_fst, WithLp.toLp_snd, Complex.sq_norm,
      Complex.normSq_neg, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      emptyProbability, oddProbability]
    ring
  have hY : ‖Y‖ ^ 2 = oddProbability x * fullProbability y := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [Y, WithLp.toLp_fst, WithLp.toLp_snd, Complex.sq_norm,
      Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, fullProbability,
      oddProbability]
    ring
  have hsum : ‖X + Y‖ ^ 2 = jumpWeight x y := by
    rw [WithLp.prod_norm_sq_eq_of_L2, jumpWeight, Fin.sum_univ_two,
      (lowering_amplitudes x y).1, (lowering_amplitudes x y).2]
    simp only [Complex.sq_norm, WithLp.add_fst, WithLp.add_snd, X, Y,
      WithLp.toLp_fst, WithLp.toLp_snd]
  have hx : ‖X‖ = Real.sqrt (emptyProbability x * oddProbability y) := by
    rw [← hX, Real.sqrt_sq (norm_nonneg X)]
  have hy : ‖Y‖ = Real.sqrt (oddProbability x * fullProbability y) := by
    rw [← hY, Real.sqrt_sq (norm_nonneg Y)]
  have h := pow_le_pow_left₀ (norm_nonneg (X + Y)) (norm_add_le X Y) 2
  simpa only [hsum, hx, hy] using h

/-- The directed occupation cap in a form affine in the two occupation products. -/
theorem jumpWeight_le (x y : Fin 4 → ℂ) {t : ℝ} (ht : 0 < t) :
    jumpWeight x y ≤ (1 + t) * emptyProbability x * oddProbability y +
      (1 + 1 / t) * oddProbability x * fullProbability y := by
  let A := emptyProbability x * oddProbability y
  let B := oddProbability x * fullProbability y
  let u := Real.sqrt A
  let v := Real.sqrt B
  have hA : 0 ≤ A := mul_nonneg (Complex.normSq_nonneg _)
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  have hB : 0 ≤ B := mul_nonneg
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)
  have hcancel : (1 + 1 / t) * t = t + 1 := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ ht.ne']
  calc
    jumpWeight x y ≤ (u + v) ^ 2 := jumpWeight_le_sqrt x y
    _ ≤ (1 + t) * u ^ 2 + (1 + 1 / t) * v ^ 2 := by
      apply (mul_le_mul_iff_left₀ ht).mp
      calc
        (u + v) ^ 2 * t ≤ ((1 + t) * t) * u ^ 2 + (t + 1) * v ^ 2 := by
          nlinarith only [sq_nonneg (t * u - v)]
        _ = ((1 + t) * u ^ 2 + (1 + 1 / t) * v ^ 2) * t := by
          rw [add_mul ((1 + t) * u ^ 2) ((1 + 1 / t) * v ^ 2) t,
            mul_right_comm (1 + t) (u ^ 2) t,
            mul_right_comm (1 + 1 / t) (v ^ 2) t, hcancel]
    _ = (1 + t) * emptyProbability x * oddProbability y +
        (1 + 1 / t) * oddProbability x * fullProbability y := by
      change (1 + t) * (Real.sqrt A) ^ 2 + (1 + 1 / t) * (Real.sqrt B) ^ 2 = _
      rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
      simp only [A, B, mul_assoc]

/-! ## The physical marginals in an arbitrary complex frame -/

def frameVector (U : unitary Mat) (i : Fin 4) : Fin 4 → ℂ :=
  fun a => (U : Mat) a i

private abbrev inFrame (U : unitary Mat) : Mat ≃⋆ₐ[ℂ] Mat :=
  (Unitary.conjStarAlgAut ℂ Mat U).symm

private theorem inFrame_entry (U : unitary Mat) (A : Mat) (i j : Fin 4) :
    inFrame U A i j = (A *ᵥ frameVector U j) ⬝ᵥ star (frameVector U i) := by
  rw [Unitary.conjStarAlgAut_symm_apply, Matrix.mul_assoc]
  simp only [frameVector, Matrix.mul_apply, Matrix.star_apply, Matrix.mulVec, dotProduct,
    Pi.star_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def frameWeight (U : unitary Mat) (i j : Fin 4) : ℝ :=
  ∑ k : Fin 2, Complex.normSq (inFrame U (lowering k) i j)

theorem frameWeight_eq_jumpWeight (U : unitary Mat) (i j : Fin 4) :
    frameWeight U i j = jumpWeight (frameVector U i) (frameVector U j) := by
  simp only [frameWeight, jumpWeight, inFrame_entry]

/-- Apply the same bound to the spectral weights with the published index order. -/
private theorem spectralWeight_le {ρ : Mat} (hρ : ρ.IsHermitian) (i j : Fin 4) {t : ℝ} (ht : 0 < t) :
    (∑ k : Fin 2, edgeWeight hρ (lowering k) (ascendingIndex i) (ascendingIndex j)) ≤
      (1 + t) * emptyProbability (frameVector hρ.eigenvectorUnitary (ascendingIndex i)) *
        oddProbability (frameVector hρ.eigenvectorUnitary (ascendingIndex j)) +
      (1 + 1 / t) * oddProbability (frameVector hρ.eigenvectorUnitary (ascendingIndex i)) *
        fullProbability (frameVector hρ.eigenvectorUnitary (ascendingIndex j)) := by
  change frameWeight hρ.eigenvectorUnitary (ascendingIndex i) (ascendingIndex j) ≤ _
  rw [frameWeight_eq_jumpWeight]
  exact jumpWeight_le _ _ ht

private def charge : Mat := diagonal ![-1, 0, 0, 1]

private theorem lowering_occupations :
    lowering 0 * (lowering 0)ᴴ + lowering 1 * (lowering 1)ᴴ = 1 - charge ∧
    (lowering 0)ᴴ * lowering 0 + (lowering 1)ᴴ * lowering 1 = 1 + charge := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [lowering_zero, lowering_one, charge, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_apply]

private theorem inFrame_charge_re (U : unitary Mat) (i : Fin 4) :
    (inFrame U charge i i).re =
      fullProbability (frameVector U i) - emptyProbability (frameVector U i) := by
  rw [inFrame_entry]
  norm_num [charge, fullProbability, emptyProbability, Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_four, Pi.star_apply, Complex.star_def, Complex.mul_conj, neg_mul,
    Complex.neg_re, Complex.add_re, Complex.sub_re]
  ring

private theorem row_normSq (A : Mat) (i : Fin 4) :
    (∑ j, Complex.normSq (A i j)) = ((A * Aᴴ) i i).re := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]

private theorem column_normSq (A : Mat) (i : Fin 4) :
    (∑ j, Complex.normSq (A j i)) = ((Aᴴ * A) i i).re := by
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.normSq_conj] using row_normSq Aᴴ i

private theorem frameWeight_marginals (U : unitary Mat) (i : Fin 4) :
    (∑ j, frameWeight U i j) = 1 - (inFrame U charge i i).re ∧
    (∑ j, frameWeight U j i) = 1 + (inFrame U charge i i).re := by
  have adjoint (A : Mat) : inFrame U Aᴴ = (inFrame U A)ᴴ := map_star (inFrame U) A
  have hr (k : Fin 2) :
      (∑ j, Complex.normSq (inFrame U (lowering k) i j)) =
        (inFrame U (lowering k * (lowering k)ᴴ) i i).re := by
    rw [row_normSq, map_mul, adjoint]
  have hc (k : Fin 2) :
      (∑ j, Complex.normSq (inFrame U (lowering k) j i)) =
        (inFrame U ((lowering k)ᴴ * lowering k) i i).re := by
    rw [column_normSq, map_mul, adjoint]
  constructor
  · unfold frameWeight
    rw [Finset.sum_comm]
    simp only [hr, Fin.sum_univ_two]
    rw [← Complex.add_re, ← Matrix.add_apply, ← map_add, lowering_occupations.1,
      map_sub, Matrix.sub_apply, Complex.sub_re, map_one, Matrix.one_apply_eq, Complex.one_re]
  · unfold frameWeight
    rw [Finset.sum_comm]
    simp only [hc, Fin.sum_univ_two]
    rw [← Complex.add_re, ← Matrix.add_apply, ← map_add, lowering_occupations.2,
      map_add, Matrix.add_apply, Complex.add_re, map_one, Matrix.one_apply_eq, Complex.one_re]

def rowImbalance (w : Fin 4 → Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (∑ j, w i j) - (∑ j, w j i)

theorem frameWeight_rowImbalance (U : unitary Mat) (i : Fin 4) :
    rowImbalance (frameWeight U) i =
      2 * (emptyProbability (frameVector U i) - fullProbability (frameVector U i)) := by
  rw [rowImbalance, (frameWeight_marginals U i).1, (frameWeight_marginals U i).2,
    inFrame_charge_re]
  ring

theorem frameWeight_abs_rowImbalance_le (U : unitary Mat) (i : Fin 4) :
    |rowImbalance (frameWeight U) i| ≤ 2 * evenProbability (frameVector U i) := by
  rw [frameWeight_rowImbalance, evenProbability, abs_le]
  unfold emptyProbability fullProbability
  constructor <;> linarith only [Complex.normSq_nonneg (frameVector U i 0),
    Complex.normSq_nonneg (frameVector U i 3)]

private theorem odd_eq_one_sub_even (U : unitary Mat) (i : Fin 4) :
    oddProbability (frameVector U i) = 1 - evenProbability (frameVector U i) := by
  have h := column_normSq (U : Mat) i
  rw [show (U : Mat)ᴴ * (U : Mat) = 1 from Unitary.coe_star_mul_self U,
    Matrix.one_apply_eq, Complex.one_re, Fin.sum_univ_four] at h
  unfold oddProbability evenProbability emptyProbability fullProbability frameVector
  linarith only [h]

/-! ## A rational table in the strengthened scalar relaxation -/

def table : Fin 4 → Fin 4 → ℝ :=
  ![![1 / 4, 3 / 4, 1 / 2, 0],
    ![1 / 4, 1 / 4, 0, 1 / 2],
    ![0, 0, 1 / 4, 3 / 4],
    ![0, 0, 1 / 4, 1 / 4]]

def tableOccupation (_ : Fin 4) : ℝ := 1 / 2

def roots : Fin 4 → ℝ := ![43, 45, 73, 76]

def mass : ℝ := 998625

def spectrum : Fin 4 → ℝ := spectrumOf roots mass

def tableMoment : ℝ := (spectrum 3 - spectrum 0) / 2

private theorem spectrum_pos (i : Fin 4) : 0 < spectrum i := by
  fin_cases i <;> norm_num [spectrum, spectrumOf, roots, mass]

private theorem spectrum_sum : (∑ i, spectrum i) = 1 := by
  norm_num [Fin.sum_univ_four, spectrum, spectrumOf, roots, mass]

private theorem spectrum_strictMono : StrictMono spectrum := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    norm_num [spectrum, spectrumOf, roots, mass]

private theorem table_rowImbalance (i : Fin 4) :
    rowImbalance table i = (![1, 0, 0, -1] : Fin 4 → ℝ) i := by
  fin_cases i <;> norm_num [rowImbalance, table, Fin.sum_univ_four]

private theorem table_abs_rowImbalance_le (i : Fin 4) :
    |rowImbalance table i| ≤ 2 * tableOccupation i := by
  rw [table_rowImbalance]
  fin_cases i <;> norm_num [tableOccupation]

private theorem table_carConstraints : CARConstraints spectrum table tableOccupation tableMoment := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [table]
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_four, sym, table]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num [sym, table]
  · intro i
    fin_cases i <;> norm_num [table, tableOccupation]
  · intro i
    norm_num [tableOccupation, Set.mem_Icc]
  · norm_num [Fin.sum_univ_four, tableOccupation]
  · norm_num [orientationMoment, edgeSum, spectrum, spectrumOf, roots, mass, table, tableMoment]
  · intro v
    have hm : 0 ≤ tableMoment := by
      unfold tableMoment
      exact div_nonneg
        (sub_nonneg.mpr (spectrum_strictMono.monotone (by decide : (0 : Fin 4) ≤ 3)))
        (by norm_num)
    rw [abs_of_nonneg hm]
    have hends : spectrum 3 - spectrum 0 ≤ |spectrum 3 - v| + |spectrum 0 - v| := by
      calc
        spectrum 3 - spectrum 0 = (spectrum 3 - v) + (v - spectrum 0) := by ring
        _ ≤ |spectrum 3 - v| + |v - spectrum 0| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ = _ := by rw [abs_sub_comm v (spectrum 0)]
    simp only [Fin.sum_univ_four, tableOccupation, tableMoment]
    linarith only [hends, abs_nonneg (spectrum 1 - v), abs_nonneg (spectrum 2 - v)]

/-- The edge \(01\) is forbidden for every complex orthonormal frame with these probabilities. -/
theorem table_no_unitary_realization :
    ¬ ∃ U : unitary Mat, frameWeight U = table ∧
      ∀ i, evenProbability (frameVector U i) = tableOccupation i := by
  rintro ⟨U, hw, he⟩
  have hrow0 := frameWeight_rowImbalance U 0
  have hrow1 := frameWeight_rowImbalance U 1
  rw [hw, table_rowImbalance] at hrow0 hrow1
  norm_num at hrow0 hrow1
  have he0 := he 0
  have he1 := he 1
  simp only [evenProbability, tableOccupation] at he0 he1
  have ha0 : emptyProbability (frameVector U 0) = 1 / 2 := by
    linarith only [hrow0, he0]
  have hb1 : fullProbability (frameVector U 1) = 1 / 4 := by
    linarith only [hrow1, he1]
  have ho (i : Fin 4) : oddProbability (frameVector U i) = 1 / 2 := by
    rw [odd_eq_one_sub_even, he i, tableOccupation]
    norm_num
  have h01 := jumpWeight_le (frameVector U 0) (frameVector U 1)
    (t := 2 / 3) (by norm_num)
  rw [← frameWeight_eq_jumpWeight U 0 1, ha0, hb1, ho 0, ho 1] at h01
  have hcap : frameWeight U 0 1 ≤ 35 / 48 := h01.trans (by norm_num)
  rw [hw] at hcap
  norm_num [table] at hcap

/-! ## Strict deficit at the normalized spectrum -/

def temperature : ℝ := 3 * Real.log (21 / 20)

private theorem temperature_pos : 0 < temperature :=
  mul_pos (by norm_num) (Real.log_pos (by norm_num))

def entropyConstant : ℝ :=
  (∑ i, spectrum i * Real.log (4 * spectrum i)) + 2 * Real.log (Real.cosh temperature)

private def thermalFactor : ℝ :=
  (Real.cosh temperature - Real.cosh (temperature / 3)) *
    Real.cosh temperature / Real.sinh temperature

/-- This is the ordinary cubic deficit scaled by \(4\cosh(h)/9\).
Here \(H=\mathrm{entropyConstant}-2hm\) and the scaled sharp coefficient
is \(F/(2h)\) with \(F=\mathrm{thermalFactor}\). -/
def normalizedCubicDeficit (w : Fin 4 → Fin 4 → ℝ) (m : ℝ) : ℝ :=
  scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
    (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots mass w -
    thermalFactor / (2 * temperature) * (entropyConstant - 2 * temperature * m)

private theorem normalizedCubicDeficit_eq (w : Fin 4 → Fin 4 → ℝ) (m : ℝ) :
    normalizedCubicDeficit w m =
      scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
        (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots mass w +
        thermalFactor * m - thermalFactor * entropyConstant / (2 * temperature) := by
  unfold normalizedCubicDeficit
  field_simp [temperature_pos.ne']
  ring

private theorem exp_temperature : Real.exp temperature = 9261 / 8000 := by
  unfold temperature
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
    Real.exp_log (by norm_num)]
  norm_num

private theorem exp_third : Real.exp (temperature / 3) = 21 / 20 := by
  rw [show temperature / 3 = Real.log (21 / 20) by unfold temperature; ring]
  exact Real.exp_log (by norm_num)

private theorem cosh_temperature : Real.cosh temperature = 149766121 / 148176000 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_temperature]
  norm_num

private theorem sinh_temperature : Real.sinh temperature = 21766121 / 148176000 := by
  rw [Real.sinh_eq, Real.exp_neg, exp_temperature]
  norm_num

private theorem cosh_third : Real.cosh (temperature / 3) = 841 / 840 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_third]
  norm_num

private theorem sinh_third : Real.sinh (temperature / 3) = 41 / 840 := by
  rw [Real.sinh_eq, Real.exp_neg, exp_third]
  norm_num

private theorem thermalFactor_eq : thermalFactor = 5164085618201 / 78663823056000 := by
  norm_num [thermalFactor, cosh_temperature, cosh_third, sinh_temperature]

private theorem affineEnergy_eq :
    scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
      (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots mass table +
      thermalFactor * tableMoment = 56324886644826199 / 1047408803990640000 := by
  norm_num [scaledCubicEnergy, Fin.sum_univ_four, spectrum, spectrumOf, roots, mass, table,
    tableMoment, cosh_temperature, sinh_temperature, cosh_third, sinh_third, thermalFactor_eq]

-- Five terms and the exact geometric tail bound suffice for the strict rational margin.
private theorem log_enclosure (z x : ℝ) (hz : |z| < 1) (hx : (1 + z) / (1 - z) = x) :
    |1 / 2 * Real.log x - ∑ j ∈ Finset.range 5, z ^ (2 * j + 1) / (2 * j + 1)| ≤
      |z| ^ 11 / (1 - z ^ 2) := by
  simpa only [hx] using Real.sum_range_sub_log_div_le hz 5

private theorem log_lower (z x L : ℝ) (hz : |z| < 1) (hx : (1 + z) / (1 - z) = x)
    (hL : L ≤ 2 * ((∑ j ∈ Finset.range 5, z ^ (2 * j + 1) / (2 * j + 1)) -
      |z| ^ 11 / (1 - z ^ 2))) : L ≤ Real.log x := by
  linarith only [hL, (abs_le.mp (log_enclosure z x hz hx)).1]

private theorem log_base_upper : Real.log (21 / 20) ≤ 487902 / 10000000 := by
  have h := (abs_le.mp (log_enclosure (1 / 41) (21 / 20) (by norm_num) (by norm_num))).2
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

private theorem entropyConstant_lower : 2589 / 10000 ≤ entropyConstant := by
  have h0 := log_lower (-680597 / 1316653) (318028 / 998625) (-1146 / 1000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h1 := log_lower (-1691 / 3635) (972 / 2663) (-10084 / 10000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h2 := log_lower (557443 / 2554693) (1556068 / 998625) (4435 / 10000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h3 := log_lower (757279 / 2754529) (1755904 / 998625) (5643 / 10000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have hC := log_lower (1590121 / 297942121) (149766121 / 148176000) (1067 / 100000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  norm_num [entropyConstant, Fin.sum_univ_four, spectrum, spectrumOf, roots, mass,
    cosh_temperature] at h0 h1 h2 h3 hC ⊢
  linarith only [h0, h1, h2, h3, hC]

private theorem table_normalizedCubicDeficit_lt :
    normalizedCubicDeficit table tableMoment < -(1 / 250 : ℝ) := by
  have hF : 0 < thermalFactor := by norm_num [thermalFactor_eq]
  have hden : 0 < 2 * temperature := mul_pos (by norm_num) temperature_pos
  have hden_upper : 2 * temperature ≤ 6 * (487902 / 10000000) := by
    unfold temperature
    linarith only [log_base_upper]
  have hquot :
      thermalFactor * (2589 / 10000) / (6 * (487902 / 10000000)) ≤
        thermalFactor * entropyConstant / (2 * temperature) := by
    calc
      _ ≤ thermalFactor * (2589 / 10000) / (2 * temperature) :=
        div_le_div_of_nonneg_left (mul_nonneg hF.le (by norm_num)) hden hden_upper
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left entropyConstant_lower hF.le) hden.le
  calc
    normalizedCubicDeficit table tableMoment ≤
        56324886644826199 / 1047408803990640000 -
          thermalFactor * (2589 / 10000) / (6 * (487902 / 10000000)) := by
      rw [normalizedCubicDeficit_eq, affineEnergy_eq]
      exact sub_le_sub_left hquot _
    _ < -(1 / 250 : ℝ) := by norm_num [thermalFactor_eq]

/-- The proposed deficit bound under the scalar CAR and marginal-imbalance constraints. -/
def strengthenedRelaxationClaim : Prop :=
  ∀ (w : Fin 4 → Fin 4 → ℝ) (e : Fin 4 → ℝ) (m : ℝ),
    CARConstraints spectrum w e m → (∀ i, |rowImbalance w i| ≤ 2 * e i) →
    -(1 / 250 : ℝ) ≤ normalizedCubicDeficit w m

/-- The displayed table gives a normalized scalar deficit strictly below \(-1/250\). -/
theorem strengthenedRelaxation_refuted : ¬ strengthenedRelaxationClaim := by
  unfold strengthenedRelaxationClaim
  intro h
  exact (not_le.mpr table_normalizedCubicDeficit_lt)
    (h table tableOccupation tableMoment table_carConstraints table_abs_rowImbalance_le)

/-! ## Positive deficit for frames with balanced even occupation -/

/-- The expectation of the number operator minus the identity at this spectrum. -/
def frameMoment (U : unitary Mat) : ℝ :=
  ∑ i, spectrum i *
    (fullProbability (frameVector U i) - emptyProbability (frameVector U i))

private theorem frameMoment_eq_imbalance (U : unitary Mat) :
    frameMoment U = -(∑ i, spectrum i * rowImbalance (frameWeight U) i) / 2 := by
  simp only [frameMoment, frameWeight_rowImbalance, Fin.sum_univ_four]
  ring

private theorem jumpWeight_self (x : Fin 4 → ℂ) :
    jumpWeight x x = evenProbability x * oddProbability x := by
  obtain ⟨h0, h1⟩ := lowering_amplitudes x x
  rw [jumpWeight, Fin.sum_univ_two, h0, h1]
  simp only [evenProbability, emptyProbability, fullProbability, oddProbability,
    Complex.normSq_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im]
  ring

private def leadingPairImbalance (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (rowImbalance w 0 + rowImbalance w 1) / 2

private theorem balanced_leadingPair_cap (U : unitary Mat)
    (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) {t : ℝ} (ht : 0 < t) :
    sym (frameWeight U) 0 1 ≤
      (1 + t) * (1 + leadingPairImbalance (frameWeight U)) / 4 +
      (1 + 1 / t) * (1 - leadingPairImbalance (frameWeight U)) / 4 := by
  have ho (i : Fin 4) : oddProbability (frameVector U i) = 1 / 2 := by
    rw [odd_eq_one_sub_even, he i]
    norm_num
  have h01 := jumpWeight_le (frameVector U 0) (frameVector U 1) ht
  have h10 := jumpWeight_le (frameVector U 1) (frameVector U 0) ht
  rw [← frameWeight_eq_jumpWeight, ho 0, ho 1] at h01 h10
  have h0 := he 0
  have h1 := he 1
  unfold evenProbability at h0 h1
  simp only [sym, leadingPairImbalance, frameWeight_rowImbalance]
  linear_combination h01 + h10
    + ((1 + t) / 4 + (1 + 1 / t) / 4) * (h0 + h1)

-- The four combined marginals and the four diagonals reduce the symmetric cost to
-- three matching weights. The directed cap at the rational parameter 883/1250
-- bounds the cheapest matching. Nonnegativity pays for the reverse-edge cost.
private theorem balanced_affineEnergy_lower (w : Fin 4 → Fin 4 → ℝ)
    (hrows : ∀ i, (∑ j, sym w i j) = 2)
    (hdiag : ∀ i, w i i = 1 / 4)
    (hnonneg : ∀ i j, 0 ≤ w i j)
    (himb0 : rowImbalance w 0 ≤ 1) (himb3 : -1 ≤ rowImbalance w 3)
    (hq : |leadingPairImbalance w| ≤ 1)
    (hcap : sym w 0 1 ≤
      (1 + (883 / 1250 : ℝ)) * (1 + leadingPairImbalance w) / 4 +
      (1 + 1 / (883 / 1250 : ℝ)) * (1 - leadingPairImbalance w) / 4) :
    6013 / 100000 ≤
      scaledCubicEnergy (Real.cosh temperature) (Real.sinh temperature)
        (Real.cosh (temperature / 3)) (Real.sinh (temperature / 3)) roots mass w +
      thermalFactor * (-(∑ i, spectrum i * rowImbalance w i) / 2) := by
  have hr0 := hrows 0
  have hr1 := hrows 1
  have hr2 := hrows 2
  have hr3 := hrows 3
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hq
  norm_num [scaledCubicEnergy, cosh_temperature, sinh_temperature, cosh_third, sinh_third,
    thermalFactor_eq, spectrum, spectrumOf, roots, mass, Fin.sum_univ_four, hdiag,
    sym, rowImbalance, leadingPairImbalance] at hr0 hr1 hr2 hr3 himb0 himb3 hqlo hqhi hcap ⊢
  linarith only [hr0, hr1, hr2, hr3, himb0, himb3, hqlo, hqhi, hcap,
    hnonneg 0 3, hnonneg 3 0, hnonneg 1 0, hnonneg 2 0, hnonneg 2 1,
    hnonneg 3 1, hnonneg 3 2]

private theorem log_upper (z x H : ℝ) (hz : |z| < 1) (hx : (1 + z) / (1 - z) = x)
    (hH : 2 * ((∑ j ∈ Finset.range 8, z ^ (2 * j + 1) / (2 * j + 1)) +
      |z| ^ 17 / (1 - z ^ 2)) ≤ H) : Real.log x ≤ H := by
  have h := abs_le.mp (Real.sum_range_sub_log_div_le hz 8)
  rw [hx] at h
  linarith only [hH, h.2]

private theorem entropyConstant_upper : entropyConstant ≤ 25915 / 100000 := by
  have h0 := log_upper (-680597 / 1316653) (318028 / 998625) (-1144201 / 1000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h1 := log_upper (-1691 / 3635) (972 / 2663) (-1007846 / 1000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h2 := log_upper (557443 / 2554693) (1556068 / 998625) (443539 / 1000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have h3 := log_upper (757279 / 2754529) (1755904 / 998625) (564360 / 1000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have hC := log_upper (1590121 / 297942121) (149766121 / 148176000) (1067413 / 100000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  norm_num [entropyConstant, Fin.sum_univ_four, spectrum, spectrumOf, roots, mass,
    cosh_temperature] at h0 h1 h2 h3 hC ⊢
  linarith only [h0, h1, h2, h3, hC]

private theorem entropyTerm_upper :
    thermalFactor * entropyConstant / (2 * temperature) ≤ 5812 / 100000 := by
  have hF : 0 ≤ thermalFactor := by norm_num [thermalFactor_eq]
  have hlog := log_lower (1 / 41) (21 / 20) (4879016 / 100000000)
    (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ])
  have hden : 6 * (4879016 / 100000000) ≤ 2 * temperature := by
    unfold temperature
    linarith only [hlog]
  calc
    _ ≤ thermalFactor * (25915 / 100000) / (2 * temperature) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left entropyConstant_upper hF)
        (mul_nonneg (by norm_num) temperature_pos.le)
    _ ≤ thermalFactor * (25915 / 100000) / (6 * (4879016 / 100000000)) :=
      div_le_div_of_nonneg_left (mul_nonneg hF (by norm_num)) (by norm_num) hden
    _ ≤ _ := by norm_num [thermalFactor_eq]

/-- At the obstruction spectrum and temperature, all complex frames with even
occupation probability one half have normalized cubic deficit greater than \(1/500\). -/
theorem balancedFrame_normalizedCubicDeficit_gt (U : unitary Mat)
    (he : ∀ i, evenProbability (frameVector U i) = 1 / 2) :
    1 / 500 < normalizedCubicDeficit (frameWeight U) (frameMoment U) := by
  have hrows (i : Fin 4) : (∑ j, sym (frameWeight U) i j) = 2 := by
    simp only [sym, Finset.sum_add_distrib, (frameWeight_marginals U i).1,
      (frameWeight_marginals U i).2]
    ring
  have hdiag (i : Fin 4) : frameWeight U i i = 1 / 4 := by
    rw [frameWeight_eq_jumpWeight, jumpWeight_self, odd_eq_one_sub_even, he i]
    norm_num
  have hnonneg (i j : Fin 4) : 0 ≤ frameWeight U i j :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have himb (i : Fin 4) : |rowImbalance (frameWeight U) i| ≤ 1 := by
    simpa [he i] using frameWeight_abs_rowImbalance_le U i
  have hq : |leadingPairImbalance (frameWeight U)| ≤ 1 := by
    have h0 := abs_le.mp (himb 0)
    have h1 := abs_le.mp (himb 1)
    rw [leadingPairImbalance, abs_le]
    constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2]
  have hcap := balanced_leadingPair_cap U he (t := 883 / 1250) (by norm_num)
  have henergy := balanced_affineEnergy_lower (frameWeight U) hrows hdiag hnonneg
    (abs_le.mp (himb 0)).2 (abs_le.mp (himb 3)).1 hq hcap
  rw [normalizedCubicDeficit_eq, frameMoment_eq_imbalance]
  linarith only [henergy, entropyTerm_upper]

end D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
