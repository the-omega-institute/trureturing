/- GID: D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable
   generality: G
   mirror-B: D5/B/S3/QuantumContext/SingularSupportCandidateDiagonalizable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive singular-support candidate columns admit an explicit real diagonalization. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped BigOperators Matrix

namespace D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable

/-- The Euclidean radius of the distinguished coordinate and the two remaining coordinates. -/
def r (z : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (z ^ 2 + p 0 ^ 2 + p 1 ^ 2)

/-- The positive two-dimensional support block before column normalization. -/
def gZero (z : ℝ) (p : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (z * r z p) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
    (r z p / (r z p + z)) • Matrix.vecMulVec p p

/-- The positive diagonal column-normalization matrix. -/
def H (z : ℝ) (p : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun j => p j / (r z p * Real.sqrt (z ^ 2 + p j ^ 2))

/-- The normalized two-dimensional support block. -/
def K (z : ℝ) (p : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  gZero z p * H z p

/-- The distinguished eigenvalue of the block candidate. -/
def q (z : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  (1 / r z p) * ∑ j, p j * Real.sqrt (z ^ 2 + p j ^ 2)

/-- The final positive column of the block candidate. -/
def u (z : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (1 / z) • ((q z p • (1 : Matrix (Fin 2) (Fin 2) ℝ) - K z p) *ᵥ p)

/-- The three-dimensional singular-support candidate in two-plus-one block coordinates. -/
def Q (z : ℝ) (p : Fin 2 → ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (K z p) (fun i _ => u z p i) 0 (fun _ _ => q z p)

/-- For positive input coordinates, both candidate columns are strictly positive and the block
candidate is similar over `ℝ` to a diagonal matrix whose two support eigenvalues lie strictly
between zero and the distinguished eigenvalue. -/
theorem singular_support_candidate_positive_and_diagonalizable
    (z : ℝ) (p : Fin 2 → ℝ) (hz : 0 < z) (hp : ∀ j, 0 < p j) :
    (∀ j, 0 < u z p j) ∧
      (∀ i j, 0 < K z p i j) ∧
        ∃ lambda1 lambda2 : ℝ,
          0 < lambda1 ∧ lambda1 < q z p ∧ 0 < lambda2 ∧ lambda2 < q z p ∧
            ∃ S : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ,
              IsUnit S.det ∧
                Q z p * S =
                  S * Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0
                    (fun _ _ => q z p) := by
  classical
  have hp0 : 0 < p 0 := hp 0
  have hp1 : 0 < p 1 := hp 1
  have hs0 : 0 < Real.sqrt (z ^ 2 + p 0 ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hs1 : 0 < Real.sqrt (z ^ 2 + p 1 ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hr : 0 < r z p := by
    rw [r, Real.sqrt_pos]
    positivity
  have hr_sq : (r z p) ^ 2 = z ^ 2 + p 0 ^ 2 + p 1 ^ 2 := by
    rw [r, Real.sq_sqrt]
    positivity
  have hs0_sq : (Real.sqrt (z ^ 2 + p 0 ^ 2)) ^ 2 = z ^ 2 + p 0 ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hs1_sq : (Real.sqrt (z ^ 2 + p 1 ^ 2)) ^ 2 = z ^ 2 + p 1 ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hrz : 0 < r z p + z := add_pos hr hz
  have hHdiag : ∀ j, 0 < H z p j j := by
    intro j
    fin_cases j
    · change 0 < p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2))
      positivity
    · change 0 < p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))
      positivity
  have hgZeroentry : ∀ i j, 0 < gZero z p i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · have hdiag :
          0 < z * r z p + r z p / (r z p + z) * (p 0 * p 0) :=
        add_pos (mul_pos hz hr) (mul_pos (div_pos hr hrz) (mul_pos hp0 hp0))
      simpa [gZero, Matrix.vecMulVec_apply] using hdiag
    · have hoff : 0 < r z p / (r z p + z) * (p 0 * p 1) :=
        mul_pos (div_pos hr hrz) (mul_pos hp0 hp1)
      simpa [gZero, Matrix.vecMulVec_apply] using hoff
    · have hoff : 0 < r z p / (r z p + z) * (p 1 * p 0) :=
        mul_pos (div_pos hr hrz) (mul_pos hp1 hp0)
      simpa [gZero, Matrix.vecMulVec_apply] using hoff
    · have hdiag :
          0 < z * r z p + r z p / (r z p + z) * (p 1 * p 1) :=
        add_pos (mul_pos hz hr) (mul_pos (div_pos hr hrz) (mul_pos hp1 hp1))
      simpa [gZero, Matrix.vecMulVec_apply] using hdiag
  have hKentry : ∀ i j, 0 < K z p i j := by
    intro i j
    have hKij : K z p i j = gZero z p i j * H z p j j := by
      fin_cases j <;> simp [K, H, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hKij]
    exact mul_pos (hgZeroentry i j) (hHdiag j)
  let h : Fin 2 → ℝ := fun j => H z p j j
  have hh0 : 0 < h 0 := hHdiag 0
  have hh1 : 0 < h 1 := hHdiag 1
  have hq_formula :
      q z p = z ^ 2 * (h 0 + h 1) + p 0 ^ 2 * h 0 + p 1 ^ 2 * h 1 := by
    have hterm0 :
        (z ^ 2 + p 0 ^ 2) * (p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2))) =
          (1 / r z p) * (p 0 * Real.sqrt (z ^ 2 + p 0 ^ 2)) := by
      calc
        _ = (Real.sqrt (z ^ 2 + p 0 ^ 2)) ^ 2 *
              (p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2))) := by rw [hs0_sq]
        _ = _ := by field_simp [hr.ne', hs0.ne']
    have hterm1 :
        (z ^ 2 + p 1 ^ 2) * (p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))) =
          (1 / r z p) * (p 1 * Real.sqrt (z ^ 2 + p 1 ^ 2)) := by
      calc
        _ = (Real.sqrt (z ^ 2 + p 1 ^ 2)) ^ 2 *
              (p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))) := by rw [hs1_sq]
        _ = _ := by field_simp [hr.ne', hs1.ne']
    simp only [q, h, H, Fin.sum_univ_two, Matrix.diagonal_apply, if_pos]
    rw [show z ^ 2 *
            (p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2)) +
              p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))) +
            p 0 ^ 2 * (p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2))) +
            p 1 ^ 2 * (p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))) =
          (z ^ 2 + p 0 ^ 2) *
              (p 0 / (r z p * Real.sqrt (z ^ 2 + p 0 ^ 2))) +
            (z ^ 2 + p 1 ^ 2) *
              (p 1 / (r z p * Real.sqrt (z ^ 2 + p 1 ^ 2))) by ring,
      hterm0, hterm1]
    ring
  have hKp_formula : ∀ i,
      (K z p *ᵥ p) i = z * r z p * h i * p i +
        r z p / (r z p + z) * p i * (p 0 ^ 2 * h 0 + p 1 ^ 2 * h 1) := by
    intro i
    fin_cases i <;>
      simp [K, gZero, H, h, Matrix.mulVec, Matrix.mul_apply, Matrix.vecMulVec_apply,
        Fin.sum_univ_two] <;> ring
  have hu0_formula :
      u z p 0 = p 0 *
        (z * h 1 + p 1 ^ 2 / (r z p + z) * (h 1 - h 0)) := by
    simp only [u, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hKp_formula 0, hq_formula]
    field_simp [hz.ne', hrz.ne']
    linear_combination (-z * h 0) * hr_sq
  have hu1_formula :
      u z p 1 = p 1 *
        (z * h 0 + p 0 ^ 2 / (r z p + z) * (h 0 - h 1)) := by
    simp only [u, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hKp_formula 1, hq_formula]
    field_simp [hz.ne', hrz.ne']
    linear_combination (-z * h 1) * hr_sq
  have hratio01_eq :
      h 0 / h 1 =
        p 0 * Real.sqrt (z ^ 2 + p 1 ^ 2) /
          (p 1 * Real.sqrt (z ^ 2 + p 0 ^ 2)) := by
    simp only [h, H, Matrix.diagonal_apply, if_pos]
    field_simp [hr.ne', hs0.ne', hs1.ne', hp0.ne', hp1.ne']
  have hratio10_eq :
      h 1 / h 0 =
        p 1 * Real.sqrt (z ^ 2 + p 0 ^ 2) /
          (p 0 * Real.sqrt (z ^ 2 + p 1 ^ 2)) := by
    simp only [h, H, Matrix.diagonal_apply, if_pos]
    field_simp [hr.ne', hs0.ne', hs1.ne', hp0.ne', hp1.ne']
  have hratio01 : h 0 / h 1 < Real.sqrt (1 + z ^ 2 / p 1 ^ 2) := by
    rw [hratio01_eq, ← sq_lt_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity)]
    field_simp [hp0.ne', hp1.ne', hs0.ne', hs1.ne']
    rw [hs0_sq, hs1_sq]
    nlinarith [sq_pos_of_pos hz]
  have hratio10 : h 1 / h 0 < Real.sqrt (1 + z ^ 2 / p 0 ^ 2) := by
    rw [hratio10_eq, ← sq_lt_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity)]
    field_simp [hp0.ne', hp1.ne', hs0.ne', hs1.ne']
    rw [hs0_sq, hs1_sq]
    nlinarith [sq_pos_of_pos hz]
  have hroot01 : Real.sqrt (1 + z ^ 2 / p 1 ^ 2) < 1 + z ^ 2 / p 1 ^ 2 := by
    rw [Real.sqrt_lt_self_iff]
    exact lt_add_of_pos_right 1 (div_pos (sq_pos_of_pos hz) (sq_pos_of_pos hp1))
  have hroot10 : Real.sqrt (1 + z ^ 2 / p 0 ^ 2) < 1 + z ^ 2 / p 0 ^ 2 := by
    rw [Real.sqrt_lt_self_iff]
    exact lt_add_of_pos_right 1 (div_pos (sq_pos_of_pos hz) (sq_pos_of_pos hp0))
  have hratio01_coarse : h 0 / h 1 < 1 + z ^ 2 / p 1 ^ 2 := hratio01.trans hroot01
  have hratio10_coarse : h 1 / h 0 < 1 + z ^ 2 / p 0 ^ 2 := hratio10.trans hroot10
  have hu0 : 0 < u z p 0 := by
    rw [hu0_formula]
    apply mul_pos hp0
    have hratio := (div_lt_iff₀ hh1).mp hratio01_coarse
    have hscaled : p 1 ^ 2 * h 0 < (p 1 ^ 2 + z ^ 2) * h 1 := by
      calc
        p 1 ^ 2 * h 0 < p 1 ^ 2 * ((1 + z ^ 2 / p 1 ^ 2) * h 1) :=
          mul_lt_mul_of_pos_left hratio (sq_pos_of_pos hp1)
        _ = (p 1 ^ 2 + z ^ 2) * h 1 := by field_simp [hp1.ne']
    have hgap : 0 < (p 1 ^ 2 + z ^ 2) * h 1 - p 1 ^ 2 * h 0 :=
      sub_pos.2 hscaled
    have hnum :
        0 < (r z p + z) * (z * h 1) + p 1 ^ 2 * (h 1 - h 0) := by
      rw [show (r z p + z) * (z * h 1) + p 1 ^ 2 * (h 1 - h 0) =
          r z p * z * h 1 + ((p 1 ^ 2 + z ^ 2) * h 1 - p 1 ^ 2 * h 0) by ring]
      exact add_pos (mul_pos (mul_pos hr hz) hh1) hgap
    have heq :
        z * h 1 + p 1 ^ 2 / (r z p + z) * (h 1 - h 0) =
          ((r z p + z) * (z * h 1) + p 1 ^ 2 * (h 1 - h 0)) /
            (r z p + z) := by
      field_simp [hrz.ne']
    rw [heq]
    exact div_pos hnum hrz
  have hu1 : 0 < u z p 1 := by
    rw [hu1_formula]
    apply mul_pos hp1
    have hratio := (div_lt_iff₀ hh0).mp hratio10_coarse
    have hscaled : p 0 ^ 2 * h 1 < (p 0 ^ 2 + z ^ 2) * h 0 := by
      calc
        p 0 ^ 2 * h 1 < p 0 ^ 2 * ((1 + z ^ 2 / p 0 ^ 2) * h 0) :=
          mul_lt_mul_of_pos_left hratio (sq_pos_of_pos hp0)
        _ = (p 0 ^ 2 + z ^ 2) * h 0 := by field_simp [hp0.ne']
    have hgap : 0 < (p 0 ^ 2 + z ^ 2) * h 0 - p 0 ^ 2 * h 1 :=
      sub_pos.2 hscaled
    have hnum :
        0 < (r z p + z) * (z * h 0) + p 0 ^ 2 * (h 0 - h 1) := by
      rw [show (r z p + z) * (z * h 0) + p 0 ^ 2 * (h 0 - h 1) =
          r z p * z * h 0 + ((p 0 ^ 2 + z ^ 2) * h 0 - p 0 ^ 2 * h 1) by ring]
      exact add_pos (mul_pos (mul_pos hr hz) hh0) hgap
    have heq :
        z * h 0 + p 0 ^ 2 / (r z p + z) * (h 0 - h 1) =
          ((r z p + z) * (z * h 0) + p 0 ^ 2 * (h 0 - h 1)) /
            (r z p + z) := by
      field_simp [hrz.ne']
    rw [heq]
    exact div_pos hnum hrz
  have hu : ∀ j, 0 < u z p j := by
    intro j
    fin_cases j
    · exact hu0
    · exact hu1
  have hgZeropos : (gZero z p).PosDef := by
    have hscalar :
        ((z * r z p) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosDef :=
      (Matrix.PosDef.one (n := Fin 2) (R := ℝ)).smul (mul_pos hz hr)
    have hrank :
        ((r z p / (r z p + z)) • Matrix.vecMulVec p p).PosSemidef := by
      have hbase : (Matrix.vecMulVec p p).PosSemidef := by
        simpa using Matrix.posSemidef_vecMulVec_self_star (R := ℝ) p
      exact hbase.smul (div_nonneg hr.le hrz.le)
    exact hscalar.add_posSemidef hrank
  let d : Fin 2 → ℝ := fun j => Real.sqrt (H z p j j)
  let sqrtH : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal d
  have hdpos : ∀ j, 0 < d j := fun j => Real.sqrt_pos.2 (hHdiag j)
  have hdne : ∀ j, d j ≠ 0 := fun j => (hdpos j).ne'
  have hH_sqrtH : H z p = sqrtH * sqrtH := by
    change H z p = Matrix.diagonal d * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply, if_pos]
      change H z p i i = Real.sqrt (H z p i i) * Real.sqrt (H z p i i)
      rw [show Real.sqrt (H z p i i) * Real.sqrt (H z p i i) =
          Real.sqrt (H z p i i) ^ 2 by ring, Real.sq_sqrt (hHdiag i).le]
    · simp [H, hij]
  have hsqrtHunit : IsUnit sqrtH := by
    change IsUnit (Matrix.diagonal d)
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro j
    exact isUnit_iff_ne_zero.2 (hdne j)
  let invSqrtH : Matrix (Fin 2) (Fin 2) ℝ := sqrtH⁻¹
  have hsqrtH_invSqrtH : sqrtH * invSqrtH = 1 := by
    change sqrtH * sqrtH⁻¹ = 1
    exact Matrix.mul_nonsing_inv sqrtH (Matrix.isUnit_iff_isUnit_det sqrtH |>.mp hsqrtHunit)
  have hinvSqrtH_sqrtH : invSqrtH * sqrtH = 1 := by
    change sqrtH⁻¹ * sqrtH = 1
    exact Matrix.nonsing_inv_mul sqrtH (Matrix.isUnit_iff_isUnit_det sqrtH |>.mp hsqrtHunit)
  let sym : Matrix (Fin 2) (Fin 2) ℝ := sqrtH * gZero z p * sqrtH
  have hsympos : sym.PosDef := by
    have hcongr := (Matrix.IsUnit.posDef_star_left_conjugate_iff hsqrtHunit).2 hgZeropos
    simpa [sym, sqrtH, Matrix.star_eq_conjTranspose] using hcongr
  let unitary : Matrix (Fin 2) (Fin 2) ℝ := hsympos.isHermitian.eigenvectorUnitary
  let eigDiag : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal hsympos.isHermitian.eigenvalues
  let basis : Matrix (Fin 2) (Fin 2) ℝ := invSqrtH * unitary
  have hunitary_star_unitary : star unitary * unitary = 1 := by
    exact Unitary.coe_star_mul_self hsympos.isHermitian.eigenvectorUnitary
  have hsym_decomp : sym = unitary * eigDiag * star unitary := by
    simpa [unitary, eigDiag, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hsympos.isHermitian.spectral_theorem
  have hsym_unitary : sym * unitary = unitary * eigDiag := by
    calc
      sym * unitary = (unitary * eigDiag * star unitary) * unitary := by rw [hsym_decomp]
      _ = unitary * eigDiag * (star unitary * unitary) := by noncomm_ring
      _ = unitary * eigDiag := by rw [hunitary_star_unitary]; simp
  change (sqrtH * gZero z p * sqrtH) * unitary = unitary * eigDiag at hsym_unitary
  have hK_basis : K z p * basis = basis * eigDiag := by
    change K z p * (invSqrtH * unitary) = (invSqrtH * unitary) * eigDiag
    calc
      K z p * (invSqrtH * unitary) =
          (gZero z p * (sqrtH * sqrtH)) * (invSqrtH * unitary) := by
        rw [K, hH_sqrtH]
      _ = gZero z p * sqrtH * (sqrtH * invSqrtH) * unitary := by noncomm_ring
      _ = gZero z p * sqrtH * unitary := by rw [hsqrtH_invSqrtH]; simp
      _ = (invSqrtH * sqrtH) * (gZero z p * sqrtH * unitary) := by
        rw [hinvSqrtH_sqrtH]
        simp
      _ = invSqrtH * ((sqrtH * gZero z p * sqrtH) * unitary) := by noncomm_ring
      _ = invSqrtH * (unitary * eigDiag) := by rw [hsym_unitary]
      _ = (invSqrtH * unitary) * eigDiag := by noncomm_ring
  have hinvSqrtHunit : IsUnit invSqrtH := by
    change IsUnit sqrtH⁻¹
    exact Matrix.isUnit_nonsing_inv_iff.mpr hsqrtHunit
  have hbasisUnit : IsUnit basis := by
    change IsUnit (invSqrtH * unitary)
    exact hinvSqrtHunit.mul Unitary.isUnit_coe
  have hKp : ∀ i, (K z p *ᵥ p) i + z * u z p i = q z p * p i := by
    intro i
    simp only [u, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    field_simp [hz.ne']
    ring
  have hKp_lt : ∀ i, (K z p *ᵥ p) i < q z p * p i := by
    intro i
    nlinarith [mul_pos hz (hu i), hKp i]
  have heigen_lt : ∀ (lambda : ℝ) (w : Fin 2 → ℝ), 0 < lambda → w ≠ 0 →
      K z p *ᵥ w = lambda • w → lambda < q z p := by
    intro lambda w hlambda hwne heig
    have heig0 := congrFun heig 0
    have heig1 := congrFun heig 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      at heig0 heig1
    have hkp0 := hKp_lt 0
    have hkp1 := hKp_lt 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hkp0 hkp1
    by_cases hcmp : |w 1| * p 0 ≤ |w 0| * p 1
    · have hw0abs : 0 < |w 0| := by
        have hw0ne : w 0 ≠ 0 := by
          intro hw0
          have hw1abs : |w 1| = 0 := by
            have : |w 1| * p 0 ≤ 0 := by simpa [hw0] using hcmp
            have hnonneg : 0 ≤ |w 1| * p 0 := mul_nonneg (abs_nonneg _) hp0.le
            exact (mul_eq_zero.mp (le_antisymm this hnonneg)).resolve_right hp0.ne'
          apply hwne
          funext i
          fin_cases i
          · exact hw0
          · exact abs_eq_zero.mp hw1abs
        exact abs_pos.2 hw0ne
      have habs :
          lambda * |w 0| ≤ K z p 0 0 * |w 0| + K z p 0 1 * |w 1| := by
        calc
          lambda * |w 0| = |lambda * w 0| := by rw [abs_mul, abs_of_pos hlambda]
          _ = |K z p 0 0 * w 0 + K z p 0 1 * w 1| := congrArg abs heig0.symm
          _ ≤ |K z p 0 0 * w 0| + |K z p 0 1 * w 1| := abs_add_le _ _
          _ = K z p 0 0 * |w 0| + K z p 0 1 * |w 1| := by
            rw [abs_mul, abs_mul, abs_of_pos (hKentry 0 0), abs_of_pos (hKentry 0 1)]
      have habsp := mul_le_mul_of_nonneg_right habs hp0.le
      have hcmpp := mul_le_mul_of_nonneg_left hcmp (hKentry 0 1).le
      have hkpp := mul_lt_mul_of_pos_right hkp0 hw0abs
      have hmiddle :
          (K z p 0 0 * |w 0| + K z p 0 1 * |w 1|) * p 0 ≤
            (K z p 0 0 * p 0 + K z p 0 1 * p 1) * |w 0| := by
        calc
          _ = K z p 0 0 * |w 0| * p 0 + K z p 0 1 * (|w 1| * p 0) := by ring
          _ ≤ K z p 0 0 * |w 0| * p 0 + K z p 0 1 * (|w 0| * p 1) :=
            add_le_add (le_refl _) hcmpp
          _ = _ := by ring
      have hfinal : lambda * (|w 0| * p 0) < q z p * (|w 0| * p 0) := by
        calc
          lambda * (|w 0| * p 0) = (lambda * |w 0|) * p 0 := by ring
          _ ≤ (K z p 0 0 * |w 0| + K z p 0 1 * |w 1|) * p 0 := habsp
          _ ≤ (K z p 0 0 * p 0 + K z p 0 1 * p 1) * |w 0| := hmiddle
          _ < (q z p * p 0) * |w 0| := hkpp
          _ = q z p * (|w 0| * p 0) := by ring
      exact lt_of_mul_lt_mul_right hfinal (mul_pos hw0abs hp0).le
    · have hcmp' : |w 0| * p 1 ≤ |w 1| * p 0 := (lt_of_not_ge hcmp).le
      have hw1abs : 0 < |w 1| := by
        have hw1ne : w 1 ≠ 0 := by
          intro hw1
          have hw0abs : |w 0| = 0 := by
            have : |w 0| * p 1 ≤ 0 := by simpa [hw1] using hcmp'
            have hnonneg : 0 ≤ |w 0| * p 1 := mul_nonneg (abs_nonneg _) hp1.le
            exact (mul_eq_zero.mp (le_antisymm this hnonneg)).resolve_right hp1.ne'
          apply hwne
          funext i
          fin_cases i
          · exact abs_eq_zero.mp hw0abs
          · exact hw1
        exact abs_pos.2 hw1ne
      have habs :
          lambda * |w 1| ≤ K z p 1 0 * |w 0| + K z p 1 1 * |w 1| := by
        calc
          lambda * |w 1| = |lambda * w 1| := by rw [abs_mul, abs_of_pos hlambda]
          _ = |K z p 1 0 * w 0 + K z p 1 1 * w 1| := congrArg abs heig1.symm
          _ ≤ |K z p 1 0 * w 0| + |K z p 1 1 * w 1| := abs_add_le _ _
          _ = K z p 1 0 * |w 0| + K z p 1 1 * |w 1| := by
            rw [abs_mul, abs_mul, abs_of_pos (hKentry 1 0), abs_of_pos (hKentry 1 1)]
      have habsp := mul_le_mul_of_nonneg_right habs hp1.le
      have hcmpp := mul_le_mul_of_nonneg_left hcmp' (hKentry 1 0).le
      have hkpp := mul_lt_mul_of_pos_right hkp1 hw1abs
      have hmiddle :
          (K z p 1 0 * |w 0| + K z p 1 1 * |w 1|) * p 1 ≤
            (K z p 1 0 * p 0 + K z p 1 1 * p 1) * |w 1| := by
        calc
          _ = K z p 1 1 * |w 1| * p 1 + K z p 1 0 * (|w 0| * p 1) := by ring
          _ ≤ K z p 1 1 * |w 1| * p 1 + K z p 1 0 * (|w 1| * p 0) :=
            add_le_add (le_refl _) hcmpp
          _ = _ := by ring
      have hfinal : lambda * (|w 1| * p 1) < q z p * (|w 1| * p 1) := by
        calc
          lambda * (|w 1| * p 1) = (lambda * |w 1|) * p 1 := by ring
          _ ≤ (K z p 1 0 * |w 0| + K z p 1 1 * |w 1|) * p 1 := habsp
          _ ≤ (K z p 1 0 * p 0 + K z p 1 1 * p 1) * |w 1| := hmiddle
          _ < (q z p * p 1) * |w 1| := hkpp
          _ = q z p * (|w 1| * p 1) := by ring
      exact lt_of_mul_lt_mul_right hfinal (mul_pos hw1abs hp1).le
  let lambda1 : ℝ := hsympos.isHermitian.eigenvalues 0
  let lambda2 : ℝ := hsympos.isHermitian.eigenvalues 1
  have hlambda1pos : 0 < lambda1 := hsympos.eigenvalues_pos 0
  have hlambda2pos : 0 < lambda2 := hsympos.eigenvalues_pos 1
  have heigenvalues_lt : ∀ j, hsympos.isHermitian.eigenvalues j < q z p := by
    intro j
    let ej : Fin 2 → ℝ := Pi.single j 1
    let w : Fin 2 → ℝ := basis *ᵥ ej
    have hej : ej ≠ 0 := by
      exact Pi.single_ne_zero_iff.2 one_ne_zero
    have hw : w ≠ 0 := by
      simpa only [w, Matrix.mulVec_zero] using
        (Matrix.mulVec_injective_of_isUnit hbasisUnit).ne hej
    have heig : K z p *ᵥ w = hsympos.isHermitian.eigenvalues j • w := by
      have hv := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m *ᵥ ej) hK_basis
      have heigDiagVec :
          eigDiag *ᵥ ej = hsympos.isHermitian.eigenvalues j • ej := by
        change Matrix.diagonal hsympos.isHermitian.eigenvalues *ᵥ Pi.single j 1 =
          hsympos.isHermitian.eigenvalues j • Pi.single j 1
        rw [Matrix.diagonal_mulVec_single]
        simpa using
          (Pi.single_smul' j (hsympos.isHermitian.eigenvalues j) (1 : ℝ))
      have heigBasis :
          K z p *ᵥ (basis *ᵥ ej) =
            hsympos.isHermitian.eigenvalues j • (basis *ᵥ ej) := by
        calc
          K z p *ᵥ (basis *ᵥ ej) = (K z p * basis) *ᵥ ej :=
            Matrix.mulVec_mulVec _ _ _
          _ = (basis * eigDiag) *ᵥ ej := hv
          _ = basis *ᵥ (eigDiag *ᵥ ej) := (Matrix.mulVec_mulVec _ _ _).symm
          _ = basis *ᵥ (hsympos.isHermitian.eigenvalues j • ej) := by rw [heigDiagVec]
          _ = hsympos.isHermitian.eigenvalues j • (basis *ᵥ ej) :=
            Matrix.mulVec_smul _ _ _
      exact heigBasis
    exact heigen_lt _ w (hsympos.eigenvalues_pos j) hw heig
  have hlambda1lt : lambda1 < q z p := heigenvalues_lt 0
  have hlambda2lt : lambda2 < q z p := heigenvalues_lt 1
  have heigDiag : eigDiag = Matrix.diagonal ![lambda1, lambda2] := by
    change Matrix.diagonal hsympos.isHermitian.eigenvalues =
      Matrix.diagonal ![lambda1, lambda2]
    apply Matrix.diagonal_injective
    funext j
    fin_cases j <;> rfl
  let c : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => p i / z
  let ucol : Matrix (Fin 2) (Fin 1) ℝ := fun i _ => u z p i
  let qblock : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => q z p
  let blockBasis : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks basis c 0 1
  have hblockBasisDet : IsUnit blockBasis.det := by
    apply (Matrix.isUnit_iff_isUnit_det blockBasis).1
    change IsUnit (Matrix.fromBlocks basis c 0 1)
    exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hbasisUnit, isUnit_one⟩
  have hcolumn :
      K z p * c + ucol = c * qblock := by
    ext i j
    have hi := hKp i
    have hKc : (K z p * c) i j = (1 / z) * (K z p *ᵥ p) i := by
      calc
        (K z p * c) i j = ∑ k : Fin 2, K z p i k * c k j := Matrix.mul_apply
        _ = (1 / z) * (K z p *ᵥ p) i := by
          simp only [c, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ring
    have hcq : (c * qblock) i j = (p i / z) * q z p := by
      calc
        _ = ∑ k : Fin 1, c i k * qblock k j := Matrix.mul_apply
        _ = (p i / z) * q z p := by simp [c, qblock]
    calc
      (K z p * c + ucol) i j = (K z p * c) i j + ucol i j := rfl
      _ = (1 / z) * (K z p *ᵥ p) i + u z p i := by rw [hKc]
      _ = (1 / z) * ((K z p *ᵥ p) i + z * u z p i) := by
        field_simp [hz.ne']
      _ = (1 / z) * (q z p * p i) := by rw [hi]
      _ = (p i / z) * q z p := by ring
      _ = (c * qblock) i j := hcq.symm
  have hQ_blockBasis :
      Q z p * blockBasis =
        blockBasis *
          Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0 (fun _ _ => q z p) := by
    change Q z p * Matrix.fromBlocks basis c 0 1 =
      Matrix.fromBlocks basis c 0 1 *
        Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0 (fun _ _ => q z p)
    change Matrix.fromBlocks (K z p) ucol 0 qblock * Matrix.fromBlocks basis c 0 1 =
      Matrix.fromBlocks basis c 0 1 *
        Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0 qblock
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, ← heigDiag, hK_basis]
    simpa using hcolumn
  exact ⟨hu, hKentry, lambda1, lambda2, hlambda1pos, hlambda1lt, hlambda2pos,
    hlambda2lt, blockBasis, hblockBasisDet, hQ_blockBasis⟩

#print axioms singular_support_candidate_positive_and_diagonalizable

end D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
