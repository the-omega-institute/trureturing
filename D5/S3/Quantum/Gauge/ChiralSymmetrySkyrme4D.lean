/- GID: D5/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/ChiralSymmetrySkyrme4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-flavor chiral fields, pion mass and anomaly formulas, and Skyrme energy bounds. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The two-flavor effective field uses the Pauli basis and the unnormalized sinc.
The mass and width formulas use their leading-order effective theory normalizations.
The Skyrme inequality is pointwise and the Derrick energy describes spatial rescaling. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Matrix
open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate Topology

namespace D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev CMat2 := Matrix (Fin 2) (Fin 2) ℂ

def chiralAct (L R U : SU2) : SU2 := L * U * R⁻¹

theorem chiral_vacuum_stabilizer_iff (L R : SU2) :
    chiralAct L R 1 = 1 ↔ L = R := by
  change L * 1 * R⁻¹ = 1 ↔ L = R
  rw [mul_one, mul_inv_eq_one]

theorem chiral_orbit_transitive (U : SU2) : ∃ L R : SU2, chiralAct L R 1 = U := by
  exact ⟨U, 1, by simp [chiralAct]⟩

/-- The common left and right rotations which fix the identity vacuum. -/
def chiralDiagonal : Subgroup (SU2 × SU2) where
  carrier := {p | p.1 = p.2}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a.1 = a.2 at ha
    change b.1 = b.2 at hb
    change a.1 * b.1 = a.2 * b.2
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    change a.1 = a.2 at ha
    change a.1⁻¹ = a.2⁻¹
    rw [ha]

/-- The vacuum orbit identifies the left cosets of the diagonal with the field group. -/
def chiralCosetEquiv : ((SU2 × SU2) ⧸ chiralDiagonal) ≃ SU2 where
  toFun := Quotient.lift (fun p : SU2 × SU2 => chiralAct p.1 p.2 1) (by
    intro a b h
    have h := QuotientGroup.leftRel_apply.mp h
    change a.1⁻¹ * b.1 = a.2⁻¹ * b.2 at h
    let r := a.2⁻¹ * b.2
    have hL : a.1 * r = b.1 := by
      rw [show r = a.1⁻¹ * b.1 from h.symm, mul_inv_cancel_left]
    have hR : a.2 * r = b.2 := mul_inv_cancel_left a.2 b.2
    rw [← hL, ← hR]
    simp [chiralAct, _root_.mul_inv_rev, mul_assoc])
  invFun := fun U => QuotientGroup.mk (U, 1)
  left_inv := fun q => QuotientGroup.induction_on q fun p => by
    apply QuotientGroup.eq.mpr
    change (chiralAct p.1 p.2 1)⁻¹ * p.1 = (1 : SU2)⁻¹ * p.2
    simp [chiralAct, _root_.mul_inv_rev, mul_assoc]
  right_inv := fun U => by simp [QuotientGroup.mk, chiralAct]

def pionNorm (π : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (π 0 ^ 2 + π 1 ^ 2 + π 2 ^ 2)

def pauliPion (π : Fin 3 → ℝ) : CMat2 :=
  !![↑(π 2), ↑(π 0) - Complex.I * ↑(π 1);
     ↑(π 0) + Complex.I * ↑(π 1), -↑(π 2)]

/-- The closed Pauli expression for the exponential pion field. -/
def chiralField (fπ : ℝ) (π : Fin 3 → ℝ) : CMat2 :=
  (Real.cos (pionNorm π / fπ) : ℂ) • (1 : CMat2) +
    (Complex.I * (Real.sinc (pionNorm π / fπ) / fπ : ℝ)) • pauliPion π

private theorem pionNorm_sq (π : Fin 3 → ℝ) :
    pionNorm π ^ 2 = π 0 ^ 2 + π 1 ^ 2 + π 2 ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem sinc_mul_self (x : ℝ) : Real.sinc x * x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx, div_mul_cancel₀ _ hx]

private theorem pion_trig_norm {fπ : ℝ} (hf : fπ ≠ 0) (π : Fin 3 → ℝ) :
    Real.cos (pionNorm π / fπ) ^ 2 +
      (Real.sinc (pionNorm π / fπ) / fπ) ^ 2 *
        (π 0 ^ 2 + π 1 ^ 2 + π 2 ^ 2) = 1 := by
  rw [← pionNorm_sq]
  calc
    _ = Real.cos (pionNorm π / fπ) ^ 2 +
      (Real.sinc (pionNorm π / fπ) * (pionNorm π / fπ)) ^ 2 := by field_simp
    _ = 1 := by rw [sinc_mul_self, add_comm, Real.sin_sq_add_cos_sq]

private def su2Matrix (a x y z : ℝ) : CMat2 :=
  !![⟨a, z⟩, ⟨y, x⟩; ⟨-y, x⟩, ⟨a, -z⟩]

private theorem su2Matrix_unitary_iff (a x y z : ℝ) :
    su2Matrix a x y z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      a ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  constructor
  · intro h
    have he := congrArg Complex.re h.2
    simp [Matrix.det_fin_two, su2Matrix, Complex.mul_re, Complex.sub_re] at he
    nlinarith
  · intro h
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        norm_num [su2Matrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
          Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;>
        first | solve_by_elim | linear_combination h | ring
    · rw [Matrix.det_fin_two]
      apply Complex.ext <;>
        norm_num [su2Matrix, Complex.mul_re, Complex.mul_im, Complex.sub_re,
          Complex.sub_im] <;> first | solve_by_elim | linear_combination h | ring

private theorem chiralField_coordinates (fπ : ℝ) (π : Fin 3 → ℝ) :
    let c := Real.cos (pionNorm π / fπ)
    let s := Real.sinc (pionNorm π / fπ) / fπ
    chiralField fπ π = su2Matrix c (s * π 0) (s * π 1) (s * π 2) := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [chiralField, pauliPion, su2Matrix, Matrix.one_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      smul_eq_mul, -Complex.ofReal_cos]

theorem chiralField_mem_su2 {fπ : ℝ} (hf : fπ ≠ 0) (π : Fin 3 → ℝ) :
    chiralField fπ π ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [chiralField_coordinates, su2Matrix_unitary_iff]
  linear_combination pion_trig_norm hf π

theorem chiralField_zero (fπ : ℝ) : chiralField fπ 0 = 1 := by
  rw [chiralField_coordinates]
  simp [pionNorm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> norm_num [su2Matrix, Matrix.one_apply]

private theorem pionNorm_smul (t : ℝ) (v : Fin 3 → ℝ) :
    pionNorm (t • v) = |t| * pionNorm v := by
  unfold pionNorm
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (t * v 0) ^ 2 + (t * v 1) ^ 2 + (t * v 2) ^ 2 =
    t ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

private theorem chiralField_line (fπ t : ℝ) (v : Fin 3 → ℝ) :
    chiralField fπ (t • v) =
      Real.cos (t * (pionNorm v / fπ)) • (1 : CMat2) +
        (t * Real.sinc (t * (pionNorm v / fπ))) •
          ((Complex.I / (fπ : ℂ)) • pauliPion v) := by
  have hangle : pionNorm (t • v) / fπ = |t| * (pionNorm v / fπ) := by
    rw [pionNorm_smul, mul_div_assoc]
  have hc : Real.cos (pionNorm (t • v) / fπ) =
      Real.cos (t * (pionNorm v / fπ)) := by
    rw [hangle]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, neg_mul, Real.cos_neg]
  have hs : Real.sinc (pionNorm (t • v) / fπ) =
      Real.sinc (t * (pionNorm v / fπ)) := by
    rw [hangle]
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, neg_mul, Real.sinc_neg]
  simp only [chiralField, hc, hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliPion, Matrix.smul_apply, Pi.smul_apply, Complex.real_smul,
      smul_eq_mul, div_eq_mul_inv] <;> ring

private theorem sinc_line_hasDerivAt (c : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.sinc (t * c)) 1 0 := by
  by_cases hc : c = 0
  · simpa only [hc, mul_zero, Real.sinc_zero, mul_one] using hasDerivAt_id' (0 : ℝ)
  have hfun : (fun t : ℝ => t * Real.sinc (t * c)) =
      fun t : ℝ => Real.sin (t * c) / c := by
    funext t
    rw [← sinc_mul_self (t * c), ← mul_assoc, mul_comm (Real.sinc (t * c)) t,
      mul_div_cancel_right₀ _ hc]
  rw [hfun]
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const c).sin).div_const c
  simpa only [id_eq, zero_mul, Real.cos_zero, one_mul, div_self hc] using h

private theorem chiralField_line_hasDerivAt (fπ : ℝ) (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => chiralField fπ (t • v))
      ((Complex.I / (fπ : ℂ)) • pauliPion v) 0 := by
  simp only [chiralField_line]
  let c := pionNorm v / fπ
  have hc : HasDerivAt (fun t : ℝ => Real.cos (t * c)) 0 0 := by
    simpa only [zero_mul, Real.sin_zero, neg_zero, one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const c).cos
  convert (hc.smul_const (1 : CMat2)).add
    ((sinc_line_hasDerivAt c).smul_const
      ((Complex.I / (fπ : ℂ)) • pauliPion v)) using 1
  · rfl
  · simp

private theorem pauliPion_adjoint_square (v : Fin 3 → ℝ) :
    (pauliPion v)ᴴ * pauliPion v =
      ((v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 : ℝ) : ℂ) • (1 : CMat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [pauliPion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, smul_eq_mul, ← Complex.ofReal_pow] <;> ring

open scoped Matrix.Norms.Operator in
private theorem exp_of_square_neg_one (J : CMat2) (hJ : J * J = -1) (r : ℝ) :
    NormedSpace.exp (r • J) = Real.cos r • (1 : CMat2) + Real.sin r • J := by
  let ϕ := Complex.liftAux J hJ
  have hϕ : Continuous ϕ := by
    have hfun : (ϕ : ℂ → CMat2) = fun z => z.re • (1 : CMat2) + z.im • J := by
      funext z
      simp [ϕ, Algebra.algebraMap_eq_smul_one]
    rw [hfun]
    exact (Complex.continuous_re.smul continuous_const).add
      (Complex.continuous_im.smul continuous_const)
  have he := NormedSpace.map_exp ϕ hϕ ((r : ℂ) * Complex.I)
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I] at he
  simp [ϕ, Algebra.algebraMap_eq_smul_one, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at he
  exact he.symm

/-- The regular Pauli expression is the matrix exponential of the pion generator. -/
theorem chiralField_eq_exp (fπ : ℝ) (π : Fin 3 → ℝ) :
    chiralField fπ π = NormedSpace.exp ((Complex.I / (fπ : ℂ)) • pauliPion π) := by
  let r := pionNorm π
  by_cases hr : r = 0
  · have hsum := pionNorm_sq π
    change r ^ 2 = _ at hsum
    rw [hr] at hsum
    have h0 : π 0 = 0 := by nlinarith
    have h1 : π 1 = 0 := by nlinarith
    have h2 : π 2 = 0 := by nlinarith
    have hπ : π = 0 := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hp0 : pauliPion 0 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliPion]
    rw [hπ, chiralField_zero, hp0, smul_zero, NormedSpace.exp_zero]
  · have hherm : (pauliPion π)ᴴ = pauliPion π := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliPion, sub_eq_add_neg]
    have hP : pauliPion π * pauliPion π = (r : ℂ) ^ 2 • (1 : CMat2) := by
      simpa only [hherm, ← pionNorm_sq, Complex.ofReal_pow] using pauliPion_adjoint_square π
    let J := (Complex.I / (r : ℂ)) • pauliPion π
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have hJ : J * J = -1 := by
      dsimp only [J]
      rw [Matrix.smul_mul, Matrix.mul_smul, hP, ← smul_assoc, ← smul_assoc]
      have hcoeff : (Complex.I / (r : ℂ)) * (Complex.I / (r : ℂ)) * (r : ℂ) ^ 2 = -1 := by
        field_simp
        exact Complex.I_sq
      rw [smul_eq_mul, smul_eq_mul, hcoeff, neg_one_smul]
    have hscale (a : ℝ) : a • J =
        (Complex.I * ((a / r : ℝ) : ℂ)) • pauliPion π := by
      dsimp only [J]
      rw [← Complex.coe_smul, smul_smul, Complex.ofReal_div]
      congr 1
      ring
    have harg : (r / fπ) • J = (Complex.I / (fπ : ℂ)) • pauliPion π := by
      rw [hscale, div_right_comm r fπ r, div_self hr, Complex.ofReal_div,
        Complex.ofReal_one, mul_one_div]
    have hsin : Real.sin (r / fπ) / r = Real.sinc (r / fπ) / fπ := by
      rw [← sinc_mul_self (r / fπ), mul_div_assoc, div_right_comm r fπ r, div_self hr]
      ring
    rw [← harg, exp_of_square_neg_one J hJ, hscale, hsin, ← Complex.coe_smul]
    rfl

theorem chiral_kinetic_quadratic_normalization {fπ : ℝ} (hf : 0 < fπ)
    (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => chiralField fπ (t • v))
      ((Complex.I / (fπ : ℂ)) • pauliPion v) 0 ∧
    let U' := deriv (fun t : ℝ => chiralField fπ (t • v)) 0
    (fπ ^ 2 / 4) * (U'ᴴ * U').trace.re = (1 / 2) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  refine ⟨chiralField_line_hasDerivAt fπ v, ?_⟩
  dsimp
  have h := (chiralField_line_hasDerivAt fπ v).deriv
  erw [h]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, pauliPion_adjoint_square]
  have hfC : (fπ : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hs : star (Complex.I / (fπ : ℂ)) * (Complex.I / (fπ : ℂ)) =
      ((1 / fπ ^ 2 : ℝ) : ℂ) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    field_simp
    rw [pow_two, Complex.I_mul_I, neg_neg]
  rw [← smul_assoc, smul_eq_mul, hs]
  simp [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    -Complex.ofReal_pow, -Complex.ofReal_add, -Complex.ofReal_div]
  field_simp
  ring

def chiralPotential (B₀ fπ mᵤ m_d : ℝ) (U : CMat2) : ℝ :=
  -B₀ * fπ ^ 2 * ((Matrix.diagonal ![(mᵤ : ℂ), (m_d : ℂ)] * U).trace).re

private theorem chiralPotential_entries (B₀ fπ mᵤ m_d : ℝ) (U : CMat2) :
    chiralPotential B₀ fπ mᵤ m_d U =
      -B₀ * fπ ^ 2 * (mᵤ * (U 0 0).re + m_d * (U 1 1).re) := by
  simp [chiralPotential, Matrix.diagonal_mul, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Complex.add_re, Complex.mul_re]

private theorem su2_reconstruct (U : SU2) :
    (U : CMat2) = su2Matrix ((U : CMat2) 0 0).re ((U : CMat2) 0 1).im
      ((U : CMat2) 0 1).re ((U : CMat2) 0 0).im := by
  let A : CMat2 := U
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp U.property
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  have hadj : Aᴴ = Matrix.adjugate A := by
    have hright : A * Matrix.adjugate A = 1 := by
      rw [Matrix.mul_adjugate, show A.det = 1 from hd, one_smul]
    calc
      Aᴴ = Aᴴ * (A * Matrix.adjugate A) := by rw [hright, mul_one]
      _ = Matrix.adjugate A := by rw [← mul_assoc, show Aᴴ * A = 1 from hu, one_mul]
  rw [Matrix.adjugate_fin_two] at hadj
  have hdiag : star (A 0 0) = A 1 1 := by
    simpa using congrArg (fun M : CMat2 => M 0 0) hadj
  have hoff : star (A 0 1) = -(A 1 0) := by
    simpa using congrArg (fun M : CMat2 => M 1 0) hadj
  change A = su2Matrix (A 0 0).re (A 0 1).im (A 0 1).re (A 0 0).im
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> rfl
  · apply Complex.ext <;> rfl
  · change A 1 0 = _
    erw [← neg_eq_iff_eq_neg.mpr hoff]
    apply Complex.ext <;> simp [su2Matrix]
  · change A 1 1 = _
    erw [← hdiag]
    apply Complex.ext <;> simp [su2Matrix]

/-- The unit three-sphere in real four-coordinate form. -/
abbrev ChiralSphere :=
  {q : Fin 4 → ℝ // q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 = 1}

/-- The determinant-one unitary matrices are parametrized by the unit three-sphere. -/
def su2SphereCoordinates : SU2 ≃ₜ ChiralSphere where
  toFun := fun U =>
    ⟨![((U : CMat2) 0 0).re, ((U : CMat2) 0 1).im,
        ((U : CMat2) 0 1).re, ((U : CMat2) 0 0).im], by
      have h : su2Matrix ((U : CMat2) 0 0).re ((U : CMat2) 0 1).im
          ((U : CMat2) 0 1).re ((U : CMat2) 0 0).im ∈ SU2 := by
        rw [← su2_reconstruct U]
        exact U.property
      exact (su2Matrix_unitary_iff _ _ _ _).mp h⟩
  invFun := fun q =>
    ⟨su2Matrix (q.val 0) (q.val 1) (q.val 2) (q.val 3),
      (su2Matrix_unitary_iff _ _ _ _).mpr q.property⟩
  left_inv := fun U => Subtype.ext (su2_reconstruct U).symm
  right_inv := fun q => by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re.comp (continuous_subtype_val.matrix_elem 0 0)
    · exact Complex.continuous_im.comp (continuous_subtype_val.matrix_elem 0 1)
    · exact Complex.continuous_re.comp (continuous_subtype_val.matrix_elem 0 1)
    · exact Complex.continuous_im.comp (continuous_subtype_val.matrix_elem 0 0)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    have hq (k : Fin 4) : Continuous (fun q : ChiralSphere => q.val k) :=
      (continuous_apply k).comp continuous_subtype_val
    fin_cases i <;> fin_cases j
    · exact Complex.equivRealProdCLM.symm.continuous.comp ((hq 0).prodMk (hq 3))
    · exact Complex.equivRealProdCLM.symm.continuous.comp ((hq 2).prodMk (hq 1))
    · exact Complex.equivRealProdCLM.symm.continuous.comp ((hq 2).neg.prodMk (hq 1))
    · exact Complex.equivRealProdCLM.symm.continuous.comp ((hq 0).prodMk (hq 3).neg)

theorem chiralPotential_global_min_at_one {B₀ fπ mᵤ m_d : ℝ}
    (hB : 0 < B₀) (hf : 0 < fπ) (hu : 0 < mᵤ) (hd : 0 < m_d) (U : SU2) :
    chiralPotential B₀ fπ mᵤ m_d 1 ≤ chiralPotential B₀ fπ mᵤ m_d U ∧
      (chiralPotential B₀ fπ mᵤ m_d 1 = chiralPotential B₀ fπ mᵤ m_d U ↔
        (U : CMat2) = 1) := by
  let a := ((U : CMat2) 0 0).re
  let x := ((U : CMat2) 0 1).im
  let y := ((U : CMat2) 0 1).re
  let z := ((U : CMat2) 0 0).im
  have hU : (U : CMat2) = su2Matrix a x y z := su2_reconstruct U
  have hn : a ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 := (su2SphereCoordinates U).property
  have ha : a ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hfactors : 0 < B₀ * fπ ^ 2 * (mᵤ + m_d) := by positivity
  have hgap : chiralPotential B₀ fπ mᵤ m_d U - chiralPotential B₀ fπ mᵤ m_d 1 =
      (B₀ * fπ ^ 2 * (mᵤ + m_d)) * (1 - a) := by
    rw [chiralPotential_entries, chiralPotential_entries]
    simp [hU, su2Matrix, Matrix.one_apply_eq]
    ring
  refine ⟨sub_nonneg.mp (hgap.symm ▸ mul_nonneg hfactors.le (sub_nonneg.mpr ha)), ?_⟩
  constructor
  · intro he
    rw [he, sub_self] at hgap
    have hae : a = 1 :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hgap.symm).resolve_left hfactors.ne')).symm
    rw [hae] at hn
    have hxe : x = 0 := by nlinarith only [hn, sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hye : y = 0 := by nlinarith only [hn, sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hze : z = 0 := by nlinarith only [hn, sq_nonneg x, sq_nonneg y, sq_nonneg z]
    rw [hU, hae, hxe, hye, hze]
    ext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> norm_num [su2Matrix, Matrix.one_apply]
  · intro he
    rw [he]

private theorem potential_line (B₀ fπ mᵤ m_d : ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    chiralPotential B₀ fπ mᵤ m_d (chiralField fπ (t • v)) =
      (-B₀ * fπ ^ 2 * (mᵤ + m_d)) * Real.cos (t * (pionNorm v / fπ)) := by
  rw [chiralPotential_entries, chiralField_line]
  simp [pauliPion, Matrix.one_apply_eq, smul_eq_mul, Complex.real_smul,
    Complex.mul_re, Complex.add_re, Complex.div_re, -Complex.ofReal_cos]
  ring

theorem gmor_exact_hessian {fπ : ℝ} (hf : 0 < fπ)
    (B₀ mᵤ m_d : ℝ) (v : Fin 3 → ℝ) :
    deriv (deriv (fun t : ℝ =>
      chiralPotential B₀ fπ mᵤ m_d (chiralField fπ (t • v)))) 0 =
        B₀ * (mᵤ + m_d) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  let A := -B₀ * fπ ^ 2 * (mᵤ + m_d)
  let c := pionNorm v / fπ
  have hfirst : deriv (fun t : ℝ =>
      chiralPotential B₀ fπ mᵤ m_d (chiralField fπ (t • v))) =
      fun t : ℝ => A * (-Real.sin (t * c) * c) := by
    ext t
    simp only [potential_line]
    simpa only [id_eq, one_mul] using (((hasDerivAt_id t).mul_const c).cos.const_mul A).deriv
  rw [hfirst]
  have hsecond := ((((hasDerivAt_id (0 : ℝ)).mul_const c).sin.neg).mul_const c).const_mul A
  have hvalue : deriv (fun t : ℝ => A * (-Real.sin (t * c) * c)) 0 = A * (-c * c) := by
    simpa only [id_eq, Pi.neg_apply, zero_mul, Real.cos_zero, one_mul] using hsecond.deriv
  rw [hvalue]
  dsimp [A, c]
  field_simp
  linear_combination B₀ * (mᵤ + m_d) * (pionNorm_sq v)

theorem gmor_pion_mass_relation {fπ : ℝ} (hf : 0 < fπ) (B₀ mᵤ m_d : ℝ) :
    let mPiSq := B₀ * (mᵤ + m_d)
    let condensate := B₀ * fπ ^ 2
    mPiSq * fπ ^ 2 = (mᵤ + m_d) * condensate ∧
      (∀ i : Fin 3, deriv (deriv (fun t : ℝ =>
        chiralPotential B₀ fπ mᵤ m_d (chiralField fπ (t • Pi.single i 1)))) 0 = mPiSq) ∧
      Tendsto (fun massSum : ℝ => B₀ * massSum) (𝓝 0) (𝓝 0) := by
  dsimp
  refine ⟨by ring, ?_, ?_⟩
  · intro i
    rw [gmor_exact_hessian hf]
    fin_cases i <;> norm_num [Pi.single_apply]
  · have h := Filter.Tendsto.const_mul B₀
      (tendsto_id : Tendsto (fun massSum : ℝ => massSum) (𝓝 0) (𝓝 0))
    rwa [mul_zero] at h

def abjTrace (Nc Qu Qd : ℝ) : ℝ := Nc * (Qu ^ 2 - Qd ^ 2)

def pi0GammaGammaWidth (α mPi fπ Nc Qu Qd : ℝ) : ℝ :=
  (α ^ 2 * mPi ^ 3 / (64 * Real.pi ^ 3 * fπ ^ 2)) * abjTrace Nc Qu Qd ^ 2

theorem abj_anomaly_free_general_Nc {Nc : ℝ} (hNc : Nc ≠ 0) :
    abjTrace Nc ((Nc + 1) / (2 * Nc)) (-(Nc - 1) / (2 * Nc)) = 1 := by
  unfold abjTrace
  field_simp
  ring

theorem abj_fixed_charges_color_test (Nc α mPi fπ : ℝ) :
    abjTrace Nc (2 / 3) (-1 / 3) = Nc / 3 ∧
      abjTrace 3 (2 / 3) (-1 / 3) = 1 ∧
      (0 < fπ → pi0GammaGammaWidth α mPi fπ 3 (2 / 3) (-1 / 3) =
        9 * pi0GammaGammaWidth α mPi fπ 1 (2 / 3) (-1 / 3)) := by
  constructor
  · unfold abjTrace
    ring
  · constructor
    · norm_num [abjTrace]
    · intro hf
      unfold pi0GammaGammaWidth abjTrace
      field_simp [hf.ne', Real.pi_ne_zero]
      ring

def skyrmeE2 (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2

def skyrmeE4 (x y z : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2

def skyrmeBaryon (x y z : ℝ) : ℝ := x * y * z

private theorem skyrme_energy_gap (x y z : ℝ) :
    skyrmeE2 x y z + skyrmeE4 x y z - 6 * |skyrmeBaryon x y z| =
      (|x| - |y| * |z|) ^ 2 + (|y| - |z| * |x|) ^ 2 + (|z| - |x| * |y|) ^ 2 := by
  simp only [skyrmeE2, skyrmeE4, skyrmeBaryon, abs_mul]
  calc
    _ = (|x| ^ 2 + |y| ^ 2 + |z| ^ 2) +
        (|x| ^ 2 * |y| ^ 2 + |y| ^ 2 * |z| ^ 2 + |z| ^ 2 * |x| ^ 2) -
          6 * (|x| * |y| * |z|) := by simp
    _ = _ := by ring

theorem faddeev_bogomolny_skyrme_bound (x y z : ℝ) :
    6 * |skyrmeBaryon x y z| ≤ skyrmeE2 x y z + skyrmeE4 x y z := by
  rw [← sub_nonneg, skyrme_energy_gap]
  positivity

private theorem skyrme_saturation_values {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hA : a = b * c) (hB : b = c * a) (hC : c = a * b) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 1) := by
  by_cases hz : a * b * c = 0
  · left
    rcases mul_eq_zero.mp hz with hab | hc
    · rcases mul_eq_zero.mp hab with ha | hb
      · have hB0 : b = 0 := by simpa [ha] using hB
        exact ⟨ha, hB0, by simpa [ha] using hC⟩
      · have hA0 : a = 0 := by simpa [hb] using hA
        exact ⟨hA0, hb, by simpa [hb] using hC⟩
    · exact ⟨by simpa [hc] using hA, by simpa [hc] using hB, hc⟩
  · right
    have ha₀ : a ≠ 0 := by intro h; simp [h] at hz
    have hb₀ : b ≠ 0 := by intro h; simp [h] at hz
    have hc₀ : c ≠ 0 := by intro h; simp [h] at hz
    have ha₂ : a ^ 2 = 1 := by
      apply mul_left_cancel₀ hb₀
      linear_combination -hB - a * hC
    have hb₂ : b ^ 2 = 1 := by
      apply mul_left_cancel₀ hc₀
      linear_combination -b * hA - hC
    have hc₂ : c ^ 2 = 1 := by
      apply mul_left_cancel₀ ha₀
      linear_combination -c * hB - hA
    exact ⟨(sq_eq_sq₀ ha zero_le_one).mp (by simpa using ha₂),
      (sq_eq_sq₀ hb zero_le_one).mp (by simpa using hb₂),
      (sq_eq_sq₀ hc zero_le_one).mp (by simpa using hc₂)⟩

theorem faddeev_bogomolny_saturation_iff (x y z : ℝ) :
    6 * |skyrmeBaryon x y z| = skyrmeE2 x y z + skyrmeE4 x y z ↔
      (x = 0 ∧ y = 0 ∧ z = 0) ∨ (|x| = 1 ∧ |y| = 1 ∧ |z| = 1) := by
  constructor
  · intro h
    have hg := skyrme_energy_gap x y z
    rw [← h, sub_self] at hg
    have ha : |x| = |y| * |z| := by nlinarith [hg]
    have hb : |y| = |z| * |x| := by nlinarith [hg]
    have hc : |z| = |x| * |y| := by nlinarith [hg]
    simpa using skyrme_saturation_values (abs_nonneg x) (abs_nonneg y) (abs_nonneg z) ha hb hc
  · intro h
    have hg := skyrme_energy_gap x y z
    rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      norm_num [skyrmeBaryon, skyrmeE2, skyrmeE4]
    · rw [h.1, h.2.1, h.2.2] at hg
      norm_num at hg
      linarith

def derrickEnergy (E₂ E₄ μ : ℝ) : ℝ := E₂ / μ + E₄ * μ

theorem derrick_no_pure_sigma_soliton {E₂ : ℝ} (h₂ : 0 < E₂) :
    StrictAntiOn (derrickEnergy E₂ 0) (Set.Ioi 0) ∧
      (∀ μ : ℝ, 0 < μ → ∃ ν : ℝ, 0 < ν ∧
        derrickEnergy E₂ 0 ν < derrickEnergy E₂ 0 μ) ∧
      Tendsto (derrickEnergy E₂ 0) atTop (𝓝 0) := by
  have hs : StrictAntiOn (derrickEnergy E₂ 0) (Set.Ioi 0) := by
    intro a ha b hb hab
    simpa [derrickEnergy] using div_lt_div_of_pos_left h₂ ha hab
  refine ⟨hs, ?_, ?_⟩
  · intro μ hμ
    have hν : 0 < μ + 1 := by positivity
    exact ⟨μ + 1, hν, hs hμ hν (by linarith)⟩
  · have hfun : derrickEnergy E₂ 0 = (fun μ : ℝ => E₂ / μ) := by
      ext μ
      simp [derrickEnergy]
    rw [hfun]
    exact tendsto_id.const_div_atTop E₂

theorem derrick_skyrme_virial_minimum {E₂ E₄ : ℝ} (h₂ : 0 < E₂) (h₄ : 0 < E₄) :
    let μstar := Real.sqrt (E₂ / E₄)
    0 < μstar ∧ E₂ / μstar = E₄ * μstar ∧
      derrickEnergy E₂ E₄ μstar = 2 * Real.sqrt (E₂ * E₄) ∧
      ∀ μ : ℝ, 0 < μ → μ ≠ μstar →
        derrickEnergy E₂ E₄ μstar < derrickEnergy E₂ E₄ μ := by
  let s := Real.sqrt (E₂ / E₄)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos h₂ h₄)
  have hs₂ : E₄ * s ^ 2 = E₂ := by
    dsimp [s]
    rw [Real.sq_sqrt (div_pos h₂ h₄).le, mul_comm, div_mul_cancel₀ _ h₄.ne']
  have hsqrt : E₄ * s = Real.sqrt (E₂ * E₄) := by
    apply (sq_eq_sq₀ (mul_nonneg h₄.le hs.le) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (mul_nonneg h₂.le h₄.le)]
    linear_combination E₄ * hs₂
  have hvirial : E₂ / s = E₄ * s := by
    apply (div_eq_iff hs.ne').2
    simpa [pow_two, mul_assoc] using hs₂.symm
  refine ⟨hs, hvirial, ?_, ?_⟩
  · change derrickEnergy E₂ E₄ s = _
    rw [derrickEnergy, hvirial, hsqrt]
    ring
  · intro μ hμ hne
    have hgap : derrickEnergy E₂ E₄ μ - derrickEnergy E₂ E₄ s =
        E₄ * (μ - s) ^ 2 / μ := by
      rw [derrickEnergy, derrickEnergy, hvirial]
      apply (eq_div_iff hμ.ne').2
      rw [sub_mul, add_mul, div_mul_cancel₀ _ hμ.ne']
      linear_combination -1 * hs₂
    have hpos : 0 < E₄ * (μ - s) ^ 2 / μ :=
      div_pos (mul_pos h₄ (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))) hμ
    linarith

end D5.S3.Quantum.Gauge.ChiralSymmetrySkyrme4D
