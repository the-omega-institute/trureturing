/- GID: D5/S3/Quantum/Approximate/BalancedSU2Commutator
   generality: G
   mirror-B: D5/B/S3/Quantum/Approximate/BalancedSU2Commutator
   mirror-E: none(waiver:kernel-checked-content)
   anchors: []
   utility: none
   digest: Exact balanced commutator decomposition of determinant-one two-dimensional unitaries. -/

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore.
Adapted from zblore/csd-lean4@9b2d2c17e926ae13795119c5f2f62e85ea240c2d:
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/SU2Rotation.lean
(original declarations QuantumInfo.SU2.su2, su2_mul, su2_one, su2_det,
axisRot, axisRot_det), and
https://github.com/zblore/csd-lean4/blob/9b2d2c17e926ae13795119c5f2f62e85ea240c2d/CsdLean4/Mathlib/QuantumInfo/CommutatorDecomposition.lean
(original declarations QuantumInfo.SU2.su2_star through exists_commutator_of_det_one).
Full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
The parameterization, standard pair, reflection and conjugation proofs are licensed reuse.
-/

module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic

@[expose] public section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Approximate.BalancedSU2Commutator
noncomputable section
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The unit-quaternion matrix used by the licensed SU(2) support. -/
noncomputable def su2 (w x y z : ℝ) : Mat2 :=
  !![(w : ℂ) - Complex.I * z, -Complex.I * ((x : ℂ) - Complex.I * y);
     -Complex.I * ((x : ℂ) + Complex.I * y), (w : ℂ) + Complex.I * z]

/-- Quaternion multiplication in matrix form. -/
theorem su2_mul (w x y z w' x' y' z' : ℝ) :
    su2 w x y z * su2 w' x' y' z' =
      su2 (w * w' - x * x' - y * y' - z * z') (w * x' + x * w' + y * z' - z * y')
        (w * y' - x * z' + y * w' + z * x') (w * z' + x * y' - y * x' + z * w') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> ring

theorem su2_one : su2 1 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2]

theorem su2_det (w x y z : ℝ) :
    (su2 w x y z).det = ((w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  rw [su2, Matrix.det_fin_two_of]
  push_cast
  simp [Complex.ext_iff, ← Complex.ofReal_pow]
  constructor <;> ring

/-- Rotation by `theta` about a unit axis. -/
noncomputable def axisRot (a b c θ : ℝ) : Mat2 :=
  su2 (Real.cos (θ / 2)) (a * Real.sin (θ / 2))
    (b * Real.sin (θ / 2)) (c * Real.sin (θ / 2))

theorem axisRot_det {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    (axisRot a b c θ).det = 1 := by
  rw [axisRot, su2_det,
    show Real.cos (θ / 2) ^ 2 + (a * Real.sin (θ / 2)) ^ 2
        + (b * Real.sin (θ / 2)) ^ 2 + (c * Real.sin (θ / 2)) ^ 2 = 1 by
      linear_combination (Real.sin (θ / 2)) ^ 2 * hu + Real.sin_sq_add_cos_sq (θ / 2)]
  norm_num

theorem su2_star (w x y z : ℝ) : star (su2 w x y z) = su2 w (-x) (-y) (-z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Matrix.star_apply, Complex.ext_iff]

theorem su2_mem_unitary {w x y z : ℝ}
    (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) : su2 w x y z ∈ unitary Mat2 := by
  rw [Unitary.mem_iff]
  constructor
  · rw [su2_star, su2_mul, ← su2_one]
    congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)
  · rw [su2_star, su2_mul, ← su2_one]
    congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)

theorem axisRot_mem_unitary {a b c : ℝ}
    (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) : axisRot a b c θ ∈ unitary Mat2 := by
  apply su2_mem_unitary
  nlinarith [Real.sin_sq_add_cos_sq (θ / 2), hu]

theorem su2_star_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z) * su2 w x y z = 1 := by
  rw [su2_star, su2_mul, ← su2_one]
  congr 1 <;> (first | linear_combination hu | linear_combination -hu | ring)

theorem su2_add_star (w x y z : ℝ) :
    su2 w x y z + star (su2 w x y z) = ((2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [su2_star]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2, Complex.ext_iff] <;> ring

theorem star_su2_sub_one_mul_self {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    star (su2 w x y z - 1) * (su2 w x y z - 1)
      = ((2 - 2 * w : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have key : star (su2 w x y z - 1) * (su2 w x y z - 1)
      = star (su2 w x y z) * su2 w x y z + 1 - (su2 w x y z + star (su2 w x y z)) := by
    rw [star_sub, star_one]
    noncomm_ring
  rw [key, su2_star_mul_self hu, su2_add_star]
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 = ((2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    push_cast
    rw [two_smul]
  rw [h2, ← sub_smul]
  congr 1
  push_cast
  ring


theorem norm_su2_sub_one {w x y z : ℝ} (hu : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ‖su2 w x y z - 1‖ = Real.sqrt (2 - 2 * w) := by
  have hw : w ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hw' : w ≤ 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hsq : ‖su2 w x y z - 1‖ * ‖su2 w x y z - 1‖ = 2 - 2 * w := by
    rw [← CStarRing.norm_star_mul_self, star_su2_sub_one_mul_self hu, norm_smul, norm_one,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [← Real.sqrt_mul_self (norm_nonneg (su2 w x y z - 1)), hsq]


theorem norm_axisRot_sub_one {a b c : ℝ} (hu : a ^ 2 + b ^ 2 + c ^ 2 = 1) (θ : ℝ) :
    ‖axisRot a b c θ - 1‖ = Real.sqrt (2 - 2 * Real.cos (θ / 2)) := by
  rw [axisRot]
  refine norm_su2_sub_one ?_
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [hu, h]




noncomputable def skV (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 1 0 0 φ


noncomputable def skW (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := axisRot 0 1 0 φ


noncomputable def skComm (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  skV φ * skW φ * star (skV φ) * star (skW φ)


theorem skComm_eq (φ : ℝ) :
    skComm φ = su2 (1 - 2 * Real.sin (φ / 2) ^ 4)
      (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
  rw [skComm, skV, skW, axisRot, axisRot, su2_star, su2_star, su2_mul, su2_mul, su2_mul]
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  congr 1
  · linear_combination (s ^ 2 + c ^ 2 + 1) * h
  · ring
  · ring
  · ring


theorem skComm_unit (φ : ℝ) :
    (1 - 2 * Real.sin (φ / 2) ^ 4) ^ 2 + (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  set c := Real.cos (φ / 2) with hc
  set s := Real.sin (φ / 2) with hs
  linear_combination (4 * s ^ 4 * (s ^ 2 + c ^ 2 + 1)) * h


theorem norm_skComm_sub_one (φ : ℝ) : ‖skComm φ - 1‖ = 2 * Real.sin (φ / 2) ^ 2 := by
  rw [skComm_eq, norm_su2_sub_one (skComm_unit φ),
    show (2 : ℝ) - 2 * (1 - 2 * Real.sin (φ / 2) ^ 4)
      = (2 * Real.sin (φ / 2) ^ 2) ^ 2 from by ring]
  exact Real.sqrt_sq (by positivity)


theorem norm_skV_sub_one (φ : ℝ) :
    ‖skV φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skV]
  exact norm_axisRot_sub_one (by norm_num) φ

theorem norm_skW_sub_one (φ : ℝ) :
    ‖skW φ - 1‖ = Real.sqrt (2 - 2 * Real.cos (φ / 2)) := by
  rw [skW]
  exact norm_axisRot_sub_one (by norm_num) φ




theorem norm_skV_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  have hpi' := Real.pi_pos
  have hs : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hc1 : Real.cos (φ / 2) ≤ 1 := Real.cos_le_one _
  have hsc : Real.sin (φ / 2) ^ 2 = 1 - Real.cos (φ / 2) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (φ / 2)]
  rw [norm_skV_sub_one, norm_skComm_sub_one, ← Real.sqrt_mul (by norm_num)]
  refine Real.sqrt_le_sqrt ?_
  rw [show (2 : ℝ) * (2 * Real.sin (φ / 2) ^ 2) = 4 * Real.sin (φ / 2) ^ 2 from by ring, hsc]
  nlinarith [hc, hc1]

theorem norm_skW_sub_one_le {φ : ℝ} (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖skComm φ - 1‖ := by
  rw [norm_skW_sub_one, ← norm_skV_sub_one]
  exact norm_skV_sub_one_le h0 hpi


theorem exists_skComm_norm_eq {ε : ℝ} (h0 : 0 ≤ ε) (h2 : ε ≤ 2) :
    ∃ φ : ℝ, 0 ≤ φ ∧ φ ≤ Real.pi ∧ ‖skComm φ - 1‖ = ε ∧
      ‖skV φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε ∧ ‖skW φ - 1‖ ≤ Real.sqrt 2 * Real.sqrt ε := by
  have hhalf : Real.sqrt (ε / 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hnn : 0 ≤ Real.sqrt (ε / 2) := Real.sqrt_nonneg _
  have harc0 : 0 ≤ Real.arcsin (Real.sqrt (ε / 2)) := Real.arcsin_nonneg.2 hnn
  have harc1 : Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have h0φ : (0 : ℝ) ≤ 2 * Real.arcsin (Real.sqrt (ε / 2)) := by linarith
  have hpiφ : 2 * Real.arcsin (Real.sqrt (ε / 2)) ≤ Real.pi := by linarith
  have hsin : Real.sin (2 * Real.arcsin (Real.sqrt (ε / 2)) / 2) = Real.sqrt (ε / 2) := by
    rw [show 2 * Real.arcsin (Real.sqrt (ε / 2)) / 2 = Real.arcsin (Real.sqrt (ε / 2)) from by
      ring]
    exact Real.sin_arcsin (by linarith) hhalf
  have hnorm : ‖skComm (2 * Real.arcsin (Real.sqrt (ε / 2))) - 1‖ = ε := by
    rw [norm_skComm_sub_one, hsin, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨2 * Real.arcsin (Real.sqrt (ε / 2)), h0φ, hpiφ, hnorm, ?_, ?_⟩
  · have hV := norm_skV_sub_one_le h0φ hpiφ
    rwa [hnorm] at hV
  · have hW := norm_skW_sub_one_le h0φ hpiφ
    rwa [hnorm] at hW




theorem exists_su2_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hdet : U.det = 1) :
    ∃ w x y z : ℝ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1 ∧ U = su2 w x y z := by
  have hstar : U⁻¹ = star U :=
    Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hU)
  have hadj : U⁻¹ = U.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have hkey : star U = !![U 1 1, -U 0 1; -U 1 0, U 0 0] := by
    rw [← hstar, hadj, Matrix.adjugate_fin_two]
  have h11 : U 1 1 = starRingEnd ℂ (U 0 0) := by
    have h : (star U) 0 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination -h
  have h10 : U 1 0 = -starRingEnd ℂ (U 0 1) := by
    have h : (star U) 1 0
        = (!![U 1 1, -U 0 1; -U 1 0, U 0 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by rw [hkey]
    simp [Matrix.star_apply] at h
    linear_combination h
  have hrow : U 0 0 * starRingEnd ℂ (U 0 0) + U 0 1 * starRingEnd ℂ (U 0 1) = 1 := by
    have h : (U * star U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      rw [Unitary.mul_star_self_of_mem hU]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] at h
    linear_combination h
  have hrow' : Complex.normSq (U 0 0) + Complex.normSq (U 0 1) = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj] at hrow
    exact_mod_cast hrow
  refine ⟨(U 0 0).re, -(U 0 1).im, -(U 0 1).re, -(U 0 0).im, ?_, ?_⟩
  · simp only [Complex.normSq_apply] at hrow'
    nlinarith [hrow']
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [su2, h11, h10, Complex.ext_iff]




theorem su2_conj_pure {m₁ m₂ m₃ : ℝ} (hm : m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1) (w x y z : ℝ) :
    su2 0 m₁ m₂ m₃ * su2 w x y z * star (su2 0 m₁ m₂ m₃)
      = su2 w (2 * (m₁ * x + m₂ * y + m₃ * z) * m₁ - x)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₂ - y)
          (2 * (m₁ * x + m₂ * y + m₃ * z) * m₃ - z) := by
  rw [su2_star, su2_mul, su2_mul]
  congr 1
  · linear_combination w * hm
  · linear_combination (-x) * hm
  · linear_combination (-y) * hm
  · linear_combination (-z) * hm


theorem bisector_reflect {p₁ p₂ p₃ n₁ n₂ n₃ ρ : ℝ} (hp : p₁ ^ 2 + p₂ ^ 2 + p₃ ^ 2 = ρ)
    (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = ρ)
    (hsum : 0 < (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2) :
    ∃ m₁ m₂ m₃ : ℝ, m₁ ^ 2 + m₂ ^ 2 + m₃ ^ 2 = 1 ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₁ - p₁ = n₁ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₂ - p₂ = n₂ ∧
      2 * (m₁ * p₁ + m₂ * p₂ + m₃ * p₃) * m₃ - p₃ = n₃ := by
  obtain ⟨r, hrpos, hr⟩ : ∃ r : ℝ, 0 < r ∧
      r ^ 2 = (p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2 :=
    ⟨Real.sqrt ((p₁ + n₁) ^ 2 + (p₂ + n₂) ^ 2 + (p₃ + n₃) ^ 2), Real.sqrt_pos.2 hsum,
      Real.sq_sqrt (le_of_lt hsum)⟩
  have hrne : r ≠ 0 := ne_of_gt hrpos
  refine ⟨(p₁ + n₁) / r, (p₂ + n₂) / r, (p₃ + n₃) / r, ?_, ?_, ?_, ?_⟩
  · field_simp
    rw [hr]
  · field_simp
    rw [hr]
    linear_combination (p₁ + n₁) * hp - (p₁ + n₁) * hn
  · field_simp
    rw [hr]
    linear_combination (p₂ + n₂) * hp - (p₂ + n₂) * hn
  · field_simp
    rw [hr]
    linear_combination (p₃ + n₃) * hp - (p₃ + n₃) * hn




theorem norm_conj_sub_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] {S : E}
    (hS : S ∈ unitary E) (K : E) : ‖S * K * star S - 1‖ = ‖K - 1‖ := by
  have hexp : S * (K - 1) * star S = S * K * star S - S * star S := by noncomm_ring
  have h1 : S * K * star S - 1 = S * (K - 1) * star S := by
    rw [hexp, Unitary.mul_star_self_of_mem hS]
  rw [h1, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hS),
    CStarRing.norm_mem_unitary_mul _ hS]


theorem conj_groupCommutator {E : Type*} [Monoid E] [StarMul E] {S : E} (hS : S ∈ unitary E)
    (V W : E) :
    (S * V * star S) * (S * W * star S) * star (S * V * star S) * star (S * W * star S)
      = S * (V * W * star V * star W) * star S := by
  have hss : star S * S = 1 := Unitary.star_mul_self_of_mem hS
  have hsv : star (S * V * star S) = S * star V * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  have hsw : star (S * W * star S) = S * star W * star S := by
    simp only [star_mul, star_star]
    noncomm_ring
  rw [hsv, hsw]
  calc S * V * star S * (S * W * star S) * (S * star V * star S) * (S * star W * star S)
      = S * V * (star S * S) * W * (star S * S) * star V * (star S * S) * star W * star S := by
        noncomm_ring
    _ = S * (V * W * star V * star W) * star S := by
        rw [hss]
        noncomm_ring


theorem star_groupCommutator {E : Type*} [Monoid E] [StarMul E] (V W : E) :
    star (V * W * star V * star W) = W * V * star W * star V := by
  simp only [star_mul, star_star]
  noncomm_ring




theorem det_conj_of_mem_unitary {S : Matrix (Fin 2) (Fin 2) ℂ}
    (hS : S ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (S * X * star S).det = X.det := by
  have hone : S.det * (star S).det = 1 := by
    rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem hS, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc S.det * X.det * (star S).det = S.det * (star S).det * X.det := by ring
    _ = X.det := by rw [hone, one_mul]



theorem exists_commutator_of_det_one {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ)) (hdet : U.det = 1) :
    ∃ V W : Matrix (Fin 2) (Fin 2) ℂ,
      V ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧ W ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) ∧
      V.det = 1 ∧ W.det = 1 ∧
      U = V * W * star V * star W ∧
      ‖V - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ ∧
      ‖W - 1‖ ≤ Real.sqrt 2 * Real.sqrt ‖U - 1‖ := by
  obtain ⟨w, x, y, z, hunit, hUeq⟩ := exists_su2_of_det_one hU hdet
  have hw1 : w ≤ 1 := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hwm1 : -1 ≤ w := by nlinarith [hunit, sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hnn : (0 : ℝ) ≤ 2 - 2 * w := by linarith
  have hnormU : ‖U - 1‖ = Real.sqrt (2 - 2 * w) := by
    rw [hUeq]
    exact norm_su2_sub_one hunit
  have hε0 : (0 : ℝ) ≤ ‖U - 1‖ := norm_nonneg _
  have hε2 : ‖U - 1‖ ≤ 2 := by
    rw [hnormU]
    calc Real.sqrt (2 - 2 * w) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num]
          exact Real.sqrt_sq (by norm_num)
  obtain ⟨φ, hφ0, hφpi, hφnorm, hVb, hWb⟩ := exists_skComm_norm_eq hε0 hε2

  have h2s : 2 * Real.sin (φ / 2) ^ 2 = ‖U - 1‖ := by
    rw [← hφnorm, norm_skComm_sub_one]
  have hsq : (2 * Real.sin (φ / 2) ^ 2) ^ 2 = 2 - 2 * w := by
    rw [h2s, hnormU, Real.sq_sqrt hnn]
  have hw' : w = 1 - 2 * Real.sin (φ / 2) ^ 4 := by nlinarith [hsq]

  have hKeq : skComm φ = su2 w (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)
      (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3))
      (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
    rw [skComm_eq, hw']
  have hKunit := skComm_unit φ
  rw [← hw'] at hKunit

  have hlenU : x ^ 2 + y ^ 2 + z ^ 2 = 1 - w ^ 2 := by linarith [hunit]
  have hlenK : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3)) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) ^ 2 = 1 - w ^ 2 := by
    nlinarith [hKunit]
  have hVu : skV φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skV]; exact axisRot_mem_unitary (by norm_num) φ
  have hWu : skW φ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [skW]; exact axisRot_mem_unitary (by norm_num) φ
  by_cases hopp : (0 : ℝ) < (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
      + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
      + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2
  · -- the generic case: rotate the commutator's axis onto `U`'s
    obtain ⟨m₁, m₂, m₃, hm, hr₁, hr₂, hr₃⟩ := bisector_reflect hlenK hlenU hopp
    have hSu : su2 0 m₁ m₂ m₃ ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
      su2_mem_unitary (by linarith)
    have hconj : su2 0 m₁ m₂ m₃ * skComm φ * star (su2 0 m₁ m₂ m₃) = U := by
      rw [hKeq, su2_conj_pure hm, hUeq, hr₁, hr₂, hr₃]
    refine ⟨su2 0 m₁ m₂ m₃ * skV φ * star (su2 0 m₁ m₂ m₃),
      su2 0 m₁ m₂ m₃ * skW φ * star (su2 0 m₁ m₂ m₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_mem (mul_mem hSu hVu) (Unitary.star_mem hSu)
    · exact mul_mem (mul_mem hSu hWu) (Unitary.star_mem hSu)
    · rw [det_conj_of_mem_unitary hSu, skV, axisRot_det (by norm_num)]
    · rw [det_conj_of_mem_unitary hSu, skW, axisRot_det (by norm_num)]
    · rw [conj_groupCommutator hSu, ← skComm, hconj]
    · rw [norm_conj_sub_one hSu]
      exact hVb
    · rw [norm_conj_sub_one hSu]
      exact hWb
  · -- the opposite case: `U` is the adjoint of the commutator, i.e. the same pair swapped
    have hzero : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
        + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
        + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      have hge : (0 : ℝ) ≤ (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2
          + (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2
          + (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 := by positivity
      linarith [not_lt.1 hopp]
    have hsq1 : (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq2 : (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hsq3 : (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z) ^ 2 = 0 := by
      linarith [sq_nonneg (-(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) + y),
        sq_nonneg (2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2 + z),
        sq_nonneg (2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 + x), hzero]
    have hx : x = -(2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3) := by
      have h := sq_eq_zero_iff.1 hsq1
      linarith
    have hy : y = 2 * Real.cos (φ / 2) * Real.sin (φ / 2) ^ 3 := by
      have h := sq_eq_zero_iff.1 hsq2
      linarith
    have hz : z = -(2 * Real.cos (φ / 2) ^ 2 * Real.sin (φ / 2) ^ 2) := by
      have h := sq_eq_zero_iff.1 hsq3
      linarith
    have hUstar : U = star (skComm φ) := by
      rw [hKeq, su2_star, hUeq, hx, hy, hz]
      congr 1
      ring
    refine ⟨skW φ, skV φ, hWu, hVu, ?_, ?_, ?_, ?_, ?_⟩
    · rw [skW, axisRot_det (by norm_num)]
    · rw [skV, axisRot_det (by norm_num)]
    · rw [hUstar, skComm, star_groupCommutator]
    · exact hWb
    · exact hVb


end
end D5.S3.Quantum.Approximate.BalancedSU2Commutator
