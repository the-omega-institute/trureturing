import D5.S3.Quantum.Semigroups.WuCubicConditionedHessian
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Vec

/-! The physical relative anticommutator for the conditioned Wu cubic Hessian. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicRelativeAnticommutator

open WuCubicOperatorBridge (Mat Occupation)
open WuCubicTranslationEnergy (base baseEntry)
open private base_diagonal from D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

abbrev Entry := Occupation × Occupation
abbrev Operator := Matrix Entry Entry ℂ

/-- The anticommutator matrix acting on column-major vectorization. -/
def anticommutator (M : Mat) : Operator :=
  (1 / 2 : ℂ) • ((1 : Mat) ⊗ₖ M + Mᵀ ⊗ₖ (1 : Mat))

theorem anticommutator_mulVec (M X : Mat) :
    anticommutator M *ᵥ X.vec = ((1 / 2 : ℂ) • (M * X + X * M)).vec := by
  simp only [anticommutator, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_one, Matrix.one_mul,
    Matrix.vec_add, Matrix.vec_smul]

private theorem anticommutator_add (A B : Mat) :
    anticommutator (A + B) = anticommutator A + anticommutator B := by
  simp only [anticommutator, Matrix.transpose_add, Matrix.kronecker_add, Matrix.add_kronecker]
  module

private theorem anticommutator_scalar (c : ℝ) :
    anticommutator ((c : ℂ) • (1 : Mat)) = (c : ℂ) • (1 : Operator) := by
  simp only [anticommutator, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.kronecker_smul, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  module

theorem anticommutator_monotone : Monotone anticommutator := by
  intro A B hAB
  have h : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hOne : (1 : Mat).PosSemidef := Matrix.PosSemidef.one
  have hPos : (anticommutator (B - A)).PosSemidef := by
    have hhalf : (0 : ℂ) ≤ 1 / 2 := by
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    exact ((hOne.kronecker h).add (h.transpose.kronecker hOne)).smul hhalf
  apply Matrix.le_iff.mpr
  have hSub : anticommutator (B - A) = anticommutator B - anticommutator A := by
    apply eq_sub_of_add_eq
    rw [← anticommutator_add, sub_add_cancel]
  exact hSub ▸ hPos

theorem anticommutator_order (M : Mat) (a b : ℝ)
    (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ (b : ℂ) • (1 : Mat)) :
    (a : ℂ) • (1 : Operator) ≤ anticommutator M ∧
      anticommutator M ≤ (b : ℂ) • (1 : Operator) := by
  exact ⟨anticommutator_scalar a ▸ anticommutator_monotone hlo,
    anticommutator_scalar b ▸ anticommutator_monotone hhi⟩

/-- The diagonal entry of the base anticommutator at a column-row pair. -/
def entryWeight (d : Occupation → ℝ) (e : Entry) : ℝ :=
  (d e.1 + d e.2) / 2

theorem anticommutator_base (r : ℝ) :
    anticommutator (base r) = diagonal (fun e => (entryWeight (baseEntry r) e : ℂ)) := by
  simp only [base_diagonal, anticommutator, Matrix.diagonal_transpose, ← Matrix.diagonal_one,
    Matrix.diagonal_kronecker_diagonal, one_mul, mul_one, Matrix.diagonal_add,
    ← Matrix.diagonal_smul]
  congr 1
  funext e
  simp only [entryWeight, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Diagonal inverse square root of the base anticommutator in embedded coordinates. -/
def invSqrtWeight (d : Occupation → ℝ) : Operator :=
  diagonal fun e => (((Real.sqrt (entryWeight d e))⁻¹ : ℝ) : ℂ)

/-- Congruence of the physical anticommutator by the inverse square root of its base. -/
def relativeOperator (d : Occupation → ℝ) (M : Mat) : Operator :=
  invSqrtWeight d * anticommutator M * invSqrtWeight d

theorem relativeOperator_mulVec (d : Occupation → ℝ) (M X : Mat) :
    relativeOperator d M *ᵥ X.vec =
      invSqrtWeight d *ᵥ ((1 / 2 : ℂ) •
        (M * (of fun i j => (invSqrtWeight d *ᵥ X.vec) (j, i)) +
          (of fun i j => (invSqrtWeight d *ᵥ X.vec) (j, i)) * M)).vec := by
  rw [relativeOperator, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact congrArg (invSqrtWeight d *ᵥ ·) (anticommutator_mulVec M
    (of fun i j => (invSqrtWeight d *ᵥ X.vec) (j, i)))

private theorem invSqrtWeight_hermitian (d : Occupation → ℝ) :
    (invSqrtWeight d)ᴴ = invSqrtWeight d := by
  simp [invSqrtWeight, Matrix.diagonal_conjTranspose]

private theorem congruence_scalar (d : Occupation → ℝ) (c : ℝ)
    (hpos : ∀ e, 0 < entryWeight d e) :
    invSqrtWeight d * ((c : ℂ) • (1 : Operator)) * invSqrtWeight d =
      diagonal (fun e => ((c / entryWeight d e : ℝ) : ℂ)) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, invSqrtWeight,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext e
  have h : ((Real.sqrt (entryWeight d e))⁻¹ : ℝ) ^ 2 = (entryWeight d e)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (hpos e).le]
  rw [Pi.smul_apply, smul_eq_mul, ← pow_two, ← Complex.ofReal_pow, h,
    ← Complex.ofReal_mul, ← div_eq_mul_inv]

private theorem real_diagonal_le_iff {f g : Entry → ℝ} :
    diagonal (fun e => (f e : ℂ)) ≤ diagonal (fun e => (g e : ℂ)) ↔ ∀ e, f e ≤ g e := by
  simp only [Matrix.le_iff, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff,
    ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg]

/-- The relative operator inherits the spectral endpoints (a/w_{\max}) and
(b/w_{\min}) from the two input intervals. -/
theorem relativeOperator_order (d : Occupation → ℝ) (M : Mat) (a b wMin wMax : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hw : 0 < wMin)
    (hweight : ∀ e, wMin ≤ entryWeight d e ∧ entryWeight d e ≤ wMax)
    (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ (b : ℂ) • (1 : Mat)) :
    ((a / wMax : ℝ) : ℂ) • (1 : Operator) ≤ relativeOperator d M ∧
      relativeOperator d M ≤ ((b / wMin : ℝ) : ℂ) • (1 : Operator) := by
  have hpos (e : Entry) : 0 < entryWeight d e := hw.trans_le (hweight e).1
  obtain ⟨hlo', hhi'⟩ := anticommutator_order M a b hlo hhi
  have hcongrLo := star_left_conjugate_le_conjugate hlo' (invSqrtWeight d)
  have hcongrHi := star_left_conjugate_le_conjugate hhi' (invSqrtWeight d)
  simp only [Matrix.star_eq_conjTranspose, invSqrtWeight_hermitian,
    congruence_scalar d _ hpos] at hcongrLo hcongrHi
  constructor
  · rw [Matrix.smul_one_eq_diagonal]
    exact (real_diagonal_le_iff.mpr (fun e =>
      div_le_div_of_nonneg_left ha.le (hpos e) (hweight e).2)).trans hcongrLo
  · rw [Matrix.smul_one_eq_diagonal]
    exact hcongrHi.trans (real_diagonal_le_iff.mpr (fun e =>
      div_le_div_of_nonneg_left hb hw (hweight e).1))

private theorem eigenvalues_mem_Icc {A : Operator} (hA : A.IsHermitian) {a b : ℝ}
    (hlo : (a : ℂ) • (1 : Operator) ≤ A) (hhi : A ≤ (b : ℂ) • (1 : Operator))
    (i : Entry) : a ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ b := by
  let U := hA.eigenvectorUnitary
  have hD : star (U : Operator) * A * (U : Operator) =
      diagonal (fun e => (hA.eigenvalues e : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hscalar (c : ℝ) : star (U : Operator) * ((c : ℂ) • (1 : Operator)) * (U : Operator) =
      diagonal (fun _ => (c : ℂ)) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Unitary.coe_star_mul_self, Matrix.smul_one_eq_diagonal]
  have hlo' := star_left_conjugate_le_conjugate hlo (U : Operator)
  have hhi' := star_left_conjugate_le_conjugate hhi (U : Operator)
  rw [hD, hscalar] at hlo' hhi'
  exact ⟨real_diagonal_le_iff.mp hlo' i, real_diagonal_le_iff.mp hhi' i⟩

/-- Spectral interval and a bound on every ratio of eigenvalues of the
positive relative operator. -/
theorem relativeOperator_spectralBounds (d : Occupation → ℝ) (M : Mat)
    (a b wMin wMax : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hw : 0 < wMin)
    (hweight : ∀ e, wMin ≤ entryWeight d e ∧ entryWeight d e ≤ wMax)
    (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ (b : ℂ) • (1 : Mat)) :
    ∃ hP : (relativeOperator d M).IsHermitian,
      (∀ i, a / wMax ≤ hP.eigenvalues i ∧ hP.eigenvalues i ≤ b / wMin) ∧
      (∀ i j, hP.eigenvalues i / hP.eigenvalues j ≤ (b / a) * (wMax / wMin)) := by
  have hwMax : 0 < wMax := hw.trans_le
    ((hweight ((0, 0), (0, 0))).1.trans (hweight ((0, 0), (0, 0))).2)
  have hmin : 0 < a / wMax := div_pos ha hwMax
  obtain ⟨hlo', hhi'⟩ := relativeOperator_order d M a b wMin wMax ha hb hw hweight hlo hhi
  have hI : ((a / wMax : ℝ) : ℂ) • (1 : Operator) ≥ 0 := Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hmin.le))
  have hP := (Matrix.nonneg_iff_posSemidef.mp (hI.trans hlo')).isHermitian
  have hbounds := eigenvalues_mem_Icc hP hlo' hhi'
  refine ⟨hP, hbounds, fun i j => ?_⟩
  calc
    hP.eigenvalues i / hP.eigenvalues j ≤ (b / wMin) / hP.eigenvalues j :=
      div_le_div_of_nonneg_right (hbounds i).2 (hmin.trans_le (hbounds j).1).le
    _ ≤ (b / wMin) / (a / wMax) :=
      div_le_div_of_nonneg_left (div_nonneg hb hw.le) hmin (hbounds j).1
    _ = (b / a) * (wMax / wMin) := by
      field_simp [ha.ne', hw.ne', hwMax.ne']

open private rootScale rootScale_pos rootValue rootRatio from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

private theorem baseEntry_bounds {r : ℝ} (hr : 1 ≤ r) (i : Occupation) :
    baseEntry r (0, 0) ≤ baseEntry r i ∧ baseEntry r i ≤ r ^ 2 * baseEntry r (0, 0) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hrr : r ≤ r ^ 2 := by simpa only [pow_two, mul_one] using
    mul_le_mul_of_nonneg_left hr hr0
  have h₁ := mul_le_mul_of_nonneg_left hr (sq_nonneg (rootScale r))
  have h₂ := mul_le_mul_of_nonneg_left hrr (sq_nonneg (rootScale r))
  obtain ⟨i, j⟩ := i
  fin_cases i <;> fin_cases j <;> constructor <;>
    norm_num [baseEntry, rootValue, finProdFinEquiv, rootRatio, mul_pow, Real.sq_sqrt hr0] <;>
    nlinarith only [h₁, h₂]

/-- The smallest diagonal base entry is attained at the vacuum occupation. -/
theorem physicalWeight_bounds {r : ℝ} (hr : 1 ≤ r) :
    0 < baseEntry r (0, 0) ∧ ∀ e : Entry,
      baseEntry r (0, 0) ≤ entryWeight (baseEntry r) e ∧
        entryWeight (baseEntry r) e ≤ r ^ 2 * baseEntry r (0, 0) := by
  constructor
  · simpa [baseEntry, rootValue, finProdFinEquiv] using
      pow_pos (rootScale_pos (zero_le_one.trans hr)) 2
  · intro e
    unfold entryWeight
    constructor <;> linarith [(baseEntry_bounds hr e.1).1, (baseEntry_bounds hr e.1).2,
      (baseEntry_bounds hr e.2).1, (baseEntry_bounds hr e.2).2]

abbrev physicalRelative (r : ℝ) (M : Mat) : Operator := relativeOperator (baseEntry r) M

/-- For the Gibbs base the ratio of the extreme pair weights is (r^2). -/
theorem physicalRelative_spectralBounds {r : ℝ} (hr : 1 ≤ r) (M : Mat)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ (b : ℂ) • (1 : Mat)) :
    ∃ hP : (physicalRelative r M).IsHermitian,
      (∀ i, a / (r ^ 2 * baseEntry r (0, 0)) ≤ hP.eigenvalues i ∧
        hP.eigenvalues i ≤ b / baseEntry r (0, 0)) ∧
      (∀ i j, hP.eigenvalues i / hP.eigenvalues j ≤ (b / a) * r ^ 2) := by
  obtain ⟨hw, hweight⟩ := physicalWeight_bounds hr
  obtain ⟨hP, heig, hratio⟩ := relativeOperator_spectralBounds (baseEntry r) M a b _ _
    ha hb hw hweight hlo hhi
  exact ⟨hP, heig, by simpa only [mul_div_cancel_right₀ _ hw.ne'] using hratio⟩

/-- With normalized upper endpoint one, the bound specializes to
`(36 / 25) * (9 / 5)` at `a = 5 / 9` and `96 / 35` at `a = 21 / 40`. -/
theorem physicalRelative_normalized {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5)
    (M : Mat) (a : ℝ) (ha : 0 < a)
    (hlo : (a : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ 1) :
    ∃ hP : (physicalRelative r M).IsHermitian,
      (∀ i, a / (r ^ 2 * baseEntry r (0, 0)) ≤ hP.eigenvalues i) ∧
      (∀ i j, hP.eigenvalues i / hP.eigenvalues j ≤ (36 / 25 : ℝ) / a) := by
  obtain ⟨hP, heig, hratio⟩ := physicalRelative_spectralBounds hr M a 1 ha zero_le_one
    hlo (by simpa using hhi)
  refine ⟨hP, fun i => (heig i).1, fun i j => (hratio i j).trans ?_⟩
  have hrsq : r ^ 2 ≤ (36 / 25 : ℝ) := by
    convert pow_le_pow_left₀ (zero_le_one.trans hr) hrhi 2 using 1
    norm_num
  calc
    (1 / a) * r ^ 2 ≤ (1 / a) * (36 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_left hrsq (div_nonneg zero_le_one ha.le)
    _ = (36 / 25 : ℝ) / a := by ring

open WuCubicOperatorBridge (G GInv generator)
open WuCubicTranslationEnergy (sandwich vPairing)
open WuCubicConditionedHessian (degree_contraction mixedDual mixedDual_pairing)
open WuCubicThermalBasis (Index coefficient degree)
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

private def sqrtWeight (d : Occupation → ℝ) : Operator :=
  diagonal fun e => (Real.sqrt (entryWeight d e) : ℂ)

/-- Euclidean coordinates of an embedded direction for the base anticommutator pairing. -/
def weightedVec (d : Occupation → ℝ) (X : Mat) : Entry → ℂ :=
  sqrtWeight d *ᵥ X.vec

private theorem invSqrtWeight_mulVec_weightedVec (d : Occupation → ℝ) (X : Mat)
    (hpos : ∀ e, 0 < entryWeight d e) :
    invSqrtWeight d *ᵥ weightedVec d X = X.vec := by
  rw [weightedVec, Matrix.mulVec_mulVec, invSqrtWeight, sqrtWeight, Matrix.diagonal_mul_diagonal]
  funext e
  rw [Matrix.mulVec_diagonal, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos e)).ne', Complex.ofReal_one, one_mul]

theorem relativeOperator_mulVec_weightedVec (d : Occupation → ℝ) (M X : Mat)
    (hpos : ∀ e, 0 < entryWeight d e) :
    relativeOperator d M *ᵥ weightedVec d X =
      invSqrtWeight d *ᵥ ((1 / 2 : ℂ) • (M * X + X * M)).vec := by
  rw [relativeOperator, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    invSqrtWeight_mulVec_weightedVec d X hpos, anticommutator_mulVec]

theorem relativeOperator_weighted_pairing (d : Occupation → ℝ) (M X Y : Mat)
    (hpos : ∀ e, 0 < entryWeight d e) :
    star (relativeOperator d M *ᵥ weightedVec d X) ⬝ᵥ weightedVec d Y =
      (((1 / 2 : ℂ) • (M * X + X * M))ᴴ * Y).trace := by
  rw [relativeOperator_mulVec_weightedVec d M X hpos, Matrix.star_mulVec,
    invSqrtWeight_hermitian, ← Matrix.dotProduct_mulVec,
    invSqrtWeight_mulVec_weightedVec d Y hpos, Matrix.star_vec_dotProduct_vec]

private theorem physicalWeight_pos {r : ℝ} (hr : 1 ≤ r) (e : Entry) :
    0 < entryWeight (baseEntry r) e :=
  (physicalWeight_bounds hr).1.trans_le ((physicalWeight_bounds hr).2 e).1

theorem weightedVec_sandwich_pairing {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) :
    star (weightedVec (baseEntry r) (sandwich r X)) ⬝ᵥ
      weightedVec (baseEntry r) (sandwich r Y) = vPairing r X Y := by
  have hs : (sqrtWeight (baseEntry r))ᴴ * sqrtWeight (baseEntry r) = anticommutator (base r) := by
    rw [sqrtWeight, anticommutator_base, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← pow_two,
      ← Complex.ofReal_pow, Real.sq_sqrt (physicalWeight_pos hr e).le]
  rw [weightedVec, weightedVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hs, anticommutator_mulVec, Matrix.star_vec_dotProduct_vec]
  unfold vPairing
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  rw [Matrix.trace_mul_cycle' (sandwich r X)ᴴ (sandwich r Y) (base r)]
  simp only [Matrix.mul_assoc, add_comm]

/-- The physical operator pairing realizes the existing dual functional. -/
theorem physicalRelative_mixedDual_pairing {r : ℝ} (hr : 1 ≤ r) (M H Y : Mat)
    (hM : M.IsHermitian) (hW : (sandwich r H).IsHermitian) :
    star (physicalRelative r M *ᵥ weightedVec (baseEntry r) (sandwich r H)) ⬝ᵥ
      weightedVec (baseEntry r) (sandwich r Y) = vPairing r (mixedDual r M H) Y := by
  rw [relativeOperator_weighted_pairing _ M _ _ (physicalWeight_pos hr),
    mixedDual_pairing hr]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hM.eq, hW.eq, add_comm (sandwich r H * M),
    Matrix.smul_mul, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- The image under the physical relative operator gives the coordinates of
the dual direction in the same Euclidean space. -/
theorem physicalRelative_mixedDual_mulVec {r : ℝ} (hr : 1 ≤ r) (M H : Mat)
    (hM : M.IsHermitian) (hW : (sandwich r H).IsHermitian) :
    physicalRelative r M *ᵥ weightedVec (baseEntry r) (sandwich r H) =
      weightedVec (baseEntry r) (sandwich r (mixedDual r M H)) := by
  have hinv : sqrtWeight (baseEntry r) * invSqrtWeight (baseEntry r) = 1 := by
    rw [sqrtWeight, invSqrtWeight, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext e
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (physicalWeight_pos hr e)).ne',
      Complex.ofReal_one]
  apply star_injective
  apply dotProduct_eq
  intro v
  let Z : Mat := of fun i j => (invSqrtWeight (baseEntry r) *ᵥ v) (j, i)
  let Y := GInv r * Z * GInv r
  have hZ : Z.vec = invSqrtWeight (baseEntry r) *ᵥ v := rfl
  have hY : sandwich r Y = Z := by
    calc
      sandwich r Y = (G r * GInv r) * Z * (GInv r * G r) := by
        dsimp only [sandwich, Y]
        noncomm_ring
      _ = Z := by rw [G_mul_GInv hr, GInv_mul_G hr, one_mul, mul_one]
  have hv : weightedVec (baseEntry r) (sandwich r Y) = v := by
    rw [hY, weightedVec, hZ, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [← hv, physicalRelative_mixedDual_pairing hr M H Y hM hW, weightedVec_sandwich_pairing hr]

theorem physicalRelative_quadratic {r : ℝ} (hr : 1 ≤ r) (M H : Mat)
    (hM : M.IsHermitian) (hW : (sandwich r H).IsHermitian) :
    let u := weightedVec (baseEntry r) (sandwich r H)
    star (physicalRelative r M *ᵥ u) ⬝ᵥ u = (M * (sandwich r H) ^ 2).trace := by
  dsimp only
  rw [physicalRelative_mixedDual_pairing hr M H H hM hW, mixedDual_pairing hr,
    Matrix.add_mul, Matrix.trace_add, pow_two, Matrix.trace_mul_cycle (sandwich r H) M,
    Matrix.mul_assoc, Matrix.trace_mul_comm (sandwich r H * sandwich r H) M]
  ring

theorem weightedVec_degree_contraction {r : ℝ} (hr : 1 ≤ r) (H : Mat)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r H k = 0) :
    let u := weightedVec (baseEntry r) (sandwich r H)
    let v := weightedVec (baseEntry r) (sandwich r (generator r H - (3 : ℂ) • H))
    (star v ⬝ᵥ v).re ≤ (star u ⬝ᵥ u).re := by
  dsimp only
  rw [weightedVec_sandwich_pairing hr, weightedVec_sandwich_pairing hr]
  exact degree_contraction hr H hdegree

end D5.S3.Quantum.Semigroups.WuCubicRelativeAnticommutator
