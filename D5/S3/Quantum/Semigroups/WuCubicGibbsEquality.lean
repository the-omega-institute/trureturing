import D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
import D5.S3.Quantum.Semigroups.WuCubicGibbsIsospectral
import OmegaBuild.Commands

/-! Equality on the normalized Gibbs spectrum and transfer to ordinary-trace operators. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicGibbsEquality

open WuCubicDirectedOccupationCap (Mat frameWeight frameVector emptyProbability fullProbability)
open WuCubicAngularCertificate (normalizedDeficit normalized_deficit_eq_ordinary_trace
  physicalFrame endCharge)
open WuCubicOperatorNormalization (normalizedEmbedded normalizedDeficit_gibbs_zero
  operatorDeficit operatorDeficit_nonneg_of_normalized operatorDeficit_eq_zero_iff_of_normalized)
open WuCubicGibbsIsospectral (gibbsRoots gibbsDensity moment deficit deficit_eq_zero_iff
  deficit_ge_moment_sq)
open WuCubicOperatorBridge (GInv)
open WuRepeatedMiddleCubic (alpha weight)
open WuCubicSignedTransfer (sourceDeficitAt)
open private gibbsLogColumn gibbs_log_column gibbsLow gibbsHigh beta gamma energyKernel from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private occupationBasis from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private physicalFrame_columns physicalFrame_rows physicalFrame_weight physicalFrame_charge
  frameWeight_occupation from D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private recover_embedded from D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
open private A a b d respectsGibbsBlocks conjugate_gibbs_eq_iff from
  D5.S3.Quantum.Semigroups.WuCubicGibbsIsospectral

private theorem gibbs_levels {r : ℝ} (hr : 0 < r) :
    levelsAt (r ^ 2)⁻¹ r⁻¹ r⁻¹ = fun i => (r ^ 2)⁻¹ * gibbsRoots r i := by
  funext i
  fin_cases i <;> norm_num [levelsAt, gibbsRoots] <;> field_simp [hr.ne'] <;> ring

private def gibbsEnergy (r : ℝ) (U : unitary Mat) : ℝ :=
  ∑ i, ∑ j, frameWeight U i j *
    (r * gibbsRoots r i - gibbsRoots r j)^2 * (r * gibbsRoots r i + gibbsRoots r j)

/-- Convert the orbit deficit using the actual lowering weights and signed log charge.
The unnormalized roots have top level r² and the deficit is cubic in the roots. -/
private theorem normalized_gibbs_deficit {r : ℝ} (hr : 1 < r) (U : unitary Mat) :
    normalizedDeficit r U (r ^ 2)⁻¹ r⁻¹ r⁻¹ =
      (gamma r * ((r ^ 2)⁻¹)^3) * deficit r U := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  let s : ℝ := (r ^ 2)⁻¹
  let v := levelsAt (r ^ 2)⁻¹ r⁻¹ r⁻¹
  have hv : v = fun i => s * gibbsRoots r i := gibbs_levels hr0
  have hEnergy (V : unitary Mat) :
      (∑ i, ∑ j, weight (physicalFrame V) i j * energyKernel r (v i) (v j)) =
        gamma r * s^3 * gibbsEnergy r V := by
    rw [hv, gibbsEnergy]
    simp only [Finset.mul_sum, physicalFrame_weight]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    unfold energyKernel
    ring
  have hLog (V : unitary Mat) :
      (∑ i, gibbsLogColumn r (physicalFrame V) i * v i ^ 3) =
        (∑ i, Real.log (gibbsLow r * gibbsHigh r) * v i ^ 3) -
          beta r * s ^ 3 * (moment r V - (r ^ 6 - 1)) := by
    rw [hv]
    simp_rw [gibbs_log_column hr.le _ (physicalFrame_columns V), physicalFrame_charge]
    simp only [moment, a, b, d, endCharge, Fin.sum_univ_four]
    ring
  have hEnergy_one : gibbsEnergy r 1 = 0 := by
    norm_num [gibbsEnergy, Fin.sum_univ_four, frameWeight_occupation, gibbsRoots] <;> ring_nf <;> simp
  have hMoment_one : moment r 1 = 0 := by
    norm_num [moment, a, b, d, Fin.sum_univ_four, gibbsRoots, emptyProbability, fullProbability,
      frameVector, Matrix.one_apply, Complex.normSq_apply] <;> ring
  have hcoef : alpha r * beta r =
      gamma r * ((r - 1)^2 * (r + 1) * (r^3 + 1) / (r^3 - 1)) := by
    have hpow : r ^ 3 - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hr (by decide))).ne'
    have hden : 0 < r ^ 2 + r + 1 := by positivity
    have hnorm : 0 < 1 + r ^ 3 := by positivity
    unfold alpha beta gamma
    rw [if_neg hr.ne']
    field_simp [(Real.log_pos hr).ne', hpow, hden.ne', hnorm.ne'] <;> ring
  have hdiff :
      normalizedDeficit r U (r ^ 2)⁻¹ r⁻¹ r⁻¹ -
        normalizedDeficit r 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹ =
      gamma r * s^3 * (gibbsEnergy r U - gibbsEnergy r 1) -
        (alpha r * beta r) * s^3 * (moment r U - moment r 1) := by
    unfold normalizedDeficit sourceDeficitAt
    rw [hEnergy U, hEnergy 1, hLog U, hLog 1]
    ring
  simp only [normalizedDeficit_gibbs_zero hr.le, hEnergy_one, hMoment_one, sub_zero,
    hcoef] at hdiff
  change _ = (gamma r * s ^ 3) * deficit r U
  rw [hdiff]
  unfold deficit gibbsEnergy A
  ring

private theorem embedded_eq_relabel (U : unitary Mat) (m n q : ℝ) :
    normalizedEmbedded U m n q =
      ((U : Mat) * diagonal (fun i => (levelsAt m n q i : ℂ)) * (U : Mat)ᴴ).submatrix
        occupationBasis occupationBasis := by
  unfold normalizedEmbedded physicalFrame
  rw [Matrix.conjTranspose_submatrix]
  let A : Mat := diagonal (fun i => (levelsAt m n q i : ℂ))
  change (U : Mat).submatrix occupationBasis id * A.submatrix id id *
    ((U : Mat)ᴴ).submatrix id occupationBasis = _
  rw [← Matrix.submatrix_mul (U : Mat) A occupationBasis id id Function.bijective_id,
    ← Matrix.submatrix_mul ((U : Mat) * A) (U : Mat)ᴴ occupationBasis id occupationBasis
      Function.bijective_id]

private theorem embedded_gibbs_eq_iff {r : ℝ} (hr : 1 < r) (U : unitary Mat) :
    normalizedEmbedded U (r ^ 2)⁻¹ r⁻¹ r⁻¹ = normalizedEmbedded 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹ ↔
      Unitary.conjStarAlgAut ℂ Mat U (gibbsDensity r) = gibbsDensity r := by
  let Q : Mat := U
  let z := fun i => (levelsAt (r ^ 2)⁻¹ r⁻¹ r⁻¹ i : ℂ)
  have hcols : Qᴴ * Q = 1 := Unitary.coe_star_mul_self U
  have hrows : Q * Qᴴ = 1 := Unitary.coe_mul_star_self U
  have hrel := Matrix.submatrix_injective (α := ℂ)
    occupationBasis.surjective occupationBasis.surjective
  rw [conjugate_gibbs_eq_iff hr, embedded_eq_relabel U, embedded_eq_relabel 1]
  simp only [Submonoid.coe_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  change (Q * diagonal z * Qᴴ).submatrix occupationBasis occupationBasis =
    (diagonal z).submatrix occupationBasis occupationBasis ↔ _
  rw [hrel.eq_iff]
  have hcomm : Q * diagonal z * Qᴴ = diagonal z ↔ Q * diagonal z = diagonal z * Q := by
    constructor
    · intro h
      simpa only [Matrix.mul_assoc, hcols, mul_one] using congrArg (· * Q) h
    · intro h
      rw [h, Matrix.mul_assoc, hrows, mul_one]
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hs : (r ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr0.ne')
  have hz (i j : Fin 4) : z i = z j ↔ gibbsRoots r i = gibbsRoots r j := by
    simp only [z, gibbs_levels hr0]
    constructor
    · intro h
      exact mul_left_cancel₀ hs (Complex.ofReal_injective h)
    · intro h
      rw [h]
  rw [hcomm]
  constructor
  · intro h i j hij
    have he := congrArg (fun M : Mat => M i j) h
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hzero : Q i j * (z i - z j) = 0 := by
      rw [mul_sub, he, mul_comm (Q i j) (z i), sub_self]
    exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr (hij ∘ (hz i j).mp))
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : gibbsRoots r i = gibbsRoots r j
    · rw [(hz i j).mpr hij, mul_comm]
    · have hentry : Q i j = 0 := h i j hij
      simp only [hentry, zero_mul, mul_zero]

/-- On the Gibbs spectrum the normalized deficit is nonnegative and vanishes precisely
when the embedded matrix equals the occupation-frame Gibbs matrix. -/
theorem normalizedDeficit_gibbs {r : ℝ} (hr : 1 ≤ r) (U : unitary Mat) :
    0 ≤ normalizedDeficit r U (r ^ 2)⁻¹ r⁻¹ r⁻¹ ∧
      (normalizedDeficit r U (r ^ 2)⁻¹ r⁻¹ r⁻¹ = 0 ↔
        normalizedEmbedded U (r ^ 2)⁻¹ r⁻¹ r⁻¹ = normalizedEmbedded 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹) := by
  rcases hr.eq_or_lt with rfl | hlt
  · have hD : diagonal (fun i => (levelsAt 1 1 1 i : ℂ)) = (1 : Mat) := by
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> norm_num [levelsAt]
    have hM (V : unitary Mat) : normalizedEmbedded V 1 1 1 = 1 := by
      rw [normalizedEmbedded, hD, Matrix.mul_one, physicalFrame_rows]
    have htrace (V : unitary Mat) :
        operatorDeficit 1 (GInv 1 * normalizedEmbedded V 1 1 1 * GInv 1) =
          normalizedDeficit 1 V 1 1 1 := by
      dsimp only [operatorDeficit]
      rw [recover_embedded le_rfl]
      exact (normalized_deficit_eq_ordinary_trace le_rfl V 1 1 1).symm
    have hzero : normalizedDeficit 1 U 1 1 1 = 0 := by
      rw [← htrace U, hM U, ← hM 1, htrace 1]
      simpa using normalizedDeficit_gibbs_zero (r := 1) le_rfl
    norm_num [hzero, hM]
  · have hr0 : 0 < r := zero_lt_one.trans hlt
    have hscale : 0 < gamma r * ((r ^ 2)⁻¹)^3 := by unfold gamma; positivity
    have hOrbit : 0 ≤ deficit r U :=
      le_trans (by positivity) (deficit_ge_moment_sq r hlt U)
    rw [normalized_gibbs_deficit hlt U, embedded_gibbs_eq_iff hlt U]
    refine ⟨mul_nonneg hscale.le hOrbit, ?_⟩
    rw [mul_eq_zero, or_iff_right hscale.ne', deficit_eq_zero_iff r hlt U]

/-- Strict positivity off the ordered Gibbs spectrum, together with rigidity on
its unitary orbit, gives the ordinary-trace inequality and scalar equality. -/
theorem operatorDeficit_nonneg_and_eq_zero_iff {r : ℝ} (hr : 1 ≤ r)
    (hStrict : ∀ (U : unitary Mat) (m n q : ℝ),
      0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 →
      ¬ (m = (r ^ 2)⁻¹ ∧ n = r⁻¹ ∧ q = r⁻¹) → 0 < normalizedDeficit r U m n q)
    {X : WuCubicOperatorBridge.Mat} (hX : X.PosSemidef) :
    0 ≤ operatorDeficit r X ∧
      (operatorDeficit r X = 0 ↔ ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : WuCubicOperatorBridge.Mat)) := by
  constructor
  · apply operatorDeficit_nonneg_of_normalized hr _ hX
    intro U m n q hm hmn hnq hq
    by_cases he : m = (r ^ 2)⁻¹ ∧ n = r⁻¹ ∧ q = r⁻¹
    · obtain ⟨rfl, rfl, rfl⟩ := he
      exact (normalizedDeficit_gibbs hr U).1
    · exact (hStrict U m n q hm hmn hnq hq he).le
  · apply operatorDeficit_eq_zero_iff_of_normalized hr _ hX
    intro U m n q hm hmn hnq hq hzero
    by_cases he : m = (r ^ 2)⁻¹ ∧ n = r⁻¹ ∧ q = r⁻¹
    · obtain ⟨rfl, rfl, rfl⟩ := he
      exact (normalizedDeficit_gibbs hr U).2.mp hzero
    · exact ((hStrict U m n q hm hmn hnq hq he).ne' hzero).elim

#print axioms normalizedDeficit_gibbs
#print axioms operatorDeficit_nonneg_and_eq_zero_iff

end D5.S3.Quantum.Semigroups.WuCubicGibbsEquality
