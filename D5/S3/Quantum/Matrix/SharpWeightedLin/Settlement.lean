/- GID: D5/S3/Quantum/Matrix/SharpWeightedLin/Settlement
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SharpWeightedLin/Settlement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp weighted Lin comparison resolving Hiai Problem 4.15. -/

import D5.S3.Quantum.Matrix.SharpWeightedLin.Generality
import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import D5.S3.Quantum.Schatten.Partition
import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.Weil.Pick.DiagonalSignNegativeIndex
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-! The inertia method follows Sra; the sharp scalar barrier gives the weighted endpoint. -/

/- admission_basis: open-problem-resolution (preregistration #31169). -/
noncomputable section
namespace D5.S3.Quantum.Matrix.SharpWeightedLin

section Scalar
open scoped BigOperators

/- The sharp scalar estimate used in the rank-reduced argument. -/
private theorem scalar_power_barrier {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hx : 0 ≤ x) (hax : a * x < 1) :
    x ^ (a / b) * (1 - a * x) ≤ b := by
  have haxb : 0 ≤ (1 - a * x) / b := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le hx haxb hab
  have hsum : a * x + b * ((1 - a * x) / b) = 1 := by
    field_simp
    nlinarith [hab]
  rw [hsum] at hgm
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ x ^ a * ((1 - a * x) / b) ^ b)
      hgm (by positivity : 0 ≤ (1 : ℝ) / b)
  have hbne : b ≠ 0 := ne_of_gt hb
  have hleft : (x ^ a * ((1 - a * x) / b) ^ b) ^ (1 / b) =
      x ^ (a / b) * ((1 - a * x) / b) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx]
    · rw [← Real.rpow_mul haxb]
      have hbmul : b * (1 / b) = 1 := by field_simp
      rw [hbmul, Real.rpow_one]
      simp [div_eq_mul_inv]
  rw [hleft] at hpow
  simp only [Real.one_rpow] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow hb.le
  calc
    x ^ (a / b) * (1 - a * x) =
        b * (x ^ (a / b) * ((1 - a * x) / b)) := by
          field_simp
    _ ≤ b := by simpa [mul_comm] using hmul

/- Tangent-line form of convexity of t ↦ t^(1/a). -/
private theorem scalar_tangent {a b z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hz : 1 ≤ z) :
    (b / a) * (z - 1) ≤ (b * z) ^ (1 / a) := by
  have hz0 : 0 ≤ z := zero_le_one.trans hz
  have hbase : -1 ≤ b * z - 1 := by
    nlinarith [mul_nonneg hb.le hz0]
  have hp : 1 ≤ 1 / a := by
    rw [one_le_div₀ ha]
    nlinarith [hab]
  have h := one_add_mul_self_le_rpow_one_add hbase hp
  have h' : 1 + (1 / a) * (b * z - 1) ≤ (b * z) ^ (1 / a) := by
    simpa [sub_eq_add_neg, add_assoc] using h
  have hrewrite : 1 + (1 / a) * (b * z - 1) = (b / a) * (z - 1) := by
    field_simp
    linear_combination hab
  rw [hrewrite] at h'
  exact h'

/-- Resolvent form of the barrier, including the zero spectral value. -/
private theorem scalar_resolvent {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hx : 0 ≤ x) (hax : a * x < 1) :
    x ^ (1 / b) ≤ (b / a) * ((1 - a * x)⁻¹ - 1) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hd : 0 < 1 - a * x := sub_pos.mpr hax
  have he : 1 / b = a / b + 1 := by
    field_simp
    linarith
  have hmul : x ^ (1 / b) = x ^ (a / b) * x := by
    rw [he, Real.rpow_add' hx]
    · rw [Real.rpow_one]
    · have : 0 < a / b := div_pos ha hb
      positivity
  have h := mul_le_mul_of_nonneg_right (scalar_power_barrier ha hb hab hx hax) hx
  have hres : b / a * ((1 - a * x)⁻¹ - 1) = b * x / (1 - a * x) := by
    field_simp
    <;> ring
  rw [hres, le_div_iff₀ hd]
  calc
    x ^ (1 / b) * (1 - a * x) =
        (x ^ (a / b) * (1 - a * x)) * x := by rw [hmul]; ring
    _ ≤ b * x := h

/- Finite weighted Jensen for the concave power on nonnegative reals. -/
private theorem finite_weighted_rpow_concave {ι : Type*} (s : Finset ι)
    (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ i ∈ s, w i * z i ^ p ≤ (∑ i ∈ s, w i * z i) ^ p := by
  simpa only [smul_eq_mul] using
    (Real.concaveOn_rpow hp0 hp1).le_map_sum hw hw1
      (fun i hi => hz i hi)
end Scalar

section FiniteSpectral
open scoped BigOperators

/-- The sharp power-resolvent estimate for every finite probability measure. -/
private theorem finite_weighted_resolvent_bound {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hax : ∀ i ∈ s, a * x i < 1) :
    (∑ i ∈ s, w i * (x i) ^ (1 / b)) ^ a ≤
      b * ∑ i ∈ s, w i * (1 - a * x i)⁻¹ := by
  let z := ∑ i ∈ s, w i * (1 - a * x i)⁻¹
  have hz : 1 ≤ z := by
    rw [← hw1]
    refine Finset.sum_le_sum fun i hi => ?_
    have hd : 0 < 1 - a * x i := sub_pos.mpr (hax i hi)
    have hdinv : 1 ≤ (1 - a * x i)⁻¹ := by
      rw [one_le_inv₀ hd]
      nlinarith [mul_nonneg ha.le (hx i hi)]
    simpa using mul_le_mul_of_nonneg_left hdinv (hw i hi)
  have hsum : ∑ i ∈ s, w i * (x i) ^ (1 / b) ≤ (b / a) * (z - 1) := by
    calc
      _ ≤ ∑ i ∈ s, w i * ((b / a) * ((1 - a * x i)⁻¹ - 1)) := by
        exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (scalar_resolvent ha hb hab (hx i hi) (hax i hi)) (hw i hi)
      _ = (b / a) * (z - 1) := by
        simp_rw [mul_left_comm (w _) (b / a), mul_sub, mul_one]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, mul_one]
  have hbound := hsum.trans (scalar_tangent ha hb hab hz)
  have hn : 0 ≤ ∑ i ∈ s, w i * (x i) ^ (1 / b) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi) _)
  have hpow := Real.rpow_le_rpow hn hbound ha.le
  have hbz : 0 ≤ b * z := mul_nonneg hb.le (zero_le_one.trans hz)
  rw [← Real.rpow_mul hbz, one_div_mul_cancel ha.ne', Real.rpow_one] at hpow
  exact hpow
end FiniteSpectral

section MatrixSpectral
open _root_.Matrix RHLinalg
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem hermForm_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (u : n → ℂ) :
    hermForm (cfc f A) u = ∑ i, f (hA.eigenvalues i) *
      ‖(star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ u) i‖ ^ 2 := by
  rw [hA.cfc_eq]
  exact hermForm_specMap hA f u

/-- Jensen's inequality for a unit vector and a nonnegative Hermitian matrix. -/
private theorem matrix_rpow_jensen {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (u : n → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    hermForm (CFC.rpow A p) u ≤ (hermForm A u) ^ p := by
  let w := fun i => ‖(star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ u) i‖ ^ 2
  have hw : ∑ i, w i = 1 := (sum_normSq_unitary_mulVec hA.isHermitian u).trans hu
  have hj := finite_weighted_rpow_concave Finset.univ w hA.isHermitian.eigenvalues
    (fun i _ => sq_nonneg _) (by simpa using hw)
    (fun i _ => hA.eigenvalues_nonneg i) hp0 hp1
  have hid : hermForm A u = ∑ i, hA.isHermitian.eigenvalues i * w i := by
    simpa only [specMap_id, id_eq, hermForm, w] using hermForm_specMap hA.isHermitian id u
  have hr : CFC.rpow A p = cfc (fun x : ℝ => x ^ p) A :=
    CFC.rpow_eq_cfc_real hA.nonneg
  rw [hr, hermForm_cfc, hid]
  simpa only [mul_comm, w] using hj

/-- The resolvent estimate needs spectral support only where the vector has mass.
Eigenvalues outside the strict barrier contribute zero. -/
private theorem matrix_spectral_resolvent_bound {X : Matrix n n ℂ} (hX : X.PosSemidef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (u : n → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1)
    (hsupport : ∀ i, ¬ a * hX.isHermitian.eigenvalues i < 1 →
      (star (hX.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ u) i = 0) :
    (hermForm (CFC.rpow X (1 / b)) u) ^ a ≤
      b * hermForm (cfc (fun x : ℝ => (1 - a * x)⁻¹) X) u := by
  let w := fun i => ‖(star (hX.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ u) i‖ ^ 2
  let s := Finset.univ.filter fun i => a * hX.isHermitian.eigenvalues i < 1
  have hwzero : ∀ i, i ∉ s → w i = 0 := by
    intro i hi
    have hi' : ¬ a * hX.isHermitian.eigenvalues i < 1 := by simpa [s] using hi
    simp [w, hsupport i hi']
  have hrestrict (f : n → ℝ) : ∑ i ∈ s, w i * f i = ∑ i, w i * f i := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    rw [hwzero i hi, zero_mul]
  have hmass : ∑ i ∈ s, w i = 1 := by
    have he := hrestrict (fun _ => 1)
    simp only [mul_one] at he
    rw [he]
    exact (sum_normSq_unitary_mulVec hX.isHermitian u).trans hu
  have h := finite_weighted_resolvent_bound s w hX.isHermitian.eigenvalues
    ha hb hab (fun i _ => sq_nonneg _) hmass (fun i _ => hX.eigenvalues_nonneg i)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [hrestrict, hrestrict] at h
  have hr : CFC.rpow X (1 / b) = cfc (fun x : ℝ => x ^ (1 / b)) X :=
    CFC.rpow_eq_cfc_real hX.nonneg
  rw [hr, hermForm_cfc, hermForm_cfc]
  simpa only [mul_comm, w] using h

/-- On the low spectral subspace the compressed Birman--Schwinger form is nonpositive.
The hypothesis on the spectral values expresses the nonsingular case of the shift. -/
private theorem compressed_birman_schwinger_nonpos
    {k : Type*} [Fintype k] [DecidableEq k]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (J : Matrix n k ℂ)
    (hJ : Jᴴ * J = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hne : ∀ i, a * hX.isHermitian.eigenvalues i - 1 ≠ 0)
    (u : k → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1)
    (hsupport : ∀ i, ¬ a * hX.isHermitian.eigenvalues i < 1 →
      (star (hX.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ (J *ᵥ u)) i = 0) :
    hermForm (b⁻¹ • CFC.rpow (Jᴴ * CFC.rpow X (1 / b) * J) a +
      Jᴴ * (a • X - 1)⁻¹ * J) u ≤ 0 := by
  let S := Jᴴ * CFC.rpow X (1 / b) * J
  let V := cfc (fun x : ℝ => (1 - a * x)⁻¹) X
  have hS : S.PosSemidef :=
    (CFC.rpow_nonneg (a := X) (y := 1 / b)).posSemidef.conjTranspose_mul_mul_same J
  have huJ : ∑ i, ‖(J *ᵥ u) i‖ ^ 2 = 1 := by
    rw [← hermForm_one, ← hermForm_conj (1 : Matrix n n ℂ) J u,
      Matrix.mul_one, hJ, hermForm_one, hu]
  have hj := matrix_rpow_jensen hS u hu ha.le (show a ≤ 1 by linarith)
  have hs := matrix_spectral_resolvent_bound hX ha hb hab (J *ᵥ u) huJ hsupport
  have hbound : hermForm (CFC.rpow S a) u ≤ b * hermForm V (J *ᵥ u) := by
    apply hj.trans
    simpa only [S, hermForm_conj, V] using hs
  have hc : cfc (fun x : ℝ => a * x - 1) X = a • X - 1 := by
    exact (cfc_sub (fun x : ℝ => a * x) (fun _ : ℝ => 1) X).trans
      (congrArg₂ (fun P Q : Matrix n n ℂ => P - Q)
        (cfc_const_mul_id a X hX.isHermitian) (cfc_const_one ℝ X hX.isHermitian))
  have hn : ∀ x ∈ spectrum ℝ X, a * x - 1 ≠ 0 := by
    intro x hx
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hne i
  have hinv : (a • X - 1)⁻¹ = -V := by
    rw [← hc, Matrix.nonsing_inv_eq_ringInverse, ← cfc_inv _ X hn]
    have hf : (fun x : ℝ => (a * x - 1)⁻¹) =
        (fun x : ℝ => -((1 - a * x)⁻¹)) := by
      funext x
      rw [show a * x - 1 = -(1 - a * x) by ring, inv_neg]
    rw [hf, cfc_neg]
  have hform : hermForm (b⁻¹ • CFC.rpow S a + Jᴴ * (a • X - 1)⁻¹ * J) u =
      b⁻¹ * hermForm (CFC.rpow S a) u - hermForm V (J *ᵥ u) := by
    rw [hermForm_add, hermForm_conj, hinv]
    simp only [hermForm, smul_mulVec, dotProduct_smul, RCLike.smul_re,
      neg_mulVec, dotProduct_neg, map_neg, sub_eq_add_neg]
  change hermForm (b⁻¹ • CFC.rpow S a + Jᴴ * (a • X - 1)⁻¹ * J) u ≤ 0
  rw [hform]
  have h := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hb.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul, sub_nonpos] using h
end MatrixSpectral

section IndexAssembly
open _root_.Matrix RHLinalg
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- The unit-vector bound extends to the entire low spectral subspace. -/
private theorem compressed_birman_schwinger_nonpos_all
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (J : Matrix n k ℂ)
    (hJ : Jᴴ * J = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hne : ∀ i, a * hX.isHermitian.eigenvalues i - 1 ≠ 0)
    (u : k → ℂ)
    (hsupport : ∀ i, ¬ a * hX.isHermitian.eigenvalues i < 1 →
      (star (hX.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ (J *ᵥ u)) i = 0) :
    hermForm (b⁻¹ • CFC.rpow (Jᴴ * CFC.rpow X (1 / b) * J) a +
      Jᴴ * (a • X - 1)⁻¹ * J) u ≤ 0 := by
  by_cases hu : u = 0
  · subst u
    simp [hermForm]
  have hs : 0 < ∑ i, ‖u i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
      pow_pos (norm_pos_iff.mpr hi) 2⟩
  let r := Real.sqrt (∑ i, ‖u i‖ ^ 2)
  have hr : 0 < r := Real.sqrt_pos.2 hs
  have hrsq : r ^ 2 = ∑ i, ‖u i‖ ^ 2 := Real.sq_sqrt hs.le
  let v : k → ℂ := (r⁻¹ : ℝ) • u
  have hv : ∑ i, ‖v i‖ ^ 2 = 1 := by
    simp only [v, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), mul_pow, ← Finset.mul_sum, ← hrsq]
    field_simp
  have hvs : ∀ i, ¬ a * hX.isHermitian.eigenvalues i < 1 →
      (star (hX.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *ᵥ (J *ᵥ v)) i = 0 := by
    intro i hi
    simp only [v, mulVec_smul, Pi.smul_apply, hsupport i hi, smul_zero]
  have h := compressed_birman_schwinger_nonpos hX J hJ ha hb hab hne v hv hvs
  have hscale (A : Matrix k k ℂ) : hermForm A v = r⁻¹ ^ 2 * hermForm A u := by
    simp only [v, hermForm, star_smul, star_trivial, mulVec_smul,
      dotProduct_smul, smul_dotProduct, RCLike.smul_re, smul_eq_mul]
    ring
  rw [hscale] at h
  by_contra hn
  have hp := mul_pos (pow_pos (inv_pos.mpr hr) 2) (lt_of_not_ge hn)
  linarith

private theorem posIndex_specMap {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (f : ℝ → ℝ) :
    posIndex (specMap_isHermitian hX f) =
      (Finset.univ.filter fun i => 0 < f (hX.eigenvalues i)).card := by
  let d := fun i => f (hX.eigenvalues i)
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let D := _root_.D5.S3.Weil.Pick.DiagonalSignNegativeIndex.realDiagonal d
  have hD := _root_.D5.S3.Weil.Pick.DiagonalSignNegativeIndex.real_diagonal_isHermitian d
  have hi := _root_.D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det
    hD Uᴴ (by simpa only [det_conjTranspose] using (UnitaryGroup.det_isUnit hX.eigenvectorUnitary).star)
  have he : Uᴴᴴ * D * Uᴴ = specMap hX f := by
    simp only [conjTranspose_conjTranspose, D, U, specMap, Unitary.conjStarAlgAut_apply,
      _root_.D5.S3.Weil.Pick.DiagonalSignNegativeIndex.realDiagonal]
    rfl
  have hh : posIndex (isHermitian_conjTranspose_mul_mul Uᴴ hD) =
      posIndex (specMap_isHermitian hX f) := by congr 1
  rw [hh] at hi
  exact hi.1.trans (_root_.D5.S3.Weil.Pick.DiagonalSignNegativeIndex.real_diagonal_inertia_eq_sign_counts d).1

private theorem specMap_affine {X : Matrix n n ℂ} (hX : X.IsHermitian) (a : ℝ) :
    specMap hX (fun x => a * x - 1) = a • X - 1 := by
  change hX.cfc (fun x => a * x - 1) = _
  rw [← hX.cfc_eq]
  exact (cfc_sub (fun x : ℝ => a * x) (fun _ : ℝ => 1) X).trans
    (congrArg₂ (fun P Q : Matrix n n ℂ => P - Q)
      (cfc_const_mul_id a X hX) (cfc_const_one ℝ X hX))

/-- The high spectral coordinates impose at most the positive inertia of the shift
many linear constraints. Their common kernel carries the nonpositive form. -/
private theorem compressed_nonpos_dimension
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (J : Matrix n k ℂ)
    (hJ : Jᴴ * J = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hne : ∀ i, a * hX.isHermitian.eigenvalues i - 1 ≠ 0)
    (hH : (a • X - 1).IsHermitian)
    (hG : (b⁻¹ • CFC.rpow (Jᴴ * CFC.rpow X (1 / b) * J) a +
      Jᴴ * (a • X - 1)⁻¹ * J).IsHermitian) :
    Fintype.card k ≤ posIndex hH + nonposIndex hG := by
  let High := {i : n // ¬ a * hX.isHermitian.eigenvalues i < 1}
  let U : Matrix n n ℂ := hX.isHermitian.eigenvectorUnitary
  let L : (k → ℂ) →ₗ[ℂ] (High → ℂ) :=
    ((star U * J).submatrix Subtype.val id).mulVecLin
  have hsupport (u : k → ℂ) (hu : u ∈ L.ker) :
      ∀ i, ¬ a * hX.isHermitian.eigenvalues i < 1 →
        (star U *ᵥ (J *ᵥ u)) i = 0 := by
    intro i hi
    have hh := congrFun (show L u = 0 from hu) (⟨i, hi⟩ : High)
    change ((star U * J) *ᵥ u) i = 0 at hh
    rwa [← mulVec_mulVec] at hh
  have hform : ∀ u ∈ L.ker, hermForm
      (b⁻¹ • CFC.rpow (Jᴴ * CFC.rpow X (1 / b) * J) a +
        Jᴴ * (a • X - 1)⁻¹ * J) u ≤ 0 := by
    intro u hu
    exact compressed_birman_schwinger_nonpos_all hX J hJ ha hb hab hne u
      (hsupport u hu)
  have hker := finrank_le_nonposIndex hG L.ker hform
  have hdim := L.finrank_range_add_finrank_ker
  have hdimRange := (LinearMap.range L).finrank_le
  have hcount : Fintype.card High = posIndex hH := by
    have hp := posIndex_specMap hX.isHermitian (fun x => a * x - 1)
    have he : posIndex (specMap_isHermitian hX.isHermitian (fun x => a * x - 1)) =
        posIndex hH := by congr 1; exact specMap_affine hX.isHermitian a
    rw [he] at hp
    rw [hp, Fintype.card_subtype]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    have hi := hne i
    constructor
    · intro hh
      exact lt_of_le_of_ne (by linarith) hi.symm
    · intro hh
      linarith
  have hrange : Module.finrank ℂ (LinearMap.range L) ≤ posIndex hH := by
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, hcount] using hdimRange
  have hdim' : Module.finrank ℂ (LinearMap.range L) + Module.finrank ℂ L.ker =
      Fintype.card k := by
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using hdim
  omega

/-- The compressed endpoint count when the affine shift is nonsingular. -/
private theorem compressed_endpoint_count_nonsingular
    (X : Matrix n n ℂ) (hX : X.PosDef)
    (J : Matrix n k ℂ) (hJ : Jᴴ * J = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hne : ∀ i, a * hX.isHermitian.eigenvalues i - 1 ≠ 0) :
    let S := Jᴴ * CFC.rpow X (1 / b) * J
    let M := a • X + b • (J * CFC.rpow S (-a) * Jᴴ) - 1
    ∃ hM : M.IsHermitian, Fintype.card k ≤ nonnegIndex hM := by
  let S := Jᴴ * CFC.rpow X (1 / b) * J
  let H := a • X - 1
  have hH : H.IsHermitian :=
    (hX.isHermitian.smul (IsSelfAdjoint.of_nonneg ha.le)).sub isHermitian_one
  have hXp : (CFC.rpow X (1 / b)).PosDef :=
    CFC.rpow_nonneg.posSemidef.posDef_iff_isUnit.mpr (hX.isUnit.cfcRpow _)
  have hJinj : Function.Injective J.mulVec := by
    intro u v huv
    have hh := congrArg (fun w => Jᴴ *ᵥ w) huv
    simpa only [mulVec_mulVec, hJ, one_mulVec] using hh
  have hS : S.PosDef := hXp.conjTranspose_mul_mul_same hJinj
  let W := b • CFC.rpow S (-a)
  have hW : W.PosDef :=
    (CFC.rpow_nonneg.posSemidef.posDef_iff_isUnit.mpr (hS.isUnit.cfcRpow _)).smul hb
  have hWinv : W⁻¹ = b⁻¹ • CFC.rpow S a := by
    apply Matrix.inv_eq_left_inv
    dsimp [W]
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hb.ne', one_smul,
      CFC.rpow_mul_rpow_neg a hS.isStrictlyPositive]
  have hHunit : IsUnit H.det := by
    apply (isUnit_iff_isUnit_det _).mp
    have he : cfc (fun x : ℝ => a * x - 1) X = H := by
      rw [hX.isHermitian.cfc_eq]
      exact specMap_affine hX.isHermitian a
    rw [← he]
    apply (isUnit_cfc_iff (fun x : ℝ => a * x - 1) X).mpr
    intro x hx
    rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hne i
  have hG : (W⁻¹ + Jᴴ * H⁻¹ * J).IsHermitian :=
    hW.inv.isHermitian.add (isHermitian_conjTranspose_mul_mul J hH.inv)
  have hcount := compressed_nonpos_dimension hX.posSemidef J hJ ha hb hab hne hH
    (show (b⁻¹ • CFC.rpow S a + Jᴴ * H⁻¹ * J).IsHermitian by rwa [hWinv] at hG)
  have hinertia := positive_update_inertia H J W hH hHunit hW
  have hM : (H + J * W * Jᴴ).IsHermitian :=
    hH.add (by simpa using isHermitian_conjTranspose_mul_mul Jᴴ hW.isHermitian)
  have he : H + J * W * Jᴴ =
      a • X + b • (J * CFC.rpow S (-a) * Jᴴ) - 1 := by
    dsimp [H, W]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    abel
  refine ⟨he ▸ hM, ?_⟩
  have hh : nonnegIndex (he ▸ hM) = nonnegIndex hM := by congr 1; exact he.symm
  rw [hh, hinertia]
  have heG : nonposIndex hG = nonposIndex
      (show (b⁻¹ • CFC.rpow S a + Jᴴ * H⁻¹ * J).IsHermitian by
        rwa [hWinv] at hG) := by congr 1; rw [hWinv]
  change Fintype.card k ≤ posIndex hH + nonposIndex hG
  rw [heG]
  exact hcount
end IndexAssembly

section SingularEndpoint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
local instance singularEndpointPow {ι : Type} [Fintype ι] [DecidableEq ι] :
    Pow (Matrix ι ι ℂ) ℝ := ⟨CFC.rpow⟩

/-- The compressed endpoint includes singular values of the shifted matrix.
A threshold below one avoids the finite exceptional spectrum and preserves
all strictly negative eigenvalues, so no limit of matrix powers is needed. -/
private theorem compressed_endpoint_count
    (X : Matrix n n ℂ) (hX : X.PosDef)
    (J : Matrix n k ℂ) (hJ : Jᴴ * J = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    let S := Jᴴ * CFC.rpow X (1 / b) * J
    let M := a • X + b • (J * CFC.rpow S (-a) * Jᴴ) - 1
    ∃ hM : M.IsHermitian, Fintype.card k ≤ nonnegIndex hM := by
  let S := Jᴴ * CFC.rpow X (1 / b) * J
  let Y := J * CFC.rpow S (-a) * Jᴴ
  let M := a • X + b • Y - 1
  have hY : Y.PosSemidef := CFC.rpow_nonneg.posSemidef.mul_mul_conjTranspose_same J
  have hM : M.IsHermitian :=
    ((hX.isHermitian.smul (IsSelfAdjoint.all a)).add (hY.isHermitian.smul (IsSelfAdjoint.all b))).sub isHermitian_one
  refine ⟨hM, ?_⟩
  have hkn : Fintype.card k ≤ Fintype.card n := by
    calc
      Fintype.card k = (Jᴴ * J).rank := by rw [hJ, rank_one]
      _ ≤ J.rank := rank_mul_le_right _ _
      _ ≤ Fintype.card n := rank_le_card_height J
  let N := Finset.univ.filter fun i => hM.eigenvalues i < 0
  by_cases hN : N.Nonempty
  · let r := N.sup' hN hM.eigenvalues
    have hr : r < 0 := (Finset.sup'_lt_iff hN).mpr fun i hi => (Finset.mem_filter.mp hi).2
    have hδ : max 0 (1 + r) < (1 : ℝ) := max_lt (by norm_num) (by linarith)
    obtain ⟨t, ht, hex⟩ :=
      ((Set.Ioo_infinite hδ).sdiff
        (Set.finite_range fun i => a * hX.isHermitian.eigenvalues i)).nonempty
    have ht0 : 0 < t := (le_max_left 0 (1 + r)).trans_lt ht.1
    have ht1 : t < 1 := ht.2
    have htr : 1 + r < t := (le_max_right 0 (1 + r)).trans_lt ht.1
    let Xt := t⁻¹ • X
    have hXt : Xt.PosDef := hX.smul (inv_pos.mpr ht0)
    have hne : ∀ i, a * hXt.isHermitian.eigenvalues i - 1 ≠ 0 := by
      intro i hi
      have he := eigenvalues_real_smul hX.isHermitian t⁻¹ (inv_pos.mpr ht0).le
        hXt.isHermitian i
      rw [he] at hi
      have htne : t ≠ a * hX.isHermitian.eigenvalues i := by
        intro heq
        exact hex ⟨i, heq.symm⟩
      apply htne
      have hh := congrArg (fun z : ℝ => t * z) (sub_eq_zero.mp hi)
      have hcancel : t * (a * (t⁻¹ * hX.isHermitian.eigenvalues i)) =
          a * hX.isHermitian.eigenvalues i := by
        calc
          _ = (t * t⁻¹) * (a * hX.isHermitian.eigenvalues i) := by ring
          _ = a * hX.isHermitian.eigenvalues i := by
            rw [mul_inv_cancel₀ ht0.ne', one_mul]
      rw [hcancel, mul_one] at hh
      exact hh.symm
    obtain ⟨hMt, hcount⟩ := compressed_endpoint_count_nonsingular Xt hXt J hJ ha hb hab hne
    let St := Jᴴ * CFC.rpow Xt (1 / b) * J
    let Mt := a • Xt + b • (J * CFC.rpow St (-a) * Jᴴ) - 1
    change Mt.IsHermitian at hMt
    change Fintype.card k ≤ nonnegIndex hMt at hcount
    let c := (t⁻¹ ^ (1 / b)) ^ (-a)
    have hcpos : 0 < c := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (inv_pos.mpr ht0) _) _
    have hc1 : c ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact Real.one_le_rpow (by simpa using (one_le_inv₀ ht0).mpr ht1.le) (by positivity)
      · linarith
    have htc : t * c ≤ 1 := (mul_le_mul_of_nonneg_left hc1 ht0.le).trans (by simpa using ht1.le)
    have hSt : St = (t⁻¹ ^ (1 / b)) • S := by
      dsimp [St, Xt]
      rw [Schatten.Partition.rpow_smul hX.posSemidef t⁻¹ (inv_pos.mpr ht0).le (1 / b)]
      simp only [Matrix.mul_smul, Matrix.smul_mul, S]
      rfl
    have hSp : S.PosSemidef :=
      CFC.rpow_nonneg.posSemidef.conjTranspose_mul_mul_same J
    have hYt : J * CFC.rpow St (-a) * Jᴴ = c • Y := by
      have hp := Schatten.Partition.rpow_smul hSp (t⁻¹ ^ (1 / b))
        (Real.rpow_pos_of_pos (inv_pos.mpr ht0) _).le (-a)
      change CFC.rpow ((t⁻¹ ^ (1 / b)) • S) (-a) = c • CFC.rpow S (-a) at hp
      rw [hSt, hp]
      simp only [Matrix.mul_smul, Matrix.smul_mul, c, Y]
    let B := M + (1 - t) • (1 : Matrix n n ℂ)
    have hB : B.IsHermitian := hM.add (isHermitian_one.smul (IsSelfAdjoint.all (1 - t)))
    have htMt : (t • Mt).IsHermitian := hMt.smul (IsSelfAdjoint.all t)
    have hdiff : B - t • Mt = (b * (1 - t * c)) • Y := by
      change a • X + b • Y - 1 + (1 - t) • 1 -
        t • (a • (t⁻¹ • X) + b • (J * CFC.rpow St (-a) * Jᴴ) - 1) = _
      rw [hYt]
      simp only [smul_add, smul_sub, smul_smul]
      have hti : t * (a * t⁻¹) = a := by
        rw [mul_left_comm, mul_inv_cancel₀ ht0.ne', mul_one]
      rw [hti]
      module
    have hle : t • Mt ≤ B := by
      apply sub_nonneg.mp
      rw [hdiff]
      exact smul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr htc)) hY.nonneg
    have hmono := nonnegIndex_mono htMt hB hle
    rw [nonnegIndex_real_smul hMt t ht0 htMt] at hmono
    have hlast : nonnegIndex hB ≤ nonnegIndex hM := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hshift : hB.eigenvalues i = hM.eigenvalues i + (1 - t) := by
        have hs : ((1 - t : ℝ) : ℂ) • (1 : Matrix n n ℂ) = (1 - t) • 1 := by
          ext i j
          simp [RCLike.real_smul_eq_coe_mul]
        have hh := LinGProperty.eigenvalues_zero_add_scalar_finite M hM (1 - t)
          (by rw [hs]; exact hB)
          ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
        simpa only [hs, IsHermitian.eigenvalues] using hh
      rw [hshift] at hi
      by_contra hh
      have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hh⟩
      have hri : hM.eigenvalues i ≤ r := Finset.le_sup' _ hiN
      linarith
    exact hcount.trans (hmono.trans hlast)
  · have hnonneg : ∀ i, 0 ≤ hM.eigenvalues i := by
      intro i
      by_contra hi
      exact hN ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hi⟩⟩
    have hc : nonnegIndex hM = Fintype.card n := by
      unfold nonnegIndex
      simp [hnonneg]
    simpa only [hc] using hkn
end SingularEndpoint

section PowerComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {n : ℕ}
local instance : Pow (Matrix (Fin n) (Fin n) ℂ) ℝ := ⟨CFC.rpow⟩

/-- The weighted arithmetic matrix power mean. -/
def hiaiArithmeticMean (α q : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow ((1 - α) • CFC.rpow A q + α • CFC.rpow B q) (1 / q)

/-- The weighted sandwich power mean in Hiai's comparison. -/
def hiaiRMean (α p : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  CFC.rpow (CFC.rpow A ((1 - α) * p / 2) * CFC.rpow B (α * p) *
    CFC.rpow A ((1 - α) * p / 2)) (1 / p)

/-- Operator concavity compares weighted sums at two positive exponents. -/
private theorem weighted_power_sum_le {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hp : 0 < p) (hpq : p ≤ q) :
    a • CFC.rpow A p + b • CFC.rpow B p ≤
      CFC.rpow (a • CFC.rpow A q + b • CFC.rpow B q) (p / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : p / q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos hp hq).le, (div_le_one hq).mpr hpq⟩
  have h := (CFC.concaveOn_rpow (A := Matrix (Fin n) (Fin n) ℂ) hr).2
    (CFC.rpow_nonneg (a := A) (y := q))
    (CFC.rpow_nonneg (a := B) (y := q)) ha hb hab
  change a • CFC.rpow (CFC.rpow A q) (p / q) +
    b • CFC.rpow (CFC.rpow B q) (p / q) ≤
      CFC.rpow (a • CFC.rpow A q + b • CFC.rpow B q) (p / q) at h
  have hpA : CFC.rpow (CFC.rpow A q) (p / q) = CFC.rpow A p := by
    have hpow := CFC.rpow_rpow_of_exponent_nonneg A q (p / q) hq.le hr.1 hA.nonneg
    change CFC.rpow (CFC.rpow A q) (p / q) = CFC.rpow A (q * (p / q)) at hpow
    convert hpow using 1 <;> congr 1 <;> field_simp
  have hpB : CFC.rpow (CFC.rpow B q) (p / q) = CFC.rpow B p := by
    have hpow := CFC.rpow_rpow_of_exponent_nonneg B q (p / q) hq.le hr.1 hB.nonneg
    change CFC.rpow (CFC.rpow B q) (p / q) = CFC.rpow B (q * (p / q)) at hpow
    convert hpow using 1 <;> congr 1 <;> field_simp
  simpa only [hpA, hpB] using h

/-- The arithmetic power mean is positive semidefinite. -/
private theorem hiaiArithmeticMean_posSemidef (α q : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (hiaiArithmeticMean α q A B).PosSemidef :=
  CFC.rpow_nonneg.posSemidef

/-- Every descending eigenvalue of the weighted arithmetic power mean
increases with its positive exponent. -/
private theorem hiaiArithmeticMean_eigenvalue_mono
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {α p q : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hp : 0 < p) (hpq : p ≤ q)
    (j : Fin (Fintype.card (Fin n))) :
    (hiaiArithmeticMean_posSemidef α p A B).isHermitian.eigenvalues₀ j ≤
      (hiaiArithmeticMean_posSemidef α q A B).isHermitian.eigenvalues₀ j := by
  let P := (1 - α) • CFC.rpow A p + α • CFC.rpow B p
  let Q := (1 - α) • CFC.rpow A q + α • CFC.rpow B q
  have hq : 0 < q := hp.trans_le hpq
  have hP : P.PosSemidef := (add_nonneg
    (smul_nonneg (sub_nonneg.mpr hα1) CFC.rpow_nonneg)
    (smul_nonneg hα0 CFC.rpow_nonneg)).posSemidef
  have hQ : Q.PosSemidef := (add_nonneg
    (smul_nonneg (sub_nonneg.mpr hα1) CFC.rpow_nonneg)
    (smul_nonneg hα0 CFC.rpow_nonneg)).posSemidef
  have hPQ : P ≤ CFC.rpow Q (p / q) :=
    weighted_power_sum_le hA hB (sub_nonneg.mpr hα1) hα0 (by ring) hp hpq
  have hQpow : (CFC.rpow Q (p / q)).PosSemidef := CFC.rpow_nonneg.posSemidef
  have he := D5.S3.Quantum.Schatten.eigenvalues_zero_mono hP.isHermitian
    hQpow.isHermitian (sub_nonneg.mpr hPQ).posSemidef j
  rw [eigenvalues_zero_rpow hQ (div_pos hp hq).le hQpow.isHermitian] at he
  have hnonnegP : 0 ≤ hP.isHermitian.eigenvalues₀ j := by
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hP.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  have hnonnegQ : 0 ≤ hQ.isHermitian.eigenvalues₀ j := by
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hQ.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  have hexp : p / q * (1 / p) = 1 / q := by field_simp
  have hpowers := Real.rpow_le_rpow hnonnegP he (by positivity : 0 ≤ 1 / p)
  rw [← Real.rpow_mul hnonnegQ, hexp] at hpowers
  simpa only [hiaiArithmeticMean,
    eigenvalues_zero_rpow hP (by positivity : 0 ≤ 1 / p),
    eigenvalues_zero_rpow hQ (by positivity : 0 ≤ 1 / q)] using hpowers

/-- The sandwich power mean is positive semidefinite. -/
private theorem hiaiRMean_posSemidef (α p : ℝ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (hiaiRMean α p A B).PosSemidef :=
  CFC.rpow_nonneg.posSemidef

/-- The descending sandwich spectrum is a power of the corresponding singular values. -/
private theorem hiaiRMean_eigenvalue_eq_singular
    (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.PosDef)
    (α : ℝ) {p : ℝ} (hp : 0 < p) (j : Fin (Fintype.card (Fin n))) :
    (hiaiRMean_posSemidef α p A B).isHermitian.eigenvalues₀ j =
      _root_.singularValuesSorted
        (CFC.rpow A ((1 - α) * p / 2) * CFC.rpow B (α * p / 2)) j ^ (2 / p) := by
  let P := CFC.rpow A ((1 - α) * p / 2)
  let Q := CFC.rpow B (α * p / 2)
  let C := P * Q
  have hP : P.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have hQ : Q.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have hQQ : Q * Q = CFC.rpow B (α * p) := by
    dsimp [Q]
    rw [← CFC.rpow_add hB.isUnit]
    congr 1
    ring
  have hGram : C * Cᴴ = P * CFC.rpow B (α * p) * P := by
    dsimp [C]
    rw [conjTranspose_mul, hP.eq, hQ.eq]
    calc
      _ = P * (Q * Q) * P := by noncomm_ring
      _ = _ := by rw [hQQ]; rfl
  have hSand : (P * CFC.rpow B (α * p) * P).PosSemidef := by
    exact hGram ▸ posSemidef_self_mul_conjTranspose C
  have hr := eigenvalues_zero_rpow hSand (by positivity : 0 ≤ 1 / p)
    (hiaiRMean_posSemidef α p A B).isHermitian j
  have hs := D5.S3.Quantum.Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero Cᴴ j
  rw [D5.S3.Quantum.Schatten.singularValuesSorted_conjTranspose] at hs
  have hEval : (isHermitian_mul_conjTranspose_self Cᴴᴴ).eigenvalues₀ j =
      hSand.isHermitian.eigenvalues₀ j := by
    congr 1
    simpa only [conjTranspose_conjTranspose] using hGram
  rw [hEval] at hs
  rw [hr, hs, Real.sqrt_eq_rpow, ← Real.rpow_mul]
  · congr 1
    field_simp
    <;> ring
  · simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hSand.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
end PowerComparison

section Endpoint
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance endpointPow {ι : Type} [Fintype ι] [DecidableEq ι] :
    Pow (Matrix ι ι ℂ) ℝ := ⟨CFC.rpow⟩

/-- The spectral endpoint at unit Gram threshold. -/
private theorem weighted_lin_normalized_endpoint {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (j : Fin (Fintype.card (Fin n)))
    (hthreshold : 1 ≤ (posSemidef_self_mul_conjTranspose
      (CFC.rpow X (1 / (2 * b)) * CFC.rpow Y (1 / (2 * a)))).isHermitian.eigenvalues₀ j) :
    ∃ hM : (a • X + b • Y).IsHermitian, 1 ≤ hM.eigenvalues₀ j := by
  let P := CFC.rpow X (1 / (2 * b))
  let Q := CFC.rpow Y (1 / (2 * a))
  let C := P * Q
  have hP : P.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have hQ : Q.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have hQQ : Q * Q = CFC.rpow Y (1 / a) := by
    dsimp [Q]
    rw [← CFC.rpow_add hY.isUnit]
    congr 1
    field_simp
    <;> ring
  have hGram : C * Cᴴ = P * CFC.rpow Y (1 / a) * P := by
    dsimp [C]
    rw [conjTranspose_mul, hP.eq, hQ.eq]
    calc
      _ = P * (Q * Q) * P := by noncomm_ring
      _ = _ := by rw [hQQ]; rfl
  obtain ⟨E, hE, hE2, hErank, hEC⟩ := spectral_lower_projection (C * Cᴴ)
    (posSemidef_self_mul_conjTranspose C) j hthreshold
  have horder : CFC.rpow
      (CFC.rpow X (-(1 / (2 * b))) * E * CFC.rpow X (-(1 / (2 * b)))) a ≤ Y :=
    rank_reduction_order hX hY.posSemidef ha (by linarith) hb (by rwa [hGram] at hEC)
  let K := CFC.rpow X (-(1 / (2 * b))) * E * CFC.rpow X (-(1 / (2 * b)))
  obtain ⟨J, hJ, hS, hKrep⟩ := reduced_projection_compression X E hX hE hE2 hErank ha hb
  let F := a • X + b • CFC.rpow K a
  have hF : F.PosSemidef :=
    (add_nonneg (smul_nonneg ha.le hX.posSemidef.nonneg)
      (smul_nonneg hb.le CFC.rpow_nonneg)).posSemidef
  have hM : (a • X + b • Y).PosSemidef :=
    (add_nonneg (smul_nonneg ha.le hX.posSemidef.nonneg)
      (smul_nonneg hb.le hY.posSemidef.nonneg)).posSemidef
  obtain ⟨hN, hcount⟩ := compressed_endpoint_count X hX J hJ ha hb hab
  have hFI : (F - 1).IsHermitian := hF.isHermitian.sub isHermitian_one
  have hcountF : j.val + 1 ≤ nonnegIndex hFI := by
    have he : a • X + b • (J * CFC.rpow (Jᴴ * CFC.rpow X (1 / b) * J) (-a) * Jᴴ) - 1 =
        F - 1 := by rw [← hKrep]
    have hc : nonnegIndex hN = nonnegIndex hFI := by congr 1
    simpa only [Fintype.card_fin, hc] using hcount
  have hlow : 1 ≤ hF.isHermitian.eigenvalues₀ j :=
    one_le_eigenvalue_of_nonnegIndex_sub_one hF.isHermitian hFI j hcountF
  refine ⟨hM.isHermitian, hlow.trans ?_⟩
  apply D5.S3.Quantum.Schatten.eigenvalues_zero_mono hF.isHermitian hM.isHermitian
  change (a • X + b • Y - (a • X + b • CFC.rpow K a)).PosSemidef
  have hc : a • X + b • Y - (a • X + b • CFC.rpow K a) = b • (Y - CFC.rpow K a) := by
    module
  rw [hc]
  exact (smul_nonneg hb.le (sub_nonneg.mpr horder)).posSemidef

/-- Homogeneity promotes the unit Gram threshold to every spectral value. -/
private theorem weighted_lin_gram_endpoint {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (j : Fin (Fintype.card (Fin n))) :
    ∃ hM : (a • X + b • Y).IsHermitian,
      ((posSemidef_self_mul_conjTranspose
        (CFC.rpow X (1 / (2 * b)) * CFC.rpow Y (1 / (2 * a)))).isHermitian.eigenvalues₀ j) ^
        (a * b) ≤ hM.eigenvalues₀ j := by
  let C := CFC.rpow X (1 / (2 * b)) * CFC.rpow Y (1 / (2 * a))
  let G := C * Cᴴ
  have hG : G.PosSemidef := posSemidef_self_mul_conjTranspose C
  let z := hG.isHermitian.eigenvalues₀ j
  have hz : 0 ≤ z := by
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hG.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  let M := a • X + b • Y
  have hM : M.PosSemidef :=
    (add_nonneg (smul_nonneg ha.le hX.posSemidef.nonneg)
      (smul_nonneg hb.le hY.posSemidef.nonneg)).posSemidef
  refine ⟨hM.isHermitian, ?_⟩
  change z ^ (a * b) ≤ hM.isHermitian.eigenvalues₀ j
  obtain hz0 | hzpos := hz.eq_or_lt
  · rw [← hz0, Real.zero_rpow (mul_pos ha hb).ne']
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hM.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  let r := z ^ (-(a * b))
  have hr : 0 < r := Real.rpow_pos_of_pos hzpos _
  let Xr := r • X
  let Yr := r • Y
  have hXr : Xr.PosDef := hX.smul hr
  have hYr : Yr.PosDef := hY.smul hr
  let d := r ^ (1 / (2 * b)) * r ^ (1 / (2 * a))
  let Cr := CFC.rpow Xr (1 / (2 * b)) * CFC.rpow Yr (1 / (2 * a))
  have hCr : Cr = d • C := by
    dsimp [Cr, Xr, Yr]
    rw [D5.S3.Quantum.Schatten.Partition.rpow_smul hX.posSemidef r hr.le,
      D5.S3.Quantum.Schatten.Partition.rpow_smul hY.posSemidef r hr.le,
      smul_mul_smul_comm]
    rfl
  have hGr : Cr * Crᴴ = (d ^ 2) • G := by
    rw [hCr, conjTranspose_smul, star_trivial, smul_mul_smul_comm]
    change (d * d) • (C * Cᴴ) = (d ^ 2) • (C * Cᴴ)
    rw [pow_two]
  have hd : d ^ 2 * z = 1 := by
    have hd2 : d ^ 2 = z ^ (-1 : ℝ) := by
      dsimp [d]
      rw [mul_pow, ← Real.rpow_mul_natCast hr.le, ← Real.rpow_mul_natCast hr.le,
        ← Real.rpow_add hr, ← Real.rpow_mul hzpos.le]
      congr 1
      have he : -(a * b) * (1 / (2 * b) * 2 + 1 / (2 * a) * 2) = -1 := by
        field_simp
        nlinarith [hab]
      exact he
    rw [hd2, Real.rpow_neg_one]
    exact inv_mul_cancel₀ hzpos.ne'
  have hthreshold : 1 ≤ (posSemidef_self_mul_conjTranspose Cr).isHermitian.eigenvalues₀ j := by
    have hscaled : ((d ^ 2) • G).IsHermitian :=
      hG.isHermitian.smul (IsSelfAdjoint.of_nonneg (sq_nonneg d))
    have hreal : ((d ^ 2 : ℝ) : ℂ) • G = (d ^ 2) • G := by
      ext i k
      simp [RCLike.real_smul_eq_coe_mul]
    have hs := LinGProperty.eigenvalues_zero_smul_finite G hG.isHermitian
      (d ^ 2) (sq_nonneg d)
      (by rw [hreal]; exact hscaled) j
    have he : (posSemidef_self_mul_conjTranspose Cr).isHermitian.eigenvalues₀ j =
        hscaled.eigenvalues₀ j := by congr 1
    rw [he]
    have hs' : hscaled.eigenvalues₀ j = d ^ 2 * z := by
      simpa only [hreal] using hs
    rw [hs', hd]
  obtain ⟨hMr, hlow⟩ := weighted_lin_normalized_endpoint Xr Yr hXr hYr ha hb hab j hthreshold
  have hscale : a • Xr + b • Yr = r • M := by dsimp [Xr, Yr, M]; module
  have hMs : (r • M).IsHermitian :=
    hM.isHermitian.smul (IsSelfAdjoint.of_nonneg hr.le)
  have hreal : (r : ℂ) • M = r • M := by
    ext i k
    simp [RCLike.real_smul_eq_coe_mul]
  have hs := LinGProperty.eigenvalues_zero_smul_finite M hM.isHermitian r hr.le
    (by rw [hreal]; exact hMs) j
  have he : hMr.eigenvalues₀ j = hMs.eigenvalues₀ j := by congr 1
  rw [he] at hlow
  have hs' : hMs.eigenvalues₀ j = r * hM.isHermitian.eigenvalues₀ j := by
    simpa only [hreal] using hs
  have hlow' : 1 ≤ r * hM.isHermitian.eigenvalues₀ j := by rwa [hs'] at hlow
  have hrinv : r * z ^ (a * b) = 1 := by
    dsimp [r]
    rw [← Real.rpow_add hzpos, neg_add_cancel, Real.rpow_zero]
  nlinarith

/-- The sharp weighted Lin endpoint for every descending singular value. -/
private theorem weighted_lin_endpoint {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) (hX : X.PosDef) (hY : Y.PosDef)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∃ hM : (a • X + b • Y).IsHermitian,
      ∀ j : Fin (Fintype.card (Fin n)),
        singularValuesSorted (CFC.rpow X (1 / (2 * b)) *
          CFC.rpow Y (1 / (2 * a))) j ^ (2 * a * b) ≤ hM.eigenvalues₀ j := by
  let C := CFC.rpow X (1 / (2 * b)) * CFC.rpow Y (1 / (2 * a))
  have hM : (a • X + b • Y).IsHermitian :=
    ((hX.posSemidef.smul ha.le).add (hY.posSemidef.smul hb.le)).isHermitian
  refine ⟨hM, ?_⟩
  intro j
  obtain ⟨hM', hbound⟩ := weighted_lin_gram_endpoint X Y hX hY ha hb hab j
  have hs := D5.S3.Quantum.Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero Cᴴ j
  rw [D5.S3.Quantum.Schatten.singularValuesSorted_conjTranspose] at hs
  have he : (isHermitian_mul_conjTranspose_self Cᴴᴴ).eigenvalues₀ j =
      (posSemidef_self_mul_conjTranspose C).isHermitian.eigenvalues₀ j := by congr 1; simp
  rw [he] at hs
  change singularValuesSorted C j ^ (2 * a * b) ≤ hM.eigenvalues₀ j
  rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul]
  · convert hbound using 1 <;> congr 1 <;> ring
  · simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      (posSemidef_self_mul_conjTranspose C).eigenvalues_nonneg
        ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
end Endpoint

section Result
open _root_.Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance resultPow {ι : Type} [Fintype ι] [DecidableEq ι] :
    Pow (Matrix ι ι ℂ) ℝ := ⟨CFC.rpow⟩

/-- Every descending eigenvalue of the sandwich mean is bounded by that of
the arithmetic power mean at and above the sharp weighted exponent. -/
theorem result {n : ℕ} {α p q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hp : 0 < p)
    (hq : α * (1 - α) * p ≤ q)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (j : Fin (Fintype.card (Fin n))) :
    (hiaiRMean_posSemidef α p A B).isHermitian.eigenvalues₀ j ≤
      (hiaiArithmeticMean_posSemidef α q A B).isHermitian.eigenvalues₀ j := by
  let a := 1 - α
  let b := α
  let q0 := a * b * p
  have ha : 0 < a := sub_pos.mpr hα1
  have hb : 0 < b := hα0
  have hq0 : 0 < q0 := mul_pos (mul_pos ha hb) hp
  have hq0q : q0 ≤ q := by dsimp [q0, a, b]; nlinarith [hq]
  let X := CFC.rpow A q0
  let Y := CFC.rpow B q0
  have hX : X.PosDef := (hA.isStrictlyPositive.rpow A q0).posDef
  have hY : Y.PosDef := (hB.isStrictlyPositive.rpow B q0).posDef
  obtain ⟨hM, hbound⟩ := weighted_lin_endpoint X Y hX hY ha hb (by dsimp [a, b]; ring)
  have hXA : CFC.rpow X (1 / (2 * b)) = CFC.rpow A (a * p / 2) := by
    have hc := CFC.rpow_rpow_of_exponent_nonneg A q0 (1 / (2 * b)) hq0.le
      (by positivity) hA.posSemidef.nonneg
    change CFC.rpow (CFC.rpow A q0) (1 / (2 * b)) =
      CFC.rpow A (q0 * (1 / (2 * b))) at hc
    change CFC.rpow (CFC.rpow A q0) (1 / (2 * b)) = _
    rw [hc]
    congr 1
    dsimp [q0]
    field_simp
    <;> ring
  have hYB : CFC.rpow Y (1 / (2 * a)) = CFC.rpow B (b * p / 2) := by
    have hc := CFC.rpow_rpow_of_exponent_nonneg B q0 (1 / (2 * a)) hq0.le
      (by positivity) hB.posSemidef.nonneg
    change CFC.rpow (CFC.rpow B q0) (1 / (2 * a)) =
      CFC.rpow B (q0 * (1 / (2 * a))) at hc
    change CFC.rpow (CFC.rpow B q0) (1 / (2 * a)) = _
    rw [hc]
    congr 1
    dsimp [q0]
    field_simp
    <;> ring
  let C := CFC.rpow A (a * p / 2) * CFC.rpow B (b * p / 2)
  have he : singularValuesSorted C j ^ (2 * a * b) ≤ hM.eigenvalues₀ j := by
    simpa only [hXA, hYB] using hbound j
  have hpowers := Real.rpow_le_rpow
    (Real.rpow_nonneg (singularValuesSorted_nonneg C j) _) he
    (by positivity : 0 ≤ 1 / q0)
  have hscalar : (2 * a * b) * (1 / q0) = 2 / p := by
    dsimp [q0]
    field_simp
  rw [← Real.rpow_mul (singularValuesSorted_nonneg C j), hscalar] at hpowers
  let P := a • X + b • Y
  have hP : P.PosSemidef :=
    ((hX.posSemidef.smul ha.le).add (hY.posSemidef.smul hb.le))
  have hArith : (hiaiArithmeticMean_posSemidef α q0 A B).isHermitian.eigenvalues₀ j =
      hM.eigenvalues₀ j ^ (1 / q0) :=
    eigenvalues_zero_rpow hP (by positivity) _ j
  have hR := hiaiRMean_eigenvalue_eq_singular A B hB α hp j
  have hendpoint :
      (hiaiRMean_posSemidef α p A B).isHermitian.eigenvalues₀ j ≤
        (hiaiArithmeticMean_posSemidef α q0 A B).isHermitian.eigenvalues₀ j := by
    rw [hArith, hR]
    exact hpowers
  exact hendpoint.trans
    (hiaiArithmeticMean_eigenvalue_mono hA.posSemidef hB.posSemidef hα0.le hα1.le hq0 hq0q j)
end Result

end D5.S3.Quantum.Matrix.SharpWeightedLin
