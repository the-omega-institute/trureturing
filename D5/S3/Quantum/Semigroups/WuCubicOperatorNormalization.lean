import D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import Mathlib.Analysis.Matrix.PosDef
import OmegaBuild.Commands

compile_only_with_mathlib

/-! Ordinary-trace normalization for Wu v1 (3.54), with two equal-cap CAR modes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization

open WuCubicOperatorBridge (Occupation Frame Mat D G GInv generator dissipator)
open WuCubicAngularCertificate (normalizedDeficit physicalFrame normalized_deficit_eq_ordinary_trace)
open WuRepeatedMiddleCubic (alpha weight)
open WuCubicOccupationTaylor (gibbsLevels cubicMass occupationEntropy)
open private cubicMass_pos gibbsLevels_pos spectral_entropy_eq_occupationEntropy
  occupationGibbsProb_fun_eq from
  D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor

open private GInv_mul_G G_mul_GInv rootValue rootScale_pos rootRatio_sq rootScale
  spectralEntropy spectral_entropy_operator spectral_entropy_scale
  weighted_spectral_energy weighted_spectral_energy_scale from
  D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private physicalFrame_columns physicalFrame_rows from
  D5.S3.Quantum.Semigroups.WuCubicAngularCertificate
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private energyKernel from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private occupationBasis from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap

/-- The Wu cubic deficit with the ordinary trace on the occupation matrix. -/
def operatorDeficit (r : ℝ) (X : Mat) : ℝ :=
  let M := G r * X * G r
  (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re -
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re)

private theorem G_adjoint (r : ℝ) : (G r)ᴴ = G r := by
  rw [G, Matrix.diagonal_conjTranspose]
  apply congrArg diagonal
  funext i
  exact Complex.conj_ofReal (rootValue r i)

private theorem recover_input {r : ℝ} (hr : 1 ≤ r) (X : Mat) :
    GInv r * (G r * X * G r) * GInv r = X := by
  calc
    _ = (GInv r * G r) * X * (G r * GInv r) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [GInv_mul_G hr, G_mul_GInv hr, Matrix.one_mul, Matrix.mul_one]

private theorem recover_embedded {r : ℝ} (hr : 1 ≤ r) (M : Mat) :
    G r * (GInv r * M * GInv r) * G r = M := by
  calc
    _ = (G r * GInv r) * M * (GInv r * G r) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [G_mul_GInv hr, GInv_mul_G hr, Matrix.one_mul, Matrix.mul_one]

private theorem deficit_eq_weighted {r : ℝ} (hr : 1 ≤ r) (X : Mat)
    (U : unitary WuCubicDirectedOccupationCap.Mat) (v : Fin 4 → ℝ)
    (hM : G r * X * G r =
      physicalFrame U * diagonal (fun i => (v i : ℂ)) * (physicalFrame U)ᴴ) :
    operatorDeficit r X =
      (∑ i, ∑ j, weight (physicalFrame U) i j * energyKernel r (v i) (v j)) -
        alpha r * spectralEntropy r (physicalFrame U) v := by
  let V := physicalFrame U
  let M := V * diagonal (fun i => (v i : ℂ)) * Vᴴ
  have hX : GInv r * M * GInv r = X := by
    change GInv r * (physicalFrame U * diagonal _ * (physicalFrame U)ᴴ) * GInv r = X
    rw [← hM, recover_input hr X]
  have hE := weighted_spectral_energy hr V (physicalFrame_columns U) (physicalFrame_rows U) v
  have hS := spectral_entropy_operator r V (physicalFrame_columns U) (physicalFrame_rows U) v
  change (9 / 8 : ℝ) *
      (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)).trace.re = _ at hE
  change spectralEntropy r V v =
    (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re at hS
  dsimp only [operatorDeficit]
  change G r * X * G r = M at hM
  rw [hX] at hE
  rw [hM, ← hS, hE]

/-- Exact cubic scaling in an arbitrary unitary frame. The levels may vanish. -/
theorem operatorDeficit_eq_scaled {r : ℝ} (hr : 1 ≤ r) (X : Mat)
    (U : unitary WuCubicDirectedOccupationCap.Mat) (ell m n q : ℝ)
    (hM : G r * X * G r = physicalFrame U *
      diagonal (fun i => ((ell * levelsAt m n q i : ℝ) : ℂ)) * (physicalFrame U)ᴴ) :
    operatorDeficit r X = ell ^ 3 * normalizedDeficit r U m n q := by
  let v := levelsAt m n q
  let V := physicalFrame U
  let N := V * diagonal (fun i => (v i : ℂ)) * Vᴴ
  let Y := GInv r * N * GInv r
  have hNormalized : normalizedDeficit r U m n q = operatorDeficit r Y := by
    dsimp only [operatorDeficit]
    rw [show G r * Y * G r = N from recover_embedded hr N]
    exact normalized_deficit_eq_ordinary_trace hr U m n q
  rw [deficit_eq_weighted hr X U (fun i => ell * v i) hM,
    weighted_spectral_energy_scale, spectral_entropy_scale, hNormalized,
    deficit_eq_weighted hr Y U v (recover_embedded hr N)]
  ring

private theorem exists_ordered_frame {M : Mat} (hM : M.PosSemidef) :
    ∃ (U : unitary WuCubicDirectedOccupationCap.Mat) (v : Fin 4 → ℝ),
      Monotone v ∧ (∀ i, 0 ≤ v i) ∧ Set.range v = spectrum ℝ M ∧
      M = physicalFrame U * diagonal (fun i => (v i : ℂ)) * (physicalFrame U)ᴴ := by
  let e : Fin (Fintype.card Occupation) ≃ Occupation :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : Fin 4 ≃ Fin (Fintype.card Occupation) :=
    finCongr (by simp [Occupation, Fintype.card_prod])
  let p : Fin 4 ≃ Occupation := Fin.revPerm.trans (f.trans e)
  let E : Mat := hM.isHermitian.eigenvectorUnitary
  let V : WuCubicDirectedOccupationCap.Mat := E.submatrix occupationBasis.symm p
  let v : Fin 4 → ℝ := fun i => hM.isHermitian.eigenvalues (p i)
  have hVstar : Vᴴ = Eᴴ.submatrix p occupationBasis.symm := rfl
  have hEcols : Eᴴ * E = 1 := Unitary.coe_star_mul_self hM.isHermitian.eigenvectorUnitary
  have hErows : E * Eᴴ = 1 := Unitary.coe_mul_star_self hM.isHermitian.eigenvectorUnitary
  have hVcols : Vᴴ * V = 1 := by
    rw [hVstar]
    change Eᴴ.submatrix p occupationBasis.symm * E.submatrix occupationBasis.symm p = _
    rw [Matrix.submatrix_mul_equiv, hEcols, Matrix.submatrix_one_equiv]
  have hVrows : V * Vᴴ = 1 := by
    rw [hVstar]
    change E.submatrix occupationBasis.symm p * Eᴴ.submatrix p occupationBasis.symm = _
    rw [Matrix.submatrix_mul_equiv, hErows, Matrix.submatrix_one_equiv]
  let U : unitary WuCubicDirectedOccupationCap.Mat :=
    ⟨V, Unitary.mem_iff.mpr ⟨hVcols, hVrows⟩⟩
  have hV : physicalFrame U = E.submatrix id p := by
    ext o i
    change E (occupationBasis.symm (occupationBasis o)) (p i) = E o (p i)
    rw [Equiv.symm_apply_apply]
  have hV' : (physicalFrame U)ᴴ = Eᴴ.submatrix p id := by
    rw [hV, Matrix.conjTranspose_submatrix]
  refine ⟨U, v, ?_, (fun i => hM.eigenvalues_nonneg (p i)), ?_, ?_⟩
  · have hv (i : Fin 4) : v i = hM.isHermitian.eigenvalues₀ (f i.rev) := by
      change hM.isHermitian.eigenvalues₀ (e.symm (e (f i.rev))) = _
      rw [Equiv.symm_apply_apply]
    intro i j hij
    rw [hv i, hv j]
    apply hM.isHermitian.eigenvalues₀_antitone
    have hrev : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    exact hrev
  · rw [hM.isHermitian.spectrum_real_eq_range_eigenvalues]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨p i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨p.symm i, ?_⟩
      simp [v]
  · let A : Mat := diagonal (fun o => (hM.isHermitian.eigenvalues o : ℂ))
    have hA : A.submatrix p p = diagonal (fun i => (v i : ℂ)) :=
      Matrix.submatrix_diagonal_equiv _ p
    rw [hV', hV, ← hA,
      Matrix.submatrix_mul_equiv E A id p p,
      Matrix.submatrix_mul_equiv (E * A) Eᴴ id p id]
    change M = (E * A * Eᴴ).submatrix id id
    rw [Matrix.submatrix_id_id]
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hM.isHermitian.spectral_theorem

/-- Every nonzero PSD input has an increasing normalized spectrum. The scale is
the largest eigenvalue of the physical sandwich `G r * X * G r`. -/
theorem exists_ordered_normalization {r : ℝ} (hr : 1 ≤ r) {X : Mat}
    (hX : X.PosSemidef) (hX0 : X ≠ 0) :
    ∃ (U : unitary WuCubicDirectedOccupationCap.Mat) (ell m n q : ℝ),
      0 < ell ∧ IsGreatest (spectrum ℝ (G r * X * G r)) ell ∧
      0 ≤ m ∧ m ≤ n ∧ n ≤ q ∧ q ≤ 1 ∧
      G r * X * G r = physicalFrame U *
        diagonal (fun i => ((ell * levelsAt m n q i : ℝ) : ℂ)) * (physicalFrame U)ᴴ ∧
      operatorDeficit r X = ell ^ 3 * normalizedDeficit r U m n q := by
  let M := G r * X * G r
  have hM : M.PosSemidef := by
    simpa only [G_adjoint] using hX.conjTranspose_mul_mul_same (G r)
  have hM0 : M ≠ 0 := by
    intro h
    apply hX0
    calc
      X = GInv r * M * GInv r := (recover_input hr X).symm
      _ = 0 := by simp [h]
  obtain ⟨U, v, hv, hv0, hspec, hdiag⟩ := exists_ordered_frame hM
  let ell := v 3
  have hvle (i : Fin 4) : v i ≤ ell := hv (Fin.le_last i)
  have hell : 0 < ell := by
    by_contra! h
    have hz : v = 0 := funext fun i => le_antisymm ((hvle i).trans h) (hv0 i)
    apply hM0
    rw [hdiag, hz]
    simp [Pi.zero_apply]
  have hmax : IsGreatest (spectrum ℝ M) ell := by
    rw [← hspec]
    refine ⟨⟨3, rfl⟩, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hvle i
  let m := v 0 / ell
  let n := v 1 / ell
  let q := v 2 / ell
  have hlevels : v = fun i => ell * levelsAt m n q i := by
    funext i
    have hscale (x : ℝ) : ell * (x / ell) = x := by
      rw [mul_comm, div_mul_cancel₀ _ hell.ne']
    fin_cases i <;> simp [levelsAt, m, n, q, hscale] <;> rfl
  have hnorm : M = physicalFrame U *
      diagonal (fun i => ((ell * levelsAt m n q i : ℝ) : ℂ)) * (physicalFrame U)ᴴ := by
    rw [hdiag, hlevels]
  exact ⟨U, ell, m, n, q, hell, hmax, div_nonneg (hv0 0) hell.le,
    div_le_div_of_nonneg_right (hv (by decide : (0 : Fin 4) ≤ 1)) hell.le,
    div_le_div_of_nonneg_right (hv (by decide : (1 : Fin 4) ≤ 2)) hell.le,
    (div_le_one hell).mpr (hvle 2), hnorm, operatorDeficit_eq_scaled hr X U ell m n q hnorm⟩

@[simp] theorem operatorDeficit_zero (r : ℝ) : operatorDeficit r 0 = 0 := by
  simp [operatorDeficit]

/-- A bound on the normalized chamber suffices for every complex PSD input. -/
theorem operatorDeficit_nonneg_of_normalized {r : ℝ} (hr : 1 ≤ r)
    (hSpectral : ∀ (U : unitary WuCubicDirectedOccupationCap.Mat) (m n q : ℝ),
      0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 → 0 ≤ normalizedDeficit r U m n q)
    {X : Mat} (hX : X.PosSemidef) :
    0 ≤ operatorDeficit r X := by
  rcases eq_or_ne X 0 with rfl | hX0
  · simp
  obtain ⟨U, ell, m, n, q, hell, _, hm, hmn, hnq, hq, _, h⟩ :=
    exists_ordered_normalization hr hX hX0
  rw [h]
  exact mul_nonneg (pow_nonneg hell.le 3) (hSpectral U m n q hm hmn hnq hq)

/-- The embedded matrix represented by a normalized spectral certificate. -/
def normalizedEmbedded (U : unitary WuCubicDirectedOccupationCap.Mat) (m n q : ℝ) : Mat :=
  physicalFrame U * diagonal (fun i => (levelsAt m n q i : ℂ)) * (physicalFrame U)ᴴ

private theorem scaled_diagonal (V : Frame) (v : Fin 4 → ℝ) (s : ℝ) :
    V * diagonal (fun i => ((s * v i : ℝ) : ℂ)) * Vᴴ =
      (s : ℂ) • (V * diagonal (fun i => (v i : ℂ)) * Vᴴ) := by
  have hdiag : diagonal (fun i => ((s * v i : ℝ) : ℂ)) =
      (s : ℂ) • diagonal (fun i => (v i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    exact Complex.ofReal_mul _ _
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul]

private theorem occupation_diagonal (v : Fin 4 → ℝ) :
    physicalFrame 1 * diagonal (fun i => (v i : ℂ)) * (physicalFrame 1)ᴴ =
      diagonal (fun o => (v (occupationBasis o) : ℂ)) := by
  let A : WuCubicDirectedOccupationCap.Mat := diagonal (fun i => (v i : ℂ))
  change (1 : WuCubicDirectedOccupationCap.Mat).submatrix occupationBasis id * A *
    ((1 : WuCubicDirectedOccupationCap.Mat).submatrix occupationBasis id)ᴴ = _
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change (1 : WuCubicDirectedOccupationCap.Mat).submatrix occupationBasis id *
    A.submatrix id id * (1 : WuCubicDirectedOccupationCap.Mat).submatrix id occupationBasis = _
  calc
    _ = ((1 : WuCubicDirectedOccupationCap.Mat) * A * 1).submatrix
          occupationBasis occupationBasis := by
      rw [← Matrix.submatrix_mul (1 : WuCubicDirectedOccupationCap.Mat) A
        occupationBasis id id Function.bijective_id,
        ← Matrix.submatrix_mul _ 1 occupationBasis id occupationBasis Function.bijective_id]
    _ = _ := by
      rw [Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_diagonal_equiv] <;> rfl

private theorem scalar_sandwich {r : ℝ} (hr : 1 ≤ r) (c : ℝ) :
    G r * ((c : ℂ) • (1 : Mat)) * G r =
      physicalFrame 1 *
        diagonal (fun i => ((c * (rootScale r ^ 2 * r ^ 2) * gibbsLevels r i : ℝ) : ℂ)) *
        (physicalFrame 1)ᴴ := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  rw [occupation_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← pow_two,
    G, Matrix.diagonal_pow, ← Matrix.diagonal_smul]
  congr 1
  funext o
  change (c : ℂ) * (rootValue r o : ℂ) ^ 2 =
    ((c * (rootScale r ^ 2 * r ^ 2) * gibbsLevels r (occupationBasis o) : ℝ) : ℂ)
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rcases o with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rootValue, occupationBasis, finProdFinEquiv, gibbsLevels, mul_pow,
      rootRatio_sq (zero_le_one.trans hr)] <;>
    field_simp [hr0] <;> ring

private theorem gibbs_spectral_entropy_zero {r : ℝ} (hr : 1 ≤ r) :
    spectralEntropy r (physicalFrame 1) (gibbsLevels r) = 0 := by
  change spectralEntropy r WuCubicOccupationTaylor.occupationFrame (gibbsLevels r) = 0
  rw [spectral_entropy_eq_occupationEntropy hr _ (gibbsLevels_pos hr), occupationEntropy,
    occupationGibbsProb_fun_eq hr]
  have hlog (i : Fin 4) :
      Real.log ((gibbsLevels r i ^ 3 / cubicMass (gibbsLevels r)) /
        (gibbsLevels r i ^ 3 / cubicMass (gibbsLevels r))) = 0 := by
    rw [div_self (div_pos (pow_pos (gibbsLevels_pos hr i) 3)
      (cubicMass_pos (gibbsLevels_pos hr))).ne', Real.log_one]
  simp only [D5.S3.Divergence.ClassicalDPI.klDivergence, hlog, mul_zero, Finset.sum_const_zero]

/-- Scalar inputs have zero deficit by the generator and Gibbs entropy identities. -/
theorem operatorDeficit_scalar {r : ℝ} (hr : 1 ≤ r) (c : ℝ) :
    operatorDeficit r ((c : ℂ) • (1 : Mat)) = 0 := by
  have hJ (J : Mat) : dissipator J ((c : ℂ) • (1 : Mat)) = 0 := by
    simp only [dissipator, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    rw [← add_smul, smul_smul,
      show (1 / 2 : ℂ) * ((c : ℂ) + (c : ℂ)) = (c : ℂ) by ring, sub_self]
  have hE : generator r ((c : ℂ) • (1 : Mat)) = 0 := by
    simp only [generator, hJ, smul_zero, add_zero, Finset.sum_const_zero]
  have hS := spectral_entropy_operator r (physicalFrame 1)
    (physicalFrame_columns 1) (physicalFrame_rows 1)
    (fun i => c * (rootScale r ^ 2 * r ^ 2) * gibbsLevels r i)
  dsimp only at hS
  rw [spectral_entropy_scale, gibbs_spectral_entropy_zero hr, mul_zero] at hS
  simp only [operatorDeficit, scalar_sandwich hr c, ← hS, hE, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, mul_zero, sub_zero]

/-- For a positive scalar input, the ordered eigenvalue ratios are realized by
the literal occupation frame with `(m,n,q) = (r⁻²,r⁻¹,r⁻¹)`. -/
theorem scalar_ordered_spectrum {r c : ℝ} (hr : 1 ≤ r) (hc : 0 < c) :
    ∃ ell : ℝ, 0 < ell ∧
      G r * ((c : ℂ) • (1 : Mat)) * G r =
        (ell : ℂ) • normalizedEmbedded 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹ := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hroot : 0 < rootScale r := rootScale_pos hrpos.le
  refine ⟨c * (rootScale r ^ 2 * r ^ 2), by positivity, ?_⟩
  rw [scalar_sandwich hr c, scaled_diagonal] <;> rfl

/-- The occupation-frame Gibbs point gives equality in the normalized deficit. -/
theorem normalizedDeficit_gibbs_zero {r : ℝ} (hr : 1 ≤ r) :
    normalizedDeficit r 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹ = 0 := by
  let s := (rootScale r ^ 2 * r ^ 2)
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hroot : 0 < rootScale r := rootScale_pos hrpos.le
  have hs : 0 < s := by dsimp only [s]; positivity
  have h := operatorDeficit_eq_scaled hr (((1 : ℝ) : ℂ) • (1 : Mat)) 1 (1 * s)
    (r ^ 2)⁻¹ r⁻¹ r⁻¹ (scalar_sandwich hr 1)
  rw [operatorDeficit_scalar hr 1] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (mul_ne_zero one_ne_zero hs.ne'))

/-- Spectral rigidity at equality transfers to the physical operator. The
hypothesis identifies the normalized matrix, allowing all equivalent frames
at repeated eigenvalues. The converse follows from `operatorDeficit_scalar`. -/
theorem operatorDeficit_eq_zero_iff_of_normalized {r : ℝ} (hr : 1 ≤ r)
    (hSpectral : ∀ (U : unitary WuCubicDirectedOccupationCap.Mat) (m n q : ℝ),
      0 ≤ m → m ≤ n → n ≤ q → q ≤ 1 → normalizedDeficit r U m n q = 0 →
        normalizedEmbedded U m n q = normalizedEmbedded 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹)
    {X : Mat} (hX : X.PosSemidef) :
    operatorDeficit r X = 0 ↔ ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : Mat) := by
  constructor
  · intro h
    rcases eq_or_ne X 0 with rfl | hX0
    · exact ⟨0, le_rfl, by simp⟩
    obtain ⟨U, ell, m, n, q, hell, _, hm, hmn, hnq, hq, hM, hΔ⟩ :=
      exists_ordered_normalization hr hX hX0
    have hzero := (mul_eq_zero.mp (hΔ.symm.trans h)).resolve_left (pow_ne_zero _ hell.ne')
    have hN := hSpectral U m n q hm hmn hnq hq hzero
    let s := rootScale r ^ 2 * r ^ 2
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    have hroot : 0 < rootScale r := rootScale_pos hrpos.le
    have hs : 0 < s := by dsimp only [s]; positivity
    let c := ell / s
    have hscale : c * s = ell := div_mul_cancel₀ _ hs.ne'
    have hScalar : G r * ((c : ℂ) • (1 : Mat)) * G r =
        (ell : ℂ) • normalizedEmbedded 1 (r ^ 2)⁻¹ r⁻¹ r⁻¹ := by
      rw [scalar_sandwich hr c, show c * (rootScale r ^ 2 * r ^ 2) = ell from hscale,
        scaled_diagonal] <;> rfl
    have hEmbedded : G r * X * G r = G r * ((c : ℂ) • (1 : Mat)) * G r := by
      rw [hM, scaled_diagonal, hScalar]
      exact congrArg (fun N : Mat => (ell : ℂ) • N) hN
    refine ⟨c, div_nonneg hell.le hs.le, ?_⟩
    calc
      X = GInv r * (G r * X * G r) * GInv r := (recover_input hr X).symm
      _ = (c : ℂ) • (1 : Mat) := by rw [hEmbedded, recover_input hr]
  · rintro ⟨c, _, rfl⟩
    exact operatorDeficit_scalar hr c

run_cmd do
  for theoremName in #[``exists_ordered_normalization, ``operatorDeficit_nonneg_of_normalized,
      ``operatorDeficit_eq_zero_iff_of_normalized] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom for {theoremName}: {axiomName}"

end D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
