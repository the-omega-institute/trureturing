/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: Exact canonical-to-native spectral extraction with scalar and boundary inverse. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization

/-! Finite spectral extraction from the existing five-complex canonical core.
The canonical core belongs to the Ma--Zhang C8 reconstruction (CC BY 4.0).
This supplier proves a gauge equivalence and its inverse, not genericity. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
open Matrix
open scoped BigOperators Matrix
open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open OpenBoundaryMPSMarginalBirationality (mpsState)
open OpenBoundaryMPSDensityRecovery

abbrev A (c : Fin 5 → ℂ) := OpenBoundaryMPSTwoSiteMinimality.core (c, 0, 0)
abbrev L (c : Fin 5 → ℂ) := OpenBoundaryMPSTwoSiteMinimality.left (c, 0, 0)
def h (c : Fin 5 → ℂ) := c 4 - c 1
def D (c : Fin 5 → ℂ) := h c ^ 2 + 4 * c 2 * c 3
def t0 (c : Fin 5 → ℂ) := c 1 - c 0 * c 2
def t1 (c : Fin 5 → ℂ) := 1 + c 3 - c 0 * c 4
def U (c : Fin 5 → ℂ) := h c * t0 c * t1 c - c 2 * t1 c ^ 2 + c 3 * t0 c ^ 2

def Admissible (c : Fin 5 → ℂ) (e : ℂ) : Prop :=
  e ^ 2 = D c ∧ c 2 * D c * U c * (U c + D c) ≠ 0

def lam (c : Fin 5 → ℂ) (e : ℂ) := (h c + e) / (2 * c 2)
def mu (c : Fin 5 → ℂ) (e : ℂ) := (h c - e) / (2 * c 2)
def T (c : Fin 5 → ℂ) (e : ℂ) : Bond :=
  A c 0 * !![1, 1; lam c e, mu c e]
def K (c : Fin 5 → ℂ) (e : ℂ) : Bond := (T c e)⁻¹ * A c 0 * T c e
def u (c : Fin 5 → ℂ) (e : ℂ) := K c e 0 0
def v (c : Fin 5 → ℂ) (e : ℂ) := K c e 0 1
def w (c : Fin 5 → ℂ) (e : ℂ) := K c e 1 0
def t (c : Fin 5 → ℂ) (e : ℂ) := K c e 1 1
def gap (c : Fin 5 → ℂ) (e : ℂ) := -e / c 2
def rho (c : Fin 5 → ℂ) (e : ℂ) := -c 2 / (gap c e * u c e * v c e)
def S (c : Fin 5 → ℂ) (e : ℂ) : Bond := T c e * diagonal ![1, rho c e]
def z (c : Fin 5 → ℂ) (e : ℂ) := -c 2 / (gap c e * u c e ^ 2)
def offset (c : Fin 5 → ℂ) (e : ℂ) := gap c e * v c e * w c e / (-c 2)
def sector (c : Fin 5 → ℂ) (e : ℂ) : OpenBoundaryMPSInteriorRootRealization.Sector :=
  ⟨lam c e, mu c e, lam c e - offset c e⟩

def nativeLeft (c : Fin 5 → ℂ) (e : ℂ) := L c ᵥ* S c e
def nativeRight (c : Fin 5 → ℂ) (e : ℂ) (N : ℕ) (R : Fin 2 → ℂ) :=
  u c e ^ N • ((S c e)⁻¹ *ᵥ R)
/-- The actual two-row left normalizer, computed from the native cores. -/
def leftNormalizer (s : OpenBoundaryMPSInteriorRootRealization.Sector) (zz : ℂ) (l : Fin 2 → ℂ) : Bond :=
  fun i j => (l ᵥ* OpenBoundaryMPSInteriorRootRealization.core s zz i) j

private lemma factors {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    c 2 ≠ 0 ∧ D c ≠ 0 ∧ U c ≠ 0 ∧ U c + D c ≠ 0 ∧ e ≠ 0 := by
  rcases hc with ⟨he, hn⟩
  have hh := (mul_ne_zero_iff.mp hn)
  have hh' := (mul_ne_zero_iff.mp hh.1)
  have hh'' := (mul_ne_zero_iff.mp hh'.1)
  refine ⟨hh''.1, hh''.2, hh'.2, hh.2, ?_⟩
  intro hz
  rw [hz, zero_pow (by decide)] at he
  exact hh''.2 he.symm

private lemma det_A (c : Fin 5 → ℂ) : (A c 0).det = -c 2 := by
  simp [A, OpenBoundaryMPSTwoSiteMinimality.core, det_fin_two]; ring

private lemma det_T {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    (T c e).det = e := by
  rw [T, det_mul, det_A]
  simp [det_fin_two, lam, mu]
  field_simp [(factors hc).1]
  ring

private lemma unit_T {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    IsUnit (T c e).det := by rw [det_T hc]; exact isUnit_iff_ne_zero.mpr (factors hc).2.2.2.2

private lemma left_T (c : Fin 5 → ℂ) (e : ℂ) : L c ᵥ* T c e = ![1, 1] := by
  ext j
  fin_cases j <;> simp [L, T, A, OpenBoundaryMPSTwoSiteMinimality.left, OpenBoundaryMPSTwoSiteMinimality.core, vecMul,
    mul_apply, dotProduct, Fin.sum_univ_two] <;> ring

private lemma eigen {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    A c 1 * !![1, 1; lam c e, mu c e] =
      T c e * diagonal ![lam c e, mu c e] := by
  have he := hc.1
  dsimp [D, h] at he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, A, OpenBoundaryMPSTwoSiteMinimality.core, lam, mu, h, mul_apply, Fin.sum_univ_two]
  all_goals field_simp [(factors hc).1]
  all_goals ring_nf
  all_goals simp only [he]
  all_goals ring

private lemma diagonal_entries {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    u c e = c 2 / e * (t1 c - mu c e * t0 c) ∧
    t c e = c 2 / e * (lam c e * t0 c - t1 c) := by
  have he := hc.1
  dsimp [D, h] at he
  have hi : (T c e)⁻¹ = e⁻¹ • (T c e).adjugate := by
    rw [Matrix.inv_def, det_T hc, Ring.inverse_eq_inv]
  constructor <;> simp only [u, t, K, hi]
  all_goals simp [T, A, OpenBoundaryMPSTwoSiteMinimality.core, adjugate_fin_two,
    mul_apply, Fin.sum_univ_two, lam, mu, h, t0, t1, smul_eq_mul]
  all_goals field_simp [(factors hc).1, (factors hc).2.2.2.2]
  all_goals ring_nf
  all_goals simp only [he]
  all_goals ring

private lemma det_K {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    u c e * t c e - v c e * w c e = -c 2 := by
  change K c e 0 0 * K c e 1 1 - K c e 0 1 * K c e 1 0 = -c 2
  rw [← det_fin_two]
  rw [K, det_mul, det_mul, mul_assoc, mul_comm (A c 0).det,
    ← mul_assoc, det_nonsing_inv_mul_det _ (unit_T hc), one_mul, det_A]

/-- The canonical spectral frame and its four nonzero conjugated entries. -/
theorem spectral_frame {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    (T c e).det = e ∧ L c ᵥ* T c e = ![1, 1] ∧
    (A c 1 * (A c 0)⁻¹) * T c e = T c e * diagonal ![lam c e, mu c e] ∧
    (K c e).det = -c 2 ∧
    u c e * t c e = c 2 * U c / D c ∧
    v c e * w c e = c 2 * (U c + D c) / D c ∧
    u c e ≠ 0 ∧ v c e ≠ 0 ∧ w c e ≠ 0 ∧ t c e ≠ 0 ∧ gap c e ≠ 0 := by
  rcases factors hc with ⟨hc2, hd, hu, hud, he⟩
  have hut : u c e * t c e = c 2 * U c / D c := by
    rw [(diagonal_entries hc).1, (diagonal_entries hc).2, ← hc.1]
    dsimp [U, t0, t1, lam, mu, h]
    field_simp [hc2, he]
    have heq := hc.1
    dsimp [D, h] at heq
    ring_nf
    simp only [heq]
    ring
  have hvw : v c e * w c e = c 2 * (U c + D c) / D c := by
    have hk := det_K hc
    rw [hut] at hk
    field_simp [hd] at *
    linear_combination -hk
  have hut0 := mul_ne_zero_iff.mp (show u c e * t c e ≠ 0 by
    rw [hut]; exact div_ne_zero (mul_ne_zero hc2 hu) hd)
  have hvw0 := mul_ne_zero_iff.mp (show v c e * w c e ≠ 0 by
    rw [hvw]; exact div_ne_zero (mul_ne_zero hc2 hud) hd)
  refine ⟨det_T hc, left_T c e, ?_, ?_, hut, hvw, hut0.1, hvw0.1, hvw0.2,
    hut0.2, div_ne_zero (neg_ne_zero.mpr he) hc2⟩
  · rw [T, Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _
      (isUnit_iff_ne_zero.mpr (by rw [det_A]; exact neg_ne_zero.mpr hc2))]
    exact eigen hc
  · simpa only [det_fin_two, u, v, w, t] using det_K hc

private lemma extraction_algebra {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) = gap c e ∧
    OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = offset c e ∧
    OpenBoundaryMPSInteriorRootRealization.beta (sector c e) =
      gap c e * u c e * t c e / (-c 2) ∧
    rho c e ≠ 0 ∧ z c e ≠ 0 ∧
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.beta (sector c e) ≠ 0 := by
  rcases spectral_frame hc with ⟨_, _, _, _, _, _, hu, hv, hw, ht, hg⟩
  have hc2 := (factors hc).1
  have hd : mu c e - lam c e = gap c e := by
    dsimp [mu, lam, gap]
    field_simp [hc2]
    ring
  have ha : OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = offset c e := by
    simp [OpenBoundaryMPSInteriorRootRealization.alpha, sector]
  have hb : OpenBoundaryMPSInteriorRootRealization.beta (sector c e) =
      gap c e * u c e * t c e / (-c 2) := by
    have hk := det_K hc
    dsimp [OpenBoundaryMPSInteriorRootRealization.beta, sector]
    rw [show mu c e - (lam c e - offset c e) = gap c e + offset c e by rw [← hd]; ring]
    dsimp [offset]
    field_simp [hc2]
    linear_combination hk
  have hd' : OpenBoundaryMPSInteriorRootRealization.delta (sector c e) = gap c e := hd
  refine ⟨hd', ha, hb, ?_, ?_, ?_⟩
  · exact div_ne_zero (neg_ne_zero.mpr hc2) (mul_ne_zero (mul_ne_zero hg hu) hv)
  · exact div_ne_zero (neg_ne_zero.mpr hc2) (mul_ne_zero hg (pow_ne_zero 2 hu))
  · rw [hd', ha, hb]
    exact mul_ne_zero (mul_ne_zero hg (div_ne_zero (mul_ne_zero (mul_ne_zero hg hv) hw)
      (neg_ne_zero.mpr hc2))) (div_ne_zero (mul_ne_zero (mul_ne_zero hg hu) ht)
        (neg_ne_zero.mpr hc2))

private lemma TK {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    A c 0 * T c e = T c e * K c e := by
  rw [K, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ (unit_T hc), one_mul]

private lemma unit_S {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    IsUnit (S c e).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [S, det_mul, det_T hc]
  simpa [det_fin_two] using mul_ne_zero (factors hc).2.2.2.2
    (extraction_algebra hc).2.2.2.1

private lemma core_intertwine {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e)
    (i : Fin 2) : A c i * S c e =
      u c e • (S c e * OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i) := by
  rcases spectral_frame hc with ⟨_, _, hm, _, _, _, hu, hv, hw, ht, hg⟩
  rcases extraction_algebra hc with ⟨hd, ha, hb, hr, hz, hn⟩
  have hc2 := (factors hc).1
  have hdg : K c e * diagonal ![1, rho c e] =
      u c e • (diagonal ![1, rho c e] *
        OpenBoundaryMPSInteriorRootRealization.G (sector c e) (z c e)) := by
    have hK : K c e = !![u c e, v c e; w c e, t c e] := by
      ext j k; fin_cases j <;> fin_cases k <;> rfl
    rw [hK]
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [OpenBoundaryMPSInteriorRootRealization.G, ha, hb, mul_apply,
        Fin.sum_univ_two, smul_eq_mul]
    all_goals dsimp [rho, z, offset]
    all_goals field_simp [hc2, hu, hv, hw, ht, hg]
  have ha1 : A c 1 * T c e =
      T c e * OpenBoundaryMPSInteriorRootRealization.B (sector c e) * K c e := by
    calc
      A c 1 * T c e = (A c 1 * (A c 0)⁻¹) * (A c 0 * T c e) := by
        rw [← mul_assoc, mul_assoc (A c 1), nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (by rw [det_A]; exact neg_ne_zero.mpr hc2)), mul_one]
      _ = _ := by rw [TK hc, ← mul_assoc, hm]; rfl
  have commute : OpenBoundaryMPSInteriorRootRealization.B (sector c e) * diagonal ![1, rho c e] =
      diagonal ![1, rho c e] * OpenBoundaryMPSInteriorRootRealization.B (sector c e) := by
    rw [OpenBoundaryMPSInteriorRootRealization.B, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; ext j; exact mul_comm _ _
  fin_cases i
  · change A c 0 * S c e = u c e • (S c e *
      OpenBoundaryMPSInteriorRootRealization.G (sector c e) (z c e))
    rw [S, ← mul_assoc, TK hc, mul_assoc, hdg, Matrix.mul_smul, mul_assoc]
  · change A c 1 * S c e = u c e • (S c e *
      (OpenBoundaryMPSInteriorRootRealization.B (sector c e) *
        OpenBoundaryMPSInteriorRootRealization.G (sector c e) (z c e)))
    rw [S, ← mul_assoc, ha1, mul_assoc, hdg, Matrix.mul_smul, mul_assoc,
      ← mul_assoc (OpenBoundaryMPSInteriorRootRealization.B _), commute]
    simp only [mul_assoc]

/-- Extraction is an exact equivalence to the existing native cores. The Schur
cross factor is deliberately separate from all spectral nonvanishing factors. -/
theorem native_extraction {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    (S c e).det ≠ 0 ∧ z c e ≠ 0 ∧
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) = gap c e ∧
    OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = offset c e ∧
    OpenBoundaryMPSInteriorRootRealization.beta (sector c e) =
      gap c e * u c e * t c e / (-c 2) ∧
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.beta (sector c e) ≠ 0 ∧
    nativeLeft c e = ![1, rho c e] ∧
    (∀ i, A c i * S c e = u c e •
      (S c e * OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i)) ∧
    (OpenBoundaryMPSInteriorRootRealization.Regular (sector c e) ↔
      1 + star (lam c e) * mu c e ≠ 0) ∧
    OpenBoundaryMPSInteriorRootRealization.beta (sector c e) -
      OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = gap c e := by
  rcases extraction_algebra hc with ⟨hd, ha, hb, hr, hz, hn⟩
  refine ⟨isUnit_iff_ne_zero.mp (unit_S hc), hz, hd, ha, hb, hn, ?_,
    core_intertwine hc, ?_, ?_⟩
  · rw [nativeLeft, S, ← vecMul_vecMul, left_T]
    ext i; fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two]
  · change (_ ∧ 0 < Complex.normSq (1 + star (lam c e) * mu c e)) ↔ _
    rw [and_iff_right hn, Complex.normSq_pos]
  · rw [← hd]
    simp [OpenBoundaryMPSInteriorRootRealization.beta,
      OpenBoundaryMPSInteriorRootRealization.alpha, OpenBoundaryMPSInteriorRootRealization.delta]

/-- Every full raw amplitude, for arbitrary length and original right boundary,
including the complete core scalar u^N in the new right boundary. -/
theorem raw_amplitude {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e)
    (N : ℕ) (R : Fin 2 → ℂ) :
    mpsState N (A c 0) (A c 1) (L c) R =
      mpsState N (OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) 0)
        (OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) 1)
        (nativeLeft c e) (nativeRight c e N R) := by
  let C := OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e)
  let φ : Bond →* Bond := {
    toFun := fun X => S c e * X * (S c e)⁻¹
    map_one' := by simp [mul_nonsing_inv _ (unit_S hc)]
    map_mul' := by intro X Y; simp only [mul_assoc,
      nonsing_inv_mul_cancel_left _ _ (unit_S hc)] }
  have hA (i : Fin 2) : A c i = u c e • φ (C i) := by
    have hh := congrArg (fun X : Bond => X * (S c e)⁻¹) (core_intertwine hc i)
    change A c i = u c e • (S c e *
      OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i * (S c e)⁻¹)
    simpa only [mul_nonsing_inv_cancel_right _ _ (unit_S hc), smul_mul_assoc] using hh
  have hw (a : Word N) : wordMatrix (A c) a =
      u c e ^ N • (S c e * wordMatrix C a * (S c e)⁻¹) := by
    rw [wordMatrix, show (fun i => A c (a i)) = (fun i => u c e • φ (C (a i)))
      from funext (fun i => hA (a i))]
    rw [show (List.ofFn fun i => u c e • φ (C (a i))) =
      (List.ofFn fun i => φ (C (a i))).map (u c e • ·) from List.map_ofFn.symm,
      ← List.smul_prod, List.length_ofFn]
    congr 1
    exact (show φ (wordMatrix C a) = _ from by
      rw [wordMatrix, map_list_prod, List.map_ofFn]; rfl).symm
  funext a
  rw [state_formula, state_formula, hw]
  simp only [nativeLeft, nativeRight, smul_mulVec, dotProduct_smul, mulVec_smul,
    dotProduct_mulVec, vecMul_vecMul, mul_assoc]
  rfl

/-- The measured native left normalizer is S/u, so its canonical scalar is u. -/
theorem normalizer_inverse {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e) :
    leftNormalizer (sector c e) (z c e) (nativeLeft c e) = (u c e)⁻¹ • S c e ∧
    nativeLeft c e ᵥ* (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹ =
      u c e • L c ∧
    (nativeLeft c e ᵥ* (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹) 1 =
      u c e := by
  have hu := (spectral_frame hc).2.2.2.2.2.2.1
  have hn : leftNormalizer (sector c e) (z c e) (nativeLeft c e) =
      (u c e)⁻¹ • S c e := by
    ext i j
    have hh := congrArg (fun X : Bond => (L c ᵥ* X) j) (core_intertwine hc i)
    simp only [← vecMul_vecMul, OpenBoundaryMPSTwoSiteMinimality.normalized_rows (c, 0, 0),
      single_one_vecMul, vecMul_smul,
      Pi.smul_apply, smul_eq_mul] at hh
    change _ = (u c e)⁻¹ * S c e i j
    change S c e i j = u c e * leftNormalizer (sector c e) (z c e) (nativeLeft c e) i j at hh
    rw [hh]; field_simp [hu]
  have hi : ((u c e)⁻¹ • S c e)⁻¹ = u c e • (S c e)⁻¹ := by
    apply inv_eq_right_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hu,
      one_smul, mul_nonsing_inv _ (unit_S hc)]
  have hv : nativeLeft c e ᵥ* (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹ =
      u c e • L c := by
    rw [hn, hi, nativeLeft, vecMul_smul, vecMul_vecMul,
      mul_nonsing_inv _ (unit_S hc), vecMul_one]
  refine ⟨hn, hv, ?_⟩
  rw [hv]; simp [L, OpenBoundaryMPSTwoSiteMinimality.left]

/-- Canonicalizing the extracted native data at the recovered scalar u returns
both original cores and both boundaries, for every full length N. -/
theorem canonicalization_inverse {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e)
    (N : ℕ) (R : Fin 2 → ℂ) :
    let J := leftNormalizer (sector c e) (z c e) (nativeLeft c e)
    (∀ i, u c e • (J * OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i * J⁻¹) = A c i) ∧
    (u c e)⁻¹ • (nativeLeft c e ᵥ* J⁻¹) = L c ∧
    (u c e * (u c e ^ N)⁻¹) • (J *ᵥ nativeRight c e N R) = R := by
  dsimp only
  have hu := (spectral_frame hc).2.2.2.2.2.2.1
  have hn := (normalizer_inverse hc).1
  have hi : (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹ =
      u c e • (S c e)⁻¹ := by
    rw [hn]; apply inv_eq_right_inv
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hu, one_smul, mul_nonsing_inv _ (unit_S hc)]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hi, hn]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hu, one_smul]
    have hh := congrArg (fun X : Bond => X * (S c e)⁻¹) (core_intertwine hc i)
    simpa only [mul_nonsing_inv_cancel_right _ _ (unit_S hc), smul_mul_assoc] using hh.symm
  · rw [(normalizer_inverse hc).2.1, smul_smul, inv_mul_cancel₀ hu, one_smul]
  · rw [hn, nativeRight, smul_mulVec, mulVec_smul, mulVec_mulVec,
      mul_nonsing_inv _ (unit_S hc), one_mulVec, smul_smul, smul_smul]
    convert one_smul ℂ R using 1
    field_simp [hu]


/-! Exact transport of the same native witness, retaining the full raw scale. -/

def witnessC : Fin 5 → ℂ := ![0, 0, 1/2, 0, 1]
def witnessSector : OpenBoundaryMPSInteriorRootRealization.Sector := ⟨2, 0, 1⟩
def witnessLeft : Fin 2 → ℂ := ![1, 1]
def witnessRight : Fin 2 → ℂ := ![1, Complex.I]
def witnessCanonicalRight (N : ℕ) : Fin 2 → ℂ := (2 : ℂ) ^ N • ![1, 1 + Complex.I]

private lemma witness_frame :
    T witnessC 1 = !![1, 0; 1, 1] ∧
    K witnessC 1 = !![1/2, 1/2; 1/2, -(1/2)] ∧
    S witnessC 1 = !![1, 0; 1, 1] := by
  have hT : T witnessC 1 = !![1, 0; 1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [T, A, OpenBoundaryMPSTwoSiteMinimality.core, witnessC, lam, mu, h,
        mul_apply, Fin.sum_univ_two]
  have hK : K witnessC 1 = !![1/2, 1/2; 1/2, -(1/2)] := by
    rw [K, hT]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.inv_def, Ring.inverse_eq_inv, adjugate_fin_two, det_fin_two,
        A, OpenBoundaryMPSTwoSiteMinimality.core, witnessC, mul_apply, Fin.sum_univ_two]
  refine ⟨hT, hK, ?_⟩
  rw [S, hT]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [rho, u, v, hK] <;>
    norm_num [gap, witnessC, mul_apply, Fin.sum_univ_two]

private lemma witness_S_inv : (S witnessC 1)⁻¹ = !![1, 0; -1, 1] := by
  rw [witness_frame.2.2]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.inv_def, Ring.inverse_eq_inv, adjugate_fin_two, det_fin_two]

/-- Extraction returns the very same native witness. With the canonical raw
boundary (1,eta), it returns precisely 2^(-N) times the original native right. -/
theorem fixed_witness_extraction (N : ℕ) :
    Admissible witnessC 1 ∧ D witnessC = 1 ∧ U witnessC = -1/2 ∧
    U witnessC + D witnessC = 1/2 ∧
    T witnessC 1 = !![1, 0; 1, 1] ∧
    K witnessC 1 = !![1/2, 1/2; 1/2, -(1/2)] ∧
    rho witnessC 1 = 1 ∧ sector witnessC 1 = witnessSector ∧ z witnessC 1 = 1 ∧
    nativeLeft witnessC 1 = witnessLeft ∧
    nativeRight witnessC 1 N (witnessCanonicalRight N) = witnessRight ∧
    nativeRight witnessC 1 N ![1, 1 + Complex.I] = (1/2 : ℂ) ^ N • witnessRight ∧
    1 + star (lam witnessC 1) * mu witnessC 1 = 1 := by
  have hu : u witnessC 1 = 1/2 := by simp [u, witness_frame.2.1]
  have hr : rho witnessC 1 = 1 := by
    simp only [rho, u, v, witness_frame.2.1]
    norm_num [gap, witnessC]
  refine ⟨?_, ?_, ?_, ?_, witness_frame.1, witness_frame.2.1, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Admissible, D, U, h, t0, t1, witnessC]
  · norm_num [D, h, witnessC]
  · norm_num [U, h, t0, t1, witnessC]
  · norm_num [D, U, h, t0, t1, witnessC]
  · simp only [sector, offset, u, v, w, witness_frame.2.1]
    norm_num [lam, mu, h, gap, witnessC, witnessSector]
  · rw [z, hu]
    norm_num [gap, witnessC]
  · rw [nativeLeft, witness_frame.2.2]
    ext j; fin_cases j <;>
      norm_num [L, OpenBoundaryMPSTwoSiteMinimality.left, witnessC, witnessLeft,
        vecMul, dotProduct, Fin.sum_univ_two]
  · rw [nativeRight, hu, witness_S_inv]
    have hp : (1/2 : ℂ)^N * (2 : ℂ)^N = 1 := by rw [← mul_pow]; norm_num
    ext j; fin_cases j <;>
      simp [witnessCanonicalRight, witnessRight, mulVec, dotProduct, Fin.sum_univ_two,
        mul_add, ← mul_assoc, hp]
  · rw [nativeRight, hu, witness_S_inv]
    ext j; fin_cases j <;>
      simp [witnessRight, mulVec, dotProduct, Fin.sum_univ_two]
  · norm_num [lam, mu, h, witnessC]

private lemma sqrt_four_pow (N : ℕ) : Real.sqrt ((4 : ℝ)^N) = (2 : ℝ)^N := by
  rw [show (4 : ℝ)^N = ((2 : ℝ)^N)^2 by
    rw [← pow_mul, Nat.mul_comm N 2, pow_mul]; norm_num, Real.sqrt_sq (by positivity)]

/-- The original quotient's positive boundary restores sigma=4^N and eta=1+I,
without discarding any length-dependent raw scale. -/
theorem fixed_witness_quotient_boundary (N : ℕ) :
    OpenBoundaryMPSQuotient.positiveBoundary (witnessC, (4 : ℝ)^N, 1 + Complex.I) =
      witnessCanonicalRight N ∧
    Complex.normSq (witnessCanonicalRight N 0) = (4 : ℝ)^N ∧
    witnessCanonicalRight N 1 / witnessCanonicalRight N 0 = 1 + Complex.I ∧
    mpsState N (A witnessC 0) (A witnessC 1) (L witnessC)
      (OpenBoundaryMPSQuotient.positiveBoundary (witnessC, (4 : ℝ)^N, 1 + Complex.I)) =
    mpsState N (OpenBoundaryMPSInteriorRootRealization.core witnessSector 1 0)
      (OpenBoundaryMPSInteriorRootRealization.core witnessSector 1 1) witnessLeft witnessRight := by
  have hb : OpenBoundaryMPSQuotient.positiveBoundary (witnessC, (4 : ℝ)^N, 1 + Complex.I) =
      witnessCanonicalRight N := by
    ext j; fin_cases j <;>
      simp [OpenBoundaryMPSQuotient.positiveBoundary, sqrt_four_pow,
        witnessCanonicalRight, Complex.ofReal_pow]
  refine ⟨hb, ?_, ?_, ?_⟩
  · norm_num [witnessCanonicalRight, map_pow, Complex.normSq_ofNat]
  · simp [witnessCanonicalRight,
      mul_div_cancel_left₀ _ (pow_ne_zero N (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [hb]
    rcases fixed_witness_extraction N with ⟨hc, _, _, _, _, _, _, hs, hz, hl, hr, _, _⟩
    simpa only [hs, hz, hl, hr] using raw_amplitude hc N (witnessCanonicalRight N)

#print axioms fixed_witness_extraction
#print axioms fixed_witness_quotient_boundary

#print axioms spectral_frame
#print axioms native_extraction
#print axioms raw_amplitude
#print axioms normalizer_inverse
#print axioms canonicalization_inverse

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
