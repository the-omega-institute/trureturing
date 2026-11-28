/- GID: D5/S3/Geometry/Lorentz/KerrSchildSchwarzschild4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/KerrSchildSchwarzschild4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Schwarzschild and Coulomb Weyl double copy in the orthonormal radial frame. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.KerrSchildDoubleCopy4D
import D5.S3.Geometry.Lorentz.KerrSchildWeylDoubleCopy4D
import Mathlib.Tactic.FieldSimp

/-! At unit radius both the Coulomb field strength and the orthonormal Schwarzschild
curvature can be computed directly from the same Kerr–Schild jet. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Lorentz.KerrSchildSchwarzschild4D

open Matrix Polynomial KerrSchildDoubleCopy4D WeylNullScreen

private abbrev Ind := Fin 4
private abbrev Four := Matrix Ind Ind ℝ
private abbrev Six := Matrix (Fin 6) (Fin 6) ℝ

private abbrev transverse (i : Ind) : Prop := i = 1 ∨ i = 2

/-- The jet of `φ = p / |x|` and `k = (1, x / |x|)` at `x = (0,0,1)`. -/
def radialJet (p : ℝ) : Jet ℝ where
  phi := p
  k := ![1, 0, 0, 1]
  dphi := ![0, 0, 0, -p]
  dk a b := if a = b ∧ transverse a then 1 else 0
  ddphi := diagonal ![0, -p, -p, 2 * p]
  ddk a b c := if (a = b ∧ transverse a ∧ c = 3) ∨
    (a = c ∧ transverse a ∧ b = 3) ∨ (b = c ∧ transverse b ∧ a = 3) then -1 else 0
  ddphi_symm := fun a b => congrFun (congrFun (diagonal_transpose _) b) a
  ddk_symm a b c := by fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [transverse]

private def left : Fin 6 → Ind := ![0, 0, 0, 2, 3, 1]
private def right : Fin 6 → Ind := ![1, 2, 3, 3, 1, 2]

/-- An orthonormal frame obtained by a null rank-one change of the Cartesian frame. -/
def radialFrame (p : ℝ) : Four :=
  1 - (p / 2) • vecMulVec (raise (radialJet p).k) (radialJet p).k

private def outerFrame (T : Four) : Six :=
  fun i j => T (left i) (left j) * T (right i) (right j) -
    T (left i) (right j) * T (right i) (left j)

private def lower (j : FirstJet ℝ) (a b c : Ind) : ℝ :=
  (dPerturbation j b a c + dPerturbation j c a b - dPerturbation j a b c) / 2

private def curvature (j : Jet ℝ) (a b c d : Ind) : ℝ :=
  (ddPerturbation j c b a d - ddPerturbation j c a d b -
    ddPerturbation j d b a c + ddPerturbation j d a c b) / 2 +
    ∑ i, ∑ l, (ksMetric j.phi j.k)⁻¹ i l *
      (lower j.toFirstJet i d a * lower j.toFirstJet l c b -
       lower j.toFirstJet i c a * lower j.toFirstJet l d b)

/-- Oriented curvature pair matrix in the frame `radialFrame`. -/
def radialCurvature (p : ℝ) : Six :=
  let R : Six := fun i j => curvature (radialJet p) (left i) (right i) (left j) (right j)
  let T := outerFrame (radialFrame p)
  Tᵀ * R * T

private theorem inverse_radial (p : ℝ) :
    (ksMetric p (radialJet p).k)⁻¹ = ksInv p (radialJet p).k := by
  have hn : raise (radialJet p).k ⬝ᵥ (radialJet p).k = 0 := by
    norm_num [radialJet, raise, KerrSchildDoubleCopy4D.sign, dotProduct, Fin.sum_univ_succ]
  have hd : IsUnit (ksMetric p (radialJet p).k).det := by
    rw [ks_metric_det p _ hn]
    exact isUnit_one.neg
  calc
    _ = (ksMetric p (radialJet p).k)⁻¹ *
        (ksMetric p (radialJet p).k * ksInv p (radialJet p).k) := by
          rw [(ks_metric_mul_inv p _ hn).1, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]

private theorem frame_entries (p : ℝ) :
    radialFrame p = !![1 + p/2, 0, 0, p/2; 0, 1, 0, 0;
      0, 0, 1, 0; -(p/2), 0, 0, 1-p/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialFrame, radialJet, raise, KerrSchildDoubleCopy4D.sign, Matrix.one_apply, vecMulVec_apply] <;> ring

private theorem frame_isometry (p : ℝ) :
    (radialFrame p)ᵀ * ksMetric p (radialJet p).k * radialFrame p = eta ℝ := by
  rw [frame_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ksMetric, KerrSchildDoubleCopy4D.eta, KerrSchildDoubleCopy4D.sign, diagonal_apply, vecMulVec_apply, radialJet, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 1800000 in
private theorem coordinate_curvature (p : ℝ) :
    (fun i j => curvature (radialJet p) (left i) (right i) (left j) (right j) : Six) =
      !![p/2-p^2/2, 0, 0, 0, -p^2/2, 0;
         0, p/2-p^2/2, 0, p^2/2, 0, 0;
         0, 0, -p, 0, 0, 0;
         0, p^2/2, 0, -p/2-p^2/2, 0, 0;
         -p^2/2, 0, 0, 0, -p/2-p^2/2, 0;
         0, 0, 0, 0, 0, p] := by
  have hi : (ksMetric (radialJet p).phi (radialJet p).k)⁻¹ =
      ksInv (radialJet p).phi (radialJet p).k := inverse_radial p
  ext i j
  simp only [curvature, hi]
  fin_cases i <;> fin_cases j <;>
    norm_num [left, right, radialJet, transverse, ksInv,
      diagonal_apply, KerrSchildDoubleCopy4D.eta, raise, KerrSchildDoubleCopy4D.sign, vecMulVec_apply, lower, dPerturbation, ddPerturbation,
      Fin.sum_univ_succ] <;> ring

private theorem frame_curvature (p : ℝ) :
    radialCurvature p = diagonal ![p/2, p/2, -p, -p/2, -p/2, p] := by
  rw [radialCurvature, coordinate_curvature, frame_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [outerFrame, left, right, Matrix.mul_apply, Fin.sum_univ_succ,
      diagonal_apply] <;> ring

private def pairIndex : PairIndex → Fin 6
  | .inl i => Fin.castLE (by decide) i
  | .inr i => Fin.natAdd 3 i

private def radialElectric (p : ℝ) : STF3 ℝ :=
  ⟨diagonal ![p/2, p/2, -p], fun i j => congrFun (congrFun (diagonal_transpose _) j) i, by
    change (∑ i : Fin 3, (1 : ℝ) * diagonal ![p/2, p/2, -p] i i) = 0
    simp [Fin.sum_univ_three]⟩

/-- The Ricci-free curvature with the electric diagonal of the radial frame. -/
def radialWeyl (p : ℝ) : Weyl4 := weyl_electric_magnetic_equiv.symm (radialElectric p, 0)

private theorem radial_weyl_matrix (p : ℝ) :
    (radialWeyl p).val.val = fun i j => radialCurvature p (pairIndex i) (pairIndex j) := by
  rw [frame_curvature]
  have h (a b : Fin 3) : (radialWeyl p).val.val (.inr a) (.inr b) =
      -(diagonal ![p/2, p/2, -p] a b) := rfl
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals fin_cases i <;> fin_cases j <;> first | rfl | (rw [h]; norm_num [pairIndex, diagonal_apply] <;> ring)

private def coulombScreen (p : ℝ) (r : FutureNullRay) : ℂ :=
  ∑ i, ∑ j, Complex.ofReal (fieldStrength (radialJet p).toFirstJet i j) *
    screenVector r i * (nullGenerator r j : ℂ)

private theorem coulomb_screen_polynomial (p : ℝ) (r : FutureNullRay) :
    coulombScreen p r = Omega.ProjectivePolynomial.eval 2 r
      (maxwellQuadratic (2 * (p : ℂ)) (some 0) none) := by
  cases r <;> simp [coulombScreen, fieldStrength, radialJet, transverse, screenVector,
    nullGenerator, maxwellQuadratic, Omega.ProjectivePolynomial.eval,
    Omega.ProjectivePolynomial.nodalQuadratic, Omega.ProjectivePolynomial.rayFactor,
    Polynomial.smul_eq_C_mul, Fin.sum_univ_succ] <;> ring

private theorem radial_weyl_eq (p : ℝ) :
    radialWeyl p = KerrSchildWeylDoubleCopy4D.schwarzschildWeyl (-p/2) 1 := by
  have he : radialElectric p = KerrSchildWeylDoubleCopy4D.schwarzschildElectric (-p/2) 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [radialElectric, KerrSchildWeylDoubleCopy4D.schwarzschildElectric, diagonal_apply] <;> ring
  simp only [radialWeyl, KerrSchildWeylDoubleCopy4D.schwarzschildWeyl, he]

private theorem radial_null (p : ℝ) : Null (radialJet p) := by
  constructor
  · norm_num [raise, KerrSchildDoubleCopy4D.sign, dotProduct, radialJet, Fin.sum_univ_four]
  · intro a
    fin_cases a <;> norm_num [raise, KerrSchildDoubleCopy4D.sign, dotProduct, radialJet,
      transverse, Fin.sum_univ_four]
  · intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [raise, KerrSchildDoubleCopy4D.sign, dotProduct, radialJet, transverse, Fin.sum_univ_four]

private theorem radial_geodesic (p : ℝ) : Geodesic (radialJet p) := by
  constructor
  · intro b
    fin_cases b <;> norm_num [raise, KerrSchildDoubleCopy4D.sign, radialJet, transverse, Fin.sum_univ_four]
  · intro a b
    fin_cases a <;> fin_cases b <;>
      norm_num [raise, KerrSchildDoubleCopy4D.sign, radialJet, transverse, Fin.sum_univ_four]

private theorem radial_stationary (p : ℝ) : StationaryUnit (radialJet p) := by
  constructor <;> try rfl
  all_goals
    first
    | intro a b; fin_cases a <;> fin_cases b <;> norm_num [radialJet, transverse]
    | intro a; fin_cases a <;> norm_num [radialJet, transverse, diagonal_apply]

private theorem radial_maxwell_vacuum (p : ℝ) (i : Ind) :
    maxwellDivergence (radialJet p) i = 0 := by
  have hn := radial_null p
  have hg := radial_geodesic p
  have hs := radial_stationary p
  have ht : mixedRicci (radialJet p) 0 0 = 0 :=
    (stationary_ks_ricci_poisson_zeroth_copy (radialJet p) hn hg hs).2.mpr (by
      norm_num [radialJet]
      ring)
  fin_cases i
  · exact (stationary_ks_ricci_maxwell_double_copy (radialJet p) hn hg hs 0).2.mp ht
  all_goals norm_num [maxwellDivergence, ddPotential, radialJet, transverse,
    KerrSchildDoubleCopy4D.sign, diagonal_apply, Fin.sum_univ_four] <;> ring

/-- For the radial Kerr–Schild jet the Maxwell screen is the Coulomb quadratic,
and the Weyl quartic is its square with scalar normalization `-3 / p`. -/
theorem schwarzschild_coulomb_weyl_double_copy (p : ℝ) (hp : p ≠ 0) :
    (radialFrame p)ᵀ * ksMetric p (radialJet p).k * radialFrame p = eta ℝ ∧
    (∀ i j, (radialWeyl p).val.val i j = radialCurvature p (pairIndex i) (pairIndex j)) ∧
    (∀ r, coulombScreen p r = Omega.ProjectivePolynomial.eval 2 r
      (maxwellQuadratic (2 * (p : ℂ)) (some 0) none)) ∧
    (∀ i, maxwellDivergence (radialJet p) i = 0) ∧
    (weylQuarticEquiv (radialWeyl p) : ℂ[X]) =
      (-3 / (p : ℂ)) • (maxwellSquare (2 * (p : ℂ)) (some 0) none : ℂ[X]) := by
  refine ⟨frame_isometry p, fun i j => congrFun (congrFun (radial_weyl_matrix p) i) j,
    coulomb_screen_polynomial p, radial_maxwell_vacuum p, ?_⟩
  rw [radial_weyl_eq, KerrSchildWeylDoubleCopy4D.schwarzschild_weylQuartic,
    (coulomb_schwarzschild_quartic (2 * (p : ℂ))).2.1, ← C_mul_X_pow_eq_monomial]
  simp only [smul_eq_C_mul, ← mul_assoc, ← map_mul, one_pow, div_one, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 2
  have hp' : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  field_simp
  ring

end D5.S3.Geometry.Lorentz.KerrSchildSchwarzschild4D
