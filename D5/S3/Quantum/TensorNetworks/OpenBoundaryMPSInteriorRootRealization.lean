/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Distinct residual roots realize actual finite interior ambiguity. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
import D5.S3.Topology.AnnularSecondZero
import Mathlib.Topology.Instances.Matrix

/-! Conditional root-to-actual reconstruction for the entire raw interior
observation. Algebraic inverse transfer is not a positive physical inverse.
The endpoint and real transversality assumptions remain explicit. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization

open scoped BigOperators Matrix ComplexOrder Kronecker
open Matrix
open PeriodicMPSParentIntersection
open OpenBoundaryMPSMarginalBirationality (mpsState openBoundaryMPS)
open OpenBoundaryMPSDensityRecovery
open OpenBoundaryMPSInteriorCommonCore

structure Sector where
  lambda : ℂ
  mu : ℂ
  a : ℂ

def delta (s : Sector) : ℂ := s.mu - s.lambda
def alpha (s : Sector) : ℂ := s.lambda - s.a
def beta (s : Sector) : ℂ := s.mu - s.a

def Regular (s : Sector) : Prop :=
  delta s * alpha s * beta s ≠ 0 ∧
    0 < Complex.normSq (1 + star s.lambda * s.mu)

def B (s : Sector) : Bond := diagonal ![s.lambda, s.mu]
def G (s : Sector) (z : ℂ) : Bond := !![1, z; alpha s, beta s * z]
def C (s : Sector) : Bond := !![s.a, 1; -alpha s * beta s, s.lambda + s.mu - s.a]
def core (s : Sector) (z : ℂ) : Fin 2 → Bond := ![G s z, B s * G s z]
def K (s : Sector) (w : Word 2) : Bond :=
  (![1, B s] : Fin 2 → Bond) (w 0) * (![1, C s] : Fin 2 → Bond) (w 1)

private lemma regular_factors {s : Sector} (hs : Regular s) :
    delta s ≠ 0 ∧ alpha s ≠ 0 ∧ beta s ≠ 0 := by
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).2, (mul_ne_zero_iff.mp hs.1).2⟩

private lemma det_G (s : Sector) (z : ℂ) : (G s z).det = delta s * z := by
  simp [G, delta, alpha, beta, det_fin_two]
  ring

private lemma unit_G {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0) :
    IsUnit (G s z).det := by
  rw [det_G]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (regular_factors hs).1 hz)

private lemma intertwining (s : Sector) (z : ℂ) : C s * G s z = G s z * B s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C, G, B, alpha, beta, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma pair_product (s : Sector) (z : ℂ) (w : Word 2) :
    wordMatrix (core s z) w = K s w * G s z ^ 2 := by
  have h : G s z * (B s * G s z) = C s * (G s z * G s z) := by
    rw [← Matrix.mul_assoc, ← intertwining, Matrix.mul_assoc]
  have hw : w = ![w 0, w 1] := (FinVec.etaExpand_eq w).symm
  rw [hw]
  simp only [wordMatrix, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, Matrix.mul_one]
  generalize w 0 = i
  generalize w 1 = j
  fin_cases i <;> fin_cases j <;>
    simp [K, core, pow_two, Matrix.mul_assoc, h]

/-- The diagonal Schur inverse of X ↦ X+B X B†. -/
def diagonalInverse (s : Sector) (X : Bond) : Bond :=
  fun i j => X i j / (1 + (![s.lambda, s.mu] : Fin 2 → ℂ) i *
    star ((![s.lambda, s.mu] : Fin 2 → ℂ) j))

/-- The diagonal Schur inverse of X ↦ X+B† X B. -/
def diagonalStarInverse (s : Sector) (X : Bond) : Bond :=
  fun i j => X i j / (1 + star ((![s.lambda, s.mu] : Fin 2 → ℂ) i) *
    (![s.lambda, s.mu] : Fin 2 → ℂ) j)

def inverseTransfer (s : Sector) (z : ℂ) (X : Bond) : Bond :=
  (G s z)⁻¹ * diagonalInverse s X * ((G s z)⁻¹)ᴴ

def inverseDualTransfer (s : Sector) (z : ℂ) (X : Bond) : Bond :=
  diagonalStarInverse s (((G s z)⁻¹)ᴴ * X * (G s z)⁻¹)

private lemma schur_nonzero {s : Sector} (hs : Regular s) (i j : Fin 2) :
    1 + (![s.lambda, s.mu] : Fin 2 → ℂ) i *
      star ((![s.lambda, s.mu] : Fin 2 → ℂ) j) ≠ 0 := by
  have hd (x : ℂ) : 1 + x * star x ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re,
      RCLike.star_def, Complex.mul_conj, Complex.ofReal_re] at he
    have := Complex.normSq_nonneg x
    linarith
  have hc : 1 + star s.lambda * s.mu ≠ 0 :=
    Complex.normSq_pos.mp hs.2
  fin_cases i <;> fin_cases j
  · exact hd _
  · have he : 1 + s.lambda * star s.mu = star (1 + star s.lambda * s.mu) := by
      simp [star_add, star_mul, mul_comm]
    change 1 + s.lambda * star s.mu ≠ 0
    rw [he]
    exact star_ne_zero.mpr hc
  · simpa [mul_comm] using hc
  · exact hd _

private lemma schur_star_nonzero {s : Sector} (hs : Regular s) (i j : Fin 2) :
    1 + star ((![s.lambda, s.mu] : Fin 2 → ℂ) i) *
      (![s.lambda, s.mu] : Fin 2 → ℂ) j ≠ 0 := by
  simpa only [mul_comm] using schur_nonzero hs j i

private lemma transfer_formula (s : Sector) (z : ℂ) (X : Bond) :
    transfer (core s z) X =
      G s z * X * (G s z)ᴴ + B s * (G s z * X * (G s z)ᴴ) * (B s)ᴴ := by
  simp [transfer, core, Fin.sum_univ_two, conjTranspose_mul, Matrix.mul_assoc]

private lemma dual_formula (s : Sector) (z : ℂ) (X : Bond) :
    dualTransfer (core s z) X =
      (G s z)ᴴ * (X + (B s)ᴴ * X * B s) * G s z := by
  simp [dualTransfer, core, Fin.sum_univ_two, conjTranspose_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]

private lemma diagonal_cancel {s : Sector} (hs : Regular s) (X : Bond) :
    diagonalInverse s X + B s * diagonalInverse s X * (B s)ᴴ = X := by
  ext i j
  simp only [B, diagonal_conjTranspose, Pi.star_apply, mul_diagonal,
    diagonal_mul, Matrix.add_apply, diagonalInverse]
  have h := schur_nonzero hs i j
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) i = a at *
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) j = b at *
  field_simp
  <;> grind

private lemma diagonal_cancel' {s : Sector} (hs : Regular s) (X : Bond) :
    diagonalInverse s (X + B s * X * (B s)ᴴ) = X := by
  ext i j
  simp only [B, diagonal_conjTranspose, Pi.star_apply, mul_diagonal,
    diagonal_mul, Matrix.add_apply, diagonalInverse]
  have h := schur_nonzero hs i j
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) i = a at *
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) j = b at *
  field_simp
  <;> grind

private lemma diagonal_star_cancel {s : Sector} (hs : Regular s) (X : Bond) :
    diagonalStarInverse s X + (B s)ᴴ * diagonalStarInverse s X * B s = X := by
  ext i j
  simp only [B, diagonal_conjTranspose, Pi.star_apply, mul_diagonal,
    diagonal_mul, Matrix.add_apply, diagonalStarInverse]
  have h := schur_star_nonzero hs i j
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) i = a at *
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) j = b at *
  field_simp
  <;> grind

private lemma diagonal_star_cancel' {s : Sector} (hs : Regular s) (X : Bond) :
    diagonalStarInverse s (X + (B s)ᴴ * X * B s) = X := by
  ext i j
  simp only [B, diagonal_conjTranspose, Pi.star_apply, mul_diagonal,
    diagonal_mul, Matrix.add_apply, diagonalStarInverse]
  have h := schur_star_nonzero hs i j
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) i = a at *
  generalize (![s.lambda, s.mu] : Fin 2 → ℂ) j = b at *
  field_simp
  <;> grind

private lemma inverse_transfer_right {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (X : Bond) :
    transfer (core s z) (inverseTransfer s z X) = X := by
  rw [transfer_formula]
  have h : G s z * inverseTransfer s z X * (G s z)ᴴ = diagonalInverse s X := by
    simp only [inverseTransfer, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ (unit_G hs hz),
      ← conjTranspose_mul, nonsing_inv_mul _ (unit_G hs hz),
      mul_nonsing_inv _ (unit_G hs hz), conjTranspose_one,
      Matrix.mul_one]
  rw [h]
  exact diagonal_cancel hs X

lemma inverse_transfer_left {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (X : Bond) :
    inverseTransfer s z (transfer (core s z) X) = X := by
  rw [transfer_formula, inverseTransfer, diagonal_cancel' hs]
  simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ (unit_G hs hz),
    ← conjTranspose_mul, mul_nonsing_inv _ (unit_G hs hz),
      nonsing_inv_mul _ (unit_G hs hz), conjTranspose_one,
    Matrix.mul_one]

private lemma inverse_dual_right {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (X : Bond) :
    dualTransfer (core s z) (inverseDualTransfer s z X) = X := by
  rw [dual_formula, inverseDualTransfer, diagonal_star_cancel hs]
  have hc : (G s z)ᴴ * ((G s z)⁻¹)ᴴ = 1 := by
    rw [← conjTranspose_mul, nonsing_inv_mul _ (unit_G hs hz), conjTranspose_one]
  simp only [← Matrix.mul_assoc, hc, Matrix.one_mul,
    nonsing_inv_mul_cancel_right _ _ (unit_G hs hz)]

lemma inverse_dual_left {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (X : Bond) :
    inverseDualTransfer s z (dualTransfer (core s z) X) = X := by
  rw [inverseDualTransfer, dual_formula]
  have hc : ((G s z)⁻¹)ᴴ * (G s z)ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ (unit_G hs hz), conjTranspose_one]
  have h : ((G s z)⁻¹)ᴴ * ((G s z)ᴴ * (X + (B s)ᴴ * X * B s) * G s z) *
      (G s z)⁻¹ = X + (B s)ᴴ * X * B s := by
    simp only [← Matrix.mul_assoc, hc, Matrix.one_mul,
      mul_nonsing_inv_cancel_right _ _ (unit_G hs hz)]
  rw [h, diagonal_star_cancel' hs]


/-- Actual left environment, fixed throughout all trial operations. -/
def leftTarget (s : Sector) (z : ℂ) (l : Fin 2 → ℂ) (p : ℕ) : Bond :=
  (dualTransfer (core s z))^[p] (vecMulVec (star l) l)

/-- Actual right environment with the central two-site G-square included. -/
def rightTarget (s : Sector) (z : ℂ) (r : Fin 2 → ℂ) (q : ℕ) : Bond :=
  G s z ^ 2 * (transfer (core s z))^[q] (vecMulVec r (star r)) * (G s z ^ 2)ᴴ

def trialLeft (s : Sector) (p : ℕ) (P : Bond) (z : ℂ) : Bond :=
  (inverseDualTransfer s z)^[p] P

def trialRight (s : Sector) (q : ℕ) (H : Bond) (z : ℂ) : Bond :=
  (inverseTransfer s z)^[q] ((G s z ^ 2)⁻¹ * H * ((G s z ^ 2)⁻¹)ᴴ)

/-- Explicit real two-component residual with fixed target environments. -/
def residual (s : Sector) (p q : ℕ) (P H : Bond) (z : ℂ) : ℂ :=
  ((trialLeft s p P z).det.re : ℂ) + Complex.I * ((trialRight s q H z).det.re : ℂ)

private lemma raw_trace_dictionary (s : Sector) (z : ℂ) (l r : Fin 2 → ℂ)
    (p q : ℕ) (u v : Word 2) :
    rawInterior p 2 q (mpsState ((p + 2) + q) (core s z 0) (core s z 1) l r) u v =
      trace (leftTarget s z l p * K s u * rightTarget s z r q * (K s v)ᴴ) := by
  rw [interior_density_dictionary]
  have hu := pair_product s z u
  have hv := pair_product s z v
  simp only [mul_apply, conjTranspose_apply, feature, kronecker_apply,
    transpose_apply, Fintype.sum_prod_type]
  simp only [hu, hv, mul_apply, Fin.sum_univ_two, star_add, star_mul,
    leftTarget, rightTarget, trace, diag, conjTranspose_apply]
  ring

private lemma transfer_conj (A : Fin 2 → Bond) (X : Bond) :
    transfer A Xᴴ = (transfer A X)ᴴ := by
  simp [transfer, conjTranspose_sum, conjTranspose_mul, Matrix.mul_assoc]

private lemma dual_conj (A : Fin 2 → Bond) (X : Bond) :
    dualTransfer A Xᴴ = (dualTransfer A X)ᴴ := by
  simp [dualTransfer, conjTranspose_sum, conjTranspose_mul, Matrix.mul_assoc]

private lemma inverse_transfer_hermitian {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) {X : Bond} (hX : X.IsHermitian) :
    (inverseTransfer s z X).IsHermitian := by
  apply (Function.LeftInverse.injective (inverse_transfer_left hs hz))
  rw [transfer_conj, inverse_transfer_right hs hz, hX.eq]

private lemma inverse_dual_hermitian {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) {X : Bond} (hX : X.IsHermitian) :
    (inverseDualTransfer s z X).IsHermitian := by
  apply (Function.LeftInverse.injective (inverse_dual_left hs hz))
  rw [dual_conj, inverse_dual_right hs hz, hX.eq]

private lemma iterate_hermitian (F : Bond → Bond)
    (hF : ∀ X, X.IsHermitian → (F X).IsHermitian) (n : ℕ)
    {X : Bond} (hX : X.IsHermitian) : (F^[n] X).IsHermitian := by
  induction n with
  | zero => exact hX
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

private lemma left_forward {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0)
    (p : ℕ) (P : Bond) :
    (dualTransfer (core s z))^[p] (trialLeft s p P z) = P :=
  Function.LeftInverse.iterate (inverse_dual_right hs hz) p P

private lemma right_forward {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0)
    (q : ℕ) (H : Bond) :
    G s z ^ 2 * (transfer (core s z))^[q] (trialRight s q H z) * (G s z ^ 2)ᴴ = H := by
  rw [trialRight, Function.LeftInverse.iterate (inverse_transfer_right hs hz) q]
  have hu : IsUnit (G s z ^ 2).det := by rw [det_pow]; exact (unit_G hs hz).pow 2
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu,
    ← conjTranspose_mul, nonsing_inv_mul _ hu, mul_nonsing_inv _ hu, conjTranspose_one, Matrix.mul_one]

lemma left_at_target {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0)
    (p : ℕ) (l : Fin 2 → ℂ) :
    trialLeft s p (leftTarget s z l p) z = vecMulVec (star l) l :=
  Function.LeftInverse.iterate (inverse_dual_left hs hz) p _

lemma right_at_target {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0)
    (q : ℕ) (r : Fin 2 → ℂ) :
    trialRight s q (rightTarget s z r q) z = vecMulVec r (star r) := by
  have hu : IsUnit (G s z ^ 2).det := by rw [det_pow]; exact (unit_G hs hz).pow 2
  unfold trialRight rightTarget
  simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu,
    ← conjTranspose_mul, mul_nonsing_inv _ hu, nonsing_inv_mul _ hu, conjTranspose_one, Matrix.mul_one]
  exact Function.LeftInverse.iterate (inverse_transfer_left hs hz) q _

private lemma det_outer (x y : Fin 2 → ℂ) : (vecMulVec x y).det = 0 := by
  simp [det_fin_two, vecMulVec_apply]
  ring

lemma residual_at_target {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0)
    (p q : ℕ) (l r : Fin 2 → ℂ) :
    residual s p q (leftTarget s z l p) (rightTarget s z r q) z = 0 := by
  rw [residual, left_at_target hs hz, right_at_target hs hz,
    det_outer, det_outer]
  simp


private lemma transfer_psd (A : Fin 2 → Bond) {X : Bond} (hX : X.PosSemidef) :
    (transfer A X).PosSemidef := by
  simpa only [transfer, Fin.sum_univ_two] using
    (hX.mul_mul_conjTranspose_same (A 0)).add (hX.mul_mul_conjTranspose_same (A 1))

private lemma dual_psd (A : Fin 2 → Bond) {X : Bond} (hX : X.PosSemidef) :
    (dualTransfer A X).PosSemidef := by
  simpa only [dualTransfer, Fin.sum_univ_two] using
    (hX.conjTranspose_mul_mul_same (A 0)).add (hX.conjTranspose_mul_mul_same (A 1))

private lemma iterate_psd (F : Bond → Bond)
    (hF : ∀ X, X.PosSemidef → (F X).PosSemidef) (n : ℕ)
    {X : Bond} (hX : X.PosSemidef) : (F^[n] X).PosSemidef := by
  induction n with
  | zero => exact hX
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

lemma iterate_smul (F : Bond → Bond)
    (hF : ∀ (t : ℂ) X, F (t • X) = t • F X) (n : ℕ) (t : ℂ) (X : Bond) :
    F^[n] (t • X) = t • F^[n] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, hF]

lemma transfer_smul (A : Fin 2 → Bond) (t : ℂ) (X : Bond) :
    transfer A (t • X) = t • transfer A X := by simp [transfer]

private lemma dual_smul (A : Fin 2 → Bond) (t : ℂ) (X : Bond) :
    dualTransfer A (t • X) = t • dualTransfer A X := by simp [dualTransfer]

/-- The sign is forced by a positive definite forward image, not by positivity
of the algebraic inverse. Rank factorization is the existing supplier. -/
private lemma actual_rank_one_factor (F : Bond → Bond)
    (hscale : ∀ (t : ℂ) X, F (t • X) = t • F X)
    (hpos : ∀ X, X.PosSemidef → (F X).PosSemidef)
    {X : Bond} (hX : X.IsHermitian) (hdet : X.det = 0) (hFX : (F X).PosDef) :
    ∃ v : Fin 2 → ℂ, X = vecMulVec v (star v) := by
  have hzero : F 0 = 0 := by simpa using hscale 0 0
  have hne : X ≠ 0 := by
    intro he
    have hd := hFX.diag_pos (i := 0)
    rw [he, hzero] at hd
    simpa using hd
  have hrank : X.rank ≤ 1 := by
    have hupper : X.rank ≤ 2 := by simpa using X.rank_le_card_width
    by_contra hn
    have hf : X.rank = Fintype.card (Fin 2) := by simpa using (show X.rank = 2 by omega)
    have hu := Matrix.mulVec_surjective_iff_isUnit.mp
      (Matrix.mulVec_surjective_iff_rank_eq_card.mpr hf)
    exact ((Matrix.isUnit_iff_isUnit_det X).mp hu).ne_zero hdet
  obtain ⟨x, y, hxy⟩ := D5.S3.Quantum.Schatten.exists_rank_one_factors X hrank
  have hx : x ≠ 0 := by intro hx; apply hne; rw [hxy, hx]; ext i j; simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
  let t : ℂ := star (y i) / x i
  have hy (j : Fin 2) : y j = t * star (x j) := by
    have he := congrArg star (hX.apply j i)
    rw [hxy] at he
    simp only [vecMulVec_apply, star_mul, star_star] at he
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hi).mpr
    simp only [RCLike.star_def] at he ⊢
    simpa only [mul_comm] using he
  have hf : X = t • vecMulVec x (star x) := by
    rw [hxy]
    ext j k
    simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply, hy]
    ring
  have ht : star t = t := by
    have he := hX.apply i i
    rw [hf] at he
    simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply,
      star_mul, star_star] at he
    apply mul_right_cancel₀ (mul_ne_zero hi (star_ne_zero.mpr hi))
    linear_combination he
  have hreal : (t.re : ℂ) = t := Complex.conj_eq_iff_re.mp ht
  have hnonneg := (hpos _ (posSemidef_vecMulVec_self_star x)).diag_nonneg (i := 0)
  have hpositive := hFX.diag_pos (i := 0)
  rw [hf, hscale, ← hreal] at hpositive
  have ha : 0 ≤ (F (vecMulVec x (star x)) 0 0).re := (Complex.nonneg_iff.mp hnonneg).1
  have hp : 0 < t.re * (F (vecMulVec x (star x)) 0 0).re := by
    simpa only [Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using (Complex.pos_iff.mp hpositive).1
  have htpos : 0 < t.re := by nlinarith
  refine ⟨(Real.sqrt t.re : ℂ) • x, ?_⟩
  rw [hf]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply,
    Pi.smul_apply, star_mul, RCLike.star_def, Complex.conj_ofReal]
  have hsq : (Real.sqrt t.re : ℂ) ^ 2 = t := by
    rw [← hreal]
    exact_mod_cast Real.sq_sqrt (le_of_lt htpos)
  linear_combination -(x j * (starRingEnd ℂ) (x k)) * hsq

private lemma K_decomposition {s : Sector} (hs : Regular s) (M : Bond) :
    ∃ t₀ t₁ t₂ t₃ : ℂ, M = t₀ • K s ![0, 0] + t₁ • K s ![0, 1] +
      t₂ • K s ![1, 0] + t₃ • K s ![1, 1] := by
  let c := -alpha s * beta s
  let d := s.lambda + s.mu - s.a
  let t₃ := (M 1 0 / c - M 0 1) / delta s
  let t₁ := M 0 1 - s.lambda * t₃
  let u := M 0 0 - s.a * M 0 1
  let v := M 1 1 - d * (M 1 0 / c)
  let t₂ := (v - u) / delta s
  let t₀ := u - s.lambda * t₂
  refine ⟨t₀, t₁, t₂, t₃, ?_⟩
  have hc : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (regular_factors hs).2.1)
    (regular_factors hs).2.2
  have hd := (regular_factors hs).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, B, C, Matrix.mul_apply, Fin.sum_univ_two, t₀, t₁, t₂, t₃, u, v, d,
      Matrix.smul_apply, smul_eq_mul] <;>
    dsimp [c] at * <;> field_simp <;> grind [delta, alpha, beta]

private lemma pencil_rigidity {ι κ : Type} [Fintype ι] [Fintype κ]
    (L L' : Matrix ι (Fin 2) ℂ) (S S' : Matrix (Fin 2) κ ℂ)
    (hL : (Lᴴ * L).PosDef) (hS : (S * Sᴴ).PosDef)
    (η : ℂ) (hη : η ≠ 0)
    (he : ∀ M : Bond, L' * M * S' = η • (L * M * S)) :
    ∃ h : ℂ, h ≠ 0 ∧ L' = h • L := by
  let LL := (Lᴴ * L)⁻¹ * Lᴴ
  let RR := Sᴴ * (S * Sᴴ)⁻¹
  have hdetL : IsUnit (Lᴴ * L).det := (Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit
  have hdetS : IsUnit (S * Sᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hLL : LL * L = 1 := by dsimp [LL]; rw [Matrix.mul_assoc, nonsing_inv_mul _ hdetL]
  have hRR : S * RR = 1 := by dsimp [RR]; rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdetS]
  let U := LL * L'
  let V := S' * RR
  have hUV (M : Bond) : U * M * V = η • M := by
    calc
      U * M * V = LL * (L' * M * S') * RR := by simp only [U, V, Matrix.mul_assoc]
      _ = LL * (η • (L * M * S)) * RR := by rw [he]
      _ = η • ((LL * L) * M * (S * RR)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = η • M := by rw [hLL, hRR, Matrix.one_mul, Matrix.mul_one]
  have huv : U * V = η • (1 : Bond) := by simpa using hUV 1
  have hd : U.det * V.det ≠ 0 := by
    rw [← det_mul, huv, det_smul]
    simpa using pow_ne_zero 2 hη
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hd).1
  have hv : IsUnit V.det := isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hd).2
  have hvu : V * U = η • (1 : Bond) := by
    have hh := congrArg (fun Z => U⁻¹ * Z * U) huv
    simpa only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hu,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, nonsing_inv_mul _ hu] using hh
  have hcomm (M : Bond) : U * M = M * U := by
    have hh := congrArg (fun Z => Z * U) (hUV M)
    have hh' : η • (U * M) = η • (M * U) := by
      simpa only [Matrix.mul_assoc, hvu, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul] using hh
    exact (smul_right_injective _ hη) hh'
  obtain ⟨h, hh⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr
    (fun i j => (show Commute (single i j 1) U from (hcomm _).symm))
  have hh' : U = h • (1 : Bond) := by simpa only [Matrix.scalar_apply, smul_one_eq_diagonal] using hh.symm
  have hn : h ≠ 0 := by
    intro hz
    rw [hh', hz, zero_smul, zero_mul] at huv
    have he := congrFun (congrFun huv 0) 0
    simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
      mul_one] at he
    exact hη he.symm
  have hLV : L' * V = η • L := by
    have hh := congrArg (fun Z => Z * RR) (he 1)
    simpa only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc, hRR,
      Matrix.mul_one] using hh
  have heq : L' * V = (L * U) * V := by
    rw [hLV, Matrix.mul_assoc, huv, Matrix.mul_smul, Matrix.mul_one]
  have heq' := congrArg (fun Z => Z * V⁻¹) heq
  have heq'' : L' = L * U := by
    simpa only [mul_nonsing_inv_cancel_right _ _ hv] using heq'
  exact ⟨h, hn, by rw [heq'', hh', Matrix.mul_smul, Matrix.mul_one]⟩


private lemma continuous_G (s : Sector) : Continuous (G s) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [G] <;> fun_prop

private lemma continuousAt_inverse_G {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) : ContinuousAt (fun w => (G s w)⁻¹) z := by
  apply ContinuousAt.comp _ (continuous_G s).continuousAt
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (unit_G hs hz).ne_zero

private lemma continuousAt_inverse_G_square {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) : ContinuousAt (fun w => (G s w ^ 2)⁻¹) z := by
  have hg : Continuous (fun w => G s w ^ 2) := by
    simpa only [pow_two] using (continuous_G s).matrix_mul (continuous_G s)
  apply ContinuousAt.comp _ hg.continuousAt
  apply continuousAt_matrix_inv
  have hu : IsUnit (G s z ^ 2).det := by rw [det_pow]; exact (unit_G hs hz).pow 2
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hu.ne_zero

private lemma continuousAt_inverse_transfer {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (F : ℂ → Bond) (hF : ContinuousAt F z) :
    ContinuousAt (fun w => inverseTransfer s w (F w)) z := by
  have hi := continuousAt_inverse_G hs hz
  have hd : ContinuousAt (fun w => diagonalInverse s (F w)) z := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (((continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hF)).div_const _)
  exact (hi.mul hd).mul hi.star

private lemma continuousAt_inverse_dual {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (F : ℂ → Bond) (hF : ContinuousAt F z) :
    ContinuousAt (fun w => inverseDualTransfer s w (F w)) z := by
  have hi := continuousAt_inverse_G hs hz
  have hm := (hi.star.mul hF).mul hi
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact (((continuous_apply j).continuousAt.comp
    ((continuous_apply i).continuousAt.comp hm)).div_const _)

private lemma continuousAt_trialLeft {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (p : ℕ) (P : Bond) : ContinuousAt (trialLeft s p P) z := by
  induction p with
  | zero => exact continuousAt_const
  | succ p ih =>
    have he : trialLeft s (p + 1) P =
        fun w => inverseDualTransfer s w (trialLeft s p P w) := by
      funext w
      exact Function.iterate_succ_apply' _ _ _
    rw [he]
    exact continuousAt_inverse_dual hs hz (trialLeft s p P) ih

private lemma continuousAt_trialRight {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (q : ℕ) (H : Bond) : ContinuousAt (trialRight s q H) z := by
  have hi := continuousAt_inverse_G_square hs hz
  induction q with
  | zero => exact (hi.mul continuousAt_const).mul hi.star
  | succ q ih =>
    have he : trialRight s (q + 1) H =
        fun w => inverseTransfer s w (trialRight s q H w) := by
      funext w
      exact Function.iterate_succ_apply' _ _ _
    rw [he]
    exact continuousAt_inverse_transfer hs hz (trialRight s q H) ih

private lemma continuousAt_residual {s : Sector} (hs : Regular s) {z : ℂ}
    (hz : z ≠ 0) (p q : ℕ) (P H : Bond) :
    ContinuousAt (residual s p q P H) z := by
  have hl := Complex.continuous_re.continuousAt.comp
    (continuous_id.matrix_det.continuousAt.comp (continuousAt_trialLeft hs hz p P))
  have hr := Complex.continuous_re.continuousAt.comp
    (continuous_id.matrix_det.continuousAt.comp (continuousAt_trialRight hs hz q H))
  exact (Complex.continuous_ofReal.continuousAt.comp hl).add
    (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hr))


private lemma boundary_pencil (s : Sector) (z : ℂ) (l r : Fin 2 → ℂ)
    (p q : ℕ) (w : Word 2) (u : Word p) (v : Word q) :
    (prefixMap (core s z) l p * K s w *
      (G s z ^ 2 * tailMap (core s z) r q) : Matrix (Word p) (Word q) ℂ) u v =
      mpsState ((p + 2) + q) (core s z 0) (core s z 1) l r
        (Fin.append (Fin.append u w) v) := by
  rw [state_formula, wordMatrix_append, wordMatrix_append, pair_product]
  simp only [Matrix.mul_assoc, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [mul_apply, prefixMap, tailMap, mulVec, vecMul, dotProduct,
    Fin.sum_univ_two]
  ring

private lemma zero_word (s : Sector) (z : ℂ) (n : ℕ) :
    wordMatrix (core s z) (fun _ : Fin n => 0) = G s z ^ n := by
  simp [wordMatrix, core, List.ofFn_const, List.prod_replicate]

private lemma prefix_separation {s : Sector} (hs : Regular s) {z z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (l l' : Fin 2 → ℂ) (p : ℕ) (hp : 1 ≤ p)
    (hP : (leftTarget s z₀ l p).PosDef) (h : ℂ) (hh : h ≠ 0)
    (he : prefixMap (core s z) l' p = h • prefixMap (core s z₀) l p) : z = z₀ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  let v := l ᵥ* G s z₀ ^ n
  let w := l' ᵥ* G s z ^ n
  have sample (z : ℂ) (l : Fin 2 → ℂ) (j : Fin 2) :
      prefixMap (core s z) l (n + 1) (Fin.snoc (fun _ : Fin n => 0) j) =
        (l ᵥ* G s z ^ n) ᵥ* core s z j := by
    rw [prefixMap, wordMatrix_snoc, zero_word, vecMul_vecMul]
  have he' (j k : Fin 2) : (w ᵥ* core s z j) k = h * (v ᵥ* core s z₀ j) k := by
    have ht := congrFun (congrFun he (Fin.snoc (fun _ : Fin n => 0) j)) k
    simpa only [Matrix.smul_apply, smul_eq_mul, sample] using ht
  have e₀ := he' 0 0
  have e₁ := he' 1 0
  have e₂ := he' 0 1
  have e₃ := he' 1 1
  simp only [core, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    vecMul, dotProduct, mul_apply, B, G, diagonal, Matrix.of_apply,
    Fin.sum_univ_two, Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta,
    one_mul, mul_one, ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add,
    Fin.zero_ne_one, Ne.symm Fin.zero_ne_one] at e₀ e₁ e₂ e₃
  have hw₁ : w 1 = h * v 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (regular_factors hs).2.1 (regular_factors hs).1)
    dsimp [delta]
    linear_combination e₁ - s.lambda * e₀
  have hw₀ : w 0 = h * v 0 := by
    rw [hw₁] at e₀
    linear_combination e₀
  rw [hw₀, hw₁] at e₂ e₃
  by_contra hzz
  have hc : h * (z - z₀) ≠ 0 := mul_ne_zero hh (sub_ne_zero.mpr hzz)
  have ev₀ : v 0 + beta s * v 1 = 0 := by
    apply (mul_eq_zero.mp (show h * (z - z₀) * (v 0 + beta s * v 1) = 0 by
      linear_combination e₂)).resolve_left hc
  have ev₁ : beta s * delta s * v 1 = 0 := by
    apply (mul_eq_zero.mp (show h * (z - z₀) * (beta s * delta s * v 1) = 0 by
      dsimp [delta]
      linear_combination e₃ - s.lambda * e₂)).resolve_left hc
  have hv₁ : v 1 = 0 := (mul_eq_zero.mp ev₁).resolve_left
    (mul_ne_zero (regular_factors hs).2.2 (regular_factors hs).1)
  have hv₀ : v 0 = 0 := by simpa only [hv₁, mul_zero, add_zero] using ev₀
  have hv : v = 0 := by ext i; fin_cases i <;> assumption
  have hu : IsUnit (G s z₀ ^ n) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [det_pow]; exact (unit_G hs hz₀).pow n)
  have hl : l = 0 := Matrix.vecMul_injective_iff_isUnit.mpr hu
    (by simpa only [Matrix.zero_vecMul] using hv)
  have hgram : (leftTarget s z₀ l (n + 1)) = 0 := by
    rw [leftTarget, ← left_boundary_gram, hl]
    have he : prefixMap (core s z₀) 0 (n + 1) = 0 := by
      ext w i
      simp [prefixMap, vecMul, dotProduct]
    rw [he, conjTranspose_zero, Matrix.zero_mul]
  have := hP.diag_pos (i := 0)
  rw [hgram] at this
  simpa using this

private lemma phase_separation {s : Sector} (hs : Regular s) {z z₀ : ℂ}
    (hz₀ : z₀ ≠ 0) (l r l' r' : Fin 2 → ℂ) (p q : ℕ) (hp : 1 ≤ p)
    (hP : (leftTarget s z₀ l p).PosDef) (hH : (rightTarget s z₀ r q).PosDef)
    (η : ℂ) (hη : η ≠ 0)
    (he : mpsState ((p + 2) + q) (core s z 0) (core s z 1) l' r' =
      η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r) : z = z₀ := by
  let L := prefixMap (core s z₀) l p
  let L' := prefixMap (core s z) l' p
  let S := G s z₀ ^ 2 * tailMap (core s z₀) r q
  let S' := G s z ^ 2 * tailMap (core s z) r' q
  have hLL : (Lᴴ * L).PosDef := by simpa only [L, left_boundary_gram, leftTarget] using hP
  have hSS : (S * Sᴴ).PosDef := by
    have he : S * Sᴴ = rightTarget s z₀ r q := by
      dsimp [S, rightTarget]
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (tailMap (core s z₀) r q), tail_gram]
    rw [he]
    exact hH
  have hk (w : Word 2) : L' * K s w * S' = η • (L * K s w * S) := by
    ext u v
    change (prefixMap (core s z) l' p * K s w *
      (G s z ^ 2 * tailMap (core s z) r' q) : Matrix (Word p) (Word q) ℂ) u v =
      η * (prefixMap (core s z₀) l p * K s w *
      (G s z₀ ^ 2 * tailMap (core s z₀) r q) : Matrix (Word p) (Word q) ℂ) u v
    rw [boundary_pencil, boundary_pencil]
    exact congrFun he (Fin.append (Fin.append u w) v)
  have hm (M : Bond) : L' * M * S' = η • (L * M * S) := by
    obtain ⟨t₀, t₁, t₂, t₃, hM⟩ := K_decomposition hs M
    rw [hM]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      hk, smul_add, smul_smul, mul_comm η]
  obtain ⟨h, hh, hleft⟩ := pencil_rigidity L L' S S' hLL hSS η hη hm
  exact prefix_separation hs hz₀ l l' p hp hP h hh hleft


private lemma state_nonzero (s : Sector) (z : ℂ) (l r : Fin 2 → ℂ) (p q : ℕ)
    (hP : (leftTarget s z l p).PosDef) (hH : (rightTarget s z r q).PosDef) :
    mpsState ((p + 2) + q) (core s z 0) (core s z 1) l r ≠ 0 := by
  let L := prefixMap (core s z) l p
  let S := G s z ^ 2 * tailMap (core s z) r q
  have hLL : Lᴴ * L = leftTarget s z l p := left_boundary_gram _ _ _
  have hSS : S * Sᴴ = rightTarget s z r q := by
    dsimp [S, rightTarget]
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (tailMap (core s z) r q), tail_gram]
  have huP : IsUnit (Lᴴ * L).det := (isUnit_iff_isUnit_det _).mp (hLL.symm ▸ hP).isUnit
  have huH : IsUnit (S * Sᴴ).det := (isUnit_iff_isUnit_det _).mp (hSS.symm ▸ hH).isUnit
  intro hz
  have he : L * S = 0 := by
    ext u v
    have hb := boundary_pencil s z l r p q ![0, 0] u v
    simpa [K, hz, L, S] using hb
  let LL := (Lᴴ * L)⁻¹ * Lᴴ
  let RR := Sᴴ * (S * Sᴴ)⁻¹
  have hleft : LL * L = 1 := by
    dsimp [LL]
    rw [Matrix.mul_assoc, nonsing_inv_mul _ huP]
  have hright : S * RR = 1 := by
    dsimp [RR]
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ huH]
  have hbad : (1 : Bond) = 0 := calc
    1 = (LL * L) * (S * RR) := by rw [hleft, hright, Matrix.one_mul]
    _ = LL * (L * S) * RR := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [he, Matrix.mul_zero, Matrix.zero_mul]
  exact one_ne_zero hbad

/-- Every nonzero distinct common determinant root reconstructs actual finite
boundaries, preserves the entire raw Q2 and separates the full phase classes. -/
theorem distinct_residual_root_actual_ambiguity (p q : ℕ) (hp : 1 ≤ p) (_hq : 1 ≤ q)
    (s : Sector) (hs : Regular s) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (l r : Fin 2 → ℂ)
    (hP : (leftTarget s z₀ l p).PosDef) (hH : (rightTarget s z₀ r q).PosDef)
    (z : ℂ) (hz : z ≠ 0) (hne : z ≠ z₀)
    (hx : (trialLeft s p (leftTarget s z₀ l p) z).det = 0)
    (hy : (trialRight s q (rightTarget s z₀ r q) z).det = 0) :
    ∃ φ : Word ((p + 2) + q) → ℂ,
      φ ∈ openBoundaryMPS ((p + 2) + q) ∧ φ ≠ 0 ∧
      rawInterior p 2 q φ = rawInterior p 2 q
        (mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ =
        η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r := by
  let P := leftTarget s z₀ l p
  let H := rightTarget s z₀ r q
  let X := trialLeft s p P z
  let Y := trialRight s q H z
  have hX : X.IsHermitian := iterate_hermitian _
    (fun _ h => inverse_dual_hermitian hs hz h) p hP.isHermitian
  have hY : Y.IsHermitian := iterate_hermitian _
    (fun _ h => inverse_transfer_hermitian hs hz h) q
    ((hH.posSemidef.mul_mul_conjTranspose_same ((G s z ^ 2)⁻¹)).isHermitian)
  obtain ⟨v, hv⟩ := actual_rank_one_factor ((dualTransfer (core s z))^[p])
    (iterate_smul _ (dual_smul _) p) (fun _ h => iterate_psd _ (fun _ => dual_psd _) p h)
    hX hx (by rw [left_forward hs hz]; exact hP)
  obtain ⟨r', hr'⟩ := actual_rank_one_factor
    (fun W => G s z ^ 2 * (transfer (core s z))^[q] W * (G s z ^ 2)ᴴ)
    (by intro t W; rw [iterate_smul _ (transfer_smul _) q]; simp)
    (fun _ h => (iterate_psd _ (fun _ => transfer_psd _) q h).mul_mul_conjTranspose_same _)
    hY hy (by rw [right_forward hs hz]; exact hH)
  let l' := star v
  have hl' : X = vecMulVec (star l') l' := by simpa only [l', star_star] using hv
  have hleft : leftTarget s z l' p = P := by
    rw [leftTarget, ← hl']
    exact left_forward hs hz p P
  have hright : rightTarget s z r' q = H := by
    rw [rightTarget, ← hr']
    exact right_forward hs hz q H
  let φ := mpsState ((p + 2) + q) (core s z 0) (core s z 1) l' r'
  refine ⟨φ, ⟨core s z 0, core s z 1, l', r', rfl⟩,
    state_nonzero s z l' r' p q (hleft.symm ▸ hP) (hright.symm ▸ hH), ?_, ?_⟩
  · ext u v
    rw [raw_trace_dictionary, raw_trace_dictionary, hleft, hright]
  · rintro ⟨η, hη, he⟩
    have hη' : η ≠ 0 := by intro hh; simp [hh] at hη
    exact hne (phase_separation hs hz₀ l r l' r' p q hp hP hH η hη' he)

private lemma det_real {X : Bond} (hX : X.IsHermitian) : (X.det.re : ℂ) = X.det := by
  apply Complex.conj_eq_iff_re.mp
  change star X.det = X.det
  rw [← det_conjTranspose, hX.eq]

/-- With negative first residual component on both boundary circles and an
ordinary invertible real derivative at the actual root, there is an actual
nonzero nonphase competitor with exactly the same entire raw interior Q2. -/
theorem annular_regular_root_actual_ambiguity (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (s : Sector) (hs : Regular s) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (l r : Fin 2 → ℂ)
    (hP : (leftTarget s z₀ l p).PosDef) (hH : (rightTarget s z₀ r q).PosDef)
    (ε R : ℝ) (L : ℂ ≃L[ℝ] ℂ) (hε : 0 < ε) (hεz : ε < ‖z₀‖) (hzR : ‖z₀‖ < R)
    (hd : HasFDerivAt (residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q))
      (L : ℂ →L[ℝ] ℂ) z₀)
    (hb : ∀ z : ℂ, ‖z‖ = ε ∨ ‖z‖ = R →
      (residual s p q (leftTarget s z₀ l p) (rightTarget s z₀ r q) z).re < 0) :
    ∃ φ : Word ((p + 2) + q) → ℂ,
      φ ∈ openBoundaryMPS ((p + 2) + q) ∧ φ ≠ 0 ∧
      rawInterior p 2 q φ = rawInterior p 2 q
        (mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r) ∧
      ¬ ∃ η : ℂ, ‖η‖ = 1 ∧ φ =
        η • mpsState ((p + 2) + q) (core s z₀ 0) (core s z₀ 1) l r := by
  let P := leftTarget s z₀ l p
  let H := rightTarget s z₀ r q
  have hc : ContinuousOn (residual s p q P H)
      (Metric.closedBall (0 : ℂ) R \ Metric.ball 0 ε) := by
    intro z hz
    apply (continuousAt_residual hs (p := p) (q := q) (P := P) (H := H) ?_).continuousWithinAt
    intro he
    have hnorm : ε ≤ ‖z‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz.2
    rw [he, norm_zero] at hnorm
    exact (not_le_of_gt hε) hnorm
  obtain ⟨z, hzε, _, hne, hf⟩ := D5.S3.Topology.AnnularSecondZero.annular_second_zero
    (residual s p q P H) z₀ ε R L hε hεz hzR hc (residual_at_target hs hz₀ p q l r) hd hb
  have hz : z ≠ 0 := by intro he; simp [he] at hzε; linarith
  have hX : (trialLeft s p P z).IsHermitian := iterate_hermitian _
    (fun _ h => inverse_dual_hermitian hs hz h) p hP.isHermitian
  have hY : (trialRight s q H z).IsHermitian := iterate_hermitian _
    (fun _ h => inverse_transfer_hermitian hs hz h) q
    ((hH.posSemidef.mul_mul_conjTranspose_same ((G s z ^ 2)⁻¹)).isHermitian)
  have hx : (trialLeft s p P z).det = 0 := by
    rw [← det_real hX]
    have he := congrArg Complex.re hf
    simpa [residual] using he
  have hy : (trialRight s q H z).det = 0 := by
    rw [← det_real hY]
    have he := congrArg Complex.im hf
    simpa [residual] using he
  exact distinct_residual_root_actual_ambiguity p q hp hq s hs z₀ hz₀ l r hP hH z hz hne hx hy

#print axioms distinct_residual_root_actual_ambiguity
#print axioms annular_regular_root_actual_ambiguity

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
