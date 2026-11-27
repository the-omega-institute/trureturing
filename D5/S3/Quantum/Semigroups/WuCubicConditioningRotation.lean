import D5.S3.Quantum.Semigroups.WuPhysicalProductCut
import D5.S3.Quantum.Semigroups.WuCubicThermalBasis
import D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
import D5.S3.Quantum.Semigroups.WuPhysicalHighHigh

/-! The degree-one CAR covariance used by the conditioned cubic argument. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker

namespace D5.S3.Quantum.Semigroups.WuCubicConditioningRotation

open WuCubicOperatorBridge (Mat Occupation D G GInv generator dissipator)
open WuCubicThermalBasis (Index degree coefficient direction basis basis_repr)
open WuCubicHotInnerPartialTrace (reduce lift)
open WuCubicOperatorNormalization (operatorDeficit)
open WuPhysicalHighHigh (F parity)
open TwistedTwoModeOUComparison (modeJump)
open private J₁ J₂ literal_modes from D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
open private jump_zero jump_one gibbsOccupation gibbsLow gibbsHigh from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private parityValue localCoefficient phase from D5.S3.Quantum.Semigroups.WuCubicThermalBasis
open private reduce_apply reduce_lift from D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
open WuCubicThermalBasis (leftFamily rightFamily localVector e Z a b)

/-- The active and spectator annihilators are the signed physical jumps multiplied
on the left by total parity. -/
theorem degreeOne_annihilators (r : ℝ) :
    direction r (0, 1) = -(parity * modeJump 1) ∧
      direction r (1, 0) = parity * modeJump 0 := by
  constructor <;> ext ⟨i, s⟩ ⟨j, t⟩ <;>
    fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    norm_num [parity, jump_zero, jump_one, direction, leftFamily, rightFamily,
      localVector, e, Z, parityValue, Matrix.diagonal_mul, Matrix.diagonal_apply,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem raising_eq (r : ℝ) :
    direction r (0, 2) = (direction r (0, 1))ᴴ ∧
      direction r (2, 0) = (direction r (1, 0))ᴴ := by
  constructor <;> ext ⟨i, s⟩ ⟨j, t⟩ <;>
    fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    norm_num [direction, leftFamily, rightFamily, localVector, e, Z, parityValue,
      Matrix.diagonal_apply, Matrix.kroneckerMap_apply, Matrix.mul_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Conjugation in the physical occupation basis. -/
def rotate (U X : Mat) : Mat := U * X * Uᴴ

private theorem rotate_star (U X : Mat) : rotate U Xᴴ = (rotate U X)ᴴ := by
  simp [rotate, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem rotate_mul {U : Mat} (hU : Uᴴ * U = 1) (X Y : Mat) :
    rotate U (X * Y) = rotate U X * rotate U Y := by
  simp only [rotate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

private theorem rotate_of_commute {U X : Mat} (hU : U * Uᴴ = 1)
    (h : U * X = X * U) : rotate U X = X := by
  rw [rotate, h, Matrix.mul_assoc, hU, Matrix.mul_one]

private def rotateLinear (U : Mat) : Mat →ₗ[ℂ] Mat where
  toFun := rotate U
  map_add' X Y := by simp [rotate, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [rotate]

private theorem commute_diagonal {U : Mat} (hF : U * F = F * U)
    (v : Occupation → ℂ) (hv : v (0, 1) = v (1, 0)) :
    U * diagonal v = diagonal v * U := by
  let f : Occupation → ℂ := fun i => if i = (0, 0) then 1 else if i = (1, 1) then -1 else 0
  have hf (i j : Occupation) (h : f i = f j) : v i = v j := by
    obtain ⟨i, s⟩ := i
    obtain ⟨j, t⟩ := j
    fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
      norm_num [f] at h <;> simp [hv]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : f i = f j
  · rw [hf i j hij, mul_comm]
  · have h := congrArg (fun M : Mat => M i j) hF
    change (U * diagonal f) i j = (diagonal f * U) i j at h
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm (f i)] at h
    have hz : U i j * (f j - f i) = 0 := by rw [mul_sub, h, sub_self]
    have hzero := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr (Ne.symm hij))
    rw [hzero, zero_mul, mul_zero]

/-- An occupation-preserving unitary intertwining the literal Wu generator. -/
structure ModeRotation (U : Mat) : Prop where
  rows : U * Uᴴ = 1
  columns : Uᴴ * U = 1
  occupation : U * F = F * U
  generator_eq : ∀ (r : ℝ) (X : Mat), generator r (rotate U X) = rotate U (generator r X)

theorem ModeRotation.gibbs_eq {U : Mat} (hU : ModeRotation U) (r : ℝ) :
    rotate U (D r) = D r :=
  rotate_of_commute hU.rows (commute_diagonal hU.occupation _ (congrArg Complex.ofReal (mul_comm _ _)))

theorem ModeRotation.root_eq {U : Mat} (hU : ModeRotation U) (r : ℝ) :
    rotate U (G r) = G r :=
  rotate_of_commute hU.rows (commute_diagonal hU.occupation _ rfl)

private theorem parity_eq {U : Mat} (hU : ModeRotation U) : rotate U parity = parity :=
  rotate_of_commute hU.rows (commute_diagonal hU.occupation _ rfl)

private theorem star_norm_sum (z w : ℂ) (h : Complex.normSq z + Complex.normSq w = 1) :
    star z * z + star w * w = 1 := by
  rw [mul_comm (star z), mul_comm (star w)]
  change z * (starRingEnd ℂ) z + w * (starRingEnd ℂ) w = 1
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, h, Complex.ofReal_one]

private theorem mixed_sandwich (A B X : Mat) (z w : ℂ)
    (h : star z * z + star w * w = 1) :
    let P := z • A + w • B
    let Q := (-star w) • A + star z • B
    Pᴴ * X * P + Qᴴ * X * Q = Aᴴ * X * A + Bᴴ * X * B := by
  dsimp only
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_neg, star_star,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  have hA : star z * z + w * star w = 1 := by rw [mul_comm w, h]
  have hB : star w * w + z * star z = 1 := by rw [mul_comm z, add_comm, h]
  calc
    _ = (star z * z + w * star w) • (Aᴴ * X * A) +
        (star w * w + z * star z) • (Bᴴ * X * B) := by
      simp only [smul_add, smul_smul, add_smul]
      simp only [mul_neg, neg_mul, neg_neg, neg_smul]
      simp only [mul_comm z (star z), mul_comm w (star z), mul_comm z (star w),
        mul_comm w (star w)]
      abel
    _ = _ := by rw [hA, hB, one_smul, one_smul]

private theorem mixed_dissipators (A B X : Mat) (z w : ℂ)
    (h : star z * z + star w * w = 1) :
    dissipator (z • A + w • B) X + dissipator ((-star w) • A + star z • B) X =
      dissipator A X + dissipator B X := by
  let P := z • A + w • B
  let Q := (-star w) • A + star z • B
  have hs := mixed_sandwich A B X z w h
  have hp : Pᴴ * P + Qᴴ * Q = Aᴴ * A + Bᴴ * B := by
    simpa only [Matrix.mul_one] using mixed_sandwich A B 1 z w h
  change dissipator P X + dissipator Q X = _
  calc
    _ = (1 / 2 : ℂ) • ((Pᴴ * P + Qᴴ * Q) * X + X * (Pᴴ * P + Qᴴ * Q)) -
        (Pᴴ * X * P + Qᴴ * X * Q) := by
      simp only [dissipator, Matrix.add_mul, Matrix.mul_add, smul_add]
      abel
    _ = _ := by rw [hp, hs]; simp only [dissipator, Matrix.add_mul, Matrix.mul_add, smul_add]; abel

private theorem rotate_dissipator {U : Mat} (hU : Uᴴ * U = 1) (J X : Mat) :
    rotate U (dissipator J X) = dissipator (rotate U J) (rotate U X) := by
  simp only [dissipator, ← show ∀ Y, rotateLinear U Y = rotate U Y from fun _ => rfl,
    map_sub, map_add, map_smul]
  simp only [show ∀ Y, rotateLinear U Y = rotate U Y from fun _ => rfl,
    rotate_mul hU, rotate_star]

private theorem generator_literal (r : ℝ) (X : Mat) :
    generator r X =
      (2 * (gibbsLow r : ℂ)) • (dissipator J₁ X + dissipator J₂ X) +
      (2 * (gibbsHigh r : ℂ)) • (dissipator J₁ᴴ X + dissipator J₂ᴴ X) := by
  simp only [generator, Fin.sum_univ_two, literal_modes.1, literal_modes.2,
    Matrix.conjTranspose_neg, dissipator, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_add]
  abel

private theorem generator_covariance {U : Mat} (hU : Uᴴ * U = 1) {z w : ℂ}
    (h : Complex.normSq z + Complex.normSq w = 1)
    (h₁ : rotate U J₁ = z • J₁ + w • J₂)
    (h₂ : rotate U J₂ = (-star w) • J₁ + star z • J₂) (r : ℝ) (X : Mat) :
    generator r (rotate U X) = rotate U (generator r X) := by
  rw [generator_literal, generator_literal]
  let Y := rotate U X
  have h₃ : rotate U J₁ᴴ = star z • J₁ᴴ + star w • J₂ᴴ := by
    rw [rotate_star, h₁, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul]
  have h₄ : rotate U J₂ᴴ = (-w) • J₁ᴴ + z • J₂ᴴ := by
    rw [rotate_star, h₂]
    simp
  have hstar : star (star z) * star z + star (star w) * star w = 1 := by
    simpa only [star_star, mul_comm] using star_norm_sum z w h
  conv_rhs =>
    change rotateLinear U _
    simp only [map_add, map_smul]
  simp only [show ∀ Z, rotateLinear U Z = rotate U Z from fun _ => rfl,
    rotate_dissipator hU, h₁, h₂, h₃, h₄]
  rw [mixed_dissipators J₁ J₂ Y z w (star_norm_sum z w h)]
  have hadj := mixed_dissipators J₁ᴴ J₂ᴴ Y (star z) (star w) hstar
  simp only [star_star] at hadj
  rw [hadj]

open D5.S3.Quantum.FiniteDimensional
  D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence in
private theorem imbalance_eq : WuRankOneEndpointFloor.carImbalance = F := by
  ext ⟨i, s⟩ ⟨j, t⟩
  fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    norm_num [WuRankOneEndpointFloor.carImbalance, WuRankOneEndpointFloor.pauliWord,
      pauliMatrix, qubitZ, F, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, smul_eq_mul]

set_option maxHeartbeats 600000 in
private theorem exists_rotation (r : ℝ) (z w : ℂ)
    (h : Complex.normSq z + Complex.normSq w = 1) :
    ∃ U : Mat, ModeRotation U ∧
      rotate U (direction r (0, 1)) = z • direction r (0, 1) + w • direction r (1, 0) := by
  have hn : z.re ^ 2 + (-z.im) ^ 2 + w.re ^ 2 + (-w.im) ^ 2 = 1 := by
    rw [Complex.normSq_apply, Complex.normSq_apply] at h
    nlinarith only [h]
  obtain ⟨U, hrow, hcol, hF, _, h₁, h₂⟩ :=
    WuRankOneEndpointFloor.carProductCut_modeRotation z.re (-z.im) w.re (-w.im) 1 0 hn
  have hz : (z.re : ℂ) - ((-z.im : ℝ) : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp
  have hw : (w.re : ℂ) - ((-w.im : ℝ) : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp
  simp only [hz, hw, imbalance_eq] at hF h₁ h₂
  have hU : ModeRotation U := ⟨hrow, hcol, hF, generator_covariance hcol h h₁ h₂⟩
  refine ⟨U, hU, ?_⟩
  rw [(degreeOne_annihilators r).1, (degreeOne_annihilators r).2]
  rw [literal_modes.2, literal_modes.1, Matrix.mul_neg, neg_neg, rotate_mul hcol,
    parity_eq hU, show rotate U J₁ = z • J₁ + w • J₂ from h₁]
  simp [Matrix.mul_add]

private theorem rotateLinear_apply (U X : Mat) : rotateLinear U X = rotate U X := rfl

private theorem rotate_inverse {U : Mat} (hU : Uᴴ * U = 1) (X : Mat) :
    rotate Uᴴ (rotate U X) = X := by
  simp only [rotate, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (Uᴴ * U) * X * (Uᴴ * U) := by noncomm_ring
    _ = X := by simp [hU]

theorem ModeRotation.adjoint {U : Mat} (hU : ModeRotation U) : ModeRotation Uᴴ := by
  refine ⟨by simpa using hU.columns, by simpa using hU.rows, ?_, ?_⟩
  · have h := congrArg Matrix.conjTranspose hU.occupation
    have hF : Fᴴ = F := by
      rw [F, Matrix.diagonal_conjTranspose]
      congr 1
      funext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp
    simpa only [Matrix.conjTranspose_mul, hF] using h.symm
  · intro r X
    have h := congrArg (rotate Uᴴ) (hU.generator_eq r (rotate Uᴴ X))
    rw [rotate_inverse hU.columns] at h
    have hrow : (Uᴴ)ᴴ * Uᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose, hU.rows]
    have hback := rotate_inverse hrow X
    rw [Matrix.conjTranspose_conjTranspose] at hback
    rw [hback] at h
    exact h.symm

private theorem rotate_sandwich {U : Mat} (hU : ModeRotation U) (r : ℝ) (X : Mat) :
    G r * rotate U X * G r = rotate U (G r * X * G r) := by
  rw [rotate_mul hU.columns, rotate_mul hU.columns, hU.root_eq]

/-- The sandwiched generator on the embedded variable has the same covariance. -/
theorem ModeRotation.embedded_generator_eq {U : Mat} (hU : ModeRotation U) (r : ℝ) (M : Mat) :
    G r * generator r (GInv r * rotate U M * GInv r) * G r =
      rotate U (G r * generator r (GInv r * M * GInv r) * G r) := by
  have hInv : rotate U (GInv r) = GInv r :=
    rotate_of_commute hU.rows (commute_diagonal hU.occupation _ rfl)
  have hs : GInv r * rotate U M * GInv r = rotate U (GInv r * M * GInv r) := by
    rw [rotate_mul hU.columns, rotate_mul hU.columns, hInv]
  rw [hs, hU.generator_eq, rotate_sandwich hU]

private theorem rotate_pow {U : Mat} (hU : ModeRotation U) (X : Mat) (n : ℕ) :
    (rotate U X) ^ n = rotate U (X ^ n) := by
  induction n with
  | zero => simp [rotate, hU.rows]
  | succ n ih => rw [pow_succ, pow_succ, ih, rotate_mul hU.columns]

private theorem trace_rotate {U : Mat} (hU : ModeRotation U) (X : Mat) :
    (rotate U X).trace = X.trace := by
  rw [rotate, Matrix.trace_mul_cycle, hU.columns, Matrix.one_mul]

private theorem rotate_log {U : Mat} (hU : ModeRotation U) (X : Mat) :
    cfc Real.log (rotate U X) = rotate U (cfc Real.log X) :=
  Matrix.cfc_conj_isometry Real.log hU.columns (by
    change (Uᴴ)ᴴ * Uᴴ = 1
    simpa using hU.rows)

/-- Conjugation preserves the ordinary-trace Wu cubic deficit. -/
theorem ModeRotation.deficit_eq {U : Mat} (hU : ModeRotation U) (r : ℝ) (X : Mat) :
    operatorDeficit r (rotate U X) = operatorDeficit r X := by
  have hLogD := rotate_log hU (D r)
  rw [hU.gibbs_eq] at hLogD
  dsimp only [operatorDeficit]
  simp only [hU.generator_eq, rotate_sandwich hU, rotate_pow hU, rotate_log hU]
  rw [hLogD, ← rotateLinear_apply U (cfc Real.log ((G r * X * G r) ^ 3)),
    ← rotateLinear_apply U (cfc Real.log (D r)), ← map_sub, rotateLinear_apply]
  simp only [← rotate_mul hU.columns, trace_rotate hU, rotateLinear_apply, ← hLogD]

/-- The coordinate projection onto the degree-one eigenspace of the Wu generator. -/
def degreeOne (r : ℝ) (hr : 0 ≤ r) : Mat →ₗ[ℂ] Mat :=
  (basis r hr).constr ℂ fun k => if degree k = 1 then direction r k else 0

private theorem degreeOne_sum {r : ℝ} (hr : 0 ≤ r) (X : Mat) :
    degreeOne r hr X = ∑ k : Index,
      if degree k = 1 then coefficient r X k • direction r k else 0 := by
  simp only [degreeOne, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
    basis_repr]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

private theorem coefficient_generator {r : ℝ} (hr : 0 ≤ r) (X : Mat) (k : Index) :
    coefficient r (generator r X) k = (degree k : ℂ) * coefficient r X k := by
  rw [← basis_repr hr, WuCubicThermalBasis.generator_expansion hr X]
  simp_rw [← WuCubicThermalBasis.basis_apply (hr := hr)]
  exact congrFun ((basis r hr).repr_sum_self
    (fun j => (degree j : ℂ) * coefficient r X j)) k

private theorem degreeOne_eigenvector {r : ℝ} (hr : 0 ≤ r) (X : Mat) (d : ℕ)
    (hX : generator r X = (d : ℂ) • X) :
    degreeOne r hr X = if d = 1 then X else 0 := by
  have hzero (k : Index) (hk : degree k ≠ d) : coefficient r X k = 0 := by
    have h := congrArg (fun Y => (basis r hr).repr Y k) hX
    simp only [basis_repr, coefficient_generator hr] at h
    have h' : coefficient r ((d : ℂ) • X) k = (d : ℂ) * coefficient r X k := by
      simp only [← basis_repr hr, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [h'] at h
    have hprod : ((degree k : ℂ) - (d : ℂ)) * coefficient r X k = 0 := by
      rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hk))
  rw [degreeOne_sum]
  split_ifs with hd
  · subst d
    calc
      _ = ∑ k : Index, coefficient r X k • direction r k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : degree k = 1 <;> simp [hk, hzero]
      _ = X := WuCubicThermalBasis.expansion hr X
  · apply Finset.sum_eq_zero
    intro k _
    by_cases hk : degree k = 1
    · simp [hk, hzero k (by simpa [hk] using Ne.symm hd)]
    · simp [hk]

/-- Rotating an observable commutes with taking its degree-one projection. -/
theorem ModeRotation.degreeOne_eq {r : ℝ} (hr : 0 ≤ r) {U : Mat} (hU : ModeRotation U) (X : Mat) :
    degreeOne r hr (rotate U X) = rotate U (degreeOne r hr X) := by
  have h : (degreeOne r hr).comp (rotateLinear U) =
      (rotateLinear U).comp (degreeOne r hr) := by
    apply (basis r hr).ext
    intro k
    simp only [LinearMap.comp_apply, WuCubicThermalBasis.basis_apply, rotateLinear_apply]
    rw [degreeOne_eigenvector hr _ (degree k)]
    · rw [degreeOne_eigenvector hr _ _ (WuCubicThermalBasis.generator_direction hr k)]
      split_ifs <;> simp [rotate]
    · rw [hU.generator_eq, WuCubicThermalBasis.generator_direction hr k,
        ← rotateLinear_apply, map_smul, rotateLinear_apply]
  exact DFunLike.congr_fun h X

private theorem degreeOne_entries {r : ℝ} (hr : 0 ≤ r) (X : Mat) :
    degreeOne r hr X =
      coefficient r X (0, 1) • direction r (0, 1) +
      coefficient r X (0, 2) • direction r (0, 2) +
      (coefficient r X (1, 0) • direction r (1, 0) +
        coefficient r X (2, 0) • direction r (2, 0)) := by
  simp [degreeOne_sum, Fintype.sum_prod_type, Fin.sum_univ_four,
    degree, WuCubicThermalBasis.localDegree, add_assoc]

private theorem coefficient_adjoint {r : ℝ} {X : Mat} (hX : X.IsHermitian) :
    coefficient r X (0, 2) = star (coefficient r X (0, 1)) ∧
    coefficient r X (2, 0) = star (coefficient r X (1, 0)) := by
  have h (i j : Occupation) : star (X i j) = X j i := hX.apply j i
  constructor <;>
    simp [coefficient, localCoefficient, phase, parityValue, h]

private def quadrature (z : ℂ) (A : Mat) : Mat := z • A + star z • Aᴴ

private theorem degreeOne_quadratures {r : ℝ} (hr : 0 ≤ r) {X : Mat} (hX : X.IsHermitian) :
    degreeOne r hr X = quadrature (coefficient r X (0, 1)) (direction r (0, 1)) +
      quadrature (coefficient r X (1, 0)) (direction r (1, 0)) := by
  rw [degreeOne_entries hr, (coefficient_adjoint hX).1, (coefficient_adjoint hX).2,
    (raising_eq r).1, (raising_eq r).2, quadrature, quadrature]

private theorem exists_active_projection {r : ℝ} (hr : 0 ≤ r) {X : Mat}
    (hX : X.IsHermitian) :
    ∃ U : Mat, ModeRotation U ∧ ∃ t : ℝ,
      degreeOne r hr (rotate U X) = quadrature (t : ℂ) (direction r (0, 1)) := by
  let x := coefficient r X (0, 1)
  let y := coefficient r X (1, 0)
  let s := Complex.normSq x + Complex.normSq y
  have hs : 0 ≤ s := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  by_cases hzero : s = 0
  · have hx : x = 0 := Complex.normSq_eq_zero.mp
      (by linarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y])
    have hy : y = 0 := Complex.normSq_eq_zero.mp
      (by linarith [Complex.normSq_nonneg x, Complex.normSq_nonneg y])
    have hI (A : Mat) : rotate 1 A = A := by simp [rotate]
    refine ⟨1, ⟨by simp, by simp, by simp, fun r A => by rw [hI, hI]⟩, 0, ?_⟩
    rw [hI, degreeOne_quadratures hr hX]
    change quadrature x _ + quadrature y _ = _
    simp [quadrature, hx, hy]
  let t := Real.sqrt s
  have ht : 0 < t := Real.sqrt_pos.2 (lt_of_le_of_ne hs (Ne.symm hzero))
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have htSq : Complex.normSq (t : ℂ) = s := by
    simpa [t, Complex.normSq_apply, pow_two] using Real.mul_self_sqrt hs
  let z := x / (t : ℂ)
  let w := y / (t : ℂ)
  have hnorm : Complex.normSq z + Complex.normSq w = 1 := by
    simp only [z, w, Complex.normSq_div, htSq, ← add_div]
    exact div_self hzero
  obtain ⟨V, hV, hproj⟩ := exists_rotation r z w hnorm
  refine ⟨Vᴴ, hV.adjoint, t, ?_⟩
  have hq : rotate V (quadrature (t : ℂ) (direction r (0, 1))) = degreeOne r hr X := by
    have hz : (t : ℂ) * z = x := by dsimp [z]; field_simp
    have hw : (t : ℂ) * w = y := by dsimp [w]; field_simp
    have htz : star (t : ℂ) * star z = star x := by simpa using congrArg star hz
    have htw : star (t : ℂ) * star w = star y := by simpa using congrArg star hw
    rw [degreeOne_quadratures hr hX]
    change _ = quadrature x _ + quadrature y _
    simp only [quadrature, ← rotateLinear_apply V (_ + _), map_add, map_smul,
      rotateLinear_apply, rotate_star, hproj, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, smul_add, smul_smul, hz, hw, htz, htw]
    abel
  rw [hV.adjoint.degreeOne_eq hr, ← hq, rotate_inverse hV.columns]

private theorem coefficient_right {r : ℝ} (X : Mat) (k : Fin 4) :
    coefficient r X (0, k) = localCoefficient r (reduce r X) k := by
  unfold coefficient
  congr 1
  funext s t
  simp [localCoefficient, phase, reduce_apply, Fin.sum_univ_two,
    show gibbsLow r = a r from rfl, show gibbsHigh r = b r from rfl, gibbsOccupation]

private theorem residual_reduce {r : ℝ} (hr : 1 ≤ r) (X : Mat) :
    reduce r (X - lift (reduce r X)) = 0 := by
  simpa only [reduce_lift hr, sub_self] using
    (show reduce r (X - lift (reduce r X)) = reduce r X - reduce r (lift (reduce r X)) by
      ext i j
      simp [reduce_apply, mul_sub, Finset.sum_sub_distrib])

private theorem coefficient_sub {r : ℝ} (hr : 0 ≤ r) (X Y : Mat) (k : Index) :
    coefficient r (X - Y) k = coefficient r X k - coefficient r Y k := by
  simp only [← basis_repr hr, map_sub, Finsupp.sub_apply]

private theorem coefficient_spectator_lift (r : ℝ) (Q : WuCubicHotInnerPartialTrace.Local) :
    coefficient r (lift Q) (1, 0) = 0 ∧ coefficient r (lift Q) (2, 0) = 0 := by
  constructor <;>
    simp [coefficient, localCoefficient, lift, Matrix.kroneckerMap_apply]

private theorem spectator_zero {r : ℝ} (hr : 0 ≤ r) (X : Mat) {t : ℝ}
    (h : degreeOne r hr X = quadrature (t : ℂ) (direction r (0, 1))) :
    coefficient r X (1, 0) = 0 ∧ coefficient r X (2, 0) = 0 := by
  rw [degreeOne_entries hr, quadrature, ← (raising_eq r).1] at h
  simp only [← WuCubicThermalBasis.basis_apply (hr := hr)] at h
  have hc (k : Index) := congrArg (fun A => (basis r hr).repr A k) h
  have h10 := hc (1, 0)
  have h20 := hc (2, 0)
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self_apply] at h10 h20
  exact ⟨by simpa using h10, by simpa using h20⟩

private theorem degree_lt_two (k : Index) :
    degree k < 2 ↔ (k.1 = 0 ∧ k.2 ≠ 3) ∨ k = (1, 0) ∨ k = (2, 0) := by
  obtain ⟨i, j⟩ := k
  fin_cases i <;> fin_cases j <;> decide

private theorem residual_coefficients {r : ℝ} (hr : 1 ≤ r) (Y : Mat)
    (hs : coefficient r Y (1, 0) = 0 ∧ coefficient r Y (2, 0) = 0)
    (k : Index) (hk : degree k < 2) :
    coefficient r (Y - lift (reduce r Y)) k = 0 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hl := coefficient_spectator_lift r (reduce r Y)
  rcases (degree_lt_two k).1 hk with h | rfl | rfl
  · obtain ⟨i, j⟩ := k
    have hi : i = 0 := h.1
    subst i
    rw [coefficient_right, residual_reduce hr]
    fin_cases j <;> simp [localCoefficient]
  · rw [coefficient_sub hr0, hs.1, hl.1, sub_zero]
  · rw [coefficient_sub hr0, hs.2, hl.2, sub_zero]

private theorem active_quadrature_lift (r t : ℝ) :
    quadrature (t : ℂ) (direction r (0, 1)) =
      lift ((t : ℂ) • (e + eᴴ)) := by
  have ha : direction r (0, 1) = lift e := by
    simp [direction, leftFamily, rightFamily, localVector, lift]
  rw [ha]
  simp [quadrature, lift, Matrix.conjTranspose_kronecker, ← Matrix.kronecker_smul,
    ← Matrix.kronecker_add, smul_add]

/-- Every Hermitian input admits a physical rotation into the active degree-one
mode. The residual after Gibbs-weighted product projection has only degrees
two through four. -/
theorem exists_conditioning_rotation {r : ℝ} (hr : 1 ≤ r) {X : Mat} (hX : X.IsHermitian) :
    ∃ (U : Mat) (t : ℝ), ModeRotation U ∧
      let Y := rotate U X
      let H := Y - lift (reduce r Y)
      degreeOne r (zero_le_one.trans hr) Y = lift ((t : ℂ) • (e + eᴴ)) ∧
        reduce r H = 0 ∧ ∀ k : Index, degree k < 2 → coefficient r H k = 0 := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  obtain ⟨U, hU, t, ht⟩ := exists_active_projection hr0 hX
  exact ⟨U, t, hU, ht.trans (active_quadrature_lift r t), residual_reduce hr _,
    residual_coefficients hr _ (spectator_zero hr0 _ ht)⟩

end D5.S3.Quantum.Semigroups.WuCubicConditioningRotation
