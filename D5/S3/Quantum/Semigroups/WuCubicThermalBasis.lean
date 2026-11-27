/- GID: D5/S3/Quantum/Semigroups/WuCubicThermalBasis
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuCubicThermalBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex common eigenbasis for the signed CAR generator and Gibbs modular action. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! The common generator and Gibbs eigenbasis for the equal-cap two-mode generator
in Wu, arXiv:2610.33686v1, (3.54). -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker

namespace D5.S3.Quantum.Semigroups.WuCubicThermalBasis

open WuCubicOperatorBridge (Occupation Mat D generator dissipator)
open TwistedTwoModeOUComparison (modeJump)
open private gibbsLow gibbsHigh gibbsOccupation jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

abbrev LocalMat := Matrix (Fin 2) (Fin 2) ℂ
abbrev Index := Fin 4 × Fin 4

/-- The rate for the low occupation. -/
def a (r : ℝ) : ℝ := 1 / (1 + r ^ 3)

/-- The rate for the high occupation. -/
def b (r : ℝ) : ℝ := r ^ 3 * a r

theorem a_add_b {r : ℝ} (hr : 0 ≤ r) : a r + b r = 1 := by
  have h : 1 + r ^ 3 ≠ 0 := ne_of_gt (by positivity)
  unfold b a
  field_simp [h]

private theorem complex_rates {r : ℝ} (hr : 0 ≤ r) : (a r : ℂ) + (b r : ℂ) = 1 := by
  exact_mod_cast a_add_b hr

/-- The directed one-mode unit `E₀₁`. -/
def e : LocalMat := !![0,1;0,0]

private def parityValue : Fin 2 → ℂ := ![1,-1]

/-- The parity matrix on one mode. -/
private def Z : LocalMat := diagonal parityValue

/-- The stationary-mean-zero population direction. -/
def population (r : ℝ) : LocalMat := diagonal ![(b r : ℂ), -(a r : ℂ)]

/-- Local order: identity, lowering, raising, centered population. -/
def localVector (r : ℝ) (k : Fin 4) : LocalMat :=
  ![1, e, eᴴ, population r] k

def leftFamily (r : ℝ) (k : Fin 4) : Mat :=
  localVector r k ⊗ₖ (if k = 1 ∨ k = 2 then Z else 1)

def rightFamily (r : ℝ) (k : Fin 4) : Mat :=
  (1 : LocalMat) ⊗ₖ localVector r k

/-- Ordinary matrix products of the two families, with the physical parity on the left. -/
def direction (r : ℝ) (k : Index) : Mat :=
  leftFamily r k.1 * rightFamily r k.2

private def localDegree (k : Fin 4) : ℕ := ![0, 1, 1, 2] k

private def localCharge (k : Fin 4) : ℤ := ![0, -1, 1, 0] k

def degree (k : Index) : ℕ := localDegree k.1 + localDegree k.2

def charge (k : Index) : ℤ := localCharge k.1 + localCharge k.2

/-- The modular charge of a direction lies between minus its degree and its degree. -/
theorem abs_charge_le_degree (k : Index) : |charge k| ≤ (degree k : ℤ) := by
  obtain ⟨p,q⟩ := k
  fin_cases p <;> fin_cases q <;> decide

/-- The Gibbs modular eigenvalue at signed charge `q`. -/
def modularEigenvalue (r : ℝ) (q : ℤ) : ℂ := ((r : ℂ) ^ 3) ^ q

-- The right row picks up parity exactly on the off-diagonal left block.
private def phase (i j s : Fin 2) : ℂ := if i = j then 1 else parityValue s

private theorem phase_sq (i j s : Fin 2) : phase i j s * phase i j s = 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases s <;> norm_num [phase, parityValue]

private def twistedTensor (A B : LocalMat) : Mat :=
  fun i j => phase i.1 j.1 i.2 * (A i.1 j.1 * B i.2 j.2)

private theorem localParity (r : ℝ) (k : Fin 4) (i j s : Fin 2) :
    localVector r k i j * (if k = 1 ∨ k = 2 then parityValue s else 1) =
      phase i j s * localVector r k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases s <;>
    norm_num [localVector, phase, parityValue, e, population, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.of_apply]

private theorem direction_eq_tensor (r : ℝ) (k : Index) :
    direction r k = twistedTensor (localVector r k.1) (localVector r k.2) := by
  rw [direction, leftFamily, rightFamily, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  ext ⟨i,s⟩ ⟨j,t⟩
  simp only [Matrix.kroneckerMap_apply]
  change localVector r k.1 i j *
      (((if k.1 = 1 ∨ k.1 = 2 then Z else 1) * localVector r k.2) s t) =
    phase i j s * (localVector r k.1 i j * localVector r k.2 s t)
  rw [show (((if k.1 = 1 ∨ k.1 = 2 then Z else 1) * localVector r k.2) s t) =
      (if k.1 = 1 ∨ k.1 = 2 then parityValue s else 1) * localVector r k.2 s t by
    split_ifs <;> simp [Z, Matrix.diagonal_mul]]
  rw [← mul_assoc, localParity, mul_assoc]

private def localGenerator (a b : ℂ) (X : LocalMat) : LocalMat :=
  !![2 * b * (X 0 0 - X 1 1), (a + b) * X 0 1;
      (a + b) * X 1 0, 2 * a * (X 1 1 - X 0 0)]

private theorem local_generator_direction {r : ℝ} (hr : 0 ≤ r) (k : Fin 4) :
    localGenerator (a r) (b r) (localVector r k) =
      (localDegree k : ℂ) • localVector r k := by
  have hab := complex_rates hr
  have hneg : -(a r : ℂ) - (b r : ℂ) = -1 := by linear_combination -hab
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [localGenerator, localVector, localDegree, e, population, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, hab, hneg]
  linear_combination (2 * (b r : ℂ)) * hab

set_option maxHeartbeats 3000000 in
-- The two jump matrices have one possible nonzero entry in each row and column.
private theorem generator_twistedTensor (r : ℝ) (A B : LocalMat) :
    generator r (twistedTensor A B) =
      twistedTensor (localGenerator (a r) (b r) A) B +
        twistedTensor A (localGenerator (a r) (b r) B) := by
  ext ⟨i,s⟩ ⟨j,t⟩
  fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    norm_num [generator, dissipator, jump_zero, jump_one, twistedTensor, localGenerator,
      show gibbsLow r = a r from rfl, show gibbsHigh r = b r from rfl,
      phase, parityValue, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- The actual Wu generator acts by the sum of the two local degrees. -/
theorem generator_direction {r : ℝ} (hr : 0 ≤ r) (k : Index) :
    generator r (direction r k) = (degree k : ℂ) • direction r k := by
  rw [direction_eq_tensor, generator_twistedTensor,
    local_generator_direction hr, local_generator_direction hr]
  ext i j
  simp only [twistedTensor, degree, Nat.cast_add, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The actual Wu generator as a complex-linear endomorphism. -/
def generatorLinear (r : ℝ) : Mat →ₗ[ℂ] Mat where
  toFun := generator r
  map_add' X Y := by
    simp only [generator, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [dissipator, Matrix.mul_add, Matrix.add_mul, smul_add, smul_sub]
    abel
  map_smul' c X := by
    have h (J : Mat) : dissipator J (c • X) = c • dissipator J X := by
      simp only [dissipator, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_sub]
      rw [smul_comm (1 / 2 : ℂ) c]
    simp only [RingHom.id_apply, generator, h, Finset.smul_sum, smul_add]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_comm (2 * (gibbsLow r : ℂ)) c, smul_comm (2 * (gibbsHigh r : ℂ)) c]

@[simp] theorem generatorLinear_apply (r : ℝ) (X : Mat) :
    generatorLinear r X = generator r X := rfl

private def occupationWeight (r : ℝ) (i : Fin 2) : ℂ := gibbsOccupation r i

private theorem local_modular_direction {r : ℝ} (hr : r ≠ 0) (k : Fin 4) (i j : Fin 2) :
    occupationWeight r i * localVector r k i j =
      modularEigenvalue r (localCharge k) * (localVector r k i j * occupationWeight r j) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hb : (b r : ℂ) = (r : ℂ) ^ 3 * (a r : ℂ) := by simp [b]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [occupationWeight, gibbsOccupation, show gibbsLow r = a r from rfl,
      show gibbsHigh r = b r from rfl, localVector, localCharge, modularEigenvalue, e,
      population, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, hb] <;>
    field_simp [hrC] <;> ring

/-- The modular eigenvector relation in the actual Gibbs matrix, in a form that avoids
the matrix inverse. -/
theorem modular_direction {r : ℝ} (hr : r ≠ 0) (k : Index) :
    D r * direction r k = modularEigenvalue r (charge k) • (direction r k * D r) := by
  have ht : (r : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hr)
  rw [direction_eq_tensor]
  ext ⟨i,s⟩ ⟨j,t⟩
  simp only [D, diagonal_mul, mul_diagonal, Complex.ofReal_mul,
    twistedTensor, Matrix.smul_apply, smul_eq_mul, modularEigenvalue, charge, zpow_add₀ ht]
  change (occupationWeight r i * occupationWeight r s) *
      (phase i j s * (localVector r k.1 i j * localVector r k.2 s t)) =
    (((r : ℂ) ^ 3) ^ localCharge k.1 * ((r : ℂ) ^ 3) ^ localCharge k.2) *
      (phase i j s * (localVector r k.1 i j * localVector r k.2 s t) *
        (occupationWeight r j * occupationWeight r t))
  calc
    _ = phase i j s * ((occupationWeight r i * localVector r k.1 i j) *
        (occupationWeight r s * localVector r k.2 s t)) := by ring
    _ = _ := by
      rw [local_modular_direction hr, local_modular_direction hr]
      unfold modularEigenvalue
      ring

/-- Gibbs modular conjugation as a complex-linear endomorphism. -/
def modularLinear (r : ℝ) : Mat →ₗ[ℂ] Mat where
  toFun X := D r * X * (D r)⁻¹
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

private theorem gibbs_det_unit {r : ℝ} (hr : 0 < r) : IsUnit (D r).det := by
  rw [D, Matrix.det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hweight (j : Fin 2) : gibbsOccupation r j ≠ 0 := by
    fin_cases j <;> simp [gibbsOccupation, gibbsLow, gibbsHigh, pow_ne_zero _ hr.ne']
    all_goals positivity
  exact_mod_cast mul_ne_zero (hweight i.1) (hweight i.2)

/-- The basis directions diagonalize actual Gibbs conjugation at positive temperature ratio. -/
theorem modularLinear_direction {r : ℝ} (hr : 0 < r) (k : Index) :
    modularLinear r (direction r k) =
      modularEigenvalue r (charge k) • direction r k := by
  change D r * direction r k * (D r)⁻¹ = _
  rw [modular_direction hr.ne', Matrix.smul_mul,
    Matrix.mul_nonsing_inv_cancel_right _ _ (gibbs_det_unit hr)]

private def localCoefficient (r : ℝ) (X : LocalMat) (k : Fin 4) : ℂ :=
  ![(a r : ℂ) * X 0 0 + (b r : ℂ) * X 1 1, X 0 1, X 1 0, X 0 0 - X 1 1] k

private theorem local_expansion {r : ℝ} (hr : 0 ≤ r) (X : LocalMat) (i j : Fin 2) :
    (∑ k : Fin 4, localCoefficient r X k * localVector r k i j) = X i j := by
  have hab := complex_rates hr
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_four, localCoefficient, localVector, e, population,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.of_apply] <;>
    first | linear_combination (X 0 0) * hab | linear_combination (X 1 1) * hab

/-- Apply the one-mode coefficient formula in the left and then in the right index,
after undoing parity on the left off-diagonal blocks. -/
def coefficient (r : ℝ) (X : Mat) (k : Index) : ℂ :=
  localCoefficient r (fun s t =>
    localCoefficient r (fun i j => phase i j s * X (i,s) (j,t)) k.1) k.2

/-- Explicit expansion of every complex matrix into its sixteen physical directions. -/
theorem expansion {r : ℝ} (hr : 0 ≤ r) (X : Mat) :
    (∑ k : Index, coefficient r X k • direction r k) = X := by
  ext ⟨i,s⟩ ⟨j,t⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    direction_eq_tensor, twistedTensor]
  let leftCoords (p : Fin 4) : LocalMat :=
    fun u v => localCoefficient r (fun l m => phase l m u * X (l,u) (m,v)) p
  calc
    _ = phase i j s * ∑ p : Fin 4, (∑ q : Fin 4,
        localCoefficient r (leftCoords p) q * localVector r q s t) *
          localVector r p i j := by
      simp only [Finset.mul_sum, Finset.sum_mul, coefficient]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = phase i j s * (phase i j s * X (i,s) (j,t)) := by
      have hright (p : Fin 4) := local_expansion hr (leftCoords p) s t
      simp only [hright]
      exact congrArg (phase i j s * ·)
        (local_expansion hr (fun l m => phase l m s * X (l,s) (m,t)) i j)
    _ = X (i,s) (j,t) := by rw [← mul_assoc, phase_sq, one_mul]

private theorem direction_span {r : ℝ} (hr : 0 ≤ r) :
    ⊤ ≤ Submodule.span ℂ (Set.range (direction r)) := by
  intro X _
  rw [← expansion hr X]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

private theorem card_index :
    Fintype.card Index = Module.finrank ℂ Mat := by
  simp [Index, Mat, Occupation, Module.finrank_matrix]

/-- The sixteen physical directions as a complex basis of all four-by-four matrices. -/
def basis (r : ℝ) (hr : 0 ≤ r) : Module.Basis Index ℂ Mat :=
  basisOfTopLeSpanOfCardEqFinrank (direction r) (direction_span hr) card_index

@[simp] theorem basis_apply {r : ℝ} (hr : 0 ≤ r) (k : Index) :
    basis r hr k = direction r k :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank
    (direction r) (direction_span hr) card_index) k

theorem basis_repr {r : ℝ} (hr : 0 ≤ r) (X : Mat) (k : Index) :
    (basis r hr).repr X k = coefficient r X k := by
  have h := (basis r hr).repr_sum_self (coefficient r X)
  simp only [basis_apply, expansion hr X] at h
  exact congrFun h k

/-- The generator is diagonal in the explicit coefficient expansion. -/
theorem generator_expansion {r : ℝ} (hr : 0 ≤ r) (X : Mat) :
    generator r X =
      ∑ k : Index, ((degree k : ℂ) * coefficient r X k) • direction r k := by
  conv_lhs => rw [← generatorLinear_apply, ← expansion hr X]
  simp only [map_sum, map_smul, generatorLinear_apply, generator_direction hr, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

/-- The Hermitian combination of the charges `-2` and `2` at degree two. -/
def highChargeHermitian (r : ℝ) : Mat := direction r (1,1) - direction r (2,2)

theorem highChargeHermitian_eq (r : ℝ) :
    highChargeHermitian r = single (0,0) (1,1) 1 + single (1,1) (0,0) 1 := by
  ext ⟨i,s⟩ ⟨j,t⟩
  fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    norm_num [highChargeHermitian, direction_eq_tensor, twistedTensor, phase, parityValue,
      localVector, e, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      Prod.mk.injEq, Matrix.add_apply, Matrix.sub_apply]

theorem highChargeHermitian_isHermitian (r : ℝ) : (highChargeHermitian r).IsHermitian := by
  rw [highChargeHermitian_eq]
  change (single (0,0) (1,1) (1 : ℂ) + single (1,1) (0,0) 1 : Mat)ᴴ = _
  simp [add_comm]

theorem highChargeHermitian_ne_zero (r : ℝ) : highChargeHermitian r ≠ 0 := by
  intro h
  have hentry := congrArg (fun X : Mat => X (0,0) (1,1)) h
  norm_num [highChargeHermitian_eq, Matrix.add_apply, Matrix.single_apply, Prod.mk.injEq] at hentry

theorem generator_highChargeHermitian {r : ℝ} (hr : 0 ≤ r) :
    generator r (highChargeHermitian r) = (2 : ℂ) • highChargeHermitian r := by
  change generatorLinear r (direction r (1,1) - direction r (2,2)) =
    (2 : ℂ) • (direction r (1,1) - direction r (2,2))
  rw [map_sub, generatorLinear_apply, generatorLinear_apply,
    generator_direction hr, generator_direction hr,
    show degree (1,1) = 2 by decide, show degree (2,2) = 2 by decide, Nat.cast_two, smul_sub]

end D5.S3.Quantum.Semigroups.WuCubicThermalBasis
