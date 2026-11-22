/- GID: D5/S3/Quantum/ProcessReconstruction/PartialSwap
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/PartialSwap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary SWAP chains and diamond invariance under unitary precomposition. -/

import D5.S3.Quantum.ProcessReconstruction.PureDistance
import D5.S3.Quantum.ProcessReconstruction.SwapReconstruction
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Complementary SWAP chains and diamond invariance under unitary precomposition. -/

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder CStarAlgebra
  Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance

namespace UnitaryReconstruction

universe u

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem conjugation_mul (U V : unitaryGroup a ℂ) :
    conjugation (U * V) = (conjugation U).comp (conjugation V) := by
  apply channel_ext
  intro X
  apply CStarMatrix.ofMatrix.symm.injective
  rw [QuantumChannel.comp_apply]
  obtain ⟨Y, rfl⟩ := CStarMatrix.ofMatrix.surjective X
  rw [conjugation_apply, ← CStarMatrix.ofMatrix.apply_symm_apply
    ((conjugation V).toCompletelyPositiveMap (CStarMatrix.ofMatrix Y)),
    conjugation_apply, conjugation_apply]
  change (U.val * V.val) * Y * (U.val * V.val)ᴴ = U.val * (V.val * Y * V.valᴴ) * U.valᴴ
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

theorem conjugation_one_apply (X : CStarMatrix a a ℂ) :
    (conjugation (1 : unitaryGroup a ℂ)).toCompletelyPositiveMap X = X := by
  obtain ⟨Y, rfl⟩ := CStarMatrix.ofMatrix.surjective X
  apply CStarMatrix.ofMatrix.symm.injective
  rw [conjugation_apply]
  simp

private theorem refState_comp {r : Type*} [Fintype r] [DecidableEq r]
    (C : QuantumChannel a b) (D : QuantumChannel a a) (ρ : DensityState (r × a)) :
    referenceState (C.comp D) ρ = referenceState C (referenceState D ρ) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  simpa only [referenceState, referenceMatrix, CStarMatrix.ofMatrix.apply_symm_apply] using
    (referenceMatrix_comp C D (CStarMatrix.ofMatrix.symm ρ.val))

private theorem refState_conj_one {r : Type*} [Fintype r] [DecidableEq r]
    (ρ : DensityState (r × a)) :
    referenceState (conjugation (1 : unitaryGroup a ℂ)) ρ = ρ := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  have h := referenceMatrix_conjugation (1 : unitaryGroup a ℂ) (CStarMatrix.ofMatrix.symm ρ.val)
  simpa [referenceState, referenceMatrix, referenceUnitary, Matrix.one_kronecker_one] using h

theorem diamondDistance_precompose_unitary (C D : QuantumChannel a b) (U : unitaryGroup a ℂ) :
    diamondDistance (C.comp (conjugation U)) (D.comp (conjugation U)) =
      diamondDistance C D := by
  apply le_antisymm
  · apply diamondDistance_le _ _ (diamondDistance_nonneg' _ _)
    intro n ρ
    unfold referenceError
    rw [refState_comp, refState_comp]
    exact referenceError_le_diamond C D (referenceState (conjugation U) ρ)
  · apply diamondDistance_le _ _ (diamondDistance_nonneg' _ _)
    intro n ρ
    have h := referenceError_le_diamond (C.comp (conjugation U)) (D.comp (conjugation U))
      (referenceState (conjugation (star U)) ρ)
    unfold referenceError at h
    rw [refState_comp, refState_comp, ← refState_comp (conjugation U),
      ← conjugation_mul, Unitary.mul_star_self, refState_conj_one] at h
    exact h

theorem reducedConjugation_mul {c : Type*} [Fintype c] [DecidableEq c]
    (e : a ≃ c × b) (U V : unitaryGroup a ℂ) :
    reducedConjugation e (U * V) = (reducedConjugation e U).comp (conjugation V) := by
  simp only [reducedConjugation, conjugation_mul]
  apply channel_ext
  intro X
  simp only [QuantumChannel.comp_apply]

theorem referenceUnitary_one {r : Type*} [Fintype r] [DecidableEq r] :
    referenceUnitary r (1 : unitaryGroup a ℂ) = 1 :=
  Subtype.ext Matrix.one_kronecker_one

local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

def tensorVector {r : Type*} [Fintype r] (x : ℓ² r) (y : ℓ² a) : ℓ² (r × a) :=
  WithLp.toLp 2 (fun ij => x ij.1 * y ij.2)

omit [DecidableEq a] in
theorem tensorVector_inner {r : Type*} [Fintype r] (x x' : ℓ² r) (y y' : ℓ² a) :
    ⟪tensorVector x y, tensorVector x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, tensorVector, dotProduct, Pi.star_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq a] in
theorem tensorVector_norm_one {r : Type*} [Fintype r] {x : ℓ² r} {y : ℓ² a}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖tensorVector x y‖ = 1 := by
  apply euclidean_norm_one_of_dot (tensorVector x y).ofLp
  rw [dotProduct_comm]
  change ⟪tensorVector x y, tensorVector x y⟫_ℂ = 1
  rw [tensorVector_inner, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hx, hy]
  norm_num

theorem kron_tensorVector (M : Matrix a a ℂ) (N : Matrix b b ℂ) (x : ℓ² a) (y : ℓ² b) :
    L (M ⊗ₖ N) (tensorVector x y) = tensorVector (L M x) (L N y) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  change ((L (M ⊗ₖ N) (tensorVector x y)).ofLp) (i,j) =
    (L M x).ofLp i * (L N y).ofLp j
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum, tensorVector]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

section Sites

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → Type u)
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

local notation:max "P" s:arg => permUnitary (swapOn d s)
local notation:max "B" W:arg => referenceUnitary (System d) W

def partiallySwapped (s : Finset ι) (W : unitaryGroup (System d) ℂ) :
    unitaryGroup (System d × System d) ℂ :=
  P s * B W * star (P s)

theorem swap_star (s : Finset ι) : star (P s) = P s :=
  Subtype.ext (perm_hermitian _ (swapOn_involutive d s))

theorem partiallySwapped_empty (W : unitaryGroup (System d) ℂ) :
    partiallySwapped d ∅ W = B W := by
  have h : P (∅ : Finset ι) = 1 := by
    rw [swapOn_empty]
    exact Subtype.ext Matrix.permMatrix_one
  simp [partiallySwapped, h]

theorem partiallySwapped_univ (W : unitaryGroup (System d) ℂ) :
    (partiallySwapped d Finset.univ W).val =
      W.val ⊗ₖ (1 : Matrix (System d) (System d) ℂ) := by
  unfold partiallySwapped
  rw [swap_star, swapOn_univ]
  exact fullSwap_sandwich W.val

theorem norm_partial_step (W : unitaryGroup (System d) ℂ)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    opNorm ((partiallySwapped d (insert i s) W).val - (partiallySwapped d s W).val) ≤
      localError d i W 1 := by
  have hinsert : P (insert i s) = P ({i} : Finset ι) * P s := by
    rw [swapOn_insert d s i hi]
    exact Subtype.ext (Matrix.permMatrix_mul _ _)
  have hcomm : P ({i} : Finset ι) * P s = P s * P ({i} : Finset ι) := by
    calc
      _ = P (insert i s) := hinsert.symm
      _ = star (P (insert i s)) := (swap_star d _).symm
      _ = _ := by rw [hinsert, star_mul, swap_star, swap_star]
  let T := P ({i} : Finset ι)
  let A := B W
  have ht : star T = T := swap_star d _
  have h₁ : partiallySwapped d (insert i s) W = P s * (T * A * T) * star (P s) := by
    rw [partiallySwapped, hinsert, hcomm, star_mul, swap_star d {i}]
    simp only [mul_assoc]
    rfl
  have h₂ : conjugatedSwap d {i} W = star A * T * A := rfl
  have h₃ : conjugatedSwap d {i} (1 : unitaryGroup (System d) ℂ) = T := by
    simp [conjugatedSwap, referenceUnitary_one, T]
  have h := conjugatedSwap_local d i W 1
  rw [h₂, h₃] at h
  rw [h₁, partiallySwapped]
  change opNorm ((P s).val * (T.val * A.val * T.val) * (star (P s)).val -
    (P s).val * A.val * (star (P s)).val) ≤ _
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, opNorm_unitary_right, opNorm_unitary_left]
  have ha : A.val * (star A).val = 1 := Unitary.mul_star_self_of_mem A.prop
  have hts : T.val * T.val = 1 := by
    exact congrArg Subtype.val (show T * T = 1 from
      (congrArg (· * T) ht).symm.trans (Unitary.star_mul_self T))
  have he : T.val * A.val * T.val - A.val =
      A.val * ((star A).val * T.val * A.val - T.val) * T.val := by
    symm
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← mul_assoc, ha, one_mul, mul_assoc _ T.val T.val,
      hts, mul_one]
  rw [he, opNorm_unitary_right, opNorm_unitary_left]
  exact h

theorem norm_partial_displacement (W : unitaryGroup (System d) ℂ) (s : Finset ι) :
    opNorm ((partiallySwapped d s W).val - (B W).val) ≤ ∑ i ∈ s, localError d i W 1 := by
  induction s using Finset.induction_on with
  | empty => simp [partiallySwapped_empty, opNorm]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    let X := (partiallySwapped d (insert i s) W).val
    let Y := (partiallySwapped d s W).val
    let Z := (B W).val
    change ‖X - Z‖ ≤ _
    rw [← sub_add_sub_cancel X Y Z]
    exact (norm_add_le _ _).trans (add_le_add (norm_partial_step d W s i hi) ih)

end Sites

end UnitaryReconstruction
