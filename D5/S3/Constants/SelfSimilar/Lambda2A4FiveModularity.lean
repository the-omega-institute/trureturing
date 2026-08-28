/- GID: D5/S3/Constants/SelfSimilar/Lambda2A4FiveModularity
   generality: I
   mirror-B: D5/B/S3/Constants/SelfSimilar/Lambda2A4FiveModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The six-dimensional Lambda2 A4 lattice is five-modular with discriminant 5^3. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * No declaration covering `Lambda^2 A4`, its five-modularity, or this Gram
     matrix occurs in `D5/` or the frozen catalog.
   * Pinned Mathlib supplies `LinearMap.BilinForm.dualSubmodule` for the actual
     integral dual lattice and `Module.finrank_eq_card_basis` for its rank.
   * Pinned Mathlib's `BilinForm.IsometryEquiv` does not apply directly: these
     lattices are Z-modules with an R-valued form. `LatticeSimilarity` below is
     the thin scaled, R-valued lattice analogue; it retains a Z-linear
     equivalence and the exact scale equation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity

open LinearMap

/-- The integral Gram matrix of `Lambda^2 A4` in the ordered basis
`u12, u13, u14, u23, u24, u34`. -/
def lambda2A4GramInt : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![3, 1, 1, -1, -1, 0],
    ![1, 3, 1, 1, 0, -1],
    ![1, 1, 3, 0, 1, 1],
    ![-1, 1, 0, 3, 1, -1],
    ![-1, 0, 1, 1, 3, 1],
    ![0, -1, 1, -1, 1, 3]]

/-- The same integral Gram matrix, regarded over the ambient real scalar field. -/
noncomputable def lambda2A4Gram : Matrix (Fin 6) (Fin 6) ℝ :=
  lambda2A4GramInt.map fun x ↦ (x : ℝ)

/-- The coordinate-sum functional whose kernel is the real `A4` root space. -/
def a4CoordinateSum : (Fin 5 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- The concrete real `A4` root space `sum x_i = 0` from source lines 2767-2777. -/
def a4RootSpace : Submodule ℝ (Fin 5 → ℝ) :=
  LinearMap.ker a4CoordinateSum

/-- Coordinates on `A4` in the ordered root basis `b_i = e_i - e_5`. -/
noncomputable def a4RootCoordinates : a4RootSpace ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun x i := (x : Fin 5 → ℝ) i.castSucc
  invFun x :=
    ⟨Fin.snoc x (-∑ i, x i),
      by
        change ∑ i : Fin 5,
          Fin.snoc x (-∑ j : Fin 4, x j) i = 0
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        ring⟩
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl
  left_inv x := by
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp only [Fin.snoc_last]
        have hx := x.property
        change ∑ i, (x : Fin 5 → ℝ) i = 0 at hx
        rw [Fin.sum_univ_castSucc] at hx
        linarith
    | cast j => simp only [Fin.snoc_castSucc]
  right_inv x := by
    ext i
    simp only [Fin.snoc_castSucc]

/-- The ordered basis `b1,b2,b3,b4` of the concrete `A4` root space. -/
noncomputable def a4RootBasis : Module.Basis (Fin 4) ℝ a4RootSpace :=
  Module.Basis.ofEquivFun a4RootCoordinates

/-- The actual second exterior power of the concrete real `A4` root space. -/
abbrev Lambda2A4Space := ⋀[ℝ]^2 a4RootSpace

/-- The source order `12,13,14,23,24,34` on two-element subsets of `Fin 4`. -/
def lambda2A4Pair (i : Fin 6) : Set.powersetCard (Fin 4) 2 :=
  ![Set.powersetCard.ofCard (s := {0, 1}) (by decide),
    Set.powersetCard.ofCard (s := {0, 2}) (by decide),
    Set.powersetCard.ofCard (s := {0, 3}) (by decide),
    Set.powersetCard.ofCard (s := {1, 2}) (by decide),
    Set.powersetCard.ofCard (s := {1, 3}) (by decide),
    Set.powersetCard.ofCard (s := {2, 3}) (by decide)] i

set_option linter.style.nativeDecide false in
/-- The source order is a bijection onto the standard exterior-power index. -/
noncomputable def lambda2A4PairEquiv : Fin 6 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective lambda2A4Pair (by native_decide)

/-- The ordered exterior basis `u12,u13,u14,u23,u24,u34`. -/
noncomputable def lambda2A4Basis : Module.Basis (Fin 6) ℝ Lambda2A4Space :=
  (a4RootBasis.exteriorPower 2).reindex lambda2A4PairEquiv.symm

/-- The concrete integral exterior-square lattice inside the real exterior power. -/
def lambda2A4Lattice : Submodule ℤ Lambda2A4Space :=
  Submodule.span ℤ (Set.range lambda2A4Basis)

/-- The source ordered wedge basis, now as an integral basis of `Lambda^2 A4`. -/
noncomputable def lambda2A4IntegralBasis :
    Module.Basis (Fin 6) ℤ lambda2A4Lattice :=
  lambda2A4Basis.restrictScalars ℤ

/-- The integral Hodge discriminant matrix from source lines 2913-2924. -/
def lambda2A4HodgeMatrixInt : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![0, 1, -1, 1, -1, -3],
    ![-1, 0, 1, 1, 3, 1],
    ![1, -1, 0, -3, -1, 1],
    ![-1, -1, -3, 0, -1, -1],
    ![1, 3, 1, 1, 0, -1],
    ![-3, -1, -1, 1, 1, 0]]

/-- The fixed Hodge matrix over the ambient real scalar field. -/
noncomputable def lambda2A4HodgeMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  lambda2A4HodgeMatrixInt.map fun x ↦ (x : ℝ)

/-- The fixed integral matrix `U = GJ/5` from source lines 4197-4219. -/
def lambda2A4UnimodularMatrixInt : Matrix (Fin 6) (Fin 6) ℤ :=
  ![![0, 0, 0, 0, 0, -1],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, -1, 0, 0],
    ![0, 0, -1, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![-1, 0, 0, 0, 0, 0]]

/-- The fixed unimodular pairing matrix over the real scalar field. -/
noncomputable def lambda2A4UnimodularMatrix : Matrix (Fin 6) (Fin 6) ℝ :=
  lambda2A4UnimodularMatrixInt.map fun x ↦ (x : ℝ)

/-- The concrete real bilinear form on `Lambda^2 A4`, specified by the source Gram matrix. -/
noncomputable def lambda2A4Form : LinearMap.BilinForm ℝ Lambda2A4Space :=
  Matrix.toBilin lambda2A4Basis lambda2A4Gram

/-- The concrete Hodge operator on `Lambda^2 A4`, specified by the source matrix `J`. -/
noncomputable def lambda2A4Hodge : Lambda2A4Space →ₗ[ℝ] Lambda2A4Space :=
  Matrix.toLin lambda2A4Basis lambda2A4Basis lambda2A4HodgeMatrix

set_option linter.style.nativeDecide false in
/-- The source Gram determinant, computed over the integral matrix. -/
theorem lambda2A4GramInt_det : lambda2A4GramInt.det = 125 := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The source Hodge matrix is a similitude of multiplier five. -/
theorem lambda2A4_hodge_similitude_matrix_int :
    lambda2A4HodgeMatrixInt.transpose * lambda2A4GramInt * lambda2A4HodgeMatrixInt =
      5 • lambda2A4GramInt := by
  native_decide

set_option linter.style.nativeDecide false in
/-- Pairing `(J/5)` of the source basis against itself gives the fixed matrix `U`. -/
theorem lambda2A4_hodge_pairing_matrix_int :
    lambda2A4HodgeMatrixInt.transpose * lambda2A4GramInt =
      5 • lambda2A4UnimodularMatrixInt := by
  native_decide

set_option linter.style.nativeDecide false in
/-- The source matrix `U` is unimodular with determinant `-1`. -/
theorem lambda2A4UnimodularMatrixInt_det :
    lambda2A4UnimodularMatrixInt.det = -1 := by
  native_decide

/-- Real form of `Jᵀ G J = 5G`. -/
theorem lambda2A4_hodge_similitude_matrix :
    lambda2A4HodgeMatrix.transpose * lambda2A4Gram * lambda2A4HodgeMatrix =
      (5 : ℝ) • lambda2A4Gram := by
  have h := congrArg
    (fun M : Matrix (Fin 6) (Fin 6) ℤ ↦ M.map fun x ↦ (x : ℝ))
    lambda2A4_hodge_similitude_matrix_int
  have hsmul :
      (5 • lambda2A4GramInt).map (fun x ↦ (x : ℝ)) =
        (5 : ℝ) • lambda2A4GramInt.map (fun x ↦ (x : ℝ)) := by
    ext i j
    change (((5 : ℤ) * lambda2A4GramInt i j : ℤ) : ℝ) =
      (5 : ℝ) * (lambda2A4GramInt i j : ℝ)
    norm_cast
  rw [hsmul] at h
  simpa only [lambda2A4HodgeMatrix, lambda2A4Gram,
    Matrix.map_mul_intCast, Matrix.transpose_map] using h

/-- Real form of `Jᵀ G = 5U`. -/
theorem lambda2A4_hodge_pairing_matrix :
    lambda2A4HodgeMatrix.transpose * lambda2A4Gram =
      (5 : ℝ) • lambda2A4UnimodularMatrix := by
  have h := congrArg
    (fun M : Matrix (Fin 6) (Fin 6) ℤ ↦ M.map fun x ↦ (x : ℝ))
    lambda2A4_hodge_pairing_matrix_int
  have hsmul :
      (5 • lambda2A4UnimodularMatrixInt).map (fun x ↦ (x : ℝ)) =
        (5 : ℝ) • lambda2A4UnimodularMatrixInt.map (fun x ↦ (x : ℝ)) := by
    ext i j
    change (((5 : ℤ) * lambda2A4UnimodularMatrixInt i j : ℤ) : ℝ) =
      (5 : ℝ) * (lambda2A4UnimodularMatrixInt i j : ℝ)
    norm_cast
  rw [hsmul] at h
  simpa only [lambda2A4HodgeMatrix, lambda2A4Gram, lambda2A4UnimodularMatrix,
    Matrix.map_mul_intCast, Matrix.transpose_map] using h

/-- The real Gram matrix has determinant `125`. -/
theorem lambda2A4Gram_det : lambda2A4Gram.det = (125 : ℝ) := by
  rw [lambda2A4Gram, ← Int.cast_det, lambda2A4GramInt_det]
  norm_num

/-- The concrete Gram form is nondegenerate. -/
theorem lambda2A4Form_nondegenerate : lambda2A4Form.Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero lambda2A4Basis]
  have hdet : lambda2A4Gram.det ≠ 0 := by
    rw [lambda2A4Gram_det]
    norm_num
  simpa [lambda2A4Form] using hdet

/-- The fixed Hodge operator scales the concrete Gram form by five. -/
theorem lambda2A4_hodge_similitude (x y : Lambda2A4Space) :
    lambda2A4Form (lambda2A4Hodge x) (lambda2A4Hodge y) =
      5 * lambda2A4Form x y := by
  have hforms :
      lambda2A4Form.comp lambda2A4Hodge lambda2A4Hodge =
        (5 : ℝ) • lambda2A4Form := by
    apply (LinearMap.BilinForm.toMatrix lambda2A4Basis).injective
    rw [LinearMap.BilinForm.toMatrix_comp (b := lambda2A4Basis)
      (c := lambda2A4Basis)]
    simpa only [lambda2A4Form, lambda2A4Hodge,
      LinearMap.toMatrix_toLin, LinearMap.BilinForm.toMatrix_toBilin, map_smul] using
      lambda2A4_hodge_similitude_matrix
  change (lambda2A4Form.comp lambda2A4Hodge lambda2A4Hodge) x y = _
  rw [hforms]
  simp

/-- Pairing `(J/5)u_i` with `u_j` gives the source unimodular matrix `U`. -/
theorem lambda2A4_hodge_basis_pairing (i j : Fin 6) :
    lambda2A4Form ((5 : ℝ)⁻¹ • lambda2A4Hodge (lambda2A4Basis i))
        (lambda2A4Basis j) = lambda2A4UnimodularMatrix i j := by
  have hmatrix := congrFun (congrFun lambda2A4_hodge_pairing_matrix i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hmatrix
  have hpair :
      lambda2A4Form (lambda2A4Hodge (lambda2A4Basis i)) (lambda2A4Basis j) =
        (lambda2A4HodgeMatrix.transpose * lambda2A4Gram) i j := by
    calc
      _ = LinearMap.BilinForm.toMatrix lambda2A4Basis
          (lambda2A4Form.comp lambda2A4Hodge
            (LinearMap.id : Lambda2A4Space →ₗ[ℝ] Lambda2A4Space)) i j := by
        simp [LinearMap.BilinForm.comp_apply]
      _ = _ := by
        rw [LinearMap.BilinForm.toMatrix_comp (b := lambda2A4Basis)
          (c := lambda2A4Basis)]
        simp only [lambda2A4Form, lambda2A4Hodge,
          LinearMap.toMatrix_toLin, LinearMap.BilinForm.toMatrix_toBilin,
          LinearMap.toMatrix_id, Matrix.mul_one]
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hpair, hmatrix]
  ring

/-- Reversal of the six source basis positions. -/
def lambda2A4ReverseIndex (i : Fin 6) : Fin 6 :=
  ![5, 4, 3, 2, 1, 0] i

set_option linter.style.nativeDecide false in
/-- Reversal is a permutation of the ordered exterior basis. -/
noncomputable def lambda2A4ReverseEquiv : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective lambda2A4ReverseIndex (by native_decide)

theorem lambda2A4ReverseEquiv_symm_apply (i : Fin 6) :
    lambda2A4ReverseEquiv.symm i = lambda2A4ReverseIndex i := by
  apply lambda2A4ReverseEquiv.injective
  rw [lambda2A4ReverseEquiv.apply_symm_apply]
  change i = lambda2A4ReverseIndex (lambda2A4ReverseIndex i)
  fin_cases i <;> rfl

/-- Signs of the anti-diagonal unimodular matrix `U`. -/
def lambda2A4DualSign (i : Fin 6) : ℤˣ :=
  ![(-1 : ℤˣ), 1, -1, -1, 1, -1] i

/-- The dual lattice is the integral span of the reverse-ordered real dual basis. -/
theorem lambda2A4DualSubmodule_eq_span :
    lambda2A4Form.dualSubmodule lambda2A4Lattice =
      Submodule.span ℤ (Set.range <|
        (lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis).reindex
          lambda2A4ReverseEquiv) := by
  change lambda2A4Form.dualSubmodule
      (Submodule.span ℤ (Set.range lambda2A4Basis)) = _
  rw [lambda2A4Form.dualSubmodule_span_of_basis
    lambda2A4Form_nondegenerate lambda2A4Basis]
  simp

/-- The reverse-ordered real dual basis, restricted to the actual integral dual lattice. -/
noncomputable def lambda2A4DualIntegralBasisBase :
    Module.Basis (Fin 6) ℤ
      (lambda2A4Form.dualSubmodule lambda2A4Lattice) :=
  (((lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis).reindex
      lambda2A4ReverseEquiv).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ lambda2A4DualSubmodule_eq_span.symm)

/-- The integral dual basis whose pairing matrix is exactly the source matrix `U`. -/
noncomputable def lambda2A4DualIntegralBasis :
    Module.Basis (Fin 6) ℤ
      (lambda2A4Form.dualSubmodule lambda2A4Lattice) :=
  lambda2A4DualIntegralBasisBase.unitsSMul lambda2A4DualSign

/-- The same source signs, now as real units. -/
def lambda2A4DualSignReal (i : Fin 6) : ℝˣ :=
  ![(-1 : ℝˣ), 1, -1, -1, 1, -1] i

/-- The signed, reverse-ordered real dual basis underlying the integral dual basis. -/
noncomputable def lambda2A4DualRealBasis :
    Module.Basis (Fin 6) ℝ Lambda2A4Space :=
  ((lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis).reindex
    lambda2A4ReverseEquiv).unitsSMul lambda2A4DualSignReal

/-- The fixed integral equivalence from `Lambda²A₄` to its actual dual lattice. -/
noncomputable def lambda2A4DualEquiv :
    lambda2A4Lattice ≃ₗ[ℤ]
      lambda2A4Form.dualSubmodule lambda2A4Lattice :=
  lambda2A4IntegralBasis.equiv lambda2A4DualIntegralBasis (Equiv.refl (Fin 6))

theorem lambda2A4DualIntegralBasisBase_apply (i : Fin 6) :
    (lambda2A4DualIntegralBasisBase i : Lambda2A4Space) =
      lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis
        (lambda2A4ReverseIndex i) := by
  simp [lambda2A4DualIntegralBasisBase, Module.Basis.reindex_apply,
    lambda2A4ReverseEquiv_symm_apply]

theorem lambda2A4DualIntegralBasis_apply (i : Fin 6) :
    (lambda2A4DualIntegralBasis i : Lambda2A4Space) =
      (lambda2A4DualSign i : ℤ) •
        lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis
          (lambda2A4ReverseIndex i) := by
  simp [lambda2A4DualIntegralBasis, Module.Basis.unitsSMul_apply,
    lambda2A4DualIntegralBasisBase_apply, Units.smul_def]

/-- The real and integral signed dual bases have the same ambient vectors. -/
theorem lambda2A4DualRealBasis_eq_integral (i : Fin 6) :
    lambda2A4DualRealBasis i =
      (lambda2A4DualIntegralBasis i : Lambda2A4Space) := by
  rw [lambda2A4DualIntegralBasis_apply]
  simp only [lambda2A4DualRealBasis, Module.Basis.unitsSMul_apply,
    Module.Basis.reindex_apply, lambda2A4ReverseEquiv_symm_apply]
  fin_cases i <;>
    norm_num [lambda2A4DualSignReal, lambda2A4DualSign, Units.smul_def]

/-- The concrete integral dual basis has the source pairing matrix `U`. -/
theorem lambda2A4DualIntegralBasis_pairing (i j : Fin 6) :
    lambda2A4Form (lambda2A4DualIntegralBasis i : Lambda2A4Space)
      (lambda2A4Basis j) = lambda2A4UnimodularMatrix i j := by
  rw [lambda2A4DualIntegralBasis_apply, map_zsmul]
  change (lambda2A4DualSign i : ℤ) •
      lambda2A4Form
        (lambda2A4Form.dualBasis lambda2A4Form_nondegenerate lambda2A4Basis
          (lambda2A4ReverseIndex i)) (lambda2A4Basis j) = _
  rw [lambda2A4Form.apply_dualBasis_left]
  fin_cases i <;> fin_cases j <;>
    norm_num [lambda2A4DualSign, lambda2A4ReverseIndex,
      lambda2A4UnimodularMatrix, lambda2A4UnimodularMatrixInt] <;> decide

/-- Each dual basis vector is exactly `(J/5)` of the corresponding wedge basis vector. -/
theorem lambda2A4DualIntegralBasis_eq_hodge (i : Fin 6) :
    (lambda2A4DualIntegralBasis i : Lambda2A4Space) =
      (5 : ℝ)⁻¹ • lambda2A4Hodge (lambda2A4Basis i) := by
  apply LinearMap.ker_eq_bot.mp lambda2A4Form_nondegenerate.ker_eq_bot
  apply lambda2A4Basis.ext
  intro j
  exact (lambda2A4DualIntegralBasis_pairing i j).trans
    (lambda2A4_hodge_basis_pairing i j).symm

/-- The concrete lattice equivalence is the source formula `x ↦ Jx/5`. -/
theorem lambda2A4DualEquiv_apply (x : lambda2A4Lattice) :
    (lambda2A4DualEquiv x : Lambda2A4Space) =
      (5 : ℝ)⁻¹ • lambda2A4Hodge (x : Lambda2A4Space) := by
  let left : lambda2A4Lattice →ₗ[ℤ] Lambda2A4Space :=
    (lambda2A4Form.dualSubmodule lambda2A4Lattice).subtype.comp
      lambda2A4DualEquiv.toLinearMap
  let right : lambda2A4Lattice →ₗ[ℤ] Lambda2A4Space :=
    (((5 : ℝ)⁻¹ • lambda2A4Hodge).restrictScalars ℤ).comp
      lambda2A4Lattice.subtype
  have heq : left = right := by
    apply lambda2A4IntegralBasis.ext
    intro i
    change (lambda2A4DualEquiv (lambda2A4IntegralBasis i) : Lambda2A4Space) =
      (5 : ℝ)⁻¹ • lambda2A4Hodge
        (lambda2A4IntegralBasis i : Lambda2A4Space)
    rw [lambda2A4DualEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]
    have hcoe :
        (lambda2A4IntegralBasis i : Lambda2A4Space) = lambda2A4Basis i := by
      exact lambda2A4Basis.restrictScalars_apply ℤ i
    rw [hcoe]
    exact lambda2A4DualIntegralBasis_eq_hodge i
  exact LinearMap.congr_fun heq x

/-- The concrete integral basis coerces to the fixed ordered wedge basis. -/
theorem lambda2A4SourceRealBasis_apply (i : Fin 6) :
    lambda2A4Basis i =
      (lambda2A4IntegralBasis i : Lambda2A4Space) :=
  (lambda2A4Basis.restrictScalars_apply ℤ i).symm

/-- The concrete real dual basis is the image of the integral basis under the fixed equivalence. -/
theorem lambda2A4DualRealBasis_apply (i : Fin 6) :
    lambda2A4DualRealBasis i =
      (lambda2A4DualEquiv (lambda2A4IntegralBasis i) : Lambda2A4Space) := by
  rw [lambda2A4DualEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact lambda2A4DualRealBasis_eq_integral i

/-- The Gram matrix of a real-valued bilinear lattice in a chosen integral basis. -/
noncomputable def latticeGram {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => B (b i : E) (b j : E)

/-- The determinant convention for an integral lattice is the determinant of
its Gram matrix in the displayed integral basis. -/
noncomputable def latticeDiscriminant {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L) : ℝ :=
  (latticeGram B L b).det

/-- `L1` and `L2` are similar with ratio `r` when a Z-linear equivalence scales
their ambient real-valued bilinear form by `r^2`. -/
def LatticeSimilarity {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (r : ℝ) (L1 L2 : Submodule ℤ E) : Prop :=
  ∃ e : L1 ≃ₗ[ℤ] L2, ∀ x y : L1,
    B (e x : E) (e y : E) = r ^ 2 * B (x : E) (y : E)

/-- The integral pairing matrix between the transported dual basis and the
source basis. In the source this is the unimodular matrix `U = GJ/5`. -/
noncomputable def latticePairingMatrix
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j => B (dualEquiv (b i) : E) (b j : E)

/-- The source's forcing sentence as one assertion: exact five-modular scaling
through the specified equivalence with the actual dual lattice forces the
rank-six discriminant. -/
def FiveModularityForcesDiscriminant
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L) : Prop :=
  (∀ x y : L,
      B (dualEquiv x : E) (dualEquiv y : E) = (1 / 5 : ℝ) * B x y) →
    latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2)

/-- Change of real basis identifies dual/source discriminant reciprocity with
the square of the integral pairing determinant. -/
theorem dual_discriminant_mul_source_eq_pairing_det_sq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L)
    (sourceRealBasis dualRealBasis : Module.Basis (Fin 6) ℝ E)
    (sourceRealBasis_apply : ∀ i, sourceRealBasis i = (b i : E))
    (dualRealBasis_apply : ∀ i,
      dualRealBasis i = (dualEquiv (b i) : E)) :
    latticeDiscriminant B (B.dualSubmodule L) (b.map dualEquiv) *
        latticeDiscriminant B L b =
      (latticePairingMatrix B L b dualEquiv).det ^ 2 := by
  classical
  have hsourceGram :
      latticeGram B L b = LinearMap.BilinForm.toMatrix sourceRealBasis B := by
    ext i j
    simp only [latticeGram, LinearMap.BilinForm.toMatrix_apply]
    rw [sourceRealBasis_apply i, sourceRealBasis_apply j]
  have hdualGram :
      latticeGram B (B.dualSubmodule L) (b.map dualEquiv) =
        LinearMap.BilinForm.toMatrix dualRealBasis B := by
    ext i j
    simp only [latticeGram, Module.Basis.map_apply,
      LinearMap.BilinForm.toMatrix_apply]
    rw [dualRealBasis_apply i, dualRealBasis_apply j]
  have hpairingMatrix :
      latticePairingMatrix B L b dualEquiv =
        Matrix.transpose (sourceRealBasis.toMatrix dualRealBasis) *
          LinearMap.BilinForm.toMatrix sourceRealBasis B := by
    ext i j
    simp only [latticePairingMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      LinearMap.BilinForm.toMatrix_apply]
    rw [← sourceRealBasis_apply j, ← dualRealBasis_apply i]
    calc
      B (dualRealBasis i) (sourceRealBasis j) =
          B (∑ k, sourceRealBasis.toMatrix dualRealBasis k i •
            sourceRealBasis k) (sourceRealBasis j) := by
        rw [sourceRealBasis.sum_toMatrix_smul_self dualRealBasis i]
      _ = ∑ k, sourceRealBasis.toMatrix dualRealBasis k i *
          B (sourceRealBasis k) (sourceRealBasis j) := by
        simp only [map_sum, LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
  have hdualChange :
      Matrix.transpose (sourceRealBasis.toMatrix dualRealBasis) *
          LinearMap.BilinForm.toMatrix sourceRealBasis B *
          sourceRealBasis.toMatrix dualRealBasis =
        LinearMap.BilinForm.toMatrix dualRealBasis B :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      sourceRealBasis dualRealBasis B
  have hdualDet :
      (LinearMap.BilinForm.toMatrix dualRealBasis B).det =
        (sourceRealBasis.toMatrix dualRealBasis).det ^ 2 *
          (LinearMap.BilinForm.toMatrix sourceRealBasis B).det := by
    rw [← hdualChange, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hpairingDet :
      (latticePairingMatrix B L b dualEquiv).det =
        (sourceRealBasis.toMatrix dualRealBasis).det *
          (LinearMap.BilinForm.toMatrix sourceRealBasis B).det := by
    rw [hpairingMatrix, Matrix.det_mul, Matrix.det_transpose]
  change
    (latticeGram B (B.dualSubmodule L) (b.map dualEquiv)).det *
        (latticeGram B L b).det =
      (latticePairingMatrix B L b dualEquiv).det ^ 2
  rw [hdualGram, hsourceGram, hdualDet, hpairingDet]
  ring

/-- Rank-six scaling by `1/5`, dual reciprocity, and positivity select the
positive discriminant `5^(6/2)`. -/
theorem rankSixFiveModular_discriminant_forced
    (source dual : ℝ) (hsource : 0 < source)
    (hscale : dual = (1 / 5 : ℝ) ^ 6 * source)
    (hreciprocal : dual * source = 1) :
    source = (5 : ℝ) ^ (6 / 2) := by
  norm_num at hscale ⊢
  rw [hscale] at hreciprocal
  nlinarith [sq_nonneg (source - 125)]

/-- Generic proof engine for the six five-modularity conclusions from exact
Hodge, dual-basis, unimodularity, and positivity certificates. -/
private theorem lambda2A4_five_modularity_of_certificates
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (J : E →ₗ[ℝ] E)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L)
    (dualEquiv_apply : ∀ x : L,
      (dualEquiv x : E) = (5 : ℝ)⁻¹ • J (x : E))
    (hodge_similitude : ∀ x y : E, B (J x) (J y) = 5 * B x y)
    (sourceRealBasis dualRealBasis : Module.Basis (Fin 6) ℝ E)
    (sourceRealBasis_apply : ∀ i, sourceRealBasis i = (b i : E))
    (dualRealBasis_apply : ∀ i,
      dualRealBasis i = (dualEquiv (b i) : E))
    (dualPairing_det :
      (latticePairingMatrix B L b dualEquiv).det = (-1 : ℝ))
    (source_discriminant_pos : 0 < latticeDiscriminant B L b) :
    LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
      Module.finrank ℤ L = 6 ∧
      LatticeSimilarity B (Real.sqrt 5) (B.dualSubmodule L) L ∧
      latticeDiscriminant B L b = (5 : ℝ) ^ 3 ∧
      latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2) ∧
      FiveModularityForcesDiscriminant B L b dualEquiv := by
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsmall_sq : (1 / Real.sqrt 5) ^ 2 = (1 / 5 : ℝ) := by
    rw [div_pow, one_pow, hsqrt_sq]
  have hforward_apply : ∀ x y : L,
      B (dualEquiv x : E) (dualEquiv y : E) =
        (1 / Real.sqrt 5) ^ 2 * B (x : E) (y : E) := by
    intro x y
    rw [dualEquiv_apply x, dualEquiv_apply y]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hodge_similitude]
    rw [hsmall_sq]
    ring_nf
  have hforward : LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) :=
    ⟨dualEquiv, hforward_apply⟩
  have hreverse : LatticeSimilarity B (Real.sqrt 5) (B.dualSubmodule L) L := by
    refine ⟨dualEquiv.symm, ?_⟩
    intro x y
    have h := hforward_apply (dualEquiv.symm x) (dualEquiv.symm y)
    simp only [dualEquiv.apply_symm_apply] at h
    rw [hsmall_sq] at h
    rw [hsqrt_sq]
    linarith
  letI : Module.Free ℤ L := Module.Free.of_basis b
  letI : Module.Finite ℤ L := Module.Finite.of_basis b
  have hrank : Module.finrank ℤ L = 6 := by
    rw [Module.finrank_eq_card_basis b]
    norm_num
  have hdualReciprocal :
      latticeDiscriminant B (B.dualSubmodule L) (b.map dualEquiv) *
        latticeDiscriminant B L b = 1 := by
    rw [dual_discriminant_mul_source_eq_pairing_det_sq B L b dualEquiv
      sourceRealBasis dualRealBasis sourceRealBasis_apply dualRealBasis_apply,
      dualPairing_det]
    norm_num
  have hforcing : FiveModularityForcesDiscriminant B L b dualEquiv := by
    intro hfiveScaling
    have hdualGram :
        latticeGram B (B.dualSubmodule L) (b.map dualEquiv) =
          (1 / 5 : ℝ) • latticeGram B L b := by
      ext i j
      simp only [latticeGram, Module.Basis.map_apply, Matrix.smul_apply, smul_eq_mul]
      rw [hfiveScaling]
    have hdualDiscriminant :
        latticeDiscriminant B (B.dualSubmodule L) (b.map dualEquiv) =
          (1 / 5 : ℝ) ^ 6 * latticeDiscriminant B L b := by
      change (latticeGram B (B.dualSubmodule L) (b.map dualEquiv)).det =
        (1 / 5 : ℝ) ^ 6 * (latticeGram B L b).det
      rw [hdualGram, Matrix.det_smul]
      norm_num
    exact rankSixFiveModular_discriminant_forced
      (latticeDiscriminant B L b)
      (latticeDiscriminant B (B.dualSubmodule L) (b.map dualEquiv))
      source_discriminant_pos hdualDiscriminant hdualReciprocal
  have hfiveScaling : ∀ x y : L,
      B (dualEquiv x : E) (dualEquiv y : E) = (1 / 5 : ℝ) * B x y := by
    intro x y
    rw [hforward_apply, hsmall_sq]
  have hforced := hforcing hfiveScaling
  have hdisc : latticeDiscriminant B L b = (5 : ℝ) ^ 3 := by
    norm_num at hforced ⊢
    exact hforced
  exact ⟨hforward, hrank, hreverse, hdisc, hforced, hforcing⟩

/-- The fixed wedge basis has exactly the source Gram matrix. -/
theorem lambda2A4_latticeGram :
    latticeGram lambda2A4Form lambda2A4Lattice lambda2A4IntegralBasis =
      lambda2A4Gram := by
  ext i j
  change lambda2A4Form
    (lambda2A4IntegralBasis i : Lambda2A4Space)
    (lambda2A4IntegralBasis j : Lambda2A4Space) = lambda2A4Gram i j
  rw [← lambda2A4SourceRealBasis_apply i, ← lambda2A4SourceRealBasis_apply j]
  have h := congrFun (congrFun
    (LinearMap.BilinForm.toMatrix_toBilin lambda2A4Basis lambda2A4Gram) i) j
  simpa only [lambda2A4Form, LinearMap.BilinForm.toMatrix_apply] using h

/-- The fixed dual/source pairing matrix is the source matrix `U`. -/
theorem lambda2A4_latticePairingMatrix :
    latticePairingMatrix lambda2A4Form lambda2A4Lattice
      lambda2A4IntegralBasis lambda2A4DualEquiv =
        lambda2A4UnimodularMatrix := by
  ext i j
  change lambda2A4Form
    (lambda2A4DualEquiv (lambda2A4IntegralBasis i) : Lambda2A4Space)
    (lambda2A4IntegralBasis j : Lambda2A4Space) = lambda2A4UnimodularMatrix i j
  rw [lambda2A4DualEquiv, Module.Basis.equiv_apply, Equiv.refl_apply,
    ← lambda2A4SourceRealBasis_apply j]
  exact lambda2A4DualIntegralBasis_pairing i j

/-- The determinant of the fixed dual/source pairing matrix is `-1`. -/
theorem lambda2A4_latticePairingMatrix_det :
    (latticePairingMatrix lambda2A4Form lambda2A4Lattice
      lambda2A4IntegralBasis lambda2A4DualEquiv).det = (-1 : ℝ) := by
  rw [lambda2A4_latticePairingMatrix, lambda2A4UnimodularMatrix,
    ← Int.cast_det, lambda2A4UnimodularMatrixInt_det]
  norm_num

/-- The concrete discriminant is positive. -/
theorem lambda2A4_latticeDiscriminant_pos :
    0 < latticeDiscriminant lambda2A4Form lambda2A4Lattice
      lambda2A4IntegralBasis := by
  rw [latticeDiscriminant, lambda2A4_latticeGram, lambda2A4Gram_det]
  norm_num

/-- OACTC theorem 39.2 for the concrete exterior-square `A4` lattice,
its fixed ordered wedge basis, fixed Hodge operator, and actual bilinear dual. -/
theorem lambda2A4_five_modularity :
    LatticeSimilarity lambda2A4Form (1 / Real.sqrt 5) lambda2A4Lattice
        (lambda2A4Form.dualSubmodule lambda2A4Lattice) ∧
      Module.finrank ℤ lambda2A4Lattice = 6 ∧
      LatticeSimilarity lambda2A4Form (Real.sqrt 5)
        (lambda2A4Form.dualSubmodule lambda2A4Lattice) lambda2A4Lattice ∧
      latticeDiscriminant lambda2A4Form lambda2A4Lattice
        lambda2A4IntegralBasis = (5 : ℝ) ^ 3 ∧
      latticeDiscriminant lambda2A4Form lambda2A4Lattice
        lambda2A4IntegralBasis = (5 : ℝ) ^ (6 / 2) ∧
      FiveModularityForcesDiscriminant lambda2A4Form lambda2A4Lattice
        lambda2A4IntegralBasis lambda2A4DualEquiv := by
  exact lambda2A4_five_modularity_of_certificates
    lambda2A4Form lambda2A4Lattice lambda2A4IntegralBasis lambda2A4Hodge
    lambda2A4DualEquiv lambda2A4DualEquiv_apply lambda2A4_hodge_similitude
    lambda2A4Basis lambda2A4DualRealBasis lambda2A4SourceRealBasis_apply
    lambda2A4DualRealBasis_apply lambda2A4_latticePairingMatrix_det
    lambda2A4_latticeDiscriminant_pos

/- Reverse probe (CAS-A1/A4/A6): the closed public proposition projects the
actual dual-lattice similarity, non-unit discriminant, and forcing implication. -/
example
    (conclusion :
      LatticeSimilarity lambda2A4Form (1 / Real.sqrt 5) lambda2A4Lattice
          (lambda2A4Form.dualSubmodule lambda2A4Lattice) ∧
        Module.finrank ℤ lambda2A4Lattice = 6 ∧
        LatticeSimilarity lambda2A4Form (Real.sqrt 5)
          (lambda2A4Form.dualSubmodule lambda2A4Lattice) lambda2A4Lattice ∧
        latticeDiscriminant lambda2A4Form lambda2A4Lattice
          lambda2A4IntegralBasis = (5 : ℝ) ^ 3 ∧
        latticeDiscriminant lambda2A4Form lambda2A4Lattice
          lambda2A4IntegralBasis = (5 : ℝ) ^ (6 / 2) ∧
        FiveModularityForcesDiscriminant lambda2A4Form lambda2A4Lattice
          lambda2A4IntegralBasis lambda2A4DualEquiv) :
    LatticeSimilarity lambda2A4Form (1 / Real.sqrt 5) lambda2A4Lattice
        (lambda2A4Form.dualSubmodule lambda2A4Lattice) ∧
      latticeDiscriminant lambda2A4Form lambda2A4Lattice
        lambda2A4IntegralBasis = 125 ∧
      FiveModularityForcesDiscriminant lambda2A4Form lambda2A4Lattice
        lambda2A4IntegralBasis lambda2A4DualEquiv := by
  refine ⟨conclusion.1, ?_, conclusion.2.2.2.2.2⟩
  have hdisc := conclusion.2.2.2.1
  norm_num at hdisc ⊢
  exact hdisc

/- Trivialization probe (CAS-A1/A3): on the fixed exterior-square carrier,
replacing the source form by zero contradicts its displayed Gram matrix. -/
example :
    latticeGram (0 : LinearMap.BilinForm ℝ Lambda2A4Space)
      lambda2A4Lattice lambda2A4IntegralBasis ≠ lambda2A4Gram := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 6)) (0 : Fin 6)
  norm_num [latticeGram, lambda2A4Gram, lambda2A4GramInt] at h00

/- Direction probe (CAS-A6 -> CAS-A5): the concrete forcing leaf consumes
exact modular scaling and yields the final discriminant. Its proof above uses
dual reciprocity and positivity, not the precomputed Gram determinant. -/
example
    (hscale : ∀ x y : lambda2A4Lattice,
      lambda2A4Form (lambda2A4DualEquiv x : Lambda2A4Space)
          (lambda2A4DualEquiv y : Lambda2A4Space) =
        (1 / 5 : ℝ) * lambda2A4Form x y) :
    latticeDiscriminant lambda2A4Form lambda2A4Lattice
      lambda2A4IntegralBasis = (5 : ℝ) ^ (6 / 2) :=
  lambda2A4_five_modularity.2.2.2.2.2 hscale

#print axioms lambda2A4_five_modularity

end D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity
