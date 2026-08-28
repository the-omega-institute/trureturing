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

/-- OACTC five-modularity for `Lambda^2 A4`.

The hypotheses are the data fixed immediately before the source theorem: its
integral and real bases, Gram matrix, integral Hodge operator, exact formula
`L# = (J/5)L`, unimodular pairing matrix `U`, and `J^T G J = 5G`. The six
conclusions retain both similarities, rank, both discriminant displays, and the
forcing implication. -/
theorem lambda2A4_five_modularity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (hGram : latticeGram B L b = lambda2A4Gram)
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

/- Reverse probe (CAS-A1/A4/A6): the public proposition projects the actual
dual-lattice similarity, non-unit discriminant, and forcing implication. -/
example
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L)
    (conclusion :
      LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
        Module.finrank ℤ L = 6 ∧
        LatticeSimilarity B (Real.sqrt 5) (B.dualSubmodule L) L ∧
        latticeDiscriminant B L b = (5 : ℝ) ^ 3 ∧
        latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2) ∧
        FiveModularityForcesDiscriminant B L b dualEquiv) :
    LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
      latticeDiscriminant B L b = 125 ∧
      FiveModularityForcesDiscriminant B L b dualEquiv := by
  refine ⟨conclusion.1, ?_, conclusion.2.2.2.2.2⟩
  have hdisc := conclusion.2.2.2.1
  norm_num at hdisc ⊢
  exact hdisc

/- Trivialization probe: replacing the source Gram form by zero contradicts
the displayed Gram certificate, so the zero pairing cannot inhabit the type. -/
example
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : Submodule ℤ E) (b : Module.Basis (Fin 6) ℤ L) :
    latticeGram (0 : LinearMap.BilinForm ℝ E) L b ≠ lambda2A4Gram := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 6)) (0 : Fin 6)
  norm_num [latticeGram, lambda2A4Gram, lambda2A4GramInt] at h00

/- Direction probe (CAS-A6 -> CAS-A5): exact modular scaling, the two real
bases, unimodular pairing, and positivity force the final discriminant. There
is deliberately no fixed Gram matrix or precomputed determinant premise. -/
example
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L)
    (sourceRealBasis dualRealBasis : Module.Basis (Fin 6) ℝ E)
    (sourceRealBasis_apply : ∀ i, sourceRealBasis i = (b i : E))
    (dualRealBasis_apply : ∀ i,
      dualRealBasis i = (dualEquiv (b i) : E))
    (dualPairing_det :
      (latticePairingMatrix B L b dualEquiv).det = (-1 : ℝ))
    (source_discriminant_pos : 0 < latticeDiscriminant B L b)
    (hscale : ∀ x y : L,
      B (dualEquiv x : E) (dualEquiv y : E) = (1 / 5 : ℝ) * B x y) :
    latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2) := by
  have hreciprocal :
      latticeDiscriminant B (B.dualSubmodule L) (b.map dualEquiv) *
        latticeDiscriminant B L b = 1 := by
    rw [dual_discriminant_mul_source_eq_pairing_det_sq B L b dualEquiv
      sourceRealBasis dualRealBasis sourceRealBasis_apply dualRealBasis_apply,
      dualPairing_det]
    norm_num
  have hdualGram :
      latticeGram B (B.dualSubmodule L) (b.map dualEquiv) =
        (1 / 5 : ℝ) • latticeGram B L b := by
    ext i j
    simp only [latticeGram, Module.Basis.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hscale]
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
    source_discriminant_pos hdualDiscriminant hreciprocal

#print axioms lambda2A4_five_modularity

end D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity
