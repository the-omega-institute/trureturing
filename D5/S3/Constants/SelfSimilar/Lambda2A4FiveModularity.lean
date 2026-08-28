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

private theorem lambda2A4GramInt_det : lambda2A4GramInt.det = 125 := by
  set_option maxRecDepth 100000 in
    decide

private theorem lambda2A4Gram_det : lambda2A4Gram.det = (5 : ℝ) ^ 3 := by
  rw [lambda2A4Gram, ← Int.cast_det, lambda2A4GramInt_det]
  norm_num

/-- OACTC five-modularity for `Lambda^2 A4`.

The hypotheses are precisely the data fixed immediately before the source
theorem: its six-element integral basis and Gram matrix, the integral Hodge
operator, the exact formula `L# = (J/5)L`, and `J^T G J = 5G`. The conclusion
keeps both displayed similarities, the six-dimensional assertion, and both
displayed forms of the discriminant identity as separate conjuncts. -/
theorem lambda2A4_five_modularity
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (hGram : latticeGram B L b = lambda2A4Gram)
    (J : E →ₗ[ℝ] E)
    (dualEquiv : L ≃ₗ[ℤ] B.dualSubmodule L)
    (dualEquiv_apply : ∀ x : L,
      (dualEquiv x : E) = (5 : ℝ)⁻¹ • J (x : E))
    (hodge_similitude : ∀ x y : E, B (J x) (J y) = 5 * B x y) :
    LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
      Module.finrank ℤ L = 6 ∧
      LatticeSimilarity B (Real.sqrt 5) (B.dualSubmodule L) L ∧
      latticeDiscriminant B L b = (5 : ℝ) ^ 3 ∧
      latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2) := by
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
  have hdisc : latticeDiscriminant B L b = (5 : ℝ) ^ 3 := by
    rw [latticeDiscriminant, hGram, lambda2A4Gram_det]
  refine ⟨hforward, hrank, hreverse, hdisc, ?_⟩
  norm_num at hdisc ⊢
  exact hdisc

/- Reverse probe: the public proposition recovers both the non-numerical
dual-lattice similarity and the non-unit discriminant. -/
example
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (L : Submodule ℤ E)
    (b : Module.Basis (Fin 6) ℤ L)
    (conclusion :
      LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
        Module.finrank ℤ L = 6 ∧
        LatticeSimilarity B (Real.sqrt 5) (B.dualSubmodule L) L ∧
        latticeDiscriminant B L b = (5 : ℝ) ^ 3 ∧
        latticeDiscriminant B L b = (5 : ℝ) ^ (6 / 2)) :
    LatticeSimilarity B (1 / Real.sqrt 5) L (B.dualSubmodule L) ∧
      latticeDiscriminant B L b = 125 := by
  refine ⟨conclusion.1, ?_⟩
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

#print axioms lambda2A4_five_modularity

end D5.S3.Constants.SelfSimilar.Lambda2A4FiveModularity
