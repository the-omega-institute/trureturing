/- GID: D5/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeDualCosetFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized full-Hahn additive fusion is linearly equivalent to complex scalars. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetFusionRigidity

/-!
The identity cross block specializes the complete canonical Hahn field to
the literal additive-target full-law operator space. Ground evaluation is
the scalar coordinate for arbitrary rational solutions of the two original
Gram equations. Both the old and external ranks may be zero.

This combines the canonical existence and full-law rigidity suppliers in
the conventions of Bakalov--Kac, math/0402315v1, section 4.1. Native residue
and conformal suppliers retain their Carnahan and Kytölä attributions.
There is no categorical, physical, or string-completion assertion.

proof_shape: canonical_lawful, shift_eq_groundPower,
canonical_groundEvaluation, canonical_mode, dualVector_eq, scalarInclusion_injective:
bind-only, consumed helpers of the exact scalar equivalence construction.
consumers: canonical_mode -> canonical_lawful;
canonical_lawful -> canonicalOperator;
dualVector_eq -> shift_eq_groundPower;
shift_eq_groundPower -> canonical_groundEvaluation;
canonicalOperator -> scalarInclusion, canonical_groundEvaluation;
canonical_groundEvaluation -> scalarEquiv (left inverse);
scalarInclusion_injective -> scalarEquiv (right inverse).
escape_witness: The live full-law content is supplied by the co-delivered
canonical projection_translation, translation_injection, mixed_jacobi and
derivative proofs, on the full ambient and original carriers. This adapter
and the inverse-Gram normalization do not claim independent new mathematics.
admission_basis: co-delivered escape-witness content; exact integration.

-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeDualCosetFusion

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeDualCosetConformal LatticeDualCosetEnergy
open LatticeDualCosetIntertwiner LatticeCosetCompression LatticeDiscriminantTheta
open scoped BigOperators VertexOperator Matrix
noncomputable section

open private shift_pair from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws
open private rat_unit pairRaw_symm from
  D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

variable (D : LatticeData) (hD : (gramReal D).PosDef) (a b : Charge D)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (μ ν : Fin D.rank → ℚ)
variable (ha : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (a i : ℚ))
variable (hb : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = (b i : ℚ))

private theorem canonical_mode (u : Carrier D) (τ : ℚ) :
    mode (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) u τ =
      LatticeCosetCanonicalIntertwiner.mode D (1 : Matrix _ _ ℤ) a b u τ := rfl

include hD hHG hGH in
/-- The actual canonical field obeys exactly the original full laws. -/
theorem canonical_lawful :
    Lawful D a b H (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) where
  source u τ := by
    apply LinearMap.ext
    intro v
    simpa only [Matrix.one_mulVec, canonical_mode, LinearMap.smul_apply] using
      LatticeCosetCanonicalIntertwiner.source_derivative D (1 : Matrix _ _ ℤ) hD H hHG hGH a b u v τ
  target u τ := by
    apply LinearMap.ext
    intro v
    simpa only [Matrix.one_mulVec, canonical_mode, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.smul_apply] using
      LatticeCosetCanonicalIntertwiner.target_derivative D (1 : Matrix _ _ ℤ) hD H hHG hGH a b u v τ
  jacobi h u v p r τ := by
    have hL (i : ℕ) : leftTerm D a
        (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) h u v p r τ i =
        LatticeCosetCanonicalIntertwiner.mixedLeft D (1 : Matrix _ _ ℤ) a b h u v p r τ i := by
      dsimp only [leftTerm, LatticeCosetCanonicalIntertwiner.mixedLeft]
      rw [Matrix.one_mulVec, canonical_mode]
    have hF (i : ℕ) : firstTerm D a b
        (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) h u v p r τ i =
        LatticeCosetCanonicalIntertwiner.mixedFirst D (1 : Matrix _ _ ℤ) a b h u v p r τ i := by
      dsimp only [firstTerm, LatticeCosetCanonicalIntertwiner.mixedFirst]
      rw [Matrix.one_mulVec, Matrix.one_mulVec, canonical_mode]
    have hS (i : ℕ) : secondTerm D b
        (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) h u v p r τ i =
        LatticeCosetCanonicalIntertwiner.mixedSecond D (1 : Matrix _ _ ℤ) a b h u v p r τ i := by
      dsimp only [secondTerm, LatticeCosetCanonicalIntertwiner.mixedSecond,
        StateFieldResidueReconstruction.epsilon]
      rw [Matrix.one_mulVec, canonical_mode]
    have hJ := LatticeCosetCanonicalIntertwiner.mixed_jacobi D
      (1 : Matrix _ _ ℤ) hD a b h u v p r τ
    rw [← funext hL, ← funext hF, ← funext hS] at hJ
    exact hJ

/-- A member of the exact lawful submodule, with no added predicates. -/
def canonicalOperator : operatorSpace D a b H :=
  ⟨LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b,
    canonical_lawful D hD a b H hHG hGH⟩

include hD in
private theorem dualVector_eq (c : Charge D) (x : Fin D.rank → ℚ)
    (hx : ∀ i, ∑ j, (D.G i j : ℚ) * x j = (c i : ℚ)) :
    dualVector D c = x := by
  have hc : (fun i => (c i : ℚ)) = gramRat D *ᵥ x := by
    funext i
    exact (hx i).symm
  letI : Invertible (gramRat D) :=
    Matrix.invertibleOfIsUnitDet (gramRat D) (rat_unit D hD)
  change (gramRat D)⁻¹ *ᵥ (fun i => (c i : ℚ)) = x
  exact Matrix.inv_mulVec_eq_vec hc

include hD ha hb in
/-- The canonical offset is the raw power used by the original ground evaluation. -/
theorem shift_eq_groundPower :
    LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) a b = groundPower D μ ν 0 0 := by
  rw [shift_pair, Matrix.one_mulVec, Matrix.one_mulVec, pairRaw_symm,
    pairRaw, dualVector_eq D hD a μ ha]
  simp only [groundPower, Pi.zero_apply, Int.cast_zero, zero_add, dotProduct]
  simp only [LatticeDualCosetEnergy.pairing, ← Finset.mul_sum, mul_assoc, hb]

include ha hb in
/-- The exact groundEvaluation coordinate of the lawful canonical member is one. -/
theorem canonical_groundEvaluation :
    groundEvaluation D a b H μ ν (canonicalOperator D hD a b H hHG hGH) = 1 := by
  change groundScalar D
    (LatticeCosetCanonicalIntertwiner.intertwiner D (1 : Matrix _ _ ℤ) a b) μ ν 0 0 = 1
  unfold groundScalar
  rw [← shift_eq_groundPower D hD a b μ ν ha hb]
  simpa only [ground, vacuum, zero_add, MvPolynomial.constantCoeff_eq] using
    LatticeCosetCanonicalIntertwiner.ground_scalar D (1 : Matrix _ _ ℤ) a b

/-- Scalar multiplication of the normalized canonical field in the actual lawful space. -/
def scalarInclusion : ℂ →ₗ[ℂ] operatorSpace D a b H :=
  LinearMap.toSpanSingleton ℂ _ (canonicalOperator D hD a b H hHG hGH)

private theorem scalarInclusion_injective :
    Function.Injective (scalarInclusion D hD a b H hHG hGH) := by
  apply smul_left_injective ℂ
  intro hz
  apply LatticeCosetCanonicalIntertwiner.intertwiner_ne_zero D (1 : Matrix _ _ ℤ) a b
  exact congrArg Subtype.val hz

/-- Ground evaluation is the linear equivalence; its inverse is scalar inclusion. -/
def scalarEquiv : operatorSpace D a b H ≃ₗ[ℂ] ℂ := by
  let f := scalarInclusion D hD a b H hHG hGH
  let g := groundEvaluation D a b H μ ν
  have left (J : operatorSpace D a b H) : f (g J) = J := by
    apply groundEvaluation_injective D a b H hHG hGH μ ν ha hb
    change g (g J • canonicalOperator D hD a b H hHG hGH) = g J
    rw [map_smul, canonical_groundEvaluation D hD a b H hHG hGH μ ν ha hb]
    simp
  exact {
    toLinearMap := g
    invFun := f
    left_inv := left
    right_inv := fun z => scalarInclusion_injective D hD a b H hHG hGH (left (f z)) }

end
end D5.S3.VertexAlgebra.LatticeDualCosetFusion
