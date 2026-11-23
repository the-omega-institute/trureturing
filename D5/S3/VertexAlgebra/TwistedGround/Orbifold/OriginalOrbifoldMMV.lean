/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldMMV
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldMMV
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original two-twisted-source Borcherds identity with fixed third input. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMMSkew
import D5.S3.VertexAlgebra.StateField.SkewSymmetry
import Batteries.Tactic.OpenPrivate

/-!
The last-input permutation uses mixed skew on the input pair, fixed skew on
the fixed iterate, and original two-twisted-input skew on the reverse iterate.
This takes the defect to the established twisted-fixed-twisted order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution HalfFock.LatticeHalfFockParityField
open OriginalOrbifoldField OriginalOrbifoldTranslation
open OriginalFourMChargeCoset (originalI)
open StateField.BorcherdsPermutations
open StateFieldResidueReconstruction (epsilon)
open private mode_vv mode_mv mode_mm truncation sum_v smul_v from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi

variable {D : LatticeData} {hu : IsUnit D.G.det}
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

local notation "μ" => modesOfStateField (Y D hu hD)
local notation "τ" => T D hu
local notation "V₀" => FixedCarrier D
local notation "M₀" => paritySpace D hu (-1)
local notation "vIn" => (LinearMap.inl ℂ V₀ M₀)
local notation "mIn" => (LinearMap.inr ℂ V₀ M₀)

private theorem pow_v (j : ℕ) (a : V₀) :
    (τ ^ j) (vIn a : Carrier D hu) = vIn ((fixedTranslation D ^ j) a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    change (fixedTranslation D ((fixedTranslation D ^ j) a),
      MixedIntertwiner.translation D hu 0) =
      (fixedTranslation D ((fixedTranslation D ^ j) a), (0 : M₀))
    rw [map_zero]

private theorem skew_vv (a b : V₀) : SkewAt μ τ (vIn a) (vIn b) := by
  intro n
  have h := ((StateField.SkewSymmetry.skew_symmetry
    (fixed_actualVertexAlgebra D) a b).1 n).2
  change ((fixedField D a)[[n]]) b = ∑ᶠ j : ℕ,
    (epsilon (n + j + 1) / (j.factorial : ℂ)) •
      (fixedTranslation D ^ j) (((fixedField D b)[[n+j]]) a) at h
  simp only [fixedField_ncoeff] at h
  simp only [mode_vv, dividedTranslation, LinearMap.smul_apply, pow_v, smul_smul, smul_v,
    ← div_eq_mul_inv, ← sum_v]
  exact congrArg (vIn : V₀ →ₗ[ℂ] Carrier D hu) h

private theorem skew_mm (h24 : D.rank = 24) (u v : M₀) :
    SkewAt μ τ (mIn u) (mIn v) := by
  intro n
  simp only [mode_mm, dividedTranslation, LinearMap.smul_apply, pow_v, smul_smul, smul_v,
    ← div_eq_mul_inv, ← sum_v]
  exact congrArg (vIn : V₀ →ₗ[ℂ] Carrier D hu)
    (OriginalMMSkew.originalI_skew D hu hD h24 n u v)

/-- The MMV defect vanishes for the literal assembled original field. -/
theorem defect_mmv (h24 : D.rank = 24) (u v : M₀) (a : V₀) (p q r : ℤ) :
    defect μ (mIn u) (mIn v) (vIn a) p q r = 0 := by
  have law := (defect_swap_last μ (truncation hD) (mIn u) (mIn v) (vIn a)
    p q r (divided_mode_translation hD h24 _) (skew_mv hD v a)
    (fun i => by rw [mode_mm]; exact skew_vv hD _ a)
    (fun i => by rw [mode_mv]; exact skew_mm hD h24 v _)).2
  rw [law]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [defect_mvm hD h24 u a v, map_zero]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
