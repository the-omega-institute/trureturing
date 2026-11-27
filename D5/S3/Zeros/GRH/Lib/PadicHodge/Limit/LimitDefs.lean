/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Limit/LimitDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Limit/LimitDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Limit.LimitDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Limit/LimitDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.HodgeTateFrame
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Limits of crystalline representations with bounded weights are crystalline (known
result; see Lib.PadicHodge.Limit.LocalLimit).

This file: A_max periods embed in B_max periods; crystalline with weights in [0,h]; bundled
representations. -/


open TensorProduct Module
variable {p} [ThePrime p] {Γ T R : Type} [Group Γ] [OverGp Γ p] [AddCommGroup T] [Module ℤ_[p] T]
  [CommRing R] [Module R T] [Algebra ℤ_[p] R] [IsScalarTower ℤ_[p] R T]

lemma periodTensorMap_injective [Flat ℤ_[p] T] : (periodTensorMap _ _ .id : Amax ⊗[_] T →
  Bcris ⊗ T).Injective := Flat.rTensor_preserves_injective_linearMap (Algebra.algHom ..).toLinearMap
  (injective_BPlus_Bcris.comp injective_Amax_BPlus)

/-- The representation is crystalline and all its Hodge–Tate jumps, at every γ: R → C_p, lie in
[0, h]. -/
def IsCrystallineUpTo (h : ℕ) (ρ : Representation R Γ T) := IsCrystalline ρ ∧ ∀ γ k,
  jump ρ γ k ≠ 0 → 0 ≤ k ∧ k ≤ h

/-- A representation of Γ over Q̄_p of some finite dimension: a finite index type m with a group
homomorphism r from Γ to GL_m(Q̄_p), with no continuity required. -/
structure PadicRep Γ [Group Γ] p [ThePrime p] where
  {Index : Type} [fintypeIndex : Fintype Index] (rep : Γ →* GL Index (PadicAlgCl p))

attribute [instance] PadicRep.fintypeIndex

/-- For a Z_p-linear map u from T to square matrices over Q̄_p and a vector v, the Z_p-linear
map sending x to u(x)v. -/
noncomputable abbrev applyVec {m} [Fintype m] (u : T →ₗ[ℤ_[p]] Matrix m m (PadicAlgCl p)) v :=
  (Matrix.mulVecBilin _ ℤ_[p]).flip v ∘ₗ u
