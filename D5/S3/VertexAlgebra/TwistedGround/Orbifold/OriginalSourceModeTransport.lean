/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original fixed source mode under the graded BPZ duality. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients
import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose

/-! The inverse of the fixed-grade pairing carries the actual opposite action
to the ordinary source field mode. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy LatticeInvolution
open SourceBPZ.OriginalSourcePairing SourceBPZ.AllStateTranspose
open HalfFock.LatticeHalfFockParityField
open OriginalFourMChargeCoset (originalI)
open private sourceGradePairingEquiv sourceGradePairingEquiv_evaluation from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private oppositePull originalL1 from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private fixedSourceInclusion fixed_source_expansion mixedMode mixedLeftTerm
  mixedFirstTerm mixedSecondTerm mixed_families_finite mixed_residual_zero
  mixed_residual_expansion from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite

/-- The induced opposite action on each full grade dual is conjugate to the
original lattice field mode via the unchanged fixed-grade BPZ pairing. -/
theorem source_mode_of_oppositeDual (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (d m e : ℤ)
    (a : fixedGrade D d) (f : Module.Dual ℂ (fixedGrade D e)) :
    ((sourceGradePairingEquiv D hu hD (e + d - m - 1)).symm
      (oppositeDualMode D hu hD d m a e f)).val =
      ((Y D a.val)[[m]]) ((sourceGradePairingEquiv D hu hD e).symm f).val := by
  classical
  let E := sourceGradePairingEquiv D hu hD (e + d - m - 1)
  let x := (sourceGradePairingEquiv D hu hD e).symm f
  let mode := ((Y D a.val)[[m]]) x.val
  have hm : mode ∈ grade D (e + d - m - 1) := by
    simpa only [mode, add_comm d e] using
      positive_actual_mode_grade D hD d e m a.val x.val a.property.1 x.property.1
  let y : fixedGrade D (e + d - m - 1) :=
    ⟨mode, hm, fixed_mode_closed D a.val x.val a.property.2 x.property.2 m⟩
  have hy : E.symm (oppositeDualMode D hu hD d m a e f) = y := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    ext b
    change f (oppositePull D hu hD d m a e b) = E y b
    have he : E y b = sourcePairing D y.val b.val := by
      simpa only [E, LinearEquiv.symm_apply_apply] using
        (sourceGradePairingEquiv_evaluation D hu hD _ (E y) b).symm
    rw [he, ← sourceGradePairingEquiv_evaluation D hu hD e f]
    have bpz := sourcePairing_allState D hu d m a.val a.property.1 x.val b.val
    change sourcePairing D x.val
      (oppositeMode D hu hD d m a (e + d - m - 1) b).val =
        sourcePairing D (((Y D a.val)[[m]]) x.val) b.val
    rw [bpz]
    simp only [oppositeMode, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
      smul_eq_mul, div_eq_mul_inv,
      Finset.mul_sum, originalL1, mul_assoc]
  exact congrArg Subtype.val hy

private def restoreFixedSource (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FixedRestrictedDual D →ₗ[ℂ] FixedCarrier D :=
  DirectSum.toModule ℂ ℤ (FixedCarrier D) (fun e =>
    (Submodule.inclusion (show fixedGrade D e ≤ fixedSpace D from inf_le_right)).comp
      (sourceGradePairingEquiv D hu hD e).symm.toLinearMap)

/-- A homogeneous source mode acts through the original inverse pairing on
every restricted dual of finite grade support. -/
theorem restore_fixed_source_opposite (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (d m : ℤ) (a : fixedGrade D d) :
    (restoreFixedSource D hu hD).comp
        (oppositeAction D hu hD m (⟨a.val, a.property.2⟩ : FixedCarrier D)) =
      (fixedMode D ⟨a.val, a.property.2⟩ m).comp (restoreFixedSource D hu hD) := by
  classical
  rw [oppositeAction_homogeneous D hu hD d m a]
  apply DirectSum.linearMap_ext
  intro e
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, oppositeHomogeneous, LinearMap.coe_mk,
    AddHom.coe_mk, DirectSum.toModule_lof, restoreFixedSource]
  apply Subtype.ext
  exact source_mode_of_oppositeDual D hu hD d m e a f

private theorem restore_opposite_action (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (m : ℤ)
    (a : FixedCarrier D) (f : FixedRestrictedDual D) :
    restoreFixedSource D hu hD (oppositeAction D hu hD m a f) =
      fixedMode D a m (restoreFixedSource D hu hD f) := by
  classical
  let eval : FixedCarrier D →ₗ[ℂ] FixedCarrier D := {
    toFun a := fixedMode D a m (restoreFixedSource D hu hD f)
    map_add' a b := by
      apply Subtype.ext
      change ((Y D (a.val + b.val))[[m]]) _ =
        ((Y D a.val)[[m]]) _ + ((Y D b.val)[[m]]) _
      simp only [map_add, Pi.add_apply, LinearMap.add_apply]
    map_smul' c a := by
      apply Subtype.ext
      change ((Y D (c • a.val))[[m]]) _ = c • ((Y D a.val)[[m]]) _
      simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, RingHom.id_apply] }
  change _ = eval a
  rw [← fixed_source_expansion D hu a]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d _
  exact LinearMap.congr_fun (restore_fixed_source_opposite D hu hD d m
    (fixedProjection D hu d a)) f

/-- The mixed coefficient Jacobi law with one fixed input and two twisted
inputs, valued in the original fixed lattice sector via its original inverse. -/
theorem original_mixed_jacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (a : FixedCarrier D) (u v : paritySpace D hu (-1)) :
    (∑ᶠ j : ℕ, Ring.choose (m : ℂ) j •
      originalI D hu hD (m + n - (j : ℤ))
        (((fixedParitySlice D hu (-1) a)[[r + (j : ℤ)]]) u) v) =
    (∑ᶠ j : ℕ, ((-1 : ℂ)^j * Ring.choose (r : ℂ) j) •
      fixedMode D a (m + r - (j : ℤ)) (originalI D hu hD (n + (j : ℤ)) u v)) -
    (∑ᶠ j : ℕ, (((-1 : ℂ)^j * Ring.choose (r : ℂ) j) * (-1 : ℂ)^r) •
      originalI D hu hD (n + r - (j : ℤ)) u
        (((fixedParitySlice D hu (-1) a)[[m + (j : ℤ)]]) v)) := by
  let restore := restoreFixedSource D hu hD
  have hr := mixed_residual_zero D hu hD h24 m n r a u v
  rw [mixed_residual_expansion] at hr
  obtain ⟨hl, hf, hs⟩ := mixed_families_finite D hu hD m n r a u v
  have hz := congrArg restore hr
  rw [map_add, map_sub, map_zero, map_finsum restore hl, map_finsum restore hf,
    map_finsum restore hs] at hz
  apply sub_eq_zero.mp
  change (_ - _) = 0
  simp only [mixedLeftTerm, mixedFirstTerm, mixedSecondTerm, mixedMode, map_smul]
    at hz
  simp only [restore, restore_opposite_action] at hz
  unfold originalI
  change _ - (_ - _) = 0
  convert hz using 1 <;> abel

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
