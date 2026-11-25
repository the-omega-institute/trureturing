/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldMatter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Virasoro matter from the literal Leech orbifold stress field. -/

import D5.S3.VertexAlgebra.BRST.VirasoroBRST
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
import Mathlib.RingTheory.TensorProduct.Maps

/-! The Virasoro representation of the original fixed and negative twisted
Leech sectors, obtained from the assembled field's actual stress coefficients. -/

set_option autoImplicit false
noncomputable section
open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldMatter

open LatticeGeneratingFieldLocality LatticeInvolution LatticeHalfFock
open LatticeHalfFockCorrectedField HalfFock.LatticeHalfFockParityField
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeSugawaraCurrents LatticeSugawaraVirasoro HalfFockSpectralFiberSource
open TwistedGround.Orbifold
open ActualLeechHyperbolic (leechData leech_spec)
open private stress from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation

abbrev leechUnit : IsUnit leechData.G.det := leech_spec.2.1
abbrev leechPosDef : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1

/-- The fixed Leech sector paired with the native negative twisted sector. -/
abbrev Orbifold := OriginalOrbifoldField.Carrier leechData leechUnit

/-- The existing theta-fixed stress state in the fixed summand. -/
abbrev omega : Orbifold := (stress leechData, 0)

/-- The normalized coefficient at index `n+1` of the literal assembled field. -/
def mode (n : ℤ) : Module.End ℂ Orbifold :=
  (OriginalOrbifoldField.Y leechData leechUnit leechPosDef omega)[[n + 1]]

/-- The same normalized mode acts by ordinary Sugawara on the fixed sector
and corrected tensor half-Fock on the negative twisted sector. -/
theorem mode_apply (n : ℤ) (x : Orbifold) :
    ((mode n x).1.val, (mode n x).2.val) =
      (sugawaraMode leechData (actualInverse leechData) n x.1.val,
        tensorL leechData (ActualGround leechData leechUnit)
          (actualInverse leechData) n x.2.val) := by
  unfold mode omega
  rw [OriginalOrbifoldField.Y_fixed_ncoeff_apply]
  apply Prod.ext
  · change ((LatticeAllStateField.Y leechData
      (LatticeActualConformalState.omega leechData (actualInverse leechData)))[[n+1]]) x.1.val = _
    rw [LatticeActualConformalState.omega_modes]
  · simp only [fixedParitySlice]
    change ((correctedField leechData leechUnit
      (LatticeActualConformalState.omega leechData (actualInverse leechData))).coeff
        (2 * (-(n + 1) - 1))) x.2.val = _
    rw [LatticeHalfFockCorrectedConformal.correctedField_omega _ _ _
      (actualInverse_left leechData leechUnit), tensorStressField,
      HVertexOperator.coeff_of_coeff, show 2 * (-(n+1) - 1) = -2*n - 4 by omega]
    simp only [stressCoeff, show (-2*n-4) % 2 = 0 by omega, ite_true,
      show (-(-2*n-4)-4)/2 = n by omega, tensorL]

private theorem twisted_virasoro (m n : ℤ) :
    let T := fun k => tensorL leechData (ActualGround leechData leechUnit)
      (actualInverse leechData) k
    T m * T n - T n * T m =
      ((m-n : ℤ) : ℂ) • T (m+n) +
        (if m+n = 0 then (24 / 12 : ℂ) * ((m : ℂ)^3-m) else 0) • 1 := by
  let lift := Module.End.rTensorAlgHom ℂ (Oscillator leechData) (ActualGround leechData leechUnit)
  have h := congrArg lift (L_virasoro leechData (actualInverse leechData)
    (actualInverse_left leechData leechUnit) (actualInverse_right leechData leechUnit) m n)
  simp only [map_add, map_sub, map_smul, map_mul, map_one] at h
  have lift_mode (k : ℤ) : lift (L leechData (actualInverse leechData) k) =
      tensorL leechData (ActualGround leechData leechUnit) (actualInverse leechData) k := rfl
  simpa only [lift_mode, Int.cast_sub, leech_spec.1, Nat.cast_ofNat] using h

/-- The literal Leech orbifold stress coefficients carry central charge 24. -/
theorem virasoro (m n : ℤ) :
    mode m * mode n - mode n * mode m =
      ((m-n : ℤ) : ℂ) • mode (m+n) +
        (if m+n = 0 then (24 / 12 : ℂ) * ((m : ℂ)^3-m) else 0) •
          (1 : Module.End ℂ Orbifold) := by
  have fixed_apply (k : ℤ) (y : Orbifold) :
      (mode k y).1.val = sugawaraMode leechData (actualInverse leechData) k y.1.val :=
    congrArg Prod.fst (mode_apply k y)
  have twisted_apply (k : ℤ) (y : Orbifold) :
      (mode k y).2.val = tensorL leechData (ActualGround leechData leechUnit)
        (actualInverse leechData) k y.2.val :=
    congrArg Prod.snd (mode_apply k y)
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · apply Subtype.ext
    simpa only [Module.End.mul_apply, Module.End.one_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, Prod.fst_sub, Prod.fst_add,
      Prod.smul_fst, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      fixed_apply, leech_spec.1, Nat.cast_ofNat] using
      LinearMap.congr_fun
        (sugawaraMode_virasoro leechData (actualInverse leechData)
          (actualInverse_left leechData leechUnit) (actualInverse_right leechData leechUnit) m n)
        x.1.val
  · apply Subtype.ext
    simpa only [Module.End.mul_apply, Module.End.one_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, Prod.snd_sub, Prod.snd_add,
      Prod.smul_snd, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      twisted_apply] using LinearMap.congr_fun (twisted_virasoro m n) x.2.val

/-- Truncation is inherited from the assembled field on each actual state. -/
theorem positive_mode_truncation (x : Orbifold) :
    ∃ B : ℤ, ∀ n : ℤ, B < n → mode n x = 0 := by
  obtain ⟨B, hB⟩ := OriginalOrbifoldField.mode_tail leechData leechUnit leechPosDef omega x
  exact ⟨B, fun n hn => by
    rw [mode, OriginalOrbifoldField.Y_ncoeff]
    exact hB (n+1) (by omega)⟩

/-- Bosonic-string matter on the literal two-sector Leech orbifold. -/
@[instance_reducible] def matter : VirasoroBRST.MatterDatum Orbifold where
  mode := mode
  centralCharge := 24
  virasoro := virasoro
  positive_mode_truncation := positive_mode_truncation

#print axioms mode_apply
#print axioms matter

end D5.S3.VertexAlgebra.ActualLeechOrbifoldMatter
