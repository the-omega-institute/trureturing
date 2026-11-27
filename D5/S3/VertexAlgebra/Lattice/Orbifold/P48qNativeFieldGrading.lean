/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFieldGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFieldGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal weight shift of every coefficient of the native cubic field. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan

/-! The conformal Ward identity extends to arbitrary lattice states by projecting
onto the lift eigenspace selected by the cover exponent. This gives the weight
shift on the full momentum–Fock carrier used in the graded dual. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFieldGrading

open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField)
open P48qNativeVirasoro (native_LZero_ward)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedStateEnergy (totalLZero)
open private lift_sourceLZero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private residueIndex liftProject_residue_coeff liftProject_residue_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
open private liftProject from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "L" => sugawaraMode lattice (actualInverse lattice) 0
local notation "σ" => standardLift lattice g g_cube g_isometry

/-- The zero-mode Ward commutator at cover exponent `m`, for arbitrary
source states, including states with mixed weights and lift eigenvalues. -/
theorem nativeField_LZero_ward (a : NativeStates) (m : ℤ) :
    let B := C (nativeField a) m
    totalLZero * B - B * totalLZero =
      C (nativeField (L a)) m + ((m : ℂ) / 3) • B := by
  intro B
  let b := liftProject (residueIndex m) a
  have hComm (u : NativeStates) : L (σ u) = σ (L u) := (lift_sourceLZero u).symm
  have hProjected : L b = liftProject (residueIndex m) (L a) := by
    dsimp only [b, liftProject]
    simp only [map_smul, map_add, hComm]
  have hMode : C (nativeField b) m = B := liftProject_residue_coeff a m
  have hSourceMode : C (nativeField (L b)) m = C (nativeField (L a)) m := by
    rw [hProjected, liftProject_residue_coeff]
  have hWard := native_LZero_ward b m (liftProject_residue_eigen a m) (-1)
  have hIndex : m - 3 * ((-1 : ℤ) + 1) = m := by omega
  have hScalar : ((-1 : ℤ) : ℂ) - (m : ℂ) / 3 + 1 = -((m : ℂ) / 3) := by
    push_cast <;> ring
  simpa only [hIndex, hScalar, hMode, hSourceMode, neg_smul, sub_neg_eq_add] using hWard

/-- With `x^3 = z`, the coefficient of `x^m` takes twisted weight `w` to
`w + d + m/3` when the actual source state has weight `d`. -/
theorem nativeField_coeff_weight (a : NativeStates) (v : State) (m : ℤ) (d w : ℂ)
    (ha : L a = d • a) (hv : totalLZero v = w • v) :
    let B := C (nativeField a) m
    totalLZero (B v) = (w + d + (m : ℂ) / 3) • B v := by
  intro B
  have h := DFunLike.congr_fun (nativeField_LZero_ward a m) v
  change totalLZero (B v) - B (totalLZero v) =
    C (nativeField (L a)) m v + ((m : ℂ) / 3) • B v at h
  simp only [ha, hv, map_smul, Pi.smul_apply, LinearMap.smul_apply] at h
  calc
    totalLZero (B v) = (d • B v + ((m : ℂ) / 3) • B v) + w • B v := eq_add_of_sub_eq h
    _ = _ := by
      rw [← add_smul, ← add_smul]
      congr 1
      ring

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFieldGrading
