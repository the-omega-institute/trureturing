/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite cubic residue support of the native BPZ dual coefficients. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualCoefficients
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeCurrentLocality
import Mathlib.Data.Int.ModEq
import OmegaBuild.Commands

/-! The source conformal mode preserves each lift eigenspace. Coordinate
inversion negates the occupied cover residue of the resulting dual coefficients. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidue

open scoped VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_ncoeff)
open LatticeAllStateField (Y)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift standardLift_compatible)
open P48qAllJetWickField (NativeStates)
open P48qNativeConformalSector (fixedOmega)
open P48qNativeCurrentLocality (nativeField_inResidue)
open P48qNativeDualCoefficients (bpzTerm bpzTermOnEigenspaces bpzDualCoeff bpzDualCoeff_apply)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

private theorem lift_sourceLOne_commute : Commute (σ).toLinearMap L₁ := by
  change (σ).toLinearMap * L₁ = L₁ * (σ).toLinearMap
  apply LinearMap.ext
  intro v
  change σ (L₁ v) = L₁ (σ v)
  have hFixed : σ fixedOmega.val = fixedOmega.val := by
    have hMem : fixedOmega.val ∈ Module.End.eigenspace (σ).toLinearMap 1 := fixedOmega.property
    simpa only [LinearEquiv.coe_toLinearMap, one_smul] using
      Module.End.mem_eigenspace_iff.mp hMem
  have hMode : ((Y lattice fixedOmega.val)[[2]]) = L₁ := by
    change ((Y lattice (omega lattice (actualInverse lattice)))[[2]]) = L₁
    rw [omega_ncoeff, show (2 : ℤ) - 1 = 1 by decide]
  have h := (standardLift_compatible lattice g g_cube g_isometry).2.1 fixedOmega.val 2 v
  simpa only [hFixed, hMode] using h

/-- For a source lift eigenvector of eigenvalue `ζ^s`, the dual coefficient
vanishes outside the residue `-s` on the cubic cover. -/
theorem bpzDualCoeff_eq_zero_of_residue_ne (a : NativeStates) (d : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (s : ℤ)
    (hs : a ∈ Module.End.eigenspace (σ).toLinearMap (ζ ^ s))
    (w : ℂ) (k : ℤ) (hk : k % 3 ≠ (-s) % 3) : bpzDualCoeff a d ha w k = 0 := by
  have hEigen : σ a = ζ ^ s • a := by
    simpa only [LinearEquiv.coe_toLinearMap] using Module.End.mem_eigenspace_iff.mp hs
  have hPower (j : ℕ) : σ ((L₁ ^ j) a) = ζ ^ s • (L₁ ^ j) a := by
    have h := LinearMap.congr_fun (lift_sourceLOne_commute.pow_right j).eq a
    change σ ((L₁ ^ j) a) = (L₁ ^ j) (σ a) at h
    rw [h, hEigen, map_smul]
  have hTerm (j : ℕ) : bpzTerm a d k j = 0 := by
    unfold bpzTerm
    have hIndex : (-k - 6 * (d : ℤ) + 3 * (j : ℤ)) % 3 ≠ s % 3 := by
      rw [show (-k - 6 * (d : ℤ) + 3 * (j : ℤ)) % 3 = (-k) % 3 by omega]
      intro h
      have hNeg := (show Int.ModEq 3 (-k) s from h).neg
      exact hk (by simpa only [Int.ModEq, neg_neg] using hNeg)
    exact nativeField_inResidue ((L₁ ^ j) a) s (hPower j) _ hIndex
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  have hRestricted (j : ℕ) : bpzTermOnEigenspaces a d ha w k j v = 0 := by
    apply Subtype.ext
    change bpzTerm a d k j v.val = 0
    exact LinearMap.congr_fun (hTerm j) v.val
  simp only [bpzDualCoeff_apply, LinearMap.zero_apply, hRestricted, map_zero, mul_zero,
    Finset.sum_const_zero]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidue
