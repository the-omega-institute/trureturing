/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResidueIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualResidueIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reflected dual residue equals a finite native iterate sum at one uniform cutoff. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResiduePairing
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidue
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
import OmegaBuild.Commands

/-! Finite native iterate expansion of the reflected restricted-dual residue. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeAllStateReconstruction (mu)
open LatticeHalfFockGroundRightCurrentTransport.Calculus (R Z)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open OrdinaryResidueIterate (ordinary_residue)
open P48qAllJetWickField (NativeStates nativeField)
open P48qFieldCarrierTransport (stripResidueOn)
open P48qNativeCurrentLocality (stripResidue stripResidue_coeff)
open P48qNativeDualLinearField (dualField)
open P48qNativeResidueIterate (TwistedBorcherdsAt)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open SignedFieldResidueLocality (residueField)
open StateFieldResidueReconstruction (epsilon)
open private R_sum_first nativeField_twisted_borcherds_with_cutoff
  twistedBorcherdsAt_mono source_cutoff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
open private R_smul_first from D5.S3.VertexAlgebra.SignedFields.OrdinaryResidueIterate
open private R_sum R_smul R_Z Z_mode from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue
open private lift_sourceLOne_commute from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidue

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

private theorem residueField_sum_mode_zero
    (I J : Finset ℕ) (X Y : ℕ → VertexOperator ℂ State)
    (α β : ℂ) (c u : ℕ → ℂ) (n : ℤ) :
    ((residueField 1 n (α • ∑ i ∈ I, c i • X i)
      (β • ∑ l ∈ J, u l • Y l)).operator)[[0]] =
      (α * β) • ∑ i ∈ I, c i • ∑ l ∈ J, u l •
        ((residueField 1 n (X i) (Y l)).operator)[[0]] := by
  simp only [← ordinary_residue]
  rw [R_smul_first, R_smul, R_sum_first]
  simp_rw [R_smul_first, R_sum, R_smul]
  simp only [VertexOperator.ncoeff_apply, map_smul, map_sum, Pi.smul_apply,
    Finset.sum_apply, smul_smul]

set_option maxHeartbeats 1500000 in
/-- The actual restricted-dual residue pairs with the native source iterates
using one source cutoff for all integer indices. -/
theorem gradedPairing_dualField_residue_iterate (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (s t : ℤ) (hsa : σ a = ζ ^ s • a) (htb : σ b = ζ ^ t • b) :
    ∃ N : ℕ, d + e ≤ N ∧ (∀ m ≥ (N : ℤ), mu lattice a m b = 0) ∧
      ∀ (p q n : ℤ) (f : RestrictedDual) (v : State),
        let pNative (i : ℕ) : ℤ := -p + 2 * (d : ℤ) - (i : ℤ) - 2 - n
        let qNative (l : ℕ) : ℤ := -q + 2 * (e : ℤ) - (l : ℤ) - 2 - n
        let T : Module.End ℂ State :=
          ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ •
            ∑ l ∈ Finset.range (e + 1), (l.factorial : ℂ)⁻¹ •
              ∑ h ∈ Finset.range ((N : ℤ) - n).toNat,
                Ring.choose ((pNative i : ℂ) - (s : ℂ) / 3) h •
                  HVertexOperator.coeff
                    (nativeField (mu lattice ((L₁ ^ i) a) (n + (h : ℤ)) ((L₁ ^ l) b)))
                    (s + t - 3 * (pNative i + qNative l - (h : ℤ) + 1))
        gradedPairing ((((residueField 1 n
          (stripResidueOn (-s - 3 * p) (dualField a))
          (stripResidueOn (-t) (dualField b))).operator)[[q]]) f) v =
          (-epsilon n * ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e)) * gradedPairing f (T v) := by
  classical
  have liftEigenPow (c : NativeStates) (r : ℤ) (hc : σ c = ζ ^ r • c) (j : ℕ) :
      σ ((L₁ ^ j) c) = ζ ^ r • (L₁ ^ j) c := by
    have h := LinearMap.congr_fun (lift_sourceLOne_commute.pow_right j).eq c
    change σ ((L₁ ^ j) c) = (L₁ ^ j) (σ c) at h
    rw [h, hc, map_smul]
  choose cutoff hcut hborcherds using fun ij : ℕ × ℕ =>
    nativeField_twisted_borcherds_with_cutoff ((L₁ ^ ij.1) a) ((L₁ ^ ij.2) b) s t
      (liftEigenPow a s hsa ij.1) (liftEigenPow b t htb ij.2)
  obtain ⟨K, hK⟩ := source_cutoff a b
  let pairs := (Finset.range (d + 1)).product (Finset.range (e + 1))
  let N := max (d + e) (max K (pairs.sup cutoff))
  have hUniform (i l : ℕ) (hi : i ∈ Finset.range (d + 1)) (hl : l ∈ Finset.range (e + 1)) :
      TwistedBorcherdsAt nativeField ((L₁ ^ i) a) ((L₁ ^ l) b) s t N := by
    have hmem : (i, l) ∈ pairs := Finset.mem_product.mpr ⟨hi, hl⟩
    have hle : cutoff (i, l) ≤ N :=
      (Finset.le_sup (f := cutoff) hmem).trans
        ((le_max_right K (pairs.sup cutoff)).trans (le_max_right _ _))
    exact twistedBorcherdsAt_mono nativeField _ _ s t hle (hcut (i, l)) (hborcherds (i, l))
  refine ⟨N, le_max_left _ _, ?_, ?_⟩
  · intro m hm
    have hle : K ≤ N := (le_max_left _ _).trans (le_max_right _ _)
    exact hK m (by omega)
  · intro p q n f v pNative qNative T
    let X (i : ℕ) := stripResidue (s - 3 * pNative i) (nativeField ((L₁ ^ i) a))
    let Y (l : ℕ) := stripResidue (t - 3 * qNative l) (nativeField ((L₁ ^ l) b))
    let A : VertexOperator ℂ State := (-1 : ℂ) ^ d •
      ∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ • X i
    let B : VertexOperator ℂ State := (-1 : ℂ) ^ e •
      ∑ l ∈ Finset.range (e + 1), (l.factorial : ℂ)⁻¹ • Y l
    have hIterate (i l : ℕ) (hi : i ∈ Finset.range (d + 1))
        (hl : l ∈ Finset.range (e + 1)) :
        ((residueField 1 n (X i) (Y l)).operator)[[0]] =
          ∑ h ∈ Finset.range ((N : ℤ) - n).toNat,
            Ring.choose ((pNative i : ℂ) - (s : ℂ) / 3) h •
              HVertexOperator.coeff
                (nativeField (mu lattice ((L₁ ^ i) a) (n + (h : ℤ)) ((L₁ ^ l) b)))
                (s + t - 3 * (pNative i + qNative l - (h : ℤ) + 1)) := by
      have hShift : Y l = Z (-(qNative l)) (stripResidue t (nativeField ((L₁ ^ l) b))) := by
        change stripResidue (t - 3 * qNative l) (nativeField ((L₁ ^ l) b)) = _
        apply HVertexOperator.coeff_inj
        funext k
        have hk := Z_mode (-(qNative l))
          (stripResidue t (nativeField ((L₁ ^ l) b))) (-k - 1)
        simpa only [VertexOperator.ncoeff_apply, stripResidue_coeff,
          show -(-k - 1) - 1 = k by omega,
          show 3 * (-(-k - 1 - -(qNative l)) - 1) + t =
            3 * k + (t - 3 * qNative l) by omega] using hk.symm
      rw [hShift, ← ordinary_residue, R_Z, Z_mode, zero_sub, neg_neg, ordinary_residue]
      exact hUniform i l hi hl (pNative i) (qNative l) n
    have hSum :
        (∑ i ∈ Finset.range (d + 1), (i.factorial : ℂ)⁻¹ •
          ∑ l ∈ Finset.range (e + 1), (l.factorial : ℂ)⁻¹ •
            ((residueField 1 n (X i) (Y l)).operator)[[0]]) = T := by
      dsimp only [T]
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun M : Module.End ℂ State => (i.factorial : ℂ)⁻¹ • M)
      apply Finset.sum_congr rfl
      intro l hl
      exact congrArg (fun M : Module.End ℂ State => (l.factorial : ℂ)⁻¹ • M)
        (hIterate i l hi hl)
    have hMode : ((residueField 1 n A B).operator)[[0]] =
        ((-1 : ℂ) ^ d * (-1 : ℂ) ^ e) • T := by
      dsimp only [A, B]
      rw [residueField_sum_mode_zero (Finset.range (d + 1)) (Finset.range (e + 1)) X Y
        ((-1 : ℂ) ^ d) ((-1 : ℂ) ^ e) (fun i => (i.factorial : ℂ)⁻¹)
        (fun l => (l.factorial : ℂ)⁻¹) n, hSum]
    have hPaired :
        gradedPairing ((((residueField 1 n
          (stripResidueOn (-s - 3 * p) (dualField a))
          (stripResidueOn (-t) (dualField b))).operator)[[q]]) f) v =
          -epsilon n * gradedPairing f ((((residueField 1 n A B).operator)[[0]]) v) := by
      simpa only [A, B, X, Y, pNative, qNative] using
        gradedPairing_dualField_residue a b d e ha hb s t p q n f v
    simp only [hPaired, hMode, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_assoc]

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeRestrictedDualField
