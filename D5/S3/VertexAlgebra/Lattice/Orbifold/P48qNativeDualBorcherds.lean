/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeDualBorcherds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual P48q restricted dual satisfies the inverse cubic twisted module law. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualResidueIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualIterateSum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qOrderThreeSpectrumTransport
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-! The complete Borcherds identity and inverse cubic module law on the actual P48q dual. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualBorcherds

open scoped BigOperators DirectSum VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeAllStateReconstruction (mu)
open LatticePositiveEnergy (carrierEnergyDecomposition grade)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open OrdinaryResidueIterate (ordinary_residue)
open P48qAllJetWickField (NativeStates)
open P48qFieldCarrierTransport (stripResidueOn TwistedBorcherdsOn)
open P48qNativeDualLinearField (dualField dualField_inverse_residue dualField_translate_coeff
  dualField_vacuum)
open P48qNativeRestrictedDualField (RestrictedDual gradedPairing_injective
  gradedPairing_dualField_residue_iterate gradedPairing_dualField_iterate_sum)
open P48qOrderThreeSpectrumTransport (CubicTwistedModuleLaw)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open SignedFieldResidueLocality (residueField)
open private source_grade_weight liftOnGrade lift_on_decomposition from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualLinearField
open private R_sum_first from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueIterate
open private R_sum from D5.S3.VertexAlgebra.GroundRightCurrentTransport.Residue

noncomputable section

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0

private theorem source_eigen_weight_sum (a : NativeStates) (s : ℤ)
    (ha : σ a = ζ ^ s • a) :
    ∃ (S : Finset ℤ) (A : ℤ → NativeStates),
      (∑ i ∈ S, A i) = a ∧
      ∀ i, L₀ (A i) = (i.toNat : ℂ) • A i ∧ σ (A i) = ζ ^ s • A i := by
  classical
  let x := carrierEnergyDecomposition lattice a
  have hx : DirectSum.lmap liftOnGrade x = ζ ^ s • x := by
    change DirectSum.lmap liftOnGrade (carrierEnergyDecomposition lattice a) =
      ζ ^ s • carrierEnergyDecomposition lattice a
    rw [lift_on_decomposition a, ha, map_smul]
  refine ⟨x.support, fun i => (x i).val, ?_, ?_⟩
  · have hsum :
        (∑ i ∈ x.support, DirectSum.lof ℂ ℤ (fun j => grade lattice j) i (x i)) = x := by
      simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of x
    calc
      (∑ i ∈ x.support, (x i).val) =
          DirectSum.coeLinearMap (grade lattice)
            (∑ i ∈ x.support, DirectSum.lof ℂ ℤ (fun j => grade lattice j) i (x i)) := by
        simp only [map_sum, DirectSum.coeLinearMap_lof]
      _ = a := by
        rw [hsum]
        exact (carrierEnergyDecomposition lattice).symm_apply_apply a
  · intro i
    refine ⟨source_grade_weight i (x i), ?_⟩
    have hi := congrArg (fun y : (⨁ j : ℤ, grade lattice j) => (y i).val) hx
    simpa only [DirectSum.lmap_apply, DirectSum.smul_apply, Submodule.coe_smul, liftOnGrade,
      LinearMap.coe_restrict_apply, LinearEquiv.coe_coe] using hi

private theorem stripResidueOn_sum (s : ℤ) (S : Finset ℤ)
    (F : ℤ → VertexOperator ℂ RestrictedDual) :
    stripResidueOn s (∑ i ∈ S, F i) = ∑ i ∈ S, stripResidueOn s (F i) := by
  apply HVertexOperator.coeff_inj
  funext k
  simp only [stripResidueOn, VertexOperator.of_coeff, HVertexOperator.coeff_of_coeff,
    map_sum, Finset.sum_apply]

private theorem source_mu_sum (S T : Finset ℤ) (A B : ℤ → NativeStates) (n : ℤ) :
    mu lattice (∑ i ∈ S, A i) n (∑ l ∈ T, B l) =
      ∑ i ∈ S, ∑ l ∈ T, mu lattice (A i) n (B l) := by
  simp only [mu, map_sum, Finset.sum_apply, LinearMap.sum_apply]
  exact Finset.sum_comm

private theorem twistedBorcherdsOn_cutoff_mono (a b : NativeStates) (s t : ℤ) {N M : ℕ}
    (hNM : N ≤ M) (hcut : ∀ j ≥ (N : ℤ), mu lattice a j b = 0)
    (h : TwistedBorcherdsOn dualField a b s t N) :
    TwistedBorcherdsOn dualField a b s t M := by
  intro p q n
  rw [h p q n]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  rw [hcut (n + (j : ℤ)) (by omega)]
  simp only [map_zero, Pi.zero_apply, smul_zero]

private theorem forward_eigen_of_inverse (a : NativeStates) (s : ℤ)
    (ha : (σ).symm a = ζ ^ s • a) : σ a = ζ ^ (-s) • a := by
  have h := congrArg (fun v : NativeStates => σ v) ha
  change σ ((σ).symm a) = σ (ζ ^ s • a) at h
  rw [LinearEquiv.apply_symm_apply, map_smul] at h
  calc
    σ a = (ζ ^ s)⁻¹ • (ζ ^ s • σ a) := by
      rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero s (Units.ne_zero ThirdTwistedChargeCocycle.zeta)),
        one_smul]
    _ = ζ ^ (-s) • a := by rw [← h, zpow_neg]

set_option maxHeartbeats 2000000 in
-- Comparing the paired series specializes both finite expansions and their grading maps.
/-- The two finite paired expansions agree for a homogeneous source eigenpair. -/
theorem dualField_inverse_borcherds_homogeneous
    (a b : NativeStates) (d e : ℕ)
    (ha : L₀ a = (d : ℂ) • a) (hb : L₀ b = (e : ℂ) • b)
    (s t : ℤ) (hsa : σ a = ζ ^ s • a) (htb : σ b = ζ ^ t • b) :
    ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice a j b = 0) ∧
      TwistedBorcherdsOn dualField a b (-s) (-t) N := by
  obtain ⟨N, hN, hCut, hResidue⟩ :=
    gradedPairing_dualField_residue_iterate a b d e ha hb s t hsa htb
  refine ⟨N, hCut, ?_⟩
  intro p q n
  apply LinearMap.ext
  intro f
  apply gradedPairing_injective
  apply LinearMap.ext
  intro v
  exact (hResidue p q n f v).trans
    (gradedPairing_dualField_iterate_sum a b d e ha hb N hN s t p q n f v).symm

section

variable (hHom : ∀ (a b : NativeStates) (d e : ℕ),
  L₀ a = (d : ℂ) • a → L₀ b = (e : ℂ) • b →
  ∀ (s t : ℤ), σ a = ζ ^ s • a → σ b = ζ ^ t • b →
  ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice a j b = 0) ∧
    TwistedBorcherdsOn dualField a b (-s) (-t) N)

include hHom

set_option maxHeartbeats 2000000 in
-- Extending the identity uses two nested finite sums of graded-state coefficients.
/-- The inverse-twisted identity extends to source eigenstates of mixed weight. -/
theorem dualField_inverse_borcherds_of_homogeneous (a b : NativeStates) (s t : ℤ)
    (ha : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b) :
    ∃ N : ℕ, (∀ j ≥ (N : ℤ), mu lattice a j b = 0) ∧
      TwistedBorcherdsOn dualField a b (-s) (-t) N := by
  classical
  obtain ⟨S, A, hA, hAeigen⟩ := source_eigen_weight_sum a s ha
  obtain ⟨T, B, hB, hBeigen⟩ := source_eigen_weight_sum b t hb
  choose cutoff hcut hBorcherds using fun ij : ℤ × ℤ =>
    hHom (A ij.1) (B ij.2) ij.1.toNat ij.2.toNat (hAeigen ij.1).1 (hBeigen ij.2).1
      s t (hAeigen ij.1).2 (hBeigen ij.2).2
  let N := (S.product T).sup cutoff
  have hle (i l : ℤ) (hi : i ∈ S) (hl : l ∈ T) : cutoff (i, l) ≤ N :=
    Finset.le_sup (s := S.product T) (f := cutoff) (Finset.mem_product.mpr ⟨hi, hl⟩)
  refine ⟨N, ?_, ?_⟩
  · intro n hn
    rw [← hA, ← hB, source_mu_sum]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro l hl
    have hpair := hle i l hi hl
    exact hcut (i, l) n (by omega)
  · intro p q n
    let X (v : NativeStates) := stripResidueOn (-s - 3 * p) (dualField v)
    let Y (v : NativeStates) := stripResidueOn (-t) (dualField v)
    let J := Finset.range ((N : ℤ) - n).toNat
    let rhsTerm (j : ℕ) (v w : NativeStates) : Module.End ℂ RestrictedDual :=
      Ring.choose ((p : ℂ) - ((-s : ℤ) : ℂ) / 3) j •
        HVertexOperator.coeff (dualField (mu lattice v (n + (j : ℤ)) w))
          ((-s) + (-t) - 3 * (p + q - (j : ℤ) + 1))
    change ((residueField 1 n (X a) (Y b)).operator)[[q]] = ∑ j ∈ J, rhsTerm j a b
    have hX : X a = ∑ i ∈ S, X (A i) := by
      rw [← hA]
      change stripResidueOn (-s - 3 * p) (dualField (∑ i ∈ S, A i)) = _
      rw [map_sum, stripResidueOn_sum]
    have hY : Y b = ∑ l ∈ T, Y (B l) := by
      rw [← hB]
      change stripResidueOn (-t) (dualField (∑ l ∈ T, B l)) = _
      rw [map_sum, stripResidueOn_sum]
    calc
      _ = ∑ i ∈ S, ∑ l ∈ T,
          ((residueField 1 n (X (A i)) (Y (B l))).operator)[[q]] := by
        rw [hX, hY]
        simp only [← ordinary_residue]
        rw [R_sum_first]
        simp only [R_sum, VertexOperator.ncoeff_apply, map_sum, Finset.sum_apply]
      _ = ∑ i ∈ S, ∑ l ∈ T, ∑ j ∈ J, rhsTerm j (A i) (B l) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
        exact (twistedBorcherdsOn_cutoff_mono (A i) (B l) (-s) (-t) (hle i l hi hl)
          (hcut (i, l)) (hBorcherds (i, l))) p q n
      _ = ∑ j ∈ J, ∑ i ∈ S, ∑ l ∈ T, rhsTerm j (A i) (B l) :=
        Finset.sum_comm_cycle
      _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        symm
        rw [← hA, ← hB]
        simp only [rhsTerm, source_mu_sum, map_sum, Finset.sum_apply, Finset.smul_sum]

/-- The actual dual field satisfies the cubic module law for the inverse lift
once the homogeneous inverse-twisted Borcherds identities are supplied. -/
theorem dualField_cubicTwistedModuleLaw_inverse_of_homogeneous :
    CubicTwistedModuleLaw (σ).symm dualField where
  vacuum := dualField_vacuum
  residue := dualField_inverse_residue
  borcherds := by
    intro a b s t ha hb
    simpa only [neg_neg] using
      dualField_inverse_borcherds_of_homogeneous hHom a b (-s) (-t)
        (forward_eigen_of_inverse a s ha) (forward_eigen_of_inverse b t hb)
  translation := dualField_translate_coeff

end

/-- The actual cubic lift has an inverse-twisted module on the restricted dual. -/
theorem dualField_cubicTwistedModuleLaw_inverse :
    CubicTwistedModuleLaw (σ).symm dualField :=
  dualField_cubicTwistedModuleLaw_inverse_of_homogeneous
    dualField_inverse_borcherds_homogeneous

#print axioms dualField_cubicTwistedModuleLaw_inverse

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeDualBorcherds
