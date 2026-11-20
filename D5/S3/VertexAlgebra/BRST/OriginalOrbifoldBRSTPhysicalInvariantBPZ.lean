/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalInvariantBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalInvariantBPZ
   mirror-E: none(waiver:algebraic-original-physical-bpz-invariance)
   anchors: []
   utility: none
   digest: The native BPZ form is invariant under the original Leech physical BRST Lie bracket. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTAmbientAdjoint
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatterModeBPZ
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterOrbifoldBPZ
import D5.S3.Quantum.Fermionic.BcGhostOppositeNormalProduct

/-! The orbifold weight, hyperbolic oscillator cutoff and ghost energy bound the
divided lowering powers on each native basis state. At total weight one and even
occupation parity, the resulting tensor BPZ transpose descends to the physical form. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalInvariantBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket parity)
open OriginalOrbifoldCriticalMatter
  (Orbifold Hyperbolic Matter State orbifoldMode orbifoldVertexAlgebra hyperbolicData
    hyperbolicInverse hyperbolic_inverse_left hyperbolic_inverse_right mode matterDatum)
open OriginalOrbifoldBRSTZeroEnergy (FullLabel orbifoldBasis totalEnergy)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ)
open OriginalOrbifoldMatterOrbifoldBPZ (original_orbifold_bpz)
open OriginalOrbifoldCriticalMatterModeBPZ
  (hyperbolicLoweringCutoff divided_matter_L1_tmul matterBPZ_mode_adjoint)
open OriginalOrbifoldBRSTTensorBPZ (divided_total_L1_tmul betaTotal_mode_adjoint_tmul)
open OriginalOrbifoldBRSTGhostBPZ (beta)
open OriginalOrbifoldBRSTAmbientAdjoint (WeightOneBasisAdjunction physicalBPZ_invariant_of_basis)
open OriginalOrbifoldBRSTPhysicalPairing (physicalBPZ)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne)
open LatticePositiveEnergy (carrierBasis energy grade actualL0_basis actualL0_eigen_iff_grade)
open StateField.BorcherdsPermutations (dividedTranslation modesOfStateField)
open StateFieldResidueReconstruction (epsilon)
open Finset.HasAntidiagonal (mem_antidiagonal)

open private fullBasis_apply orbifoldMode_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTZeroEnergy
open private fixed_grade negative_energy fixed_energy_tail negative_energy_tail from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterOrbifoldBPZ
open private hyperbolic_lowering_tail from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatterModeBPZ
open private oppositeMode_eq_sum from D5.S3.Quantum.Fermionic.BcGhostOppositeNormalProduct

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "DO" => dividedTranslation (orbifoldMode 1)
local notation "DM" => dividedTranslation (mode 1)
local notation "DG" => dividedTranslation (BcGhostVirasoro.L 1)
local notation "DT" => dividedTranslation (VirasoroBRST.Ltotal matterDatum 1)
local notation "YO" => orbifoldVertexAlgebra.stateField
local notation "YG" => BcGhostStateField.Y

private theorem orbifold_lowering_tail (a : Orbifold) (h : ℕ)
    (ha : orbifoldMode 0 a = (h : ℂ) • a) (r : ℕ) (hr : h + 1 ≤ r) :
    DO r a = 0 := by
  have ha' : orbifoldMode 0 a = ((h : ℤ) : ℂ) • a := by
    simpa only [Int.cast_natCast] using ha
  have hFixed := fixed_energy_tail h a.1 (fixed_grade (h : ℤ) a ha') r hr
  have hNegative := negative_energy_tail h a.2
    (by simpa only [Int.cast_natCast] using negative_energy (h : ℤ) a ha') r (by omega)
  have hsplit : ((a.1, 0) : Orbifold) + (0, a.2) = a :=
    Prod.ext (by simp) (by simp)
  have hpow : (orbifoldMode 1 ^ r) a = 0 := by
    calc
      _ = (orbifoldMode 1 ^ r) (((a.1, 0) : Orbifold) + (0, a.2)) :=
        congrArg (fun u : Orbifold => (orbifoldMode 1 ^ r) u) hsplit.symm
      _ = 0 := by rw [map_add, hFixed, hNegative, zero_add]
  simp only [dividedTranslation, LinearMap.smul_apply, hpow, smul_zero]

private theorem orbifoldBPZ_divided_mode (a : Orbifold) (h : ℕ)
    (ha : orbifoldMode 0 a = (h : ℂ) • a) (n : ℤ) (u v : Orbifold) :
    orbifoldBPZ (((YO a)[[n]]) u) v =
      (-1 : ℂ) ^ (h : ℤ) * ∑ r ∈ Finset.range (h + 1),
        orbifoldBPZ u (((YO (DO r a))[[2 * (h : ℤ) - (r : ℤ) - n - 2]]) v) := by
  have hadj := original_orbifold_bpz (h : ℤ) n a u v
    (by simpa only [Int.cast_natCast] using ha)
  rw [hadj, Int.toNat_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  change (r.factorial : ℂ)⁻¹ *
      orbifoldBPZ u (modesOfStateField YO (2 * (h : ℤ) - (r : ℤ) - n - 2)
        ((orbifoldMode 1 ^ r) a) v) =
    orbifoldBPZ u (modesOfStateField YO (2 * (h : ℤ) - (r : ℤ) - n - 2) (DO r a) v)
  simp only [dividedTranslation, LinearMap.smul_apply, map_smul, smul_eq_mul]

private theorem matter_lowering_tail (a : Orbifold) (b : Hyperbolic) (A : ℕ)
    (ha : ∀ r, A ≤ r → DO r a = 0) (d : ℕ) (hd : A + hyperbolicLoweringCutoff b ≤ d) :
    DM d (a ⊗ₜ[ℂ] b) = 0 := by
  rw [divided_matter_L1_tmul]
  apply Finset.sum_eq_zero
  intro rs hrs
  have hsum : rs.1 + rs.2 = d := mem_antidiagonal.mp hrs
  by_cases hr : A ≤ rs.1
  · rw [ha rs.1 hr, TensorProduct.zero_tmul]
  · have hs : hyperbolicLoweringCutoff b ≤ rs.2 := by omega
    rw [hyperbolic_lowering_tail b rs.2 hs, TensorProduct.tmul_zero]

private theorem ghostBPZ_divided_mode (S : Finset ℕ) (n : ℤ) (x y : Fock) :
    beta (((YG (ket S))[[n]]) x) y =
      epsilon (BcGhostRelativeEnergy.energy S) *
        ∑ s ∈ Finset.range (max 1 (BcGhostRelativeEnergy.energy S + 2).toNat),
          beta ((parity ^ S.card) x)
            (((YG (DG s (ket S)))[[2 * BcGhostRelativeEnergy.energy S - (s : ℤ) - n - 2]]) y) := by
  let g := BcGhostRelativeEnergy.energy S
  let B := max 1 (g + 2).toNat
  have htail := BcGhostOppositeNormalProduct.dividedL1_eq_zero (ket S) g
    (BcGhostRelativeEnergy.L_zero_ket S)
  have hadj := BcGhostOppositeNormalProduct.beta_occupation_mode S n x y
  rw [oppositeMode_eq_sum (ket S) y g n B htail] at hadj
  change _ = beta ((parity ^ S.card) x)
    (epsilon g • ∑ s ∈ Finset.range B,
      (((YG (DG s (ket S)))[[2 * g - n - (s : ℤ) - 2]]) y)) at hadj
  have hindex (s : ℕ) :
      2 * BcGhostRelativeEnergy.energy S - n - (s : ℤ) - 2 =
        2 * BcGhostRelativeEnergy.energy S - (s : ℤ) - n - 2 := by omega
  simpa only [g, B, map_smul, map_sum, smul_eq_mul, hindex] using hadj

/-- The native weight-one basis has finite BPZ zero-mode adjunction on its even
occupation states. -/
theorem weightOneBasisAdjunction : WeightOneBasisAdjunction := by
  intro i hweight heven
  let h := i.1.1
  let k := energy hyperbolicData i.2.1
  let g := BcGhostRelativeEnergy.energy i.2.2
  let a := orbifoldBasis i.1
  let b := carrierBasis hyperbolicData i.2.1
  let q := ket i.2.2
  let m : Matter := a ⊗ₜ[ℂ] b
  let A := h + 1 + hyperbolicLoweringCutoff b
  let B := max 1 (g + 2).toNat
  have hk : b ∈ grade hyperbolicData k :=
    (actualL0_eigen_iff_grade hyperbolicData hyperbolicInverse
      hyperbolic_inverse_left hyperbolic_inverse_right k b).mp
      (actualL0_basis hyperbolicData hyperbolicInverse
        hyperbolic_inverse_left hyperbolic_inverse_right i.2.1)
  have ha := orbifoldMode_basis i.1
  have hOrbifold := orbifoldBPZ_divided_mode a h ha
  have hOrbifoldTail := orbifold_lowering_tail a h ha
  have hMatterTail : ∀ r, A ≤ r → DM r m = 0 :=
    matter_lowering_tail a b (h + 1) hOrbifoldTail
  have hGhostTail : ∀ s, B ≤ s → DG s q = 0 :=
    BcGhostOppositeNormalProduct.dividedL1_eq_zero q g (BcGhostRelativeEnergy.L_zero_ket i.2.2)
  have htotal : (h : ℤ) + k + g = 1 := by
    simpa only [h, k, g, totalEnergy, LatticeBRSTZeroEnergyReduction.totalEnergy, add_assoc]
      using hweight
  have hparity : parity ^ i.2.2.card = 1 := by
    obtain ⟨t, ht⟩ := heven
    have ht' : i.2.2.card = 2 * t := by omega
    rw [ht', pow_mul, pow_two, CountableOccupationFock.parity_involution, one_pow]
  refine ⟨A + B, ?_, ?_⟩
  · intro d hd
    rw [fullBasis_apply]
    change DT d (m ⊗ₜ[ℂ] q) = 0
    rw [divided_total_L1_tmul]
    apply Finset.sum_eq_zero
    intro rs hrs
    have hsum : rs.1 + rs.2 = d := mem_antidiagonal.mp hrs
    by_cases hr : A ≤ rs.1
    · rw [hMatterTail rs.1 hr, TensorProduct.zero_tmul]
    · have hs : B ≤ rs.2 := by omega
      rw [hGhostTail rs.2 hs, TensorProduct.tmul_zero]
  · intro u v x y
    rw [fullBasis_apply]
    have hadj := betaTotal_mode_adjoint_tmul m q ((h : ℤ) + k) g i.2.2.card A B
      hMatterTail hGhostTail
      (matterBPZ_mode_adjoint a b (h : ℤ) k (h + 1) hOrbifoldTail hk hOrbifold)
      (ghostBPZ_divided_mode i.2.2) 0 u v x y
    have hindex (d : ℕ) : 2 * (1 : ℤ) - (d : ℤ) - 0 - 2 = -(d : ℤ) := by omega
    rw [htotal, hparity] at hadj
    simpa only [hindex, Module.End.one_apply] using hadj

/-- The BPZ form is invariant under the original physical Lie bracket on degree one. -/
theorem physicalBPZ_invariant (a b c : DegreeOne) :
    physicalBPZ ⁅a, b⁆ c = physicalBPZ a ⁅b, c⁆ :=
  physicalBPZ_invariant_of_basis weightOneBasisAdjunction a b c

#print axioms weightOneBasisAdjunction
#print axioms physicalBPZ_invariant

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalInvariantBPZ
