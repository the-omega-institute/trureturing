/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedInvertedIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedInvertedIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Divided L(1) covariance of actual P48q fixed-field modes on the twisted sectors. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedInvertedIterate

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalWard (omega_product)
open LatticeSugawaraCurrents (sugawaraMode)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedOmega fixedProduct fixedField_borcherds)
open P48qTwistedChargeAction (lattice)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private fixedField_translate_coeff signedBinomial_zero_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion
open private sourceMode sectorMode from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
open private sourceLOne_pow_weight dividedAd_modes_of_ward from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeSourceMobius
open private dividedTranslation_mode_of_dividedAd from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeInvertedIterate

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "L₀" => sugawaraMode lattice (actualInverse lattice) 0
local notation "L₁" => sugawaraMode lattice (actualInverse lattice) 1

/-- The normalized conformal mode `ω₂` on the fixed source algebra. -/
def fixedSourceLOne : Module.End ℂ fixedStates := sourceMode 2 fixedOmega

/-- The normalized conformal mode `ω₂` on the actual twisted sector. -/
def sectorLOne (s : Fin 3) : Module.End ℂ (sector s) := (fixedField s fixedOmega)[[2]]

private theorem fixedSourceLOne_val (a : fixedStates) : (fixedSourceLOne a).val = L₁ a.val :=
  omega_product lattice (actualInverse lattice) a.val 2

private theorem fixedSourceLOne_pow_val (i : ℕ) (a : fixedStates) :
    ((fixedSourceLOne ^ i) a).val = (L₁ ^ i) a.val := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [pow_succ', Module.End.mul_apply, fixedSourceLOne_val, ih]

/-- The native Ward commutator on the normalized fixed-field modes. In the
Borcherds sum the derivative term has index `m + 2` before differentiation. -/
theorem sectorLOne_mode_commutator (s : Fin 3) (a : fixedStates) (e : ℂ)
    (ha : L₀ a.val = e • a.val) (m : ℤ) :
    sectorLOne s * ((fixedField s a)[[m]]) - ((fixedField s a)[[m]]) * sectorLOne s =
      ((fixedField s (fixedSourceLOne a))[[m]]) +
        (2 * e - (m : ℂ) - 2) • ((fixedField s a)[[m + 1]]) := by
  apply LinearMap.ext
  intro u
  obtain ⟨N, hcut, hB⟩ := fixedField_borcherds s fixedOmega a
  let term (j : ℕ) : sector s :=
    Ring.choose (2 : ℂ) j • ((fixedField s (fixedProduct fixedOmega a j))[[2 + m - j]]) u
  have h := hB 2 m 0 u
  simp only [signedBinomial_zero_sum, epsilon, zpow_zero, one_smul, Nat.cast_zero,
    Int.toNat_natCast, add_zero, zero_add, sub_zero] at h
  change sectorLOne s (((fixedField s a)[[m]]) u) -
    ((fixedField s a)[[m]]) (sectorLOne s u) = ∑ j ∈ Finset.range N, term j at h
  have support (k : ℕ) (hz : ∀ j ≥ k, term j = 0) :
      Function.support term ⊆ ↑(Finset.range k) := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge (fun hkj => hj (hz j hkj)))
  have hN := support N (by
    intro j hj
    simp only [term, hcut j (by exact_mod_cast hj), map_zero, VertexOperator.ncoeff_apply,
      Pi.zero_apply, LinearMap.zero_apply, smul_zero])
  have hThree := support 3 (by
    intro j hj
    have hChoose : Ring.choose (2 : ℂ) j = 0 := by
      change Ring.choose ((2 : ℕ) : ℂ) j = 0
      rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show 2 < j by omega), Nat.cast_zero]
    simp only [term, hChoose, zero_smul])
  rw [← finsum_eq_sum_of_support_subset term hN,
    finsum_eq_sum_of_support_subset term hThree] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have h0 : term 0 = -((m + 2 : ℤ) : ℂ) • ((fixedField s a)[[m + 1]]) u := by
    have hDerivative := fixedField_translate_coeff s a u (-(m + 2) - 1)
    have hIndex : -(m + 2) - 1 + 1 = -(m + 1) - 1 := by omega
    have hScalar : ((-(m + 2) - 1 + 1 : ℤ) : ℂ) = -((m + 2 : ℤ) : ℂ) := by
      push_cast
      ring
    rw [hScalar, hIndex] at hDerivative
    simpa only [term, Ring.choose_zero_right, Nat.cast_zero, sub_zero, one_smul,
      show (2 : ℤ) + m = m + 2 by omega, VertexOperator.ncoeff_apply] using hDerivative
  have hWeight : fixedProduct fixedOmega a 1 = e • a := by
    apply Subtype.ext
    exact (omega_product lattice (actualInverse lattice) a.val 1).trans ha
  have h1 : term 1 = (2 * e) • ((fixedField s a)[[m + 1]]) u := by
    change Ring.choose (2 : ℂ) 1 • sectorMode s (2 + m - 1) (fixedProduct fixedOmega a 1) u = _
    rw [show (2 : ℤ) + m - 1 = m + 1 by omega, hWeight, map_smul, LinearMap.smul_apply,
      smul_smul, Ring.choose_one_right] <;> rfl
  have h2 : term 2 = ((fixedField s (fixedSourceLOne a))[[m]]) u := by
    have hChoose : Ring.choose (2 : ℂ) 2 = 1 := by
      change Ring.choose ((2 : ℕ) : ℂ) 2 = 1
      rw [Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    change Ring.choose (2 : ℂ) 2 •
      ((fixedField s (fixedSourceLOne a))[[2 + m - 2]]) u = _
    rw [hChoose, one_smul, show (2 : ℤ) + m - 2 = m by omega]
  rw [h0, h1, h2, ← add_smul] at h
  have hScalar : -((m + 2 : ℤ) : ℂ) + 2 * e = 2 * e - (m : ℂ) - 2 := by
    push_cast
    ring
  rw [hScalar, add_comm] at h
  exact h

/-- The finite coefficient identity for inversion of a native fixed-field
iterate, with a homogeneous source state and arbitrary twisted input. -/
theorem sectorLOne_divided_inverted_iterate (s : Fin 3) (a : fixedStates) (u : sector s)
    (e : ℤ) (ha : L₀ a.val = (e : ℂ) • a.val) (m : ℤ) (r : ℕ) :
    dividedTranslation (sectorLOne s) r (((fixedField s a)[[m]]) u) =
      ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r - i + 1),
        integerBinomial (2 * e - m - (i : ℤ) - 2) (r - i - j) •
          ((fixedField s (dividedTranslation fixedSourceLOne i a))[[m + (r : ℤ) - (i : ℤ) - (j : ℤ)]])
            (dividedTranslation (sectorLOne s) j u) := by
  apply dividedTranslation_mode_of_dividedAd fixedSourceLOne (sectorLOne s) (sectorMode s)
    a u e m _ r
  intro n
  apply dividedAd_modes_of_ward fixedSourceLOne (sectorLOne s) (sectorMode s) a e m _ n
  intro i q
  have hWeight : L₀ (((fixedSourceLOne ^ i) a).val) =
      ((e : ℂ) - (i : ℂ)) • ((fixedSourceLOne ^ i) a).val := by
    rw [fixedSourceLOne_pow_val]
    exact sourceLOne_pow_weight a.val (e : ℂ) ha i
  exact sectorLOne_mode_commutator s _ _ hWeight q

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedInvertedIterate
