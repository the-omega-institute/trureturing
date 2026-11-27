/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedRightJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedRightJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed Borcherds for the native cubic right insertion. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi

open scoped BigOperators VertexOperator
open LatticeAllStateField (Y stateField_covariance)
open LatticeSugawaraConformal (translation)
open NativeStandardThirdLift (standardLift_compatible)
open P48qNativeConformalSector (fixedStates sector fixedField fixedProduct fixedField_borcherds)
open P48qNativeFixedRightInsertion (rightInsertion sectorTranslation)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open StateField.BorcherdsPermutations
open StateField.SkewSymmetry (reversalTerm reversal_finite)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private mem_fixedStates_iff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private fixedInsertion fixedField_translation_commutator from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion
-- The induction used in OriginalOrbifoldJacobi.defect_vmv is independent of the carrier.
open private choose_cast divided_mode_of_step from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldJacobi
open private finsum_range from D5.S3.VertexAlgebra.StateField.BorcherdsPermutations

noncomputable section

private def sourceMode (n : ℤ) : fixedStates →ₗ[ℂ] Module.End ℂ fixedStates := by
  let mode := modesOfStateField (Y lattice) n
  have h (a b : fixedStates) : (fixedProduct a b n).val = mode a.val b.val := rfl
  refine LinearMap.mk₂ ℂ (fun a b => fixedProduct a b n) ?_ ?_ ?_ ?_
  · intro a b c
    apply Subtype.ext
    simp only [Submodule.coe_add, h, LinearMap.map_add₂]
  · intro z a b
    apply Subtype.ext
    simp only [Submodule.coe_smul, h, LinearMap.map_smul₂]
  · intro a b c
    apply Subtype.ext
    simp only [Submodule.coe_add, h, map_add]
  · intro z a b
    apply Subtype.ext
    simp only [Submodule.coe_smul, h, map_smul]

private def sectorMode (s : Fin 3) (n : ℤ) : fixedStates →ₗ[ℂ] Module.End ℂ (sector s) :=
  (LinearMap.proj n).comp (VertexOperator.ncoeff.comp (fixedField s))

private theorem fixedInsertion_coeff (s : Fin 3) (a : fixedStates) (u : sector s) (k : ℤ) :
    (fixedInsertion s a u).coeff k = HVertexOperator.coeff (fixedField s a) k u := rfl

private abbrev rightTerm (s : Fin 3) (n : ℤ) (u : sector s) (a : fixedStates) :=
  reversalTerm (sectorTranslation s) (fixedInsertion s a u) (-n - 1)

private def rightMode (s : Fin 3) (n : ℤ) : sector s →ₗ[ℂ] fixedStates →ₗ[ℂ] sector s :=
  LinearMap.mk₂ ℂ (fun u a => (rightInsertion s u a).coeff (-n - 1))
    (by
      intro u v a
      change (∑ᶠ j, rightTerm s n (u + v) a j) =
        (∑ᶠ j, rightTerm s n u a j) + ∑ᶠ j, rightTerm s n v a j
      simpa only [rightTerm, reversalTerm, fixedInsertion_coeff, map_add, smul_add] using
        (finsum_add_distrib
          (reversal_finite (sectorTranslation s) (fixedInsertion s a u) (-n - 1))
          (reversal_finite (sectorTranslation s) (fixedInsertion s a v) (-n - 1))))
    (by
      intro z u a
      change (∑ᶠ j, rightTerm s n (z • u) a j) = z • ∑ᶠ j, rightTerm s n u a j
      simpa only [rightTerm, reversalTerm, fixedInsertion_coeff, map_smul, RingHom.id_apply,
        smul_smul, mul_comm z] using (smul_finsum z (rightTerm s n u a)).symm)
    (by
      intro u a b
      change (∑ᶠ j, rightTerm s n u (a + b) j) =
        (∑ᶠ j, rightTerm s n u a j) + ∑ᶠ j, rightTerm s n u b j
      simpa only [rightTerm, reversalTerm, fixedInsertion_coeff, map_add, Pi.add_apply,
        LinearMap.add_apply, smul_add] using
        (finsum_add_distrib
          (reversal_finite (sectorTranslation s) (fixedInsertion s a u) (-n - 1))
          (reversal_finite (sectorTranslation s) (fixedInsertion s b u) (-n - 1))))
    (by
      intro z u a
      change (∑ᶠ j, rightTerm s n u (z • a) j) = z • ∑ᶠ j, rightTerm s n u a j
      simpa only [rightTerm, reversalTerm, fixedInsertion_coeff, map_smul, Pi.smul_apply,
        LinearMap.smul_apply, RingHom.id_apply, smul_smul, mul_comm z] using
        (smul_finsum z (rightTerm s n u a)).symm)

variable (s : Fin 3)

local notation "aIn" => (LinearMap.inl ℂ fixedStates (sector s))
local notation "mIn" => (LinearMap.inr ℂ fixedStates (sector s))
local notation "prA" => (LinearMap.fst ℂ fixedStates (sector s))
local notation "prM" => (LinearMap.snd ℂ fixedStates (sector s))

/-- The product carrier used for the last-input permutation. -/
private def mixedModes : Modes (fixedStates × sector s) := fun n =>
  ((sourceMode n).compl₁₂ prA prA).compr₂ aIn +
  ((sectorMode s n).compl₁₂ prA prM).compr₂ mIn +
  ((rightMode s n).compl₁₂ prM prA).compr₂ mIn

local notation "μ" => mixedModes s

private theorem mixedModes_apply (n : ℤ) (x y : fixedStates × sector s) :
    μ n x y = (fixedProduct x.1 y.1 n, sectorMode s n x.1 y.2 + rightMode s n x.2 y.1) := by
  change (sourceMode n x.1 y.1, 0) + (0, sectorMode s n x.1 y.2) +
    (0, rightMode s n x.2 y.1) = _
  change (sourceMode n x.1 y.1 + 0 + 0,
    0 + sectorMode s n x.1 y.2 + rightMode s n x.2 y.1) = _
  simp only [add_zero, zero_add] <;> rfl

private theorem mode_a (n : ℤ) (a : fixedStates) (x : fixedStates × sector s) :
    μ n (aIn a) x = (sourceMode n a x.1, sectorMode s n a x.2) := by
  rw [mixedModes_apply]
  change (sourceMode n a x.1, sectorMode s n a x.2 + rightMode s n 0 x.1) = _
  simp only [LinearMap.map_zero₂, add_zero]

private theorem mode_aa (n : ℤ) (a b : fixedStates) :
    μ n (aIn a) (aIn b) = aIn (fixedProduct a b n) := by
  rw [mode_a]
  change (fixedProduct a b n, sectorMode s n a 0) = (fixedProduct a b n, 0)
  rw [map_zero]

private theorem mode_am (n : ℤ) (a : fixedStates) (u : sector s) :
    μ n (aIn a) (mIn u) = mIn ((fixedField s a)[[n]] u) := by
  rw [mode_a]
  change (sourceMode n a 0, sectorMode s n a u) = (0, sectorMode s n a u)
  rw [map_zero]

private theorem mode_ma (n : ℤ) (u : sector s) (a : fixedStates) :
    μ n (mIn u) (aIn a) = mIn ((rightInsertion s u a).coeff (-n - 1)) := by
  rw [mixedModes_apply]
  change (sourceMode n 0 a, sectorMode s n 0 0 + rightMode s n u a) =
    (0, rightMode s n u a)
  simp only [LinearMap.map_zero₂, zero_add]

private theorem truncation : LowerTruncated μ := by
  rintro ⟨a, u⟩ ⟨b, v⟩
  let A := (HahnModule.of ℂ).symm (Y lattice a.val b.val)
  let B := fixedInsertion s a v
  let R := rightInsertion s u b
  refine ⟨max (-A.order) (max (-B.order) (-R.order)), ?_⟩
  intro n hn
  have ha : -A.order ≤ n := le_trans (le_max_left _ _) hn
  have hb : -B.order ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hr : -R.order ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hA : fixedProduct a b n = 0 := by
    apply Subtype.ext
    change ((Y lattice a.val)[[n]]) b.val = 0
    exact VertexOperator.ncoeff_eq_zero_of_lt_order (Y lattice a.val) n b.val
      (show -n - 1 < A.order by omega)
  have hB : sectorMode s n a v = 0 := by
    exact VertexOperator.ncoeff_eq_zero_of_lt_order (fixedField s a) n v
      (show -n - 1 < B.order by omega)
  have hR : rightMode s n u b = 0 := by
    change R.coeff (-n - 1) = 0
    exact HahnSeries.coeff_eq_zero_of_lt_order (by omega)
  rw [mixedModes_apply]
  change (fixedProduct a b n, sectorMode s n a v + rightMode s n u b) = (0, 0)
  rw [hA, hB, hR, add_zero]

private def sourceTranslation : Module.End ℂ fixedStates :=
  (translation lattice).restrict (fun a ha => (mem_fixedStates_iff _).mpr (by
    rw [(standardLift_compatible lattice g g_cube g_isometry).2.2,
      (mem_fixedStates_iff a).mp ha]))

private def mixedTranslation : Module.End ℂ (fixedStates × sector s) :=
  sourceTranslation.prodMap (sectorTranslation s)

local notation "T" => mixedTranslation s

private theorem source_mode_step (a b : fixedStates) (n : ℤ) :
    sourceMode n a (sourceTranslation b) =
      sourceTranslation (sourceMode n a b) + (n : ℂ) • sourceMode (n - 1) a b := by
  have h := LinearMap.congr_fun (stateField_covariance lattice a.val n) b.val
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  apply Subtype.ext
  change ((Y lattice a.val)[[n]]) (translation lattice b.val) =
    translation lattice (((Y lattice a.val)[[n]]) b.val) +
      (n : ℂ) • (((Y lattice a.val)[[n - 1]]) b.val)
  rw [← sub_neg_eq_add, ← neg_smul, ← h, sub_sub_cancel]

private theorem sector_mode_step (a : fixedStates) (u : sector s) (n : ℤ) :
    sectorMode s n a (sectorTranslation s u) =
      sectorTranslation s (sectorMode s n a u) + (n : ℂ) • sectorMode s (n - 1) a u := by
  have h := fixedField_translation_commutator s a u (-n - 1)
  have hindex : -n - 1 + 1 = -n := by omega
  rw [hindex, Int.cast_neg] at h
  have hprev : HVertexOperator.coeff (fixedField s a) (-n) u = sectorMode s (n - 1) a u := by
    change HVertexOperator.coeff (fixedField s a) (-n) u =
      HVertexOperator.coeff (fixedField s a) (-(n - 1) - 1) u
    rw [show -(n - 1) - 1 = -n by omega]
  rw [hprev] at h
  change sectorTranslation s (sectorMode s n a u) -
    sectorMode s n a (sectorTranslation s u) =
      -(n : ℂ) • sectorMode s (n - 1) a u at h
  rw [← sub_neg_eq_add, ← neg_smul, ← h, sub_sub_cancel]

private theorem divided_mode_translation (a : fixedStates) :
    DividedModeTranslation μ T (aIn a) := by
  apply divided_mode_of_step
  intro n x
  simp only [mode_a, mixedTranslation, LinearMap.prodMap_apply]
  exact Prod.ext (source_mode_step a x.1 n) (sector_mode_step s a x.2 n)

private theorem pow_m (j : ℕ) (u : sector s) :
    (T ^ j) (mIn u) = mIn ((sectorTranslation s ^ j) u) := by
  induction j with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    change (sourceTranslation 0, _) = ((0 : fixedStates), _)
    rw [map_zero]

private theorem smul_m (z : ℂ) (u : sector s) : z • mIn u = mIn (z • u) :=
  (map_smul mIn z u).symm

private theorem sum_m (f : ℕ → sector s) :
    mIn (∑ᶠ j, f j) = ∑ᶠ j, mIn (f j) :=
  (mIn : sector s →ₗ[ℂ] fixedStates × sector s).toAddMonoidHom.map_finsum_of_injective
    LinearMap.inr_injective f

private theorem skew_ma (u : sector s) (a : fixedStates) : SkewAt μ T (mIn u) (aIn a) := by
  intro n
  simp only [mode_ma, mode_am, dividedTranslation, LinearMap.smul_apply, pow_m,
    smul_m, smul_smul]
  change mIn (∑ᶠ j, rightTerm s n u a j) = _
  rw [sum_m]
  apply finsum_congr
  intro j
  apply congrArg mIn
  have hindex : -n - 1 - (j : ℤ) = -(n + j) - 1 := by omega
  have hsign : (-1 : ℂ) ^ (-(n + (j : ℤ)) - 1) = epsilon (n + j + 1) := by
    rw [epsilon, show -(n + (j : ℤ)) - 1 = -(n + j + 1) by omega,
      zpow_neg, ← inv_zpow]
    norm_num
  simp only [rightTerm, reversalTerm, hindex, hsign, fixedInsertion_coeff, div_eq_mul_inv,
    VertexOperator.ncoeff_apply]

private theorem defect_aam (a b : fixedStates) (u : sector s) (p q r : ℤ) :
    defect μ (aIn a) (aIn b) (mIn u) p q r = 0 := by
  obtain ⟨N, hcut, hB⟩ := fixedField_borcherds s a b
  have hIter :
      (∑ᶠ i : ℕ, integerBinomial p i •
        (fixedField s (fixedProduct a b (r + i)))[[p + q - i]] u) =
      ∑ i ∈ Finset.range ((N : ℤ) - r).toNat, Ring.choose (p : ℂ) i •
        (fixedField s (fixedProduct a b (r + i)))[[p + q - i]] u := by
    rw [finsum_range (N := ((N : ℤ) - r).toNat)]
    · simp only [choose_cast]
    · intro i hi
      rw [hcut _ (by omega), map_zero, VertexOperator.ncoeff_apply,
        Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  simp only [defect, product, iterate, mode_aa, mode_am, smul_m, ← sum_m, ← map_sub]
  rw [hIter, hB p q r u, sub_self, map_zero]

private theorem finite_of_inr {f : ℕ → sector s}
    (h : Function.HasFiniteSupport (fun i => mIn (f i))) : Function.HasFiniteSupport f := by
  apply h.subset
  intro i hi hz
  exact hi (LinearMap.inr_injective (hz.trans (map_zero mIn).symm))

/-- Mixed Borcherds for the actual right insertion in each cubic rotation sector.
The iterate and the two product summands have finite support individually. -/
theorem rightInsertion_borcherds (a b : fixedStates) (u : sector s) (p q r : ℤ) :
    let R (n : ℤ) (v : sector s) (c : fixedStates) :=
      (rightInsertion s v c).coeff (-n - 1)
    let left : ℕ → sector s := fun i =>
      integerBinomial p i • R (p + q - i) ((fixedField s a)[[r + i]] u) b
    let first : ℕ → sector s := fun i =>
      ((-1 : ℂ) ^ i * integerBinomial r i) • (fixedField s a)[[p + r - i]] (R (q + i) u b)
    let second : ℕ → sector s := fun i =>
      ((-1 : ℂ) ^ i * integerBinomial r i) •
        (epsilon r • R (q + r - i) u (fixedProduct a b (p + i)))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * integerBinomial r i) •
          ((fixedField s a)[[p + r - i]] (R (q + i) u b) -
            epsilon r • R (q + r - i) u (fixedProduct a b (p + i))) := by
  have hzero : defect μ (aIn a) (mIn u) (aIn b) p q r = 0 := by
    rw [(defect_swap_last μ (truncation s) (aIn a) (mIn u) (aIn b) p q r
      (divided_mode_translation s a) (skew_ma s u b)
      (fun i => by rw [mode_am]; exact skew_ma s _ b)
      (fun i => by rw [mode_aa]; exact skew_ma s u _)).2]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [defect_aam s a b u, map_zero]
  obtain ⟨hl, hf, hs, hsum⟩ :=
    (defect_eq_zero_iff_borcherds μ (truncation s) _ _ _ _ _ _).mp hzero
  simp only [mode_aa, mode_am, mode_ma, smul_m] at hl hf hs
  simp only [mode_aa, mode_am, mode_ma, smul_m, ← map_sub, ← sum_m] at hsum
  exact ⟨finite_of_inr s hl, finite_of_inr s hf, finite_of_inr s hs, LinearMap.inr_injective hsum⟩

#print axioms rightInsertion_borcherds

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightJacobi
