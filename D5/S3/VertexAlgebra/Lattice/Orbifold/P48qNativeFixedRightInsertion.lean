/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedRightInsertion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeFixedRightInsertion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic right insertion on the actual fixed module with vacuum creation and translation. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePositiveSkew
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeActualConformalState (omega)
open LatticeActualConformalWard (omega_product)
open LatticeActualVertexAlgebra (translation_as_mode)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeSugawaraConformal (sugawaraMode_minus_one_eq_translation)
open NativeStandardThirdLift (standardLift)
open P48qNativeConformalSector
  (fixedStates sector fixedField fixedField_coeff_val fixedVacuum fixedField_vacuum_coeff
    fixedOmega fixedProduct fixedField_borcherds)
open P48qNativePositiveSkew
  (cubicHalfTurn cubicHalfTurn_cube nativeTranslation nativeInsertion nativeSkew
    positiveSkew_coeff)
open P48qNativeVirasoro (native_vacuum_minus_two_mode)
open P48qThirdTwistedField (State)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qAllJetWickField (nativeField)
open StateField.BorcherdsPermutations (dividedTranslation)
open StateField.SkewSymmetry (reversal reversalTerm reversal_finite)
open StateFieldResidueReconstruction (epsilon integerBinomial)
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private lift_fixed from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private skewTerm from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePositiveSkew

noncomputable section

local notation "C" => HVertexOperator.coeff
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The conformal mode `L(-1)` on the actual fixed module. -/
def sectorTranslation (s : Fin 3) : Module.End ℂ (sector s) :=
  C (fixedField s fixedOmega) (-1)

private theorem sectorTranslation_val (s : Fin 3) (u : sector s) :
    (sectorTranslation s u).val = nativeTranslation u.val := by
  exact fixedField_coeff_val s fixedOmega (-1) u

private theorem sectorTranslation_pow_val (s : Fin 3) (j : ℕ) (u : sector s) :
    ((sectorTranslation s ^ j) u).val = (nativeTranslation ^ j) u.val := by
  induction j with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ j ih => simp only [pow_succ', Module.End.mul_apply, sectorTranslation_val, ih]

private def fixedInsertion (s : Fin 3) (a : fixedStates) (u : sector s) :
    HahnSeries ℤ (sector s) :=
  (HahnModule.of ℂ).symm (fixedField s a u)

/-- Reverse the actual fixed-module insertion by the integral half-turn
and the divided powers of the restricted conformal translation. -/
def rightInsertion (s : Fin 3) (u : sector s) (a : fixedStates) :
    HahnSeries ℤ (sector s) :=
  reversal (sectorTranslation s) (fixedInsertion s a u)

/-- The cubic half-turn on the original field gives the integral right insertion
on the same rotation sector. All other cover coefficients vanish. -/
theorem nativeSkew_fixedInsertion (s : Fin 3) (u : sector s) (a : fixedStates) (k : ℤ) :
    (nativeSkew (nativeInsertion a.val u.val)).coeff k =
      if k % 3 = 0 then ((rightInsertion s u a).coeff (k / 3)).val else 0 := by
  by_cases hk : k % 3 = 0
  · rw [if_pos hk]
    let n := k / 3
    have hkn : k = 3 * n := by dsimp [n]; omega
    change (nativeSkew (nativeInsertion a.val u.val)).coeff k =
      ((rightInsertion s u a).coeff n).val
    rw [hkn]
    let incl : sector s →ₗ[ℂ] State := (sector s).subtype
    let A := fixedInsertion s a u
    let T := sectorTranslation s
    change (∑ᶠ j : ℕ, skewTerm 3 cubicHalfTurn nativeTranslation
        (nativeInsertion a.val u.val) (3 * n) j) =
      incl (∑ᶠ j : ℕ, reversalTerm T A n j)
    rw [map_finsum incl (reversal_finite T A n)]
    apply finsum_congr
    intro j
    have hphase (m : ℤ) : cubicHalfTurn ^ (3 * m) = (-1 : ℂ) ^ m := by
      have hcube : cubicHalfTurn ^ (3 : ℤ) = -1 :=
        (zpow_natCast cubicHalfTurn (3 : ℕ)).trans cubicHalfTurn_cube
      rw [zpow_mul, hcube]
    have hcoeff (m : ℤ) :
        (A.coeff m).val = (nativeInsertion a.val u.val).coeff (3 * m) :=
      fixedField_coeff_val s a m u
    simp only [skewTerm, Nat.cast_ofNat]
    rw [show 3 * n - (3 : ℤ) * (j : ℤ) = 3 * (n - (j : ℤ)) by ring,
      hphase, ← hcoeff (n - (j : ℤ))]
    change (-1 : ℂ) ^ (n - (j : ℤ)) •
        dividedTranslation nativeTranslation j (A.coeff (n - (j : ℤ))).val =
      (reversalTerm T A n j).val
    simp only [dividedTranslation, reversalTerm, LinearMap.smul_apply, Submodule.coe_smul,
      smul_smul, div_eq_mul_inv, T, sectorTranslation_pow_val]
  · rw [if_neg hk, nativeSkew, positiveSkew_coeff]
    apply Finset.sum_eq_zero
    intro j _
    have ha : σ a.val = ζ ^ (0 : ℤ) • a.val := by
      simpa only [zpow_zero, one_smul] using lift_fixed a
    have hzero : (nativeInsertion a.val u.val).coeff (k - (3 : ℤ) * (j : ℤ)) = 0 := by
      change C (nativeField a.val) (k - 3 * (j : ℤ)) u.val = 0
      rw [P48qNativeCurrentLocality.nativeField_inResidue a.val 0 ha _ (by omega),
        LinearMap.zero_apply]
    simp only [Nat.cast_ofNat, hzero, map_zero, smul_zero]

/-- The actual fixed vacuum gives `exp(z L(-1)) u` in the right argument.
The negative integral powers vanish, and the constant coefficient is `u`. -/
theorem rightInsertion_vacuum_coeff (s : Fin 3) (u : sector s) (k : ℤ) :
    (rightInsertion s u fixedVacuum).coeff k =
      if k < 0 then 0 else dividedTranslation (sectorTranslation s) k.toNat u := by
  let T := sectorTranslation s
  let A := fixedInsertion s fixedVacuum u
  have hA (m : ℤ) : A.coeff m = if m = 0 then u else 0 := by
    change C (fixedField s fixedVacuum) m u = _
    rw [fixedField_vacuum_coeff]
    split <;> rfl
  change (∑ᶠ j : ℕ, reversalTerm T A k j) = _
  by_cases hk : k < 0
  · rw [if_pos hk]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hj : k - (j : ℤ) ≠ 0 := by omega
    simp only [reversalTerm, hA, if_neg hj, map_zero, smul_zero]
  · rw [if_neg hk, finsum_eq_single _ k.toNat]
    · have hj : k - (k.toNat : ℤ) = 0 := by omega
      simp only [reversalTerm, hj, hA, ite_true, zpow_zero, one_div, dividedTranslation,
        LinearMap.smul_apply, T]
    · intro j hj
      have hindex : k - (j : ℤ) ≠ 0 := by omega
      simp only [reversalTerm, hA, if_neg hindex, map_zero, smul_zero]

private theorem conformal_zero_product_val (a : fixedStates) :
    (fixedProduct fixedOmega a 0).val = (fixedProduct a fixedVacuum (-2)).val := by
  change mu lattice (omega lattice (actualInverse lattice)) 0 a.val =
    mu lattice a.val (-2) (vacuum lattice)
  rw [omega_product, show (0 : ℤ) - 1 = -1 by decide,
    sugawaraMode_minus_one_eq_translation lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit),
    translation_as_mode] <;> rfl

private theorem fixedField_translate_coeff (s : Fin 3) (a : fixedStates) (u : sector s)
    (k : ℤ) : C (fixedField s (fixedProduct fixedOmega a 0)) k u =
      ((k + 1 : ℤ) : ℂ) • C (fixedField s a) (k + 1) u := by
  apply Subtype.ext
  simp only [Submodule.coe_smul, fixedField_coeff_val, conformal_zero_product_val]
  change C (nativeField (mu lattice a.val (-2) (vacuum lattice))) (3 * k) u.val =
    ((k + 1 : ℤ) : ℂ) • C (nativeField a.val) (3 * (k + 1)) u.val
  have h := native_vacuum_minus_two_mode a.val (lift_fixed a) (-k - 1)
  rw [show -3 * (-k - 1 + 1) = 3 * k by ring,
    show -3 * (-k - 1) = 3 * (k + 1) by ring,
    show -(((-k - 1 : ℤ) : ℂ)) = ((k + 1 : ℤ) : ℂ) by push_cast; ring] at h
  simpa only [LinearMap.smul_apply] using LinearMap.congr_fun h u.val

private theorem signedBinomial_zero_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → V) :
    (∑ᶠ j : ℕ, (((-1 : ℂ) ^ j) * integerBinomial 0 j) • f j) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro j hj
    simp only [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hj), Int.cast_zero,
      mul_zero, zero_smul]

private theorem fixedField_translation_commutator (s : Fin 3) (a : fixedStates)
    (u : sector s) (k : ℤ) :
    sectorTranslation s (C (fixedField s a) k u) -
      C (fixedField s a) k (sectorTranslation s u) =
        ((k + 1 : ℤ) : ℂ) • C (fixedField s a) (k + 1) u := by
  obtain ⟨N, hcut, hB⟩ := fixedField_borcherds s fixedOmega a
  let q : ℤ := -k - 1
  have h := hB 0 q 0 u
  simp only [signedBinomial_zero_sum, epsilon, zpow_zero, one_smul, Nat.cast_zero,
    Int.cast_zero, Int.toNat_natCast, add_zero, zero_add, sub_zero] at h
  have hsum : (∑ j ∈ Finset.range N, Ring.choose (0 : ℂ) j •
        ((fixedField s (fixedProduct fixedOmega a (j : ℤ)))[[q - (j : ℤ)]]) u) =
      ((fixedField s (fixedProduct fixedOmega a 0))[[q]]) u := by
    rw [Finset.sum_eq_single 0]
    · simp only [Ring.choose_zero_right, one_smul, Nat.cast_zero, sub_zero]
    · intro j _ hj
      rw [Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), zero_smul]
    · intro hzero
      have hN : ¬ 0 < N := fun hn => hzero (Finset.mem_range.mpr hn)
      have hz := hcut 0 (by omega)
      simp only [Nat.cast_zero, hz, map_zero, VertexOperator.ncoeff_apply,
        Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  rw [hsum] at h
  have hq : -q - 1 = k := by dsimp [q]; omega
  simp only [VertexOperator.ncoeff_apply, neg_zero, zero_sub, hq] at h
  exact h.trans (fixedField_translate_coeff s a u k)

/-- Translation in the twisted input differentiates the opposite-order
insertion in the physical coordinate `z`. -/
theorem rightInsertion_translation (s : Fin 3) (u : sector s) (a : fixedStates) (k : ℤ) :
    (rightInsertion s (sectorTranslation s u) a).coeff k =
      ((k + 1 : ℤ) : ℂ) • (rightInsertion s u a).coeff (k + 1) := by
  classical
  let T := sectorTranslation s
  let A := fixedInsertion s a u
  let B := fixedInsertion s a (T u)
  let c : ℂ := ((k + 1 : ℤ) : ℂ)
  let r := reversalTerm T A (k + 1)
  let w := fun j : ℕ => (j : ℂ) • r j
  have hterm (j : ℕ) : reversalTerm T B k j = w (j + 1) + (c - (j : ℂ)) • r j := by
    let m : ℤ := k - (j : ℤ)
    have hB : B.coeff m = T (A.coeff m) - ((m + 1 : ℤ) : ℂ) • A.coeff (m + 1) := by
      have h := fixedField_translation_commutator s a u m
      change T (A.coeff m) - B.coeff m = ((m + 1 : ℤ) : ℂ) • A.coeff (m + 1) at h
      rw [← h]
      abel
    have hnext : k + 1 - (j : ℤ) = m + 1 := by dsimp [m]; omega
    have hsucc : k + 1 - ((j + 1 : ℕ) : ℤ) = m := by dsimp [m]; omega
    have hphase : (-1 : ℂ) ^ (m + 1) = -((-1 : ℂ) ^ m) := by
      rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, mul_neg_one]
    have hcast : ((m + 1 : ℤ) : ℂ) = c - (j : ℂ) := by
      dsimp only [m, c]
      push_cast
      ring
    have hraise : ((j + 1 : ℕ) : ℂ) * ((-1 : ℂ) ^ m / ((j + 1).factorial : ℂ)) =
        ((-1 : ℂ) ^ m / (j.factorial : ℂ)) := by
      have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hjf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp [hj, hjf] <;> ring
    have hpow : (T ^ j) (T (A.coeff m)) = (T ^ (j + 1)) (A.coeff m) := by
      rw [pow_succ, Module.End.mul_apply]
    dsimp only [w, r, reversalTerm]
    rw [hnext, hsucc, show k - (j : ℤ) = m from rfl,
      hB, hphase, ← hcast, map_sub, map_smul, smul_sub, hpow]
    simp only [smul_smul, hraise, sub_eq_add_neg]
    rw [← neg_smul, show -(((-1 : ℂ) ^ m / (j.factorial : ℂ)) * ((m + 1 : ℤ) : ℂ)) =
      ((m + 1 : ℤ) : ℂ) * (-((-1 : ℂ) ^ m) / (j.factorial : ℂ)) by ring]
  let N := (k + 1 - A.order).toNat + 1
  have htail (j : ℕ) (hj : N ≤ j) : w j = 0 := by
    have hlt : k + 1 - (j : ℤ) < A.order := by dsimp [N] at hj; omega
    simp only [w, r, reversalTerm, HahnSeries.coeff_eq_zero_of_lt_order hlt,
      map_zero, smul_zero]
  have hzero : w 0 = 0 := by simp [w]
  have hwSupport : Function.support w ⊆ Finset.range N := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge (fun ht => hj (htail j ht)))
  have hsuccSupport : Function.support (fun j : ℕ => w (j + 1)) ⊆ Finset.range N := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_not_ge (fun ht => hj (htail (j + 1) (by omega))))
  have hshift : (∑ᶠ j : ℕ, w (j + 1)) = ∑ᶠ j : ℕ, w j := by
    rw [finsum_eq_sum_of_support_subset _ hsuccSupport,
      finsum_eq_sum_of_support_subset _ hwSupport]
    have h := Finset.sum_range_succ' w N
    rw [Finset.sum_range_succ, hzero, htail N le_rfl, add_zero, add_zero] at h
    exact h.symm
  have hr : Function.HasFiniteSupport r := reversal_finite T A (k + 1)
  have hw : Function.HasFiniteSupport w := (Finset.range N).finite_toSet.subset hwSupport
  have hs : Function.HasFiniteSupport (fun j : ℕ => w (j + 1)) :=
    (Finset.range N).finite_toSet.subset hsuccSupport
  have hd : Function.HasFiniteSupport (fun j : ℕ => (c - (j : ℂ)) • r j) :=
    hr.subset (Function.support_smul_subset_right (fun j : ℕ => c - (j : ℂ)) r)
  have hc : Function.HasFiniteSupport (fun j : ℕ => c • r j) :=
    hr.subset (Function.support_smul_subset_right (fun _ : ℕ => c) r)
  change (∑ᶠ j : ℕ, reversalTerm T B k j) = c • (∑ᶠ j : ℕ, r j)
  simp_rw [hterm]
  rw [finsum_add_distrib hs hd, hshift]
  simp_rw [sub_smul]
  change (∑ᶠ j : ℕ, w j) + (∑ᶠ j : ℕ, (c • r j - w j)) = c • (∑ᶠ j : ℕ, r j)
  rw [finsum_sub_distrib hc hw, ← smul_finsum' c hr]
  abel

/-- On the cubic cover the physical derivative is `(1/3) x⁻² ∂ₓ`.
Its coefficient at `x^(3k)` reads the coefficient at `x^(3k+3)`. -/
theorem nativeSkew_fixedInsertion_translation (s : Fin 3) (u : sector s)
    (a : fixedStates) (k : ℤ) :
    (nativeSkew (nativeInsertion a.val (nativeTranslation u.val))).coeff (3 * k) =
      ((k + 1 : ℤ) : ℂ) • (nativeSkew (nativeInsertion a.val u.val)).coeff (3 * (k + 1)) := by
  rw [← sectorTranslation_val s u]
  have hresidue (n : ℤ) : (3 * n) % 3 = 0 := by omega
  have hquotient (n : ℤ) : (3 * n) / 3 = n := by omega
  simp only [nativeSkew_fixedInsertion s (sectorTranslation s u) a,
    nativeSkew_fixedInsertion s u a, hresidue, if_pos, hquotient,
    rightInsertion_translation, Submodule.coe_smul]

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeFixedRightInsertion
