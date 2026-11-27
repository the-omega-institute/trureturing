/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeModeProductSpan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qNativeModeProductSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic twisted Borcherds reduces products of native modes on a vector to source iterate modes. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedFockIrreducibility
import OmegaBuild.Commands

/-! Pointwise mode-product reduction for the native cubic twisted action. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan

open scoped BigOperators VertexOperator
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeAllStateReconstruction (mu)
open LatticeGeneratingFieldLocality (Charge)
open LatticePositiveEnergy (actualL0_eigen_iff_grade gradeProjection gradeProjection_mem
  stateEnergies sum_gradeProjections)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField nativeField_ground)
open P48qChargedResidueProduct (mu_eigen)
open P48qFullEnergySpectrum (totalLZero_exact_eigenvalues)
open P48qNativeConformalSector (fixedStates sector fixedField fixedField_coeff_val)
open P48qNativeCurrentLocality (nativeField_inResidue stripResidue stripResidue_coeff)
open P48qNativeGradingRotation (gradingIndex gradingRotation gradingRotation_coeff
  gradingRotation_nativeField_coeff totalWeight_eq_gradingIndex)
open P48qNativeMonodromy (currentAlong nativeField_action_coeff nativeField_current)
open P48qNativeResidueIterate (nativeField_twisted_borcherds)
open P48qThirdTwistedField (Cartan State fieldCoeff fixedDualBases)
open P48qTwistedChargeAction (lattice g g_cube g_isometry)
open P48qTwistedFockIrreducibility (current_charged_coeff_irreducible)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open P48qTwistedHeisenberg (mode currentField_coeff)
open P48qTwistedStateEnergy (totalLZero)
open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (integerBinomial)
open private zeta_zpow_eq_iff from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct
open private gram_det_unit from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private mem_fixedStates_iff fixedProjection fixedProjection_fixed lift_sourceLZero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalSector
open private fourier_sum liftProject liftProject_eigen from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality
open private weight_eq_of_coeff_ne_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

noncomputable section

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff
local notation "L" => sugawaraMode lattice (actualInverse lattice) 0

private theorem nativeMode_truncation (a : NativeStates) (s : ℤ) (v : State) :
    ∃ cutoff : ℤ, ∀ k ≥ cutoff, C (nativeField a) (s - 3 * (k + 1)) v = 0 := by
  let lower := ((HahnModule.of ℂ).symm (nativeField a v)).order
  refine ⟨max 0 (s - lower), ?_⟩
  intro k hk
  have hk₀ : 0 ≤ k := (le_max_left 0 (s - lower)).trans hk
  have hk₁ : s - lower ≤ k := (le_max_right 0 (s - lower)).trans hk
  apply VertexOperator.coeff_eq_zero_of_lt_order
  change s - 3 * (k + 1) < lower
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- A vectorwise descent with the first mode index universally quantified.
The submodule only needs to contain the actual source iterates on the given vector. -/
private theorem product_mem_of_iterates
    (a b : NativeStates) (s t : ℤ)
    (ha : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b)
    (v : State) (S : Submodule ℂ State)
    (iterates : ∀ n m : ℤ, C (nativeField (mu lattice a n b))
      (s + t - 3 * (m + 1)) v ∈ S) (k q : ℤ) :
    C (nativeField a) (s - 3 * (k + 1))
      (C (nativeField b) (t - 3 * (q + 1)) v) ∈ S := by
  classical
  let product (k q : ℤ) : State :=
    C (nativeField a) (s - 3 * (k + 1))
      (C (nativeField b) (t - 3 * (q + 1)) v)
  obtain ⟨p, ha_zero⟩ := nativeMode_truncation a s v
  obtain ⟨cutoff, hb_zero⟩ := nativeMode_truncation b t v
  obtain ⟨N, hB⟩ := nativeField_twisted_borcherds a b s t ha hb
  let A := stripResidue (s - 3 * p) (nativeField a)
  let B := stripResidue t (nativeField b)
  have hA (m : ℤ) :
      VertexOperator.ncoeff A m = C (nativeField a) (s - 3 * (p + m + 1)) := by
    simp only [A, VertexOperator.ncoeff_apply, stripResidue_coeff]
    rw [show 3 * (-m - 1) + (s - 3 * p) = s - 3 * (p + m + 1) by omega]
  have hBm (m : ℤ) :
      VertexOperator.ncoeff B m = C (nativeField b) (t - 3 * (m + 1)) := by
    simp only [B, VertexOperator.ncoeff_apply, stripResidue_coeff]
    rw [show 3 * (-m - 1) + t = t - 3 * (m + 1) by omega]
  have descend (d : ℕ) :
      ∀ q : ℤ, (cutoff - q).toNat = d → ∀ k : ℤ, product k q ∈ S := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd k
      by_cases hq : cutoff ≤ q
      · dsimp only [product]
        rw [hb_zero q hq, map_zero]
        exact S.zero_mem
      have distance : (d : ℤ) = cutoff - q := by
        rw [← hd]
        exact Int.toNat_of_nonneg (by omega)
      -- The forward term at j = 0 is the desired product.
      let n : ℤ := k - p
      let first (j : ℕ) : State :=
        (((-1 : ℂ) ^ j) * integerBinomial n j) • product (k - j) (q + j)
      let iterate (j : ℕ) : State :=
        Ring.choose ((p : ℂ) - (s : ℂ) / 3) j •
          C (nativeField (mu lattice a (n + (j : ℤ)) b))
            (s + t - 3 * (p + q - (j : ℤ) + 1)) v
      have law := congrArg (fun T : Module.End ℂ State => T v) (hB p q n)
      change (VertexOperator.ncoeff (residueField 1 n A B).operator q) v = _ at law
      rw [(residueField 1 n A B).coefficient q v] at law
      have reverse_zero : residueRight n q A B v = 0 := by
        unfold residueRight
        apply finsum_eq_zero_of_forall_eq_zero
        intro j
        rw [hA, ha_zero (p + j) (by omega), map_zero, smul_zero]
      have forward_eq : residueLeft n q A B v = ∑ᶠ j : ℕ, first j := by
        unfold residueLeft
        apply finsum_congr
        intro j
        have hindex : p + (n - (j : ℤ)) = k - (j : ℤ) := by
          dsimp only [n]
          omega
        simp only [hA, hBm, hindex, first, product]
      have support : Function.support first ⊆ (↑(Finset.range (d + 1)) : Set ℕ) := by
        intro j hj
        by_contra outside
        simp only [Finset.mem_coe, Finset.mem_range] at outside
        have hqj : cutoff ≤ q + (j : ℤ) := by omega
        exact hj (by
          dsimp only [first, product]
          rw [hb_zero _ hqj, map_zero, smul_zero])
      have first_zero : first 0 = product k q := by
        simp only [first, pow_zero, integerBinomial, Ring.choose_zero_right, Int.cast_one,
          one_mul, one_smul, Nat.cast_zero, add_zero, sub_zero]
      have tail_mem : (∑ j ∈ Finset.range d, first (j + 1)) ∈ S := by
        apply S.sum_mem
        intro j _
        have smaller : (cutoff - (q + ((j + 1 : ℕ) : ℤ))).toNat < d := by omega
        dsimp only [first]
        apply S.smul_mem
        exact ih _ smaller _ rfl _
      rw [residueCoefficient, reverse_zero, smul_zero, sub_zero, forward_eq,
        finsum_eq_sum_of_support_subset _ support, Finset.sum_range_succ', first_zero] at law
      simp only [LinearMap.sum_apply, LinearMap.smul_apply] at law
      change _ = ∑ j ∈ Finset.range ((N : ℤ) - n).toNat, iterate j at law
      have iterate_sum_mem : (∑ j ∈ Finset.range ((N : ℤ) - n).toNat, iterate j) ∈ S := by
        apply S.sum_mem
        intro j _
        dsimp only [iterate]
        exact S.smul_mem _ (iterates (n + j) (p + q - j))
      have recover : product k q =
          (∑ j ∈ Finset.range ((N : ℤ) - n).toNat, iterate j) -
          (∑ j ∈ Finset.range d, first (j + 1)) :=
        eq_sub_iff_add_eq.mpr ((add_comm _ _).trans law)
      rw [recover]
      exact S.sub_mem iterate_sum_mem tail_mem
  exact descend (cutoff - q).toNat q rfl k

/-- Every ordered pair of native eigenfield modes on one vector lies in the span
of the modes of its actual source iterates on that same vector. -/
theorem mode_product_mem_iterate_span (a b : NativeStates) (s t : ℤ)
    (ha : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b) (v : State) (k q : ℤ) :
    C (nativeField a) (s - 3 * (k + 1))
      (C (nativeField b) (t - 3 * (q + 1)) v) ∈
        Submodule.span ℂ (Set.range fun index : ℤ × ℤ =>
          C (nativeField (mu lattice a index.1 b)) (s + t - 3 * (index.2 + 1)) v) := by
  let read (index : ℤ × ℤ) : State :=
    C (nativeField (mu lattice a index.1 b)) (s + t - 3 * (index.2 + 1)) v
  refine product_mem_of_iterates a b s t ha hb v (Submodule.span ℂ (Set.range read)) ?_ k q
  intro n m
  exact Submodule.subset_span (Set.mem_range_self (f := read) (n, m))

/-- The cyclic span of the integral fixed-field coefficients on a sector vector. -/
def fixedModeSpan (r : Fin 3) (v : sector r) : Submodule ℂ (sector r) :=
  Submodule.span ℂ (Set.range fun index : fixedStates × ℤ =>
    C (fixedField r index.1) index.2 v)

private theorem fixedMode_mem_span (r : Fin 3) (v : sector r) (a : fixedStates) (e : ℤ) :
    C (fixedField r a) e v ∈ fixedModeSpan r v := by
  apply Submodule.subset_span
  exact ⟨(a, e), rfl⟩

/-- A pair of native modes of total residue zero has a representative in the
cyclic span of the actual fixed-field action on the rotation sector. -/
theorem neutral_mode_product_mem_fixedModeSpan (a b : NativeStates) (s t : ℤ)
    (ha : σ a = ζ ^ s • a) (hb : σ b = ζ ^ t • b)
    (hneutral : (3 : ℤ) ∣ s + t) (r : Fin 3) (v : sector r) (k q : ℤ) :
    ∃ w ∈ fixedModeSpan r v,
      w.val = C (nativeField a) (s - 3 * (k + 1))
        (C (nativeField b) (t - 3 * (q + 1)) v.val) := by
  let S := (fixedModeSpan r v).map (sector r).subtype
  have hζ : ζ ^ (s + t) = 1 :=
    ((IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive :
      IsPrimitiveRoot ζ 3).zpow_eq_one_iff_dvd (s + t)).mpr hneutral
  obtain ⟨d, hd⟩ := hneutral
  have hprod := product_mem_of_iterates a b s t ha hb v.val S (by
    intro n m
    let x : fixedStates := ⟨mu lattice a n b, (mem_fixedStates_iff _).mpr (by
      rw [mu_eigen a b s t n ha hb, hζ, one_smul])⟩
    refine Submodule.mem_map.mpr ⟨C (fixedField r x) (d - (m + 1)) v,
      fixedMode_mem_span r v x (d - (m + 1)), ?_⟩
    change (C (fixedField r x) (d - (m + 1)) v).val =
      C (nativeField x.val) (s + t - 3 * (m + 1)) v.val
    rw [fixedField_coeff_val, show 3 * (d - (m + 1)) = s + t - 3 * (m + 1) by omega]) k q
  exact Submodule.mem_map.mp hprod

private def residueIndex (e : ℤ) : Fin 3 :=
  ⟨((-e) % 3).toNat, by omega⟩

private theorem residueIndex_class (e : ℤ) :
    (((residueIndex e).val * 2 : ℕ) : ℤ) % 3 = e % 3 := by
  have he : ((residueIndex e).val : ℤ) = (-e) % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  change (((residueIndex e).val * 2 : ℕ) : ℤ) ≡ e [ZMOD 3]
  rw [Int.modEq_iff_dvd]
  simp only [Nat.cast_mul, Nat.cast_ofNat, he]
  refine ⟨e + 2 * ((-e) / 3), ?_⟩
  omega

private theorem liftProject_eigen_int (r : Fin 3) (a : NativeStates) :
    σ (liftProject r a) = ζ ^ ((r.val * 2 : ℕ) : ℤ) • liftProject r a := by
  rw [zpow_natCast, pow_mul]
  exact liftProject_eigen r a

private theorem liftProject_residue_coeff (a : NativeStates) (e : ℤ) :
    C (nativeField (liftProject (residueIndex e) a)) e = C (nativeField a) e := by
  classical
  let read : NativeStates →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj e).comp HVertexOperator.coeff).comp nativeField
  have hsum : (∑ r : Fin 3, liftProject r a) = a := fourier_sum a (σ a) (σ (σ a))
  have hread := congrArg read hsum
  rw [map_sum] at hread
  change read (liftProject (residueIndex e) a) = read a
  rw [← hread]
  symm
  apply Finset.sum_eq_single_of_mem (residueIndex e) (Finset.mem_univ _)
  intro r _ hr
  change C (nativeField (liftProject r a)) e = 0
  apply nativeField_inResidue _ _ (liftProject_eigen_int r a) e
  intro he
  apply hr
  apply Fin.ext
  have h := residueIndex_class e
  have hrb := r.isLt
  have hib := (residueIndex e).isLt
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h he
  omega

private theorem liftProject_residue_eigen (a : NativeStates) (e : ℤ) :
    σ (liftProject (residueIndex e) a) = ζ ^ e • liftProject (residueIndex e) a := by
  have h := (zeta_zpow_eq_iff _ e).mpr (residueIndex_class e)
  simpa only [h] using liftProject_eigen_int (residueIndex e) a

private def nativeModeSpan (v : State) : Submodule ℂ State :=
  Submodule.span ℂ (Set.range fun index : NativeStates × ℤ =>
    C (nativeField index.1) index.2 v)

private theorem nativeMode_mem_span (v : State) (a : NativeStates) (e : ℤ) :
    C (nativeField a) e v ∈ nativeModeSpan v := by
  apply Submodule.subset_span
  exact ⟨(a, e), rfl⟩

private theorem self_mem_nativeModeSpan (v : State) : v ∈ nativeModeSpan v := by
  have h := nativeMode_mem_span v (Finsupp.single (0 : Charge lattice) 1) 0
  simpa only [nativeField_ground, concreteChargedField_zero_coeff, ite_true,
    LinearMap.id_apply] using h

private theorem nativeModeSpan_stable (v : State) (a : NativeStates) (e : ℤ)
    {w : State} (hw : w ∈ nativeModeSpan v) :
    C (nativeField a) e w ∈ nativeModeSpan v := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨b, f⟩, rfl⟩ := hw
    change C (nativeField a) e (C (nativeField b) f v) ∈ nativeModeSpan v
    let a' := liftProject (residueIndex e) a
    let b' := liftProject (residueIndex f) b
    have ha : C (nativeField a') e = C (nativeField a) e := liftProject_residue_coeff a e
    have hb : C (nativeField b') f = C (nativeField b) f := liftProject_residue_coeff b f
    have h := product_mem_of_iterates a' b' e f (liftProject_residue_eigen a e)
      (liftProject_residue_eigen b f) v (nativeModeSpan v)
      (fun n m => nativeMode_mem_span v (mu lattice a' n b') (e + f - 3 * (m + 1))) (-1) (-1)
    simpa only [neg_add_cancel, mul_zero, sub_zero, ha, hb] using h
  | zero => rw [map_zero]; exact (nativeModeSpan v).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (nativeModeSpan v).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (nativeModeSpan v).smul_mem c hx

private theorem nativeModeSpan_eq_top (v : State) (hv : v ≠ 0) :
    nativeModeSpan v = ⊤ := by
  let S := nativeModeSpan v
  have hcurrent (a : Cartan) (k : ℤ) (w : State) (hw : w ∈ S) : mode a k w ∈ S := by
    have h := nativeModeSpan_stable v (currentAlong lattice a) (-k - 3) hw
    simpa only [nativeField_current, currentField_coeff,
      show -(-k - 3) - 3 = k by omega] using h
  have hcharged (a : Charge lattice) (k : ℤ) (w : State) (hw : w ∈ S) :
      fieldCoeff fixedDualBases a k w ∈ S := by
    have h := nativeModeSpan_stable v (Finsupp.single a 1) k hw
    rw [nativeField_ground] at h
    exact h
  rcases current_charged_coeff_irreducible S hcurrent hcharged with hbot | htop
  · have hmem : v ∈ S := self_mem_nativeModeSpan v
    exact (hv (by simpa only [hbot, Submodule.mem_bot] using hmem)).elim
  · exact htop

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem gradingRotation_any_coeff (a : NativeStates) (e : ℤ) :
    gradingRotation * C (nativeField a) e =
      ζ ^ e • (C (nativeField a) e * gradingRotation) := by
  let read : NativeStates →ₗ[ℂ] Module.End ℂ State :=
    ((LinearMap.proj e).comp HVertexOperator.coeff).comp nativeField
  have hsum := congrArg read (sum_gradeProjections lattice a)
  rw [map_sum] at hsum
  change gradingRotation * read a = ζ ^ e • (read a * gradingRotation)
  rw [← hsum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro h _
  let x := gradeProjection lattice h a
  let y := liftProject (residueIndex e) x
  have hx : L x = (h : ℂ) • x :=
    (actualL0_eigen_iff_grade lattice (actualInverse lattice)
      (actualInverse_left lattice gram_det_unit) (actualInverse_right lattice gram_det_unit)
      h x).mpr (gradeProjection_mem lattice h a)
  have hcomm (u : NativeStates) : L (σ u) = σ (L u) := (lift_sourceLZero u).symm
  have hy : L y = (h : ℂ) • y := by
    dsimp only [y, liftProject]
    simp only [map_add, map_smul, hcomm, hx, smul_add, smul_smul] <;> ac_rfl
  change gradingRotation * C (nativeField x) e = ζ ^ e • (C (nativeField x) e * gradingRotation)
  rw [← liftProject_residue_coeff x e]
  exact gradingRotation_nativeField_coeff y e (liftProject_residue_eigen x e) e h hy

private def sectorAverage (r : Fin 3) : Module.End ℂ State :=
  let R := (ζ ^ r.val)⁻¹ • gradingRotation
  (3 : ℂ)⁻¹ • (1 + R + R * R)

private theorem sectorAverage_eq_self (r : Fin 3) (v : sector r) :
    sectorAverage r v.val = v.val := by
  let R : Module.End ℂ State := (ζ ^ r.val)⁻¹ • gradingRotation
  have hz : ζ ^ r.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ThirdTwistedChargeCocycle.zeta)
  have hv : gradingRotation v.val = ζ ^ r.val • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property
  have hR : R v.val = v.val := by
    change ((ζ ^ r.val)⁻¹ • gradingRotation : Module.End ℂ State) v.val = v.val
    rw [LinearMap.smul_apply, hv, smul_smul, inv_mul_cancel₀ hz, one_smul]
  change (3 : ℂ)⁻¹ • (v.val + R v.val + R (R v.val)) = v.val
  simp only [hR]
  have hthree : v.val + v.val + v.val = (3 : ℂ) • v.val := by module
  rw [hthree, smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

set_option maxRecDepth 4096 in
private theorem sectorAverage_native_coeff (r : Fin 3) (v : sector r)
    (a : NativeStates) (e : ℤ) :
    sectorAverage r (C (nativeField a) e v.val) =
      C (nativeField (fixedProjection a)) e v.val := by
  let R : Module.End ℂ State := (ζ ^ r.val)⁻¹ • gradingRotation
  have hz : ζ ^ r.val ≠ 0 := pow_ne_zero _ (Units.ne_zero ThirdTwistedChargeCocycle.zeta)
  have hv : gradingRotation v.val = ζ ^ r.val • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property
  have hR (b : NativeStates) : R (C (nativeField b) e v.val) =
      C (nativeField (σ b)) e v.val := by
    have h := LinearMap.congr_fun (gradingRotation_any_coeff b e) v.val
    change gradingRotation (C (nativeField b) e v.val) =
      ζ ^ e • C (nativeField b) e (gradingRotation v.val) at h
    rw [nativeField_action_coeff]
    change (ζ ^ r.val)⁻¹ • gradingRotation (C (nativeField b) e v.val) =
      ζ ^ e • (C (nativeField b) e v.val)
    rw [h, hv, map_smul, smul_comm (ζ ^ e) (ζ ^ r.val), smul_smul,
      inv_mul_cancel₀ hz, one_smul]
  change (3 : ℂ)⁻¹ • (C (nativeField a) e v.val + R (C (nativeField a) e v.val) +
    R (R (C (nativeField a) e v.val))) = C (nativeField (fixedProjection a)) e v.val
  rw [hR a, hR (σ a)]
  simp only [fixedProjection, map_smul, Pi.smul_apply, LinearMap.smul_apply,
    map_add, Pi.add_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

private theorem mem_fixedModeSpan_of_nativeModeSpan (r : Fin 3) (v w : sector r)
    (hw : w.val ∈ nativeModeSpan v.val) : w ∈ fixedModeSpan r v := by
  let S := (fixedModeSpan r v).map (sector r).subtype
  have hproject : nativeModeSpan v.val ≤ S.comap (sectorAverage r) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, e⟩, rfl⟩
    change sectorAverage r (C (nativeField a) e v.val) ∈ S
    rw [sectorAverage_native_coeff]
    have hf := fixedProjection_fixed a
    by_cases he : e % 3 = 0
    · let x : fixedStates := ⟨fixedProjection a, (mem_fixedStates_iff _).mpr hf⟩
      refine Submodule.mem_map.mpr ⟨C (fixedField r x) (e / 3) v,
        fixedMode_mem_span r v x (e / 3), ?_⟩
      change (C (fixedField r x) (e / 3) v).val = C (nativeField x.val) e v.val
      rw [fixedField_coeff_val, show 3 * (e / 3) = e by omega]
    · have he' : e % 3 ≠ (0 : ℤ) % 3 := by simpa only [Int.zero_emod] using he
      have hzero : σ (fixedProjection a) = ζ ^ (0 : ℤ) • fixedProjection a := by
        simpa only [zpow_zero, one_smul] using hf
      rw [nativeField_inResidue _ 0 hzero e he', LinearMap.zero_apply]
      exact S.zero_mem
  have hw' : sectorAverage r w.val ∈ S := hproject hw
  rw [sectorAverage_eq_self] at hw'
  obtain ⟨u, hu, huw⟩ := Submodule.mem_map.mp hw'
  have he : u = w := Subtype.ext huw
  exact he ▸ hu

/-- A chain of native modes whose result returns to the input's rotation
sector lies in the span of single fixed-source modes on the original vector. -/
theorem mode_chain_mem_fixedModeSpan (r : Fin 3) (v w : sector r)
    (modes : List (NativeStates × ℤ))
    (hw : w.val = modes.foldr (fun i u => C (nativeField i.1) i.2 u) v.val) :
    w ∈ fixedModeSpan r v := by
  apply mem_fixedModeSpan_of_nativeModeSpan r v w
  rw [hw]
  clear hw
  induction modes with
  | nil => exact self_mem_nativeModeSpan v.val
  | cons i modes ih => exact nativeModeSpan_stable v.val i.1 i.2 ih

/-- Total cover exponent zero modulo three guarantees that a native mode
chain on a sector vector is a linear combination of single fixed-field modes. -/
theorem neutral_mode_chain_mem_fixedModeSpan (r : Fin 3) (v : sector r)
    (modes : List (NativeStates × ℤ)) (hneutral : (3 : ℤ) ∣ (modes.map Prod.snd).sum) :
    ∃ w ∈ fixedModeSpan r v,
      w.val = modes.foldr (fun i u => C (nativeField i.1) i.2 u) v.val := by
  let act (i : NativeStates × ℤ) (u : State) := C (nativeField i.1) i.2 u
  have hv : gradingRotation v.val = ζ ^ r.val • v.val :=
    Module.End.mem_eigenspace_iff.mp v.property
  have covariance (ms : List (NativeStates × ℤ)) :
      gradingRotation (ms.foldr act v.val) =
        (ζ ^ (ms.map Prod.snd).sum * ζ ^ r.val) • ms.foldr act v.val := by
    induction ms with
    | nil =>
      simpa only [List.foldr_nil, List.map_nil, List.sum_nil, zpow_zero, one_mul] using hv
    | cons i rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      have h := LinearMap.congr_fun (gradingRotation_any_coeff i.1 i.2)
        (rest.foldr act v.val)
      change gradingRotation (act i (rest.foldr act v.val)) =
        ζ ^ i.2 • act i (gradingRotation (rest.foldr act v.val)) at h
      rw [h, ih]
      simp only [act, map_smul, smul_smul,
        zpow_add₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta), mul_assoc]
  have hζ : ζ ^ (modes.map Prod.snd).sum = 1 :=
    ((IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive :
      IsPrimitiveRoot ζ 3).zpow_eq_one_iff_dvd _).mpr hneutral
  let w : sector r := ⟨modes.foldr act v.val, Module.End.mem_eigenspace_iff.mpr (by
    simpa only [hζ, one_mul] using covariance modes)⟩
  exact ⟨w, mode_chain_mem_fixedModeSpan r v w modes rfl, rfl⟩

/-- Every nonzero vector in a rotation sector is cyclic under single
coefficients of actual fixed-source fields. -/
theorem fixedModeSpan_eq_top (r : Fin 3) (v : sector r) (hv : v ≠ 0) :
    fixedModeSpan r v = ⊤ := by
  have hv' : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  apply top_unique
  intro w _
  apply mem_fixedModeSpan_of_nativeModeSpan r v w
  rw [nativeModeSpan_eq_top v.val hv']
  exact Submodule.mem_top

/-- Every normalized rotation phase occurs in the actual twisted space. -/
theorem sector_ne_bot (r : Fin 3) : sector r ≠ ⊥ := by
  have henergy : ∃ v : State, v ≠ 0 ∧
      totalLZero v = (16 / 9 + (r.val : ℂ) / 3) • v :=
    (totalLZero_exact_eigenvalues _).mpr ⟨r.val, rfl⟩
  obtain ⟨v, hv, heig⟩ := henergy
  refine (sector r).ne_bot_iff.mpr ⟨v, Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
  apply Finsupp.ext
  intro p
  apply MvPolynomial.ext
  intro d
  simp only [gradingRotation_coeff, Finsupp.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hd : (v p).coeff d = 0
  · rw [hd, mul_zero, mul_zero]
  · have h := weight_eq_of_coeff_ne_zero heig hd
    rw [totalWeight_eq_gradingIndex] at h
    have hindex : (gradingIndex p d : ℂ) = (r.val : ℂ) := by
      linear_combination 3 * h
    have hindexNat : gradingIndex p d = r.val := by exact_mod_cast hindex
    rw [hindexNat]

/-- Fixed-field mode stability leaves only the zero submodule and the full
rotation sector. -/
theorem fixedField_irreducible (r : Fin 3) (S : Submodule ℂ (sector r))
    (hS : ∀ (a : fixedStates) (e : ℤ) (v : sector r), v ∈ S →
      C (fixedField r a) e v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hbot
  have hle : fixedModeSpan r v ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, e⟩, rfl⟩
    exact hS a e v hv
  rw [fixedModeSpan_eq_top r v hv0] at hle
  exact Or.inr (top_unique hle)

#print axioms mode_product_mem_iterate_span
#print axioms neutral_mode_product_mem_fixedModeSpan
#print axioms mode_chain_mem_fixedModeSpan
#print axioms neutral_mode_chain_mem_fixedModeSpan
#print axioms fixedModeSpan_eq_top
#print axioms sector_ne_bot
#print axioms fixedField_irreducible

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeModeProductSpan
