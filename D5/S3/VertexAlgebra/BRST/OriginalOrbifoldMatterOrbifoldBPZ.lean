/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterOrbifoldBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterOrbifoldBPZ
   mirror-E: none(waiver:algebraic-original-matter-field)
   anchors: []
   utility: none
   digest: Finite all-sector BPZ mode adjunction on the original Leech sign orbifold. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterRightTwistedBPZ
import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import Mathlib.Algebra.DirectSum.Decomposition

/-! The literal fixed and negative sectors have distinct lowering cutoffs.
They give a common finite adjoint field on the whole original carrier. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterOrbifoldBPZ

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldCriticalMatter (Orbifold orbifoldMode orbifoldVertexAlgebra)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ orbifoldBPZ_apply)
open OriginalOrbifoldMatterRightTwistedBPZ (original_fixed_twisted_bpz original_right_twisted_bpz)
open OriginalOrbifoldMatterTwistedBPZ (original_twisted_twisted_bpz)
open SourceBPZ.AllStateTranspose (sourcePairing_allState)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open LatticeAllStateField (Y)
open LatticeInvolution (fixedSpace fixedMode)
open LatticePositiveEnergy (grade actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open LatticeHalfFockGradedTrace (actualTensorL0)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open TwistedGround
open MixedIntertwiner (fixedGrade lowering_integer_energy integer_energy_zero)
open OriginalOrbifoldConformal (L_fixed_apply L_zero_twisted)
open OriginalOrbifoldLowSpectrum (actual_leech_positive_integral_grading)
open OriginalFourMChargeCoset (originalI)

open private originalL1 original_l1_grade from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private original_negative_grade_zero from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private fixed_lowering from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterRightTwistedBPZ
open private lowered lowered_pair lowered_val from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTwistedBPZ

private abbrev Fixed := fixedSpace leechData
private abbrev Negative := paritySpace leechData leech_spec.2.1 (-1)
private abbrev fixed (a : Fixed) : Orbifold := (a, 0)
private abbrev negative (u : Negative) : Orbifold := (0, u)

private abbrev field (m : ℤ) : Orbifold →ₗ[ℂ] Module.End ℂ Orbifold :=
  ((LinearMap.proj m).comp VertexOperator.ncoeff).comp orbifoldVertexAlgebra.stateField

private def adjointMode (h m : ℤ) (R : ℕ) (u : Orbifold) : Module.End ℂ Orbifold :=
  ((-1 : ℂ) ^ h) • ∑ j ∈ Finset.range R, (j.factorial : ℂ)⁻¹ •
    field (2 * h - (j : ℤ) - m - 2) ((orbifoldMode 1 ^ j) u)

private theorem adjointMode_pair (h m : ℤ) (R : ℕ) (u x y : Orbifold) :
    orbifoldBPZ x (adjointMode h m R u y) =
      (-1 : ℂ) ^ h * ∑ j ∈ Finset.range R, (j.factorial : ℂ)⁻¹ *
        orbifoldBPZ x (field (2 * h - (j : ℤ) - m - 2) ((orbifoldMode 1 ^ j) u) y) := by
  simp only [adjointMode, LinearMap.smul_apply, LinearMap.sum_apply, map_sum, map_smul, smul_eq_mul]

private theorem adjointMode_cutoff (h m : ℤ) (u : Orbifold) (R S : ℕ)
    (hR : ∀ j, R ≤ j → (orbifoldMode 1 ^ j) u = 0)
    (hS : ∀ j, S ≤ j → (orbifoldMode 1 ^ j) u = 0) :
    adjointMode h m R u = adjointMode h m S u := by
  unfold adjointMode
  let term (j : ℕ) := (j.factorial : ℂ)⁻¹ •
    field (2 * h - (j : ℤ) - m - 2) ((orbifoldMode 1 ^ j) u)
  have extend (N : ℕ) (hN : N ≤ max R S)
      (tail : ∀ j, N ≤ j → (orbifoldMode 1 ^ j) u = 0) :
      (∑ j ∈ Finset.range N, term j) = ∑ j ∈ Finset.range (max R S), term j := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hN)
    intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [term, tail j hj, map_zero, smul_zero]
  exact congrArg (((-1 : ℂ) ^ h) • ·)
    ((extend R (le_max_left R S) hR).trans (extend S (le_max_right R S) hS).symm)

private theorem fixed_grade (h : ℤ) (u : Orbifold)
    (hu : orbifoldMode 0 u = (h : ℂ) • u) : u.1.val ∈ grade leechData h := by
  have hi : actualInverse leechData = (gramComplex leechData)⁻¹ :=
    (Matrix.inv_eq_left_inv (actualInverse_left leechData leech_spec.2.1)).symm
  have hG := SourceMobius.gram_det_unit leechData leech_spec.2.1
  apply (actualL0_eigen_iff_grade leechData (gramComplex leechData)⁻¹
    (Matrix.nonsing_inv_mul _ hG) (Matrix.mul_nonsing_inv _ hG) h u.1.val).mp
  rw [← hi, ← L_fixed_apply leechData leech_spec.2.1 leech_spec.2.2.1 0 u]
  exact congrArg (fun v : Orbifold => v.1.val) hu

private theorem negative_energy (h : ℤ) (u : Orbifold)
    (hu : orbifoldMode 0 u = (h : ℂ) • u) :
    actualTensorL0 leechData leech_spec.2.1 u.2.val = (h : ℂ) • u.2.val := by
  rw [← L_zero_twisted leechData leech_spec.2.1 leech_spec.2.2.1 u]
  exact congrArg (fun v : Orbifold => v.2.val) hu

private def loweredFixed (j : ℕ) (a : Fixed) : Fixed :=
  ((orbifoldMode 1 ^ j) (fixed a)).1

private theorem fixed_lowering_pair (j : ℕ) (a : Fixed) :
    (orbifoldMode 1 ^ j) (fixed a) = fixed (loweredFixed j a) :=
  Prod.ext rfl (Subtype.ext (fixed_lowering j a).2)

private theorem fixed_lowering_zero (j : ℕ) (a : Fixed)
    (ha : (originalL1 leechData ^ j) a.val = 0) :
    (orbifoldMode 1 ^ j) (fixed a) = 0 :=
  Prod.ext (Subtype.ext ((fixed_lowering j a).1.trans ha)) (Subtype.ext (fixed_lowering j a).2)

private theorem fixed_energy_tail (H : ℕ) (a : Fixed) (ha : a.val ∈ grade leechData (H : ℤ))
    (j : ℕ) (hj : H + 1 ≤ j) : (orbifoldMode 1 ^ j) (fixed a) = 0 := by
  apply fixed_lowering_zero
  exact original_negative_grade_zero leechData leech_spec.2.2.1 _ _
    (original_l1_grade leechData leech_spec.2.1 (H : ℤ) a.val ha j) (by omega)

private abbrev fixedCutoff (a : Fixed) : ℕ :=
  a.val.support.sup
    (fun c => MvPolynomial.weightedTotalDegree (sourceWeight leechData) (a.val c)) + 1

private theorem fixed_support_tail (a : Fixed) (j : ℕ) (hj : fixedCutoff a ≤ j) :
    (orbifoldMode 1 ^ j) (fixed a) = 0 := by
  apply fixed_lowering_zero
  have hk : (originalL1 leechData ^ fixedCutoff a) a.val = 0 :=
    SourceMobius.actual_sugawara_one_bound leechData leech_spec.2.1 a.val
  rw [show j = (j - fixedCutoff a) + fixedCutoff a by omega,
    pow_add, Module.End.mul_apply, hk, map_zero]

private theorem negative_energy_tail (H : ℕ) (u : Negative)
    (hu : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val)
    (j : ℕ) (hj : H - 1 ≤ j) : (orbifoldMode 1 ^ j) (negative u) = 0 := by
  rw [lowered_pair]
  refine Prod.ext rfl (Subtype.ext ?_)
  apply integer_energy_zero leechData leech_spec.2.1 leech_spec.1 ((H : ℤ) - (j : ℤ))
  · rw [lowered_val]
    exact lowering_integer_energy leechData leech_spec.2.1 leech_spec.1 (H : ℤ) u.val
      (by simpa only [Int.cast_natCast] using hu) j
  · omega

private theorem fixed_field (m : ℤ) (a : Fixed) (x : Orbifold) :
    field m (fixed a) x =
      (fixedMode leechData a m x.1,
        ((fixedParitySlice leechData leech_spec.2.1 (-1) a)[[m]]) x.2) :=
  OriginalOrbifoldField.Y_fixed_ncoeff_apply leechData leech_spec.2.1 leech_spec.2.2.1 m a x

private theorem negative_field (m : ℤ) (u : Negative) (x : Orbifold) :
    field m (negative u) x =
      (originalI leechData leech_spec.2.1 leech_spec.2.2.1 m u x.2,
        MixedIntertwiner.originalRightCoefficient leechData leech_spec.2.1 m u x.1) :=
  OriginalOrbifoldField.Y_twisted_ncoeff_apply leechData leech_spec.2.1 leech_spec.2.2.1 m u x

private theorem pair_sector_sum (B C : LinearMap.BilinForm ℂ Orbifold) (x y : Orbifold)
    (hff : B (fixed x.1) (fixed y.1) = C (fixed x.1) (fixed y.1))
    (hfn : B (fixed x.1) (negative y.2) = C (fixed x.1) (negative y.2))
    (hnf : B (negative x.2) (fixed y.1) = C (negative x.2) (fixed y.1))
    (hnn : B (negative x.2) (negative y.2) = C (negative x.2) (negative y.2)) :
    B x y = C x y := by
  have hx : fixed x.1 + negative x.2 = x := Prod.ext (by simp) (by simp)
  have hy : fixed y.1 + negative y.2 = y := Prod.ext (by simp) (by simp)
  rw [← hx, ← hy]
  simp only [map_add, LinearMap.add_apply, hff, hfn, hnf, hnn]

private theorem fixed_fixed (H : ℕ) (m : ℤ) (a : fixedGrade leechData (H : ℤ)) (b c : Fixed) :
    let A := fixed ⟨a.val, a.property.2⟩
    orbifoldBPZ (field m A (fixed b)) (fixed c) =
      orbifoldBPZ (fixed b) (adjointMode (H : ℤ) m (fixedCutoff A.1) A (fixed c)) := by
  dsimp only
  rw [adjointMode_pair, fixed_field, orbifoldBPZ_apply]
  simp only [Submodule.coe_zero, map_zero, add_zero]
  rw [show (fixedMode leechData ⟨a.val, a.property.2⟩ m b).val =
    ((Y leechData a.val)[[m]]) b.val from rfl,
    sourcePairing_allState leechData leech_spec.2.1 (H : ℤ) m a.val a.property.1 b.val c.val]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fixed_lowering_pair, fixed_field, orbifoldBPZ_apply]
  simp only [Submodule.coe_zero, map_zero, add_zero]
  change _ * sourcePairing leechData b.val
      (((Y leechData ((originalL1 leechData ^ j) a.val))[[2 * (H : ℤ) - (j : ℤ) - m - 2]]) c.val) =
    _ * sourcePairing leechData b.val
      (((Y leechData (((orbifoldMode 1 ^ j) (fixed ⟨a.val, a.property.2⟩)).1.val))
        [[2 * (H : ℤ) - (j : ℤ) - m - 2]]) c.val)
  rw [(fixed_lowering j ⟨a.val, a.property.2⟩).1]

private theorem fixed_source (H : ℕ) (m : ℤ) (a : fixedGrade leechData (H : ℤ)) (x y : Orbifold) :
    let A := fixed ⟨a.val, a.property.2⟩
    orbifoldBPZ (field m A x) y =
      orbifoldBPZ x (adjointMode (H : ℤ) m (H + 1) A y) := by
  intro A
  rw [adjointMode_cutoff (H : ℤ) m A (H + 1) (fixedCutoff A.1)
    (fixed_energy_tail H A.1 a.property.1) (fixed_support_tail A.1)]
  apply pair_sector_sum (LinearMap.comp orbifoldBPZ (field m A))
    (orbifoldBPZ.compl₂ (adjointMode (H : ℤ) m (fixedCutoff A.1) A)) x y
  · exact fixed_fixed H m a x.1 y.1
  · change orbifoldBPZ (field m A (fixed x.1)) (negative y.2) =
      orbifoldBPZ (fixed x.1) (adjointMode (H : ℤ) m (fixedCutoff A.1) A (negative y.2))
    rw [adjointMode_pair]
    simp only [A, fixed_lowering_pair, fixed_field, orbifoldBPZ_apply,
      Submodule.coe_zero, map_zero, LinearMap.zero_apply, add_zero, mul_zero,
      Finset.sum_const_zero]
  · change orbifoldBPZ (field m A (negative x.2)) (fixed y.1) =
      orbifoldBPZ (negative x.2) (adjointMode (H : ℤ) m (fixedCutoff A.1) A (fixed y.1))
    rw [adjointMode_pair]
    simp only [A, fixed_lowering_pair, fixed_field, orbifoldBPZ_apply,
      Submodule.coe_zero, map_zero, LinearMap.zero_apply, add_zero, mul_zero,
      Finset.sum_const_zero]
  · change orbifoldBPZ (field m A (negative x.2)) (negative y.2) =
      orbifoldBPZ (negative x.2) (adjointMode (H : ℤ) m (fixedCutoff A.1) A (negative y.2))
    rw [adjointMode_pair]
    exact original_fixed_twisted_bpz m (H : ℤ) a x.2 y.2

private theorem energy_ext {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (f g : Orbifold →ₗ[ℂ] W)
    (hom : ∀ (K : ℕ) (x : Orbifold), orbifoldMode 0 x = (K : ℂ) • x → f x = g x) : f = g := by
  classical
  let E (K : ℕ) := (orbifoldMode 0).eigenspace (K : ℂ)
  have hE : DirectSum.IsInternal E := actual_leech_positive_integral_grading.1
  let : DirectSum.Decomposition E := hE.chooseDecomposition
  apply DirectSum.decompose_lhom_ext E
  intro K
  apply LinearMap.ext
  intro x
  exact hom K x.val (Module.End.mem_eigenspace_iff.mp x.property)

private theorem negative_source (H : ℕ) (m : ℤ) (u : Negative)
    (hu : actualTensorL0 leechData leech_spec.2.1 u.val = (H : ℂ) • u.val) (x y : Orbifold) :
    orbifoldBPZ (field m (negative u) x) y =
      orbifoldBPZ x (adjointMode (H : ℤ) m (H + 1) (negative u) y) := by
  rw [adjointMode_cutoff (H : ℤ) m (negative u) (H + 1) (H - 1)
    (fun j hj => negative_energy_tail H u hu j (by omega)) (negative_energy_tail H u hu)]
  let B := LinearMap.comp orbifoldBPZ (field m (negative u))
  let C := orbifoldBPZ.compl₂ (adjointMode (H : ℤ) m (H - 1) (negative u))
  change B x y = C x y
  suffices hBC : B = C by rw [hBC]
  apply energy_ext
  intro K v hv
  apply energy_ext
  intro J w hw
  let b : fixedGrade leechData (K : ℤ) :=
    ⟨v.1.val, fixed_grade (K : ℤ) v (by simpa only [Int.cast_natCast] using hv), v.1.property⟩
  let c : fixedGrade leechData (J : ℤ) :=
    ⟨w.1.val, fixed_grade (J : ℤ) w (by simpa only [Int.cast_natCast] using hw), w.1.property⟩
  have hv' : actualTensorL0 leechData leech_spec.2.1 v.2.val = (K : ℂ) • v.2.val := by
    simpa only [Int.cast_natCast] using
      negative_energy (K : ℤ) v (by simpa only [Int.cast_natCast] using hv)
  have hw' : actualTensorL0 leechData leech_spec.2.1 w.2.val = (J : ℂ) • w.2.val := by
    simpa only [Int.cast_natCast] using
      negative_energy (J : ℤ) w (by simpa only [Int.cast_natCast] using hw)
  apply pair_sector_sum B C v w
  · change orbifoldBPZ (field m (negative u) (fixed v.1)) (fixed w.1) =
      orbifoldBPZ (fixed v.1) (adjointMode (H : ℤ) m (H - 1) (negative u) (fixed w.1))
    rw [adjointMode_pair]
    simp only [lowered_pair, negative_field, orbifoldBPZ_apply, map_zero, Submodule.coe_zero,
      LinearMap.zero_apply, zero_add, add_zero, mul_zero, Finset.sum_const_zero]
  · change orbifoldBPZ (field m (negative u) (fixed v.1)) (negative w.2) =
      orbifoldBPZ (fixed v.1) (adjointMode (H : ℤ) m (H - 1) (negative u) (negative w.2))
    rw [adjointMode_pair]
    exact original_right_twisted_bpz H J m (K : ℤ) u w.2 hu hw' b
  · change orbifoldBPZ (field m (negative u) (negative v.2)) (fixed w.1) =
      orbifoldBPZ (negative v.2) (adjointMode (H : ℤ) m (H - 1) (negative u) (fixed w.1))
    rw [adjointMode_pair]
    exact original_twisted_twisted_bpz H K m (J : ℤ) u v.2 hu hv' c
  · change orbifoldBPZ (field m (negative u) (negative v.2)) (negative w.2) =
      orbifoldBPZ (negative v.2) (adjointMode (H : ℤ) m (H - 1) (negative u) (negative w.2))
    rw [adjointMode_pair]
    simp only [lowered_pair, negative_field, orbifoldBPZ_apply, map_zero, Submodule.coe_zero,
      LinearMap.zero_apply, zero_add, add_zero, mul_zero, Finset.sum_const_zero]

private theorem original_orbifold_bpz_nat (H : ℕ) (m : ℤ) (u x y : Orbifold)
    (hu : orbifoldMode 0 u = (H : ℂ) • u) :
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField u)[[m]]) x) y =
      (-1 : ℂ) ^ (H : ℤ) * ∑ j ∈ Finset.range (H + 1),
        (j.factorial : ℂ)⁻¹ * orbifoldBPZ x
          (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ j) u))[[
            2 * (H : ℤ) - (j : ℤ) - m - 2]]) y) := by
  refine Eq.trans ?_ (adjointMode_pair (H : ℤ) m (H + 1) u x y)
  change orbifoldBPZ (field m u x) y =
    orbifoldBPZ x (adjointMode (H : ℤ) m (H + 1) u y)
  have hu' : orbifoldMode 0 u = ((H : ℤ) : ℂ) • u := by simpa only [Int.cast_natCast] using hu
  let a : fixedGrade leechData (H : ℤ) := ⟨u.1.val, fixed_grade (H : ℤ) u hu', u.1.property⟩
  have hv : actualTensorL0 leechData leech_spec.2.1 u.2.val = (H : ℂ) • u.2.val := by
    simpa only [Int.cast_natCast] using negative_energy (H : ℤ) u hu'
  have hfixed := fixed_source H m a x y
  have hnegative := negative_source H m u.2 hv x y
  change orbifoldBPZ (field m (fixed u.1) x) y =
    orbifoldBPZ x (adjointMode (H : ℤ) m (H + 1) (fixed u.1) y) at hfixed
  have hs : fixed u.1 + negative u.2 = u := Prod.ext (by simp) (by simp)
  have hadd : adjointMode (H : ℤ) m (H + 1) (fixed u.1 + negative u.2) =
      adjointMode (H : ℤ) m (H + 1) (fixed u.1) +
        adjointMode (H : ℤ) m (H + 1) (negative u.2) := by
    simp only [adjointMode, map_add, smul_add, Finset.sum_add_distrib]
  rw [← hs, hadd]
  simp only [map_add, LinearMap.add_apply, hfixed, hnegative]

/-- Finite BPZ mode adjunction on the original Leech sign orbifold for a
homogeneous source and arbitrary detectors. Weight zero uses a single term. -/
theorem original_orbifold_bpz (h m : ℤ) (u x y : Orbifold)
    (hu : orbifoldMode 0 u = (h : ℂ) • u) :
    orbifoldBPZ (((orbifoldVertexAlgebra.stateField u)[[m]]) x) y =
      (-1 : ℂ) ^ h * ∑ j ∈ Finset.range (h.toNat + 1),
        (j.factorial : ℂ)⁻¹ * orbifoldBPZ x
          (((orbifoldVertexAlgebra.stateField ((orbifoldMode 1 ^ j) u))[[
            2 * h - (j : ℤ) - m - 2]]) y) := by
  by_cases hh : 0 ≤ h
  · lift h to ℕ using hh
    simpa only [Int.toNat_natCast] using
      original_orbifold_bpz_nat h m u x y (by simpa only [Int.cast_natCast] using hu)
  · have hfixed := original_negative_grade_zero leechData leech_spec.2.2.1
      h u.1.val (fixed_grade h u hu) (lt_of_not_ge hh)
    have hnegative := integer_energy_zero leechData leech_spec.2.1 leech_spec.1
      h u.2.val (negative_energy h u hu) (by omega)
    have hu0 : u = 0 := Prod.ext (Subtype.ext hfixed) (Subtype.ext hnegative)
    subst u
    refine Eq.trans ?_ (adjointMode_pair h m (h.toNat + 1) 0 x y)
    change orbifoldBPZ (field m 0 x) y =
      orbifoldBPZ x (adjointMode h m (h.toNat + 1) 0 y)
    simp only [adjointMode, map_zero, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

#print axioms original_orbifold_bpz

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterOrbifoldBPZ
