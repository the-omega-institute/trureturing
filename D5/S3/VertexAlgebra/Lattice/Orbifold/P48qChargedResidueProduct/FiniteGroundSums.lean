/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedResidueProduct/FiniteGroundSums
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite homogeneous ground sums for residue extraction from charged radial products. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeResidueProduct
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.Interchange
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

/-! Residue extraction from finite homogeneous slices of the charged radial products. -/

set_option autoImplicit false

open scoped BigOperators VertexOperator

noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct

private def binomialKernel (d j : ℤ) : ℂ :=
  if j < 0 then 0 else (-1 : ℂ) ^ j * Ring.choose (d : ℂ) j.toNat

private theorem binomialKernel_succ (d j : ℤ) :
    binomialKernel (d + 1) j = binomialKernel d j - binomialKernel d (j - 1) := by
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · simp [binomialKernel, hj, show j - 1 < 0 by omega]
  · norm_num [binomialKernel]
  · have hj' : j.toNat = (j - 1).toNat + 1 := by omega
    rw [binomialKernel, binomialKernel, binomialKernel, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), Int.cast_add, Int.cast_one]
    simp only [hj', Ring.choose_succ_succ]
    rw [show j = (j - 1) + 1 by omega, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    norm_num [show j - 1 + 1 - 1 = j - 1 by omega]
    ring

private def forwardWeight (d l : ℤ) : ℂ := binomialKernel d (d + l + 1)

private def reverseWeight (d l : ℤ) : ℂ := (-1 : ℂ) ^ d * binomialKernel d (-l - 1)

private theorem forwardWeight_succ (d l : ℤ) :
    forwardWeight (d + 1) l = forwardWeight d (l + 1) - forwardWeight d l := by
  simpa only [forwardWeight, show d + 1 + l + 1 = d + (l + 1) + 1 by omega,
    show d + (l + 1) + 1 - 1 = d + l + 1 by omega] using
    binomialKernel_succ d (d + 1 + l + 1)

private theorem reverseWeight_succ (d l : ℤ) :
    reverseWeight (d + 1) l = reverseWeight d (l + 1) - reverseWeight d l := by
  simp only [reverseWeight, binomialKernel_succ, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_one, show -l - 1 - 1 = -(l + 1) - 1 by omega]
  ring

private theorem sign_square (j : ℤ) : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul, zpow_mul]
  norm_num

private theorem choose_negative_nat (p j : ℕ) :
    Ring.choose (-(p : ℂ)) j =
      (-1 : ℂ) ^ (j : ℤ) * Ring.choose ((p : ℂ) + j - 1) j := by
  rw [Ring.choose_neg, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ,
    Int.cast_negOnePow_natCast, zpow_natCast, smul_eq_mul]

private theorem negativeWeight_jump (m : ℕ) (l : ℤ) :
    forwardWeight (-(m : ℤ) - 1) l - reverseWeight (-(m : ℤ) - 1) l =
      Ring.choose (l : ℂ) m := by
  have hm : ((-(m : ℤ) - 1 : ℤ) : ℂ) = -((m + 1 : ℕ) : ℂ) := by push_cast; ring
  have hd : -(m : ℤ) - 1 + l + 1 = l - m := by omega
  by_cases hl : (m : ℤ) ≤ l
  · have hcast : (l.toNat : ℤ) = l := Int.toNat_of_nonneg (by omega)
    have hcast' : ((l - m).toNat : ℤ) = l - m := Int.toNat_of_nonneg (by omega)
    have hs : (((m + 1 : ℕ) : ℂ) + ((l - m).toNat : ℂ) - 1) = l.toNat := by
      rw [Nat.cast_add, Nat.cast_one, ← Int.cast_natCast (R := ℂ) (l - m).toNat,
        hcast', Int.cast_sub, Int.cast_natCast, ← Int.cast_natCast (R := ℂ) l.toNat, hcast]
      ring
    unfold forwardWeight reverseWeight binomialKernel
    rw [hd, ite_eq_right (by omega), ite_eq_left (by omega), mul_zero, sub_zero, hm,
      choose_negative_nat, hs, ← mul_assoc, hcast', sign_square, one_mul,
      show (l : ℂ) = (l.toNat : ℂ) by exact_mod_cast hcast.symm,
      Ring.choose_natCast, Ring.choose_natCast,
      show (l - (m : ℤ)).toNat = l.toNat - m by omega,
      Nat.choose_symm (show m ≤ l.toNat by omega)]
  · by_cases hn : l < 0
    · let j := (-l - 1).toNat
      have hj : (j : ℤ) = -l - 1 := Int.toNat_of_nonneg (by omega)
      have hp : (j + 1 : ℤ) = -l := by omega
      have he : (l : ℂ) = -((j + 1 : ℕ) : ℂ) := by
        exact_mod_cast (show l = -((j + 1 : ℕ) : ℤ) by omega)
      have ho : ((m + 1 : ℕ) : ℂ) + (j : ℂ) - 1 = ((m + j : ℕ) : ℂ) := by push_cast; ring
      have ho' : ((j + 1 : ℕ) : ℂ) + (m : ℂ) - 1 = ((m + j : ℕ) : ℂ) := by push_cast; ring
      unfold forwardWeight reverseWeight binomialKernel
      rw [hd, ite_eq_left (by omega), ite_eq_right (by omega), zero_sub, hm]
      change -((-1 : ℂ) ^ (-(m : ℤ) - 1) *
        ((-1 : ℂ) ^ (-l - 1) * Ring.choose (-((m + 1 : ℕ) : ℂ)) j)) = _
      rw [choose_negative_nat, ho, hj, ← mul_assoc ((-1 : ℂ) ^ (-l - 1)),
        sign_square, one_mul, he, choose_negative_nat, ho', Ring.choose_natCast,
        Ring.choose_natCast, Nat.add_comm m j, Nat.choose_symm_add]
      have hsign : -((-1 : ℂ) ^ (-(m : ℤ) - 1)) = (-1 : ℂ) ^ (m : ℤ) := by
        have eqn := zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) (1 : ℤ) (-(m : ℤ) - 1)
        rw [zpow_one, neg_one_mul] at eqn
        rw [← eqn]
        rw [show (1 : ℤ) + (-(m : ℤ) - 1) = -(m : ℤ) by omega, zpow_neg,
          inv_eq_of_mul_eq_one_right (sign_square m)]
      rw [← neg_mul, hsign]
    · unfold forwardWeight reverseWeight binomialKernel
      rw [hd, ite_eq_left (by omega), ite_eq_left (by omega), mul_zero, sub_zero,
        ← Int.toNat_of_nonneg (show 0 ≤ l by omega), Int.cast_natCast, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (show l.toNat < m by omega), Nat.cast_zero]


section Slice

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- On a fixed total degree, multiplication by the physical difference is
the first-coordinate shift minus the identity, with the total degree advanced. -/
private def difference (F : ℤ → M) : ℤ → M := fun l => F (l - 1) - F l

private def radialSum (W : ℤ → ℤ → ℂ) (F : ℤ → M) (d : ℤ) : M :=
  ∑ᶠ l : ℤ, W d l • F l

private def radialFinite (W : ℤ → ℤ → ℂ) (F : ℤ → M) : Prop :=
  ∀ d i : ℤ, Function.HasFiniteSupport (fun l : ℤ => W d (l + i) • F l)

private theorem radialFinite_difference {W : ℤ → ℤ → ℂ} {F : ℤ → M}
    (hF : radialFinite W F) : radialFinite W (difference F) := by
  intro d i
  have h₁ := Set.Finite.preimage (Equiv.addRight (-1 : ℤ)).injective.injOn (hF d (i + 1))
  refine (h₁.union (hF d i)).subset ?_
  intro l hl
  by_contra hn
  have ha : W d (l + i) • F (l - 1) = 0 := by
    have hn' : l - 1 ∉ Function.support (fun k : ℤ => W d (k + (i + 1)) • F k) :=
      fun hh => hn (Or.inl hh)
    simpa only [Function.notMem_support, show l - 1 + (i + 1) = l + i by omega] using hn'
  have hb : W d (l + i) • F l = 0 :=
    Function.notMem_support.mp (fun hh => hn (Or.inr hh))
  exact hl (by simp only [difference, smul_sub, ha, hb, sub_zero])

private theorem radialSum_difference {W : ℤ → ℤ → ℂ} {F : ℤ → M}
    (hF : radialFinite W F) (hW : ∀ d l, W (d + 1) l = W d (l + 1) - W d l) (d : ℤ) :
    radialSum W (difference F) d = radialSum W F (d + 1) := by
  have h₀ : Function.HasFiniteSupport (fun l : ℤ => W d l • F l) := by simpa using hF d 0
  have h₁ : Function.HasFiniteSupport (fun l : ℤ => W d l • F (l - 1)) := by
    have hh := Set.Finite.preimage (Equiv.addRight (-1 : ℤ)).injective.injOn (hF d 1)
    refine hh.subset ?_
    intro l hl
    change W d ((l + -1) + 1) • F (l + -1) ≠ 0
    simpa [show l + -1 = l - 1 by omega] using hl
  unfold radialSum
  simp only [difference, smul_sub, hW, sub_smul]
  rw [finsum_sub_distrib h₁ h₀, finsum_sub_distrib (hF d 1) h₀]
  congr 1
  let e := Equiv.addRight (-1 : ℤ)
  apply finsum_eq_of_bijective e e.bijective
  intro l
  simp [e, show l + -1 = l - 1 by omega]

private theorem radialSum_clear {W : ℤ → ℤ → ℂ} {F : ℤ → M}
    (hF : radialFinite W F) (hW : ∀ d l, W (d + 1) l = W d (l + 1) - W d l)
    (N : ℕ) (d : ℤ) : radialSum W (difference^[N] F) d = radialSum W F (d + N) := by
  induction N generalizing F with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih (radialFinite_difference hF),
      radialSum_difference hF hW, Nat.cast_succ, ← add_assoc]

/-- For a fixed total Laurent degree, the jump of the two radial residues
equals the collision coefficient of their common cleared Laurent polynomial.
The collision coordinate used here is (z-w)/w. -/
private theorem finite_slice_residue_to_collision (L R C : ℤ → M)
    (hL : radialFinite forwardWeight L) (hR : radialFinite reverseWeight R)
    (hC : Function.HasFiniteSupport C) (N m : ℕ)
    (hLC : difference^[N] L = C) (hRC : difference^[N] R = C) :
    radialSum forwardWeight L ((N : ℤ) - m - 1) -
      radialSum reverseWeight R ((N : ℤ) - m - 1) =
        ∑ᶠ l : ℤ, Ring.choose (l : ℂ) m • C l := by
  let d := -(m : ℤ) - 1
  have he : (N : ℤ) - m - 1 = d + N := by dsimp [d]; omega
  rw [he, ← radialSum_clear hL forwardWeight_succ, ← radialSum_clear hR reverseWeight_succ,
    hLC, hRC]
  unfold radialSum
  have hf : Function.HasFiniteSupport (fun l : ℤ => forwardWeight d l • C l) :=
    hC.smul_right _
  have hr : Function.HasFiniteSupport (fun l : ℤ => reverseWeight d l • C l) :=
    hC.smul_right _
  rw [← finsum_sub_distrib hf hr]
  congr 1
  funext l
  rw [← sub_smul, negativeWeight_jump]

end Slice

#print axioms finite_slice_residue_to_collision

section Fields

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

omit [Module ℂ V] in
private theorem finsum_on_range {I J : Type*} (e : I → J) (he : Function.Injective e)
    (f : J → V) (hf : ∀ j ∉ Set.range e, f j = 0) :
    (∑ᶠ j, f j) = ∑ᶠ i, f (e i) := by
  rw [← finsum_mem_range he, finsum_mem_def]
  congr 1
  funext j
  by_cases hj : j ∈ Set.range e <;> simp [hj, hf]

private def leftSlice (A B : VertexOperator ℂ V) (v : V) (H : ℤ) : ℤ → V :=
  fun l => HVertexOperator.coeff A l (HVertexOperator.coeff B (H - l) v)

private def rightSlice (A B : VertexOperator ℂ V) (v : V) (H : ℤ) : ℤ → V :=
  fun l => HVertexOperator.coeff B (H - l) (HVertexOperator.coeff A l v)

private theorem leftSlice_finite (A B : VertexOperator ℂ V) (v : V) (H : ℤ) :
    radialFinite forwardWeight (leftSlice A B v H) := by
  intro d i
  let b := ((HahnModule.of ℂ).symm (B v)).order
  refine (Finset.Icc (-d - i - 1) (H - b)).finite_toSet.subset ?_
  intro l hl
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra! h
    exact hl (by simp [forwardWeight, binomialKernel, show d + (l + i) + 1 < 0 by omega])
  · by_contra! h
    have hz : HVertexOperator.coeff B (H - l) v = 0 :=
      VertexOperator.coeff_eq_zero_of_lt_order B _ v (by omega)
    exact hl (by simp only [leftSlice, hz, map_zero, smul_zero])

private theorem rightSlice_finite (A B : VertexOperator ℂ V) (v : V) (H : ℤ) :
    radialFinite reverseWeight (rightSlice A B v H) := by
  intro d i
  let b := ((HahnModule.of ℂ).symm (A v)).order
  refine (Finset.Icc b (-i - 1)).finite_toSet.subset ?_
  intro l hl
  simp only [Finset.mem_coe, Finset.mem_Icc]
  constructor
  · by_contra! h
    have hz : HVertexOperator.coeff A l v = 0 :=
      VertexOperator.coeff_eq_zero_of_lt_order A _ v (by omega)
    exact hl (by simp only [rightSlice, hz, map_zero, smul_zero])
  · by_contra! h
    exact hl (by simp only [reverseWeight, binomialKernel,
      ite_eq_left (show -(l + i) - 1 < 0 by omega), mul_zero, zero_smul])

private theorem choose_cast (d : ℤ) (j : ℕ) :
    Ring.choose (d : ℂ) j = StateFieldResidueReconstruction.integerBinomial d j :=
  (Ring.map_choose (Int.castRingHom ℂ) d j).symm

private theorem residueField_eq_radial (A B : VertexOperator ℂ V) (v : V) (n H : ℤ) :
    HVertexOperator.coeff (SignedFieldResidueLocality.residueField 1 n A B).operator
      (H + n + 1) v =
        radialSum forwardWeight (leftSlice A B v H) n -
          radialSum reverseWeight (rightSlice A B v H) n := by
  rw [VertexOperator.coeff_eq_ncoeff, (SignedFieldResidueLocality.residueField 1 n A B).coefficient,
    SignedFieldResidueLocality.residueCoefficient, mul_one]
  congr 1
  · unfold radialSum
    let e (j : ℕ) : ℤ := (j : ℤ) - n - 1
    rw [finsum_on_range e (by intro a b hab; dsimp [e] at hab; omega)]
    · unfold SignedFieldResidueLocality.residueLeft
      congr 1
      funext j
      simp only [e, forwardWeight, binomialKernel, leftSlice, VertexOperator.ncoeff_apply,
        show n + ((j : ℤ) - n - 1) + 1 = j by omega,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg j)), Int.toNat_natCast, zpow_natCast, choose_cast,
        show - (n - (j : ℤ)) - 1 = j - n - 1 by omega,
        show - (-(H + n + 1) - 1 + (j : ℤ)) - 1 = H - (j - n - 1) by omega]
    · intro l hl
      have hlt : n + l + 1 < 0 := by
        by_contra! h
        exact hl ⟨(n + l + 1).toNat, by dsimp [e]; omega⟩
      simp only [forwardWeight, binomialKernel, ite_eq_left hlt, zero_smul]
  · unfold radialSum
    let e (j : ℕ) : ℤ := -(j : ℤ) - 1
    rw [finsum_on_range e (by intro a b hab; dsimp [e] at hab; omega)]
    · unfold SignedFieldResidueLocality.residueRight StateFieldResidueReconstruction.epsilon
      rw [smul_finsum' _ ((SignedFieldResidueLocality.residueField 1 n A B).right_finite
        (-(H + n + 1) - 1) v)]
      congr 1
      funext j
      simp only [e, reverseWeight, binomialKernel, rightSlice, VertexOperator.ncoeff_apply,
        show - (-(j : ℤ) - 1) - 1 = j by omega,
        ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg j)), Int.toNat_natCast, zpow_natCast, choose_cast, smul_smul,
        show -(n + (-(H + n + 1) - 1) - (j : ℤ)) - 1 = H - (-(j : ℤ) - 1) by omega]
    · intro l hl
      have hlt : -l - 1 < 0 := by
        by_contra! h
        exact hl ⟨(-l - 1).toNat, by dsimp [e]; omega⟩
      simp only [reverseWeight, binomialKernel, ite_eq_left hlt, mul_zero, zero_smul]

/-- The ordinary field residue after stripping can be computed from the common
finite homogeneous Laurent slice of the cleared products. Here the slice has
total degree H+N and the output Laurent exponent is H+n+1. -/
theorem residueField_coeff_of_cleared_slice (A B : VertexOperator ℂ V) (v : V)
    (H : ℤ) (N m : ℕ) (C : ℤ → V) (hC : Function.HasFiniteSupport C)
    (hL : difference^[N] (leftSlice A B v H) = C)
    (hR : difference^[N] (rightSlice A B v H) = C) :
    HVertexOperator.coeff
      (SignedFieldResidueLocality.residueField 1 ((N : ℤ) - m - 1) A B).operator
      (H + N - m) v = ∑ᶠ l : ℤ, Ring.choose (l : ℂ) m • C l := by
  rw [show H + (N : ℤ) - m = H + ((N : ℤ) - m - 1) + 1 by omega, residueField_eq_radial]
  exact finite_slice_residue_to_collision _ _ _
    (leftSlice_finite A B v H) (rightSlice_finite A B v H) hC N m hL hR

end Fields

#print axioms residueField_coeff_of_cleared_slice

section Cover

open P48qThirdTwistedField
open P48qTwistedChargeAction (lattice Momentum)
open LatticeGeneratingFieldLocality (Charge)
open P48qNativeCurrentLocality (Field stripResidue stripResidue_coeff)
open P48qAllJetWickField (nativeField nativeField_ground)
open P48qCurrentChargedIterate (chargedGround)

open private coverMonomial_pow coverMonomial_mul_coeff orderedChargedProduct_coeff_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
open private finiteCoverSlices from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport

local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))

private def coverSlice (A : CoverSeries Fock) (s t H : ℤ) (l : ℤ) : Fock :=
  (A.coeff (3 * (H - l) + t)).coeff (3 * l + s)

private def swappedSlice (A : CoverSeries Fock) (s t H : ℤ) (l : ℤ) : Fock :=
  (A.coeff (3 * l + s)).coeff (3 * (H - l) + t)

private theorem coverSlice_clear (A : CoverSeries Fock) (s t H : ℤ) (N : ℕ) :
    coverSlice ((Xc ^ 3 - Yc ^ 3) ^ N * A) s t (H + N) =
      difference^[N] (coverSlice A s t H) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_assoc, Function.iterate_succ_apply', ← ih]
    funext l
    let Q := (Xc ^ 3 - Yc ^ 3) ^ N * A
    change coverSlice ((Xc ^ 3 - Yc ^ 3) * Q) s t (H + (N + 1 : ℕ)) l =
      difference (coverSlice Q s t (H + N)) l
    simp only [coverSlice, difference, sub_mul, HahnSeries.coeff_sub, coverMonomial_pow,
      Nat.cast_ofNat, mul_one, mul_zero, coverMonomial_mul_coeff, one_mul, sub_zero]
    congr 1 <;> congr 1 <;> push_cast <;> ring

private theorem swappedSlice_clear (A : CoverSeries Fock) (s t H : ℤ) (N : ℕ) :
    swappedSlice ((Yc ^ 3 - Xc ^ 3) ^ N * A) s t (H + N) =
      difference^[N] (swappedSlice A s t H) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', mul_assoc, Function.iterate_succ_apply', ← ih]
    funext l
    let Q := (Yc ^ 3 - Xc ^ 3) ^ N * A
    change swappedSlice ((Yc ^ 3 - Xc ^ 3) * Q) s t (H + (N + 1 : ℕ)) l =
      difference (swappedSlice Q s t (H + N)) l
    simp only [swappedSlice, difference, sub_mul, HahnSeries.coeff_sub, coverMonomial_pow,
      Nat.cast_ofNat, mul_one, mul_zero, coverMonomial_mul_coeff, one_mul, sub_zero]
    congr 1 <;> congr 1 <;> push_cast <;> ring

private theorem coverSlice_finite {A : CoverSeries Fock} (hA : finiteCoverSlices A)
    (s t H : ℤ) : Function.HasFiniteSupport (coverSlice A s t H) := by
  let e (l : ℤ) := 3 * l + s
  refine (Set.Finite.preimage (f := e) (by intro a _ b _ hab; dsimp [e] at hab; omega)
    (hA (3 * H + s + t))).subset ?_
  intro l hl
  change (A.coeff (3 * H + s + t - e l)).coeff (e l) ≠ 0
  rw [show 3 * H + s + t - e l = 3 * (H - l) + t by dsimp [e]; ring]
  exact hl

/-- The residue of two stripped fields on a fixed input and output momentum
line equals the collision sum over the actual common cleared coefficients. -/
private theorem strippedResidue_coverSlice
    (A B : Field) (v : State) (q : Momentum) (s t H : ℤ) (N m : ℕ)
    (L R : CoverSeries Fock)
    (hL : ∀ k l, (L.coeff l).coeff k =
      HVertexOperator.coeff A k (HVertexOperator.coeff B l v) q)
    (hR : ∀ k l, (R.coeff k).coeff l =
      HVertexOperator.coeff B l (HVertexOperator.coeff A k v) q)
    (hC : finiteCoverSlices ((Xc ^ 3 - Yc ^ 3) ^ N * L))
    (hSwap : ∀ k l, (((Xc ^ 3 - Yc ^ 3) ^ N * L).coeff l).coeff k =
      (((Yc ^ 3 - Xc ^ 3) ^ N * R).coeff k).coeff l) :
    HVertexOperator.coeff (SignedFieldResidueLocality.residueField 1
      ((N : ℤ) - m - 1) (stripResidue s A) (stripResidue t B)).operator (H + N - m) v q =
      ∑ᶠ l : ℤ, Ring.choose (l : ℂ) m •
        coverSlice ((Xc ^ 3 - Yc ^ 3) ^ N * L) s t (H + N) l := by
  let C := coverSlice ((Xc ^ 3 - Yc ^ 3) ^ N * L) s t (H + N)
  let π : State →ₗ[ℂ] Fock := Finsupp.lapply q
  have hl : coverSlice L s t H = π ∘ leftSlice (stripResidue s A) (stripResidue t B) v H := by
    funext l
    simp only [coverSlice, leftSlice, Function.comp_apply, stripResidue_coeff, π,
      Finsupp.lapply_apply, hL]
  have hr : swappedSlice R s t H = π ∘ rightSlice (stripResidue s A) (stripResidue t B) v H := by
    funext l
    simp only [swappedSlice, rightSlice, Function.comp_apply, stripResidue_coeff, π,
      Finsupp.lapply_apply, hR]
  have hEq := finite_slice_residue_to_collision (coverSlice L s t H) (swappedSlice R s t H) C
  have hfin {W : ℤ → ℤ → ℂ} {F : ℤ → State} (hF : radialFinite W F) :
      radialFinite W (π ∘ F) := by
    intro d i
    refine (hF d i).subset ?_
    intro l hl hz
    exact hl (by simpa only [map_smul, Function.comp_apply, map_zero] using congrArg π hz)
  have hlf := leftSlice_finite (stripResidue s A) (stripResidue t B) v H
  have hrf := rightSlice_finite (stripResidue s A) (stripResidue t B) v H
  have hres := hEq (hl ▸ hfin hlf) (hr ▸ hfin hrf) (coverSlice_finite hC s t _) N m
    (coverSlice_clear L s t H N).symm
    ((swappedSlice_clear R s t H N).symm.trans (funext fun l => (hSwap _ _).symm))
  rw [hl, hr] at hres
  have hmap {W : ℤ → ℤ → ℂ} {F : ℤ → State} (hF : radialFinite W F) (d : ℤ) :
      radialSum W (π ∘ F) d = π (radialSum W F d) := by
    have hh : Function.HasFiniteSupport (fun l => W d l • F l) := by simpa using hF d 0
    simp only [radialSum, map_finsum π hh, map_smul, Function.comp_apply]
  rw [hmap hlf, hmap hrf, ← map_sub, ← residueField_eq_radial,
    show H + ((N : ℤ) - m - 1) + 1 = H + N - m by omega] at hres
  exact hres

end Cover

#print axioms strippedResidue_coverSlice


section Charged

open P48qThirdTwistedField
open P48qTwistedChargeAction (lattice g Momentum)
open LatticeGeneratingFieldLocality (Charge)
open P48qNativeCurrentLocality (stripResidue)
open P48qAllJetWickField (nativeField nativeField_ground)
open P48qCurrentChargedIterate (chargedGround)

open private orbitExponent orderedChargedProduct_coeff_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
open private finiteCoverSlices finiteCoverSlices_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport

local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))

private theorem cleared_sum (a b : Charge lattice) (v : State) (q : Momentum)
    (P : CoverSeries Fock) :
    P * orderedChargedProduct fixedDualBases a b v q =
      ∑ p ∈ v.support, P * orderedChargedProduct fixedDualBases a b
        (Finsupp.single p (v p)) q := by
  let f : State →ₗ[ℂ] CoverSeries Fock :=
    (Finsupp.lapply q).comp (orderedChargedProduct fixedDualBases a b)
  have hv := congrArg f (Finsupp.sum_single v)
  change f (∑ p ∈ v.support, Finsupp.single p (v p)) = f v at hv
  rw [map_sum] at hv
  change P * f v = ∑ p ∈ v.support, P * f (Finsupp.single p (v p))
  rw [← Finset.mul_sum, hv]

private theorem charged_cleared_finite (a b : Charge lattice) (v : State) (q : Momentum)
    (N : ℕ) (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    finiteCoverSlices ((Xc ^ 3 - Yc ^ 3) ^ N * orderedChargedProduct fixedDualBases a b v q) := by
  rw [cleared_sum]
  exact finiteCoverSlices_sum _ _ (fun p _ =>
    clearedOrderedChargedProduct_finiteSlice fixedDualBases a b p q (v p) N hN)

private theorem charged_cleared_swap (a b : Charge lattice) (v : State) (q : Momentum)
    (k l : ℤ) :
    ((((Xc ^ 3 - Yc ^ 3) ^ chargedLocalityOrder a b *
      orderedChargedProduct fixedDualBases a b v q).coeff l).coeff k) =
    ((((Yc ^ 3 - Xc ^ 3) ^ chargedLocalityOrder a b *
      orderedChargedProduct fixedDualBases b a v q).coeff k).coeff l) := by
  rw [cleared_sum, cleared_sum]
  simp only [HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun p _ =>
    clearedOrderedChargedProduct_coeff_swap fixedDualBases a b p q (v p) k l

/-- The native charged fields, restricted to the two selected exponent classes,
have ordinary residue given by the common finite slice of their actual radial
products cleared by the charged locality polynomial. -/
theorem chargedGround_strippedResidue_coverSlice (a b : Charge lattice)
    (v : State) (q : Momentum) (s t H : ℤ) (m : ℕ) :
    let N := chargedLocalityOrder a b
    HVertexOperator.coeff (SignedFieldResidueLocality.residueField 1 ((N : ℤ) - m - 1)
      (stripResidue s (nativeField (chargedGround a)))
      (stripResidue t (nativeField (chargedGround b)))).operator (H + N - m) v q =
      ∑ᶠ l : ℤ, Ring.choose (l : ℂ) m • coverSlice
        ((Xc ^ 3 - Yc ^ 3) ^ N * orderedChargedProduct fixedDualBases a b v q)
        s t (H + N) l := by
  dsimp only
  rw [show chargedGround a = Finsupp.single a 1 by rfl,
    show chargedGround b = Finsupp.single b 1 by rfl,
    nativeField_ground, nativeField_ground]
  apply strippedResidue_coverSlice _ _ _ _ _ _ _ _ _ _
    (orderedChargedProduct fixedDualBases b a v q)
  · exact orderedChargedProduct_coeff_apply fixedDualBases a b v q
  · intro k l
    exact orderedChargedProduct_coeff_apply fixedDualBases b a v q l k
  · exact charged_cleared_finite a b v q _
      (fun j hj => ThirdTwistedContraction.contractionLocalityOrder_add_nonneg lattice g a b hj)
  · exact charged_cleared_swap a b v q

#print axioms chargedGround_strippedResidue_coverSlice

end Charged


section Collision

open P48qThirdTwistedField
open PowerSeries (binomialSeries)
open private coverRatioPower readout_support finiteCoverSlices from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport
open private diagonalXOverYUnit coe_diagonalXOverYUnit mapScalarToFock from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

private def binomialUnits : Multiplicative ℂ →* (PowerSeries ℂ)ˣ where
  toFun a := Units.mkOfMulEqOne
    (binomialSeries ℂ a.toAdd) (binomialSeries ℂ (-a.toAdd)) (by
      rw [← PowerSeries.binomialSeries_add, add_neg_cancel, PowerSeries.binomialSeries_zero])
  map_one' := Units.ext (PowerSeries.binomialSeries_zero)
  map_mul' a b := Units.ext (PowerSeries.binomialSeries_add (A := ℂ) a.toAdd b.toAdd)

private theorem coverRatioPower_eq (i : ℤ) :
    coverRatioPower i = binomialSeries Fock ((i : ℂ) / 3) := by
  have h₀ : diagonalXOverYUnit = binomialUnits (Multiplicative.ofAdd (1 / 3 : ℂ)) :=
    Units.ext coe_diagonalXOverYUnit
  rw [coverRatioPower, h₀, ← map_zpow]
  change mapScalarToFock (binomialSeries ℂ (i • (1 / 3 : ℂ))) = _
  rw [zsmul_eq_mul, mul_one_div]
  ext j
  simp [mapScalarToFock, PowerSeries.coeff_map, Algebra.smul_def]

private theorem coeff_diagonal_strip {A : CoverSeries Fock}
    (hA : finiteCoverSlices A) (s t H : ℤ) (m : ℕ)
    (hsupport : ∀ k l, k % 3 ≠ s % 3 ∨ l % 3 ≠ t % 3 →
      (A.coeff l).coeff k = 0) :
    PowerSeries.coeff m (binomialSeries Fock (-(s : ℂ) / 3) *
      diagonalCoverReadout A (3 * H + s + t)) =
      ∑ᶠ l : ℤ, Ring.choose (l : ℂ) m • coverSlice A s t H l := by
  let K := binomialSeries Fock (-(s : ℂ) / 3)
  let h := 3 * H + s + t
  let f (k : ℤ) := PowerSeries.C ((A.coeff (h - k)).coeff k) * coverRatioPower k
  have hf : Function.HasFiniteSupport f := readout_support hA h
  change PowerSeries.coeff m (K * ∑ᶠ k, f k) = _
  have hf' : Function.HasFiniteSupport (fun k => K * f k) :=
    hf.subset (fun k hk hz => hk (show K * f k = 0 by rw [hz, mul_zero]))
  rw [mul_finsum' _ _ hf, map_finsum _ hf']
  let e (l : ℤ) := 3 * l + s
  rw [finsum_on_range e (by intro x y he; dsimp [e] at he; omega)]
  · congr 1
    funext l
    have hk : h - e l = 3 * (H - l) + t := by dsimp [h, e]; ring
    have he : -(s : ℂ) / 3 + ((e l : ℤ) : ℂ) / 3 = l := by
      dsimp [e]; push_cast; ring
    simp only [f, hk, coverRatioPower_eq, K]
    rw [mul_left_comm, ← PowerSeries.binomialSeries_add, he,
      PowerSeries.coeff_C_mul, PowerSeries.binomialSeries_coeff, Algebra.mul_smul_comm,
      mul_one]
    rfl
  · intro k hk
    have hn : k % 3 ≠ s % 3 := by
      intro he
      exact hk ⟨(k - s) / 3, by dsimp [e]; omega⟩
    simp only [f, hsupport k (h - k) (Or.inl hn), map_zero, zero_mul, mul_zero]

end Collision

#print axioms coeff_diagonal_strip


section Projected

open P48qThirdTwistedField
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open NativeStandardThirdLift (standardLift standardLift_ground_single)
open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qCurrentChargedIterate (chargedGround)
open P48qAllJetWickField (NativeStates nativeField nativeField_ground)
open P48qNativeCurrentLocality (Field InResidue nativeField_inResidue stripResidue
  restoreResidue_coeff coverDelta coverComm)
open P48qNativeResidueProduct (adjustedResidue clearedResidue binomialTail adjustedResidue_eq_iff)
open LatticeAllStateReconstruction (mu)
open PowerSeries (binomialSeries)

open private coverMonomial_pow coverMonomial_mul_coeff orbitExponent
  orderedChargedProduct_coeff_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
open private finiteCoverSlices finiteCoverSlices_sum diagonalCoverReadout_sum readout_support from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport
open private liftProject liftProject_eigen groundProject_mem groundSpan chargeGround from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativePairwiseLocality

local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))
local notation "ιF" => HahnSeries.ofPowerSeries ℤ Fock
local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem clear_coeff (A : CoverSeries Fock) (k l : ℤ) :
    ((((Xc ^ 3 - Yc ^ 3) * A).coeff l).coeff k) =
      (A.coeff l).coeff (k - 3) - (A.coeff (l - 3)).coeff k := by
  simp only [sub_mul, HahnSeries.coeff_sub, coverMonomial_pow, Nat.cast_ofNat, mul_one,
    mul_zero, coverMonomial_mul_coeff, sub_zero, one_mul]

private theorem clear_coeff_swap (A : CoverSeries Fock) (k l : ℤ) :
    ((((Yc ^ 3 - Xc ^ 3) * A).coeff k).coeff l) =
      (A.coeff (k - 3)).coeff l - (A.coeff k).coeff (l - 3) := by
  simp only [sub_mul, HahnSeries.coeff_sub, coverMonomial_pow, Nat.cast_ofNat, mul_one,
    mul_zero, coverMonomial_mul_coeff, sub_zero, one_mul]

private theorem charged_cleared_swap_mono (a b : Charge lattice) (v : State) (q : Momentum)
    (N : ℕ) (hN : chargedLocalityOrder a b ≤ N) (k l : ℤ) :
    ((((Xc ^ 3 - Yc ^ 3) ^ N * orderedChargedProduct fixedDualBases a b v q).coeff l).coeff k) =
    ((((Yc ^ 3 - Xc ^ 3) ^ N * orderedChargedProduct fixedDualBases b a v q).coeff k).coeff l) := by
  induction N, hN using Nat.le_induction generalizing k l with
  | base => exact charged_cleared_swap a b v q k l
  | succ N _ ih =>
    rw [pow_succ' (Xc ^ 3 - Yc ^ 3), pow_succ' (Yc ^ 3 - Xc ^ 3), mul_assoc, mul_assoc,
      clear_coeff, clear_coeff_swap, ih, ih]

private theorem cleared_off_residue (L : CoverSeries Fock) (s t : ℤ)
    (hL : ∀ k l, k % 3 ≠ s % 3 ∨ l % 3 ≠ t % 3 → (L.coeff l).coeff k = 0)
    (N : ℕ) (k l : ℤ) (hk : k % 3 ≠ s % 3 ∨ l % 3 ≠ t % 3) :
    ((((Xc ^ 3 - Yc ^ 3) ^ N * L).coeff l).coeff k) = 0 := by
  induction N generalizing k l with
  | zero => simpa using hL k l hk
  | succ N ih =>
    rw [pow_succ', mul_assoc, clear_coeff, ih, ih, sub_self]
    · simpa only [show (l - 3) % 3 = l % 3 by omega] using hk
    · simpa only [show (k - 3) % 3 = k % 3 by omega] using hk

private theorem clear_radial_locality (A B : Field) (N : ℕ)
    (L R : State → Momentum → CoverSeries Fock)
    (hL : ∀ v q k l, ((L v q).coeff l).coeff k =
      HVertexOperator.coeff A k (HVertexOperator.coeff B l v) q)
    (hR : ∀ v q k l, ((R v q).coeff k).coeff l =
      HVertexOperator.coeff B l (HVertexOperator.coeff A k v) q)
    (hSwap : ∀ v q k l, (((Xc ^ 3 - Yc ^ 3) ^ N * L v q).coeff l).coeff k =
      (((Yc ^ 3 - Xc ^ 3) ^ N * R v q).coeff k).coeff l) :
    coverDelta^[N] (coverComm A B) = 0 := by
  have h (n : ℕ) (v : State) (q : Momentum) (k l : ℤ) :
      (coverDelta^[n] (coverComm A B) k l) v q =
        (((Xc ^ 3 - Yc ^ 3) ^ n * L v q).coeff l).coeff k -
          (((Yc ^ 3 - Xc ^ 3) ^ n * R v q).coeff k).coeff l := by
    induction n generalizing k l with
    | zero =>
      simp only [Function.iterate_zero_apply, coverComm, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, pow_zero, one_mul, hL, hR]
    | succ n ih =>
      rw [Function.iterate_succ_apply', coverDelta, LinearMap.sub_apply, Finsupp.sub_apply,
        ih, ih, pow_succ' (Xc ^ 3 - Yc ^ 3), pow_succ' (Yc ^ 3 - Xc ^ 3),
        mul_assoc, mul_assoc, clear_coeff, clear_coeff_swap]
      abel
  funext k l
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro q
  rw [h, hSwap, sub_self]
  rfl

private theorem scalar_series_smul (c : ℂ) (A : CoverSeries Fock) :
    c • A = coverMonomial 0 0 (algebraMap ℂ Fock c) * A := by
  ext l k
  rw [coverMonomial_mul_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, sub_zero,
    sub_zero, ← Algebra.smul_def]

private theorem cleared_smul (P A : CoverSeries Fock) (c : ℂ) :
    P * (c • A) = c • (P * A) := by
  rw [scalar_series_smul c A, scalar_series_smul c (P * A)]
  ac_rfl

private theorem finiteCoverSlices_smul {A : CoverSeries Fock} (hA : finiteCoverSlices A) (c : ℂ) :
    finiteCoverSlices (c • A) := by
  intro h
  refine (hA h).subset ?_
  intro k hk hz
  exact hk (by simp only [HahnSeries.coeff_smul, show (A.coeff (h - k)).coeff k = 0 from
    hz, smul_zero])

private theorem diagonalCoverReadout_smul {A : CoverSeries Fock}
    (hA : finiteCoverSlices A) (c : ℂ) (h : ℤ) :
    diagonalCoverReadout (c • A) h = c • diagonalCoverReadout A h := by
  have hh := readout_support hA h
  rw [diagonalCoverReadout, diagonalCoverReadout, smul_finsum' _ hh]
  congr 1
  funext k
  simp only [HahnSeries.coeff_smul]
  have hC (x : Fock) : PowerSeries.C (c • x) = c • PowerSeries.C x := by
    ext j
    simp only [PowerSeries.coeff_C, PowerSeries.coeff_smul]
    split_ifs <;> simp
  rw [hC, smul_mul_assoc]

end Projected


section FiniteGroundSums

open P48qThirdTwistedField
open P48qTwistedChargeAction (lattice g g_cube g_isometry Momentum)
open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qCurrentChargedIterate (chargedGround)
open P48qAllJetWickField (NativeStates nativeField nativeField_ground)
open LatticeAllStateReconstruction (mu)
open P48qNativeCurrentLocality (InResidue restoreResidue_coeff coverComm coverDelta)
open P48qNativeResidueProduct (adjustedResidue clearedResidue binomialTail adjustedResidue_eq_iff
  clearedResidue_zero_of_locality)
open PowerSeries (binomialSeries)
open private orbitExponent orderedChargedProduct_coeff_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
open private finiteCoverSlices finiteCoverSlices_sum diagonalCoverReadout_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalTransport

local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))
local notation "ιF" => HahnSeries.ofPowerSeries ℤ Fock

private def groundSum {I : Type*} [Fintype I] (a : I → Charge lattice) (u : I → ℂ) :
    NativeStates := ∑ i, u i • chargedGround (a i)

private def radialGroundSum {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (v : State) (q : Momentum) : CoverSeries Fock :=
  ∑ i, u i • ∑ j, w j • orderedChargedProduct fixedDualBases (a i) (b j) v q

private theorem radialGroundSum_coeff {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (v : State) (q : Momentum) (k l : ℤ) :
    ((radialGroundSum a b u w v q).coeff l).coeff k =
      HVertexOperator.coeff (nativeField (groundSum a u)) k
        (HVertexOperator.coeff (nativeField (groundSum b w)) l v) q := by
  simp only [radialGroundSum, HahnSeries.coeff_sum, HahnSeries.coeff_smul,
    orderedChargedProduct_coeff_apply, groundSum, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.smul_apply,
    Finset.sum_apply']
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm]
  have hfield (c : Charge lattice) (d : ℤ) :
      HVertexOperator.coeff (nativeField (chargedGround c)) d = fieldCoeff fixedDualBases c d := by
    rw [show chargedGround c = Finsupp.single c 1 by rfl, nativeField_ground]
    rfl
  rw [hfield, hfield]

private theorem orbit_nonneg_of_le (a b : Charge lattice) (N : ℕ)
    (hN : chargedLocalityOrder a b ≤ N) (j : ℕ) (hj : j ∈ Finset.range 3) :
    0 ≤ (N : ℤ) + orbitExponent a b j := by
  have h := ThirdTwistedContraction.contractionLocalityOrder_add_nonneg lattice g a b hj
  change 0 ≤ (chargedLocalityOrder a b : ℤ) + orbitExponent a b j at h
  omega

private theorem radialGroundSum_cleared_finite {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (v : State) (q : Momentum) (N : ℕ) (hN : ∀ i j, chargedLocalityOrder (a i) (b j) ≤ N) :
    finiteCoverSlices ((Xc ^ 3 - Yc ^ 3) ^ N * radialGroundSum a b u w v q) := by
  simp only [radialGroundSum, Finset.mul_sum, cleared_smul]
  exact finiteCoverSlices_sum _ _ (fun i _ => finiteCoverSlices_smul
    (finiteCoverSlices_sum _ _ (fun j _ => finiteCoverSlices_smul
      (charged_cleared_finite _ _ _ _ _ (orbit_nonneg_of_le _ _ _ (hN i j))) _)) _)

private theorem radialGroundSum_cleared_swap {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (v : State) (q : Momentum) (N : ℕ) (hN : ∀ i j, chargedLocalityOrder (a i) (b j) ≤ N)
    (k l : ℤ) :
    (((Xc ^ 3 - Yc ^ 3) ^ N * radialGroundSum a b u w v q).coeff l).coeff k =
      (((Yc ^ 3 - Xc ^ 3) ^ N * radialGroundSum b a w u v q).coeff k).coeff l := by
  simp only [radialGroundSum, Finset.mul_sum, cleared_smul, HahnSeries.coeff_sum,
    HahnSeries.coeff_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by
    rw [smul_comm, charged_cleared_swap_mono _ _ _ _ _ (hN i j)]))

private theorem mu_groundSum {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ) (n : ℤ) :
    mu lattice (groundSum a u) n (groundSum b w) =
      ∑ i, u i • ∑ j, w j • mu lattice (chargedGround (a i)) n (chargedGround (b j)) := by
  simp only [groundSum, mu, VertexOperator.ncoeff_apply, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm _ _ _

private theorem mu_ground_eq_coeff (a b : Charge lattice) (n : ℤ) :
    mu lattice (chargedGround a) n (chargedGround b) =
      HVertexOperator.coeff
        ((LatticeActualVertexAlgebra.actualVertexAlgebra lattice).stateField (chargedGround a))
        (-n-1) (chargedGround b) := by
  rw [mu, VertexOperator.ncoeff_apply]
  rfl

private theorem groundMode_zero (a b : Charge lattice) (N : ℕ)
    (hN : chargedLocalityOrder a b ≤ N) (n : ℤ) (hn : (N : ℤ) ≤ n) :
    mu lattice (chargedGround a) n (chargedGround b) = 0 := by
  rw [mu_ground_eq_coeff]
  have hb : (0 : ℤ) ≤ (N : ℤ) + bilinear lattice a b :=
    orbit_nonneg_of_le a b N hN 0 (by decide)
  conv_lhs => rw [show -n - 1 = bilinear lattice a b + (-n - 1 - bilinear lattice a b) by ring]
  rw [untwistedChargedGround_coeff]
  simp [LatticeGeneratingFieldLocality.creationCoeff,
    show -n - 1 - bilinear lattice a b < 0 by omega]

private theorem radialGroundSum_weakAssociativity {I J : Type*} [Fintype I] [Fintype J]
    (a : I → Charge lattice) (b : J → Charge lattice) (u : I → ℂ) (w : J → ℂ)
    (v : State) (q : Momentum) (N : ℕ) (hN : ∀ i j, chargedLocalityOrder (a i) (b j) ≤ N)
    (h n : ℤ) :
    (ιF (diagonalCoverReadout ((Xc ^ 3 - Yc ^ 3) ^ N * radialGroundSum a b u w v q) h)).coeff
      ((N : ℤ) - n - 1) =
      HVertexOperator.coeff (nativeField (mu lattice (groundSum a u) n (groundSum b w)))
        (h - 3 * ((N : ℤ) - n - 1)) v q := by
  have hfin (i : I) (j : J) := charged_cleared_finite (a i) (b j) v q N
    (orbit_nonneg_of_le _ _ _ (hN i j))
  simp only [radialGroundSum, Finset.mul_sum, cleared_smul]
  rw [diagonalCoverReadout_sum _ _ (fun i _ => finiteCoverSlices_smul
    (finiteCoverSlices_sum _ _ (fun j _ => finiteCoverSlices_smul (hfin i j) _)) _) h]
  simp_rw [diagonalCoverReadout_smul
    (finiteCoverSlices_sum _ _ (fun j _ => finiteCoverSlices_smul (hfin _ j) _)),
    diagonalCoverReadout_sum _ _ (fun j _ => finiteCoverSlices_smul (hfin _ j) _)]
  simp_rw [diagonalCoverReadout_smul (hfin _ _)]
  have emb_smul (c : ℂ) (S : PowerSeries Fock) : ιF (c • S) = c • ιF S := by
    ext k
    simp only [PowerSeries.coeff_coe, HahnSeries.coeff_smul, PowerSeries.coeff_smul]
    split_ifs <;> simp
  rw [mu_groundSum]
  simp only [map_sum, map_smul, emb_smul, HahnSeries.coeff_sum, HahnSeries.coeff_smul,
    Finset.sum_apply, Pi.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    Finsupp.smul_apply, Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [mu_ground_eq_coeff]
  simpa only [show -n - 1 + (N : ℤ) = N - n - 1 by ring] using
    chargedGround_weakAssociativity_cover_coeff (a i) (b j) v q N
      (orbit_nonneg_of_le _ _ _ (hN i j)) h (-n - 1)

end FiniteGroundSums

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedResidueProduct
