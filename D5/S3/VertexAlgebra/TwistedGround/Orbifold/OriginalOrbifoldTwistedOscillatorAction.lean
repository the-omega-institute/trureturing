/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedOscillatorAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedOscillatorAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fixed quadratic modes separate normally ordered half-current pairs. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedGroundAction
import D5.S3.VertexAlgebra.ActualTensorGroundIntersection
import Batteries.Tactic.OpenPrivate

/-! Quadratic jet modes of the original fixed algebra on the algebraic twisted tensor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedOscillatorAction

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFock LatticeHalfFockFiniteCorrection LatticeHalfFockCorrectedConformal
open LatticeInvolution (FixedCarrier fixedVacuum mem_fixedSpace thetaLinear theta_single sigma_X)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open OriginalOrbifoldSectorModules (fixedParityY fixedParitySlice_vacuum_ncoeff)
open LatticeHalfFockParityT (actualParity)
open LatticeHalfFockGroundCompression (iota)
open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldTwistedGroundAction
  (PositiveTwisted Top groundEquiv fixedZeroMode twisted_top_irreducible)
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

open private tensorEnd_mul from D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
open private parity_jet from D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
open private groundEquiv_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedGroundAction
open private polynomialField_one normal_pair_coeff
  current_singleton_identity_current pair_enumeration shiftField_zero
  from D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
open private fixedParitySlice_mode_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldSectorModules

noncomputable section

/-- The neutral source with a differentiated first current and an undifferentiated second. -/
def fixedQuadratic (D : LatticeData) (i j : Fin D.rank) (k : ℕ) : FixedCarrier D :=
  ⟨Finsupp.single 0 (X (i, k) * X (j, 0) : Oscillator D), by
    apply (mem_fixedSpace D _).mpr
    change thetaLinear D (Finsupp.single 0 (X (i, k) * X (j, 0) : Oscillator D)) = _
    rw [theta_single, neg_zero, map_mul, sigma_X, sigma_X, neg_mul_neg]⟩

private abbrev correctionScalar (D : LatticeData) (i j : Fin D.rank) (k : ℕ) : ℂ :=
  pairScalar (k + 1) 1 * (D.G i j : ℂ)

private theorem quadratic_jet_correction (D : LatticeData) (i j : Fin D.rank) (k : ℕ) :
    Corr D 0 (X (i, k) * X (j, 0)) =
      Finsupp.single 0 (X (i, k) * X (j, 0)) +
        Finsupp.single (k + 2) (C (correctionScalar D i j k)) := by
  have source := Corr_monomial_enumeration D 0
    (Finsupp.single (i, k) 1 + Finsupp.single (j, 0) 1)
    [(i, k), (j, 0)] (pair_enumeration D _ _)
  have monomial : monomial (Finsupp.single (i, k) 1 + Finsupp.single (j, 0) 1) (1 : ℂ) =
      X (i, k) * X (j, 0) := by
    simp [MvPolynomial.X]
  rw [monomial] at source
  rw [source]
  have word : correctionWord D 0 [(i, k), (j, 0)] =
      X (some (i, k)) * X (some (j, 0)) +
        C (correctionScalar D i j k) * X none ^ (k + 2) := by
    rw [correctionWord_matching]
    simp [labelledRemainders, correctionWord, insertion, singletonPolynomial,
      bilinear, pairPolynomial, sourceWeight, correctionScalar]
  rw [word, map_add, map_mul, map_mul, map_pow,
    optionEquivLeft_X_some, optionEquivLeft_X_some, optionEquivLeft_C,
    optionEquivLeft_X_none, map_add, ← Polynomial.C_mul]
  apply congrArg (Finsupp.single 0 (X (i, k) * X (j, 0)) + ·)
  apply Finsupp.ext
  intro shift
  change (Polynomial.C (C (correctionScalar D i j k)) * Polynomial.X ^ (k + 2)).coeff shift = _
  rw [Polynomial.coeff_C_mul_X_pow]
  simp only [Finsupp.single_apply, eq_comm]

private theorem quadratic_jet_field (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (k : ℕ) :
    correctedField D hu (fixedQuadratic D i j k).val =
      singletonLinear D hu (i, k) (tensorCurrentField D (ActualGround D hu) j) +
        correctionScalar D i j k • shiftField D hu (k + 2) FieldNormalProduct.identityField := by
  change correctedField D hu (Finsupp.single 0 (X (i, k) * X (j, 0))) = _
  rw [correctedField, Finsupp.lsum_single]
  change (Finsupp.lsum ℂ (fun s : ℕ =>
    (shiftField D hu s).comp (polynomialField D hu 0)))
      (Corr D 0 (X (i, k) * X (j, 0))) = _
  rw [quadratic_jet_correction, map_add]
  simp only [Finsupp.lsum_single, LinearMap.comp_apply, shiftField_zero]
  have base : polynomialField D hu 0 (X (j, 0)) =
      tensorCurrentField D (ActualGround D hu) j := by
    conv_lhs => rw [← mul_one (X (j, 0) : Oscillator D)]
    rw [polynomialField_X_mul, polynomialField_one, current_charged_zero_identity,
      current_singleton_identity_current]
  have constant : C (correctionScalar D i j k) =
      correctionScalar D i j k • (1 : Oscillator D) := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [polynomialField_X_mul, base, constant, map_smul, polynomialField_one,
    current_charged_zero_identity, map_smul]

private theorem normal_jet_pair_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (k : ℕ) (t : ℤ) (v : ActualTensor D hu) :
    (singletonLinear D hu (i, k) (tensorCurrentField D (ActualGround D hu) j)).coeff
      (-2 * (t + k + 2)) v =
        ∑ᶠ m : ℤ, jetScalar k m • tensorPair D (ActualGround D hu) i j m (t - m - 1) v := by
  by_cases hk : k = 0
  · subst k
    rw [normal_pair_coeff]
    simp only [Nat.cast_zero, add_zero, jetScalar, Finset.range_zero, Finset.prod_empty,
      Nat.factorial_zero, Nat.cast_one, div_one, one_smul]
    rw [ite_eq_left (by omega), show (-(-2 * (t + 2)) - 4) / 2 = t by omega]
  rw [singletonLinear_coefficient]
  congr 1
  funext m
  have parity : (-2 * (t + (k : ℤ) + 2) + 2 * m + 2 * (k : ℤ) + 3) % 2 = 1 := by omega
  have index : (-(-2 * (t + (k : ℤ) + 2) + 2 * m + 2 * (k : ℤ) + 3) - 3) / 2 =
      t - m - 1 := by omega
  simp only [flatTerm, flatCoefficient, jetCurrent,
    tensorCurrentField, HVertexOperator.coeff_of_coeff, currentCoeff, parity, ite_true,
    index, tensorPair_eq, tensorCurrent]
  split_ifs <;> simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul]

/-- Physical mode `t+k+1` holds the total half-current frequency at `t` as the jet order varies.
The vacuum correction is supported at total frequency zero. -/
theorem fixed_quadratic_mode_val (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (i j : Fin D.rank) (k : ℕ) (t : ℤ) (v : paritySpace D hu s) :
    (((fixedParityY D hu s (fixedQuadratic D i j k))[[t + k + 1]]) v).val =
      (∑ᶠ m : ℤ, jetScalar k m • tensorPair D (ActualGround D hu) i j m (t - m - 1) v.val) +
        if t = 0 then (pairScalar (k + 1) 1 * (D.G i j : ℂ)) • v.val else 0 := by
  change (((HalfFock.LatticeHalfFockParityField.fixedParitySlice D hu s
    (fixedQuadratic D i j k))[[t + k + 1]]) v).val = _
  rw [fixedParitySlice_mode_val, show -2 * (t + (k : ℤ) + 1) - 2 = -2 * (t + k + 2) by ring,
    quadratic_jet_field]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, LinearMap.add_apply,
    LinearMap.smul_apply]
  rw [normal_jet_pair_coeff, shiftField_coefficient_public, current_identity_coefficient]
  simp only [Nat.cast_add, Nat.cast_ofNat,
    show -2 * (t + (k : ℤ) + 2) + 2 * ((k : ℤ) + 2) = 0 ↔ t = 0 by omega]
  split_ifs <;> simp [correctionScalar]

/- Multiplication by an affine factor preserves the span generated by the jets,
using the successor relation for shifted binomial polynomials. -/
private theorem jet_affine (k : ℕ) (m a : ℤ) :
    ((m : ℂ) - (a : ℂ)) * jetScalar k m =
      (-(a : ℂ) - 3 / 2 - (k : ℂ)) * jetScalar k m -
        (k + 1 : ℂ) * jetScalar (k + 1) m := by
  rw [LatticeHalfFockOriginalTranslation.jet_successor]
  ring

private theorem finite_jet_separation {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (f : ℤ → V) (B : Finset ℤ)
    (supported : Function.support f ⊆ B)
    (moments : ∀ k, (∑ m ∈ B, jetScalar k m • f m) ∈ S) (a : ℤ) :
    f a ∈ S := by
  classical
  have weighted (A : Finset ℤ) (k : ℕ) :
      (∑ m ∈ B, ((∏ b ∈ A, ((m : ℂ) - (b : ℂ))) * jetScalar k m) • f m) ∈ S := by
    induction A using Finset.induction_on generalizing k with
    | empty => simpa using moments k
    | @insert b A hb ih =>
      have expand (m : ℤ) :
          (∏ c ∈ insert b A, ((m : ℂ) - (c : ℂ))) * jetScalar k m =
            (-(b : ℂ) - 3 / 2 - (k : ℂ)) *
              ((∏ c ∈ A, ((m : ℂ) - (c : ℂ))) * jetScalar k m) -
            (k + 1 : ℂ) * ((∏ c ∈ A, ((m : ℂ) - (c : ℂ))) * jetScalar (k + 1) m) := by
        rw [Finset.prod_insert hb, mul_comm ((m : ℂ) - (b : ℂ)), mul_assoc, jet_affine]
        ring
      simp_rw [expand, sub_smul, Finset.sum_sub_distrib]
      simpa only [mul_smul, Finset.smul_sum] using
        S.sub_mem (S.smul_mem (-(b : ℂ) - 3 / 2 - (k : ℂ)) (ih k))
          (S.smul_mem (k + 1 : ℂ) (ih (k + 1)))
  by_cases ha : a ∈ B
  · let c : ℂ := ∏ b ∈ B.erase a, ((a : ℂ) - (b : ℂ))
    have hc : c ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro b hb
      exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hb).1 (Int.cast_injective h).symm)
    have h := weighted (B.erase a) 0
    simp only [jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one] at h
    rw [Finset.sum_eq_single_of_mem a ha] at h
    · change c • f a ∈ S at h
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using S.smul_mem c⁻¹ h
    · intro b hb hba
      have hz : (∏ d ∈ B.erase a, ((b : ℂ) - (d : ℂ))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba, hb⟩) (sub_self _)
      simp only [hz, zero_smul]
  · have hz : f a = 0 := by
      by_contra h
      exact ha (supported h)
    rw [hz]
    exact S.zero_mem

/-- At a given vector, each normally ordered pair is in the linear span of the
actual fixed quadratic source modes and the fixed vacuum mode applied to that vector. -/
theorem tensorPair_mem_fixed_quadratic_span (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ) (i j : Fin D.rank) (m n : ℤ) (v : paritySpace D hu s) :
    tensorPair D (ActualGround D hu) i j m n v.val ∈
      Submodule.span ℂ (insert (((fixedParityY D hu s (fixedVacuum D))[[-1]]) v).val
        (Set.range fun k : ℕ =>
        (((fixedParityY D hu s (fixedQuadratic D i j k))[[m + n + 1 + k + 1]]) v).val)) := by
  classical
  rw [fixedParitySlice_vacuum_ncoeff, ite_eq_left rfl]
  let t := m + n + 1
  let f := fun q : ℤ => tensorPair D (ActualGround D hu) i j q (t - q - 1) v.val
  let finite : Function.HasFiniteSupport f := tensorPair_finite D (ActualGround D hu) i j t v.val
  let B := finite.toFinset
  let W := Submodule.span ℂ (insert v.val (Set.range fun k : ℕ =>
    (((fixedParityY D hu s (fixedQuadratic D i j k))[[t + k + 1]]) v).val))
  have hB : Function.support f ⊆ B := fun _ hq => finite.mem_toFinset.mpr hq
  have moments (k : ℕ) : (∑ q ∈ B, jetScalar k q • f q) ∈ W := by
    have hsupport : Function.support (fun q => jetScalar k q • f q) ⊆ B := by
      intro q hq
      exact hB (fun h => hq (show jetScalar k q • f q = 0 by rw [h, smul_zero]))
    have hmode := fixed_quadratic_mode_val D hu s i j k t v
    change _ = (∑ᶠ q : ℤ, jetScalar k q • f q) + _ at hmode
    rw [finsum_eq_sum_of_support_subset _ hsupport] at hmode
    have h : (((fixedParityY D hu s (fixedQuadratic D i j k))[[t + k + 1]]) v).val ∈ W :=
      Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self k))
    rw [hmode] at h
    have hv : v.val ∈ W := Submodule.subset_span (Set.mem_insert _ _)
    have hscalar : (if t = 0 then correctionScalar D i j k • v.val else 0) ∈ W := by
      split_ifs
      · exact W.smul_mem _ hv
      · exact W.zero_mem
    simpa only [add_sub_cancel_right] using W.sub_mem h hscalar
  have h := finite_jet_separation W f B hB moments m
  change tensorPair D (ActualGround D hu) i j m (t - m - 1) v.val ∈ W at h
  rwa [show t - m - 1 = n by dsimp [t]; omega] at h

/-- Stability under the actual fixed-source modes implies stability under every
normally ordered half-current pair, on the original parity slice. -/
theorem tensorPair_mem_of_fixed_modes (D : LatticeData) (hu : IsUnit D.G.det) (s : ℂ)
    (S : Submodule ℂ (paritySpace D hu s))
    (stable : ∀ (a : FixedCarrier D) (p : ℤ) (v : paritySpace D hu s),
      v ∈ S → ((fixedParityY D hu s a)[[p]]) v ∈ S)
    (i j : Fin D.rank) (m n : ℤ) (v : paritySpace D hu s) (hv : v ∈ S) :
    tensorPair D (ActualGround D hu) i j m n v.val ∈ S.map (paritySpace D hu s).subtype := by
  refine Submodule.span_le.mpr ?_ (tensorPair_mem_fixed_quadratic_span D hu s i j m n v)
  rintro _ (rfl | ⟨k, rfl⟩)
  · exact ⟨_, stable (fixedVacuum D) (-1) v hv, rfl⟩
  · exact ⟨_, stable _ _ v hv, rfl⟩

private theorem tensorCurrent_parity (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (m : ℤ) (w : ActualTensor D hu) :
    actualParity D hu (tensorCurrent D (ActualGround D hu) i m w) =
      -tensorCurrent D (ActualGround D hu) i m (actualParity D hu w) := by
  simpa only [jetCurrent, jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
    Nat.cast_one, div_one, one_smul] using parity_jet D hu (i, 0) m w

private theorem tensorCurrent_product_mem (D : LatticeData) (hu : IsUnit D.G.det)
    (W : Submodule ℂ (ActualTensor D hu))
    (pair_mem : ∀ (i j : Fin D.rank) (m n : ℤ) (w : ActualTensor D hu),
      w ∈ W → tensorPair D (ActualGround D hu) i j m n w ∈ W)
    (i j : Fin D.rank) (m n : ℤ) (w : ActualTensor D hu) (hw : w ∈ W) :
    tensorCurrent D (ActualGround D hu) i m (tensorCurrent D (ActualGround D hu) j n w) ∈ W := by
  have hp := pair_mem i j m n w hw
  by_cases hm : m < 0
  · simpa only [tensorPair_eq, ite_eq_left hm, Module.End.mul_apply] using hp
  rw [tensorPair_eq, ite_eq_right hm, Module.End.mul_apply] at hp
  let scalar := if m + n + 1 = 0 then frequency m * (D.G i j : ℂ) else 0
  let T := ActualGround D hu
  have hunit : tensorEnd D T (1 : Module.End ℂ (Oscillator D)) = 1 := by
    apply TensorProduct.ext'
    intro p g
    simp only [tensorEnd, TensorProduct.map_tmul, Module.End.one_apply, LinearMap.id_apply]
  have h := congrArg (tensorEndLinear D T) (current_heisenberg D i j m n)
  change tensorEndLinear D T (_ - _) = tensorEndLinear D T (scalar • _) at h
  rw [map_sub, map_smul] at h
  change tensorEnd D T (_ * _) - tensorEnd D T (_ * _) = scalar • tensorEnd D T 1 at h
  rw [tensorEnd_mul, tensorEnd_mul, hunit] at h
  have hwcomm := LinearMap.congr_fun h w
  change tensorCurrent D T i m (tensorCurrent D T j n w) -
    tensorCurrent D T j n (tensorCurrent D T i m w) = scalar • w at hwcomm
  rw [sub_eq_iff_eq_add.mp hwcomm]
  exact W.add_mem (W.smul_mem _ hw) hp

private theorem positive_parity (D : LatticeData) (hD : IsUnit D.G.det)
    (v : paritySpace D hD 1) : actualParity D hD v.val = v.val := by
  simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, one_smul] using v.property

private theorem current_stable_extension {V J : Type*} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) (parity : Module.End ℂ V) (current : J → Module.End ℂ V)
    (W_parity : ∀ w ∈ W, parity w = w)
    (flip : ∀ a w, parity (current a w) = -current a (parity w))
    (product : ∀ a b w, w ∈ W → current a (current b w) ∈ W) :
    ∃ U : Submodule ℂ V, W ≤ U ∧ (∀ a, U ≤ U.comap (current a)) ∧
      (∀ w ∈ U, parity w = w → w ∈ W) := by
  let images := Set.range (fun aw : J × W => current aw.1 aw.2.val)
  let U := W ⊔ Submodule.span ℂ images
  have W_le_U : W ≤ U := le_sup_left
  have span_le_U : Submodule.span ℂ images ≤ U := le_sup_right
  have current_U (a : J) : U ≤ U.comap (current a) := by
    apply sup_le
    · intro w hw
      exact span_le_U (Submodule.subset_span (show current a w ∈ images from
        ⟨(a, ⟨w, hw⟩), rfl⟩))
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b, w⟩, rfl⟩
      exact W_le_U (product a b w.val w.property)
  -- The even component of the current-stable subspace is the original subspace.
  let P : Module.End ℂ (V) :=
    (1 / 2 : ℂ) • (LinearMap.id + parity)
  have project_fixed (w : V) (hw : parity w = w) :
      P w = w := by
    change (1 / 2 : ℂ) • (w + parity w) = w
    rw [hw, ← two_smul ℂ, smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
  have project_U : U ≤ W.comap P := by
    apply sup_le
    · intro w hw
      change P w ∈ W
      rwa [project_fixed w (W_parity w hw)]
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, w⟩, rfl⟩
      change (1 / 2 : ℂ) • (current a w.val + parity (current a w.val)) ∈ W
      rw [flip, W_parity w.val w.property, add_neg_cancel, smul_zero]
      exact W.zero_mem
  refine ⟨U, W_le_U, current_U, ?_⟩
  intro w hw he
  have hm : P w ∈ W := project_U hw
  rwa [project_fixed w he] at hm

private theorem tensor_mem_of_ground_and_currents (D : LatticeData) (hD : IsUnit D.G.det)
    (U : Submodule ℂ (ActualTensor D hD))
    (current_U : ∀ i m, U ≤ U.comap (tensorCurrent D (ActualGround D hD) i m))
    (all_ground : ∀ g' : ActualGround D hD, ((1 : Oscillator D) ⊗ₜ[ℂ] g') ∈ U) :
    ∀ w : ActualTensor D hD, w ∈ U := by
  have polynomial (p : Oscillator D) (g' : ActualGround D hD) :
      (p ⊗ₜ[ℂ] g') ∈ U := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : (MvPolynomial.C c : Oscillator D) ⊗ₜ[ℂ] g' =
          c • ((1 : Oscillator D) ⊗ₜ[ℂ] g') := by
        rw [TensorProduct.smul_tmul', MvPolynomial.smul_eq_C_mul, mul_one]
      rw [h]
      exact U.smul_mem c (all_ground g')
    | add p q hp hq => simpa only [TensorProduct.add_tmul] using U.add_mem hp hq
    | mul_X p x hp =>
      have h := current_U x.1 (-(x.2 : ℤ) - 1) hp
      change tensorCurrent D (ActualGround D hD) x.1 (-(x.2 : ℤ) - 1)
        (p ⊗ₜ[ℂ] g') ∈ U at h
      simpa only [tensorCurrent, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply,
        current_negative, LinearMap.mulLeft_apply, mul_comm] using h
  have all_mem (w : ActualTensor D hD) : w ∈ U := by
    induction w using TensorProduct.inductionOn with
    | tmul p g' => exact polynomial p g'
    | add x y hx hy => exact U.add_mem hx hy
  exact all_mem

local notation "hu" => And.left (And.right leech_spec)

/-- The original positive twisted Leech module is irreducible under the actual
physical modes of the theta-fixed source algebra. -/
theorem positive_twisted_irreducible (S : Submodule ℂ PositiveTwisted)
    (stable : ∀ (a : FixedCarrier leechData) (n : ℤ) (v : PositiveTwisted),
      v ∈ S → ((fixedParityY leechData hu 1 a)[[n]]) v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let W := S.map (paritySpace leechData hu 1).subtype
  have mem_W (v : PositiveTwisted) : v.val ∈ W ↔ v ∈ S := by
    constructor
    · rintro ⟨w, hw, he⟩
      exact (Subtype.ext he : w = v) ▸ hw
    · intro hv
      exact ⟨v, hv, rfl⟩
  let currents := fun a : Fin leechData.rank × ℤ =>
    tensorCurrent leechData (ActualGround leechData hu) a.1 a.2
  have pair_mem (i j : Fin leechData.rank) (m n : ℤ) (w : ActualTensor leechData hu)
      (hw : w ∈ W) : tensorPair leechData (ActualGround leechData hu) i j m n w ∈ W := by
    obtain ⟨v, hv, rfl⟩ := hw
    exact tensorPair_mem_of_fixed_modes leechData hu 1 S stable i j m n v hv
  obtain ⟨U, W_le_U, current_U, even_U⟩ :=
    current_stable_extension W (actualParity leechData hu) currents (by
      rintro _ ⟨v, _, rfl⟩
      change actualParity leechData hu v.val = v.val
      exact positive_parity leechData hu v)
      (fun a w => tensorCurrent_parity leechData hu a.1 a.2 w)
      (fun a b w hw => tensorCurrent_product_mem leechData hu W pair_mem a.1 b.1 a.2 b.2 w hw)
  have U_ne_bot : U ≠ ⊥ := by
    obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    intro hU
    have h := W_le_U ((mem_W v).mpr hv)
    rw [hU, Submodule.mem_bot] at h
    exact hne (Subtype.ext h)
  obtain ⟨g, g_ne, hg⟩ :=
    ActualTensorGroundIntersection.nonzero_current_stable_submodule_meets_ground leechData hu
      U U_ne_bot (fun i k w hw => current_U (i, k) hw)
  have ground_value (g' : ActualGround leechData hu) :
      (groundEquiv g').val.val = (1 : Oscillator leechData) ⊗ₜ[ℂ] g' := by
    change (groundEquiv g').val.val = iota leechData hu g'
    exact groundEquiv_val g'
  let S₀ := S.comap Top.subtype
  have g_mem : groundEquiv g ∈ S₀ := by
    change (groundEquiv g).val ∈ S
    apply (mem_W _).mp
    exact even_U _ ((ground_value g).symm ▸ hg)
      (positive_parity leechData hu (groundEquiv g).val)
  have S₀_ne_bot : S₀ ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at g_mem
    exact g_ne (groundEquiv.map_eq_zero_iff.mp g_mem)
  have S₀_top : S₀ = ⊤ :=
    (twisted_top_irreducible S₀ (by
      intro a n ha v hv
      change ((fixedParityY leechData hu 1 a)[[n - 1]]) v.val ∈ S
      exact stable a _ v.val hv)).resolve_left S₀_ne_bot
  have all_ground (g' : ActualGround leechData hu) :
      ((1 : Oscillator leechData) ⊗ₜ[ℂ] g') ∈ U := by
    rw [← ground_value]
    apply W_le_U
    apply (mem_W _).mpr
    change groundEquiv g' ∈ S₀
    rw [S₀_top]
    trivial
  apply top_unique
  intro v _
  exact (mem_W v).mp (even_U v.val
    (tensor_mem_of_ground_and_currents leechData hu U (fun i m => current_U (i, m))
      all_ground v.val)
    (positive_parity leechData hu v))

#print axioms fixed_quadratic_mode_val
#print axioms tensorPair_mem_fixed_quadratic_span
#print axioms tensorPair_mem_of_fixed_modes
#print axioms positive_twisted_irreducible

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedOscillatorAction
