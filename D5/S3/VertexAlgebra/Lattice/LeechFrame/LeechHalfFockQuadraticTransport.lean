/- GID: D5/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LeechFrame/LeechHalfFockQuadraticTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic mode transport under the Leech frame tensor splitting. -/

import D5.S3.VertexAlgebra.Lattice.LeechFrame.LeechHalfFockTensorSplit
import D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal
import Batteries.Tactic.OpenPrivate

/-! Corrected quadratic Heisenberg modes in the actual orthonormal Leech frame.

The coefficient calculation extends the one-jet formula in
`RankOneTwistedParity.quadratic_coefficient` to two arbitrary jet orders, using the
native normal field and finite correction from `LatticeHalfFockCorrectedConformal`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechHalfFockQuadraticTransport

open ActualLeechHyperbolic (leechData)
open ActualLeechHalfFockCurrents (orthonormalBasis orthonormalBasis_pairing)
open ActualLeechHalfFockTensorSplit
open LatticeLightConeCoordinates (E g lin)
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedConformal (current_charged_zero_identity current_identity_coefficient)
open MvPolynomial
open scoped TensorProduct BigOperators

open private pair_enumeration polynomialField_one shiftField_zero
  from D5.S3.VertexAlgebra.LatticeHalfFockCorrectedConformal

/-- The shift-zero word and its neutral Gram contraction, with both jet orders arbitrary.
The occurrence enumeration retains multiplicities when the two labels coincide. -/
private theorem quadratic_corr (D : LatticeData) (i j : Fin D.rank) (a b : ℕ) :
    Corr D 0 (X (i,a) * X (j,b)) =
      Finsupp.single 0 (X (i,a) * X (j,b)) +
        Finsupp.single (a + 1 + (b + 1))
          (C (pairScalar (a+1) (b+1) * (D.G i j : ℂ))) := by
  have h := Corr_monomial_enumeration D 0 _ [(i,a), (j,b)]
    (pair_enumeration D (i,a) (j,b))
  rw [show monomial (Finsupp.single (i,a) 1 + Finsupp.single (j,b) 1) (1 : ℂ) =
    X (i,a) * X (j,b) by simp [MvPolynomial.X]] at h
  rw [h]
  have word : correctionWord D 0 [(i,a), (j,b)] =
      X (some (i,a)) * X (some (j,b)) +
        C (pairScalar (a+1) (b+1) * (D.G i j : ℂ)) * X none ^ (a + 1 + (b + 1)) := by
    rw [correctionWord_matching]
    simp [labelledRemainders, correctionWord, insertion, singletonPolynomial,
      bilinear, pairPolynomial, sourceWeight]
  rw [word, map_add, map_mul, map_mul, map_pow,
    optionEquivLeft_X_some, optionEquivLeft_X_some, optionEquivLeft_C,
    optionEquivLeft_X_none, map_add, ← Polynomial.C_mul]
  congr 1
  apply Finsupp.ext
  intro n
  change (Polynomial.C (C (pairScalar (a+1) (b+1) * (D.G i j : ℂ))) *
    Polynomial.X ^ (a + 1 + (b + 1))).coeff n = _
  rw [Polynomial.coeff_C_mul_X_pow]
  simp only [Finsupp.single_apply, eq_comm]

private theorem quadratic_field (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (a b : ℕ) :
    correctedField D hu (Finsupp.single 0 (X (i,a) * X (j,b))) =
      singletonLinear D hu (i,a) (singletonLinear D hu (j,b) FieldNormalProduct.identityField) +
      (pairScalar (a+1) (b+1) * (D.G i j : ℂ)) •
        shiftField D hu (a + 1 + (b + 1)) FieldNormalProduct.identityField := by
  rw [correctedField, Finsupp.lsum_single]
  change correctedSum D hu 0 (Corr D 0 (X (i,a) * X (j,b))) = _
  rw [quadratic_corr, map_add]
  simp only [correctedSum, Finsupp.lsum_single, LinearMap.comp_apply, shiftField_zero]
  rw [polynomialField_X_mul,
    show (X (j,b) : Oscillator D) = X (j,b) * 1 by rw [mul_one],
    polynomialField_X_mul, polynomialField_one, current_charged_zero_identity]
  rw [show C (pairScalar (a+1) (b+1) * (D.G i j : ℂ)) =
      (pairScalar (a+1) (b+1) * (D.G i j : ℂ)) • (1 : Oscillator D) by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]]
  rw [map_smul, polynomialField_one, current_charged_zero_identity, map_smul]

private theorem singleton_identity_coeff (D : LatticeData) (hu : IsUnit D.G.det)
    (j : Fin D.rank) (b : ℕ) (e : ℤ) :
    (singletonLinear D hu (j,b) FieldNormalProduct.identityField).coeff e =
      if e % 2 = 1 then jetCurrent D hu (j,b) ((-e - 2*(b : ℤ) - 3)/2) else 0 := by
  apply LinearMap.ext
  intro v
  rw [singletonLinear_coefficient]
  have term (k : ℤ) :
      flatTerm D hu FieldNormalProduct.identityField [(j,b)] e v (k, ()) =
      if e + 2*k + 2*(b : ℤ) + 3 = 0 then jetCurrent D hu (j,b) k v else 0 := by
    simp only [flatTerm, flatCoefficient]
    split_ifs with hk hz hz <;>
      simp only [Module.End.mul_apply, current_identity_coefficient, hz, ite_true, ite_false, map_zero]
  simp_rw [term]
  split_ifs with he
  · rw [finsum_eq_single _ ((-e - 2*(b : ℤ) - 3)/2)]
    · rw [ite_eq_left (by omega)]
    · intro k hk
      rw [ite_eq_right (by omega)]
  · simp [show ∀ k : ℤ, e + 2*k + 2*(b : ℤ) + 3 ≠ 0 by intro k; omega]

def doubledExponent (a b : ℕ) (m : ℤ) : ℤ :=
  -2 * (m + (a : ℤ) + 1 + ((b : ℤ) + 1))

private theorem quadratic_basis_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (a b : ℕ) (m : ℤ) (v : ActualTensor D hu) :
    (correctedField D hu (Finsupp.single 0 (X (i,a) * X (j,b)))).coeff
        (doubledExponent a b m) v =
      (∑ᶠ k : ℤ, (jetScalar a k * jetScalar b (m-k-1)) •
        tensorPair D (ActualGround D hu) i j k (m-k-1) v) +
      (if m = 0 then (pairScalar (a+1) (b+1) * (D.G i j : ℂ)) • v else 0) := by
  rw [quadratic_field]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, map_smul, Pi.smul_apply,
    LinearMap.smul_apply]
  rw [singletonLinear_coefficient, shiftField_coefficient_public, current_identity_coefficient]
  have hz : doubledExponent a b m + 2 * ((a + 1 + (b + 1) : ℕ) : ℤ) = 0 ↔ m = 0 := by
    unfold doubledExponent
    push_cast
    omega
  simp only [hz, smul_ite, smul_zero]
  congr 1
  apply finsum_congr
  intro k
  let e := doubledExponent a b m + 2*k + 2*(a : ℤ) + 3
  have hp : e % 2 = 1 := by dsimp [e, doubledExponent]; omega
  have hk : (-e - 2*(b : ℤ) - 3) / 2 = m-k-1 := by
    dsimp [e, doubledExponent]
    omega
  simp only [flatTerm, flatCoefficient]
  change (if k < 0 then jetCurrent D hu (i,a) k *
      (singletonLinear D hu (j,b) FieldNormalProduct.identityField).coeff e
    else (singletonLinear D hu (j,b) FieldNormalProduct.identityField).coeff e *
      jetCurrent D hu (i,a) k) v = _
  rw [singleton_identity_coeff, ite_eq_left hp, hk, tensorPair_eq]
  split_ifs <;> simp [jetCurrent, Module.End.mul_apply, smul_smul, mul_comm]

private theorem quadratic_basis_odd (D : LatticeData) (hu : IsUnit D.G.det)
    (i j : Fin D.rank) (a b : ℕ) (e : ℤ) (he : e % 2 = 1) (v : ActualTensor D hu) :
    (correctedField D hu (Finsupp.single 0 (X (i,a) * X (j,b)))).coeff e v = 0 := by
  rw [quadratic_field]
  simp only [map_add, Pi.add_apply, LinearMap.add_apply, map_smul, Pi.smul_apply,
    LinearMap.smul_apply]
  rw [singletonLinear_coefficient, shiftField_coefficient_public, current_identity_coefficient,
    ite_eq_right (by omega), smul_zero, add_zero]
  have h (k : ℤ) : flatTerm D hu
      (singletonLinear D hu (j,b) FieldNormalProduct.identityField) [(i,a)] e v (k, ()) = 0 := by
    simp only [flatTerm, flatCoefficient, singleton_identity_coeff,
      ite_eq_right (show ¬ (e + 2*k + 2*(a : ℤ) + 3) % 2 = 1 by omega)]
    split_ifs <;> simp
  simp only [h, finsum_zero]

variable {D : LatticeData}

/-- The actual neutral quadratic state, with creation labels (a+1) and (b+1). -/
def quadraticSource (u w : E D) (a b : ℕ) : Carrier D :=
  Finsupp.single 0 (lin a u * lin b w)

private theorem quadraticSource_expand (u w : E D) (a b : ℕ) :
    quadraticSource u w a b =
      ∑ i, ∑ j, (u i * w j) • (Finsupp.single 0 (X (i,a) * X (j,b)) : Carrier D) := by
  change (Finsupp.lsingle (R := ℂ) (0 : Charge D))
    ((∑ i, u i • X (i,a)) * (∑ j, w j • X (j,b))) = _
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, Finsupp.lsingle_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm (w _) (u _)]

/-- A twisted current with the native polarization and identity ground action. -/
def polarizedTensorCurrent (hu : IsUnit D.G.det) (u : E D) (k : ℤ) :
    Module.End ℂ (ActualTensor D hu) :=
  tensorEnd D (ActualGround D hu) (polarizedCurrent k u)

private theorem polarizedTensorCurrent_expand (hu : IsUnit D.G.det) (u : E D) (k : ℤ) :
    polarizedTensorCurrent hu u k =
      ∑ i, u i • tensorCurrent D (ActualGround D hu) i k := by
  change tensorEndLinear D (ActualGround D hu) (∑ i, u i • current D i k) = _
  simp only [map_sum, map_smul]
  rfl

/-- Place the first current on the left at negative mode labels and on the right otherwise. -/
def normalProduct {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : ℤ → Module.End ℂ V) (k l : ℤ) : Module.End ℂ V :=
  if k < 0 then A k * B l else B l * A k

/-- The native truncation interval for a quadratic coefficient at mode sum (m). -/
def modeInterval (m : ℤ) (R : ℕ) : Finset ℤ :=
  Finset.Icc (min (m - R) 0) ((R : ℤ) - 1)

private theorem normalProduct_zero_outside {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : ℤ → Module.End ℂ V) (v : V) (m : ℤ) (R : ℕ)
    (hA : ∀ k : ℤ, (R : ℤ) ≤ k → A k v = 0)
    (hB : ∀ k : ℤ, (R : ℤ) ≤ k → B k v = 0)
    (k : ℤ) (hk : k ∉ modeInterval m R) :
    normalProduct A B k (m-k-1) v = 0 := by
  simp only [modeInterval, Finset.mem_Icc] at hk
  by_cases h : k < 0
  · have hl : (R : ℤ) ≤ m-k-1 := by omega
    simp only [normalProduct, ite_eq_left h, Module.End.mul_apply, hB _ hl, map_zero]
  · have hr : (R : ℤ) ≤ k := by omega
    simp only [normalProduct, ite_eq_right h, Module.End.mul_apply, hA _ hr, map_zero]

private theorem polarizedPair_expand (hu : IsUnit D.G.det) (u w : E D)
    (k l : ℤ) (v : ActualTensor D hu) :
    normalProduct (polarizedTensorCurrent hu u) (polarizedTensorCurrent hu w) k l v =
      ∑ i, ∑ j, (u i * w j) • tensorPair D (ActualGround D hu) i j k l v := by
  simp only [normalProduct, tensorPair_eq, polarizedTensorCurrent_expand]
  split_ifs
  · simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm (w _) (u _)]
  · simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, smul_smul]

/-- The actual corrected quadratic coefficient with both polarizations arbitrary.
Any bound for the standard native currents on the input gives the stated finite sum. -/
theorem quadratic_coefficient (hu : IsUnit D.G.det) (u w : E D) (a b : ℕ) (m : ℤ)
    (v : ActualTensor D hu) (R : ℕ)
    (hR : ∀ (i : Fin D.rank) (k : ℤ), (R : ℤ) ≤ k →
      tensorCurrent D (ActualGround D hu) i k v = 0) :
    (correctedField D hu (quadraticSource u w a b)).coeff (doubledExponent a b m) v =
      (∑ k ∈ modeInterval m R, (jetScalar a k * jetScalar b (m-k-1)) •
        normalProduct (polarizedTensorCurrent hu u) (polarizedTensorCurrent hu w)
          k (m-k-1) v) +
      (if m = 0 then (pairScalar (a+1) (b+1) * g D u w) • v else 0) := by
  have hb (i j : Fin D.rank) :
      (∑ᶠ k : ℤ, (jetScalar a k * jetScalar b (m-k-1)) •
        tensorPair D (ActualGround D hu) i j k (m-k-1) v) =
      ∑ k ∈ modeInterval m R, (jetScalar a k * jetScalar b (m-k-1)) •
        tensorPair D (ActualGround D hu) i j k (m-k-1) v := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    change (jetScalar a k * jetScalar b (m-k-1)) •
      tensorPair D (ActualGround D hu) i j k (m-k-1) v ≠ 0 at hk
    have hn : tensorPair D (ActualGround D hu) i j k (m-k-1) v ≠ 0 :=
      fun he => hk (by rw [he, smul_zero])
    simpa only [modeInterval, Finset.mem_coe, Finset.mem_Icc, Set.mem_Icc] using
      tensorPair_support_of_bound D (ActualGround D hu) i j m v R hR hn
  simp only [quadraticSource_expand, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    Pi.smul_apply, LinearMap.smul_apply, quadratic_basis_coefficient, hb,
    smul_add, Finset.sum_add_distrib, polarizedPair_expand]
  congr 1
  · simp only [Finset.smul_sum, smul_smul]
    let term (i j : Fin D.rank) (k : ℤ) :=
      (u i * w j * (jetScalar a k * jetScalar b (m-k-1))) •
        tensorPair D (ActualGround D hu) i j k (m-k-1) v
    calc
      (∑ i, ∑ j, ∑ k ∈ modeInterval m R, term i j k) =
          ∑ i, ∑ k ∈ modeInterval m R, ∑ j, term i j k :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ k ∈ modeInterval m R, ∑ i, ∑ j, term i j k := Finset.sum_comm
      _ = _ := by simp only [term, mul_comm (u _ * w _)]
  · split_ifs with hm
    · simp only [smul_smul, ← Finset.sum_smul, g, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    · simp

theorem quadratic_coefficient_odd (hu : IsUnit D.G.det) (u w : E D) (a b : ℕ)
    (e : ℤ) (he : e % 2 = 1) :
    (correctedField D hu (quadraticSource u w a b)).coeff e = 0 := by
  apply LinearMap.ext
  intro v
  simp only [quadraticSource_expand, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smul,
    Pi.smul_apply, LinearMap.smul_apply, quadratic_basis_odd D hu _ _ _ _ e he, smul_zero,
    Finset.sum_const_zero, LinearMap.zero_apply]

private def singleBound (p : SinglePolynomial) : ℕ :=
  p.vars.sup Nat.succ

private theorem singleCurrent_vanish (p : SinglePolynomial) (k : ℤ)
    (hk : (singleBound p : ℤ) ≤ k) : singleCurrent k p = 0 := by
  classical
  have hpos : 0 ≤ k := by omega
  lift k to ℕ using hpos
  have hvars : k ∉ p.vars := by
    intro h
    have hb : k + 1 ≤ singleBound p := Finset.le_sup (f := Nat.succ) h
    omega
  change (k + 1 / 2 : ℂ) • MvPolynomial.pderiv k p = 0
  rw [pderiv_eq_zero_of_notMem_vars hvars, smul_zero]

private theorem single_normal_finite (a b : ℕ) (m : ℤ) (p : SinglePolynomial) :
    Function.HasFiniteSupport (fun k : ℤ => (jetScalar a k * jetScalar b (m-k-1)) •
      normalProduct singleCurrent singleCurrent k (m-k-1) p) := by
  refine (modeInterval m (singleBound p)).finite_toSet.subset ?_
  intro k hk
  by_contra hout
  apply hk
  dsimp only
  rw [normalProduct_zero_outside _ _ p m (singleBound p)
    (singleCurrent_vanish p) (singleCurrent_vanish p) k hout, smul_zero]

/-- The finite-on-input normalized rank-one quadratic coefficient. The
scalar correction is the one for a Heisenberg vector of Gram norm one. -/
def singleQuadraticMode (a b : ℕ) (m : ℤ) : Module.End ℂ SinglePolynomial :=
  (show Module.End ℂ SinglePolynomial from
    { toFun := fun p => ∑ᶠ k : ℤ, (jetScalar a k * jetScalar b (m-k-1)) •
        normalProduct singleCurrent singleCurrent k (m-k-1) p
      map_add' p q := by
        simp only [map_add, smul_add]
        exact finsum_add_distrib (single_normal_finite a b m p) (single_normal_finite a b m q)
      map_smul' z p := by
        simp only [RingHom.id_apply, map_smul, smul_comm _ z]
        exact (smul_finsum' z (single_normal_finite a b m p)).symm }) +
  (if m = 0 then pairScalar (a+1) (b+1) • LinearMap.id else 0)

theorem singleQuadraticMode_interval (a b : ℕ) (m : ℤ) (p : SinglePolynomial)
    (R : ℕ) (hR : ∀ k : ℤ, (R : ℤ) ≤ k → singleCurrent k p = 0) :
    singleQuadraticMode a b m p =
      (∑ k ∈ modeInterval m R, (jetScalar a k * jetScalar b (m-k-1)) •
        normalProduct singleCurrent singleCurrent k (m-k-1) p) +
      (if m = 0 then pairScalar (a+1) (b+1) • p else 0) := by
  have hf : (∑ᶠ k : ℤ, (jetScalar a k * jetScalar b (m-k-1)) •
      normalProduct singleCurrent singleCurrent k (m-k-1) p) =
      ∑ k ∈ modeInterval m R, (jetScalar a k * jetScalar b (m-k-1)) •
        normalProduct singleCurrent singleCurrent k (m-k-1) p := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hout
    apply hk
    dsimp only
    rw [normalProduct_zero_outside _ _ p m R hR hR k hout, smul_zero]
  unfold singleQuadraticMode
  rw [LinearMap.add_apply]
  change (∑ᶠ k : ℤ, (jetScalar a k * jetScalar b (m-k-1)) •
    normalProduct singleCurrent singleCurrent k (m-k-1) p) + _ = _
  rw [hf]
  split_ifs <;> simp

abbrev FrameIndex := ActualLeechNormFourFrame.Index

/-- The polarized creation state at one coordinate of the verified unit Leech frame. -/
abbrev frameQuadraticSource (c : FrameIndex) (a b : ℕ) : Carrier leechData :=
  quadraticSource (orthonormalBasis c) (orthonormalBasis c) a b

variable (c : FrameIndex) (hu : IsUnit leechData.G.det)

private theorem nativeTensorSplit_tensorEnd (A : Module.End ℂ (Oscillator leechData)) :
    (nativeTensorSplit c hu).conj (tensorEnd leechData (ActualGround leechData hu) A) =
      TensorProduct.map ((nativeSplit c).toLinearEquiv.conj A) LinearMap.id := by
  apply TensorProduct.ext'
  intro p t
  change nativeSplit c (A ((nativeSplit c).symm p)) ⊗ₜ[ℂ] t =
    nativeSplit c (A ((nativeSplit c).symm p)) ⊗ₜ[ℂ] t
  rfl

/-- Lift a selected-factor endomorphism to the split twisted module. -/
abbrev onSingle (A : Module.End ℂ SinglePolynomial) :
    Module.End ℂ (SplitPolynomial c ⊗[ℂ] ActualGround leechData hu) :=
  TensorProduct.map (TensorProduct.map A LinearMap.id) LinearMap.id

theorem nativeTensorSplit_current_single (k : ℤ) :
    (nativeTensorSplit c hu).conj (polarizedTensorCurrent hu (orthonormalBasis c) k) =
      onSingle c hu (singleCurrent k) := by
  rw [polarizedTensorCurrent, nativeTensorSplit_tensorEnd, nativeSplit_current_single]

theorem nativeTensorSplit_current_complement (d : Complement c) (k : ℤ) :
    (nativeTensorSplit c hu).conj (polarizedTensorCurrent hu (orthonormalBasis d.val) k) =
      TensorProduct.map (TensorProduct.map LinearMap.id (complementCurrent d k)) LinearMap.id := by
  rw [polarizedTensorCurrent, nativeTensorSplit_tensorEnd, nativeSplit_current_complement]

private theorem onSingle_mul (A B : Module.End ℂ SinglePolynomial) :
    onSingle c hu (A * B) = onSingle c hu A * onSingle c hu B := by
  apply TensorProduct.ext'
  intro p t
  simp only [onSingle, TensorProduct.map_tmul, LinearMap.id_apply, Module.End.mul_apply]
  congr 1
  have h : TensorProduct.map (A * B) (LinearMap.id : Module.End ℂ (ComplementPolynomial c)) =
      TensorProduct.map A LinearMap.id * TensorProduct.map B LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, Module.End.mul_apply]
  exact LinearMap.congr_fun h p

private theorem nativeTensorSplit_normalProduct (k l : ℤ) :
    (nativeTensorSplit c hu).conj
      (normalProduct (polarizedTensorCurrent hu (orthonormalBasis c))
        (polarizedTensorCurrent hu (orthonormalBasis c)) k l) =
      onSingle c hu (normalProduct singleCurrent singleCurrent k l) := by
  simp only [normalProduct]
  split_ifs <;> rw [onSingle_mul] <;>
    simp only [Module.End.mul_eq_comp, LinearEquiv.conj_comp, nativeTensorSplit_current_single]

/-- Finite readout at an arbitrary native input, in split coordinates. -/
theorem nativeTensorSplit_quadratic_interval (a b : ℕ) (m : ℤ)
    (v : ActualTensor leechData hu) (R : ℕ)
    (hR : ∀ (i : Fin leechData.rank) (k : ℤ), (R : ℤ) ≤ k →
      tensorCurrent leechData (ActualGround leechData hu) i k v = 0) :
    nativeTensorSplit c hu
        ((correctedField leechData hu (frameQuadraticSource c a b)).coeff
          (doubledExponent a b m) v) =
      (∑ k ∈ modeInterval m R, (jetScalar a k * jetScalar b (m-k-1)) •
        onSingle c hu (normalProduct singleCurrent singleCurrent k (m-k-1))
          (nativeTensorSplit c hu v)) +
      (if m = 0 then pairScalar (a+1) (b+1) • nativeTensorSplit c hu v else 0) := by
  rw [quadratic_coefficient hu _ _ a b m v R hR]
  simp only [orthonormalBasis_pairing, ite_true, mul_one, map_add, map_sum, map_smul,
    apply_ite (nativeTensorSplit c hu), map_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun (nativeTensorSplit_normalProduct c hu k (m-k-1)) (nativeTensorSplit c hu v)

/-- Every actual corrected mode of a selected-frame quadratic transports to
the normalized rank-one coefficient tensored with the two identities. -/
theorem nativeTensorSplit_quadratic_mode (a b : ℕ) (m : ℤ) :
    (nativeTensorSplit c hu).conj
        ((correctedField leechData hu (frameQuadraticSource c a b)).coeff
          (doubledExponent a b m)) =
      onSingle c hu (singleQuadraticMode a b m) := by
  apply TensorProduct.ext'
  intro pq t
  induction pq using TensorProduct.inductionOn with
  | add pq qr hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
  | tmul p q =>
    let y : SplitPolynomial c ⊗[ℂ] ActualGround leechData hu := (p ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] t
    let v := (nativeTensorSplit c hu).symm y
    have hsplit : nativeTensorSplit c hu v = y := (nativeTensorSplit c hu).apply_symm_apply y
    obtain ⟨N, hN⟩ := tensor_current_truncation leechData (ActualGround leechData hu) v
    let R := max N (singleBound p)
    have hR : ∀ (i : Fin leechData.rank) (k : ℤ), (R : ℤ) ≤ k →
        tensorCurrent leechData (ActualGround leechData hu) i k v = 0 :=
      fun i k hk => hN i k ((by exact_mod_cast le_max_left N (singleBound p) :
        (N : ℤ) ≤ (R : ℤ)).trans hk)
    have hP : ∀ k : ℤ, (R : ℤ) ≤ k → singleCurrent k p = 0 :=
      fun k hk => singleCurrent_vanish p k ((by exact_mod_cast le_max_right N (singleBound p) :
        (singleBound p : ℤ) ≤ (R : ℤ)).trans hk)
    have h := nativeTensorSplit_quadratic_interval c hu a b m v R hR
    rw [hsplit] at h
    change nativeTensorSplit c hu
      ((correctedField leechData hu (frameQuadraticSource c a b)).coeff
        (doubledExponent a b m) v) = onSingle c hu (singleQuadraticMode a b m) y
    rw [h]
    let put : SinglePolynomial →ₗ[ℂ] SplitPolynomial c ⊗[ℂ] ActualGround leechData hu :=
      ((TensorProduct.mk ℂ (SplitPolynomial c) (ActualGround leechData hu)).flip t).comp
        ((TensorProduct.mk ℂ SinglePolynomial (ComplementPolynomial c)).flip q)
    have hput (A : Module.End ℂ SinglePolynomial) : onSingle c hu A y = put (A p) := by
      simp only [onSingle, y, put, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    simp only [hput, singleQuadraticMode_interval a b m p R hP, map_add, map_sum,
      map_smul, apply_ite put, map_zero, show put p = y from rfl]

/-- Integer mode form covering every doubled exponent. -/
theorem nativeTensorSplit_quadratic_coefficient (a b : ℕ) (e : ℤ) :
    (nativeTensorSplit c hu).conj
        ((correctedField leechData hu (frameQuadraticSource c a b)).coeff e) =
      if e % 2 = 0 then onSingle c hu (singleQuadraticMode a b (-e/2 - a - 1 - (b+1)))
      else 0 := by
  split_ifs with he
  · have hm : doubledExponent a b (-e/2 - (a : ℤ) - 1 - ((b : ℤ)+1)) = e := by
      unfold doubledExponent
      omega
    simpa only [hm] using nativeTensorSplit_quadratic_mode c hu a b
      (-e/2 - (a : ℤ) - 1 - ((b : ℤ)+1))
  · rw [quadratic_coefficient_odd hu _ _ a b e (by omega), map_zero]

end D5.S3.VertexAlgebra.ActualLeechHalfFockQuadraticTransport
