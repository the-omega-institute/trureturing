/- GID: D5/S3/VertexAlgebra/HalfFock/ActualCorrCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualCorrCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original finite correction covariance and exact coefficient grading. -/

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentCorrection
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Dual.Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable section
namespace D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection MvPolynomial
open scoped BigOperators

private abbrev P (D : LatticeData) := CorrectionPolynomial D
private def u (D : LatticeData) : P D := X none
private def c (r s : ℕ) : ℂ :=
  (-1 : ℂ) ^ (r + 1) * ((r + 1).choose (s + 1) : ℂ)
private def a (D : LatticeData) (i : Index D) (s : ℕ) : P D :=
  C (c i.2 s) * u D ^ (i.2 - s)
private def normalImage (D : LatticeData) (i : Index D) : P D :=
  ∑ s ∈ Finset.range (i.2 + 1), a D i s * X (some (i.1,s))
private def chargeImage (D : LatticeData) (q : Charge D) (i : Index D) : P D :=
  C ((-1 : ℂ) ^ (i.2 + 1) * (bilinear D (unitCharge D i.1) q : ℂ)) *
    u D ^ (i.2 + 1)

/-- Weighted triangular reflection of normal jets; the finite shift variable is fixed. -/
def normalReflection (D : LatticeData) : P D →ₐ[ℂ] P D :=
  aeval (fun x => x.elim (u D) (normalImage D))

private def reflectedDerivation (D : LatticeData) (i : Index D) :
    Derivation ℂ (P D) (P D) :=
  ∑ s ∈ Finset.range (i.2 + 1), a D i s • pairDerivation D (i.1,s)

private theorem derivation_sum_apply (D : LatticeData) (s : Finset ℕ)
    (f : ℕ → Derivation ℂ (P D) (P D)) (p : P D) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Derivation.zero_apply]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

private theorem derivation_a (D : LatticeData) (i j : Index D) (s : ℕ) :
    pairDerivation D i (a D j s) = 0 := by
  simp only [a, u, Derivation.leibniz, MvPolynomial.derivation_C,
    pairDerivation_shift, smul_eq_mul, mul_zero, zero_add, add_zero]

/-- Reuse the existing singleton transform; do not reprove its binomial induction. -/
private theorem singleton_scalar (r : ℕ) :
    halfBinomial (r + 1) =
      (∑ s ∈ Finset.range (r + 1), c r s * halfBinomial (s + 1)) +
        (-1 : ℂ) ^ (r + 1) := by
  have h := LatticeHalfFockFiniteCorrection.half_binomial_transform (r + 1)
  rw [Finset.sum_range_succ'] at h
  have hzero : halfBinomial 0 = 1 := by simp [halfBinomial]
  simp only [Nat.choose_zero_right, Nat.cast_one, hzero, mul_one] at h
  have square : (-1 : ℂ) ^ (r + 1) * (-1 : ℂ) ^ (r + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    halfBinomial (r + 1) =
        (-1 : ℂ) ^ (r + 1) *
          ((-1 : ℂ) ^ (r + 1) * halfBinomial (r + 1)) := by
            rw [← mul_assoc, square, one_mul]
    _ = (-1 : ℂ) ^ (r + 1) *
        ((∑ s ∈ Finset.range (r + 1),
            ((r + 1).choose (s + 1) : ℂ) * halfBinomial (s + 1)) + 1) := by
          rw [h]
    _ = _ := by simp only [mul_add, Finset.mul_sum, c]; ring

/-- The pair covariance is EXACTLY the already proved pairScalar_reflection,
with the finite shift powers restored. No new pair-binomial calculation. -/
private theorem pair_covariance (D : LatticeData) (i j : Index D) :
    reflectedDerivation D i (normalImage D j) = pairPolynomial D i j := by
  classical
  have term (s t : ℕ) (hs : s ∈ Finset.range (i.2 + 1))
      (ht : t ∈ Finset.range (j.2 + 1)) :
      a D i s * (a D j t * pairPolynomial D (i.1,s) (j.1,t)) =
        C (c i.2 s * c j.2 t * pairScalar (s + 1) (t + 1) *
          (D.G i.1 j.1 : ℂ)) * u D ^ (i.2 + 1 + (j.2 + 1)) := by
    have hs' : s ≤ i.2 := by have := Finset.mem_range.mp hs; omega
    have ht' : t ≤ j.2 := by have := Finset.mem_range.mp ht; omega
    simp only [a, pairPolynomial, sourceWeight]
    calc
      _ = C (c i.2 s * c j.2 t * pairScalar (s + 1) (t + 1) *
          (D.G i.1 j.1 : ℂ)) *
          u D ^ ((i.2 - s) + (j.2 - t) + (s + 1 + (t + 1))) := by
            simp only [c, u, pow_add, map_mul]
            ring
      _ = _ := by
        rw [show (i.2 - s) + (j.2 - t) + (s + 1 + (t + 1)) =
          i.2 + 1 + (j.2 + 1) by omega]
  calc
    _ = ∑ s ∈ Finset.range (i.2 + 1), ∑ t ∈ Finset.range (j.2 + 1),
        a D i s * (a D j t * pairPolynomial D (i.1,s) (j.1,t)) := by
      simp only [reflectedDerivation, normalImage, derivation_sum_apply,
        Derivation.smul_apply, map_sum, Derivation.leibniz, smul_eq_mul,
        derivation_a, mul_zero, zero_add, add_zero, pairDerivation_variable, Finset.mul_sum,
        Finset.sum_const_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = ∑ s ∈ Finset.range (i.2 + 1), ∑ t ∈ Finset.range (j.2 + 1),
        C (c i.2 s * c j.2 t * pairScalar (s + 1) (t + 1) *
          (D.G i.1 j.1 : ℂ)) * u D ^ (i.2 + 1 + (j.2 + 1)) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      exact term s t hs ht
    _ = C ((∑ s ∈ Finset.range (i.2 + 1), ∑ t ∈ Finset.range (j.2 + 1),
          c i.2 s * c j.2 t * pairScalar (s + 1) (t + 1)) *
          (D.G i.1 j.1 : ℂ)) * u D ^ (i.2 + 1 + (j.2 + 1)) := by
      simp only [Finset.sum_mul, map_sum, map_mul]
    _ = _ := by
      rw [show (∑ s ∈ Finset.range (i.2 + 1), ∑ t ∈ Finset.range (j.2 + 1),
          c i.2 s * c j.2 t * pairScalar (s + 1) (t + 1)) =
          pairScalar (i.2 + 1) (j.2 + 1) by
            simpa only [c, mul_assoc] using (pairScalar_reflection i.2 j.2).symm]
      rfl

private theorem derivation_covariance (D : LatticeData) (i : Index D) (f : P D) :
    normalReflection D (pairDerivation D i f) =
      reflectedDerivation D i (normalReflection D f) := by
  induction f using MvPolynomial.induction_on with
  | C z => simp [normalReflection, MvPolynomial.derivation_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf =>
    have hx : normalReflection D (pairDerivation D i (X x)) =
        reflectedDerivation D i (normalReflection D (X x)) := by
      cases x with
      | none => simp [normalReflection, reflectedDerivation, pairDerivation, u, mkDerivation_X]
      | some j =>
        simp only [pairDerivation_variable, normalReflection, aeval_X,
          Option.elim_some]
        rw [pair_covariance]
        simp [pairPolynomial, normalReflection, u]
    rw [Derivation.leibniz, map_add]
    simp only [smul_eq_mul, map_mul, hf, hx]
    simp only [Derivation.leibniz, smul_eq_mul]

private theorem singleton_covariance (D : LatticeData) (q : Charge D) (i : Index D) :
    normalImage D i + singletonPolynomial D q i =
      (∑ s ∈ Finset.range (i.2 + 1),
        a D i s * (X (some (i.1,s)) + singletonPolynomial D q (i.1,s))) +
          chargeImage D q i := by
  classical
  have term (s : ℕ) (hs : s ∈ Finset.range (i.2 + 1)) :
      a D i s * singletonPolynomial D q (i.1,s) =
        C (c i.2 s * halfBinomial (s + 1) *
          (bilinear D (unitCharge D i.1) q : ℂ)) * u D ^ (i.2 + 1) := by
    have h : s ≤ i.2 := by have := Finset.mem_range.mp hs; omega
    simp only [a, singletonPolynomial, sourceWeight]
    calc
      _ = C (c i.2 s * halfBinomial (s + 1) *
          (bilinear D (unitCharge D i.1) q : ℂ)) *
            u D ^ ((i.2 - s) + (s + 1)) := by
              simp only [u, pow_add, map_mul]
              ring
      _ = _ := by
        rw [show (i.2 - s) + (s + 1) = i.2 + 1 by omega]
  rw [show (∑ s ∈ Finset.range (i.2 + 1),
      a D i s * (X (some (i.1,s)) + singletonPolynomial D q (i.1,s))) =
      normalImage D i + (∑ s ∈ Finset.range (i.2 + 1),
        a D i s * singletonPolynomial D q (i.1,s)) by
          simp [normalImage, mul_add, Finset.sum_add_distrib]]
  rw [Finset.sum_congr rfl term]
  simp only [singletonPolynomial, sourceWeight, chargeImage, ← Finset.sum_mul,
    ← map_sum, ← map_mul, ← add_mul, ← map_add]
  rw [singleton_scalar]
  simp only [map_add, map_mul, u]
  ring


private def reflectedInsertion (D : LatticeData) (q : Charge D) (i : Index D) :
    Module.End ℂ (P D) :=
  (∑ s ∈ Finset.range (i.2 + 1),
    (LinearMap.mulLeft ℂ (a D i s)).comp (insertion D q (i.1,s))) +
      LinearMap.mulLeft ℂ (chargeImage D q i)

/-- The genuinely new finite insertion covariance. All coefficients, pairs and
singleton corrections are those of the ORIGINAL Corr constructor. -/
private theorem insertion_reflection (D : LatticeData) (q : Charge D) (i : Index D)
    (f : P D) :
    normalReflection D (insertion D q i f) =
      reflectedInsertion D q i (normalReflection D f) := by
  rw [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply, map_add, map_mul,
    Derivation.coeFn_coe, derivation_covariance]
  have hs : normalReflection D (X (some i) + singletonPolynomial D q i) =
      normalImage D i + singletonPolynomial D q i := by
    simp [normalReflection, singletonPolynomial, u]
  rw [hs, singleton_covariance]
  simp only [reflectedInsertion, reflectedDerivation, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    insertion, derivation_sum_apply, Derivation.smul_apply, Derivation.coeFn_coe]
  simp only [add_mul, Finset.sum_mul]
  rw [add_right_comm _ (chargeImage D q i * normalReflection D f) _,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-! Original-map assembly. No recursively defined reflected source is used below.
`Cbar` is exactly the original correctionPolynomial transported back through
optionEquivLeft. `corrLift` is its coefficientwise extension in the existing
shift variable, constructed from the original shiftCoefficients and Finsupp.lsum.
It is a linear map, NOT an algebra homomorphism. -/

private abbrev E (D : LatticeData) := optionEquivLeft ℂ (Index D)

/-- Inclusion of the original oscillator algebra, with no shift variable. -/
def embed (D : LatticeData) : Oscillator D →ₐ[ℂ] P D := rename some

/-- The ORIGINAL correctionPolynomial, in Option coordinates. -/
def Cbar (D : LatticeData) (q : Charge D) : Oscillator D →ₗ[ℂ] P D :=
  (E D).symm.toLinearMap.comp (correctionPolynomial D q)

private theorem E_embed (D : LatticeData) (p : Oscillator D) :
    E D (embed D p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [embed, E, rename_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul (embed D), map_mul (E D), hp]
    simp only [embed, rename_X, E, optionEquivLeft_X_some, Polynomial.C_mul]

private theorem E_symm_C (D : LatticeData) (p : Oscillator D) :
    (E D).symm (Polynomial.C p) = embed D p := by
  apply (E D).injective
  simp only [AlgEquiv.apply_symm_apply, E_embed]

private theorem E_Cbar (D : LatticeData) (q : Charge D) (p : Oscillator D) :
    E D (Cbar D q p) = correctionPolynomial D q p := by
  simp only [Cbar, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply]

private theorem shift_expansion (D : LatticeData) (f : P D) :
    f = ∑ s ∈ (E D f).support, u D ^ s * embed D ((E D f).coeff s) := by
  calc
    f = (E D).symm (E D f) := (AlgEquiv.symm_apply_apply (E D) f).symm
    _ = _ := by
      conv_lhs => rw [(E D f).as_sum_support_C_mul_X_pow]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [map_mul, map_pow, E_symm_C]
      simp only [E, optionEquivLeft_symm_X, u]
      exact mul_comm _ _

private theorem Cbar_monomial (D : LatticeData) (q : Charge D)
    (m : Index D →₀ ℕ) :
    Cbar D q (monomial m 1) =
      correctionWord D q (LatticeAllStateField.occurrences D m) := by
  have h := (basisMonomials (Index D) ℂ).constr_basis ℂ
    (fun m => correctionWord D q (LatticeAllStateField.occurrences D m)) m
  change ((basisMonomials (Index D) ℂ).constr ℂ
    (fun m => correctionWord D q (LatticeAllStateField.occurrences D m)))
      (monomial m 1) = _ at h
  simp only [Cbar, correctionPolynomial, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  exact h

private theorem Cbar_one (D : LatticeData) (q : Charge D) : Cbar D q 1 = 1 := by
  simpa [LatticeAllStateField.occurrences, correctionWord] using
    Cbar_monomial D q 0

private theorem Cbar_C (D : LatticeData) (q : Charge D) (z : ℂ) :
    Cbar D q (C z) = C z := by
  rw [C_eq_smul_one, map_smul, Cbar_one, ← C_eq_smul_one]

/-- The bridge from the original monomial-basis constructor to insertion.
The original occurrences enumeration retains every repetition. -/
private theorem Cbar_eq_lift (D : LatticeData) (q : Charge D) (p : Oscillator D) :
    Cbar D q p = LatticeHalfFockCurrentCorrection.correctionLift D q p := by
  simp only [Cbar, E, correctionPolynomial, LatticeHalfFockCurrentCorrection.correctionLift,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

private theorem Cbar_X_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (p : Oscillator D) :
    Cbar D q (X i * p) = insertion D q i (Cbar D q p) := by
  simpa only [Cbar_eq_lift, mul_comm (X i) p] using
    LatticeHalfFockCurrentCorrection.correctionLift_X_mul D q i p

/-- Canonical scalar extension of the ORIGINAL correction map in the original
finite shift variable. It is ℂ-linear by construction. Its ℂ[u]-linearity is
proved below from finite shift expansion, without a changed coefficient ring. -/
def corrLift (D : LatticeData) (q : Charge D) : P D →ₗ[ℂ] P D :=
  (Finsupp.lsum ℂ (fun s : ℕ =>
    (LinearMap.mulLeft ℂ (u D ^ s)).comp (Cbar D q))).comp
      ((shiftCoefficients D).comp (E D).toLinearMap)

private theorem shifts_monomial (D : LatticeData) (s : ℕ) (p : Oscillator D) :
    shiftCoefficients D (Polynomial.monomial s p) = Finsupp.single s p := by
  ext t
  simp [shiftCoefficients, Polynomial.coeff_monomial, Finsupp.single_apply,
    eq_comm]

private theorem corrLift_expansion (D : LatticeData) (q : Charge D) (f : P D) :
    corrLift D q f = ∑ s ∈ (E D f).support,
      u D ^ s * Cbar D q ((E D f).coeff s) := by
  rfl

private theorem corrLift_shift_embed (D : LatticeData) (q : Charge D)
    (s : ℕ) (p : Oscillator D) :
    corrLift D q (u D ^ s * embed D p) = u D ^ s * Cbar D q p := by
  have he : E D (u D ^ s * embed D p) = Polynomial.monomial s p := by
    simp only [map_mul, map_pow, u, E, optionEquivLeft_X_none,
      E_embed, mul_comm (Polynomial.X ^ s), Polynomial.C_mul_X_pow_eq_monomial]
  simp only [corrLift, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, he,
    shifts_monomial, Finsupp.lsum_single, LinearMap.mulLeft_apply]

private theorem corrLift_embed (D : LatticeData) (q : Charge D) (p : Oscillator D) :
    corrLift D q (embed D p) = Cbar D q p := by
  simpa using corrLift_shift_embed D q 0 p

private theorem corrLift_C (D : LatticeData) (q : Charge D) (z : ℂ) :
    corrLift D q (C z) = C z := by
  simpa only [embed, rename_C] using (corrLift_embed D q (C z)).trans (Cbar_C D q z)

private theorem corrLift_u_mul (D : LatticeData) (q : Charge D) (f : P D) :
    corrLift D q (u D * f) = u D * corrLift D q f := by
  classical
  conv_lhs => rw [shift_expansion D f]
  rw [Finset.mul_sum, map_sum, corrLift_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← mul_assoc, ← pow_succ', corrLift_shift_embed, pow_succ']
  ring

private theorem corrLift_u_pow_mul (D : LatticeData) (q : Charge D)
    (s : ℕ) (f : P D) :
    corrLift D q (u D ^ s * f) = u D ^ s * corrLift D q f := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, mul_comm (u D ^ s) (u D), mul_assoc,
      corrLift_u_mul, ih, ← mul_assoc]

private theorem corrLift_C_mul (D : LatticeData) (q : Charge D) (z : ℂ) (f : P D) :
    corrLift D q (C z * f) = C z * corrLift D q f := by
  simpa only [smul_eq_C_mul] using (corrLift D q).map_smul z f

/-- Scalar linearity over the original finite shift algebra; this is
consumed by the triangular reflection coefficients below. -/
private theorem corrLift_shiftScalar_mul (D : LatticeData) (q : Charge D)
    (h : Polynomial ℂ) (f : P D) :
    corrLift D q (Polynomial.aeval (u D) h * f) =
      Polynomial.aeval (u D) h * corrLift D q f := by
  induction h using Polynomial.induction_on' with
  | add h k hh hk => simp only [map_add, add_mul, hh, hk]
  | monomial s z =>
    rw [Polynomial.aeval_monomial, algebraMap_eq]
    rw [mul_assoc, corrLift_C_mul, corrLift_u_pow_mul, ← mul_assoc]

private theorem insertion_u_pow_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (s : ℕ) (f : P D) :
    insertion D q i (u D ^ s * f) = u D ^ s * insertion D q i f := by
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, u,
    pairDerivation_shift, mul_zero, zero_add]
  ring

private theorem corrLift_X_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (f : P D) :
    corrLift D q (X (some i) * f) = insertion D q i (corrLift D q f) := by
  classical
  conv_lhs => rw [shift_expansion D f]
  rw [Finset.mul_sum, map_sum, corrLift_expansion, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show X (some i) * (u D ^ s * embed D ((E D f).coeff s)) =
      u D ^ s * embed D (X i * (E D f).coeff s) by
        simp only [map_mul, embed, rename_X]
        ring, corrLift_shift_embed, Cbar_X_mul, insertion_u_pow_mul]

/-- The affine source transformation on P, fixing the original shift variable. -/
def affineReflection (D : LatticeData) (q : Charge D) : P D →ₐ[ℂ] P D :=
  aeval (fun x => x.elim (u D) (fun i => normalImage D i + chargeImage D q i))

def affineSource (D : LatticeData) (q : Charge D) :
    Oscillator D →ₐ[ℂ] P D := (affineReflection D q).comp (embed D)

private theorem normalReflection_u (D : LatticeData) : normalReflection D (u D) = u D := by
  simp [normalReflection, u]

private theorem affineReflection_u (D : LatticeData) (q : Charge D) :
    affineReflection D q (u D) = u D := by
  simp [affineReflection, u]

private theorem affineReflection_X (D : LatticeData) (q : Charge D) (i : Index D) :
    affineReflection D q (X (some i)) = normalImage D i + chargeImage D q i := by
  simp [affineReflection]

private theorem corrLift_a_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (s : ℕ) (f : P D) :
    corrLift D q (a D i s * f) = a D i s * corrLift D q f := by
  simpa only [Polynomial.aeval_monomial, algebraMap_eq, a] using
    corrLift_shiftScalar_mul D q (Polynomial.monomial (i.2 - s) (c i.2 s)) f

private theorem corrLift_charge_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (f : P D) :
    corrLift D q (chargeImage D q i * f) = chargeImage D q i * corrLift D q f := by
  rw [chargeImage, mul_assoc, corrLift_C_mul, corrLift_u_pow_mul, ← mul_assoc]

/-- This identifies the former recursive reflected insertion with the
canonical coefficientwise lift of the ORIGINAL source operation. -/
private theorem corrLift_affine_mul (D : LatticeData) (q : Charge D)
    (i : Index D) (f : P D) :
    corrLift D q ((normalImage D i + chargeImage D q i) * f) =
      reflectedInsertion D q i (corrLift D q f) := by
  rw [add_mul, map_add, corrLift_charge_mul]
  simp only [normalImage, Finset.sum_mul, map_sum, mul_assoc,
    corrLift_a_mul, corrLift_X_mul, reflectedInsertion,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply]

/-- Full polynomial covariance of the canonical scalar extension, including
constants, the empty word and arbitrary repetitions. -/
private theorem corrLift_reflection (D : LatticeData) (q : Charge D) (f : P D) :
    normalReflection D (corrLift D q f) = corrLift D q (affineReflection D q f) := by
  induction f using MvPolynomial.induction_on with
  | C z => simp [corrLift_C, normalReflection, affineReflection]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf =>
    cases x with
    | none =>
      change normalReflection D (corrLift D q (f * u D)) =
        corrLift D q (affineReflection D q (f * u D))
      rw [mul_comm f (u D), corrLift_u_mul, map_mul, normalReflection_u,
        hf, map_mul, affineReflection_u]
      exact (corrLift_u_mul D q _).symm
    | some i =>
      calc
        _ = normalReflection D (insertion D q i (corrLift D q f)) := by
          rw [mul_comm f (X (some i)), corrLift_X_mul]
        _ = reflectedInsertion D q i (normalReflection D (corrLift D q f)) :=
          insertion_reflection D q i _
        _ = reflectedInsertion D q i (corrLift D q (affineReflection D q f)) := by rw [hf]
        _ = corrLift D q ((normalImage D i + chargeImage D q i) *
            affineReflection D q f) := (corrLift_affine_mul D q i _).symm
        _ = corrLift D q (affineReflection D q (f * X (some i))) := by
          rw [map_mul (affineReflection D q), affineReflection_X,
            mul_comm (affineReflection D q f) (normalImage D i + chargeImage D q i)]

/-- The requested identity on the ORIGINAL correctionPolynomial, transported
through the canonical Option/Polynomial equivalence. No new corrected field. -/
theorem correctionPolynomial_reflection (D : LatticeData) (q : Charge D)
    (p : Oscillator D) :
    normalReflection D (Cbar D q p) = corrLift D q (affineSource D q p) := by
  simpa only [corrLift_embed, affineSource, AlgHom.comp_apply] using
    corrLift_reflection D q (embed D p)

private theorem Corr_coeff (D : LatticeData) (q : Charge D)
    (p : Oscillator D) (s : ℕ) :
    Corr D q p s = (correctionPolynomial D q p).coeff s := by rfl

private theorem Cbar_expansion (D : LatticeData) (q : Charge D) (p : Oscillator D) :
    Cbar D q p = ∑ s ∈ (Corr D q p).support,
      u D ^ s * embed D (Corr D q p s) := by
  change Cbar D q p = ∑ s ∈ (correctionPolynomial D q p).support,
    u D ^ s * embed D ((correctionPolynomial D q p).coeff s)
  simpa only [E_Cbar] using shift_expansion D (Cbar D q p)

private theorem corrLift_E_expansion (D : LatticeData) (q : Charge D) (f : P D) :
    E D (corrLift D q f) = ∑ s ∈ (E D f).support,
      Polynomial.X ^ s * correctionPolynomial D q ((E D f).coeff s) := by
  rw [corrLift_expansion, map_sum]
  simp only [map_mul, map_pow, u, E, optionEquivLeft_X_none, E_Cbar]

private theorem reflected_Cbar_E_expansion (D : LatticeData) (q : Charge D)
    (p : Oscillator D) :
    E D (normalReflection D (Cbar D q p)) = ∑ s ∈ (Corr D q p).support,
      Polynomial.X ^ s * E D (normalReflection D (embed D (Corr D q p s))) := by
  rw [Cbar_expansion, map_sum, map_sum]
  simp only [map_mul, map_pow, normalReflection_u]
  simp only [u, E, optionEquivLeft_X_none]

/-! Exact grading. This extends, rather than substitutes for, the original
sourceWeight. There is a single additional coordinate, of weight one. -/
def optionWeight (D : LatticeData) : Option (Index D) → ℕ :=
  fun x => x.elim 1 (sourceWeight D)

private theorem weight_option (D : LatticeData) (n : Option (Index D) →₀ ℕ) :
    Finsupp.weight (optionWeight D) n =
      n none + Finsupp.weight (sourceWeight D) n.some := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul]
  simp only [optionWeight, Option.elim_none, Option.elim_some, smul_eq_mul,
    mul_one, Finsupp.weight_apply]

private theorem weight_optionElim (D : LatticeData) (m : Index D →₀ ℕ) (s : ℕ) :
    Finsupp.weight (optionWeight D) (m.optionElim s) =
      s + Finsupp.weight (sourceWeight D) m := by
  rw [weight_option, Finsupp.optionElim_apply_none, Finsupp.some_optionElim]

private theorem u_pow_homogeneous (D : LatticeData) (s : ℕ) :
    IsWeightedHomogeneous (optionWeight D) (u D ^ s) s := by
  simpa only [u, optionWeight, Option.elim_none, nsmul_eq_mul, mul_one, Nat.cast_id] using
    (isWeightedHomogeneous_X ℂ (optionWeight D) none).pow s

private theorem singleton_homogeneous (D : LatticeData) (q : Charge D) (i : Index D) :
    IsWeightedHomogeneous (optionWeight D) (singletonPolynomial D q i) (sourceWeight D i) :=
  (u_pow_homogeneous D (sourceWeight D i)).C_mul _

private theorem pair_homogeneous (D : LatticeData) (i j : Index D) :
    IsWeightedHomogeneous (optionWeight D) (pairPolynomial D i j)
      (sourceWeight D i + sourceWeight D j) :=
  (u_pow_homogeneous D (sourceWeight D i + sourceWeight D j)).C_mul _

private theorem list_homogeneous (D : LatticeData) (fs : List (P D)) (R : ℕ)
    (hf : ∀ f ∈ fs, IsWeightedHomogeneous (optionWeight D) f R) :
    IsWeightedHomogeneous (optionWeight D) fs.sum R := by
  induction fs with
  | nil => exact isWeightedHomogeneous_zero ℂ (optionWeight D) R
  | cons f fs ih =>
    exact (hf f (by simp)).add (ih (by
      intro g hg
      exact hf g (by simp [hg])))

/-- Exact weight conservation for the original matching recurrence.
Both the singleton and pair branches consume the original source definitions. -/
private theorem correctionWord_homogeneous (D : LatticeData) (q : Charge D)
    (w : List (Index D)) :
    IsWeightedHomogeneous (optionWeight D) (correctionWord D q w) (wordWeight D w) := by
  have h : ∀ n : ℕ, ∀ w : List (Index D), w.length = n →
      IsWeightedHomogeneous (optionWeight D) (correctionWord D q w) (wordWeight D w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      cases w with
      | nil => simpa [correctionWord, wordWeight] using
          isWeightedHomogeneous_one ℂ (optionWeight D)
      | cons i tail =>
        rw [correctionWord_matching]
        apply IsWeightedHomogeneous.add
        · have ht := ih tail.length (by simp only [List.length_cons] at hw; omega) tail rfl
          have hi : IsWeightedHomogeneous (optionWeight D)
              (X (some i) + singletonPolynomial D q i) (sourceWeight D i) :=
            (isWeightedHomogeneous_X ℂ (optionWeight D) (some i)).add
              (singleton_homogeneous D q i)
          simpa only [wordWeight, List.map_cons, List.sum_cons] using hi.mul ht
        · apply list_homogeneous
          intro f hf
          obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hf
          obtain ⟨hs, hwgt⟩ := labelledRemainders_size D tail entry he
          have ht := ih entry.2.length (by
            simp only [List.length_cons] at hw
            omega) entry.2 rfl
          have combined := (pair_homogeneous D i entry.1).mul ht
          have heq : sourceWeight D i + sourceWeight D entry.1 + wordWeight D entry.2 =
              wordWeight D (i :: tail) := by
            simp only [wordWeight, List.map_cons, List.sum_cons] at *
            omega
          rwa [heq] at combined
  exact h w.length w rfl

private theorem Cbar_monomial_scalar (D : LatticeData) (q : Charge D)
    (m : Index D →₀ ℕ) (z : ℂ) :
    Cbar D q (monomial m z) = z •
      correctionWord D q (LatticeAllStateField.occurrences D m) := by
  rw [show monomial m z = z • monomial m (1 : ℂ) by
    simp only [smul_monomial, smul_eq_mul, mul_one], map_smul, Cbar_monomial]

/-- Exact homogeneity for every homogeneous original oscillator polynomial,
not just a bound on its largest shift. -/
private theorem correctionPolynomial_homogeneous (D : LatticeData) (q : Charge D)
    (p : Oscillator D) (R : ℕ) (hp : IsWeightedHomogeneous (sourceWeight D) p R) :
    IsWeightedHomogeneous (optionWeight D) (Cbar D q p) R := by
  classical
  rw [p.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [Cbar_monomial_scalar]
  apply (weightedHomogeneousSubmodule ℂ (optionWeight D) R).smul_mem
  have h := correctionWord_homogeneous D q (LatticeAllStateField.occurrences D m)
  rw [wordWeight_occurrences, hp (MvPolynomial.mem_support_iff.mp hm)] at h
  exact h

/-- Exact bigrading across optionEquivLeft. No nonzero polynomial or finite
rank hypothesis is needed; only the particular coefficient is nonzero. -/
private theorem option_coefficient_bidegree (D : LatticeData) (f : P D) (R : ℕ)
    (hf : IsWeightedHomogeneous (optionWeight D) f R)
    (s : ℕ) (m : Index D →₀ ℕ) (nonzero : ((E D f).coeff s).coeff m ≠ 0) :
    s + Finsupp.weight (sourceWeight D) m = R := by
  have hn : f.coeff (m.optionElim s) ≠ 0 := by
    simpa only [E, optionEquivLeft_coeff_coeff] using nonzero
  have h := hf hn
  rwa [weight_optionElim] at h

/-- The actual ORIGINAL Corr coefficient has exactly the complementary
oscillator weight. This is stronger than Corr_shift_bound. -/
theorem Corr_coefficient_bidegree (D : LatticeData) (q : Charge D)
    (p : Oscillator D) (R : ℕ) (hp : IsWeightedHomogeneous (sourceWeight D) p R)
    (s : ℕ) (m : Index D →₀ ℕ) (nonzero : (Corr D q p s).coeff m ≠ 0) :
    s + Finsupp.weight (sourceWeight D) m = R := by
  apply option_coefficient_bidegree D (Cbar D q p) R
    (correctionPolynomial_homogeneous D q p R hp) s m
  simpa only [E_Cbar, ← Corr_coeff] using nonzero

/-! Finite scalar contraction for the actual downstream normal-coefficient
consumer. ℓ k is any ℂ-linear oscillator readout, e.g. the actual bilinear
normal-field coefficient at -e-2N-4R+2k. There is NO transpose/covariance
hypothesis on ℓ, and no replacement correctedField is defined. -/
def scalarReadout (D : LatticeData)
    (ℓ : ℕ → Module.Dual ℂ (Oscillator D)) : Polynomial (Oscillator D) →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ ℓ).comp (shiftCoefficients D)

theorem scalarReadout_monomial (D : LatticeData)
    (ℓ : ℕ → Module.Dual ℂ (Oscillator D)) (s : ℕ) (p : Oscillator D) :
    scalarReadout D ℓ (Polynomial.C p * Polynomial.X ^ s) = ℓ s p := by
  simp only [Polynomial.C_mul_X_pow_eq_monomial, scalarReadout,
    LinearMap.comp_apply, shifts_monomial, Finsupp.lsum_single]

private theorem scalarReadout_shift (D : LatticeData)
    (ℓ : ℕ → Module.Dual ℂ (Oscillator D)) (s : ℕ) (f : Polynomial (Oscillator D)) :
    scalarReadout D ℓ (Polynomial.X ^ s * f) =
      ∑ t ∈ f.support, ℓ (s + t) (f.coeff t) := by
  classical
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [show Polynomial.X ^ s * (Polynomial.C (f.coeff t) * Polynomial.X ^ t) =
      Polynomial.C (f.coeff t) * Polynomial.X ^ (s + t) by
        rw [pow_add]
        ring, scalarReadout_monomial]

private theorem Corr_support (D : LatticeData) (q : Charge D) (p : Oscillator D) :
    (Corr D q p).support = (correctionPolynomial D q p).support := by rfl

/-- The original-Corr all-source finite scalar law, ready for the normal-field
coefficient readout. The original shift s and reflected loss t have genuinely
been reorganized, with k=s+t on the left and k=t+s on the right. -/
theorem Corr_reflection_readout (D : LatticeData) (q : Charge D) (p : Oscillator D)
    (ℓ : ℕ → Module.Dual ℂ (Oscillator D)) :
    (∑ s ∈ (Corr D q p).support,
      ∑ t ∈ (E D (normalReflection D (embed D (Corr D q p s)))).support,
        ℓ (s + t)
          ((E D (normalReflection D (embed D (Corr D q p s)))).coeff t)) =
    ∑ t ∈ (E D (affineSource D q p)).support,
      ∑ s ∈ (Corr D q ((E D (affineSource D q p)).coeff t)).support,
        ℓ (t + s) (Corr D q ((E D (affineSource D q p)).coeff t) s) := by
  have h := congrArg (fun f : P D => scalarReadout D ℓ (E D f))
    (correctionPolynomial_reflection D q p)
  rw [reflected_Cbar_E_expansion, corrLift_E_expansion] at h
  simpa only [map_sum, scalarReadout_shift, ← Corr_support, ← Corr_coeff] using h

end D5.S3.VertexAlgebra.HalfFock.ActualCorrCovariance
