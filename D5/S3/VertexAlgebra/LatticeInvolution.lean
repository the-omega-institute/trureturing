/- GID: D5/S3/VertexAlgebra/LatticeInvolution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeInvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual lattice reflection, all-state mode covariance, fixed vertex algebra and sign selection. -/

import D5.S3.VertexAlgebra.LatticeActualVertexAlgebra
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization

/-!
# Reflection on the actual ordinary-lattice vertex algebra

Every finite rank, including zero, and every symmetric integral Gram matrix with
an even diagonal is allowed. Degenerate and indefinite forms are included.
The lift negates charge and EVERY oscillator. Its phase is one for the realized
lower-triangular section; the accepted GroundRealization half-norm theorem supplies
that section's square. No automorphism or field compatibility premise is added.

The proofs transport charged coefficients, each neutral branch, divided derivatives,
ordered normal products, then the monomial basis and finite charge sums. The fixed
subtype retains the actual fields, their truncation, and the full integer Borcherds
identity with all three finite supports. The final sign law concerns actual modes.

Bakalov--Kac, math/0402315v1 (2004-02-19), section 4.1, pp. 8--10,
(4.18)--(4.20), Proposition 4.1 and Remark 4.1. Dong--Nagatomo,
math/9808088v1 (1998-08-19), pp. 4--5 and 9, for the inverse-section phase.
The inherited finite residue kernels and normal products retain Scott Carnahan,
vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0 attribution;
Matsuo--Nagatomo, hep-th/9706118v1, Proposition 1.5.5 p. 11 and Theorem 5.4.1
p. 35; and mathlib db584cd6d46c92f209a44c0f1c829460d327499d attribution.
These are actual local adaptations and dependencies, not claims of verbatim copying.

This is an ungraded fixed vertex algebra. There is no positive-form, finite-grading,
PCT, Leech, twisted-field, categorical fusion, Monster or physics-completion claim.
Square identity is proved; exact order two is not asserted at rank zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeInvolution
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal LatticeActualVertexAlgebra
open FieldNormalProduct FieldNormalProductLocality MvPolynomial
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-! ## Charge reflection and oscillator negation -/

def sigma (D : LatticeData) : Oscillator D →+* Oscillator D :=
  eval₂Hom C (fun x => -(X x : Oscillator D))

theorem bilinear_neg_neg (D : LatticeData) (a b : Charge D) :
    bilinear D (-a) (-b) = bilinear D a b := by simp [bilinear]

theorem bilinear_neg_left (D : LatticeData) (a b : Charge D) :
    bilinear D (-a) b = -bilinear D a b := by
  simp [bilinear, Finset.sum_neg_distrib]

theorem bilinear_neg_right (D : LatticeData) (a b : Charge D) :
    bilinear D a (-b) = -bilinear D a b := by
  simp [bilinear, Finset.sum_neg_distrib]

theorem lowerCocycleExponent_neg_neg (D : LatticeData) (a b : Charge D) :
    lowerCocycleExponent D (-a) (-b) = lowerCocycleExponent D a b := by
  simp [lowerCocycleExponent]

theorem epsilon_neg_neg (D : LatticeData) (a b : Charge D) :
    epsilon D (-a) (-b) = epsilon D a b := by
  rw [epsilon, lowerCocycleExponent_neg_neg]; rfl

@[simp] theorem sigma_C (D : LatticeData) (c : ℂ) : sigma D (C c) = C c := by
  simp [sigma]
@[simp] theorem sigma_X (D : LatticeData) (x : Index D) : sigma D (X x) = -X x := by
  simp [sigma]
@[simp] theorem sigma_smul (D : LatticeData) (c : ℂ) (p : Oscillator D) :
    sigma D (c • p) = c • sigma D p := by
  rw [← C_mul', map_mul, sigma_C, C_mul']

theorem sigma_involutive (D : LatticeData) : Function.Involutive (sigma D) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p x hp => simp [map_mul, hp]

def sigmaLinear (D : LatticeData) : Oscillator D →ₗ[ℂ] Oscillator D where
  toFun := sigma D
  map_add' := map_add (sigma D)
  map_smul' := sigma_smul D

def thetaLinear (D : LatticeData) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a => (Finsupp.lsingle (-a)).comp (sigmaLinear D))

@[simp] theorem theta_single (D : LatticeData) (a : Charge D) (p : Oscillator D) :
    thetaLinear D (Finsupp.single a p) = Finsupp.single (-a) (sigma D p) := by
  simp [thetaLinear, sigmaLinear]

theorem theta_involutive (D : LatticeData) : Function.Involutive (thetaLinear D) := by
  have h : (thetaLinear D).comp (thetaLinear D) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro a p
    simp [LinearMap.comp_apply, sigma_involutive D p]
  intro v
  exact LinearMap.congr_fun h v

def theta (D : LatticeData) : Carrier D ≃ₗ[ℂ] Carrier D :=
  LinearEquiv.ofInvolutive (thetaLinear D) (theta_involutive D)

theorem theta_eval (D : LatticeData) (v : Carrier D) (a : Charge D) :
    theta D v (-a) = sigma D (v a) := by
  have h : (Finsupp.lapply (-a)).comp (thetaLinear D) =
      (sigmaLinear D).comp (Finsupp.lapply a) := by
    apply Finsupp.lhom_ext
    intro b p
    simp only [LinearMap.comp_apply, theta_single, Finsupp.lapply_apply,
      sigmaLinear]
    by_cases hb : b = a
    · subst b; simp
    · have hn : -b ≠ -a := neg_injective.ne hb
      simp [Finsupp.single_apply, hb, hn, Ne.symm hb, Ne.symm hn]
  exact LinearMap.congr_fun h v

theorem theta_support (D : LatticeData) (v : Carrier D) :
    (theta D v).support = v.support.image (fun a => -a) := by
  classical
  ext a
  rw [Finsupp.mem_support_iff, Finset.mem_image]
  have he := theta_eval D v (-a)
  simp only [neg_neg] at he
  rw [he, (sigma_involutive D).injective.ne_iff' (map_zero (sigma D))]
  constructor
  · intro h; exact ⟨-a, Finsupp.mem_support_iff.mpr h, neg_neg a⟩
  · rintro ⟨b, hb, he⟩; subst a; simpa using Finsupp.mem_support_iff.mp hb

@[simp] theorem theta_vacuum (D : LatticeData) : theta D (vacuum D) = vacuum D := by
  simp [theta, vacuum]


/-! ## Charged creation and translation coefficients -/

theorem sigma_creationSeries (D : LatticeData) (a : Charge D) :
    PowerSeries.map (sigma D) (creationSeries D a) = creationSeries D (-a) := by
  ext q
  simp only [PowerSeries.coeff_map, creationSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_sum, sigma_smul, smul_neg, neg_smul]

theorem sigma_creationExponential (D : LatticeData) (a : Charge D) :
    PowerSeries.map (sigma D) (creationExponential D a) =
      creationExponential D (-a) := by
  have h : PowerSeries.HasSubst (creationSeries D a) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])
  have hm := PowerSeries.map_subst (h := sigma D) h (PowerSeries.exp (Oscillator D))
  change PowerSeries.map (sigma D) (creationExponential D a) =
    (PowerSeries.map (sigma D) (PowerSeries.exp (Oscillator D))).subst
      (PowerSeries.map (sigma D) (creationSeries D a)) at hm
  rw [hm, PowerSeries.map_exp, sigma_creationSeries]
  rfl

theorem sigma_creationCoeff (D : LatticeData) (a : Charge D) (t : ℤ) :
    sigma D (creationCoeff D a t) = creationCoeff D (-a) t := by
  unfold creationCoeff
  split_ifs
  · exact map_zero _
  · rw [← PowerSeries.coeff_map, sigma_creationExponential]

theorem sigma_translationVariable (D : LatticeData) (a : Charge D) (x : Index D) :
    Polynomial.map (sigma D) (translationVariable D a x.1 x.2) =
      -translationVariable D (-a) x.1 x.2 := by
  simp [translationVariable, bilinear_neg_left, neg_smul,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow] <;> ring

theorem translatedPolynomial_sigma (D : LatticeData) (a : Charge D)
    (p : Oscillator D) :
    Polynomial.map (sigma D) (translatedPolynomial D a p) =
      translatedPolynomial D (-a) (sigma D p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [translatedPolynomial]
  | add p q hp hq =>
    simp only [translatedPolynomial, map_add, Polynomial.map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p x hp =>
    simp only [translatedPolynomial, map_mul, Polynomial.map_mul, sigma_X,
      map_neg, eval₂Hom_X'] at hp ⊢
    rw [hp, sigma_translationVariable] <;> ring

theorem translatedPolynomial_sigma_coeff (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (d : ℕ) :
    (translatedPolynomial D (-a) (sigma D p)).coeff d =
      sigma D ((translatedPolynomial D a p).coeff d) := by
  rw [← translatedPolynomial_sigma, Polynomial.coeff_map]

theorem translatedPolynomial_sigma_support (D : LatticeData) (a : Charge D)
    (p : Oscillator D) :
    (translatedPolynomial D (-a) (sigma D p)).support =
      (translatedPolynomial D a p).support := by
  classical
  ext d
  simp only [Polynomial.mem_support_iff, translatedPolynomial_sigma_coeff]
  exact (sigma_involutive D).injective.ne_iff' (map_zero (sigma D))

theorem theta_rawSingle (D : LatticeData) (a : Charge D) (k : ℤ)
    (d : Charge D) (p : Oscillator D) :
    theta D (rawSingle D a k d p) = rawSingle D (-a) k (-d) (sigma D p) := by
  classical
  change thetaLinear D (rawSingle D a k d p) = _
  simp only [rawSingle, map_smul, theta_single, map_sum,
    sigma_smul, sigma_creationCoeff, epsilon_neg_neg, bilinear_neg_neg,
    translatedPolynomial_sigma_support, translatedPolynomial_sigma_coeff, neg_add]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_eq_mul, smul_eq_mul, map_mul, sigma_creationCoeff]

theorem theta_rawCoeff (D : LatticeData) (a : Charge D) (k : ℤ)
    (v : Carrier D) :
    theta D (rawCoeff D a k v) = rawCoeff D (-a) k (theta D v) := by
  have h : (thetaLinear D).comp (rawCoeff D a k) =
      (rawCoeff D (-a) k).comp (thetaLinear D) := by
    apply Finsupp.lhom_ext
    intro d p
    simp only [LinearMap.comp_apply, theta_single]
    rw [(actual_creation_coefficient_transport D a a).2.2.1,
      (actual_creation_coefficient_transport D (-a) (-a)).2.2.1]
    exact theta_rawSingle D a k d p
  exact LinearMap.congr_fun h v

/-- Charge is negated; the normalized integer mode is unchanged. -/
theorem theta_actualField_ncoeff (D : LatticeData) (a : Charge D) (n : ℤ)
    (v : Carrier D) :
    theta D (((actualField D a)[[n]]) v) =
      ((actualField D (-a))[[n]]) (theta D v) := by
  simp only [actualField, VertexOperator.ncoeff_of_coeff]
  exact theta_rawCoeff D a (-n-1) v


/-! ## Neutral modes and divided derivatives -/

theorem sigma_pderiv (D : LatticeData) (x : Index D) (p : Oscillator D) :
    sigma D (pderiv x p) = -pderiv x (sigma D p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq, neg_add, add_comm]
  | mul_X p y hp =>
    simp only [pderiv_mul, map_add, map_mul, sigma_X, hp, map_neg]
    by_cases h : y = x
    · subst y; simp [pderiv_X_self, pderiv_mul] <;> ring
    · simp [pderiv_X_of_ne h, pderiv_mul] <;> ring

theorem sigma_neutralPolynomialMode (D : LatticeData) (i : Fin D.rank)
    (d : Charge D) (m : ℤ) (p : Oscillator D) :
    sigma D (neutralPolynomialMode D i d m p) =
      -neutralPolynomialMode D i (-d) m (sigma D p) := by
  classical
  unfold neutralPolynomialMode
  split_ifs with hn hz
  · simp [LinearMap.mulLeft_apply, map_mul]
  · simp [bilinear_neg_right, neg_smul]
  · simp only [LinearMap.smul_apply, sigma_smul, LinearMap.sum_apply,
      map_sum]
    change (m : ℂ) • (∑ j : Fin D.rank, (D.G i j : ℂ) •
      sigma D (pderiv (j, (m-1).toNat) p)) =
      -((m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) •
        pderiv (j, (m-1).toNat) (sigma D p))
    simp_rw [sigma_pderiv]
    simp [Finset.sum_neg_distrib, smul_neg]

theorem theta_neutralMode (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (v : Carrier D) :
    theta D (neutralMode D i m v) = -neutralMode D i m (theta D v) := by
  have h : (thetaLinear D).comp (neutralMode D i m) =
      -((neutralMode D i m).comp (thetaLinear D)) := by
    apply Finsupp.lhom_ext
    intro d p
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, neutralMode,
      Finsupp.lsum_single, Finsupp.lsingle_apply, theta_single]
    rw [sigma_neutralPolynomialMode, Finsupp.single_neg]
  exact LinearMap.congr_fun h v

theorem theta_neutralField_ncoeff (D : LatticeData) (i : Fin D.rank) (m : ℤ)
    (v : Carrier D) :
    theta D (((neutralField D i)[[m]]) v) =
      -((neutralField D i)[[m]]) (theta D v) := by
  simp only [neutralField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-m-1)-1 = m by omega]
  exact theta_neutralMode D i m v

/-- Every divided derivative has sign minus, independently of its order. -/
theorem theta_dividedDerivative (D : LatticeData) (x : Index D) (m : ℤ)
    (v : Carrier D) :
    theta D (((dividedDerivative x.2 (neutralField D x.1))[[m]]) v) =
      -((dividedDerivative x.2 (neutralField D x.1))[[m]]) (theta D v) := by
  change theta D (Ring.choose (-m-1+x.2) x.2 •
    HVertexOperator.coeff (neutralField D x.1) (-m-1+x.2) v) =
    -(Ring.choose (-m-1+x.2) x.2 •
    HVertexOperator.coeff (neutralField D x.1) (-m-1+x.2) (theta D v))
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff,
    theta_neutralField_ncoeff, smul_neg]


/-! ## Ordered words and all-state covariance -/

/-- Finiteness uses the second field at the indicated actual vector. -/
theorem normal_forward_finite (D : LatticeData)
    (A B : VertexOperator ℂ (Carrier D)) (m : ℤ) (v : Carrier D) :
    Function.HasFiniteSupport (fun j : ℕ =>
      ((A[[-(j : ℤ)-1]])) (((B[[m+j]])) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (B v)).order-m).toNat, ?_⟩
  intro j hj
  contrapose! hj
  have hz : ((B[[m+j]])) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

theorem normal_reverse_finite (D : LatticeData)
    (A B : VertexOperator ℂ (Carrier D)) (m : ℤ) (v : Carrier D) :
    Function.HasFiniteSupport (fun j : ℕ =>
      ((B[[m-j-1]])) (((A[[j]])) v)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (A v)).order-1).toNat, ?_⟩
  intro j hj
  contrapose! hj
  have hz : ((A[[j]])) v = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

/-- Conjugation preserves the order of both products in the normal coefficient. -/
theorem normalMinusOne_theta (D : LatticeData)
    (A B A' B' : VertexOperator ℂ (Carrier D)) (s t : ℂ)
    (hA : ∀ n v, theta D (((A[[n]])) v) = s • ((A'[[n]])) (theta D v))
    (hB : ∀ n v, theta D (((B[[n]])) v) = t • ((B'[[n]])) (theta D v))
    (n : ℤ) (v : Carrier D) :
    theta D ((((normalMinusOne A B).1[[n]])) v) =
      (s*t) • (((normalMinusOne A' B').1[[n]])) (theta D v) := by
  rw [(normalMinusOne A B).2, (normalMinusOne A' B').2, map_add]
  have hmap (f : ℕ → Carrier D) (hf : Function.HasFiniteSupport f) :
      theta D (∑ᶠ i, f i) = ∑ᶠ i, theta D (f i) :=
    (thetaLinear D).toAddMonoidHom.map_finsum hf
  rw [hmap _ (normal_forward_finite D A B n v),
    hmap _ (normal_reverse_finite D A B n v)]
  simp only [hA, hB, map_smul, smul_smul]
  rw [← smul_finsum, ← smul_finsum, mul_comm t s, smul_add]

theorem wordField_theta (D : LatticeData) (d : Charge D) (w : List (Index D))
    (n : ℤ) (v : Carrier D) :
    theta D (((wordField D d w)[[n]]) v) =
      ((-1 : ℂ)^w.length) • ((wordField D (-d) w)[[n]]) (theta D v) := by
  induction w generalizing n v with
  | nil => simpa [wordField] using theta_actualField_ncoeff D d n v
  | cons x w ih =>
    simp only [wordField]
    have h := normalMinusOne_theta D
      (dividedDerivative x.2 (neutralField D x.1)) (wordField D d w)
      (dividedDerivative x.2 (neutralField D x.1)) (wordField D (-d) w)
      (-1) ((-1)^w.length)
      (by intro m u; simpa using theta_dividedDerivative D x m u)
      (by intro m u; exact ih m u) n v
    simpa [List.length_cons, pow_succ, mul_comm] using h

theorem sigma_word_product (D : LatticeData) (w : List (Index D)) :
    sigma D ((w.map (fun x => (X x : Oscillator D))).prod) =
      ((-1 : ℂ)^w.length) • (w.map (fun x => (X x : Oscillator D))).prod := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, sigma_X, ih, List.length_cons]
    rw [pow_succ, mul_comm ((-1 : ℂ)^w.length) (-1), mul_smul]
    simp [Algebra.mul_smul_comm]

theorem sigma_monomial (D : LatticeData) (e : Index D →₀ ℕ) :
    sigma D (monomial e 1) =
      ((-1 : ℂ)^(occurrences D e).length) • monomial e 1 := by
  rw [← occurrences_product]
  exact sigma_word_product D (occurrences D e)

theorem occurrences_length (D : LatticeData) (e : Index D →₀ ℕ) :
    (occurrences D e).length = e.sum (fun _ n => n) := by
  have h := congrArg Multiset.card (occurrences_multiset D e)
  rw [Multiset.coe_card, Finsupp.card_toMultiset] at h
  exact h

theorem sigma_monomial_degree_sign (D : LatticeData) (e : Index D →₀ ℕ) :
    sigma D (monomial e 1) =
      ((-1 : ℂ)^(e.sum (fun _ n => n))) • monomial e 1 := by
  rw [sigma_monomial, occurrences_length]

/-- The actual all-state, all-charge, all-integer-mode automorphism law. -/
theorem stateField_theta (D : LatticeData) (a b : Carrier D) (n : ℤ) :
    theta D (((Y D a)[[n]]) b) = ((Y D (theta D a))[[n]]) (theta D b) := by
  let left : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun a => theta D (((Y D a)[[n]]) b)
      map_add' := by intro a c; simp
      map_smul' := by intro s a; simp }
  let right : Carrier D →ₗ[ℂ] Carrier D :=
    { toFun := fun a => ((Y D (theta D a))[[n]]) (theta D b)
      map_add' := by intro a c; simp
      map_smul' := by intro s a; simp }
  have h : left = right := by
    apply Finsupp.lhom_ext
    intro d p
    have hp : left.comp (Finsupp.lsingle d) = right.comp (Finsupp.lsingle d) := by
      apply (basisMonomials (Index D) ℂ).ext
      intro e
      change theta D (((Y D (Finsupp.single d (monomial e 1)))[[n]]) b) =
        ((Y D (theta D (Finsupp.single d (monomial e 1))))[[n]]) (theta D b)
      rw [show theta D (Finsupp.single d (monomial e 1)) =
        Finsupp.single (-d) (sigma D (monomial e 1)) from theta_single D d _,
        sigma_monomial, ← Finsupp.smul_single,
        map_smul, stateField_monomial, stateField_monomial]
      simp only [VertexOperator.ncoeff, map_smul, LinearMap.smul_apply]
      exact wordField_theta D d (occurrences D e) n b
    exact LinearMap.congr_fun hp p
  exact LinearMap.congr_fun h a

/-- Scalar eigenvalues multiply under every actual integer mode. -/
theorem mode_eigenvalue_selection (D : LatticeData) (s t : ℂ)
    (a b : Carrier D) (ha : theta D a = s • a) (hb : theta D b = t • b) (n : ℤ) :
    theta D (((Y D a)[[n]]) b) = (s*t) • (((Y D a)[[n]]) b) := by
  rw [stateField_theta, ha, hb, map_smul]
  simp [smul_smul, mul_comm]


/-! ## Actual eigenspaces and the realized section phase -/

def eigenspace (D : LatticeData) (s : ℂ) : Submodule ℂ (Carrier D) :=
  LinearMap.ker (thetaLinear D - s • LinearMap.id)

@[simp] theorem mem_eigenspace (D : LatticeData) (s : ℂ) (v : Carrier D) :
    v ∈ eigenspace D s ↔ theta D v = s • v := by
  simp [eigenspace, LinearMap.mem_ker, sub_eq_zero, theta]

def fixedSpace (D : LatticeData) : Submodule ℂ (Carrier D) := eigenspace D 1
def minusSpace (D : LatticeData) : Submodule ℂ (Carrier D) := eigenspace D (-1)


@[simp] theorem mem_fixedSpace (D : LatticeData) (v : Carrier D) :
    v ∈ fixedSpace D ↔ theta D v = v := by simp [fixedSpace]
@[simp] theorem mem_minusSpace (D : LatticeData) (v : Carrier D) :
    v ∈ minusSpace D ↔ theta D v = -v := by simp [minusSpace]

def plusPart (D : LatticeData) (v : Carrier D) : Carrier D :=
  (2 : ℂ)⁻¹ • (v + theta D v)
def minusPart (D : LatticeData) (v : Carrier D) : Carrier D :=
  (2 : ℂ)⁻¹ • (v - theta D v)

theorem plusPart_mem (D : LatticeData) (v : Carrier D) :
    plusPart D v ∈ fixedSpace D := by
  rw [mem_fixedSpace]
  simp only [plusPart, map_smul, map_add, theta, LinearEquiv.coe_ofInvolutive]
  rw [theta_involutive D v]
  rw [add_comm]

theorem minusPart_mem (D : LatticeData) (v : Carrier D) :
    minusPart D v ∈ minusSpace D := by
  rw [mem_minusSpace]
  simp only [minusPart, map_smul, map_sub, theta, LinearEquiv.coe_ofInvolutive]
  rw [theta_involutive D v]
  rw [← neg_sub v (thetaLinear D v), smul_neg]

theorem fixed_minus_intersection (D : LatticeData) :
    fixedSpace D ⊓ minusSpace D = ⊥ := by
  apply le_antisymm
  · intro v hv
    have hp := (mem_fixedSpace D v).mp hv.1
    have hm := (mem_minusSpace D v).mp hv.2
    have h : (2 : ℂ) • v = 0 := by
      rw [two_smul]
      calc v + v = theta D v + v := by rw [hp]
           _ = -v + v := by rw [hm]
           _ = 0 := neg_add_cancel v
    have hz : v = 0 := (smul_eq_zero.mp h).resolve_left (by norm_num)
    simpa using hz
  · exact bot_le

/-- The ±1 sign law includes every integer mode of the actual Y. -/
theorem mode_sign_selection (D : LatticeData) (s t : ℂ)
    (_hs : s = 1 ∨ s = -1) (_ht : t = 1 ∨ t = -1)
    (a b : Carrier D) (ha : a ∈ eigenspace D s) (hb : b ∈ eigenspace D t) (n : ℤ) :
    ((Y D a)[[n]]) b ∈ eigenspace D (s*t) := by
  rw [mem_eigenspace]
  exact mode_eigenvalue_selection D s t a b
    ((mem_eigenspace D s a).mp ha) ((mem_eigenspace D t b).mp hb) n

theorem theta_rank_zero (D : LatticeData) (hD : D.rank = 0) (v : Carrier D) :
    theta D v = v := by
  have hs : ∀ p : Oscillator D, sigma D p = p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p x hp => exact False.elim (by have h := x.1.isLt; omega)
  have hc : ∀ a : Charge D, -a = a := by
    intro a; funext i; exact False.elim (by have h := i.isLt; omega)
  have h : thetaLinear D = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro a p
    simp [hs, hc]
  exact LinearMap.congr_fun h v

theorem minusSpace_rank_zero (D : LatticeData) (hD : D.rank = 0) :
    minusSpace D = ⊥ := by
  apply le_antisymm
  · intro v hv
    have hm := (mem_minusSpace D v).mp hv
    rw [theta_rank_zero D hD] at hm
    have h : (2 : ℂ) • v = 0 := by
      rw [two_smul]
      calc v + v = -v + v := congrArg (fun u => u + v) hm
           _ = 0 := neg_add_cancel v
    simpa using (smul_eq_zero.mp h).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  · exact bot_le

/-- The realized section square reuses the accepted integral half-norm theorem. -/
theorem realized_section_square (D : LatticeData) (a : Charge D) :
    lowerCocycleExponent D a a = bilinear D a a / 2 := by
  exact LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_square D a

/-- The inverse-section sign cancels the Dong--Nagatomo phase on actual ground states.
Here epsilon(a,-a) is its own inverse. This formula concerns this realized section. -/
theorem theta_ground_DongNagatomo (D : LatticeData) (a : Charge D) :
    theta D (Finsupp.single a (1 : Oscillator D)) =
      paritySign (bilinear D a a / 2) •
        (epsilon D a (-a) • Finsupp.single (-a) (1 : Oscillator D)) := by
  have hc : lowerCocycleExponent D a (-a) = -lowerCocycleExponent D a a := by
    simp [lowerCocycleExponent, Finset.sum_neg_distrib, add_comm]
  have hp : epsilon D a (-a) = paritySign (bilinear D a a / 2) := by
    rw [epsilon, hc, realized_section_square]
    simp [paritySign]
  rw [hp, smul_smul]
  have hs : paritySign (bilinear D a a / 2) * paritySign (bilinear D a a / 2) = 1 := by
    unfold paritySign
    split_ifs <;> norm_num
  rw [hs, one_smul]
  simp [theta]


/-! ## The restricted actual fixed vertex algebra -/

abbrev FixedCarrier (D : LatticeData) := ↥(fixedSpace D)

-- Keep the actual subtype group instance available while elaborating its endomorphisms.
local instance fixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

theorem fixed_mode_closed (D : LatticeData) (a b : Carrier D)
    (ha : a ∈ fixedSpace D) (hb : b ∈ fixedSpace D) (n : ℤ) :
    ((Y D a)[[n]]) b ∈ fixedSpace D := by
  rw [mem_fixedSpace, stateField_theta,
    (mem_fixedSpace D a).mp ha, (mem_fixedSpace D b).mp hb]

def fixedVacuum (D : LatticeData) : FixedCarrier D :=
  ⟨vacuum D, (mem_fixedSpace D _).mpr (theta_vacuum D)⟩

theorem fixed_translation_closed (D : LatticeData) (v : Carrier D)
    (hv : v ∈ fixedSpace D) : translation D v ∈ fixedSpace D := by
  rw [translation_as_mode]
  exact fixed_mode_closed D v (vacuum D) hv (fixedVacuum D).property (-2)

def fixedTranslation (D : LatticeData) : Module.End ℂ (FixedCarrier D) where
  toFun v := ⟨translation D v.val, fixed_translation_closed D v.val v.property⟩
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' s a := by apply Subtype.ext; exact map_smul _ _ _

def fixedMode (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    Module.End ℂ (FixedCarrier D) where
  toFun b := ⟨((Y D a.val)[[n]]) b.val,
    fixed_mode_closed D a.val b.val a.property b.property n⟩
  map_add' b c := by apply Subtype.ext; exact map_add _ _ _
  map_smul' s b := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem fixedMode_val (D : LatticeData) (a b : FixedCarrier D) (n : ℤ) :
    (fixedMode D a n b).val = ((Y D a.val)[[n]]) b.val := rfl

/-- Lower truncation is inherited statewise from the actual ambient field. -/
def fixedField (D : LatticeData) (a : FixedCarrier D) :
    VertexOperator ℂ (FixedCarrier D) :=
  VertexOperator.of_coeff (fun k => fixedMode D a (-k-1)) (by
    intro b
    refine ⟨((HahnModule.of ℂ).symm ((Y D a.val) b.val)).order, ?_⟩
    intro k hk
    by_contra h
    have hz : ((Y D a.val)[[-k-1]]) b.val = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hk (Subtype.ext hz))

@[simp] theorem fixedField_ncoeff (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    (fixedField D a)[[n]] = fixedMode D a n := by
  rw [fixedField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-n-1)-1 = n by omega]

def fixedY (D : LatticeData) :
    FixedCarrier D →ₗ[ℂ] VertexOperator ℂ (FixedCarrier D) where
  toFun := fixedField D
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro c
    simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply,
      LinearMap.add_apply, fixedField_ncoeff]
    apply Subtype.ext
    simp only [fixedMode_val, Submodule.coe_add, map_add, Pi.add_apply,
      LinearMap.add_apply]
  map_smul' s a := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro c
    simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply,
      LinearMap.smul_apply, fixedField_ncoeff]
    apply Subtype.ext
    simp only [fixedMode_val, Submodule.coe_smul, map_smul, Pi.smul_apply,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem fixedY_mode_val (D : LatticeData) (a b : FixedCarrier D) (n : ℤ) :
    (((fixedY D a)[[n]]) b).val = ((Y D a.val)[[n]]) b.val := by
  change (((fixedField D a)[[n]]) b).val = _
  rw [fixedField_ncoeff]; rfl

theorem fixed_creation (D : LatticeData) (a : FixedCarrier D) :
    ((fixedY D a)[[-1]]) (fixedVacuum D) = a := by
  apply Subtype.ext
  exact stateField_creation D a.val

theorem fixed_creativity (D : LatticeData) (a : FixedCarrier D) (n : ℤ)
    (hn : 0 ≤ n) : ((fixedY D a)[[n]]) (fixedVacuum D) = 0 := by
  apply Subtype.ext
  simpa only [fixedY_mode_val, fixedVacuum, Submodule.coe_zero] using
    stateField_creativity D a.val n hn

theorem fixed_vacuum_field (D : LatticeData) :
    fixedY D (fixedVacuum D) = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  rw [VertexOperator.coeff_eq_ncoeff, fixedY_mode_val]
  change ((Y D (vacuum D))[[-k-1]]) b.val = _
  rw [stateField_vacuum]
  simp [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  split_ifs <;> rfl

theorem fixed_covariance (D : LatticeData) (a : FixedCarrier D) (n : ℤ) :
    fixedTranslation D * ((fixedY D a)[[n]]) -
      ((fixedY D a)[[n]]) * fixedTranslation D =
        -(n : ℂ) • ((fixedY D a)[[n-1]]) := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  have h := LinearMap.congr_fun (stateField_covariance D a.val n) b.val
  simpa [fixedTranslation, Module.End.mul_apply] using h

/-- Subtype inclusion identifies every iterated locality coefficient. -/
theorem fixed_delta_transport (D : LatticeData)
    (f : ℤ → ℤ → Module.End ℂ (FixedCarrier D))
    (g : ℤ → ℤ → Module.End ℂ (Carrier D))
    (h : ∀ m n b, (f m n b).val = g m n b.val)
    (N : ℕ) (m n : ℤ) (b : FixedCarrier D) :
    ((delta^[N] f) m n b).val = (delta^[N] g) m n b.val := by
  induction N generalizing f g m n with
  | zero => exact h m n b
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change ((delta^[N] f) (m+1) n b - (delta^[N] f) m (n+1) b).val =
      (delta^[N] g) (m+1) n b.val - (delta^[N] g) m (n+1) b.val
    simp only [Submodule.coe_sub]
    rw [ih f g h (m+1) n, ih f g h m (n+1)]

theorem fixed_locality (D : LatticeData) (a b : FixedCarrier D) :
    ∃ N : ℕ, delta^[N]
      (FieldNormalProductLocality.commutator (fixedY D a) (fixedY D b)) = 0 := by
  obtain ⟨N, hN⟩ := LatticeAllStateLocality.stateField_locality D a.val b.val
  refine ⟨N, ?_⟩
  funext m n
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have h := fixed_delta_transport D
    (FieldNormalProductLocality.commutator (fixedY D a) (fixedY D b))
    (FieldNormalProductLocality.commutator (Y D a.val) (Y D b.val))
    (by intro u v w; simp [FieldNormalProductLocality.commutator,
      Module.End.mul_apply]) N m n c
  rw [hN] at h
  simpa using h

/-- Inclusion preserves zero exactly, hence the genuine support, for every family. -/
theorem fixed_support_transport (D : LatticeData) {I : Type*}
    (f : I → FixedCarrier D) :
    Function.support (fun i => (f i).val) = Function.support f := by
  ext i
  simp only [Function.mem_support]
  exact Subtype.val_injective.ne_iff' rfl

theorem fixed_finite_transport (D : LatticeData) {I : Type*}
    (f : I → FixedCarrier D)
    (h : Function.HasFiniteSupport (fun i => (f i).val)) :
    Function.HasFiniteSupport f := by
  simpa only [Function.HasFiniteSupport, fixed_support_transport] using h

theorem fixed_finsum_val (D : LatticeData) {I : Type*} (f : I → FixedCarrier D) :
    (∑ᶠ i, f i).val = ∑ᶠ i, (f i).val :=
  (fixedSpace D).subtype.toAddMonoidHom.map_finsum_of_injective Subtype.val_injective f

/-- Full p,q,r : Int identity and all three actual finite supports. -/
theorem fixed_borcherds (D : LatticeData) (a b c : FixedCarrier D) (p q r : ℤ) :
    let mu : FixedCarrier D → ℤ → FixedCarrier D → FixedCarrier D :=
      fun a n b => ((fixedY D a)[[n]]) b
    let left : ℕ → FixedCarrier D :=
      fun i => integerBinomial p i • mu (mu a (r+i) b) (p+q-i) c
    let first : ℕ → FixedCarrier D := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) • mu a (p+r-i) (mu b (q+i) c)
    let second : ℕ → FixedCarrier D := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (mu a (p+r-i) (mu b (q+i) c) -
              StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c)) := by
  dsimp only
  have h := (actualVertexAlgebra D).borcherds a.val b.val c.val p q r
  dsimp only [actualVertexAlgebra] at h
  refine ⟨fixed_finite_transport D _ ?_, fixed_finite_transport D _ ?_,
    fixed_finite_transport D _ ?_, ?_⟩
  · simpa only [Submodule.coe_smul, fixedY_mode_val] using h.1
  · simpa only [Submodule.coe_smul, fixedY_mode_val] using h.2.1
  · simpa only [Submodule.coe_smul, fixedY_mode_val] using h.2.2.1
  · apply Subtype.ext
    simpa only [fixed_finsum_val, Submodule.coe_smul, Submodule.coe_sub,
      fixedY_mode_val] using h.2.2.2

/-- The actual ungraded fixed VA, without compatibility hypotheses. -/
def fixed_actualVertexAlgebra (D : LatticeData) : StateFieldVertexAlgebra (FixedCarrier D) where
  stateField := fixedY D
  vacuum := fixedVacuum D
  translation := fixedTranslation D
  vacuum_field := fixed_vacuum_field D
  creation := fixed_creation D
  creativity := fixed_creativity D
  translation_vacuum := by
    apply Subtype.ext
    exact translation_kills_vacuum D
  covariance := fixed_covariance D
  locality := fixed_locality D
  borcherds := fixed_borcherds D


end
end D5.S3.VertexAlgebra.LatticeInvolution
