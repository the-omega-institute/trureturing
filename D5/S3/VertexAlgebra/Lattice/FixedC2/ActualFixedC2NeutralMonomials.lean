/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2NeutralMonomials
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Intrinsic fixed quotient multiplication and neutral word reduction by oscillator length. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralPairs
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
import Mathlib.LinearAlgebra.Quotient.Bilinear

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraCurrents LatticeInvolution LatticeFiniteNegativeGeneration
open LatticeActualConformalState LatticeActualStateDerivative LatticeActualAnnihilation
open LatticeActualStateFieldCalculus MvPolynomial FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped VertexOperator

open private finite_sum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
open private derivative_modes derivative_creation normal_right_identity
  from D5.S3.VertexAlgebra.LatticeAllStateField

noncomputable section

local instance (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

private theorem higher_fixed_product_mem (D : LatticeData) (r : ℕ)
    (a b : FixedCarrier D) : fixedMode D a (-((r : ℤ) + 2)) b ∈ fixedC2 D := by
  induction r generalizing a b with
  | zero => exact Submodule.subset_span ⟨a, b, rfl⟩
  | succ r ih =>
    have derivative :
        fixedMode D (fixedTranslation D a) (-((r : ℤ) + 2)) b =
          (r + 2 : ℂ) • fixedMode D a (-(((r + 1 : ℕ) : ℤ) + 2)) b := by
      apply Subtype.ext
      change ((Y D (LatticeSugawaraConformal.translation D a.val))[[ -((r : ℤ) + 2)]]) b.val =
        (r + 2 : ℂ) • ((Y D a.val)[[ -(((r + 1 : ℕ) : ℤ) + 2)]]) b.val
      have h := LinearMap.congr_fun
        (state_derivative_modes D a.val (-((r : ℤ) + 2))) b.val
      simpa only [LinearMap.smul_apply, Int.cast_neg, neg_neg, Int.cast_add,
        Int.cast_natCast, Int.cast_ofNat, show -((r : ℤ) + 2) - 1 =
          -(((r + 1 : ℕ) : ℤ) + 2) by omega] using h
    have previous := ih (fixedTranslation D a) b
    rw [derivative] at previous
    have hn : (r + 2 : ℂ) ≠ 0 := by exact_mod_cast (show r + 2 ≠ 0 by omega)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
      (fixedC2 D).smul_mem (r + 2 : ℂ)⁻¹ previous

private def fixedCommutatorTerm (D : LatticeData) (u v w : FixedCarrier D)
    (p q : ℤ) (j : ℕ) : FixedCarrier D :=
  integerBinomial p j • fixedMode D (fixedMode D u j v) (p + q - j) w

private theorem fixed_commutator_finite (D : LatticeData) (u v w : FixedCarrier D)
    (p q : ℤ) : Function.HasFiniteSupport (fixedCommutatorTerm D u v w p q) := by
  apply (commutator_terms_finite D u.val v.val p q).subset
  intro j hj
  contrapose! hj
  rw [Function.notMem_support] at hj ⊢
  apply Subtype.ext
  change commutatorTerm D u.val v.val p q j w.val = 0
  rw [show commutatorTerm D u.val v.val p q j = 0 from hj, LinearMap.zero_apply]

private theorem fixed_commutator (D : LatticeData) (u v w : FixedCarrier D)
    (p q : ℤ) :
    fixedMode D u p (fixedMode D v q w) - fixedMode D v q (fixedMode D u p w) =
      ∑ᶠ j, fixedCommutatorTerm D u v w p q j := by
  apply Subtype.ext
  change _ = (fixedSpace D).subtype (∑ᶠ j, fixedCommutatorTerm D u v w p q j)
  rw [map_finsum _ (fixed_commutator_finite D u v w p q)]
  have h := LinearMap.congr_fun (mode_commutator D u.val v.val p q) w.val
  change _ = LinearMap.applyₗ w.val (∑ᶠ j, commutatorTerm D u.val v.val p q j) at h
  rw [map_finsum _ (commutator_terms_finite D u.val v.val p q)] at h
  exact h

/-- The actual fixed (-1) product preserves intrinsic C₂ in the second argument. -/
theorem fixed_product_mem_c2 (D : LatticeData) (u z : FixedCarrier D)
    (hz : z ∈ fixedC2 D) : fixedMode D u (-1) z ∈ fixedC2 D := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, w, rfl⟩ := hz
    have each (j : ℕ) : fixedCommutatorTerm D u v w (-1) (-2) j ∈ fixedC2 D := by
      unfold fixedCommutatorTerm
      apply (fixedC2 D).smul_mem
      simpa only [show (-1 : ℤ) + -2 - (j : ℤ) = -(((j+1 : ℕ) : ℤ) + 2) by omega]
        using higher_fixed_product_mem D (j + 1) (fixedMode D u j v) w
    have correction := finite_sum_mem (fixedC2 D) _
      (fixed_commutator_finite D u v w (-1) (-2)) each
    have base : fixedMode D v (-2) (fixedMode D u (-1) w) ∈ fixedC2 D :=
      Submodule.subset_span ⟨v, fixedMode D u (-1) w, rfl⟩
    rw [← fixed_commutator] at correction
    simpa only [sub_add_cancel] using (fixedC2 D).add_mem correction base
  | zero => simp
  | add z w _ _ hz hw => simpa only [map_add] using (fixedC2 D).add_mem hz hw
  | smul c z _ hz => simpa only [map_smul] using (fixedC2 D).smul_mem c hz

private theorem fixed_product_comm_mem (D : LatticeData) (u v : FixedCarrier D) :
    fixedMode D u (-1) v - fixedMode D v (-1) u ∈ fixedC2 D := by
  have each (j : ℕ) : fixedCommutatorTerm D u v (fixedVacuum D) (-1) (-1) j ∈
      fixedC2 D := by
    unfold fixedCommutatorTerm
    apply (fixedC2 D).smul_mem
    simpa only [show (-1 : ℤ) + -1 - (j : ℤ) = -((j : ℤ) + 2) by omega]
      using higher_fixed_product_mem D j (fixedMode D u j v) (fixedVacuum D)
  have correction := finite_sum_mem (fixedC2 D) _
    (fixed_commutator_finite D u v (fixedVacuum D) (-1) (-1)) each
  rw [← fixed_commutator] at correction
  have creation (a : FixedCarrier D) : fixedMode D a (-1) (fixedVacuum D) = a :=
    Subtype.ext (stateField_creation D a.val)
  simpa only [creation] using correction

/-- The actual fixed (-1) product preserves intrinsic C₂ in the first argument. -/
theorem fixed_c2_product_mem (D : LatticeData) (z u : FixedCarrier D)
    (hz : z ∈ fixedC2 D) : fixedMode D z (-1) u ∈ fixedC2 D := by
  simpa only [sub_add_cancel] using (fixedC2 D).add_mem (fixed_product_comm_mem D z u)
    (fixed_product_mem_c2 D u z hz)

private def fixedProduct (D : LatticeData) :
    FixedCarrier D →ₗ[ℂ] FixedCarrier D →ₗ[ℂ] (FixedCarrier D ⧸ fixedC2 D) :=
  LinearMap.mk₂ ℂ (fun a b => (fixedC2 D).mkQ (fixedMode D a (-1) b))
    (fun a a' b => by
      rw [← map_add]
      congr 1
      apply Subtype.ext
      change mu D (a.val + a'.val) (-1) b.val =
        mu D a.val (-1) b.val + mu D a'.val (-1) b.val
      simp only [mu, map_add, Pi.add_apply, LinearMap.add_apply])
    (fun c a b => by
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      change mu D (c • a.val) (-1) b.val = c • mu D a.val (-1) b.val
      simp only [mu, map_smul, Pi.smul_apply, LinearMap.smul_apply])
    (fun a b b' => map_add ((fixedC2 D).mkQ.comp (fixedMode D a (-1))) b b')
    (fun c a b => map_smul ((fixedC2 D).mkQ.comp (fixedMode D a (-1))) c b)

/-- The product on the intrinsic fixed C₂ quotient induced by the actual (-1) mode. -/
def fixedQuotientProduct (D : LatticeData) :
    (FixedCarrier D ⧸ fixedC2 D) →ₗ[ℂ] (FixedCarrier D ⧸ fixedC2 D) →ₗ[ℂ]
      (FixedCarrier D ⧸ fixedC2 D) :=
  (fixedProduct D).liftQ₂ (fixedC2 D) (fixedC2 D)
    (fun z hz => LinearMap.mem_ker.mpr (LinearMap.ext fun u =>
      (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr (fixed_c2_product_mem D z u hz)))
    (fun z hz => LinearMap.mem_ker.mpr (LinearMap.ext fun u =>
      (Submodule.Quotient.mk_eq_zero (p := fixedC2 D)).mpr (fixed_product_mem_c2 D u z hz)))

@[simp] theorem fixed_quotient_product_mk (D : LatticeData) (a b : FixedCarrier D) :
    fixedQuotientProduct D ((fixedC2 D).mkQ a) ((fixedC2 D).mkQ b) =
      (fixedC2 D).mkQ (fixedMode D a (-1) b) := rfl

/-- The oscillator polynomial of a word, with oscillator indices numbered from zero. -/
def neutralPolynomial (D : LatticeData) (w : List (Index D)) : Oscillator D :=
  (w.map fun x => (X x : Oscillator D)).prod

private abbrev embed (D : LatticeData) : Oscillator D →ₗ[ℂ] Carrier D := Finsupp.lsingle 0

/-- The neutral lattice state of an oscillator word in the vacuum charge. -/
def neutralWord (D : LatticeData) (w : List (Index D)) : Carrier D :=
  embed D (neutralPolynomial D w)

private abbrev jet (D : LatticeData) (x : Index D) :=
  dividedDerivative x.2 (neutralField D x.1)

private theorem single_state_field (D : LatticeData) (x : Index D) :
    Y D (embed D (X x)) = jet D x := by
  change Y D (Finsupp.single 0 (X x)) = _
  rw [X, stateField_monomial]
  simp only [occurrences, Finsupp.toMultiset_single, one_nsmul,
    Multiset.toList_singleton, wordField]
  rw [actual_zero, normal_right_identity]

private theorem single_mode_create (D : LatticeData) (x : Index D) (p : Oscillator D) :
    mu D (embed D (X x)) (-1) (embed D p) = embed D (X x * p) := by
  unfold mu
  rw [single_state_field]
  exact derivative_creation D x 0 p

private def polynomialLength (D : LatticeData) (n : ℕ) : Submodule ℂ (Oscillator D) :=
  Submodule.span ℂ {p | ∃ w : List (Index D), w.length = n ∧ p = neutralPolynomial D w}

private theorem polynomial_word_mem (D : LatticeData) (w : List (Index D)) :
    neutralPolynomial D w ∈ polynomialLength D w.length :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

private theorem polynomial_create_mem (D : LatticeData) (x : Index D) (n : ℕ)
    (p : Oscillator D) (hp : p ∈ polynomialLength D n) :
    X x * p ∈ polynomialLength D (n + 1) := by
  change p ∈ (polynomialLength D (n + 1)).comap (LinearMap.mulLeft ℂ (X x))
  refine (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨x :: w, by simp [hw], rfl⟩

private theorem annihilate_word_mem (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (w : List (Index D)) :
    annihilate D i k (neutralPolynomial D w) ∈ polynomialLength D (w.length - 1) := by
  induction w with
  | nil =>
    change annihilate D i k 1 ∈ polynomialLength D 0
    rw [← annihilation_apply, Derivation.map_one_eq_zero]
    exact (polynomialLength D 0).zero_mem
  | cons x w ih =>
    change annihilate D i k (X x * neutralPolynomial D w) ∈ polynomialLength D w.length
    rw [annihilate_mul]
    apply Submodule.add_mem
    · rw [show x = (x.1, x.2) from rfl, annihilate_X]
      split_ifs
      · simpa only [smul_mul_assoc, one_mul] using
          (polynomialLength D w.length).smul_mem (D.G i x.1 : ℂ) (polynomial_word_mem D w)
      · rw [zero_mul]
        exact Submodule.zero_mem _
    · cases w with
      | nil =>
        change X x * annihilate D i k 1 ∈ polynomialLength D 0
        rw [← annihilation_apply, Derivation.map_one_eq_zero, mul_zero]
        exact Submodule.zero_mem _
      | cons y w => exact polynomial_create_mem D x w.length _ ih

/-- The span of vacuum-charge words of exactly the given oscillator length. -/
def neutralLength (D : LatticeData) (n : ℕ) : Submodule ℂ (Carrier D) :=
  (polynomialLength D n).map (embed D)

private theorem jet_negative_length (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : m < 0) (n : ℕ) (v : Carrier D) (hv : v ∈ neutralLength D n) :
    ((jet D x)[[m]]) v ∈ neutralLength D (n + 1) := by
  obtain ⟨p, hp, rfl⟩ := hv
  let k := (-(m - (x.2 : ℤ)) - 1).toNat
  have hmode : m - (x.2 : ℤ) = -(k : ℤ) - 1 := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  rw [derivative_modes, LinearMap.smul_apply, hmode]
  apply Submodule.smul_mem
  change neutralMode D x.1 (-(k : ℤ) - 1) (Finsupp.single 0 p) ∈ _
  rw [neutralMode_single, neutralPolynomialMode_negative]
  exact ⟨X (x.1, k) * p, polynomial_create_mem D _ n p hp, rfl⟩

private theorem jet_nonneg_length (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : 0 ≤ m) (y : Index D) (w : List (Index D)) :
    ((jet D x)[[m]]) (neutralWord D (y :: w)) ∈ neutralLength D w.length := by
  rw [derivative_modes, LinearMap.smul_apply]
  rcases lt_trichotomy m (x.2 : ℤ) with h | h | h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m - 1 + (x.2 : ℤ) by omega)
    have hk' : k < x.2 := by omega
    rw [hk, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hk']
    simp
  · rw [show m - (x.2 : ℤ) = 0 by omega]
    change _ • (neutralMode D x.1 0 (Finsupp.single 0 (neutralPolynomial D (y :: w)))) ∈ _
    rw [neutralMode_single]
    simp [neutralPolynomialMode, bilinear]
  · let k := (m - (x.2 : ℤ) - 1).toNat
    have hmode : m - (x.2 : ℤ) = (k : ℤ) + 1 := by
      dsimp [k]
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    rw [hmode]
    apply Submodule.smul_mem
    change neutralMode D x.1 ((k : ℤ) + 1)
      (Finsupp.single 0 (neutralPolynomial D (y :: w))) ∈ _
    rw [neutralMode_single, neutralPolynomialMode_positive, LinearMap.smul_apply]
    change embed D ((k + 1 : ℂ) • annihilate D x.1 k (neutralPolynomial D (y :: w))) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ _ ⟨_, annihilate_word_mem D x.1 k (y :: w), rfl⟩

private theorem quadratic_pair_as_product (D : LatticeData) (x y : Index D) :
    (neutralPair D x.1 y.1 x.2 y.2).val =
      mu D (embed D (X x)) (-1) (embed D (X y)) := by
  rw [single_mode_create]
  rfl

/-- The two finite normal-ordering families of the actual quadratic (-1) product.
The zeroth first-family coefficient concatenates the two creation variables. -/
private theorem quadratic_word_iterate (D : LatticeData) (x y : Index D)
    (w : List (Index D)) :
    let first (j : ℕ) := ((jet D x)[[-(j : ℤ) - 1]])
      (((jet D y)[[(-1 : ℤ) + j]]) (neutralWord D w))
    let second (j : ℕ) := ((jet D y)[[-2 - (j : ℤ)]])
      (((jet D x)[[j]]) (neutralWord D w))
    Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
      mu D (neutralPair D x.1 y.1 x.2 y.2).val (-1) (neutralWord D w) =
        (∑ᶠ j, first j) + (∑ᶠ j, second j) := by
  have h := stateField_iterate D (embed D (X x)) (embed D (X y)) (neutralWord D w) (-1) (-1)
  dsimp only at h
  simp_rw [show ∀ j : ℕ, (-1 : ℂ)^j * ((Ring.choose (-1) j : ℤ) : ℂ) = 1
    from minus_one_binomial] at h
  rw [quadratic_pair_as_product]
  simpa only [one_smul, show (-1 : ℂ)^(-1 : ℤ) = -1 by norm_num, neg_one_smul,
    sub_neg_eq_add, show ∀ j : ℕ, (-1 : ℤ) - j = -(j : ℤ) - 1 by intro j; omega,
    show (-1 : ℤ) + -1 = -2 by norm_num, ← single_state_field, mu] using h

/-- Removing the leading concatenation from the actual quadratic (-1) product
leaves a span of words of the input length, two oscillators below the leading term. -/
theorem quadratic_word_length (D : LatticeData) (x y : Index D) (w : List (Index D)) :
    mu D (neutralPair D x.1 y.1 x.2 y.2).val (-1) (neutralWord D w) -
      neutralWord D (x :: y :: w) ∈ neutralLength D w.length := by
  cases w with
  | nil =>
    rw [show neutralWord D [] = vacuum D from rfl,
      show neutralWord D [x, y] = (neutralPair D x.1 y.1 x.2 y.2).val by
        change embed D (X x * (X y * 1)) = _
        rw [mul_one]; rfl]
    rw [show mu D _ (-1) (vacuum D) = (neutralPair D x.1 y.1 x.2 y.2).val
      from stateField_creation D _]
    rw [sub_self]
    exact (neutralLength D 0).zero_mem
  | cons z w =>
    let N := neutralLength D (z :: w).length
    let v := neutralWord D (z :: w)
    let first (j : ℕ) := ((jet D x)[[-(j : ℤ) - 1]]) (((jet D y)[[(-1 : ℤ) + j]]) v)
    let second (j : ℕ) := ((jet D y)[[-2 - (j : ℤ)]]) (((jet D x)[[j]]) v)
    obtain ⟨hf, hs, h⟩ : Function.HasFiniteSupport first ∧ Function.HasFiniteSupport second ∧
        mu D (neutralPair D x.1 y.1 x.2 y.2).val (-1) v =
          (∑ᶠ j, first j) + (∑ᶠ j, second j) := quadratic_word_iterate D x y (z :: w)
    have leading : first 0 = neutralWord D (x :: y :: z :: w) := by
      change ((jet D x)[[-1]]) (((jet D y)[[-1]])
        (Finsupp.single (0 : Charge D) (neutralPolynomial D (z :: w)))) = _
      rw [derivative_creation D y 0, derivative_creation D x 0]
      rfl
    have first_high (j : ℕ) (hj : j ≠ 0) : first j ∈ N :=
      jet_negative_length D x _ (by omega) _ _
        (jet_nonneg_length D y _ (by omega) z w)
    have second_all (j : ℕ) : second j ∈ N :=
      jet_negative_length D y _ (by omega) _ _
        (jet_nonneg_length D x _ (by omega) z w)
    apply (Submodule.Quotient.mk_eq_zero (p := N)).mp
    change N.mkQ (_ - _) = 0
    rw [h, ← leading, map_sub, map_add, map_finsum N.mkQ hf]
    have first_image : (∑ᶠ j, N.mkQ (first j)) = N.mkQ (first 0) :=
      finsum_eq_single _ 0 (fun j hj =>
        (Submodule.Quotient.mk_eq_zero (p := N)).mpr (first_high j hj))
    have second_image : N.mkQ (∑ᶠ j, second j) = 0 :=
      (Submodule.Quotient.mk_eq_zero (p := N)).mpr (finite_sum_mem N second hs second_all)
    rw [first_image, second_image, add_zero, sub_self]

private theorem theta_neutralWord (D : LatticeData) (w : List (Index D)) (hw : Even w.length) :
    theta D (neutralWord D w) = neutralWord D w := by
  change thetaLinear D (Finsupp.single 0 (neutralPolynomial D w)) = _
  rw [theta_single, neg_zero]
  have hs := sigma_word_product D w
  change sigma D (neutralPolynomial D w) =
      (-1 : ℂ)^w.length • neutralPolynomial D w at hs
  rw [hs, hw.neg_one_pow, one_smul]
  rfl

/-- An even-length vacuum-charge word as an element of the literal fixed carrier. -/
def fixedNeutralWord (D : LatticeData) (w : List (Index D)) (hw : Even w.length) : FixedCarrier D :=
  ⟨neutralWord D w, (mem_fixedSpace D _).mpr (theta_neutralWord D w hw)⟩

/-- The intrinsic fixed C₂ class of an even vacuum-charge word. -/
def neutralWordClass (D : LatticeData) (w : List (Index D)) (hw : Even w.length) :
    FixedCarrier D ⧸ fixedC2 D :=
  (fixedC2 D).mkQ (fixedNeutralWord D w hw)

private def fixedWordLength (D : LatticeData) (n : ℕ) (hn : Even n) :
    Submodule ℂ (FixedCarrier D) :=
  Submodule.span ℂ {v | ∃ (w : List (Index D)) (hw : w.length = n),
    v = fixedNeutralWord D w (hw.symm ▸ hn)}

private theorem map_fixedWordLength (D : LatticeData) (n : ℕ) (hn : Even n) :
    (fixedWordLength D n hn).map (fixedSpace D).subtype = neutralLength D n := by
  unfold fixedWordLength neutralLength polynomialLength
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨neutralPolynomial D w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fixedNeutralWord D w (hw.symm ▸ hn), ⟨w, hw, rfl⟩, rfl⟩

/-- The span in the intrinsic fixed quotient of the neutral classes of length n. -/
def neutralClassLength (D : LatticeData) (n : ℕ) (hn : Even n) :
    Submodule ℂ (FixedCarrier D ⧸ fixedC2 D) :=
  (fixedWordLength D n hn).map (fixedC2 D).mkQ

private theorem even_cons_cons (D : LatticeData) (x y : Index D) (w : List (Index D))
    (hw : Even w.length) : Even (x :: y :: w).length := by
  change Even (w.length + 1 + 1)
  rw [Nat.add_assoc]
  exact hw.add (by decide : Even 2)

/-- In the intrinsic fixed quotient the quadratic product has leading word
obtained by concatenation, with contraction classes of length two less. -/
theorem fixed_quadratic_word_length (D : LatticeData) (x y : Index D) (w : List (Index D))
    (hw : Even w.length) :
    fixedQuotientProduct D (pairClass D x.1 y.1 x.2 y.2) (neutralWordClass D w hw) -
      neutralWordClass D (x :: y :: w) (even_cons_cons D x y w hw) ∈
        neutralClassLength D w.length hw := by
  let P := fixedMode D (neutralPair D x.1 y.1 x.2 y.2) (-1) (fixedNeutralWord D w hw)
  let L := fixedNeutralWord D (x :: y :: w) (even_cons_cons D x y w hw)
  have h : (P - L).val ∈ neutralLength D w.length := quadratic_word_length D x y w
  rw [← map_fixedWordLength D _ hw] at h
  obtain ⟨p, hp, he⟩ := h
  have hp' : P - L ∈ fixedWordLength D _ hw :=
    Subtype.ext he ▸ hp
  simp only [neutralWordClass, fixed_quotient_product_mk, ← map_sub, pairClass]
  exact ⟨P - L, hp', rfl⟩

/-- Any even neutral word containing a pair of index sum at least seven reduces
to the span of neutral words with two fewer oscillators. The pair can occur
anywhere in the word. -/
theorem neutral_word_high_pair (D : LatticeData) (x y : Index D) (w rest : List (Index D))
    (hrest : Even rest.length) (perm : w.Perm (x :: y :: rest))
    (hw : Even w.length) (hx : D.G x.1 x.1 ≠ 0) (hxy : 7 ≤ x.2 + y.2) :
    neutralWordClass D w hw ∈ neutralClassLength D rest.length hrest := by
  have hp : neutralWordClass D w hw =
      neutralWordClass D (x :: y :: rest) (even_cons_cons D x y rest hrest) := by
    unfold neutralWordClass
    apply congrArg (fixedC2 D).mkQ
    apply Subtype.ext
    exact congrArg (embed D) ((perm.map (fun t => (X t : Oscillator D))).prod_eq)
  rw [hp]
  have h := fixed_quadratic_word_length D x y rest hrest
  rw [neutral_pair_class_high D x.1 y.1 x.2 y.2 hx hxy] at h
  simpa only [map_zero, LinearMap.zero_apply, zero_sub, neg_mem_iff] using h

open ActualLeechHyperbolic (leechData leech_spec)

/-- The high-pair length reduction for the actual Leech fixed-lattice VOA. -/
theorem leech_neutral_word_high_pair (x y : Index leechData)
    (w rest : List (Index leechData)) (hrest : Even rest.length)
    (perm : w.Perm (x :: y :: rest)) (hw : Even w.length) (hxy : 7 ≤ x.2 + y.2) :
    neutralWordClass leechData w hw ∈ neutralClassLength leechData rest.length hrest :=
  neutral_word_high_pair leechData x y w rest hrest perm hw
    (gram_diagonal_ne leechData leech_spec.2.2.1 _) hxy

end
end D5.S3.VertexAlgebra.Lattice.ActualFixedC2
