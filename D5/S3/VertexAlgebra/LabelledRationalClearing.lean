/- GID: D5/S3/VertexAlgebra/LabelledRationalClearing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LabelledRationalClearing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-label oriented clearing and all-integer partial fractions. -/

/-
Fixed-label oriented clearing and all-integer partial fractions.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.CollisionRationalExpansions
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- Algebraic currying of the fixed-labelled common rational field.
No spectator coefficient is extracted in this construction. -/
namespace LabelledRationalClearing.GlobalRationalCurry
open CollisionRationalExpansions.OrderedRationalExpansion
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

abbrev Remaining := {i : Fin N // i ≠ z}
abbrev CoefficientPolynomial := AddMonoidAlgebra K (Remaining z → ℤ)
abbrev CoefficientField := FractionRing (CoefficientPolynomial K z)

def splitExponents : (Fin N → ℤ) ≃+ (ℤ × (Remaining z → ℤ)) where
  toFun e := (e z, fun i => e i.val)
  invFun p := fun i => if h : i = z then p.1 else p.2 ⟨i, h⟩
  left_inv e := by funext i; dsimp; split_ifs with h <;> simp_all
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i; simp [i.property]
  map_add' _ _ := rfl

/-- A genuine ring equivalence to a univariate Laurent polynomial over all
remaining labelled variables, including x and every spectator. -/
def curryLaurent : LabelledPolynomial K N ≃+*
    LaurentPolynomial (CoefficientPolynomial K z) :=
  (AddMonoidAlgebra.domCongr K K (splitExponents z)).toRingEquiv.trans
    AddMonoidAlgebra.curryRingEquiv

def coefficientsToField : LaurentPolynomial (CoefficientPolynomial K z) →+*
    LaurentPolynomial (CoefficientField K z) :=
  AddMonoidAlgebra.mapRingHom ℤ
    (algebraMap (CoefficientPolynomial K z) (CoefficientField K z))

lemma coefficientsToField_injective : Function.Injective (coefficientsToField K z) :=
  AddMonoidAlgebra.map_injective _
    (IsFractionRing.injective (CoefficientPolynomial K z) (CoefficientField K z))

variable {E : Type*} [Field E]
def laurentToRat : LaurentPolynomial E →+* RatFunc E :=
  LaurentPolynomial.eval₂ (algebraMap E (RatFunc E))
    (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

lemma laurentToRat_polynomial (p : Polynomial E) :
    laurentToRat p.toLaurent = algebraMap (Polynomial E) (RatFunc E) p := by
  rw [laurentToRat, LaurentPolynomial.eval₂_toLaurent]
  exact RatFunc.aeval_X_left_eq_algebraMap p

lemma laurentToRat_injective : Function.Injective (laurentToRat (E := E)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have hpr : algebraMap (Polynomial E) (RatFunc E) p = 0 := by
    rw [← laurentToRat_polynomial, hp, map_mul, hf, zero_mul]
  have hp0 : p = 0 := (IsFractionRing.injective (Polynomial E) (RatFunc E)).eq_iff.mp
    (hpr.trans (map_zero _).symm)
  have hprod : f * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← hp, hp0, map_zero]
  have hcancel := congrArg (fun a : LaurentPolynomial E => a * LaurentPolynomial.T (-(n : ℤ))) hprod
  simpa only [mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one, zero_mul] using hcancel

/-- The actual global Laurent algebra embeds in RatFunc E with z distinguished.
This preserves all labels and does not choose or erase their expansion order. -/
def curryPolynomial : LabelledPolynomial K N →+* RatFunc (CoefficientField K z) :=
  laurentToRat.comp ((coefficientsToField K z).comp (curryLaurent K z).toRingHom)

lemma curryPolynomial_injective : Function.Injective (curryPolynomial K z) :=
  laurentToRat_injective.comp
    ((coefficientsToField_injective K z).comp (curryLaurent K z).injective)

def curryRational : CommonRational K N →+* RatFunc (CoefficientField K z) :=
  IsFractionRing.lift (curryPolynomial_injective K z)

theorem curry_global_fraction (P Q : LabelledPolynomial K N) :
    curryRational K z
      (algebraMap _ (CommonRational K N) P / algebraMap _ (CommonRational K N) Q) =
    curryPolynomial K z P / curryPolynomial K z Q := by
  rw [map_div₀]
  simp only [curryRational, IsFractionRing.lift_algebraMap]

end LabelledRationalClearing.GlobalRationalCurry
end

section
/- The clearing polynomial below is the fixed-labelled product from
D5/S3/VertexAlgebra/UniformGradedLocalCorrelator.lean at baseline
a9f81b99cc33d0237e282b78e073ed90dddcb737, generalized only in its scalar field.
All statements here are algebraic, before any Hahn expansion or coefficient
extraction. Only labelled pair differences are admitted as pole factors. -/
namespace LabelledRationalClearing.PairDifferenceLocalization
open LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.OrderedRationalExpansion
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

def variablePolynomial (i : Fin N) : LabelledPolynomial K N :=
  AddMonoidAlgebra.single (Pi.single i 1) 1
def pairPolynomial (i j : Fin N) : LabelledPolynomial K N :=
  variablePolynomial K i - variablePolynomial K j
def labelledPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)
def clearingPolynomial (N k : ℕ) : LabelledPolynomial K N :=
  ∏ p ∈ labelledPairs N, pairPolynomial K p.1 p.2 ^ k

def remainingVariable (i : Remaining z) : CoefficientField K z :=
  algebraMap (CoefficientPolynomial K z) (CoefficientField K z)
    (AddMonoidAlgebra.single (Pi.single i 1) 1)

theorem remainingVariable_injective : Function.Injective (remainingVariable K z) := by
  classical
  intro i j h
  apply (IsFractionRing.injective (CoefficientPolynomial K z) (CoefficientField K z)) at h
  have he : (Pi.single i 1 : Remaining z → ℤ) = Pi.single j 1 :=
    AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0) h
  by_contra hne
  have hi := congrFun he i
  simpa [hne, Ne.symm hne] using hi

theorem curryPolynomial_single (e : Fin N → ℤ) (a : K) :
    curryPolynomial K z (AddMonoidAlgebra.single e a) =
      RatFunc.C (algebraMap (CoefficientPolynomial K z) (CoefficientField K z)
        (AddMonoidAlgebra.single (fun i : Remaining z => e i.val) a)) *
      RatFunc.X ^ e z := by
  have hcurry : curryLaurent K z (AddMonoidAlgebra.single e a) =
      AddMonoidAlgebra.single (e z)
        (AddMonoidAlgebra.single (fun i : Remaining z => e i.val) a) := by
    simp [curryLaurent, splitExponents]
  rw [curryPolynomial, RingHom.comp_apply, RingHom.comp_apply]
  change laurentToRat (coefficientsToField K z (curryLaurent K z (AddMonoidAlgebra.single e a))) = _
  rw [hcurry,
    coefficientsToField, AddMonoidAlgebra.mapRingHom_single,
    LaurentPolynomial.single_eq_C_mul_T]
  simp [laurentToRat]

theorem curry_variable_z :
    curryPolynomial K z (variablePolynomial K z) = RatFunc.X := by
  rw [variablePolynomial, curryPolynomial_single]
  have he : (fun i : Remaining z => (Pi.single z 1 : Fin N → ℤ) i.val) = 0 := by
    funext i; simp [i.property]
  rw [he]
  simp [← AddMonoidAlgebra.one_def]

theorem curry_variable_remaining (i : Remaining z) :
    curryPolynomial K z (variablePolynomial K i.val) = RatFunc.C (remainingVariable K z i) := by
  rw [variablePolynomial, curryPolynomial_single]
  have he : (fun j : Remaining z => (Pi.single i.val 1 : Fin N → ℤ) j.val) = Pi.single i 1 := by
    funext j
    simp only [Pi.single_apply]
    congr 1
    exact propext Subtype.ext_iff.symm
  rw [he]
  simp [remainingVariable, i.property, Ne.symm i.property]

def linearPole (i : Remaining z) : Polynomial (CoefficientField K z) :=
  Polynomial.X - Polynomial.C (remainingVariable K z i)

theorem linearPole_monic (i : Remaining z) : (linearPole K z i).Monic :=
  Polynomial.monic_X_sub_C _

theorem linearPole_pairwise_coprime :
    Pairwise (fun i j => IsCoprime (linearPole K z i) (linearPole K z j)) :=
  Polynomial.pairwise_coprime_X_sub_C (remainingVariable_injective K z)

theorem curry_pair_left (i : Remaining z) :
    curryPolynomial K z (pairPolynomial K z i.val) =
      algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z i) := by
  simp [pairPolynomial, map_sub, curry_variable_z, curry_variable_remaining,
    linearPole, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem curry_pair_right (i : Remaining z) :
    curryPolynomial K z (pairPolynomial K i.val z) =
      -(algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z i)) := by
  rw [pairPolynomial, map_sub, curry_variable_z, curry_variable_remaining]
  simp [linearPole, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

end LabelledRationalClearing.PairDifferenceLocalization
end

section
/- The partial-fraction premise is derived from the fixed-labelled Q itself.
Pairs not containing z contribute nonzero elements of the coefficient field;
pairs containing z contribute X-C(s), with the sign of their fixed orientation.
The numerator remains global throughout. -/
namespace LabelledRationalClearing.ActualClearingPartialFractions
open LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.PairDifferenceLocalization
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

abbrev LabelledPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

def pairPole (p : LabelledPair N) : Polynomial (CoefficientField K z) :=
  if h : p.val.1 = z then linearPole K z ⟨p.val.2, by simpa [← h] using p.property.ne.symm⟩
  else if h' : p.val.2 = z then linearPole K z ⟨p.val.1, h⟩
  else 1

def pairScalar (p : LabelledPair N) : CoefficientField K z :=
  if h : p.val.1 = z then 1
  else if h' : p.val.2 = z then -1
  else remainingVariable K z ⟨p.val.1, h⟩ - remainingVariable K z ⟨p.val.2, h'⟩

theorem pairScalar_ne_zero (p : LabelledPair N) : pairScalar K z p ≠ 0 := by
  unfold pairScalar
  split_ifs with h h'
  · exact one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero
  · apply sub_ne_zero.mpr
    intro he
    have hi := remainingVariable_injective K z he
    exact p.property.ne (congrArg Subtype.val hi)

theorem pairPole_monic (p : LabelledPair N) : (pairPole K z p).Monic := by
  unfold pairPole
  split_ifs <;> first | exact linearPole_monic K z _ | exact Polynomial.monic_one

theorem curry_pair (p : LabelledPair N) :
    curryPolynomial K z (pairPolynomial K p.val.1 p.val.2) =
      RatFunc.C (pairScalar K z p) *
        algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p) := by
  unfold pairScalar pairPole
  split_ifs with h h'
  · subst z
    rw [curry_pair_left K p.val.1 ⟨p.val.2, p.property.ne.symm⟩]
    simp
  · subst z
    rw [curry_pair_right K p.val.2 ⟨p.val.1, h⟩]
    simp
  · simp [pairPolynomial, map_sub, curry_variable_remaining K z ⟨p.val.1, h⟩,
      curry_variable_remaining K z ⟨p.val.2, h'⟩]

theorem pairPole_coprime : Pairwise (fun p q : LabelledPair N =>
    IsCoprime (pairPole K z p) (pairPole K z q)) := by
  intro p q hpq
  by_cases hp : p.val.1 = z
  · by_cases hq : q.val.1 = z
    · simp only [pairPole, dif_pos hp, dif_pos hq]
      apply linearPole_pairwise_coprime K z
      intro he
      apply hpq
      apply Subtype.ext
      exact Prod.ext (hp.trans hq.symm) (congrArg Subtype.val he)
    · by_cases hq' : q.val.2 = z
      · simp only [pairPole, dif_pos hp, dif_neg hq, dif_pos hq']
        apply linearPole_pairwise_coprime K z
        intro he
        have h := congrArg Subtype.val he
        change p.val.2 = q.val.1 at h
        have hplt := p.property
        have hqlt := q.property
        omega
      · simp only [pairPole, dif_pos hp, dif_neg hq, dif_neg hq']
        exact isCoprime_one_right
  · by_cases hp' : p.val.2 = z
    · by_cases hq : q.val.1 = z
      · simp only [pairPole, dif_neg hp, dif_pos hp', dif_pos hq]
        apply linearPole_pairwise_coprime K z
        intro he
        have h := congrArg Subtype.val he
        change p.val.1 = q.val.2 at h
        have hplt := p.property
        have hqlt := q.property
        omega
      · by_cases hq' : q.val.2 = z
        · simp only [pairPole, dif_neg hp, dif_pos hp', dif_neg hq, dif_pos hq']
          apply linearPole_pairwise_coprime K z
          intro he
          apply hpq
          apply Subtype.ext
          exact Prod.ext (congrArg Subtype.val he) (hp'.trans hq'.symm)
        · simp only [pairPole, dif_neg hp, dif_pos hp', dif_neg hq, dif_neg hq']
          exact isCoprime_one_right
    · simp only [pairPole, dif_neg hp, dif_neg hp']
      exact isCoprime_one_left

def clearingScalar (k : ℕ) : CoefficientField K z := ∏ p : LabelledPair N, pairScalar K z p ^ k

theorem clearingScalar_ne_zero (k : ℕ) : clearingScalar K z k ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (pairScalar_ne_zero K z p))

/-- Exact denominator factorization, with the original i<j orientation.
No z+x denominator or extra spectator collision can enter this localization. -/
theorem curry_clearingPolynomial (k : ℕ) :
    curryPolynomial K z (clearingPolynomial K N k) =
      RatFunc.C (clearingScalar K z k) *
        ∏ p : LabelledPair N,
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p)) ^ k := by
  classical
  have hprod : curryPolynomial K z (clearingPolynomial K N k) =
      ∏ p : LabelledPair N, curryPolynomial K z (pairPolynomial K p.val.1 p.val.2) ^ k := by
    rw [clearingPolynomial, map_prod]
    simp only [map_pow]
    exact Finset.prod_subtype (labelledPairs N) (by intro p; simp [labelledPairs]) _
  rw [hprod]
  simp only [curry_pair, mul_pow, Finset.prod_mul_distrib, clearingScalar, map_prod, map_pow]

/-- Actual finite numerator with nonnegative z-exponents is a univariate
polynomial over E after global currying. The support premise is exactly the
nonnegative numerator conclusion of the existing graded-correlator supplier. -/
theorem curry_numerator_polynomial (P : LabelledPolynomial K N)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ f : Polynomial (CoefficientField K z),
      curryPolynomial K z P = algebraMap _ (RatFunc (CoefficientField K z)) f := by
  classical
  let f : Polynomial (CoefficientField K z) := ∑ e ∈ P.coeff.support,
    Polynomial.monomial (e z).toNat
      (algebraMap (CoefficientPolynomial K z) (CoefficientField K z)
        (AddMonoidAlgebra.single (fun i : Remaining z => e i.val) (P.coeff e)))
  refine ⟨f, ?_⟩
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single P]
  simp only [Finsupp.sum, map_sum, curryPolynomial_single]
  simp only [f, map_sum, RatFunc.algebraMap_monomial]
  apply Finset.sum_congr rfl
  intro e he
  rw [← zpow_natCast, Int.toNat_of_nonneg (hP e he)]

/-- A derived algebraic normal form for the actual global P/Q. All denominator
premises come from Q, including the nonzero scalar orientation factor. -/
theorem actual_Q_partial_fractions (P : LabelledPolynomial K N) (k : ℕ)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ (q : Polynomial (CoefficientField K z))
      (rem : LabelledPair N → Fin k → Polynomial (CoefficientField K z)),
      (∀ p j, (rem p j).degree < (pairPole K z p).degree) ∧
      curryRational K z (algebraMap _ (CommonRational K N) P /
        algebraMap _ (CommonRational K N) (clearingPolynomial K N k)) =
      algebraMap _ (RatFunc (CoefficientField K z)) q +
        ∑ p, ∑ j, algebraMap _ (RatFunc (CoefficientField K z)) (rem p j) *
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p))⁻¹ ^ (j.val + 1) := by
  classical
  obtain ⟨f, hf⟩ := curry_numerator_polynomial K z P hP
  let f' : Polynomial (CoefficientField K z) := Polynomial.C (clearingScalar K z k)⁻¹ * f
  obtain ⟨q, rem, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := RatFunc (CoefficientField K z)) (s := Finset.univ) f'
    (fun p _ => pairPole_monic K z p)
    (fun p _ q _ hpq => pairPole_coprime K z hpq) (fun _ => k)
    (fun p _ => inv_mul_cancel₀ (by
      simpa only [map_zero] using
        (IsFractionRing.injective (Polynomial (CoefficientField K z))
          (RatFunc (CoefficientField K z))).ne (pairPole_monic K z p).ne_zero))
  refine ⟨q, rem, fun p j => hr p (Finset.mem_univ p) j, ?_⟩
  rw [curry_global_fraction, hf, curry_clearingPolynomial]
  rw [← he]
  simp only [f', map_mul, RatFunc.algebraMap_C, map_inv₀, div_eq_mul_inv,
    mul_inv_rev, ← Finset.prod_inv_distrib, inv_pow]
  ac_rfl

end LabelledRationalClearing.ActualClearingPartialFractions
end

section
/- All-integer weights retain the pair-difference localization. Negative
weights add poles only at z=x; positive weights modify only the numerator. -/
namespace LabelledRationalClearing.WeightedActualQ
open LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.PairDifferenceLocalization
open LabelledRationalClearing.ActualClearingPartialFractions
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N) (x : Remaining z)

def collisionPair : LabelledPair N :=
  if h : z < x.val then ⟨(z, x.val), h⟩
  else ⟨(x.val, z), lt_of_le_of_ne (le_of_not_gt h) x.property⟩

theorem collisionPair_pole : pairPole K z (collisionPair z x) = linearPole K z x := by
  unfold collisionPair
  split_ifs with h <;> simp [pairPole, x.property]

def weightedOrders (k : ℕ) (r : ℤ) (p : LabelledPair N) : ℕ :=
  k + if p = collisionPair z x then (-r).toNat else 0

theorem weighted_product (k : ℕ) (r : ℤ) :
    (∏ p : LabelledPair N, (algebraMap _ (RatFunc (CoefficientField K z))
      (pairPole K z p)) ^ weightedOrders z x k r p) =
    (∏ p : LabelledPair N, (algebraMap _ (RatFunc (CoefficientField K z))
      (pairPole K z p)) ^ k) *
      (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ (-r).toNat := by
  classical
  simp only [weightedOrders, pow_add, Finset.prod_mul_distrib]
  congr 1
  have hf (p : LabelledPair N) : (algebraMap _ (RatFunc (CoefficientField K z))
      (pairPole K z p)) ^ (if p = collisionPair z x then (-r).toNat else 0) =
      if p = collisionPair z x then (algebraMap _ (RatFunc (CoefficientField K z))
        (pairPole K z p)) ^ (-r).toNat else 1 := by split_ifs <;> simp
  simp only [hf, Fintype.prod_ite_eq', collisionPair_pole]

theorem integer_weight (r : ℤ) :
    (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ r =
      (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ r.toNat /
        (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ (-r).toNat := by
  have hn : (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (Polynomial (CoefficientField K z))
        (RatFunc (CoefficientField K z))).ne (linearPole_monic K z x).ne_zero
  have hr : (r.toNat : ℤ) - ((-r).toNat : ℤ) = r := by omega
  conv_lhs => rw [← hr, zpow_natCast_sub_natCast₀ hn]

def globalDiagonal : CommonRational K N := algebraMap _ _ (pairPolynomial K z x.val)

/-- The weighted actual global rational has a derived partial-fraction form
with precisely the allowed poles. This is not a collision equation premise. -/
theorem weighted_actual_Q_partial_fractions (P : LabelledPolynomial K N) (k : ℕ) (r : ℤ)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ (q : Polynomial (CoefficientField K z))
      (rem : (p : LabelledPair N) → Fin (weightedOrders z x k r p) → Polynomial (CoefficientField K z)),
      (∀ p j, (rem p j).degree < (pairPole K z p).degree) ∧
      curryRational K z (globalDiagonal K z x ^ r *
        (algebraMap _ (CommonRational K N) P /
          algebraMap _ (CommonRational K N) (clearingPolynomial K N k))) =
      algebraMap _ (RatFunc (CoefficientField K z)) q +
        ∑ p, ∑ j, algebraMap _ (RatFunc (CoefficientField K z)) (rem p j) *
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p))⁻¹ ^ (j.val + 1) := by
  classical
  obtain ⟨f, hf⟩ := curry_numerator_polynomial K z P hP
  let f' : Polynomial (CoefficientField K z) :=
    Polynomial.C (clearingScalar K z k)⁻¹ * f * linearPole K z x ^ r.toNat
  obtain ⟨q, rem, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := RatFunc (CoefficientField K z)) (s := Finset.univ) f'
    (fun p _ => pairPole_monic K z p)
    (fun p _ q _ hpq => pairPole_coprime K z hpq) (weightedOrders z x k r)
    (fun p _ => inv_mul_cancel₀ (by
      simpa only [map_zero] using
        (IsFractionRing.injective (Polynomial (CoefficientField K z))
          (RatFunc (CoefficientField K z))).ne (pairPole_monic K z p).ne_zero))
  refine ⟨q, rem, fun p j => hr p (Finset.mem_univ p) j, ?_⟩
  rw [← he]
  simp only [map_mul, map_zpow₀]
  rw [curry_global_fraction, hf, curry_clearingPolynomial]
  have hd : curryRational K z (globalDiagonal K z x) =
      algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x) := by
    simp only [globalDiagonal, curryRational, IsFractionRing.lift_algebraMap]
    exact curry_pair_left K z x
  rw [hd, integer_weight]
  simp only [inv_pow, Finset.prod_inv_distrib]
  rw [weighted_product]
  simp only [f', map_mul, map_pow, RatFunc.algebraMap_C, map_inv₀,
    div_eq_mul_inv, mul_inv_rev]
  ring

end LabelledRationalClearing.WeightedActualQ
end

section
namespace LabelledRationalClearing.WeightedNormalFormConstants
open LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.PairDifferenceLocalization
open LabelledRationalClearing.ActualClearingPartialFractions LabelledRationalClearing.WeightedActualQ
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

theorem pairPole_degree_le_one (p : LabelledPair N) : (pairPole K z p).degree ≤ 1 := by
  unfold pairPole
  split_ifs <;> simp [linearPole, Polynomial.degree_X_sub_C]

theorem remainder_constant (p : LabelledPair N) (f : Polynomial (CoefficientField K z))
    (hf : f.degree < (pairPole K z p).degree) : f = Polynomial.C (f.coeff 0) := by
  apply Polynomial.eq_C_of_degree_le_zero
  by_cases hz : f = 0
  · subst f; simp
  · have hd : f.degree < 1 := hf.trans_le (pairPole_degree_le_one K z p)
    rw [Polynomial.degree_eq_natDegree hz] at hd ⊢
    have hn : f.natDegree < 1 := by exact_mod_cast hd
    have hn0 : f.natDegree = 0 := by omega
    simp [hn0]

/-- The actual all-integer weighted P/Q normal form has scalar rational E
coefficients at the allowed poles. Remainder constancy is derived from their
linear degree; the normal form is not an assumption of the collision goal. -/
theorem weighted_actual_normal_form (x : Remaining z) (P : LabelledPolynomial K N)
    (k : ℕ) (r : ℤ) (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ (q : Polynomial (CoefficientField K z))
      (c : (p : LabelledPair N) → Fin (weightedOrders z x k r p) → CoefficientField K z),
      curryRational K z (globalDiagonal K z x ^ r *
        (algebraMap _ (CommonRational K N) P /
          algebraMap _ (CommonRational K N) (clearingPolynomial K N k))) =
      algebraMap _ (RatFunc (CoefficientField K z)) q +
        ∑ p, ∑ j, RatFunc.C (c p j) *
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p))⁻¹ ^ (j.val + 1) := by
  classical
  obtain ⟨q, rem, hr, he⟩ := weighted_actual_Q_partial_fractions K z x P k r hP
  refine ⟨q, fun p j => (rem p j).coeff 0, ?_⟩
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  rw [remainder_constant K z p (rem p j) (hr p j), RatFunc.algebraMap_C]

end LabelledRationalClearing.WeightedNormalFormConstants
end

section
namespace LabelledRationalClearing.GlobalRationalUncurry
open LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization CollisionRationalExpansions.OrderedRationalExpansion
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

def zeroExtend : (Remaining z → ℤ) →+ (Fin N → ℤ) where
  toFun e := (splitExponents z).symm (0, e)
  map_zero' := by change (splitExponents z).symm 0 = 0; exact map_zero _
  map_add' e f := by
    change (splitExponents z).symm ((0, e) + (0, f)) = _
    exact map_add _ _ _

lemma zeroExtend_injective : Function.Injective (zeroExtend z) := by
  intro e f h
  have he := congrArg (fun p => ((splitExponents z) p).2) h
  simpa only [zeroExtend, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddEquiv.apply_symm_apply] using he

def coefficientPolynomial : CoefficientPolynomial K z →+* CommonRational K N :=
  (algebraMap _ _).comp (AddMonoidAlgebra.mapDomainRingHom K (zeroExtend z))

def coefficient : CoefficientField K z →+* CommonRational K N :=
  IsFractionRing.lift (g := coefficientPolynomial K z)
    ((IsFractionRing.injective (LabelledPolynomial K N) (CommonRational K N)).comp
      (AddMonoidAlgebra.mapDomain_injective (zeroExtend_injective z)))

theorem curry_coefficient (h : CoefficientField K z) :
    curryRational K z (coefficient K z h) = RatFunc.C h := by
  have hm : (curryRational K z).comp (coefficient K z) = RatFunc.C := by
    apply IsFractionRing.ringHom_ext (A := CoefficientPolynomial K z)
    intro P
    simp only [RingHom.comp_apply, coefficient, coefficientPolynomial,
      curryRational, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
    induction P using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | single e a =>
      change curryPolynomial K z
        (AddMonoidAlgebra.mapDomain (zeroExtend z) (AddMonoidAlgebra.single e a)) = _
      rw [AddMonoidAlgebra.mapDomain_single, curryPolynomial_single]
      have hs := (splitExponents z).apply_symm_apply (0, e)
      have hz : zeroExtend z e z = 0 := congrArg Prod.fst hs
      have he : (fun i : Remaining z => zeroExtend z e i.val) = e := congrArg Prod.snd hs
      rw [hz, he, zpow_zero, mul_one]
  exact RingHom.congr_fun hm h

def globalZ : CommonRational K N := algebraMap _ _ (variablePolynomial K z)

theorem curry_globalZ : curryRational K z (globalZ K z) = RatFunc.X := by
  simp only [globalZ, curryRational, IsFractionRing.lift_algebraMap, curry_variable_z]

def polynomial : Polynomial (CoefficientField K z) →+* CommonRational K N :=
  Polynomial.eval₂RingHom (coefficient K z) (globalZ K z)

theorem polynomial_square :
    (curryRational K z).comp (polynomial K z) =
      algebraMap (Polynomial (CoefficientField K z)) (RatFunc (CoefficientField K z)) := by
  apply Polynomial.ringHom_ext
  · intro h
    simp [polynomial, RingHom.comp_apply, curry_coefficient, RatFunc.algebraMap_C]
  · simp [polynomial, RingHom.comp_apply, curry_globalZ, RatFunc.algebraMap_X]

lemma polynomial_injective : Function.Injective (polynomial K z) := by
  intro P Q h
  apply IsFractionRing.injective (Polynomial (CoefficientField K z)) (RatFunc (CoefficientField K z))
  rw [← polynomial_square]
  exact congrArg (curryRational K z) h

def uncurryRational : RatFunc (CoefficientField K z) →+* CommonRational K N :=
  IsFractionRing.lift (polynomial_injective K z)

theorem curry_uncurry (R : RatFunc (CoefficientField K z)) :
    curryRational K z (uncurryRational K z R) = R := by
  have hm : (curryRational K z).comp (uncurryRational K z) = RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := Polynomial (CoefficientField K z))
    intro P
    simp only [RingHom.comp_apply, uncurryRational, IsFractionRing.lift_algebraMap, RingHom.id_apply]
    exact RingHom.congr_fun (polynomial_square K z) P
  exact RingHom.congr_fun hm R

theorem uncurry_curry (R : CommonRational K N) :
    uncurryRational K z (curryRational K z R) = R := by
  apply (curryRational K z).injective
  rw [curry_uncurry]

/-- An actual equivalence of the original global rational field and RatFunc E;
the algebraic normal form can therefore be transported back into every true
full Hahn order without an assumed decomposition or spectator projection. -/
def curryEquiv : CommonRational K N ≃+* RatFunc (CoefficientField K z) :=
  RingEquiv.ofBijective (curryRational K z)
    ⟨(curryRational K z).injective, fun R => ⟨uncurryRational K z R, curry_uncurry K z R⟩⟩

end LabelledRationalClearing.GlobalRationalUncurry
end

end D5.S3.VertexAlgebra
