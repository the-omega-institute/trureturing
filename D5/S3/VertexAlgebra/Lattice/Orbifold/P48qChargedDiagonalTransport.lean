/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedDiagonalTransport
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transport of cleared radial products to the diagonal cover branch. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalAnnihilation

/-!
Transport of finite homogeneous slices of the cleared radial charged product
to the branch `x = y (1+t)^(1/3)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators LaurentSeries

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear)
open P48qTwistedChargeAction (lattice g Momentum)
open HahnSeries (single)
open PowerSeries (C coeff)
open ThirdTwistedContraction (clearedContractionNumerator clearedContractionNumerator_eval)
open private sum_orbitPairing from
  D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContractionReciprocity
open private diagonalXOverYUnit coe_diagonalXOverYUnit mapScalarToFock
  embed_unit_zpow embed_X_ne_zero from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
open private coverMonomial_mul_coeff coverEval_monomial creationProduct_coeff
  clearedOrderedProduct_single translation_normalForm orbitExponent groundScalar from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality

open private inverseCover translateOuter_C translateOuter_X translatedPolynomial_generator from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedOrderedProduct
open private diagonalInverseRatio fockToSeries fockToSeries_apply from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedDiagonalAnnihilation

attribute [local instance 2000] HahnSeries.instAlgebra

local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "R" => PowerSeries Fock
local notation "H" => HahnSeries.ofPowerSeries ℤ R
private def diagonalConstant : Fock →+* LaurentSeries R :=
  HahnSeries.C.comp PowerSeries.C
local notation "Xc" => (coverMonomial 1 0 (1 : Fock))
local notation "Yc" => (coverMonomial 0 1 (1 : Fock))

private def coverRatioPower (i : ℤ) : R :=
  mapScalarToFock (↑(diagonalXOverYUnit ^ i) : PowerSeries ℂ)

private theorem coverRatioPower_add (i j : ℤ) :
    coverRatioPower (i + j) = coverRatioPower i * coverRatioPower j := by
  simp only [coverRatioPower, zpow_add, Units.val_mul, map_mul]

private theorem coverRatioPower_nat (i : ℕ) :
    coverRatioPower (i : ℤ) = mapScalarToFock diagonalXOverY ^ i := by
  simp only [coverRatioPower, zpow_natCast, Units.val_pow_eq_pow_val, coe_diagonalXOverYUnit,
    map_pow]

/-- Regroup the radial coefficients with total cover degree `h`, weighting the
coefficient at `x^k y^(h-k)` by the `k`th signed power of `(1+t)^(1/3)`.
The transport laws below establish that the sums on the cleared product are finite. -/
def diagonalCoverReadout (A : CoverSeries Fock) (h : ℤ) : R :=
  ∑ᶠ k : ℤ, (C ((A.coeff (h - k)).coeff k)) * coverRatioPower k

private def finiteCoverSlices (A : CoverSeries Fock) : Prop :=
  ∀ h : ℤ, Function.HasFiniteSupport (fun k : ℤ => (A.coeff (h - k)).coeff k)

private theorem readout_support {A : CoverSeries Fock} (hA : finiteCoverSlices A) (h : ℤ) :
    Function.HasFiniteSupport
      (fun k : ℤ => C ((A.coeff (h - k)).coeff k) * coverRatioPower k) :=
  (hA h).subset fun k hk hz => hk (by simp [hz])

private theorem finiteCoverSlices_add {A B : CoverSeries Fock}
    (hA : finiteCoverSlices A) (hB : finiteCoverSlices B) : finiteCoverSlices (A + B) := by
  intro h
  refine ((hA h).union (hB h)).subset ?_
  intro k hk
  by_contra hn
  apply hk
  change k ∉ Function.support (fun k => (A.coeff (h - k)).coeff k) ∪
    Function.support (fun k => (B.coeff (h - k)).coeff k) at hn
  rw [Set.mem_union, not_or] at hn
  change ((A + B).coeff (h - k)).coeff k = 0
  rw [HahnSeries.coeff_add, HahnSeries.coeff_add,
    Function.notMem_support.mp hn.1, Function.notMem_support.mp hn.2, add_zero]

private theorem diagonalCoverReadout_add {A B : CoverSeries Fock}
    (hA : finiteCoverSlices A) (hB : finiteCoverSlices B) (h : ℤ) :
    diagonalCoverReadout (A + B) h = diagonalCoverReadout A h + diagonalCoverReadout B h := by
  simp only [diagonalCoverReadout, HahnSeries.coeff_add, map_add, add_mul]
  exact finsum_add_distrib (readout_support hA h) (readout_support hB h)

private theorem finiteCoverSlices_monomial_mul {A : CoverSeries Fock}
    (hA : finiteCoverSlices A) (i j : ℤ) (c : Fock) :
    finiteCoverSlices (coverMonomial i j c * A) := by
  intro h
  have he : Function.Injective (fun k : ℤ => k - i) := fun x y hxy => by
    change x - i = y - i at hxy
    omega
  have hshift := Set.Finite.preimage he.injOn (hA (h - (i + j)))
  refine hshift.subset ?_
  intro k hk hz
  apply hk
  change ((coverMonomial i j c * A).coeff (h - k)).coeff k = 0
  change (A.coeff (h - (i + j) - (k - i))).coeff (k - i) = 0 at hz
  rw [coverMonomial_mul_coeff,
    show h - k - j = h - (i + j) - (k - i) by omega, hz, mul_zero]

private theorem diagonalCoverReadout_monomial_mul {A : CoverSeries Fock}
    (hA : finiteCoverSlices A) (i j : ℤ) (c : Fock) (h : ℤ) :
    diagonalCoverReadout (coverMonomial i j c * A) h =
      C c * coverRatioPower i * diagonalCoverReadout A (h - (i + j)) := by
  unfold diagonalCoverReadout
  rw [mul_finsum' _ _ (readout_support hA (h - (i + j)))]
  let e : ℤ ≃ ℤ := Equiv.addRight (-i)
  apply finsum_eq_of_bijective e e.bijective
  intro k
  change C (((coverMonomial i j c * A).coeff (h - k)).coeff k) * coverRatioPower k =
    C c * coverRatioPower i *
      (C ((A.coeff (h - (i + j) - (k + -i))).coeff (k + -i)) * coverRatioPower (k + -i))
  rw [coverMonomial_mul_coeff, show h - k - j = h - (i + j) - (k + -i) by omega,
    show k - i = k + -i by omega, map_mul,
    show coverRatioPower k = coverRatioPower i * coverRatioPower (k + -i) by
      rw [← coverRatioPower_add, show i + (k + -i) = k by omega]]
  ac_rfl

private theorem finiteCoverSlices_sum {I : Type*} (s : Finset I) (A : I → CoverSeries Fock)
    (hA : ∀ i ∈ s, finiteCoverSlices (A i)) : finiteCoverSlices (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteCoverSlices, Function.HasFiniteSupport, Function.support]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact finiteCoverSlices_add (hA i (Finset.mem_insert_self _ _))
      (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

private theorem diagonalCoverReadout_sum {I : Type*} (s : Finset I) (A : I → CoverSeries Fock)
    (hA : ∀ i ∈ s, finiteCoverSlices (A i)) (h : ℤ) :
    diagonalCoverReadout (∑ i ∈ s, A i) h = ∑ i ∈ s, diagonalCoverReadout (A i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [diagonalCoverReadout]
  | insert i s hi ih =>
    have hs (j : I) (hj : j ∈ s) := hA j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      diagonalCoverReadout_add (hA i (Finset.mem_insert_self _ _))
        (finiteCoverSlices_sum s A hs), ih hs]

private theorem coverEval_mul_sum {S : Type*} [CommRing S] (f : S →+* Fock)
    (v w : ℤ × ℤ) (Q : MvPolynomial (Fin 2) S) (A : CoverSeries Fock) :
    coverEval f v w Q * A = ∑ d ∈ Q.support,
      coverMonomial ((d 0 : ℤ) * v.1 + (d 1 : ℤ) * w.1)
        ((d 0 : ℤ) * v.2 + (d 1 : ℤ) * w.2) (f (Q.coeff d)) * A := by
  conv_lhs => rw [Q.as_sum]
  simp only [map_sum, Finset.sum_mul, coverEval_monomial]

private theorem finiteCoverSlices_coverEval_mul {S : Type*} [CommRing S] (f : S →+* Fock)
    (v w : ℤ × ℤ) (Q : MvPolynomial (Fin 2) S) {A : CoverSeries Fock}
    (hA : finiteCoverSlices A) : finiteCoverSlices (coverEval f v w Q * A) := by
  rw [coverEval_mul_sum]
  exact finiteCoverSlices_sum _ _ fun _ _ => finiteCoverSlices_monomial_mul hA _ _ _

def diagonalMonomial (i j : ℤ) (c : Fock) : LaurentSeries R :=
  single (i + j) (C c * coverRatioPower i)

private theorem diagonalMonomial_mul (i j k l : ℤ) (c d : Fock) :
    diagonalMonomial i j c * diagonalMonomial k l d =
      diagonalMonomial (i + k) (j + l) (c * d) := by
  unfold diagonalMonomial
  rw [HahnSeries.single_mul_single, show i + j + (k + l) = i + k + (j + l) by omega,
    map_mul (PowerSeries.C : Fock →+* R), coverRatioPower_add]
  apply congrArg (single (i + k + (j + l)))
  ac_rfl

private theorem diagonalMonomial_pow (i j : ℤ) (n : ℕ) :
    diagonalMonomial i j 1 ^ n = diagonalMonomial ((n : ℤ) * i) ((n : ℤ) * j) 1 := by
  induction n with
  | zero => simp [diagonalMonomial, coverRatioPower]
  | succ n ih =>
    rw [pow_succ, ih, diagonalMonomial_mul, mul_one, Nat.cast_succ, add_mul, add_mul, one_mul,
      one_mul]

def diagonalCoverEval {S : Type*} [CommRing S] (f : S →+* Fock)
    (v w : ℤ × ℤ) : MvPolynomial (Fin 2) S →+* LaurentSeries R :=
  MvPolynomial.eval₂Hom (diagonalConstant.comp f)
    ![diagonalMonomial v.1 v.2 1, diagonalMonomial w.1 w.2 1]

private theorem diagonalCoverEval_monomial {S : Type*} [CommRing S] (f : S →+* Fock)
    (v w : ℤ × ℤ) (d : Fin 2 →₀ ℕ) (c : S) :
    diagonalCoverEval f v w (MvPolynomial.monomial d c) =
      diagonalMonomial ((d 0 : ℤ) * v.1 + (d 1 : ℤ) * w.1)
        ((d 0 : ℤ) * v.2 + (d 1 : ℤ) * w.2) (f c) := by
  rw [diagonalCoverEval, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, diagonalMonomial_pow, diagonalMonomial_mul]
  have hc : (diagonalConstant.comp f) c = diagonalMonomial 0 0 (f c) := by
    simp [diagonalConstant, diagonalMonomial, coverRatioPower, HahnSeries.C_apply]
  rw [hc, diagonalMonomial_mul]
  simp

private theorem diagonalCoverReadout_coverEval_mul {S : Type*} [CommRing S] (f : S →+* Fock)
    (v w : ℤ × ℤ) (Q : MvPolynomial (Fin 2) S) {A : CoverSeries Fock} {T : LaurentSeries R}
    (hA : finiteCoverSlices A) (hT : ∀ h : ℤ, diagonalCoverReadout A h = T.coeff h) (h : ℤ) :
    diagonalCoverReadout (coverEval f v w Q * A) h =
      (diagonalCoverEval f v w Q * T).coeff h := by
  rw [coverEval_mul_sum, diagonalCoverReadout_sum _ _
    (fun d _ => finiteCoverSlices_monomial_mul hA _ _ _) h]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, Finset.sum_mul, HahnSeries.coeff_sum, diagonalCoverEval_monomial,
    diagonalCoverReadout_monomial_mul hA, hT, diagonalMonomial, HahnSeries.coeff_single_mul]

private theorem finiteCoverSlices_creationProduct (B : FixedDualBases) (a b : Charge lattice) :
    finiteCoverSlices (creationProduct B a b) := by
  intro h
  refine (Finset.Icc (0 : ℤ) h).finite_toSet.subset ?_
  intro k hk
  change k ∈ Finset.Icc (0 : ℤ) h
  rw [Finset.mem_Icc]
  change ((creationProduct B a b).coeff (h - k)).coeff k ≠ 0 at hk
  rw [creationProduct_coeff] at hk
  constructor
  · exact le_of_not_gt fun hn => hk (by simp [creationCoeff, hn])
  · exact le_of_not_gt fun hn => hk (by simp [creationCoeff, show h - k < 0 by omega])

def diagonalCreationProduct (B : FixedDualBases) (a b : Charge lattice) :
    LaurentSeries R :=
  H (PowerSeries.rescale (mapScalarToFock diagonalXOverY)
    ((creationExponential B a).map C)) * H ((creationExponential B b).map C)

private theorem creationSeries_coeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    (H ((creationExponential B a).map C)).coeff k = C (creationCoeff B a k) := by
  rw [PowerSeries.coeff_coe, creationCoeff]
  split_ifs with hk
  · rw [map_zero]
  · rw [PowerSeries.coeff_map, show k.natAbs = k.toNat by omega]

private theorem scaledCreationSeries_coeff (B : FixedDualBases) (a : Charge lattice) (k : ℤ) :
    (H (PowerSeries.rescale (mapScalarToFock diagonalXOverY)
      ((creationExponential B a).map C))).coeff k =
      C (creationCoeff B a k) * coverRatioPower k := by
  cases k with
  | negSucc k => simp [PowerSeries.coeff_coe, creationCoeff, Int.negSucc_lt_zero]
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_rescale,
      PowerSeries.coeff_map, coverRatioPower_nat, creationCoeff]
    exact mul_comm _ _

private theorem diagonalCoverReadout_creationProduct (B : FixedDualBases) (a b : Charge lattice)
    (h : ℤ) : diagonalCoverReadout (creationProduct B a b) h =
      (diagonalCreationProduct B a b).coeff h := by
  unfold diagonalCoverReadout diagonalCreationProduct
  let S := H (PowerSeries.rescale (mapScalarToFock diagonalXOverY)
    ((creationExponential B a).map C))
  let T := H ((creationExponential B b).map C)
  have he (k l : ℤ) :
      C (((creationProduct B a b).coeff l).coeff k) * coverRatioPower k =
      S.coeff k * T.coeff l := by
    rw [creationProduct_coeff, map_mul, scaledCreationSeries_coeff, creationSeries_coeff]
    ac_rfl
  simp_rw [he]
  change (∑ᶠ k, S.coeff k * T.coeff (h - k)) = (S * T).coeff h
  rw [HahnSeries.coeff_mul]
  let F := Finset.antidiagonal S.isPWO_support T.isPWO_support h
  have hsupport : Function.support (fun k : ℤ => S.coeff k * T.coeff (h - k)) ⊆
      (F.image Prod.fst : Set ℤ) := by
    intro k hk
    change k ∈ F.image Prod.fst
    change S.coeff k * T.coeff (h - k) ≠ 0 at hk
    refine Finset.mem_image.mpr ⟨(k, h - k), Finset.mem_antidiagonal.mpr ?_, rfl⟩
    exact ⟨left_ne_zero_of_mul hk, right_ne_zero_of_mul hk, by omega⟩
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ij hij
    have hij' := (Finset.mem_antidiagonal.mp hij).2.2
    rw [show h - ij.1 = ij.2 by omega]
  · intro i hi j hj hij
    have hi' := (Finset.mem_antidiagonal.mp hi).2.2
    have hj' := (Finset.mem_antidiagonal.mp hj).2.2
    exact Prod.ext hij (by omega)

/-- A fixed total degree of the actual cleared radial product receives only
finitely many contributions, including on arbitrary input Fock polynomials. -/
theorem clearedOrderedChargedProduct_finiteSlice (B : FixedDualBases) (a b : Charge lattice)
    (p q : Momentum) (P : Fock) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) (h : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ =>
      ((((Xc ^ 3 - Yc ^ 3) ^ N *
        orderedChargedProduct B a b (Finsupp.single p P) q).coeff (h - k)).coeff k)) := by
  classical
  rw [clearedOrderedProduct_single B a b p q P N hN]
  split_ifs
  · rw [translation_normalForm,
      show ∀ (m n s t : CoverSeries Fock), m * n * s * t = m * (n * (t * s)) by
        intros; ac_rfl]
    exact finiteCoverSlices_monomial_mul
      (finiteCoverSlices_coverEval_mul _ _ _ _
        (finiteCoverSlices_coverEval_mul _ _ _ _ (finiteCoverSlices_creationProduct B a b)))
      _ _ _ h
  · simp [Function.HasFiniteSupport, Function.support]

/-- Diagonal substitution of the actual radial numerator and both oscillator
factors. The finite polynomial evaluations retain the momentum degrees and
use the inverse ratio on the first annihilation variable. -/
theorem clearedOrderedChargedProduct_diagonalFactors (B : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) (P : Fock) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) (h : ℤ) :
    diagonalCoverReadout ((Xc ^ 3 - Yc ^ 3) ^ N *
      orderedChargedProduct B a b (Finsupp.single p P) (shift (a + b) p)) h =
      (diagonalMonomial (momentumExponent a p) (momentumExponent b p) 1 *
        (diagonalCoverEval (algebraMap ℂ Fock) (1, 0) (0, 1)
          (chargedLocalityNumerator a b p N) *
        (diagonalCoverEval (RingHom.id Fock) (-1, 0) (0, -1) (finiteChargedTranslation B a b P) *
          diagonalCreationProduct B a b))).coeff h := by
  classical
  rw [clearedOrderedProduct_single B a b p _ P N hN, ite_eq_left rfl, translation_normalForm,
    show ∀ (m n s t : CoverSeries Fock), m * n * s * t = m * (n * (t * s)) by
      intros; ac_rfl]
  have hcreation := finiteCoverSlices_creationProduct B a b
  have htranslation := finiteCoverSlices_coverEval_mul (RingHom.id Fock) (-1, 0) (0, -1)
    (finiteChargedTranslation B a b P) hcreation
  have hnumerator := finiteCoverSlices_coverEval_mul (algebraMap ℂ Fock) (1, 0) (0, 1)
    (chargedLocalityNumerator a b p N) htranslation
  rw [diagonalCoverReadout_monomial_mul hnumerator, diagonalCoverReadout_coverEval_mul _ _ _ _
    htranslation (fun h' => diagonalCoverReadout_coverEval_mul _ _ _ _ hcreation
      (diagonalCoverReadout_creationProduct B a b) h')]
  rw [diagonalMonomial, HahnSeries.coeff_single_mul]

local notation "ζ" => ThirdTwistedChargeCocycle.zeta
local notation "X" => (PowerSeries.X : PowerSeries ℂ)
local notation "ι" => HahnSeries.ofPowerSeries ℤ ℂ

private theorem diagonalCoverEval_numerator (a b : Charge lattice) (p : Momentum) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    diagonalCoverEval (algebraMap ℂ Fock) (1, 0) (0, 1)
      (chargedLocalityNumerator a b p N) =
      single (3 * (N : ℤ) + ∑ j ∈ Finset.range 3, orbitExponent a b j)
        (mapScalarToFock (PowerSeries.C (groundScalar a b p) *
          MvPolynomial.eval₂Hom PowerSeries.C ![diagonalXOverY, 1]
            (clearedContractionNumerator lattice g ζ a b N))) := by
  let f := diagonalConstant.comp (algebraMap ℂ Fock)
  have hscalar (c : ℂ) : f c = single 0 (mapScalarToFock (PowerSeries.C c)) := by
    simp [f, diagonalConstant, HahnSeries.C_apply, mapScalarToFock]
  have hr (j : ℕ) :
      diagonalMonomial 1 0 1 - f (↑(ζ ^ j) : ℂ) * diagonalMonomial 0 1 1 =
        single 1 (mapScalarToFock (diagonalXOverY - PowerSeries.C (↑(ζ ^ j) : ℂ))) := by
    rw [hscalar, diagonalMonomial, diagonalMonomial, HahnSeries.single_mul_single,
      add_zero, zero_add, zero_add, map_sub, ← HahnSeries.single_sub]
    simp [coverRatioPower, coe_diagonalXOverYUnit]
  have hnonneg (j : ℕ) (hj : j < 3) :=
    Int.toNat_of_nonneg (hN j (Finset.mem_range.mpr hj))
  simp only [chargedLocalityNumerator, diagonalCoverEval, map_mul, MvPolynomial.eval₂Hom_C,
    clearedContractionNumerator_eval]
  change f _ * (∏ j ∈ Finset.range 3,
    (diagonalMonomial 1 0 1 - f (↑(ζ ^ j) : ℂ) * diagonalMonomial 0 1 1) ^
      ((N : ℤ) + orbitExponent a b j).toNat) = _
  simp_rw [hr]
  simp only [hscalar, HahnSeries.single_pow, Finset.prod_range_succ, Finset.prod_range_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, one_mul,
    map_mul, map_pow, mul_one, HahnSeries.single_mul_single,
    nsmul_eq_mul, mul_one, zero_add,
    hnonneg 0 (by decide), hnonneg 1 (by decide), hnonneg 2 (by decide)]
  rw [show ((N : ℤ) + orbitExponent a b 0) + ((N : ℤ) + orbitExponent a b 1) +
    ((N : ℤ) + orbitExponent a b 2) =
      3 * (N : ℤ) + (orbitExponent a b 0 + orbitExponent a b 1 + orbitExponent a b 2) by ring]

private theorem normalizedScalarNumerator (a b : Charge lattice) (p : Momentum) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    (↑(diagonalXOverYUnit ^ momentumExponent a p) : PowerSeries ℂ) *
      (PowerSeries.C (groundScalar a b p) *
        MvPolynomial.eval₂Hom PowerSeries.C ![diagonalXOverY, 1]
          (clearedContractionNumerator lattice g ζ a b N)) =
      X ^ ((N : ℤ) + bilinear lattice a b).toNat * groundDiagonalScalar a b p := by
  have he : 0 ≤ (N : ℤ) + bilinear lattice a b := hN 0 (by decide)
  let s := ∑ j ∈ Finset.range 3, orbitExponent a b j
  have hs : momentumExponent a p + s = momentumExponent a (shift b p) := by
    dsimp [s]
    rw [sum_orbitPairing lattice g a b, momentumExponent_shift]
  have hne : ι diagonalXOverY ≠ 0 := by
    intro hz
    have hu := congrArg ι (diagonalXOverY_mul_q)
    rw [map_mul, hz, zero_mul, map_one] at hu
    exact zero_ne_one hu
  have hk : (ι diagonalXOverY) ^ momentumExponent a p * (ι diagonalXOverY) ^ s =
      (ι diagonalXOverY) ^ momentumExponent a (shift b p) := by
    rw [← zpow_add₀ hne, hs]
  have hclear := diagonalChargedContraction_clear a b N hN
  rw [diagonalChargedContraction_factor] at hclear
  have hx : (ι X) ^ ((N : ℤ) + bilinear lattice a b).toNat =
      (ι X) ^ N * (ι X) ^ bilinear lattice a b := by
    rw [← zpow_natCast, Int.toNat_of_nonneg he, zpow_add₀ embed_X_ne_zero, zpow_natCast]
  have harg : (fun i : Fin 2 => ι (![diagonalXOverY, 1] i)) = ![ι diagonalXOverY, 1] := by
    funext i
    fin_cases i <;> simp
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  rw [map_mul, map_mul, map_mul, embed_unit_zpow, coe_diagonalXOverYUnit,
    MvPolynomial.map_eval₂Hom, harg, groundDiagonalScalar_eq, diagonalChargedContraction_regularize,
    map_pow, hx, ← hclear]
  change _ = _ * (ι (PowerSeries.C (groundScalar a b p)) *
    (ι diagonalXOverY) ^ momentumExponent a (shift b p) * _)
  rw [← hk]
  change (ι diagonalXOverY) ^ momentumExponent a p *
      (ι (PowerSeries.C (groundScalar a b p)) *
        ((ι X) ^ N * ((ι diagonalXOverY) ^ s *
          ((ι X) ^ bilinear lattice a b * ι (regularChargedContraction a b : PowerSeries ℂ))))) =
    _
  ac_rfl

private theorem normalizedDiagonalNumerator (a b : Charge lattice) (p : Momentum) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) :
    diagonalMonomial (momentumExponent a p) (momentumExponent b p) 1 *
      diagonalCoverEval (algebraMap ℂ Fock) (1, 0) (0, 1) (chargedLocalityNumerator a b p N) =
      single (momentumExponent (a + b) p + 3 * ((N : ℤ) + bilinear lattice a b))
        (mapScalarToFock (X ^ ((N : ℤ) + bilinear lattice a b).toNat *
          groundDiagonalScalar a b p)) := by
  let s := ∑ j ∈ Finset.range 3, orbitExponent a b j
  have hs : momentumExponent a p + s = momentumExponent a (shift b p) := by
    dsimp [s]
    rw [sum_orbitPairing lattice g a b, momentumExponent_shift]
  have hr : momentumExponent a p + momentumExponent b p + (3 * (N : ℤ) + s) =
      momentumExponent (a + b) p + 3 * ((N : ℤ) + bilinear lattice a b) := by
    have := momentumExponent_ordered a b p
    omega
  rw [diagonalCoverEval_numerator a b p N hN, diagonalMonomial, HahnSeries.single_mul_single]
  change single (_ + _ + (3 * (N : ℤ) + s)) (C 1 * coverRatioPower _ * _) = _
  rw [hr, map_one PowerSeries.C, one_mul, coverRatioPower, ← map_mul mapScalarToFock,
    normalizedScalarNumerator a b p N hN]

private theorem ratioPower_neg_one :
    coverRatioPower (-1) = diagonalInverseRatio := by
  unfold coverRatioPower diagonalInverseRatio mapScalarToFock
  congr 1
  let q := P48qTwistedHeisenberg.diagonalCoverRatio
  have h : diagonalXOverY * q = 1 := diagonalXOverY_mul_q
  rw [← coe_diagonalXOverYUnit] at h
  have he : (↑(diagonalXOverYUnit ^ (-1 : ℤ)) : PowerSeries ℂ) =
      (↑diagonalXOverYUnit⁻¹ : PowerSeries ℂ) := by simp
  rw [he]
  calc
    _ = (↑diagonalXOverYUnit⁻¹ : PowerSeries ℂ) * (↑diagonalXOverYUnit * q) := by
      rw [h, mul_one]
    _ = q := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

private theorem diagonalCoverEval_translation (B : FixedDualBases) (a b : Charge lattice)
    (P : Fock) :
    diagonalCoverEval (RingHom.id Fock) (-1, 0) (0, -1) (finiteChargedTranslation B a b P) =
      inverseCover ℂ
        (diagonalInverseCoverPolynomial (translateOuter B b (translatedPolynomial B a P))) := by
  let D : Polynomial (Polynomial Fock) →ₐ[ℂ] LaurentSeries R :=
    (inverseCover ℂ).comp diagonalInverseCoverPolynomial
  let lhs := (diagonalCoverEval (RingHom.id Fock) (-1, 0) (0, -1)).comp
    (finiteChargedTranslation B a b).toRingHom
  let rhs := (D.comp ((translateOuter B b).comp (translatedPolynomial B a))).toRingHom
  change lhs P = rhs P
  suffices h : lhs = rhs from DFunLike.congr_fun h P
  have hn (v : R) : inverseCover ℂ (Polynomial.C v) = single 0 v := by
    simp only [inverseCover, Polynomial.aevalTower_C, AlgHom.coe_mk, HahnSeries.C_apply]
  have hx : inverseCover ℂ (Polynomial.X : Polynomial R) = single (-1) 1 := by
    simp only [inverseCover, Polynomial.aevalTower_X]
  have hP (v : Polynomial Fock) :
      D (Polynomial.C v : Polynomial (Polynomial Fock)) =
        inverseCover ℂ (Polynomial.aevalTower (Polynomial.CAlgHom.comp fockToSeries)
          (Polynomial.C diagonalInverseRatio * Polynomial.X) v) := by
    simp only [D, AlgHom.comp_apply, diagonalInverseCoverPolynomial, Polynomial.aevalTower_C]
  have hC (v : Fock) : D (Polynomial.C (Polynomial.C v)) = single 0 (C v) := by
    rw [hP, Polynomial.aevalTower_C]
    simpa only [AlgHom.comp_apply, Polynomial.CAlgHom_apply, fockToSeries_apply] using hn (C v)
  have hI : D (Polynomial.C (Polynomial.X : Polynomial Fock)) = diagonalMonomial (-1) 0 1 := by
    rw [hP, Polynomial.aevalTower_X, map_mul, hn, hx, HahnSeries.single_mul_single]
    simp [diagonalMonomial, ratioPower_neg_one]
  have hO : D (Polynomial.X : Polynomial (Polynomial Fock)) = diagonalMonomial 0 (-1) 1 := by
    simp [D, diagonalInverseCoverPolynomial, Polynomial.aevalTower_X, hx, diagonalMonomial,
      coverRatioPower]
  have hdiag (v : Fock) :
      (diagonalConstant.comp (RingHom.id Fock)) v = single 0 (C v) := by
    simp [diagonalConstant, HahnSeries.C_apply]
  have htranslate (c : ℂ) :
      D (translateOuter B b (Polynomial.C (algebraMap ℂ Fock c))) =
        D (Polynomial.C (Polynomial.C (algebraMap ℂ Fock c))) := by
    rw [translateOuter_C]
    have hc := (translatedPolynomial B b).commutes c
    change translatedPolynomial B b (algebraMap ℂ Fock c) =
      Polynomial.C (algebraMap ℂ Fock c) at hc
    simp only [hc, Polynomial.coe_mapAlgHom, Polynomial.map_C, AlgHom.coe_toRingHom,
      Polynomial.CAlgHom_apply]
  apply MvPolynomial.ringHom_ext
  · intro c
    change (diagonalCoverEval (RingHom.id Fock) (-1, 0) (0, -1))
      (finiteChargedTranslation B a b (MvPolynomial.C c)) =
      D (translateOuter B b (translatedPolynomial B a (MvPolynomial.C c)))
    rw [show finiteChargedTranslation B a b (MvPolynomial.C c) =
        MvPolynomial.C (MvPolynomial.C c) from MvPolynomial.aeval_C _ _,
      show translatedPolynomial B a (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) by
          exact (translatedPolynomial B a).commutes c]
    change _ = D (translateOuter B b (Polynomial.C (algebraMap ℂ Fock c)))
    rw [diagonalCoverEval, MvPolynomial.eval₂Hom_C, hdiag, htranslate, hC]
    rfl
  · intro j
    change (diagonalCoverEval (RingHom.id Fock) (-1, 0) (0, -1))
      (finiteChargedTranslation B a b (MvPolynomial.X j)) =
      D (translateOuter B b (translatedPolynomial B a (MvPolynomial.X j)))
    rw [translatedPolynomial_generator, map_sub, map_mul, map_pow, translateOuter_X, map_sub,
      map_mul, map_pow, hI]
    rw [htranslate, hC, translateOuter_C, translatedPolynomial_generator]
    simp only [Polynomial.coe_mapAlgHom, Polynomial.map_C, Polynomial.map_X, AlgHom.coe_toRingHom,
      Polynomial.CAlgHom_apply, map_sub, map_mul, map_pow, hC, hO,
      finiteChargedTranslation, MvPolynomial.aeval_X, diagonalCoverEval,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Matrix.cons_val_zero,
      Matrix.cons_val_one, hdiag, Algebra.smul_def, mul_one]
    ring

/-- Cleared radial product on the shifted momentum line, in the physical
collision coordinates. Here the regular diagonal series is multiplied by
`t^(N+⟨a,b⟩)` and shifted by `momentumExponent + 3(N+⟨a,b⟩)`
in the right cover variable. -/
theorem clearedOrderedChargedProduct_diagonalRegular (B : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) (P : Fock) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + orbitExponent a b j) (h : ℤ) :
    diagonalCoverReadout ((Xc ^ 3 - Yc ^ 3) ^ N *
      orderedChargedProduct B a b (Finsupp.single p P) (shift (a + b) p)) h =
      (mapScalarToFock (X ^ ((N : ℤ) + bilinear lattice a b).toNat)) *
        (chargedDiagonalRegular B a b p P).coeff
          (h - (momentumExponent (a + b) p + 3 * ((N : ℤ) + bilinear lattice a b))) := by
  rw [clearedOrderedChargedProduct_diagonalFactors B a b p P N hN,
    ← mul_assoc, normalizedDiagonalNumerator a b p N hN, HahnSeries.coeff_single_mul,
    diagonalCoverEval_translation, chargedDiagonalRegular, groundDiagonalRegular,
    diagonalCreationProduct, map_mul, map_mul, map_mul, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_apply]
  simp only [mul_assoc, mul_comm (inverseCover ℂ _)]
  rw [HahnSeries.coeff_single_zero_mul, ← mul_assoc]

#print axioms clearedOrderedChargedProduct_finiteSlice
#print axioms clearedOrderedChargedProduct_diagonalFactors
#print axioms clearedOrderedChargedProduct_diagonalRegular

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
