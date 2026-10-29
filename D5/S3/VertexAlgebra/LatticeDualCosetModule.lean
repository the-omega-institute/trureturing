/- GID: D5/S3/VertexAlgebra/LatticeDualCosetModule
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetModule
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dual-coset Fock sectors inside an auxiliary even lattice. -/

import D5.S3.VertexAlgebra.LatticeActualStateDerivative
import Mathlib.Algebra.MvPolynomial.Rename

/-!
The lattice fields and normal-product conventions are those of the original
LatticeGeneratingFieldLocality and LatticeAllStateField sources. In particular
the lattice cocycle retains the half-diagonal term. The auxiliary lattice
realization does not require positivity or an inverse Gram matrix.
Bakalov--Kac, math/0402315v1, section 4.1, supplies the lattice-field construction.
Imported residue kernels retain their Scott Carnahan Apache-2.0 attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeDualCosetModule

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeAllStateField LatticeSugawaraConformal FieldNormalProduct
open MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

/-- The old Gram matrix, the integral dual pairing, and an isotropic last vector. -/
def auxiliary (D : LatticeData) (β : Charge D) : LatticeData where
  rank := D.rank + 1
  G := Fin.lastCases (Fin.lastCases 0 β)
    (fun i => Fin.lastCases (β i) (D.G i))
  symmetric i j := by
    induction i using Fin.lastCases <;> induction j using Fin.lastCases
    all_goals simp [D.symmetric]
  even_diagonal i := by
    induction i using Fin.lastCases
    · simp
    · simpa using D.even_diagonal _

variable (D : LatticeData) (β : Charge D)

def liftCharge (t : ℤ) (n : Charge D) : Charge (auxiliary D β) :=
  Fin.lastCases t n

def oldCharge (n : Charge (auxiliary D β)) : Charge D := fun i => n i.castSucc

def liftIndex (x : Index D) : Index (auxiliary D β) := (x.1.castSucc, x.2)

private theorem liftIndex_injective : Function.Injective (liftIndex D β) := by
  intro x y h
  exact Prod.ext (Fin.castSucc_injective _ (congrArg Prod.fst h)) (congrArg Prod.snd h)

def polynomialInjection : Oscillator D →ₐ[ℂ] Oscillator (auxiliary D β) :=
  rename (liftIndex D β)

def polynomialRetraction : Oscillator (auxiliary D β) →ₐ[ℂ] Oscillator D :=
  killCompl (liftIndex_injective D β)

private theorem retract_polynomial (p : Oscillator D) :
    polynomialRetraction D β (polynomialInjection D β p) = p :=
  killCompl_rename_app (liftIndex_injective D β) p

def injection (t : ℤ) : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) :=
  Finsupp.lsum ℂ (fun n =>
    (Finsupp.lsingle (liftCharge D β t n)).comp (polynomialInjection D β).toLinearMap)

def retraction (t : ℤ) : Carrier (auxiliary D β) →ₗ[ℂ] Carrier D :=
  Finsupp.lsum ℂ (fun n =>
    if n (Fin.last D.rank) = t then
      (Finsupp.lsingle (oldCharge D β n)).comp (polynomialRetraction D β).toLinearMap
    else 0)

private theorem injection_single (t : ℤ) (n : Charge D) (p : Oscillator D) :
    injection D β t (Finsupp.single n p) =
      Finsupp.single (liftCharge D β t n) (polynomialInjection D β p) := by
  simp [injection]

private theorem retraction_injection (t : ℤ) (v : Carrier D) :
    retraction D β t (injection D β t v) = v := by
  have h : (retraction D β t).comp (injection D β t) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro n p
    have hn : oldCharge D β (liftCharge D β t n) = n := by
      funext i
      simp [oldCharge, liftCharge]
    simp [injection_single, retraction, liftCharge, hn, retract_polynomial]
  exact congrArg (fun f : Module.End ℂ (Carrier D) => f v) h

private theorem injection_injective (t : ℤ) : Function.Injective (injection D β t) :=
  Function.LeftInverse.injective (retraction_injection D β t)

private theorem liftCharge_add (s t : ℤ) (a b : Charge D) :
    liftCharge D β (s + t) (a + b) = liftCharge D β s a + liftCharge D β t b := by
  funext i
  induction i using Fin.lastCases <;> simp [liftCharge]

private theorem bilinear_lift (a n : Charge D) (t : ℤ) :
    bilinear (auxiliary D β) (liftCharge D β 0 a) (liftCharge D β t n) =
      bilinear D a n + t * ∑ i, a i * β i := by
  classical
  simp only [bilinear, Fin.sum_univ_castSucc, liftCharge, auxiliary,
    Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, mul_comm t]

private theorem epsilon_lift (a n : Charge D) (t : ℤ) :
    epsilon (auxiliary D β) (liftCharge D β 0 a) (liftCharge D β t n) =
      epsilon D a n := by
  classical
  have lastNotLt (i : Fin D.rank) : ¬ Fin.last D.rank < i.castSucc :=
    not_lt.mpr (Fin.le_last _)
  unfold epsilon lowerCocycleExponent
  congr 1
  simp only [Finset.sum_filter]
  simp only [Fin.sum_univ_castSucc, liftCharge, auxiliary, halfDiagonal,
    Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Fin.castSucc_lt_castSucc_iff,
    lastNotLt, lt_self_iff_false, ↓reduceIte]
  simp

private theorem unit_lift (i : Fin D.rank) :
    unitCharge (auxiliary D β) i.castSucc = liftCharge D β 0 (unitCharge D i) := by
  funext j
  induction j using Fin.lastCases <;> simp [unitCharge, liftCharge]

private theorem creationSeries_lift (a : Charge D) :
    PowerSeries.map (polynomialInjection D β).toRingHom (creationSeries D a) =
      creationSeries (auxiliary D β) (liftCharge D β 0 a) := by
  ext q
  simp [creationSeries, polynomialInjection, liftCharge, Fin.sum_univ_castSucc,
    liftIndex, map_smul]

private theorem creationCoeff_lift (a : Charge D) (k : ℤ) :
    creationCoeff (auxiliary D β) (liftCharge D β 0 a) k =
      polynomialInjection D β (creationCoeff D a k) := by
  have hA : PowerSeries.constantCoeff (creationSeries D a) = 0 := by
    simp [creationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h : PowerSeries.map (polynomialInjection D β).toRingHom
      (creationExponential D a) =
      creationExponential (auxiliary D β) (liftCharge D β 0 a) := by
    unfold creationExponential
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
      PowerSeries.map_exp, creationSeries_lift]
  by_cases hk : k < 0
  · simp [creationCoeff, hk]
  · simpa only [creationCoeff, dif_neg hk, PowerSeries.coeff_map] using
      (congrArg (PowerSeries.coeff k.toNat) h).symm

private theorem translatedPolynomial_lift (a : Charge D) (p : Oscillator D) :
    translatedPolynomial (auxiliary D β) (liftCharge D β 0 a)
        (polynomialInjection D β p) =
      Polynomial.map (polynomialInjection D β).toRingHom (translatedPolynomial D a p) := by
  have hv (i : Fin D.rank) (k : ℕ) :
      translationVariable (auxiliary D β) (liftCharge D β 0 a) i.castSucc k =
        Polynomial.map (polynomialInjection D β).toRingHom (translationVariable D a i k) := by
    simp [translationVariable, unit_lift, bilinear_lift, polynomialInjection, liftIndex,
      map_smul]
  induction p using MvPolynomial.induction_on with
  | C c => simp [translatedPolynomial, polynomialInjection]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p x hp =>
    simp only [map_mul, polynomialInjection, rename_X, translatedPolynomial,
      MvPolynomial.eval₂Hom_X]
    change translatedPolynomial (auxiliary D β) (liftCharge D β 0 a)
      (polynomialInjection D β p) * translationVariable _ _ _ _ = _
    rw [hp, hv]
    simp [translatedPolynomial]

/-- The prescribed shifted exponential coefficient on an actual charge-polynomial sector. -/
def shiftedRawSingle (t : ℤ) (a : Charge D) (k : ℤ) (n : Charge D)
    (p : Oscillator D) : Carrier D :=
  epsilon D a n • Finsupp.single (a + n)
    (∑ d ∈ (translatedPolynomial D a p).support,
      (translatedPolynomial D a p).coeff d •
        creationCoeff D a (k - bilinear D a n - t * ∑ i, a i * β i + d))

private theorem rawSingle_lift (t : ℤ) (a n : Charge D) (k : ℤ) (p : Oscillator D) :
    rawSingle (auxiliary D β) (liftCharge D β 0 a) k
        (liftCharge D β t n) (polynomialInjection D β p) =
      injection D β t (shiftedRawSingle D β t a k n p) := by
  classical
  have hinj : Function.Injective (polynomialInjection D β) :=
    rename_injective _ (liftIndex_injective D β)
  rw [rawSingle, epsilon_lift, translatedPolynomial_lift,
    Polynomial.support_map_of_injective _ hinj]
  simp only [Polynomial.coeff_map, bilinear_lift, shiftedRawSingle,
    map_smul, injection_single, map_sum, ← liftCharge_add, zero_add]
  congr 2
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul, ← creationCoeff_lift]
  congr 2
  omega

/-- Compression inherits the lower bound on each actual ambient input. -/
def compress (t : ℤ) (A : VertexOperator ℂ (Carrier (auxiliary D β))) :
    VertexOperator ℂ (Carrier D) :=
  VertexOperator.of_coeff
    (fun k => (retraction D β t).comp
      ((HVertexOperator.coeff A k).comp (injection D β t))) (by
      intro v
      let lower := ((HahnModule.of ℂ).symm (A (injection D β t v))).order
      refine ⟨lower, ?_⟩
      intro k hk
      by_contra h
      have hz : HVertexOperator.coeff A k (injection D β t v) = 0 :=
        VertexOperator.coeff_eq_zero_of_lt_order A k _ (by dsimp [lower] at h; omega)
      exact hk (by simp only [LinearMap.comp_apply, hz, map_zero]))

private theorem compress_modes (t : ℤ) (A : VertexOperator ℂ (Carrier (auxiliary D β)))
    (m : ℤ) (v : Carrier D) :
    ((compress D β t A)[[m]]) v =
      retraction D β t ((A[[m]]) (injection D β t v)) := by
  rw [compress, VertexOperator.ncoeff_of_coeff]
  rfl

/-- The action is defined on every original state before proving its identities. -/
def action : Carrier D →ₗ[ℂ] VertexOperator ℂ (Carrier D) where
  toFun a := compress D β 1 (Y (auxiliary D β) (injection D β 0 a))
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, compress_modes, map_add,
      VertexOperator.ncoeff_add, LinearMap.add_apply]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    simp only [VertexOperator.coeff_eq_ncoeff, compress_modes, map_smul,
      VertexOperator.ncoeff_smul, LinearMap.smul_apply, RingHom.id_apply]

private def Intertwines (t : ℤ) (A : VertexOperator ℂ (Carrier D))
    (B : VertexOperator ℂ (Carrier (auxiliary D β))) : Prop :=
  ∀ (m : ℤ) (v : Carrier D), injection D β t ((A[[m]]) v) =
    (B[[m]]) (injection D β t v)

private theorem derivative_intertwines (t : ℤ)
    {A : VertexOperator ℂ (Carrier D)}
    {B : VertexOperator ℂ (Carrier (auxiliary D β))}
    (h : Intertwines D β t A B) (k : ℕ) :
    Intertwines D β t (dividedDerivative k A) (dividedDerivative k B) := by
  intro m v
  change injection D β t (Ring.choose (-m - 1 + k) k •
    HVertexOperator.coeff A (-m - 1 + k) v) =
      Ring.choose (-m - 1 + k) k •
        HVertexOperator.coeff B (-m - 1 + k) (injection D β t v)
  rw [map_zsmul, VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, h]

private theorem normal_intertwines (t : ℤ)
    {A B : VertexOperator ℂ (Carrier D)}
    {AE BE : VertexOperator ℂ (Carrier (auxiliary D β))}
    (hA : Intertwines D β t A AE) (hB : Intertwines D β t B BE) :
    Intertwines D β t (normalMinusOne A B).1 (normalMinusOne AE BE).1 := by
  intro m v
  rw [(normalMinusOne A B).2, (normalMinusOne AE BE).2, map_add,
    (injection D β t).toAddMonoidHom.map_finsum_of_injective (injection_injective D β t),
    (injection D β t).toAddMonoidHom.map_finsum_of_injective (injection_injective D β t)]
  congr 1 <;> apply finsum_congr <;> intro j
  · exact (hA _ _).trans (congrArg ((AE[[_]])) (hB _ _))
  · exact (hB _ _).trans (congrArg ((BE[[_]])) (hA _ _))

private theorem ground_original_intertwines (a : Charge D) :
    Intertwines D β 0 (actualField D a)
      (actualField (auxiliary D β) (liftCharge D β 0 a)) := by
  intro m
  have h : (injection D β 0).comp ((actualField D a)[[m]]) =
      ((actualField (auxiliary D β) (liftCharge D β 0 a))[[m]]).comp
        (injection D β 0) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, actualField, VertexOperator.ncoeff_of_coeff,
      injection_single]
    rw [(actual_creation_coefficient_transport D a a).2.2.1,
      (actual_creation_coefficient_transport (auxiliary D β)
        (liftCharge D β 0 a) (liftCharge D β 0 a)).2.2.1,
      rawSingle_lift]
    simp [shiftedRawSingle, rawSingle]
  exact fun v => congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f v) h

private theorem ground_compressed_intertwines (t : ℤ) (a : Charge D) :
    Intertwines D β t
      (compress D β t (actualField (auxiliary D β) (liftCharge D β 0 a)))
      (actualField (auxiliary D β) (liftCharge D β 0 a)) := by
  intro m
  have h : (injection D β t).comp
      ((compress D β t (actualField (auxiliary D β) (liftCharge D β 0 a)))[[m]]) =
      ((actualField (auxiliary D β) (liftCharge D β 0 a))[[m]]).comp (injection D β t) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, compress_modes, injection_single]
    rw [actualField, VertexOperator.ncoeff_of_coeff,
      (actual_creation_coefficient_transport (auxiliary D β)
        (liftCharge D β 0 a) (liftCharge D β 0 a)).2.2.1,
      rawSingle_lift, retraction_injection]
  exact fun v => congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f v) h

/-- Literal current coefficients, with the integral dual pairing in the zero mode. -/
def shiftedCurrentPolynomial (t : ℤ) (i : Fin D.rank) (n : Charge D) (m : ℤ) :
    Module.End ℂ (Oscillator D) :=
  if m < 0 then LinearMap.mulLeft ℂ (X (i, (-m - 1).toNat))
  else if m = 0 then ((bilinear D (unitCharge D i) n + t * β i : ℤ) : ℂ) • LinearMap.id
  else (m : ℂ) • ∑ j : Fin D.rank, (D.G i j : ℂ) • (pderiv (j, (m - 1).toNat)).toLinearMap

private theorem star_derivative (p : Oscillator D) (k : ℕ) :
    pderiv (Fin.last D.rank, k) (polynomialInjection D β p) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp
    (vars_rename (liftIndex D β) p h)
  exact Fin.castSucc_ne_last x.1 (congrArg Prod.fst eq)

private theorem current_polynomial_lift (t : ℤ) (i : Fin D.rank)
    (n : Charge D) (m : ℤ) (p : Oscillator D) :
    neutralPolynomialMode (auxiliary D β) i.castSucc (liftCharge D β t n) m
        (polynomialInjection D β p) =
      polynomialInjection D β (shiftedCurrentPolynomial D β t i n m p) := by
  classical
  have hu : ∑ j, unitCharge D i j * β j = β i := by simp [unitCharge]
  by_cases hm : m < 0
  · simp [neutralPolynomialMode, shiftedCurrentPolynomial, hm,
      polynomialInjection, liftIndex]
  · by_cases hz : m = 0
    · simp [neutralPolynomialMode, shiftedCurrentPolynomial, hm, hz, unit_lift,
        bilinear_lift, hu, map_smul]
    · simp only [neutralPolynomialMode, shiftedCurrentPolynomial, hm, hz, ↓reduceIte,
        LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coe_toLinearMap,
        map_smul, map_sum, Fin.sum_univ_castSucc]
      simp only [auxiliary, Fin.lastCases_castSucc, Fin.lastCases_last, star_derivative,
        smul_zero, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      exact congrArg ((D.G i j : ℂ) • ·)
        (pderiv_rename (liftIndex_injective D β) (j, (m - 1).toNat) p)

private theorem current_single_lift (t : ℤ) (i : Fin D.rank) (n : Charge D)
    (m : ℤ) (p : Oscillator D) :
    neutralMode (auxiliary D β) i.castSucc m (injection D β t (Finsupp.single n p)) =
      injection D β t (Finsupp.single n (shiftedCurrentPolynomial D β t i n m p)) := by
  simp only [injection_single, neutralMode, Finsupp.lsum_single, LinearMap.comp_apply,
    Finsupp.lsingle_apply, current_polynomial_lift]

private theorem current_original_intertwines (i : Fin D.rank) :
    Intertwines D β 0 (neutralField D i) (neutralField (auxiliary D β) i.castSucc) := by
  intro m
  have h : (injection D β 0).comp ((neutralField D i)[[m]]) =
      ((neutralField (auxiliary D β) i.castSucc)[[m]]).comp (injection D β 0) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, LatticeSugawaraCurrents.neutralField_ncoeff]
    rw [current_single_lift]
    simp [neutralMode, neutralPolynomialMode, shiftedCurrentPolynomial]
  exact fun v => congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f v) h

private theorem current_compressed_intertwines (t : ℤ) (i : Fin D.rank) :
    Intertwines D β t (compress D β t (neutralField (auxiliary D β) i.castSucc))
      (neutralField (auxiliary D β) i.castSucc) := by
  intro m
  have h : (injection D β t).comp
      ((compress D β t (neutralField (auxiliary D β) i.castSucc))[[m]]) =
      ((neutralField (auxiliary D β) i.castSucc)[[m]]).comp (injection D β t) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, compress_modes,
      LatticeSugawaraCurrents.neutralField_ncoeff]
    rw [current_single_lift, retraction_injection]
  exact fun v => congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f v) h

open private derivative_creation from D5.S3.VertexAlgebra.LatticeAllStateField

private theorem variable_state_field (x : Index D) :
    Y D (Finsupp.single (0 : Charge D) (X x)) =
      dividedDerivative x.2 (neutralField D x.1) := by
  rw [X, stateField_monomial]
  simp only [occurrences, Finsupp.toMultiset_single, one_nsmul,
    Multiset.toList_singleton, wordField]
  rw [actual_zero, normal_right_identity]

/-- Canonical multiplication recursion on the original polynomial, independent of list order. -/
private theorem multiplication_recursion (x : Index D) (n : Charge D) (p : Oscillator D) :
    Y D (Finsupp.single n (X x * p)) =
      (normalMinusOne (dividedDerivative x.2 (neutralField D x.1))
        (Y D (Finsupp.single n p))).1 := by
  have h : ((Y D (Finsupp.single (0 : Charge D) (X x)))[[-1]])
      (Finsupp.single n p) = Finsupp.single n (X x * p) := by
    rw [variable_state_field]
    exact derivative_creation D x n p
  rw [← h, LatticeActualStateFieldCalculus.minus_one_product_field,
    variable_state_field]

private def ambientWord (a : Charge D) : List (Index D) →
    VertexOperator ℂ (Carrier (auxiliary D β))
  | [] => actualField (auxiliary D β) (liftCharge D β 0 a)
  | x :: tail => (normalMinusOne
      (dividedDerivative x.2 (neutralField (auxiliary D β) x.1.castSucc))
      (ambientWord a tail)).1

/-- The normal-product recipe uses exactly the original occurrence order. -/
def shiftedWord (a : Charge D) : List (Index D) → VertexOperator ℂ (Carrier D)
  | [] => compress D β 1 (actualField (auxiliary D β) (liftCharge D β 0 a))
  | x :: tail => (normalMinusOne
      (dividedDerivative x.2 (compress D β 1 (neutralField (auxiliary D β) x.1.castSucc)))
      (shiftedWord a tail)).1

private theorem ambientWord_realization (a : Charge D) (w : List (Index D)) :
    Y (auxiliary D β)
      (injection D β 0 (Finsupp.single a (w.map (fun x => (X x : Oscillator D))).prod)) =
      ambientWord D β a w := by
  induction w with
  | nil => simp [injection_single, ambientWord, stateField_ground]
  | cons x tail ih =>
    simp only [List.map_cons, List.prod_cons, injection_single, map_mul,
      polynomialInjection, rename_X]
    rw [multiplication_recursion]
    change (normalMinusOne _ (Y (auxiliary D β)
      (injection D β 0 (Finsupp.single a (tail.map (fun x => (X x : Oscillator D))).prod))))).1 = _
    rw [ih]
    rfl

private theorem word_original_intertwines (a : Charge D) (w : List (Index D)) :
    Intertwines D β 0 (wordField D a w) (ambientWord D β a w) := by
  induction w with
  | nil => exact ground_original_intertwines D β a
  | cons x tail ih =>
    exact normal_intertwines D β 0
      (derivative_intertwines D β 0 (current_original_intertwines D β x.1) x.2) ih

private theorem word_shifted_intertwines (a : Charge D) (w : List (Index D)) :
    Intertwines D β 1 (shiftedWord D β a w) (ambientWord D β a w) := by
  induction w with
  | nil => exact ground_compressed_intertwines D β 1 a
  | cons x tail ih =>
    exact normal_intertwines D β 1
      (derivative_intertwines D β 1 (current_compressed_intertwines D β 1 x.1) x.2) ih

private theorem monomial_ambient (a : Charge D) (e : Index D →₀ ℕ) :
    Y (auxiliary D β) (injection D β 0 (Finsupp.single a (monomial e 1))) =
      ambientWord D β a (occurrences D e) := by
  rw [← occurrences_product D e]
  exact ambientWord_realization D β a _

/-- Original products are transported on all original inputs and all integer modes. -/
theorem source_transport (a b : Carrier D) (m : ℤ) :
    injection D β 0 (((Y D a)[[m]]) b) =
      ((Y (auxiliary D β) (injection D β 0 a))[[m]]) (injection D β 0 b) := by
  have h : (injection D β 0).comp ((Y D a)[[m]]) =
      ((Y (auxiliary D β) (injection D β 0 a))[[m]]).comp (injection D β 0) := by
    have linearEquality :
        (fun a : Carrier D => (injection D β 0).comp ((Y D a)[[m]])) =
        (fun a : Carrier D =>
          ((Y (auxiliary D β) (injection D β 0 a))[[m]]).comp (injection D β 0)) := by
      funext a
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, VertexOperator.ncoeff_add,
          LinearMap.comp_add, LinearMap.add_comp, ha, hb]
      | single n p =>
        induction p using MvPolynomial.induction_on' with
        | add p q hp hq => simp only [map_add, Finsupp.single_add,
            VertexOperator.ncoeff_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
        | monomial e c =>
          have hc : monomial e c = c • (monomial e 1 : Oscillator D) := by simp
          rw [hc, Finsupp.single_smul]
          simp only [map_smul, VertexOperator.ncoeff_smul, LinearMap.comp_smul,
            LinearMap.smul_comp, RingHom.id_apply]
          congr 1
          rw [stateField_monomial, monomial_ambient]
          exact LinearMap.ext (word_original_intertwines D β n (occurrences D e) m)
    exact congrFun linearEquality a
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f b) h

/-- The full literal recipe agrees with compression on every original basis input. -/
theorem action_monomial (a : Charge D) (e : Index D →₀ ℕ) :
    action D β (Finsupp.single a (monomial e 1)) =
      shiftedWord D β a (occurrences D e) := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro v
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  change ((compress D β 1 _)[[-k - 1]]) v = _
  rw [compress_modes, monomial_ambient,
    ← word_shifted_intertwines D β a (occurrences D e), retraction_injection]

/-- The entire Fock sector is invariant under every original all-state field. -/
theorem module_transport (a v : Carrier D) (m : ℤ) :
    injection D β 1 (((action D β a)[[m]]) v) =
      ((Y (auxiliary D β) (injection D β 0 a))[[m]]) (injection D β 1 v) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, VertexOperator.ncoeff_add,
      LinearMap.add_apply, ha, hb]
  | single n p =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [map_add, Finsupp.single_add,
        VertexOperator.ncoeff_add, LinearMap.add_apply, hp, hq]
    | monomial e c =>
      have hc : monomial e c = c • (monomial e 1 : Oscillator D) := by simp
      rw [hc, Finsupp.single_smul]
      simp only [map_smul, VertexOperator.ncoeff_smul, LinearMap.smul_apply,
        RingHom.id_apply]
      congr 1
      rw [action_monomial, monomial_ambient]
      exact word_shifted_intertwines D β n (occurrences D e) m v

private theorem injection_vacuum :
    injection D β 0 (vacuum D) = vacuum (auxiliary D β) := by
  have hz : liftCharge D β 0 0 = 0 := by
    funext i
    induction i using Fin.lastCases <;> simp [liftCharge]
  simp [vacuum, injection_single, hz]

theorem module_vacuum : action D β (vacuum D) = identityField := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro v
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  apply injection_injective D β 1
  rw [module_transport, injection_vacuum, stateField_vacuum,
    identity_modes, identity_modes]
  split_ifs <;> simp

private theorem derivation_lift (p : Oscillator D) :
    oscillatorDerivation (auxiliary D β) (polynomialInjection D β p) =
      polynomialInjection D β (oscillatorDerivation D p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [polynomialInjection]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p x hp =>
    simp only [map_mul, polynomialInjection, rename_X, Derivation.leibniz]
    rw [show oscillatorDerivation (auxiliary D β) (rename (liftIndex D β) p) =
      rename (liftIndex D β) (oscillatorDerivation D p) from hp]
    simp [oscillatorDerivation, MvPolynomial.mkDerivation_X, liftIndex, map_smul]

private theorem source_translation (a : Carrier D) :
    injection D β 0 (translation D a) =
      translation (auxiliary D β) (injection D β 0 a) := by
  have h : (injection D β 0).comp (translation D) =
      (translation (auxiliary D β)).comp (injection D β 0) := by
    apply Finsupp.lhom_ext
    intro n p
    simp only [LinearMap.comp_apply, translation_single, injection_single]
    congr 1
    rw [map_add, map_mul, derivation_lift]
    congr 2
    simp [chargePolynomial, Fin.sum_univ_castSucc, liftCharge, map_sum,
      map_smul, polynomialInjection, liftIndex]
  exact congrArg (fun f : Carrier D →ₗ[ℂ] Carrier (auxiliary D β) => f a) h

/-- Differentiation is on the original input; no ambient translation is restricted to sector one. -/
theorem module_input_derivative (a : Carrier D) (m : ℤ) :
    ((action D β (translation D a))[[m]]) = -(m : ℂ) • ((action D β a)[[m - 1]]) := by
  apply LinearMap.ext
  intro v
  apply injection_injective D β 1
  rw [module_transport, source_translation,
    LatticeActualStateDerivative.state_derivative_modes,
    LinearMap.smul_apply, map_smul, LinearMap.smul_apply, module_transport]

open StateFieldResidueReconstruction (integerBinomial)

def moduleLeft (p q r : ℤ) (a b v : Carrier D) (i : ℕ) : Carrier D :=
  integerBinomial p i • ((action D β (((Y D a)[[r + i]]) b))[[p + q - i]]) v

def moduleFirst (p q r : ℤ) (a b v : Carrier D) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    ((action D β a)[[p + r - i]]) (((action D β b)[[q + i]]) v)

def moduleSecond (p q r : ℤ) (a b v : Carrier D) (i : ℕ) : Carrier D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      ((action D β b)[[q + r - i]]) (((action D β a)[[p + i]]) v))

/-- Three separate supports and the literal all-integer original-product module identity. -/
theorem module_borcherds (a b v : Carrier D) (p q r : ℤ) :
    Function.HasFiniteSupport (moduleLeft D β p q r a b v) ∧
    Function.HasFiniteSupport (moduleFirst D β p q r a b v) ∧
    Function.HasFiniteSupport (moduleSecond D β p q r a b v) ∧
    (∑ᶠ i : ℕ, moduleLeft D β p q r a b v i) =
      ∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial r i) •
        (((action D β a)[[p + r - i]]) (((action D β b)[[q + i]]) v) -
          StateFieldResidueReconstruction.epsilon r •
            ((action D β b)[[q + r - i]]) (((action D β a)[[p + i]]) v)) := by
  classical
  have hl (i : ℕ) : injection D β 1 (moduleLeft D β p q r a b v i) =
      LatticeAllStateJacobi.jacobiLeftTerm (auxiliary D β) p q r
        (injection D β 0 a) (injection D β 0 b) (injection D β 1 v) i := by
    simp only [moduleLeft, map_smul, module_transport, source_transport,
      LatticeAllStateJacobi.jacobiLeftTerm, LatticeAllStateReconstruction.mu]
  have hf (i : ℕ) : injection D β 1 (moduleFirst D β p q r a b v i) =
      LatticeAllStateJacobi.jacobiRightFirstTerm (auxiliary D β) p q r
        (injection D β 0 a) (injection D β 0 b) (injection D β 1 v) i := by
    simp only [moduleFirst, map_smul, module_transport,
      LatticeAllStateJacobi.jacobiRightFirstTerm, LatticeAllStateReconstruction.mu]
  have hs (i : ℕ) : injection D β 1 (moduleSecond D β p q r a b v i) =
      LatticeAllStateJacobi.jacobiRightSecondTerm (auxiliary D β) p q r
        (injection D β 0 a) (injection D β 0 b) (injection D β 1 v) i := by
    simp only [moduleSecond, map_smul, module_transport,
      LatticeAllStateJacobi.jacobiRightSecondTerm, LatticeAllStateReconstruction.mu]
  obtain ⟨ambientL, ambientF, ambientS, ambientLaw⟩ :=
    LatticeAllStateJacobi.borcherds (auxiliary D β)
      (injection D β 0 a) (injection D β 0 b) (injection D β 1 v) p q r
  have finitePullback (f : ℕ → Carrier D) (g : ℕ → Carrier (auxiliary D β))
      (h : ∀ i, injection D β 1 (f i) = g i) (hg : Function.HasFiniteSupport g) :
      Function.HasFiniteSupport f := by
    apply hg.subset
    intro i hi
    change g i ≠ 0
    rw [← h i, ← (injection D β 1).map_zero]
    exact (injection_injective D β 1).ne hi
  have finiteL := finitePullback _ _ hl ambientL
  have finiteF := finitePullback _ _ hf ambientF
  have finiteS := finitePullback _ _ hs ambientS
  refine ⟨finiteL, finiteF, finiteS, ?_⟩
  simp_rw [smul_sub]
  change (∑ᶠ i : ℕ, moduleLeft D β p q r a b v i) =
    ∑ᶠ i : ℕ, (moduleFirst D β p q r a b v i - moduleSecond D β p q r a b v i)
  rw [finsum_sub_distrib finiteF finiteS]
  apply injection_injective D β 1
  rw [map_sub, map_finsum _ finiteL, map_finsum _ finiteF, map_finsum _ finiteS]
  simp_rw [hl, hf, hs]
  simp_rw [smul_sub] at ambientLaw
  rw [finsum_sub_distrib ambientF ambientS] at ambientLaw
  exact ambientLaw

/-- Rational pairing with a physical shift, before using the exact dual equation. -/
def physicalPairing (a : Charge D) (μ : Fin D.rank → ℚ) : ℚ :=
  ∑ i, ∑ j, (a i : ℚ) * (D.G i j : ℚ) * μ j

/-- Exact duality identifies the rational physical pairing with the integral raw-power shift. -/
theorem physical_pairing_integral (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (a : Charge D) :
    physicalPairing D a μ = ((∑ i, a i * β i : ℤ) : ℚ) := by
  simp only [physicalPairing, mul_assoc, ← Finset.mul_sum, hDual]
  push_cast
  rfl

/-- Concrete shifted ground action, on arbitrary oscillator polynomials. -/
theorem action_ground_coefficients (a n : Charge D) (p : Oscillator D) (m : ℤ) :
    ((action D β (Finsupp.single a (1 : Oscillator D)))[[m]]) (Finsupp.single n p) =
      shiftedRawSingle D β 1 a (-m - 1) n p := by
  change ((compress D β 1 (Y (auxiliary D β)
    (injection D β 0 (Finsupp.single a (1 : Oscillator D)))))[[m]]) _ = _
  rw [compress_modes, injection_single, map_one, stateField_ground, injection_single,
    actualField, VertexOperator.ncoeff_of_coeff,
    (actual_creation_coefficient_transport (auxiliary D β)
      (liftCharge D β 0 a) (liftCharge D β 0 a)).2.2.1,
    rawSingle_lift, retraction_injection]

/-- The physical shift is genuinely rational; its action uses precisely its integral dual pairing. -/
theorem physical_ground_action (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (a n : Charge D) (p : Oscillator D) (m : ℤ) :
    physicalPairing D a μ = ((∑ i, a i * β i : ℤ) : ℚ) ∧
    ((action D β (Finsupp.single a (1 : Oscillator D)))[[m]]) (Finsupp.single n p) =
      epsilon D a n • Finsupp.single (a + n)
        (∑ d ∈ (translatedPolynomial D a p).support,
          (translatedPolynomial D a p).coeff d •
            creationCoeff D a (-m - 1 - bilinear D a n - ∑ i, a i * β i + d)) := by
  constructor
  · exact physical_pairing_integral D β μ hDual a
  · simpa only [shiftedRawSingle, one_mul] using action_ground_coefficients D β a n p m

end
end D5.S3.VertexAlgebra.LatticeDualCosetModule
