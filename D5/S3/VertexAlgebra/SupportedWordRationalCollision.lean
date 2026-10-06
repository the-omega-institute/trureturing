/- GID: D5/S3/VertexAlgebra/SupportedWordRationalCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SupportedWordRationalCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite clearing reconstructs actual supported words and their collision. -/

/-
Finite clearing reconstructs actual supported words and their collision.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.OrderedCollisionCoordinates
import D5.S3.VertexAlgebra.SupportedFieldWords
import D5.S3.VertexAlgebra.CollisionRationalExpansions
import Mathlib.Data.List.FinRange
import Mathlib.Data.Complex.Basic
import D5.S3.VertexAlgebra.LabelledRationalClearing
import D5.S3.VertexAlgebra.RationalCollision
import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- The coefficientwise lambda(P) for the actual supplier's finite numerator
type (Fin N -> Nat) ->₀ V. Natural exponents are included without a cutoff. -/
namespace SupportedWordRationalCollision.VectorNumeratorScalarization
open CollisionRationalExpansions.OrderedRationalExpansion
variable (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V] {N : ℕ}

def naturalExponent (a : Fin N → ℕ) : Fin N → ℤ := fun i => a i

theorem naturalExponent_injective : Function.Injective (naturalExponent (N := N)) := by
  intro a b h
  funext i
  exact Int.ofNat_inj.mp (congrFun h i)

def scalarNumerator (P : (Fin N → ℕ) →₀ V) (lambda : V →ₗ[K] K) : LabelledPolynomial K N :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain naturalExponent (P.mapRange lambda lambda.map_zero))

theorem scalarNumerator_coefficient (P : (Fin N → ℕ) →₀ V) (lambda : V →ₗ[K] K)
    (a : Fin N → ℕ) :
    (scalarNumerator K P lambda).coeff (naturalExponent a) = lambda (P a) := by
  simp [scalarNumerator, Finsupp.mapDomain_apply naturalExponent_injective]

theorem scalarNumerator_nonnegative (P : (Fin N → ℕ) →₀ V) (lambda : V →ₗ[K] K)
    (e : Fin N → ℤ) (he : e ∈ (scalarNumerator K P lambda).coeff.support) (z : Fin N) :
    0 ≤ e z := by
  classical
  change e ∈ (Finsupp.mapDomain naturalExponent (P.mapRange lambda lambda.map_zero)).support at he
  rw [Finsupp.mapDomain_support_of_injective naturalExponent_injective] at he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact Int.natCast_nonneg (a z)

end SupportedWordRationalCollision.VectorNumeratorScalarization
end

section
namespace SupportedWordRationalCollision.ActualPolynomialBridge
open SupportedFieldWords.ActualFieldWordAdapter SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion SupportedFieldWords.FiniteConvolution SupportedWordRationalCollision.VectorNumeratorScalarization
open D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The frozen distribution action is exactly the library finite convolution. -/
theorem native_action_eq {N : ℕ} (Q : LaurentPolynomial N)
    (F : Distribution N V) : polynomialAction Q F = distributionAction Q F := by
  rfl

/-- Scalarization commutes with the finite polynomial action, with no support cutoff. -/
theorem scalar_action {N : ℕ} (Q : LaurentPolynomial N)
    (F : Distribution N V) (lambda : V →ₗ[ℂ] ℂ) (e : Fin N → ℤ) :
    lambda (polynomialAction Q F e) =
      distributionAction Q (fun b => lambda (F b)) e := by
  classical
  rw [native_action_eq]
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | single b a => rw [distributionAction_single, distributionAction_single, map_smul]

/-- Coefficients at every integer labelled exponent of the genuine finite numerator. -/
theorem scalar_numerator_all_coeff {N : ℕ} (P : VectorPolynomial N V)
    (lambda : V →ₗ[ℂ] ℂ) (e : Fin N → ℤ) :
    (scalarNumerator ℂ P lambda).coeff e =
      if ∀ i, 0 ≤ e i then lambda (P (fun i => (e i).toNat)) else 0 := by
  classical
  by_cases he : ∀ i, 0 ≤ e i
  · rw [if_pos he]
    have hnat : SupportedWordRationalCollision.VectorNumeratorScalarization.naturalExponent (fun i => (e i).toNat) = e := by
      funext i
      exact Int.toNat_of_nonneg (he i)
    calc
      (scalarNumerator ℂ P lambda).coeff e =
          (scalarNumerator ℂ P lambda).coeff
            (SupportedWordRationalCollision.VectorNumeratorScalarization.naturalExponent (fun i => (e i).toNat)) :=
        congrArg (fun b => (scalarNumerator ℂ P lambda).coeff b) hnat.symm
      _ = lambda (P (fun i => (e i).toNat)) := scalarNumerator_coefficient ℂ P lambda _
  · rw [if_neg he]
    by_contra hn
    have hs : e ∈ (scalarNumerator ℂ P lambda).coeff.support := Finsupp.mem_support_iff.mpr hn
    exact he (fun i => scalarNumerator_nonnegative ℂ P lambda e hs i)

/-- Multiplication by the exact ordered finite polynomial is the same finite action. -/
theorem ordered_mul_coeff (n : ℕ) (sigma : Equiv.Perm (Fin n))
    (Q : LabelledPolynomial ℂ n) (F : HahnSeries (Indices n) ℂ) (e : Fin n → ℤ) :
    (orderedPolynomialFor ℂ n sigma Q * F).coeff (orderExponents n sigma e) =
      distributionAction Q (fun b => F.coeff (orderExponents n sigma b)) e := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp [add_mul, hP, hQ]
  | single b a =>
    have hs : orderedPolynomialFor ℂ n sigma (AddMonoidAlgebra.single b a) =
        HahnSeries.single (orderExponents n sigma b) a := by
      change scalarPolynomial
        ((AddMonoidAlgebra.domCongr ℂ ℂ (orderExponents n sigma)) (AddMonoidAlgebra.single b a)) = _
      rw [AddMonoidAlgebra.domCongr_single, scalarPolynomial_single]
    rw [hs, HahnSeries.coeff_single_mul, distributionAction_single, ← map_sub]
    rfl

/-- An ordered embedding evaluates at the original labelled coefficient. -/
theorem ordered_polynomial_coeff (n : ℕ) (sigma : Equiv.Perm (Fin n))
    (Q : LabelledPolynomial ℂ n) (e : Fin n → ℤ) :
    (orderedPolynomialFor ℂ n sigma Q).coeff (orderExponents n sigma e) = Q.coeff e := by
  change (scalarPolynomial ((AddMonoidAlgebra.domCongr ℂ ℂ (orderExponents n sigma)) Q)).coeff
    (orderExponents n sigma e) = _
  rw [scalarPolynomial_coeff, AddMonoidAlgebra.coeff_domCongr, AddEquiv.symm_apply_apply]

/-- The actual finite polynomial action, after the actual selector and arbitrary lambda,
really is multiplication in the supported Hahn field. -/
theorem actual_clearing_coeff (n : ℕ) (D : GradedLocalFields n V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (sigma : Equiv.Perm (Fin n))
    (lambda : V →ₗ[ℂ] ℂ) (Q : LaurentPolynomial n) (e : Fin n → ℤ) :
    (orderedPolynomialFor ℂ n sigma Q *
      scalarWordCarrier n D.field sigma D.vacuum (lambda.comp selector.map)).coeff
        (orderExponents n sigma e) =
      lambda (polynomialAction Q
        (coefficientDistribution D.field D.vacuum selector.map (List.ofFn sigma)) e) := by
  have hcoeff : (fun b =>
      (scalarWordCarrier n D.field sigma D.vacuum (lambda.comp selector.map)).coeff
        (orderExponents n sigma b)) =
      (fun b => lambda (coefficientDistribution D.field D.vacuum selector.map (List.ofFn sigma) b)) := by
    funext b
    exact scalarWordCarrier_actual_coeff n D selector sigma lambda b
  rw [ordered_mul_coeff, scalar_action, hcoeff]

end SupportedWordRationalCollision.ActualPolynomialBridge
end

section
namespace SupportedWordRationalCollision.ActualOrderedCoordinates
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution CollisionRationalExpansions.OrderedRationalExpansion
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders LabelledRationalClearing.GlobalRationalCurry CollisionRationalExpansions.FullOrderSpectatorPole
set_option backward.isDefEq.respectTransparency false

/-- Insert a label after the whole inner block, retaining every outer label. -/
def insertTuple {α : Type*} (inner : ℕ) : (outer : ℕ) → α →
    (Fin (inner + outer) → α) → Fin ((inner + 1) + outer) → α
  | 0, a, f => Fin.snoc f a
  | outer + 1, a, f => Fin.snoc
      (insertTuple inner outer a (fun i => f i.castSucc)) (f (Fin.last (inner + outer)))

/-- Insert z immediately before the boundary remaining label x. -/
def firstTuple {α : Type*} (pre : ℕ) : (post : ℕ) → α →
    (Fin ((pre + 1) + post) → α) → Fin ((pre + 2) + post) → α
  | 0, a, f => Fin.snoc (Fin.snoc (fun i : Fin pre => f i.castSucc) a) (f (Fin.last pre))
  | post + 1, a, f => Fin.snoc
      (firstTuple pre post a (fun i => f i.castSucc)) (f (Fin.last ((pre + 1) + post)))

lemma insertTuple_exponents {α : Type*} (inner outer : ℕ) (a : α)
    (f : Fin (inner + outer) → α) (e : α → ℤ) :
    exponents ((inner + 1) + outer) (fun i => e (insertTuple inner outer a f i)) =
      CollisionRationalExpansions.HahnFiberResidue.insertIndex inner outer (e a)
        (exponents (inner + outer) (fun i => e (f i))) := by
  induction outer with
  | zero => simp only [insertTuple, exponents, Fin.snoc_last, Fin.snoc_castSucc]; rfl
  | succ outer ih =>
    simp only [insertTuple, exponents, Fin.snoc_last, Fin.snoc_castSucc,
      CollisionRationalExpansions.HahnFiberResidue.insertIndex, ofLex_toLex]
    change (toLex (e (f (Fin.last (inner + outer))),
      exponents ((inner + 1) + outer) (fun i => e (insertTuple inner outer a (fun j => f j.castSucc) i))) :
      ℤ ×ₗ Indices ((inner + 1) + outer)) =
      toLex (e (f (Fin.last (inner + outer))),
        CollisionRationalExpansions.HahnFiberResidue.insertIndex inner outer (e a) (exponents (inner + outer) (fun i => e (f i.castSucc))))
    exact congrArg (fun g : Indices ((inner + 1) + outer) =>
        (toLex (e (f (Fin.last (inner + outer))), g) : ℤ ×ₗ Indices ((inner + 1) + outer)))
        (ih (fun i => f i.castSucc))

lemma firstTuple_exponents {α : Type*} (pre post : ℕ) (a : α)
    (f : Fin ((pre + 1) + post) → α) (e : α → ℤ) :
    exponents ((pre + 2) + post) (fun i => e (firstTuple pre post a f i)) =
      firstInsert pre post (e a)
        (exponents ((pre + 1) + post) (fun i => e (f i))) := by
  induction post with
  | zero => simp only [firstTuple, exponents, Fin.snoc_last, Fin.snoc_castSucc]; rfl
  | succ post ih =>
    simp only [firstTuple, exponents, Fin.snoc_last, Fin.snoc_castSucc, firstInsert, ofLex_toLex]
    change (toLex (e (f (Fin.last ((pre + 1) + post))),
      exponents ((pre + 2) + post) (fun i => e (firstTuple pre post a (fun j => f j.castSucc) i))) :
      ℤ ×ₗ Indices ((pre + 2) + post)) =
      toLex (e (f (Fin.last ((pre + 1) + post))),
        firstInsert pre post (e a) (exponents ((pre + 1) + post) (fun i => e (f i.castSucc))))
    exact congrArg (fun g : Indices ((pre + 2) + post) =>
        (toLex (e (f (Fin.last ((pre + 1) + post))), g) : ℤ ×ₗ Indices ((pre + 2) + post)))
        (ih (fun i => f i.castSucc))

/-- An exact exponent equivalence proves the finite label function is a permutation. -/
lemma bijective_of_exponents {n : ℕ} (f : Fin n → Fin n)
    (E : (Fin n → ℤ) ≃+ Indices n)
    (h : ∀ e, exponents n (fun i => e (f i)) = E e) : Function.Bijective f := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card f).mpr
  refine ⟨?_, rfl⟩
  intro a
  by_contra hn
  have hz : (fun i => (Pi.single a 1 : Fin n → ℤ) (f i)) = 0 := by
    funext i
    simp only [Pi.zero_apply, Pi.single_apply]
    rw [if_neg (by intro hi; exact hn ⟨i, hi⟩)]
  have he : E (Pi.single a 1) = E 0 := by rw [← h, hz, ← h]; rfl
  have hzero := congrFun (E.injective he) a
  simpa using hzero

variable (pre post : ℕ) (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z)

def firstOrderFunction : Fin ((pre + 2) + post) → Fin ((pre + 2) + post) :=
  firstTuple pre post z (fun i => (tau i).val)
def secondOrderFunction : Fin ((pre + 2) + post) → Fin ((pre + 2) + post) :=
  insertTuple (pre + 1) post z (fun i => (tau i).val)

lemma firstOrder_exponents (e : Fin ((pre + 2) + post) → ℤ) :
    exponents ((pre + 2) + post) (fun i => e (firstOrderFunction pre post z tau i)) =
      firstExponents pre post z tau e := by
  rw [firstOrderFunction, firstTuple_exponents]
  rfl
lemma secondOrder_exponents (e : Fin ((pre + 2) + post) → ℤ) :
    exponents ((pre + 2) + post) (fun i => e (secondOrderFunction pre post z tau i)) =
      fullExponents (pre + 1) post z tau e := by
  rw [secondOrderFunction, insertTuple_exponents]
  rfl

def firstOrder : Equiv.Perm (Fin ((pre + 2) + post)) :=
  Equiv.ofBijective (firstOrderFunction pre post z tau)
    (bijective_of_exponents _ (firstExponents pre post z tau) (firstOrder_exponents pre post z tau))
def secondOrder : Equiv.Perm (Fin ((pre + 2) + post)) :=
  Equiv.ofBijective (secondOrderFunction pre post z tau)
    (bijective_of_exponents _ (fullExponents (pre + 1) post z tau) (secondOrder_exponents pre post z tau))

lemma firstOrder_equiv : orderExponents ((pre + 2) + post) (firstOrder pre post z tau) =
    firstExponents pre post z tau := by
  ext e
  exact firstOrder_exponents pre post z tau e
lemma secondOrder_equiv : orderExponents ((pre + 2) + post) (secondOrder pre post z tau) =
    fullExponents (pre + 1) post z tau := by
  ext e
  exact secondOrder_exponents pre post z tau e

lemma firstOrder_rational : orderedRationalFor ℂ ((pre + 2) + post) (firstOrder pre post z tau) =
    firstRational ℂ pre post z tau := by
  apply IsFractionRing.ringHom_ext (A := LabelledPolynomial ℂ ((pre + 2) + post))
  intro P
  simp only [orderedRationalFor, firstRational, IsFractionRing.lift_algebraMap]
  change orderedPolynomialFor ℂ ((pre + 2) + post) (firstOrder pre post z tau) P =
    polynomialViaEquiv (firstExponents pre post z tau) P
  simp only [orderedPolynomialFor, polynomialViaEquiv, AlgHom.comp_apply, RingHom.comp_apply]
  rw [firstOrder_equiv]
  rfl
lemma secondOrder_rational : orderedRationalFor ℂ ((pre + 2) + post) (secondOrder pre post z tau) =
    secondRational ℂ pre post z tau := by
  apply IsFractionRing.ringHom_ext (A := LabelledPolynomial ℂ ((pre + 2) + post))
  intro P
  simp only [orderedRationalFor, secondRational, fullRational, IsFractionRing.lift_algebraMap]
  change orderedPolynomialFor ℂ ((pre + 2) + post) (secondOrder pre post z tau) P =
    polynomialViaEquiv (fullExponents (pre + 1) post z tau) P
  simp only [orderedPolynomialFor, polynomialViaEquiv, AlgHom.comp_apply, RingHom.comp_apply]
  rw [secondOrder_equiv]
  rfl

end SupportedWordRationalCollision.ActualOrderedCoordinates
end

section
namespace SupportedWordRationalCollision.ClearingNonzero
open LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization LabelledRationalClearing.ActualClearingPartialFractions
open CollisionRationalExpansions.OrderedRationalExpansion OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

include z in
theorem actual_clearing_ne_zero (k : ℕ) : clearingPolynomial K N k ≠ 0 := by
  classical
  have hc : RatFunc.C (clearingScalar K z k) ≠ 0 := by
    simpa only [map_zero] using
      (RatFunc.C : CoefficientField K z →+* RatFunc (CoefficientField K z)).injective.ne
        (clearingScalar_ne_zero K z k)
  have hp : (∏ p : LabelledPair N,
      (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p)) ^ k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    apply pow_ne_zero
    simpa only [map_zero] using
      (IsFractionRing.injective (Polynomial (CoefficientField K z))
        (RatFunc (CoefficientField K z))).ne (pairPole_monic K z p).ne_zero
  intro hq
  have he := curry_clearingPolynomial K z k
  rw [hq, map_zero] at he
  exact mul_ne_zero hc hp he.symm

theorem full_clearing_ne_zero (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (k : ℕ) :
    firstPolynomial K pre post z tau (clearingPolynomial K ((pre + 2) + post) k) ≠ 0 ∧
    fullPolynomial K (pre + 1) post z tau (clearingPolynomial K ((pre + 2) + post) k) ≠ 0 := by
  constructor
  · simpa only [map_zero, firstPolynomial] using
      (polynomialViaEquiv_injective (K := K) (firstExponents pre post z tau)).ne
        (actual_clearing_ne_zero K z k)
  · simpa only [map_zero, fullPolynomial] using
      (polynomialViaEquiv_injective (K := K) (fullExponents (pre + 1) post z tau)).ne
        (actual_clearing_ne_zero K z k)

end SupportedWordRationalCollision.ClearingNonzero
end

section
namespace SupportedWordRationalCollision.ActualRationalReconstruction
open SupportedFieldWords.ActualFieldWordAdapter SupportedWordRationalCollision.ActualPolynomialBridge SupportedFieldWords.OrderedWords
open SupportedFieldWords.OrderedDistribution CollisionRationalExpansions.OrderedRationalExpansion SupportedWordRationalCollision.VectorNumeratorScalarization
open D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem originalQ_ne_zero (n : ℕ) (z : Fin n) (k : ℕ) :
    clearingPolynomial n k ≠ 0 :=
  SupportedWordRationalCollision.ClearingNonzero.actual_clearing_ne_zero ℂ z k


/-- Every complete label order is a permutation of the original supplier order. -/
lemma supplier_order_perm {n : ℕ} (order : List (Fin n)) (nodup : order.Nodup)
    (all_labels : ∀ i, i ∈ order) (sigma : Equiv.Perm (Fin n)) :
    order.Perm (List.ofFn sigma) := by
  apply (List.perm_ext_iff_of_nodup nodup (List.nodup_ofFn_ofInjective sigma.injective)).mpr
  intro i
  constructor
  · intro _
    exact List.mem_ofFn.mpr ⟨sigma.symm i, sigma.apply_symm_apply i⟩
  · intro _
    exact all_labels i

/-- Reconstruct only in the genuine supported Hahn field. The hypothesis here
is the finite numerator certificate, never an assumed expansion identity. -/
theorem actual_expansion_of_certificate (n : ℕ) (D : GradedLocalFields n V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (sigma : Equiv.Perm (Fin n))
    (lambda : V →ₗ[ℂ] ℂ) (P : VectorPolynomial n V)
    (hQ : clearingPolynomial n D.localityOrder ≠ 0)
    (hclear : ∀ e : Fin n → ℤ,
      polynomialAction (clearingPolynomial n D.localityOrder)
        (coefficientDistribution D.field D.vacuum selector.map (List.ofFn sigma)) e =
      if ∀ i, 0 ≤ e i then P (fun i => (e i).toNat) else 0) :
    scalarWordCarrier n D.field sigma D.vacuum (lambda.comp selector.map) =
      orderedRationalFor ℂ n sigma
        (algebraMap _ (CommonRational ℂ n) (scalarNumerator ℂ P lambda) /
          algebraMap _ (CommonRational ℂ n) (clearingPolynomial n D.localityOrder)) := by
  have hmul : orderedPolynomialFor ℂ n sigma (clearingPolynomial n D.localityOrder) *
      scalarWordCarrier n D.field sigma D.vacuum (lambda.comp selector.map) =
        orderedPolynomialFor ℂ n sigma (scalarNumerator ℂ P lambda) := by
    ext g
    obtain ⟨e, rfl⟩ := (orderExponents n sigma).surjective g
    rw [actual_clearing_coeff, hclear, ordered_polynomial_coeff, scalar_numerator_all_coeff]
    split_ifs <;> simp
  have hne : orderedPolynomialFor ℂ n sigma (clearingPolynomial n D.localityOrder) ≠ 0 := by
    simpa only [map_zero] using (orderedPolynomialFor_injective ℂ n sigma).ne hQ
  rw [map_div₀]
  simp only [orderedRationalFor, IsFractionRing.lift_algebraMap]
  apply (eq_div_iff hne).mpr
  rw [mul_comm]
  exact hmul

/-- A genuine supplier invocation identifies every supported actual order
with the expansion of the same original labelled lambda(P)/Q. -/
theorem actual_all_order_expansion (n : ℕ) (D : GradedLocalFields n V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (order : List (Fin n))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (W : Submodule ℂ V)
    (in_W : ∀ e, coefficientDistribution D.field D.vacuum selector.map order e ∈ W)
    (lambda : V →ₗ[ℂ] ℂ) (z : Fin n) :
    ∃ P : VectorPolynomial n V,
      (∀ other : List (Fin n), order.Perm other → ∀ e : Fin n → ℤ,
        polynomialAction (clearingPolynomial n D.localityOrder)
          (coefficientDistribution D.field D.vacuum selector.map other) e =
        if ∀ i, 0 ≤ e i then P (fun i => (e i).toNat) else 0) ∧
      (∀ a, P a ≠ 0 → totalExponent (D5.S3.VertexAlgebra.UniformGradedLocalCorrelator.naturalExponent a) = numeratorDegree D d) ∧
      (∀ a, P a ∈ W) ∧ (numeratorDegree D d < 0 → P = 0) ∧
      ∀ sigma : Equiv.Perm (Fin n),
        scalarWordCarrier n D.field sigma D.vacuum (lambda.comp selector.map) =
          orderedRationalFor ℂ n sigma
            (algebraMap _ (CommonRational ℂ n) (scalarNumerator ℂ P lambda) /
              algebraMap _ (CommonRational ℂ n) (clearingPolynomial n D.localityOrder)) := by
  obtain ⟨P, hclear, hdeg, hW, hnegative⟩ :=
    uniform_graded_local_correlator D d selector order nodup all_labels W in_W
  refine ⟨P, hclear, hdeg, hW, hnegative, ?_⟩
  intro sigma
  apply actual_expansion_of_certificate n D d selector sigma lambda P
  · exact originalQ_ne_zero n z D.localityOrder
  · exact hclear (List.ofFn sigma) (supplier_order_perm order nodup all_labels sigma)

end SupportedWordRationalCollision.ActualRationalReconstruction
end

section
/- Application to the actual finite numerator returned by the frozen native
graded-local-field supplier. This is still a generic field theorem, not an
identification of V^natural, its Y, grading, PCT, or fused-state grading law. -/
namespace SupportedWordRationalCollision.NativeNumeratorCollision
open CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry OrderedCollisionCoordinates.AdjacentFullOrders
open SupportedWordRationalCollision.VectorNumeratorScalarization
open D5.S3.VertexAlgebra
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module ℂ V]


/-- The rational is coefficientwise lambda(numerator)/the exact native Q.
Its numerator is supplied by actual locality, creation, and covariance, and
the collision retains the complete orders and every residue weight. -/
theorem actual_supplier_collision (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
    (hx : tau ⟨pre, by omega⟩ = x)
    (D : UniformGradedLocalCorrelator.GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : UniformGradedLocalCorrelator.OutputGradeSelector D.energy d)
    (order : List (Fin ((pre + 2) + post)))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (W : Submodule ℂ V)
    (in_W : ∀ e, UniformGradedLocalCorrelator.coefficientDistribution D.field D.vacuum selector.map order e ∈ W)
    (lambda : V →ₗ[ℂ] ℂ) :
    ∃ numerator : UniformGradedLocalCorrelator.VectorPolynomial ((pre + 2) + post) V,
      ((∀ other : List (Fin ((pre + 2) + post)), order.Perm other →
        ∀ e : UniformGradedLocalCorrelator.Exponent ((pre + 2) + post),
          UniformGradedLocalCorrelator.polynomialAction (UniformGradedLocalCorrelator.clearingPolynomial ((pre + 2) + post) D.localityOrder)
            (UniformGradedLocalCorrelator.coefficientDistribution D.field D.vacuum selector.map other) e =
          if ∀ i, 0 ≤ e i then numerator (fun i => (e i).toNat) else 0) ∧
      (∀ a : Fin ((pre + 2) + post) → ℕ, numerator a ≠ 0 →
        UniformGradedLocalCorrelator.totalExponent (UniformGradedLocalCorrelator.naturalExponent a) = UniformGradedLocalCorrelator.numeratorDegree D d) ∧
      (∀ a, numerator a ∈ W) ∧
      (UniformGradedLocalCorrelator.numeratorDegree D d < 0 → numerator = 0)) ∧
      CollisionStatement ℂ pre post z tau x
        (scalarNumerator ℂ numerator lambda) D.localityOrder := by
  obtain ⟨numerator, hnum⟩ := UniformGradedLocalCorrelator.uniform_graded_local_correlator
    D d selector order nodup all_labels W in_W
  refine ⟨numerator, hnum, ?_⟩
  exact RationalCollision.FullCollisionAssembly.required_proved ℂ pre post z tau x
    (scalarNumerator ℂ numerator lambda) D.localityOrder hx
    (fun e he => scalarNumerator_nonnegative ℂ numerator lambda e he z)

end SupportedWordRationalCollision.NativeNumeratorCollision
end

section
/-!
Actual generic graded-local-field collision. Every supported word below is
constructed from Carnahan's genuine HVertexOperator composition and the actual
D.field/D.vacuum. The finite numerator is returned by the frozen graded-local
supplier; its original i<j denominator is cancelled only in the Hahn field.
This proves neither a Moonshine identification nor an actual iterate/fused state.
-/
namespace SupportedWordRationalCollision.ActualWordCollision
open SupportedFieldWords.ActualFieldWordAdapter SupportedWordRationalCollision.ActualPolynomialBridge SupportedWordRationalCollision.ActualRationalReconstruction
open SupportedWordRationalCollision.ActualOrderedCoordinates SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders LabelledRationalClearing.GlobalRationalCurry
open SupportedWordRationalCollision.VectorNumeratorScalarization LabelledRationalClearing.WeightedActualQ OrderedCollisionCoordinates.LocalResidueCurrying
open CollisionRationalExpansions.HahnFiberResidue RationalCollision.CompleteExpansionCollision CollisionRationalExpansions.FullOrderSpectatorPole
open D5.S3.VertexAlgebra.UniformGradedLocalCorrelator
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual first full supported order pre,z,x,post. -/
def firstActualWord (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z)
    (D : GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (lambda : V →ₗ[ℂ] ℂ) :=
  scalarWordCarrier ((pre + 2) + post) D.field (firstOrder pre post z tau)
    D.vacuum (lambda.comp selector.map)
/-- The actual second full supported order pre,x,z,post. -/
def secondActualWord (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z)
    (D : GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (lambda : V →ₗ[ℂ] ℂ) :=
  scalarWordCarrier ((pre + 2) + post) D.field (secondOrder pre post z tau)
    D.vacuum (lambda.comp selector.map)

theorem firstActualWord_coeff (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z)
    (D : GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (lambda : V →ₗ[ℂ] ℂ)
    (e : Fin ((pre + 2) + post) → ℤ) :
    (firstActualWord pre post z tau D d selector lambda).coeff (firstExponents pre post z tau e) =
      lambda (coefficientDistribution D.field D.vacuum selector.map
        (List.ofFn (firstOrder pre post z tau)) e) := by
  rw [← firstOrder_equiv]
  exact scalarWordCarrier_actual_coeff _ D selector _ lambda e

theorem secondActualWord_coeff (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z)
    (D : GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (lambda : V →ₗ[ℂ] ℂ)
    (e : Fin ((pre + 2) + post) → ℤ) :
    (secondActualWord pre post z tau D d selector lambda).coeff (fullExponents (pre + 1) post z tau e) =
      lambda (coefficientDistribution D.field D.vacuum selector.map
        (List.ofFn (secondOrder pre post z tau)) e) := by
  rw [← secondOrder_equiv]
  exact scalarWordCarrier_actual_coeff _ D selector _ lambda e

/-- The same genuine supplier numerator identifies both actual words, and
transports the complete supported collision for every integer residue weight.
All remaining labels and exponents remain quantified; no finite cutoff occurs. -/
theorem actual_word_collision (pre post : ℕ) (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
    (hx : tau ⟨pre, by omega⟩ = x)
    (D : GradedLocalFields ((pre + 2) + post) V) (d : ℤ)
    (selector : OutputGradeSelector D.energy d) (order : List (Fin ((pre + 2) + post)))
    (nodup : order.Nodup) (all_labels : ∀ i, i ∈ order)
    (W : Submodule ℂ V)
    (in_W : ∀ e, coefficientDistribution D.field D.vacuum selector.map order e ∈ W)
    (lambda : V →ₗ[ℂ] ℂ) :
    ∃ P : VectorPolynomial ((pre + 2) + post) V,
      (∀ other : List (Fin ((pre + 2) + post)), order.Perm other → ∀ e : Fin ((pre + 2) + post) → ℤ,
        polynomialAction (clearingPolynomial ((pre + 2) + post) D.localityOrder)
          (coefficientDistribution D.field D.vacuum selector.map other) e =
        if ∀ i, 0 ≤ e i then P (fun i => (e i).toNat) else 0) ∧
      (∀ a, P a ≠ 0 → totalExponent (D5.S3.VertexAlgebra.UniformGradedLocalCorrelator.naturalExponent a) = numeratorDegree D d) ∧
      (∀ a, P a ∈ W) ∧ (numeratorDegree D d < 0 → P = 0) ∧
      firstActualWord pre post z tau D d selector lambda =
        firstRational ℂ pre post z tau
          (globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder) ∧
      secondActualWord pre post z tau D d selector lambda =
        secondRational ℂ pre post z tau
          (globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder) ∧
      (∀ r : ℤ,
        let R := globalDiagonal ℂ z x ^ r *
          globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder
        (fusedLocalSeries ℂ (pre + 1) post z x tau R).coeff (-1) =
          pullFiber (firstEmbedding pre post (-1))
            ((firstRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
              firstActualWord pre post z tau D d selector lambda) -
          residue (pre + 1) post
            ((secondRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
              secondActualWord pre post z tau D d selector lambda)) ∧
      (∀ (r : ℤ) (e : Remaining z → ℤ),
        let R := globalDiagonal ℂ z x ^ r *
          globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder
        ((fusedLocalSeries ℂ (pre + 1) post z x tau R).coeff (-1)).coeff
            (remainingExponents (pre + 1) post z tau e) =
          (pullFiber (firstEmbedding pre post (-1))
            ((firstRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
              firstActualWord pre post z tau D d selector lambda)).coeff
              (remainingExponents (pre + 1) post z tau e) -
          (residue (pre + 1) post
            ((secondRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
              secondActualWord pre post z tau D d selector lambda)).coeff
              (remainingExponents (pre + 1) post z tau e)) := by
  obtain ⟨P, hc, hd, hW, hn, he⟩ := actual_all_order_expansion
    ((pre + 2) + post) D d selector order nodup all_labels W in_W lambda z
  have hf : firstActualWord pre post z tau D d selector lambda =
      firstRational ℂ pre post z tau
        (globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder) := by
    rw [← firstOrder_rational]
    exact he (firstOrder pre post z tau)
  have hs : secondActualWord pre post z tau D d selector lambda =
      secondRational ℂ pre post z tau
        (globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder) := by
    rw [← secondOrder_rational]
    exact he (secondOrder pre post z tau)
  have hseries (r : ℤ) :
      (fusedLocalSeries ℂ (pre + 1) post z x tau
        (globalDiagonal ℂ z x ^ r * globalCorrelator ℂ pre post (scalarNumerator ℂ P lambda) D.localityOrder)).coeff (-1) =
      pullFiber (firstEmbedding pre post (-1))
        ((firstRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
          firstActualWord pre post z tau D d selector lambda) -
      residue (pre + 1) post
        ((secondRational ℂ pre post z tau (globalDiagonal ℂ z x)) ^ r *
          secondActualWord pre post z tau D d selector lambda) := by
    simpa only [hf, hs, map_mul, map_zpow₀] using
      (complete_expansion_collision ℂ pre post z tau x hx
        (scalarNumerator ℂ P lambda) D.localityOrder
        (fun e he => scalarNumerator_nonnegative ℂ P lambda e he z) r)
  refine ⟨P, hc, hd, hW, hn, hf, hs, hseries, ?_⟩
  intro r e
  simpa only [HahnSeries.coeff_sub] using
    congrArg (fun F => F.coeff (remainingExponents (pre + 1) post z tau e)) (hseries r)

end SupportedWordRationalCollision.ActualWordCollision
end

end D5.S3.VertexAlgebra
