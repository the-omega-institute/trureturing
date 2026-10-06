/- GID: D5/S3/VertexAlgebra/SupportedFieldWords
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SupportedFieldWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supported field words and finite labelled convolution. -/

/-
Actual supported field words and finite labelled convolution.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic.Abel
import D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- Binding of Carnahan's actual HVertexOperator composition, at arbitrary
finite rank. Coefficients remain actual products on the fixed suffix vector. -/
namespace SupportedFieldWords.OrderedWords
set_option backward.isDefEq.respectTransparency false
open scoped VertexOperator

def Indices : ℕ → Type
  | 0 => Unit
  | n + 1 => ℤ ×ₗ Indices n

instance indicesOrder (n : ℕ) : LinearOrder (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (LinearOrder Unit)
  | succ n ih => exact inferInstanceAs (LinearOrder (ℤ ×ₗ Indices n))

instance indicesGroup (n : ℕ) : AddCommGroup (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (AddCommGroup Unit)
  | succ n ih => exact inferInstanceAs (AddCommGroup (ℤ ×ₗ Indices n))

instance indicesOrdered (n : ℕ) : IsOrderedAddMonoid (Indices n) := by
  induction n with
  | zero => exact inferInstanceAs (IsOrderedAddMonoid Unit)
  | succ n ih => exact inferInstanceAs (IsOrderedAddMonoid (ℤ ×ₗ Indices n))

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def emptyField : HVertexOperator Unit K V V where
  toFun v := HahnModule.of K (HahnSeries.single () v)
  map_add' := by intros; ext g; simp
  map_smul' := by
    intro a v
    ext g
    cases g
    rw [HahnModule.of_symm_smul]
    simp

def ordered : (n : ℕ) → (Fin n → VertexOperator K V) → HVertexOperator (Indices n) K V V
  | 0, _ => emptyField
  | n + 1, A => HVertexOperator.comp
      (ordered n (fun i => A i.castSucc)) (A (Fin.last n))

def exponents : (n : ℕ) → (Fin n → ℤ) → Indices n
  | 0, _ => ()
  | n + 1, e => toLex (e (Fin.last n), exponents n (fun i => e i.castSucc))

def actualWord : (n : ℕ) → (Fin n → VertexOperator K V) → (Fin n → ℤ) → V → V
  | 0, _, _, c => c
  | n + 1, A, e, c => actualWord n (fun i => A i.castSucc) (fun i => e i.castSucc)
      ((A (Fin.last n) [[-e (Fin.last n) - 1]]) c)

/-- Every finite actual mode word embeds into the chosen ordered supported
Hahn carrier. Outer/smaller exponents have priority, from the word's right. -/
theorem ordered_coeff (n : ℕ) (A : Fin n → VertexOperator K V) (e : Fin n → ℤ) (c : V) :
    HVertexOperator.coeff (ordered n A) (exponents n e) c = actualWord n A e c := by
  induction n generalizing c with
  | zero =>
    change (HahnSeries.single () c).coeff () = c
    exact HahnSeries.coeff_single_same _ _
  | succ n ih =>
    change HVertexOperator.coeff
      (HVertexOperator.comp (ordered n (fun i => A i.castSucc)) (A (Fin.last n)))
      (toLex (e (Fin.last n), exponents n (fun i => e i.castSucc))) c = _
    rw [HVertexOperator.coeff_comp]
    simp only [LinearMap.comp_apply, VertexOperator.coeff_eq_ncoeff]
    exact ih _ _ _

/-- A prefix scalar functional and a grade selector compose at the terminal
coefficient; they do not change the supported input word. -/
def scalarOrdered (n : ℕ) (A : Fin n → VertexOperator K V) (c : V)
    (phi : V →ₗ[K] K) : HahnSeries (Indices n) K :=
  ((HahnModule.of K).symm (ordered n A c)).map phi

theorem scalarOrdered_coeff (n : ℕ) (A : Fin n → VertexOperator K V) (e : Fin n → ℤ)
    (c : V) (phi : V →ₗ[K] K) :
    (scalarOrdered n A c phi).coeff (exponents n e) = phi (actualWord n A e c) := by
  change phi (HVertexOperator.coeff (ordered n A) (exponents n e) c) = _
  rw [ordered_coeff]

end SupportedFieldWords.OrderedWords
end

section
/- Finite-convolution interface adapted from native
UniformGradedLocalCorrelator.shift/polynomialAction, with arbitrary ordered
exponent group and scalar field. No cancellation is used on unrestricted
coefficient distributions. Cancellation occurs only in HahnModule. -/
namespace SupportedFieldWords.FiniteConvolution
variable {Γ K V : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [AddCommGroup V] [Module K V]

abbrev Polynomial := AddMonoidAlgebra K Γ
abbrev Distribution := Γ → V

def shift (b : Γ) : Module.End K (Distribution (Γ := Γ) (V := V)) where
  toFun F := fun e => F (e-b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shifts : Multiplicative Γ →* Module.End K (Distribution (Γ := Γ) (V := V)) where
  toFun b := shift b.toAdd
  map_one' := by ext F e; simp [shift]
  map_mul' b c := by
    ext F e
    change F (e-(b.toAdd+c.toAdd)) = F ((e-b.toAdd)-c.toAdd)
    congr 1
    abel

def distributionAction : Polynomial (Γ := Γ) (K := K) →ₐ[K]
    Module.End K (Distribution (Γ := Γ) (V := V)) :=
  AddMonoidAlgebra.lift K _ _ shifts

def scalarMonomials : Multiplicative Γ →* HahnSeries Γ K where
  toFun b := HahnSeries.single b.toAdd 1
  map_one' := by simp [← HahnSeries.C_apply]
  map_mul' b c := by simp [HahnSeries.single_mul_single]

def scalarPolynomial : Polynomial (Γ := Γ) (K := K) →ₐ[K] HahnSeries Γ K :=
  AddMonoidAlgebra.lift K _ _ scalarMonomials

def coefficients (F : HahnModule Γ K V) : Distribution (Γ := Γ) (V := V) :=
  ((HahnModule.of K).symm F).coeff

lemma scalarPolynomial_single (b : Γ) (a : K) :
    scalarPolynomial (AddMonoidAlgebra.single b a) = HahnSeries.single b a := by
  simp only [scalarPolynomial, AddMonoidAlgebra.lift_single, scalarMonomials,
    MonoidHom.coe_mk, OneHom.coe_mk]
  ext e
  simp [HahnSeries.coeff_smul, HahnSeries.coeff_single]

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
lemma distributionAction_single (b : Γ) (a : K) (F : Distribution (Γ := Γ) (V := V)) (e : Γ) :
    distributionAction (AddMonoidAlgebra.single b a) F e = a • F (e-b) := by
  simp [distributionAction, AddMonoidAlgebra.lift_single, shifts, shift]

lemma coefficients_single_smul (b : Γ) (a : K) (F : HahnModule Γ K V) (e : Γ) :
    coefficients (HahnSeries.single b a • F) e = a • coefficients F (e-b) := by
  have h := HahnModule.coeff_single_smul_vadd (r := a) (x := F) (b := b) (a := e-b)
  change ((HahnModule.of K).symm (HahnSeries.single b a • F)).coeff (b+(e-b)) = _ at h
  simpa [coefficients] using h

theorem scalarPolynomial_coeff (Q : Polynomial (Γ := Γ) (K := K)) (e : Γ) :
    (scalarPolynomial Q).coeff e = Q.coeff e := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp [hP, hQ]
  | single b a => simp [scalarPolynomial_single, HahnSeries.coeff_single, Finsupp.single_apply, eq_comm]

lemma scalarPolynomial_ne_zero (Q : Polynomial (Γ := Γ) (K := K)) (hQ : Q ≠ 0) :
    scalarPolynomial Q ≠ 0 := by
  intro h
  apply hQ
  ext e
  rw [← scalarPolynomial_coeff, h]
  rfl

/-- Finite convolution on project-style coefficient distributions agrees with
scalar multiplication of actual supported series, for every finite polynomial. -/
theorem supported_finite_convolution (Q : Polynomial (Γ := Γ) (K := K))
    (F : HahnModule Γ K V) :
    coefficients (scalarPolynomial Q • F) = distributionAction Q (coefficients F) := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => ext e; simp [coefficients]
  | add P Q hP hQ =>
    ext e
    simp only [map_add, add_smul, coefficients, HahnModule.of_symm_add,
      HahnSeries.coeff_add, LinearMap.add_apply]
    change coefficients (scalarPolynomial P • F) e +
      coefficients (scalarPolynomial Q • F) e = _
    rw [hP, hQ]
    rfl
  | single b a =>
    ext e
    rw [scalarPolynomial_single, coefficients_single_smul, distributionAction_single]

/-- The rational scalar Q can be cancelled only after entering the supported
module over the genuine Hahn field. -/
theorem supported_clearing_unique (Q : Polynomial (Γ := Γ) (K := K))
    (hQ : scalarPolynomial Q ≠ 0) (F G : HahnModule Γ K V)
    (h : distributionAction Q (coefficients F) = distributionAction Q (coefficients G)) :
    F = G := by
  have hcoeff : coefficients (scalarPolynomial Q • F) =
      coefficients (scalarPolynomial Q • G) := by
    rw [supported_finite_convolution, supported_finite_convolution, h]
  have hfg : scalarPolynomial Q • F = scalarPolynomial Q • G :=
    HahnModule.ext _ _ hcoeff
  have hi := congrArg (fun X : HahnModule Γ K V => (scalarPolynomial Q)⁻¹ • X) hfg
  simpa only [← mul_smul, inv_mul_cancel₀ hQ, one_smul] using hi

/-- Exact division reconstruction in the supported module. Here P may be the
embedded finite numerator from the native supplier. -/
theorem supported_rational_reconstruction (Q : Polynomial (Γ := Γ) (K := K)) (hQ : Q ≠ 0)
    (F P : HahnModule Γ K V)
    (h : distributionAction Q (coefficients F) = coefficients P) :
    F = (scalarPolynomial Q)⁻¹ • P := by
  have hQP : distributionAction Q (coefficients ((scalarPolynomial Q)⁻¹ • P)) =
      coefficients P := by
    rw [← supported_finite_convolution, ← mul_smul,
      mul_inv_cancel₀ (scalarPolynomial_ne_zero Q hQ), one_smul]
  apply supported_clearing_unique Q (scalarPolynomial_ne_zero Q hQ)
  rw [h, hQP]

end SupportedFieldWords.FiniteConvolution
end

section
namespace SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.OrderedWords SupportedFieldWords.FiniteConvolution
set_option backward.isDefEq.respectTransparency false

def inverseExponents : (n : ℕ) → Indices n → (Fin n → ℤ)
  | 0, _ => fun i => Fin.elim0 i
  | n+1, g => Fin.lastCases (ofLex g).1 (inverseExponents n (ofLex g).2)

lemma inverse_exponents (n : ℕ) (e : Fin n → ℤ) :
    inverseExponents n (exponents n e) = e := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    simp only [exponents, inverseExponents, ofLex_toLex, ih]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma exponents_inverse (n : ℕ) (g : Indices n) :
    exponents n (inverseExponents n g) = g := by
  induction n with
  | zero => change () = g; cases g; rfl
  | succ n ih =>
    change toLex ((inverseExponents (n+1) g) (Fin.last n),
      exponents n (fun i => inverseExponents (n+1) g i.castSucc)) = g
    simp only [inverseExponents, Fin.lastCases_last, Fin.lastCases_castSucc, ih]
    rfl

lemma exponents_add (n : ℕ) (e f : Fin n → ℤ) :
    exponents n (e+f) = exponents n e + exponents n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change toLex (e (Fin.last n)+f (Fin.last n),
      exponents n ((fun i => e i.castSucc)+(fun i => f i.castSucc))) = _
    rw [ih]
    rfl

/-- Exact additive reindexing from the native distribution exponent type.
The last word variable becomes the first/outer lex exponent. -/
def exponentAddEquiv (n : ℕ) : (Fin n → ℤ) ≃+ Indices n where
  toFun := exponents n
  invFun := inverseExponents n
  left_inv := inverse_exponents n
  right_inv := exponents_inverse n
  map_add' := exponents_add n

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def labelledPolynomial (n : ℕ) :
    AddMonoidAlgebra K (Fin n → ℤ) →ₐ[K] AddMonoidAlgebra K (Indices n) :=
  AddMonoidAlgebra.mapDomainAlgHom K K (exponentAddEquiv n).toAddMonoidHom

/-- The actual finite mode word is represented in the same field-module
carrier on which the finite-convolution theorem applies. -/
theorem actual_supported_word (n : ℕ) (A : Fin n → VertexOperator K V) (c : V)
    (e : Fin n → ℤ) :
    coefficients (ordered n A c) (exponentAddEquiv n e) = actualWord n A e c := by
  exact ordered_coeff n A e c

/-- Applying any reindexed finite clearing polynomial really acts by scalar
convolution on the supported actual product. -/
theorem actual_supported_clearing (n : ℕ) (A : Fin n → VertexOperator K V) (c : V)
    (Q : AddMonoidAlgebra K (Fin n → ℤ)) :
    coefficients (scalarPolynomial (labelledPolynomial n Q) • ordered n A c) =
      distributionAction (labelledPolynomial n Q) (coefficients (ordered n A c)) :=
  supported_finite_convolution _ _

def transportDistribution (n : ℕ) (F : (Fin n → ℤ) → V) : Indices n → V :=
  fun g => F ((exponentAddEquiv n).symm g)

/-- Reindexing preserves the exact finite shift convention e-b used by the
native polynomialAction. No reversal of a mode sign is hidden here. -/
theorem clearing_transport (n : ℕ) (Q : AddMonoidAlgebra K (Fin n → ℤ))
    (F : (Fin n → ℤ) → V) :
    distributionAction (labelledPolynomial n Q) (transportDistribution n F) =
      transportDistribution n (distributionAction Q F) := by
  classical
  induction Q using AddMonoidAlgebra.induction_linear with
  | zero => ext g; simp [transportDistribution]
  | add P Q hP hQ =>
    ext g
    simp only [map_add, LinearMap.add_apply]
    change distributionAction (labelledPolynomial n P) (transportDistribution n F) g +
      distributionAction (labelledPolynomial n Q) (transportDistribution n F) g = _
    rw [hP, hQ]
    rfl
  | single b a =>
    ext g
    have hm : labelledPolynomial n (AddMonoidAlgebra.single b a) =
        AddMonoidAlgebra.single (exponentAddEquiv n b) a := by
      simp [labelledPolynomial]
    rw [hm, distributionAction_single]
    change a • F ((exponentAddEquiv n).symm (g-exponentAddEquiv n b)) =
      distributionAction (AddMonoidAlgebra.single b a) F ((exponentAddEquiv n).symm g)
    rw [distributionAction_single, map_sub, AddEquiv.symm_apply_apply]

/-- Exact interface for the labelled QF=P identity: first reindex the labelled actual
product, then apply the scalar Q in the supported module. -/
theorem labelled_actual_clearing (n : ℕ) (A : Fin n → VertexOperator K V) (c : V)
    (Q : AddMonoidAlgebra K (Fin n → ℤ)) :
    coefficients (scalarPolynomial (labelledPolynomial n Q) • ordered n A c) =
      transportDistribution n (distributionAction Q (fun e => actualWord n A e c)) := by
  have hc : coefficients (ordered n A c) =
      transportDistribution n (fun e => actualWord n A e c) := by
    funext g
    have h := actual_supported_word n A c ((exponentAddEquiv n).symm g)
    simpa only [AddEquiv.apply_symm_apply, transportDistribution] using h
  rw [supported_finite_convolution, hc, clearing_transport]

end SupportedFieldWords.OrderedDistribution
end

section
/-!
  Native adapter for the actual graded-local-field words.

  The supplier theorem works with `word` on a labelled list, whereas the
  Hahn carrier supplied by Carnahan's `HVertexOperator` is indexed by a
  finite coordinate function.  The lemmas below identify those two objects
  coefficient by coefficient, including the exact mode convention `-e-1`.
  No support or expansion equality is assumed: support comes from the
  `ordered` HVertexOperator itself.
-/
namespace SupportedFieldWords.ActualFieldWordAdapter
open scoped VertexOperator

open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open D5.S3.VertexAlgebra
open D5.S3.VertexAlgebra.UniformGradedLocalCorrelator

set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem word_append_adapter {N : ℕ} (A : Fin N → VertexOperator ℂ V)
    (l r : List (Fin N)) (e : Fin N → ℤ) :
    word A (l ++ r) e = word A l e * word A r e := by
  induction l with
  | nil => rw [show word A [] e = 1 by rfl]; simp
  | cons i l ih => simp [word, ih, mul_assoc]

/- The list word and the finite HVertexOperator word agree for an arbitrary
   injective or non-injective coordinate map.  Generalising the coordinate
   map (rather than assuming a permutation) is what makes the induction on
   `List.ofFn_succ'` exact. -/
theorem word_ofFn (n N : ℕ)
    (A : Fin N → VertexOperator ℂ V) (f : Fin n → Fin N)
    (e : Fin N → ℤ) (c : V) :
    (word (fun i => A i) (List.ofFn f) e) c =
      actualWord n (fun i => A (f i)) (fun i => e (f i)) c := by
  induction n generalizing c with
  | zero =>
      simp [List.ofFn_zero, word, actualWord]
  | succ n ih =>
      rw [List.ofFn_succ']
      rw [List.concat_eq_append]
      rw [word_append_adapter]
      change
        (word (fun i => A i) (List.ofFn (fun i : Fin n => f i.castSucc)) e)
            ((A (f (Fin.last n)) [[-e (f (Fin.last n)) - 1]]) c) = _
      rw [ih]
      rfl

/- The actual scalar carrier for a chosen labelled order.  The order is
   represented by `f : Fin n -> ι`; its Hahn support is inherited from the
   genuine ordered HVertexOperator, not postulated. -/
def scalarWordCarrier (n : ℕ) {N : ℕ}
    (A : Fin N → VertexOperator ℂ V) (f : Fin n → Fin N) (c : V)
    (phi : V →ₗ[ℂ] ℂ) : HahnSeries (Indices n) ℂ :=
  scalarOrdered n (fun i => A (f i)) c phi

theorem scalarWordCarrier_coeff (n : ℕ) {N : ℕ}
    (A : Fin N → VertexOperator ℂ V) (f : Fin n → Fin N)
    (c : V) (phi : V →ₗ[ℂ] ℂ) (e : Fin N → ℤ) :
    (scalarWordCarrier n A f c phi).coeff
        (exponents n (fun i => e (f i))) =
      phi ((word (fun i => A i) (List.ofFn f) e) c) := by
  rw [scalarWordCarrier, scalarOrdered_coeff]
  rw [word_ofFn]

/- Specialisation to the actual D/selector output.  This is the exact
   coefficient requested by the adapter: lambda(selector.map(actual word)). -/
theorem scalarWordCarrier_actual_coeff (n : ℕ)
    (D : GradedLocalFields n V)
    {d : ℤ} (selector : OutputGradeSelector D.energy d)
    (f : Fin n → Fin n) (lambda : V →ₗ[ℂ] ℂ) (e : Fin n → ℤ) :
    (scalarWordCarrier n D.field f D.vacuum
      (lambda.comp selector.map)).coeff
        (exponents n (fun i => e (f i))) =
      lambda (coefficientDistribution D.field D.vacuum selector.map
        (List.ofFn f) e) := by
  rw [scalarWordCarrier_coeff]
  rfl


end SupportedFieldWords.ActualFieldWordAdapter
end

end D5.S3.VertexAlgebra
