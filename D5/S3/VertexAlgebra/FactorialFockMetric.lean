/- GID: D5/S3/VertexAlgebra/FactorialFockMetric
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/FactorialFockMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.Basic, mathlib/module/Mathlib.Algebra.MvPolynomial.PDeriv, mathlib/module/Mathlib.Analysis.InnerProductSpace.l2Space]
   utility: none
   digest: An injective factorial coefficient embedding gives the polynomial Fock metric and creation-derivative pairing. -/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
This module transports the arbitrary-variable factorial polynomial metric.
Native compilation, axiom, registration and admission evidence is scoped
and recorded separately; none of these implies full-programme or CI acceptance.
Repository comparison pin: abb8bfb03a88bd17fb9f4a2f779ad0248813987c.
Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.

For arbitrary sigma, the carrier is exactly MvPolynomial sigma Complex.
The occupation weight is the product of factorials, with no finiteness or
nonemptiness assumption on sigma. The embedding multiplies each coefficient
by the real square root of its weight. The induced Core proves definiteness
using that embedding's injectivity. All induced instances stay local.
The inner product is conjugate linear first and linear second.

Proof provenance: retained statements and 31 normalized declaration bodies are
copied from the sealed 402-line TransientFactorialFockMetric.lean supplier;
inner_monomial_left instead computes the same basis coordinate directly with
repr_self, as disclosed in the SOURCE comparison. The supplier is
(SHA-256 0e0b1086fd2edacbc9ef87ddc2f9e105d48f0c61820e88f1e1e72a1a1a82a2a1).
Its historical header names repository pin 81bfc6f4cd608dc09a4bd35ba7767dcb6653c695;
that is provenance, not this module's comparison pin. Mathlib supplies the
monomial basis, unitsSMul/equiv, finite-support products, pderiv and l2 basis.
The supplier attributes the coefficient embedding architecture to its sealed
ActualHalfFockHilbertSource client; that client was not read or imported here.
The normalization is classical algebraic symmetric/Bargmann Fock normalization;
this task claims no literature novelty or newly accepted mathematical result.

Admission basis: mul_X_pderiv_pairing is the substantive all-polynomial
statement. Every other retained theorem is conservatively treated as a
consumed proof helper, not independent new mathematical content. The exact
consumer/admission map is supplied outside this mathematical module. Its
content classification is a semantic review obligation distinct from compilation.
This is general structural mathematics, not finite enumeration, a certified
instance, a checker or a numerical reduction (utility: none).

This unit constructs no VOA/current/Virasoro or charged/ground unitarity,
maximal analytic adjoint, Hilbert completion theorem or spacetime bridge.
-/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators InnerProductSpace lp Classical
open ComplexConjugate

namespace D5.S3.VertexAlgebra.FactorialFockMetric

universe u
variable {σ : Type u}

abbrev Occupation (σ : Type u) := σ →₀ ℕ

abbrev Polynomial (σ : Type u) := MvPolynomial σ ℂ

abbrev Hilbert (σ : Type u) := ℓ²(Occupation σ, ℂ)

/-- Occupation factorial, including the empty occupation. -/
def weight (d : Occupation σ) : ℕ := d.prod fun _ n => n.factorial

theorem weight_pos (d : Occupation σ) : 0 < weight d := by
  classical
  unfold weight Finsupp.prod
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem weight_eq_prod (d : Occupation σ) (s : Finset σ)
    (hs : d.support ⊆ s) : weight d = ∏ x ∈ s, (d x).factorial := by
  exact Finsupp.prod_of_support_subset d hs (fun _ n => n.factorial) (by simp)

/-- The exact creation/annihilation normalization recurrence. -/
theorem weight_add_single (d : Occupation σ) (i : σ) :
    weight (d + Finsupp.single i 1) = (d i + 1) * weight d := by
  classical
  let s := insert i d.support
  have hi : i ∈ s := Finset.mem_insert_self _ _
  have hd : d.support ⊆ s := Finset.subset_insert _ _
  have hds : (d + Finsupp.single i 1).support ⊆ s := by
    intro x hx
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx | hx
    · exact Finset.mem_insert_of_mem hx
    · have hxi : x = i := Finset.mem_singleton.mp (Finsupp.support_single_subset hx)
      subst x
      exact hi
  have hrest :
      (∏ x ∈ s.erase i, ((d + Finsupp.single i 1 : Occupation σ) x).factorial) =
        ∏ x ∈ s.erase i, (d x).factorial := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
    simp [Finsupp.single_apply, hxi, Ne.symm hxi]
  rw [weight_eq_prod _ s hds, weight_eq_prod d s hd,
    ← Finset.mul_prod_erase s (fun x => ((d + Finsupp.single i 1 : Occupation σ) x).factorial) hi,
    ← Finset.mul_prod_erase s (fun x => (d x).factorial) hi]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [Nat.factorial_succ]
  exact mul_assoc _ _ _

/-- Real square-root diagonal used to embed the positive form into l2. -/
def scale (d : Occupation σ) : ℂ := (Real.sqrt (weight d : ℝ) : ℂ)

theorem scale_ne_zero (d : Occupation σ) : scale d ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast weight_pos d))

@[simp] theorem conj_scale (d : Occupation σ) : conj (scale d) = scale d := by
  simp [scale]

theorem scale_mul_self (d : Occupation σ) : scale d * scale d = (weight d : ℂ) := by
  have h : Real.sqrt (weight d : ℝ) * Real.sqrt (weight d : ℝ) = (weight d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold scale
  exact_mod_cast h

def scaleUnit (d : Occupation σ) : ℂˣ := Units.mk0 (scale d) (scale_ne_zero d)

def scaledBasis (σ : Type u) : Module.Basis (Occupation σ) ℂ (Polynomial σ) :=
  (MvPolynomial.basisMonomials σ ℂ).unitsSMul scaleUnit

/-- An algebraic linear equivalence, not an algebra map or a bounded operator. -/
def diagonal (σ : Type u) : Polynomial σ ≃ₗ[ℂ] Polynomial σ :=
  (MvPolynomial.basisMonomials σ ℂ).equiv (scaledBasis σ) (Equiv.refl _)

theorem diagonal_basis (d : Occupation σ) :
    diagonal σ (MvPolynomial.monomial d 1) =
      scale d • MvPolynomial.monomial d 1 := by
  change (MvPolynomial.basisMonomials σ ℂ).equiv (scaledBasis σ)
      (Equiv.refl _) ((MvPolynomial.basisMonomials σ ℂ) d) =
    scale d • (MvPolynomial.basisMonomials σ ℂ) d
  rw [Module.Basis.equiv_apply]
  simp [scaledBasis, Module.Basis.unitsSMul_apply, scaleUnit, Units.smul_def]

theorem diagonal_monomial (d : Occupation σ) (a : ℂ) :
    diagonal σ (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (scale d * a) := by
  have h : MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial, smul_eq_mul]
  rw [h, map_smul, diagonal_basis]
  simp [smul_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

theorem diagonal_coeff (p : Polynomial σ) (d : Occupation σ) :
    (diagonal σ p).coeff d = scale d * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    by_cases h : e = d
    · subst e
      simp [diagonal_monomial]
    · simp [diagonal_monomial, MvPolynomial.coeff_monomial, h]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The same l2 standard-basis primitive as in the sealed Hilbert client. -/
def hilbertBasis (σ : Type u) : HilbertBasis (Occupation σ) ℂ (Hilbert σ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

def coefficientEmbedding (σ : Type u) : Polynomial σ →ₗ[ℂ] Hilbert σ :=
  (Finsupp.linearCombination ℂ (hilbertBasis σ)).comp
    (MvPolynomial.basisMonomials σ ℂ).repr.toLinearMap

theorem coefficientEmbedding_basis (d : Occupation σ) :
    coefficientEmbedding σ ((MvPolynomial.basisMonomials σ ℂ) d) =
      hilbertBasis σ d := by
  classical
  change (Finsupp.linearCombination ℂ (hilbertBasis σ))
    ((MvPolynomial.basisMonomials σ ℂ).repr ((MvPolynomial.basisMonomials σ ℂ) d)) = _
  rw [Module.Basis.repr_self, Finsupp.linearCombination_single, one_smul]

theorem coefficientEmbedding_injective : Function.Injective (coefficientEmbedding σ) :=
  (hilbertBasis σ).orthonormal.linearIndependent.finsuppLinearCombination_injective.comp
    (MvPolynomial.basisMonomials σ ℂ).repr.injective

theorem coefficientEmbedding_monomial (d : Occupation σ) (a : ℂ) :
    coefficientEmbedding σ (MvPolynomial.monomial d a) = a • hilbertBasis σ d := by
  have h : MvPolynomial.monomial d a = a • (MvPolynomial.basisMonomials σ ℂ) d := by
    simp [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul]
  rw [h, map_smul, coefficientEmbedding_basis]

theorem coefficientEmbedding_coeff (p : Polynomial σ) (d : Occupation σ) :
    coefficientEmbedding σ p d = p.coeff d := by
  change (hilbertBasis σ).repr (coefficientEmbedding σ p) d = _
  rw [(hilbertBasis σ).repr_apply_apply]
  exact (hilbertBasis σ).orthonormal.inner_right_finsupp
    ((MvPolynomial.basisMonomials σ ℂ).repr p) d

/-- Injective finite-support Hilbert embedding with factorial diagonal. -/
def embedding (σ : Type u) : Polynomial σ →ₗ[ℂ] Hilbert σ :=
  (coefficientEmbedding σ).comp (diagonal σ).toLinearMap

theorem embedding_injective : Function.Injective (embedding σ) :=
  coefficientEmbedding_injective.comp (diagonal σ).injective

theorem embedding_coeff (p : Polynomial σ) (d : Occupation σ) :
    embedding σ p d = scale d * p.coeff d := by
  change coefficientEmbedding σ (diagonal σ p) d = _
  rw [coefficientEmbedding_coeff, diagonal_coeff]

theorem embedding_monomial (d : Occupation σ) (a : ℂ) :
    embedding σ (MvPolynomial.monomial d a) =
      (scale d * a) • hilbertBasis σ d := by
  change coefficientEmbedding σ (diagonal σ (MvPolynomial.monomial d a)) = _
  rw [diagonal_monomial, coefficientEmbedding_monomial]

/-- The positive factorial form, defined through an actual injective l2 map. -/
def inner (p q : Polynomial σ) : ℂ :=
  Inner.inner ℂ (embedding σ p) (embedding σ q)

/-- Use the actual induced-inner-product infrastructure, then prove definiteness.
The induced seminorm/inner instances are LOCAL to this construction. -/
def core (σ : Type u) : InnerProductSpace.Core ℂ (Polynomial σ) := by
  letI := SeminormedAddCommGroup.induced (Polynomial σ) (Hilbert σ) (embedding σ)
  letI : InnerProductSpace ℂ (Polynomial σ) := InnerProductSpace.induced (embedding σ)
  refine { __ := (PreInnerProductSpace.toCore :
      PreInnerProductSpace.Core ℂ (Polynomial σ)), definite := ?_ }
  intro p hp
  change Inner.inner ℂ (embedding σ p) (embedding σ p) = 0 at hp
  apply embedding_injective (σ := σ)
  rw [map_zero]
  exact inner_self_eq_zero.mp hp

/-- Sesquilinearity is inherited from the concrete l2 form. -/
theorem inner_add_first (p q r : Polynomial σ) :
    inner (p + q) r = inner p r + inner q r := by
  simp only [inner, map_add, inner_add_left]

/-- The factorial pairing of one monomial with an ARBITRARY polynomial. -/
theorem inner_monomial_left (d : Occupation σ) (a : ℂ) (q : Polynomial σ) :
    inner (MvPolynomial.monomial d a) q =
      (weight d : ℂ) * conj a * q.coeff d := by
  classical
  unfold inner
  rw [embedding_monomial, inner_smul_left]
  have hb : hilbertBasis σ d = lp.single 2 d (1 : ℂ) := by
    exact (hilbertBasis σ).repr_self d
  rw [hb, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, embedding_coeff,
    map_mul, conj_scale]
  calc
    scale d * conj a * (scale d * q.coeff d) =
        (scale d * scale d) * conj a * q.coeff d := by ring
    _ = _ := by rw [scale_mul_self]

/-- Creation and partial differentiation are formal adjoints on ALL polynomials.
No positivity, adjoint identity or coefficient-finiteness hypothesis is added. -/
theorem mul_X_pderiv_pairing (i : σ) (p q : Polynomial σ) :
    inner (MvPolynomial.X i * p) q = inner p (MvPolynomial.pderiv i q) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    have hm : MvPolynomial.X i * MvPolynomial.monomial d a =
        MvPolynomial.monomial (d + Finsupp.single i 1) a := by
      rw [MvPolynomial.X, MvPolynomial.monomial_mul]
      simp only [one_mul, add_comm]
    rw [hm, inner_monomial_left, inner_monomial_left,
      MvPolynomial.coeff_pderiv, weight_add_single]
    push_cast
    ring
  | add p r hp hr =>
    rw [mul_add, inner_add_first, hp, hr, inner_add_first]

end D5.S3.VertexAlgebra.FactorialFockMetric
