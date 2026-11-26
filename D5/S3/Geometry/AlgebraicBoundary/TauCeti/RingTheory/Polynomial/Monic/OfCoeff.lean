/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Monic/OfCoeff
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Monic/OfCoeff
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Monic/OfCoeff.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The monic polynomial with prescribed lower coefficients

A monic polynomial of degree `n` is exactly its `n` lower coefficients: the leading term is forced
to be `X ^ n`. This file names the resulting polynomial `TauCeti.Polynomial.monicOfCoeff c` for a
tuple `c : Fin n → R`, and records that reading the coefficients back off is inverse to it.

The point of naming it is that it is the object against which analytic dependence on the
coefficients is stated: `TauCeti/Analysis/Polynomial/SimpleRoots/Basic.lean` differentiates
`(c, z) ↦ (monicOfCoeff c).eval z` in `c` and `z` jointly, so the lower coefficients must appear as
a *free* tuple rather than as the data of a polynomial subtype.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace TauCeti

open Polynomial

namespace Polynomial

section OfCoeff

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The monic polynomial of degree `n` whose `n` lower coefficients are `c`, that is, the
specialization of Mathlib's `Polynomial.freeMonic` at the coefficient tuple `c`. It is the inverse
of the coefficient-reading half of `TauCeti.Sym.coeffEquiv`, and is the natural object to state
analytic dependence on the coefficients against: `TauCeti.Sym.coeffEquiv_symm_apply` describes the
inverse chart as its root multiset. -/
noncomputable def monicOfCoeff (c : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, monomial (i : ℕ) (c i)

/-- The lower part of `TauCeti.Polynomial.monicOfCoeff` has degree less than `n`, which is where its
monicity and its degree come from. -/
private theorem degree_sum_monomial_lt (c : Fin n → R) :
    degree (∑ i : Fin n, monomial (i : ℕ) (c i)) < n := by
  simpa only [C_mul_X_pow_eq_monomial] using degree_sum_fin_lt c

/-- The polynomial attached to a coefficient tuple is monic: its lower part has degree `< n`, so the
term `X ^ n` leads. -/
@[simp]
theorem monic_monicOfCoeff (c : Fin n → R) : (monicOfCoeff c).Monic :=
  monic_X_pow_add (degree_sum_monomial_lt c)

/-- The prescribed coefficients are read back off: this is the defining property of
`TauCeti.Polynomial.monicOfCoeff`. -/
@[simp]
theorem coeff_monicOfCoeff (c : Fin n → R) (i : Fin n) : (monicOfCoeff c).coeff (i : ℕ) = c i := by
  have hne : (i : ℕ) ≠ n := i.2.ne
  simp [monicOfCoeff, coeff_X_pow, coeff_monomial, hne, Fin.val_eq_val]

variable [Nontrivial R]

/-- The polynomial attached to a tuple of `n` coefficients has degree exactly `n`, the degree of its
leading term `X ^ n`. -/
@[simp]
theorem natDegree_monicOfCoeff (c : Fin n → R) : (monicOfCoeff c).natDegree = n := by
  have hlt : degree (∑ i : Fin n, monomial (i : ℕ) (c i)) < degree (X ^ n : R[X]) := by
    rw [degree_X_pow]
    exact degree_sum_monomial_lt c
  rw [monicOfCoeff, natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow]

/-- Every monic polynomial of degree `n` is the monic polynomial attached to its own lower
coefficients: together with `TauCeti.Polynomial.coeff_monicOfCoeff` this identifies the monic
polynomials of degree `n` with the coefficient tuples. -/
theorem monicOfCoeff_coeff {p : R[X]} (hp : p.Monic) (hdeg : p.natDegree = n) :
    monicOfCoeff (fun i : Fin n => p.coeff (i : ℕ)) = p := by
  refine Polynomial.ext fun k => ?_
  rcases lt_trichotomy k n with hk | hk | hk
  · exact coeff_monicOfCoeff _ ⟨k, hk⟩
  · have hlead : (monicOfCoeff fun i : Fin n => p.coeff (i : ℕ)).coeff n = 1 := by
      simpa [natDegree_monicOfCoeff] using
        (monic_monicOfCoeff fun i : Fin n => p.coeff (i : ℕ)).coeff_natDegree
    rw [hk, hlead, ← hdeg, hp.coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_monicOfCoeff]),
      coeff_eq_zero_of_natDegree_lt (by rwa [hdeg])]

end OfCoeff

end Polynomial

end TauCeti
