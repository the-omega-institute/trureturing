/- GID: D5/S3/Arith/DiophantineApproximation/MvHasseDeriv
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/MvHasseDeriv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The multivariate Hasse derivative acts on monomials by binomial coefficients. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.ZMod.Basic

-- Used only by the acceptance criteria.

@[expose] public section

open Nat

noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The `μ`-th **Hasse derivative** `∂_μ = (1 / μ!) ∂^μ` of a polynomial in several variables,
defined on monomials by Bombieri–Gubler's (6.1),
`∂_μ (a X^m) = (∏ j, (m j).choose (μ j)) a X^(m - μ)`. The truncated subtraction is harmless: a
binomial coefficient `(m j).choose (μ j)` with `μ j > m j` vanishes. -/
def hasseDeriv (μ : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun m ↦
    monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) : R)

end MvPolynomial
