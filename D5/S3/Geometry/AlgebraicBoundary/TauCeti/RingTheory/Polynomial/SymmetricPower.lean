/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/SymmetricPower
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/SymmetricPower
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/SymmetricPower.lean.
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

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Data.Sym.Basic
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.MvPolynomial.Symmetric.Substitution
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.Data.Fin.VecNotation

/-!
# The symmetric power of a field, charted by elementary symmetric functions

A point of the `n`-th symmetric power `Sym R n` is an unordered `n`-tuple of scalars, and the monic
polynomial `∏_{a ∈ s} (X - a)` records exactly that information: its coefficients are the
elementary symmetric functions of the tuple, up to sign. Over an algebraically closed field the
correspondence is a bijection in both directions, and composing it with Mathlib's identification of
monic degree-`n` polynomials with their lower coefficients presents `Sym K n` as the affine space
`Fin n → K`.

This is the algebraic heart of the *symmetric product chart*: for a Riemann surface `Σ` the
symmetric product `Sym^g(Σ)` is given its complex manifold structure by exactly this map, read in a
holomorphic coordinate on `Σ` — a local identification `Sym^g(ℂ) ≅ ℂ^g` whose coordinates are the
elementary symmetric functions of the `g` points. Only the pointwise algebra is settled here, and
it takes no analytic input: everything below is a statement about polynomials over a commutative
ring or a field. The topology of `Sym^g(Σ)`, its complex structure, and the analysis that uses them
are separate later steps.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

open Multiset Polynomial

namespace TauCeti

namespace Sym

section Basic

variable {R : Type*} [CommRing R] {m n : ℕ}

/-! ### The monic polynomial of an unordered tuple -/

section Defs

variable [Nontrivial R]

/-- The monic polynomial `∏_{a ∈ s} (X - a)` of an unordered `n`-tuple `s`, bundled with its
monicity and the fact that its degree is `n`.

The underlying polynomial is Mathlib's `Polynomial.ofMultiset`; the point of the subtype is that
the degree is pinned to `n` rather than to the cardinality of the underlying multiset, which is
what `Polynomial.monicEquivDegreeLT` consumes. -/
@[expose]
noncomputable def toMonic (s : Sym R n) : { p : R[X] // p.Monic ∧ p.natDegree = n } :=
  ⟨ofMultiset (s : Multiset R), by simpa using monic_multisetProd_X_sub_C (s : Multiset R),
    by simp [Sym.card_coe]⟩

theorem coe_toMonic (s : Sym R n) : (toMonic s : R[X]) = ofMultiset (s : Multiset R) :=
  rfl

@[simp]
theorem monic_toMonic (s : Sym R n) : (toMonic s : R[X]).Monic :=
  (toMonic s).2.1

@[simp]
theorem natDegree_toMonic (s : Sym R n) : (toMonic s : R[X]).natDegree = n :=
  (toMonic s).2.2

/-- The monic polynomial of the unordered tuple underlying an ordered one `f : Fin n → R` is the
product of the corresponding linear factors. -/
theorem toMonic_ofFn (f : Fin n → R) : (toMonic (ofFn f) : R[X]) = ∏ i, (X - C (f i)) := by
  rw [coe_toMonic, coe_ofFn]
  simp [← List.prod_ofFn, List.map_ofFn, Function.comp_def]

end Defs

section Domain

variable [IsDomain R]

/-- Over an integral domain the points of a tuple are recovered, with multiplicity, as the roots of
its monic polynomial. -/
@[simp]
theorem roots_toMonic (s : Sym R n) : (toMonic s : R[X]).roots = (s : Multiset R) := by
  rw [coe_toMonic]
  exact roots_ofMultiset _

/-- A scalar lies in a tuple exactly when it is a root of the tuple's monic polynomial. -/
theorem mem_iff_isRoot {a : R} {s : Sym R n} :
    a ∈ (s : Multiset R) ↔ (toMonic s : R[X]).IsRoot a := by
  rw [← roots_toMonic s, mem_roots (monic_toMonic s).ne_zero]

end Domain

end Basic

/-! ### The chart over an algebraically closed field -/

section Components

variable {K : Type*} [Field K] {n : ℕ}

/-! Mathlib builds `Polynomial.monicEquivDegreeLT` and `Polynomial.degreeLTEquiv` as anonymous
structure instances and states no `apply` or `symm_apply` lemma for either — it unfolds their
definitions where it needs them, as in `Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean`. The
four lemmas here supply those missing component lemmas once, so that the chart proofs below rewrite
with named equations instead of reducing the composite equivalence. -/

/-- `Polynomial.degreeLTEquiv` reads off coefficients. -/
private theorem degreeLTEquiv_toEquiv_apply (p : degreeLT K n) (i : Fin n) :
    (degreeLTEquiv K n).toEquiv p i = (p : K[X]).coeff (i : ℕ) :=
  rfl

/-- `Polynomial.monicEquivDegreeLT` removes the leading term. -/
private theorem coe_monicEquivDegreeLT_apply (p : { p : K[X] // p.Monic ∧ p.natDegree = n }) :
    ((monicEquivDegreeLT n p : degreeLT K n) : K[X]) = (p : K[X]).eraseLead :=
  rfl

end Components

section AlgClosed

variable (K : Type*) [Field K] [IsAlgClosed K] (n : ℕ)

/-- Over an algebraically closed field, `TauCeti.Sym.toMonic` is a bijection from the `n`-th
symmetric power onto the monic polynomials of degree `n`, inverted by taking roots with
multiplicity. -/
@[expose]
noncomputable def monicEquiv : Sym K n ≃ { p : K[X] // p.Monic ∧ p.natDegree = n } where
  toFun := toMonic
  invFun p := Sym.mk p.1.roots <| by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits p.1), p.2.2]
  left_inv s := Sym.coe_injective (roots_toMonic s)
  right_inv p := Subtype.ext <| by
    rw [coe_toMonic]
    simpa using prod_multiset_X_sub_C_of_monic_of_roots_card_eq p.2.1
      (splits_iff_card_roots.mp (IsAlgClosed.splits p.1))

@[simp]
theorem monicEquiv_apply (s : Sym K n) : monicEquiv K n s = toMonic s :=
  rfl

/-- The **elementary symmetric chart** on the `n`-th symmetric power of an algebraically closed
field: an unordered `n`-tuple is determined by, and freely determines, the `n` lower coefficients of
its monic polynomial.

By `TauCeti.Sym.coeffEquiv_apply` the `i`-th coordinate is `(-1) ^ (n - i)` times the `(n - i)`-th
elementary symmetric function of the tuple. -/
noncomputable def coeffEquiv : Sym K n ≃ (Fin n → K) :=
  (monicEquiv K n).trans ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)

variable {K n}

/-- The chart reads off the lower coefficients of the monic polynomial of the tuple. -/
theorem coeffEquiv_apply_eq_coeff (s : Sym K n) (i : Fin n) :
    coeffEquiv K n s i = (toMonic s : K[X]).coeff i := by
  have hne : (i : ℕ) ≠ (toMonic s : K[X]).natDegree := by
    rw [natDegree_toMonic]
    exact i.2.ne
  rw [coeffEquiv, Equiv.trans_apply, Equiv.trans_apply, monicEquiv_apply,
    degreeLTEquiv_toEquiv_apply, coe_monicEquivDegreeLT_apply]
  exact eraseLead_coeff_of_ne _ hne

/-- The chart of an unordered tuple presented by an ordered one `f : Fin n → K` reads off the
coefficients of the product of the linear factors of `f`. -/
theorem coeffEquiv_ofFn_apply (f : Fin n → K) (i : Fin n) :
    coeffEquiv K n (ofFn f) i = (∏ j, (X - C (f j))).coeff i := by
  rw [coeffEquiv_apply_eq_coeff, toMonic_ofFn]

/-- The inverse chart, read as a polynomial rather than as a root multiset, is
`TauCeti.Polynomial.monicOfCoeff`: the monic polynomial of the tuple with prescribed coordinates is
the monic polynomial with those lower coefficients. Equivalently, the chart itself reads off the
lower coefficients of `TauCeti.Sym.toMonic`, which is `TauCeti.Sym.coeffEquiv_apply_eq_coeff`. -/
@[simp]
theorem toMonic_coeffEquiv_symm (c : Fin n → K) :
    (toMonic ((coeffEquiv K n).symm c) : K[X]) = Polynomial.monicOfCoeff c := by
  symm
  simpa only [← coeffEquiv_apply_eq_coeff, Equiv.apply_symm_apply] using
    Polynomial.monicOfCoeff_coeff (monic_toMonic ((coeffEquiv K n).symm c))
      (natDegree_toMonic (s := (coeffEquiv K n).symm c))

end AlgClosed

/-! ### The action of a polynomial map in coefficient coordinates -/

section PolynomialMapAlg

open _root_.MvPolynomial Finset

variable {K : Type*} [CommRing K] {n : ℕ}

end PolynomialMapAlg

section PolynomialMap

open _root_.MvPolynomial Finset

variable {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}

end PolynomialMap

end Sym

end TauCeti
