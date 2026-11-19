/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Roots
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Roots
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Roots.lean.
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

public import Mathlib.Data.Multiset.UnionInter
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Root sets and multiplicities

This file records several facts about the roots of a polynomial, either in its coefficient field
or after base change to a domain `E`.

First, an explicit numbering of the root set of a separable polynomial enumerates its full root
multiset: separability makes the roots simple, so the multiset is the image of the numbering.
This lets root-product formulas be expressed as finite products indexed by `Fin f.natDegree`,
without choosing a global order on the root set.

Second, the root set of a product of polynomials whose base changes to `E` are nonzero is the
union of the root sets of the factors. This is the lemma that decomposes the roots of a
polynomial along a factorisation, for instance the roots of a monic integer polynomial along its
monic irreducible factors. The same holds for the distinct roots of a finite product.
For a separable product, the root sets of the factors are pairwise disjoint.

Third, dividing a polynomial by the linear factor of a simple root removes exactly that root
from the root set. Here `a` only has to be a simple root in `E`: `f a` vanishes and `f' a` does
not vanish after mapping to `E`, so the map `F → E` need not be injective.

Fourth, translating the variable moves the roots: the roots of `f(X + t)` are the points `x`
with `x + t` a root of `f`, so `x ↦ x + t` is a bijection between the two root sets, and
`f(X + t)` is separable exactly when `f` is.

Fifth, if every root of a nonzero polynomial is among a family of points `θ i`, then its roots
are exactly the `θ i` in which it has positive multiplicity.

Finally, the roots of a polynomial gcd form the multiset intersection of the roots of its
inputs. In characteristic zero this identifies the degree lost to the gcd with the derivative as
the number of distinct roots.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

-/

public section

namespace TauCeti

open Finset Polynomial

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- The distinct roots in `E` of a finite product of polynomials are those of the factors together,
provided no factor vanishes after base change to `E`. -/
theorem _root_.Polynomial.aroots_prod_toFinset [DecidableEq E] {ι : Type*} (s : Finset ι)
    (f : ι → F[X]) (hf : ∀ k ∈ s, (f k).map (algebraMap F E) ≠ 0) :
    ((∏ k ∈ s, f k).aroots E).toFinset = s.biUnion fun k ↦ ((f k).aroots E).toFinset := by
  ext z
  simp only [Multiset.mem_toFinset, Finset.mem_biUnion, mem_aroots', Polynomial.map_prod,
    Finset.prod_ne_zero_iff.2 hf, ne_eq, not_false_eq_true, true_and, map_prod,
    Finset.prod_eq_zero_iff]
  exact ⟨fun ⟨k, hk, h⟩ ↦ ⟨k, hk, hf k hk, h⟩, fun ⟨k, hk, _, h⟩ ↦ ⟨k, hk, h⟩⟩

/-- If every root of a nonzero polynomial `p` is some `θ i`, and the multiplicity of each `θ i`
as a root of `p` is `m i`, then the roots of `p` are the `θ i` with `0 < m i`. -/
theorem _root_.Polynomial.isRoot_iff_of_rootMultiplicity {ι : Type*} {p : F[X]} {θ : ι → F}
    {m : ι → ℕ} (hm : ∀ i, p.rootMultiplicity (θ i) = m i)
    (hθ : ∀ t, p.IsRoot t → ∃ i, θ i = t) (hp : p ≠ 0) (t : F) :
    p.IsRoot t ↔ ∃ i, θ i = t ∧ 0 < m i := by
  refine ⟨fun ht ↦ ?_, fun ⟨i, hi, hpos⟩ ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := hθ t ht
    exact ⟨i, rfl, hm i ▸ (rootMultiplicity_pos hp).2 ht⟩
  · rw [← hi, ← rootMultiplicity_pos hp, hm i]
    exact hpos

section GCD

variable {K : Type*} [Field K] [DecidableEq K]

/-- The multiplicity of a root in the gcd of two nonzero polynomials is the minimum of its
multiplicities in the two polynomials. -/
theorem _root_.Polynomial.rootMultiplicity_gcd (p q : K[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (x : K) :
    (EuclideanDomain.gcd p q).rootMultiplicity x =
      min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  have hg : EuclideanDomain.gcd p q ≠ 0 := by
    intro h
    exact hp (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  apply le_antisymm
  · exact le_min
      (rootMultiplicity_le_rootMultiplicity_of_dvd hp (EuclideanDomain.gcd_dvd_left p q) x)
      (rootMultiplicity_le_rootMultiplicity_of_dvd hq (EuclideanDomain.gcd_dvd_right p q) x)
  · rw [le_rootMultiplicity_iff hg]
    apply EuclideanDomain.dvd_gcd
    · exact (le_rootMultiplicity_iff hp).mp (min_le_left _ _)
    · exact (le_rootMultiplicity_iff hq).mp (min_le_right _ _)

section CharZero

variable [CharZero K]

/-- In characteristic zero, the roots of a polynomial's derivative gcd, together with one copy
of each distinct root, recover all roots with multiplicity. -/
theorem _root_.Polynomial.roots_gcd_derivative_add_dedup (p : K[X]) :
    (EuclideanDomain.gcd p p.derivative).roots + p.roots.dedup = p.roots := by
  by_cases hdeg : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg, roots_C, Multiset.dedup_zero, add_zero]
    simp
  · have hp : p ≠ 0 := fun h ↦ hdeg (h ▸ natDegree_zero)
    have hd : p.derivative ≠ 0 := derivative_ne_zero.mpr hdeg
    ext x
    rw [Multiset.count_add, count_roots, rootMultiplicity_gcd p p.derivative hp hd,
      count_roots]
    by_cases hx : p.IsRoot x
    · rw [derivative_rootMultiplicity_of_root hx]
      have hm : 0 < p.rootMultiplicity x := (rootMultiplicity_pos hp).mpr hx
      rw [Multiset.count_dedup, ite_eq_left ((mem_roots hp).mpr hx)]
      omega
    · have hm : p.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hx
      have hmem : x ∉ p.roots := fun h => hx ((mem_roots hp).mp h)
      rw [hm, zero_min, Multiset.count_dedup, ite_eq_right hmem]

/-- For a split polynomial in characteristic zero, the number of distinct roots of a nonzero
polynomial is its degree minus the degree of its gcd with its derivative. -/
theorem _root_.Polynomial.natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset_of_splits
    {p : K[X]} (hp : p ≠ 0) (hsplit : p.Splits) :
    p.natDegree - (EuclideanDomain.gcd p p.derivative).natDegree = p.roots.toFinset.card := by
  by_cases hdeg : p.natDegree = 0
  · have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    rw [hdeg, hpC, roots_C]
    simp
  · have hsplitg : (EuclideanDomain.gcd p p.derivative).Splits :=
      hsplit.of_dvd hp (EuclideanDomain.gcd_dvd_left p p.derivative)
    have hcard := congrArg Multiset.card (roots_gcd_derivative_add_dedup p)
    rw [Multiset.card_add] at hcard
    rw [hsplit.natDegree_eq_card_roots, hsplitg.natDegree_eq_card_roots,
      Multiset.card_toFinset]
    omega

end CharZero

section IsAlgClosed

variable [CharZero K] [IsAlgClosed K]

end IsAlgClosed

end GCD

end TauCeti
