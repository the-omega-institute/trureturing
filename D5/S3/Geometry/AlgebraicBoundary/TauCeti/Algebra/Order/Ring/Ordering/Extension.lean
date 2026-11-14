/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Ordering/Extension
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Ordering/Extension
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Order/Ring/Ordering/Extension.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Ordering.Basic
public import Mathlib.Algebra.Order.Ring.Cone
public import Mathlib.Order.Zorn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Extending field preorderings to orderings

A proper preordering on a field extends to a total ordering. The proof adjoins
one element to a preordering and then applies Zorn's lemma. In particular, it
preserves the prescribed positive elements, as required when ordering a field
extension of an already ordered field.

## References

This is the classical preordering extension argument; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Lemma 2.1 and Corollaries 3.2 and 3.4. The Lean construction uses Mathlib's
`RingPreordering` and `RingCone` interfaces.
-/

public section

variable {K : Type*} [Field K]

namespace RingPreordering

/-- Adjoin an element whose negative is absent from a field preordering. -/
def adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) : RingPreordering K :=
  RingPreordering.mk' {x | ∃ u ∈ P, ∃ v ∈ P, x = u + a * v}
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u + w, add_mem hu hw, v + z, add_mem hv hz, by ring⟩)
    (by
      rintro x y ⟨u, hu, v, hv, rfl⟩ ⟨w, hw, z, hz, rfl⟩
      exact ⟨u * w + a ^ 2 * (v * z),
        add_mem (mul_mem hu hw) (mul_mem (P.pow_two_mem a) (mul_mem hv hz)),
        u * z + v * w, add_mem (mul_mem hu hz) (mul_mem hv hw), by ring⟩)
    (fun x => ⟨x * x, P.mul_self_mem x, 0, zero_mem P, by simp⟩)
    (by
      rintro ⟨u, hu, v, hv, heq⟩
      by_cases hv0 : v = 0
      · apply P.neg_one_notMem
        have heq' : -1 = u := by simpa only [hv0, mul_zero, add_zero] using heq
        exact heq' ▸ hu
      · apply ha
        have hmem : (1 + u) * v⁻¹ ∈ P :=
          mul_mem (add_mem (one_mem P) hu) (RingPreordering.inv_mem hv)
        have hval : -a = (1 + u) * v⁻¹ := by
          field_simp
          linear_combination heq
        rwa [← hval] at hmem)

theorem le_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    P ≤ adjoin P a ha :=
  fun x hx => ⟨x, hx, 0, zero_mem P, by simp⟩

theorem self_mem_adjoin (P : RingPreordering K) (a : K) (ha : -a ∉ P) :
    a ∈ adjoin P a ha :=
  ⟨0, zero_mem P, 1, one_mem P, by simp⟩

/-- The union of a nonempty chain of preorderings is a preordering. -/
private def chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : RingPreordering K := by
  have := hne.to_subtype
  have hd : Directed (· ≤ ·) (fun P : c => P.val.toSubsemiring) :=
    hc.directed.mono_comp _ RingPreordering.toSubsemiring_mono
  exact
    { (⨆ P : c, P.val.toSubsemiring).copy {x | ∃ P ∈ c, x ∈ P} (by
        rw [Subsemiring.coe_iSup_of_directed hd]
        ext x
        simp) with
      mem_of_isSquare' := by
        rintro x ⟨y, rfl⟩
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hP, P.mul_self_mem y⟩
      neg_one_notMem' := by
        rintro ⟨P, _, hP⟩
        exact P.neg_one_notMem hP }

private theorem le_chainUnion (c : Set (RingPreordering K)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : RingPreordering K} (hP : P ∈ c) :
    P ≤ chainUnion c hc hne :=
  fun _ hx => ⟨P, hP, hx⟩

/-- A field preordering extends to an ordering, retaining every prescribed sign. -/
theorem exists_le_isOrdering (P : RingPreordering K) :
    ∃ Q : RingPreordering K, P ≤ Q ∧ Q.IsOrdering := by
  obtain ⟨Q, hPQ, hQ⟩ := zorn_le_nonempty_Ici₀ P
    (fun c _ hc y hy =>
      ⟨chainUnion c hc ⟨y, hy⟩, fun z hz => le_chainUnion c hc ⟨y, hy⟩ hz⟩) P le_rfl
  have htotal : HasMemOrNegMem Q := ⟨by
    intro a
    by_cases ha : -a ∈ Q
    · exact Or.inr ha
    · exact Or.inl ((hQ (le_adjoin Q a ha)) (self_mem_adjoin Q a ha))⟩
  exact ⟨Q, hPQ, { htotal with toIsPrime := inferInstance }⟩

/-- A preordering on a field is a pointed ring cone. -/
def toRingCone (P : RingPreordering K) : RingCone K where
  __ := P.toSubsemiring
  eq_zero_of_mem_of_neg_mem' := P.eq_zero_of_mem_of_neg_mem

instance (P : RingPreordering K) [P.IsOrdering] : HasMemOrNegMem (toRingCone P) where
  mem_or_neg_mem := mem_or_neg_mem P

/-- The linear order associated to a field ordering. -/
@[instance_reducible] noncomputable def linearOrder (P : RingPreordering K)
    [P.IsOrdering] : LinearOrder K := by
  classical
  exact .mkOfAddGroupCone (toRingCone P)

theorem isStrictOrderedRing (P : RingPreordering K) [P.IsOrdering] :
    letI := linearOrder P
    IsStrictOrderedRing K := by
  let := linearOrder P
  have : IsOrderedRing K := .mkOfCone (toRingCone P)
  infer_instance

/-- Order a field while respecting all signs in a specified preordering. -/
theorem exists_linearOrder (P : RingPreordering K) :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K ∧ ∀ x ∈ P, 0 ≤ x := by
  obtain ⟨Q, hPQ, hQ⟩ := exists_le_isOrdering P
  let := hQ
  exact ⟨linearOrder Q, isStrictOrderedRing Q, fun x hx => show @LE.le K (linearOrder Q).toLE 0 x from hPQ (by simpa using hx)⟩

end RingPreordering
