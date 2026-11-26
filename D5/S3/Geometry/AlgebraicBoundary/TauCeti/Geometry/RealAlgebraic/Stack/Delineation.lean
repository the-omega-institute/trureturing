/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Delineation
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/Stack/Delineation
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Geometry/RealAlgebraic/Stack/Delineation.lean.
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

public import Mathlib.Algebra.MvPolynomial.Equiv
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Analysis.Polynomial.RealRoots.Common
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Geometry.RealAlgebraic.Stack.Sign
import Mathlib.Analysis.Normed.Module.Convex
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.MvPolynomial.Equiv
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Polynomial.Thom
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.RealClosure.AbstractRolle
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Roots
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Delineations of families of real polynomials

Let `P k x`, for `k` in an index type `ι`, be real polynomials depending on a parameter `x` in a
base `X`. A *delineation* of `P` is a common stack for the whole family: finitely many
continuous functions `θ₀ < θ₁ < ⋯ < θₘ₋₁` on `X` such that

* each member is either the zero polynomial at every point of the base or at none, and has the
  same degree at every point;
* at every point, the roots of every nonzero member are among the values `θᵢ x`, every `θᵢ x` is
  a root of some member, and the multiplicity of `θᵢ x` as a root of `P k x` does not depend on
  `x`;
* every member is sign-invariant on each section and each sector of the stack.

This is the conclusion of Collins' delineability theorem, the step that lifts a cylindrical
algebraic decomposition by one dimension.

Over a nonempty base the ordered list of root functions of a delineation is the increasing
enumeration of the real roots of the nonzero members, so a delineation is unique. Delineations
restrict along continuous maps of bases.

The main theorem `TauCeti.nonempty_delineation` constructs a delineation over a preconnected base
from invariant algebraic data: if the coefficients of every member are continuous, every member is
nullified everywhere or nowhere, and the degree of every member, its number of distinct complex
roots and the degree of the gcd of every pair of distinct members are constant on the base, then
the family has a delineation. Its root functions are the common ordered real roots given by the
family matching lemma `Polynomial.exists_continuous_ordered_common_roots_of_preconnectedSpace`.

When the derivative of every member is zero or a member, Thom's lemma shows that two points of
one fiber at which all members have the same signs lie in the same section or sector. So the cells
of the stack are cut out by sign conditions on the members.

For a family obtained from polynomials `f` in `n + 1` variables by singling out the first one with
`MvPolynomial.finSuccEquiv`, every `f` is sign-invariant on each cell of the stack in
`ℝ^(n + 1)`, the cells being the images of the sections and sectors under `TauCeti.cylinder`.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (Theorem 5.16).
-/

public section

open Function Polynomial Set

namespace TauCeti

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : ι → X → ℝ[X]}

/-- A *delineation* of a family `P k x` of real polynomials over a base `X` is a common stack of
their roots: continuous functions `root 0 < ⋯ < root (count - 1)` on `X` such that each member is
zero everywhere or nowhere and has constant degree, the roots of each nonzero member are among
the `root i x`, each `root i` is a root of some member, the multiplicity of `root i x` as a root of
`P k x` is a constant `multiplicity k i`, and each member is sign-invariant on every section and
every sector of the stack. -/
structure Delineation (P : ι → X → ℝ[X]) where
  /-- The number of sections of the stack. -/
  count : ℕ
  /-- The root functions, listed in increasing order. -/
  root : Fin count → X → ℝ
  /-- Each root function is continuous. -/
  continuous_root (i : Fin count) : Continuous (root i)
  /-- At each point the root functions are strictly increasing in their index. -/
  strictMono_root (x : X) : StrictMono fun i ↦ root i x
  /-- The multiplicity of the `i`-th root function as a root of the `k`-th member. -/
  multiplicity : ι → Fin count → ℕ
  /-- The multiplicity of `root i x` as a root of `P k x` is `multiplicity k i` at every `x`. -/
  rootMultiplicity_root (k : ι) (i : Fin count) (x : X) :
    (P k x).rootMultiplicity (root i x) = multiplicity k i
  /-- Every root of a nonzero member is the value of a root function. -/
  exists_root_eq (k : ι) (x : X) : P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, root i x = t
  /-- Every root function is a root of some member. -/
  exists_multiplicity_pos (i : Fin count) : ∃ k, 0 < multiplicity k i
  /-- Each member is the zero polynomial at every point or at none. -/
  eq_zero_or_ne_zero (k : ι) : (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0
  /-- Each member has the same degree at every point. -/
  natDegree_eq (k : ι) (x y : X) : (P k x).natDegree = (P k y).natDegree
  /-- Each member is sign-invariant on each section. -/
  signInvariant_sectionSet (k : ι) (i : Fin count) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectionSet root i)
  /-- Each member is sign-invariant on each sector. -/
  signInvariant_sectorSet (k : ι) (j : Fin (count + 1)) :
    SignInvariant (fun z : X × ℝ ↦ (P k z.1).eval z.2) (sectorSet root j)

namespace Delineation

/-- Construct a delineation from continuous ordered roots with specified constant
multiplicities. The roots must cover every nonzero member, and each section must have
positive multiplicity in some member. On a preconnected base these data imply
sign-invariance on all sections and sectors. -/
def ofRoots [PreconnectedSpace X] {n : ℕ} {θ : Fin n → X → ℝ} {m : ι → Fin n → ℕ}
    (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
    (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
    (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (hθ : ∀ i, Continuous (θ i)) (hmono : ∀ x, StrictMono fun i ↦ θ i x)
    (hmult : ∀ k i x, (P k x).rootMultiplicity (θ i x) = m k i)
    (hroots : ∀ k x, P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, θ i x = t)
    (hpos : ∀ i, ∃ k, 0 < m k i) : Delineation P := by
  have hP (k : ι) : Continuous fun z : X × ℝ ↦ (P k z.1).eval z.2 := by
    rcases isEmpty_or_nonempty X with hX | hX
    · exact continuous_of_const fun z ↦ isEmptyElim z.1
    · obtain ⟨x₀⟩ := hX
      exact continuous_eval_of_continuous_coeff (fun j _ ↦ hcoeff k j)
        fun x ↦ (hdeg k x x₀).le
  exact {
    count := n
    root := θ
    continuous_root := hθ
    strictMono_root := hmono
    multiplicity := m
    rootMultiplicity_root := hmult
    exists_root_eq := hroots
    exists_multiplicity_pos := hpos
    eq_zero_or_ne_zero := hnull
    natDegree_eq := hdeg
    signInvariant_sectionSet := fun k i ↦ signInvariant_eval_sectionSet
      (I := {i | 0 < m k i}) (hP k) (hθ i) (fun x ↦ (hmono x).injective) (hnull k)
      fun x hk t ↦ (isRoot_iff_of_rootMultiplicity (fun i ↦ hmult k i x)
        (hroots k x hk) hk t).trans (by simp only [mem_ofPred_eq, and_comm])
    signInvariant_sectorSet := fun k _ ↦
      signInvariant_eval_sectorSet (hP k) hθ hmono (hnull k) fun x hk ↦ hroots k x hk }

section

variable [PreconnectedSpace X] {n : ℕ} {θ : Fin n → X → ℝ} {m : ι → Fin n → ℕ}
  (hcoeff : ∀ k j, Continuous fun x ↦ (P k x).coeff j)
  (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
  (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
  (hθ : ∀ i, Continuous (θ i)) (hmono : ∀ x, StrictMono fun i ↦ θ i x)
  (hmult : ∀ k i x, (P k x).rootMultiplicity (θ i x) = m k i)
  (hroots : ∀ k x, P k x ≠ 0 → ∀ t, (P k x).IsRoot t → ∃ i, θ i x = t)
  (hpos : ∀ i, ∃ k, 0 < m k i)

end

/-- Any family of real polynomials over an empty base has a delineation. -/
theorem nonempty_of_isEmpty [IsEmpty X] (P : ι → X → ℝ[X]) : Nonempty (Delineation P) :=
  ⟨{
    count := 0
    root := Fin.elim0
    continuous_root := fun i ↦ i.elim0
    strictMono_root := fun x ↦ isEmptyElim x
    multiplicity := fun _ ↦ Fin.elim0
    rootMultiplicity_root := fun _ i ↦ i.elim0
    exists_root_eq := fun _ x ↦ isEmptyElim x
    exists_multiplicity_pos := fun i ↦ i.elim0
    eq_zero_or_ne_zero := fun _ ↦ .inl isEmptyElim
    natDegree_eq := fun _ x ↦ isEmptyElim x
    signInvariant_sectionSet := fun _ i ↦ i.elim0
    signInvariant_sectorSet := fun _ _ ↦ subsingleton_of_subsingleton.signInvariant }⟩

variable (D : Delineation P)

/-- A member of the family has positive multiplicity in a root function exactly when it is
nonzero and vanishes there. -/
theorem multiplicity_pos_iff {k : ι} {i : Fin D.count} (x : X) :
    0 < D.multiplicity k i ↔ P k x ≠ 0 ∧ (P k x).IsRoot (D.root i x) := by
  rw [← D.rootMultiplicity_root k i x, rootMultiplicity_pos']

/-- At every point of the base, the values of the root functions are exactly the real roots of
the nonzero members of the family. -/
theorem range_root (x : X) :
    range (fun i ↦ D.root i x) = {t | ∃ k, P k x ≠ 0 ∧ (P k x).IsRoot t} := by
  ext t
  refine ⟨?_, fun ⟨k, hk, ht⟩ ↦ D.exists_root_eq k x hk t ht⟩
  rintro ⟨i, rfl⟩
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  exact ⟨k, (D.multiplicity_pos_iff x).1 hk⟩

end Delineation

/-- **Delineability from invariant fiber data.** Let `P k x`, for `k` in a finite index type, be
real polynomials whose coefficients depend continuously on a parameter `x` in a preconnected
space. Suppose that each member is zero everywhere or nowhere, and that the degree of each member,
its number of distinct complex roots and the degree of the gcd of every pair of distinct members
do not depend on `x`. Then the family has a delineation. -/
theorem nonempty_delineation [Finite ι] [PreconnectedSpace X]
    (hcoeff : ∀ k i, Continuous fun x ↦ (P k x).coeff i)
    (hnull : ∀ k, (∀ x, P k x = 0) ∨ ∀ x, P k x ≠ 0)
    (hdeg : ∀ k x y, (P k x).natDegree = (P k y).natDegree)
    (hcard : ∀ k x y, ((P k x).aroots ℂ).toFinset.card = ((P k y).aroots ℂ).toFinset.card)
    (hgcd : Pairwise fun k l ↦ ∀ x y, (EuclideanDomain.gcd (P k x) (P l x)).natDegree =
      (EuclideanDomain.gcd (P k y) (P l y)).natDegree) :
    Nonempty (Delineation P) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Delineation.nonempty_of_isEmpty P
  obtain ⟨x₀⟩ := id hX
  -- the common ordered real roots of the members that are nowhere zero
  obtain ⟨n, r, hrc, hrm, hroot, hmult⟩ :=
    exists_continuous_ordered_common_roots_of_preconnectedSpace
      (ι := {k // ∀ x, P k x ≠ 0}) (F := fun k ↦ P k.1) (d := fun k ↦ (P k.1 x₀).natDegree)
      (fun k i _ ↦ hcoeff k.1 i)
      (fun k x ↦ by rw [degree_eq_natDegree (k.2 x), hdeg k.1 x x₀])
      (fun k x₀ ↦ .of_forall fun x ↦ (hcard k.1 x x₀).le)
      (fun k l hkl x₀ ↦ .of_forall fun x ↦ hgcd (Subtype.coe_ne_coe.2 hkl) x x₀)
  -- a member which is zero somewhere is zero everywhere
  have hzero {k : ι} (h : ¬∀ x, P k x ≠ 0) (x : X) : P k x = 0 :=
    (hnull k).resolve_right h x
  let m (k : ι) (i : Fin n) : ℕ := (P k x₀).rootMultiplicity (r x₀ i)
  have hm (k : ι) (i : Fin n) (x : X) : (P k x).rootMultiplicity (r x i) = m k i := by
    by_cases hk : ∀ x, P k x ≠ 0
    · exact hmult ⟨k, hk⟩ i x x₀
    · simp only [m, hzero hk, rootMultiplicity_zero]
  have hsub (k : ι) (x : X) (hk : P k x ≠ 0) (t : ℝ) (ht : (P k x).IsRoot t) :
      ∃ i, r x i = t :=
    (hroot x t).1 ⟨⟨k, fun y h ↦ hk (hzero (fun h' ↦ h' y h) x)⟩, ht⟩
  refine ⟨Delineation.ofRoots hcoeff hnull hdeg hrc hrm hm hsub fun i ↦ ?_⟩
  obtain ⟨⟨k, hk⟩, hki⟩ := (hroot x₀ (r x₀ i)).2 ⟨i, rfl⟩
  exact ⟨k, (rootMultiplicity_pos (hk x₀)).2 hki⟩

/-! ### Families closed under differentiation up to zero -/

namespace Delineation

variable (D : Delineation P)

/-- **Thom's lemma for delineations.** Suppose that at a point `x` of the base the derivative of
every member of the family is zero or a member. If every member has the same sign at two distinct
points `t ≠ t'` of the fiber over `x`, then no root function takes a value in `[t, t']` at `x`. -/
theorem root_notMem_uIcc_of_sign_eval_eq {x : X}
    (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x))
    {t t' : ℝ} (htt' : t ≠ t')
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : D.root i x ∉ uIcc t t' := by
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  obtain ⟨hk0, hroot⟩ := (D.multiplicity_pos_iff x).1 hk
  -- every iterated derivative of a member is zero or a member, so it has the same sign at `t`
  -- and `t'`
  have hiter (j : ℕ) : derivative^[j] (P k x) = 0 ∨ ∃ l, P l x = derivative^[j] (P k x) := by
    induction j with
    | zero => exact .inr ⟨k, rfl⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain h0 | ⟨l, hl⟩ := ih
      · exact .inl (by rw [h0, derivative_zero])
      · rw [← hl]
        exact hder l
  have hsign (j : ℕ) : derivativeSign (P k x) t j = derivativeSign (P k x) t' j := by
    obtain h0 | ⟨l, hl⟩ := hiter j
    · simp only [derivativeSign, h0, eval_zero]
    · simpa only [derivativeSign, hl] using h l
  exact fun hi ↦ eval_ne_zero_of_derivativeSign_eq _
    (RealClosure.polynomialRolle_of_isRealClosed (R := ℝ)) hk0 htt' hsign hi hroot.eq_zero

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sections. -/
theorem mk_mem_sectionSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (i : Fin D.count) : (x, t) ∈ sectionSet D.root i ↔ (x, t') ∈ sectionSet D.root i := by
  rcases eq_or_ne t t' with rfl | htt'
  · rfl
  have hi := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
  simp only [sectionSet]
  exact iff_of_false (fun he ↦ hi (he ▸ left_mem_uIcc)) fun he ↦ hi (he ▸ right_mem_uIcc)

/-- Suppose that at a point `x` of the base the derivative of every member of the family is zero
or a member. Then two points of the fiber over `x` at which every member has the same sign lie in
the same sectors. -/
theorem mk_mem_sectorSet_iff_of_sign_eval_eq
    {x : X} (hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)) {t t' : ℝ}
    (h : ∀ k, SignType.sign ((P k x).eval t) = SignType.sign ((P k x).eval t'))
    (j : Fin (D.count + 1)) : (x, t) ∈ sectorSet D.root j ↔ (x, t') ∈ sectorSet D.root j := by
  rcases eq_or_ne t t' with rfl | htt'
  · rfl
  have hi (i : Fin D.count) :
      (D.root i x < t ↔ D.root i x < t') ∧ (t < D.root i x ↔ t' < D.root i x) := by
    have := D.root_notMem_uIcc_of_sign_eval_eq hder htt' h i
    rw [mem_uIcc] at this
    grind
  simp only [sectorSet, Set.mem_setOf_eq, hi]

end Delineation

section MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {S : Set (Fin n → ℝ)}

/-- For a delineation of the fibers of `MvPolynomial.finSuccEquiv A n f` over `S`, the polynomial
`f` in `n + 1` variables, evaluated along `φ`, is sign-invariant on every cell of the stack in
`ℝ^(n + 1)`. -/
theorem Delineation.signInvariant_eval₂_of_mem_stackCells
    (D : Delineation fun (p : F) (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom φ x.1))
    {f : MvPolynomial (Fin (n + 1)) A} (hf : MvPolynomial.finSuccEquiv A n f ∈ F)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    SignInvariant (fun y ↦ MvPolynomial.eval₂ φ y f) E := by
  have key : (fun y ↦ MvPolynomial.eval₂ φ y f) ∘ cylinder S =
      fun z ↦ ((MvPolynomial.finSuccEquiv A n f).map (MvPolynomial.eval₂Hom φ z.1.1)).eval z.2 :=
    funext fun z ↦ by
      rw [Function.comp_apply, cylinder, MvPolynomial.polynomial_eval_map_finSuccEquiv]
  rcases hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [signInvariant_image, key]
  exacts [D.signInvariant_sectionSet ⟨_, hf⟩ i, D.signInvariant_sectorSet ⟨_, hf⟩ j]

end MvPolynomial

end TauCeti
