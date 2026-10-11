/- GID: D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension
   generality: G
   mirror-B: D5/B/S3/GraphInvariants/Simplicial/FiniteJoinSuspension
   mirror-E: none(waiver:finite-geometric-homeomorphism)
   anchors: []
   utility: none
   digest: The finite geometric two-point join is the ordinary unreduced suspension. -/

import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Compact

/-!
The join and the four standard-simplex coordinate lemmas and polyhedron
membership lemma are adapted from TauCetiProject/TauCeti, revision
64bb4d871548995899dee90beda88b787fafe27d, Join/Basic.lean and
Realization/{Basic,Coordinates}.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors
Released under the Apache 2.0 license; the full license is retained at
`docs/reports/polarization-suppliers/tauceti-LICENSE.txt`.
Only consumed declarations are retained, with the resolved Mathlib finite-sum
API. These adapters retire when equivalent declarations in the resolved
Mathlib can be substituted directly and the consumers compile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
universe u
open Set Finset

/-- The join of two pre-abstract simplicial complexes, on the disjoint sum of their vertex types.
A nonempty finite set is a face when each of its nonempty left and right projections is a face of
the corresponding complex. -/
def join {α β : Type*} (K : PreAbstractSimplicialComplex α) (L : PreAbstractSimplicialComplex β) :
    PreAbstractSimplicialComplex (α ⊕ β) where
  faces := {σ | σ.Nonempty ∧
    (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) ∧ (σ.toRight = ∅ ∨ σ.toRight ∈ L)}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hK, hL⟩
    refine ⟨hσ, fun {τ} hτσ hτ => ⟨hτ, ?_, ?_⟩⟩
    · rcases hK with hK | hK
      · left
        exact subset_empty.mp ((toLeft_subset_toLeft hτσ).trans (subset_of_eq hK))
      · by_cases hτl : τ.toLeft = ∅
        · exact Or.inl hτl
        · exact Or.inr <| (K.isRelLowerSet_faces hK).2 (toLeft_subset_toLeft hτσ)
            (Finset.nonempty_iff_ne_empty.mpr hτl)
    · rcases hL with hL | hL
      · left
        exact subset_empty.mp ((toRight_subset_toRight hτσ).trans (subset_of_eq hL))
      · by_cases hτr : τ.toRight = ∅
        · exact Or.inl hτr
        · exact Or.inr <| (L.isRelLowerSet_faces hL).2 (toRight_subset_toRight hτσ)
            (Finset.nonempty_iff_ne_empty.mpr hτr)

namespace CoordinateSource
variable {ι : Type*} [DecidableEq ι]
private abbrev StandardSimplex (σ : Finset ι) : Type _ :=
  convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))
/-- Barycentric coordinates in a standard simplex are nonnegative. -/
private theorem StandardSimplex.nonneg {σ : Finset ι} (x : StandardSimplex σ) (v : ι) :
    0 ≤ x.1 v := by
  -- View the coordinate inequality as membership in a convex half-space.
  change x.1 ∈ {y : ι →₀ ℝ | 0 ≤ y v}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨w, _, rfl⟩ := hy
      by_cases h : w = v <;> simp [h])
    (by
      intro y hy z hz a b ha hb _
      simp only [Set.mem_ofPred_eq, Finsupp.add_apply, Finsupp.smul_apply] at hy hz ⊢
      exact add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hz))
    x.2

/-- The barycentric coordinates in a standard simplex sum to one. -/
private theorem StandardSimplex.sum_eq_one {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.sum (fun _ r => r) = 1 := by
  -- Use the linear-map form of coordinate summation required by the convexity API.
  change x.1.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1
  change x.1 ∈
    {y : ι →₀ ℝ | y.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨v, _, rfl⟩ := hy
      simp)
    (by
      intro y hy z hz a b _ _ hab
      simp only [Set.mem_ofPred_eq] at hy hz ⊢
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_smul_index_linearMap', Finsupp.sum_smul_index_linearMap', hy, hz]
        simpa [smul_eq_mul] using hab
      all_goals simp)
    x.2

/-- The support of a point in a standard simplex is contained in its vertex set. -/
private theorem StandardSimplex.support_subset {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.support ⊆ σ := by
  -- Express support containment as membership in the standard supported submodule.
  change (x.1.support : Set ι) ⊆ (σ : Set ι)
  change x.1 ∈ Finsupp.supported ℝ ℝ (σ : Set ι)
  exact convexHull_min (by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simpa [Finsupp.mem_supported] using hv) (Finsupp.supported ℝ ℝ (σ : Set ι)).convex x.2

omit [DecidableEq ι] in
/-- Membership in a standard simplex in terms of barycentric coordinates. -/
@[simp]
private theorem mem_standardSimplex_iff {σ : Finset ι} {x : ι →₀ ℝ} :
    x ∈ convexHull ℝ
        ((fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set ι)) ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ⊆ σ := by
  classical
  constructor
  · intro hx
    rw [← Finset.coe_image] at hx
    let x' : StandardSimplex σ := ⟨x, hx⟩
    exact ⟨StandardSimplex.nonneg x', StandardSimplex.sum_eq_one x',
      StandardSimplex.support_subset x'⟩
  · rintro ⟨hnonneg, hsum, hsupp⟩
    have hsum' :
        x.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1 := by
      -- Put the coordinate-sum hypothesis in the linear-map form required by `Convex.sum_mem`.
      change x.sum (fun _ r => r) = 1
      exact hsum
    have hx := (convex_convexHull ℝ
        (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))).sum_mem
      (fun v _ => hnonneg v) hsum'
      (fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.2 <|
        Finset.mem_image.2 ⟨v, hsupp hv, rfl⟩))
    have heq : (∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ)) = x := by
      simpa [Finsupp.sum] using x.sum_single
    rw [heq] at hx
    rw [Finset.coe_image] at hx
    exact hx


open Geometry.SimplicialComplex
/-- A point of the standard polyhedron has nonnegative coordinates summing to one and
support a face, including for precomplexes with unused vertices. -/
@[simp]
private theorem mem_space_onFinsupp_iff {K : PreAbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (onFinsupp (𝕜 := ℝ) K).space ↔
      (∀ i, 0 ≤ x i) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ∈ K := by
  classical
  have hfaces : ∀ τ, τ ∈ (onFinsupp (𝕜 := ℝ) K).faces ↔
      ∃ σ ∈ K, σ.image (fun i => Finsupp.single i (1 : ℝ)) = τ := by
    intro τ
    simp only [onFinsupp, ofAffineIndependent, PreAbstractSimplicialComplex.map, mem_image]
    aesop
  rw [mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (hfaces τ).mp hτ
    rw [Finset.coe_image, mem_standardSimplex_iff] at hx
    refine ⟨hx.1, hx.2.1, K.isRelLowerSet_faces.mem_of_le hσ hx.2.2 ?_⟩
    apply Finsupp.support_nonempty_iff.mpr
    intro hzero
    simp [hzero] at hx
  · rintro ⟨hnonneg, hsum, hsupp⟩
    refine ⟨x.support.image (fun i => Finsupp.single i (1 : ℝ)),
      (hfaces _).mpr ⟨x.support, hsupp, rfl⟩, ?_⟩
    rw [Finset.coe_image, mem_standardSimplex_iff]
    exact ⟨hnonneg, hsum, Finset.Subset.rfl⟩

end CoordinateSource

/-- The usual finite Euclidean polyhedron, the union of closed face simplices. -/
def geometricCarrier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) : Set (ι → ℝ) :=
  {x | ∃ σ ∈ K, x ∈ convexHull ℝ ((fun i => Pi.single i (1 : ℝ)) '' (σ : Set ι))}

/-- The subspace topology from the finite real product. -/
abbrev GeometricRealization {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) := geometricCarrier K

def support {ι : Type u} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ 0

theorem mem_geometricCarrier_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {x : ι → ℝ} :
    x ∈ geometricCarrier K ↔ (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ support x ∈ K := by
  classical
  let e := Finsupp.linearEquivFunOnFinite ℝ ℝ ι
  have hface : ∀ σ : Finset ι,
      e.symm x ∈ convexHull ℝ ((fun i => Finsupp.single i (1 : ℝ)) '' (σ : Set ι)) ↔
      x ∈ convexHull ℝ ((fun i => Pi.single i (1 : ℝ)) '' (σ : Set ι)) := by
    intro σ
    have himage := e.toLinearMap.image_convexHull
      ((fun i => Finsupp.single i (1 : ℝ)) '' (σ : Set ι))
    have heq : (e : (ι →₀ ℝ) → (ι → ℝ)) ''
        convexHull ℝ ((fun i => Finsupp.single i (1 : ℝ)) '' (σ : Set ι)) =
        convexHull ℝ ((fun i => Pi.single i (1 : ℝ)) '' (σ : Set ι)) := by
      change e '' _ = convexHull ℝ (e '' _) at himage
      simpa only [Set.image_image, Function.comp_def, e,
        Finsupp.linearEquivFunOnFinite_single] using himage
    rw [← heq]
    constructor
    · intro h
      exact ⟨e.symm x, h, e.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  have hspace : e.symm x ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ↔
      x ∈ geometricCarrier K := by
    rw [Geometry.SimplicialComplex.mem_space_iff]
    simp only [Geometry.SimplicialComplex.onFinsupp,
      Geometry.SimplicialComplex.ofAffineIndependent, PreAbstractSimplicialComplex.map,
      Set.mem_image]
    constructor
    · rintro ⟨τ, ⟨σ, hσ, rfl⟩, hx⟩
      exact ⟨σ, hσ, (hface σ).mp (by simpa only [Finset.coe_image] using hx)⟩
    · rintro ⟨σ, hσ, hx⟩
      exact ⟨_, ⟨σ, hσ, rfl⟩, by simpa only [Finset.coe_image] using (hface σ).mpr hx⟩
  rw [← hspace, CoordinateSource.mem_space_onFinsupp_iff]
  have hs : (e.symm x).support = support x := by
    ext i
    simp [support, e]
  rw [hs, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rfl

private theorem isCompact_geometricCarrier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) : IsCompact (geometricCarrier K) := by
  classical
  have heq : geometricCarrier K = ⋃ σ : {σ : Finset ι // σ ∈ K},
      convexHull ℝ ((fun i => Pi.single i (1 : ℝ)) '' (σ.1 : Set ι)) := by
    ext x
    simp [geometricCarrier]
  rw [heq]
  exact isCompact_iUnion fun σ =>
    (σ.1.finite_toSet.image (fun i => Pi.single i (1 : ℝ))).isCompact_convexHull ℝ

private instance {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) : CompactSpace (GeometricRealization K) :=
  isCompact_iff_compactSpace.mp (isCompact_geometricCarrier K)

/-- Two isolated vertices, with both singleton faces and no edge. -/
def D2 : PreAbstractSimplicialComplex (Fin 2) :=
  (⊥ : AbstractSimplicialComplex (Fin 2)).toPreAbstractSimplicialComplex

/-- The interval used for the ordinary unreduced suspension. -/
abbrev Height := Set.Icc (-1 : ℝ) 1

/-- Endpoints collapse separately; every other height retains its base point. -/
def suspensionSetoid (X : Type*) : Setoid (X × Height) where
  r p q := p.2 = q.2 ∧ ((p.2 : ℝ) = -1 ∨ (p.2 : ℝ) = 1 ∨ p.1 = q.1)
  iseqv := {
    refl := fun p => ⟨rfl, Or.inr (Or.inr rfl)⟩
    symm := by
      rintro p q ⟨h, hp⟩
      refine ⟨h.symm, ?_⟩
      rcases hp with hp | hp | hp
      · exact Or.inl (h ▸ hp)
      · exact Or.inr (Or.inl (h ▸ hp))
      · exact Or.inr (Or.inr hp.symm)
    trans := by
      rintro p q r ⟨hpq, hp⟩ ⟨hqr, hq⟩
      refine ⟨hpq.trans hqr, ?_⟩
      rcases hp with hp | hp | hp
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
      · rcases hq with hq | hq | hq
        · exact Or.inl (hpq.symm ▸ hq)
        · exact Or.inr (Or.inl (hpq.symm ▸ hq))
        · exact Or.inr (Or.inr (hp.trans hq)) }

/-- The cylinder quotient with its quotient topology. -/
abbrev OrdinarySuspension (X : Type*) [TopologicalSpace X] := Quotient (suspensionSetoid X)


private theorem support_toLeft {ι : Type u} [Fintype ι] [DecidableEq ι]
    (y : (ι ⊕ Fin 2) → ℝ) :
    (support y).toLeft = support (fun i => y (.inl i)) := by
  ext i
  simp [support]

private theorem support_toRight {ι : Type u} [Fintype ι] [DecidableEq ι]
    (y : (ι ⊕ Fin 2) → ℝ) :
    (support y).toRight = support (fun j => y (.inr j)) := by
  ext j
  simp [support]

private theorem twoPointSupport_iff (f : Fin 2 → ℝ) :
    (support f = ∅ ∨ support f ∈ D2) ↔ f 0 = 0 ∨ f 1 = 0 := by
  classical
  change (support f = ∅ ∨ ∃ j, support f = {j}) ↔ _
  constructor
  · rintro (h | ⟨j, h⟩)
    · left
      have hn : (0 : Fin 2) ∉ support f := h ▸ Finset.notMem_empty _
      simpa [support] using hn
    · fin_cases j
      · right
        have hn : (1 : Fin 2) ∉ support f := by simp [h]
        simpa [support] using hn
      · left
        have hn : (0 : Fin 2) ∉ support f := by simp [h]
        simpa [support] using hn
  · intro h
    by_cases hf : f 0 = 0 ∧ f 1 = 0
    · left
      ext j
      fin_cases j <;> simp [support, hf.1, hf.2]
    · right
      rcases h with h | h
      · refine ⟨1, ?_⟩
        ext j
        fin_cases j <;> simp_all [support]
      · refine ⟨0, ?_⟩
        ext j
        fin_cases j <;> simp_all [support]

private theorem mem_joinCarrier_iff {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} {y : (ι ⊕ Fin 2) → ℝ} :
    y ∈ geometricCarrier (join K D2) ↔
      (∀ j, 0 ≤ y j) ∧
      (∑ i, y (.inl i)) + y (.inr 0) + y (.inr 1) = 1 ∧
      (y (.inr 0) = 0 ∨ y (.inr 1) = 0) ∧
      (support (fun i => y (.inl i)) = ∅ ∨ support (fun i => y (.inl i)) ∈ K) := by
  rw [mem_geometricCarrier_iff]
  have hsum : (∑ j, y j) = (∑ i, y (.inl i)) + y (.inr 0) + y (.inr 1) := by
    simp [Fintype.sum_sum_type, Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  change ((∀ j, 0 ≤ y j) ∧
      (∑ i, y (.inl i)) + y (.inr 0) + y (.inr 1) = 1 ∧
      ((support y).Nonempty ∧
        ((support y).toLeft = ∅ ∨ (support y).toLeft ∈ K) ∧
        ((support y).toRight = ∅ ∨ (support y).toRight ∈ D2))) ↔ _
  rw [support_toLeft, support_toRight, twoPointSupport_iff]
  constructor
  · rintro ⟨hn, hs, _, hK, hD⟩
    exact ⟨hn, hs, hD, hK⟩
  · rintro ⟨hn, hs, hD, hK⟩
    refine ⟨hn, hs, ?_, hK, hD⟩
    by_contra he
    have hz : ∀ j, y j = 0 := by
      intro j
      have : j ∉ support y := fun hj => he ⟨j, hj⟩
      simpa [support] using this
    simp [hz] at hs

private theorem height_identities (s : Height) :
    0 ≤ 1 - |(s : ℝ)| ∧
    max (s : ℝ) 0 + max (-(s : ℝ)) 0 = |(s : ℝ)| ∧
    max (s : ℝ) 0 - max (-(s : ℝ)) 0 = (s : ℝ) ∧
    (max (s : ℝ) 0 = 0 ∨ max (-(s : ℝ)) 0 = 0) := by
  rcases s.2 with ⟨hl, hu⟩
  by_cases h : 0 ≤ (s : ℝ)
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    exact ⟨by linarith, by ring, by ring, Or.inr rfl⟩
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [abs_of_nonpos h', max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    exact ⟨by linarith, by ring, by ring, Or.inl rfl⟩

/-- The explicit barycentric cylinder map: the two poles receive the positive
and negative parts of the height, and the base receives its remaining mass. -/
def suspensionCoordinates {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} (p : GeometricRealization K × Height) :
    (ι ⊕ Fin 2) → ℝ :=
  Sum.elim (fun i => (1 - |(p.2 : ℝ)|) * p.1.1 i)
    (fun j => if j = 0 then max (p.2 : ℝ) 0 else max (-(p.2 : ℝ)) 0)

private theorem suspensionCoordinates_mem {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} (p : GeometricRealization K × Height) :
    suspensionCoordinates p ∈ geometricCarrier (join K D2) := by
  rcases (mem_geometricCarrier_iff.mp p.1.2) with ⟨hn, hs, hK⟩
  rcases height_identities p.2 with ⟨hc, hm, _, hp⟩
  apply mem_joinCarrier_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    cases j with
    | inl i => exact mul_nonneg hc (hn i)
    | inr j =>
      fin_cases j <;> simp [suspensionCoordinates]
  · simp only [suspensionCoordinates, Sum.elim_inl, Sum.elim_inr,
      ite_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
    rw [← Finset.mul_sum, hs]
    linarith
  · simpa [suspensionCoordinates] using hp
  · by_cases hc0 : 1 - |(p.2 : ℝ)| = 0
    · left
      ext i
      simp [support, suspensionCoordinates, hc0]
    · right
      have heq : support (fun i => suspensionCoordinates p (.inl i)) = support p.1.1 := by
        ext i
        simp [support, suspensionCoordinates, hc0]
      exact heq ▸ hK

/-- The cylinder map with values in the actual geometric join. -/
def suspensionMap {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} (p : GeometricRealization K × Height) :
    GeometricRealization (join K D2) :=
  ⟨suspensionCoordinates p, suspensionCoordinates_mem p⟩

private theorem continuous_suspensionMap {ι : Type u} [Fintype ι] [DecidableEq ι]
    {K : PreAbstractSimplicialComplex ι} : Continuous (@suspensionMap ι _ _ K) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  cases j with
  | inl i =>
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_snd).abs).mul
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst))
  | inr j =>
    fin_cases j
    · exact (continuous_subtype_val.comp continuous_snd).max continuous_const
    · exact (continuous_subtype_val.comp continuous_snd).neg.max continuous_const

/-- The geometric map identifies exactly the endpoint fibres of the ordinary
suspension relation; the two opposite poles are distinct. -/
theorem suspensionMap_fibres {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (p q : GeometricRealization K × Height) :
    suspensionMap p = suspensionMap q ↔ (suspensionSetoid (GeometricRealization K)).r p q := by
  constructor
  · intro heq
    have hc : suspensionCoordinates p = suspensionCoordinates q := congrArg Subtype.val heq
    have h0 := congrFun hc (.inr 0)
    have h1 := congrFun hc (.inr 1)
    simp only [suspensionCoordinates, Sum.elim_inr, ite_true,
      show (1 : Fin 2) ≠ 0 by decide, if_false] at h0 h1
    have hs : (p.2 : ℝ) = (q.2 : ℝ) := by
      rw [← (height_identities p.2).2.2.1, ← (height_identities q.2).2.2.1, h0, h1]
    refine ⟨Subtype.ext hs, ?_⟩
    by_cases hl : (p.2 : ℝ) = -1
    · exact Or.inl hl
    by_cases hu : (p.2 : ℝ) = 1
    · exact Or.inr (Or.inl hu)
    right; right
    apply Subtype.ext
    funext i
    have hci := congrFun hc (.inl i)
    simp only [suspensionCoordinates, Sum.elim_inl, ← hs] at hci
    have hmass : 1 - |(p.2 : ℝ)| ≠ 0 := by
      have hlt : |(p.2 : ℝ)| < 1 := abs_lt.mpr
        ⟨lt_of_le_of_ne p.2.2.1 (Ne.symm hl), lt_of_le_of_ne p.2.2.2 hu⟩
      linarith
    exact mul_left_cancel₀ hmass hci
  · rintro ⟨hs, hl | hu | hb⟩
    · apply Subtype.ext
      funext j
      cases j with
      | inl i => simp [suspensionMap, suspensionCoordinates, ← hs, hl]
      | inr j => simp [suspensionMap, suspensionCoordinates, hs]
    · apply Subtype.ext
      funext j
      cases j with
      | inl i => simp [suspensionMap, suspensionCoordinates, ← hs, hu]
      | inr j => simp [suspensionMap, suspensionCoordinates, hs]
    · cases p; cases q
      subst_vars
      rfl

private theorem suspensionMap_surjective {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (hbase : Nonempty (GeometricRealization K)) :
    Function.Surjective (@suspensionMap ι _ _ K) := by
  classical
  intro y
  rcases mem_joinCarrier_iff.mp y.2 with ⟨hn, hsum, hpole, hface⟩
  let a := y.1 (.inr 0)
  let b := y.1 (.inr 1)
  let z : ι → ℝ := fun i => y.1 (.inl i)
  have ha : 0 ≤ a := hn _
  have hb : 0 ≤ b := hn _
  have hz : ∀ i, 0 ≤ z i := fun i => hn _
  have hsumz : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hz i
  have hab : a + b ≤ 1 := by change (∑ i, z i) + a + b = 1 at hsum; linarith
  let s : Height := ⟨a - b, by constructor <;> linarith⟩
  have habs : |(s : ℝ)| = a + b := by
    rcases hpole with ha0 | hb0
    · change a = 0 at ha0
      simp [s, ha0, abs_of_nonneg hb]
    · change b = 0 at hb0
      simp [s, hb0, abs_of_nonneg ha]
  have hp : max (s : ℝ) 0 = a ∧ max (-(s : ℝ)) 0 = b := by
    rcases hpole with ha0 | hb0
    · change a = 0 at ha0
      simp [s, ha0, max_eq_right (neg_nonpos.mpr hb), max_eq_left hb]
    · change b = 0 at hb0
      simp [s, hb0, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
  let c := 1 - |(s : ℝ)|
  have hc : 0 ≤ c := (height_identities s).1
  have hzc : (∑ i, z i) = c := by
    change (∑ i, z i) + a + b = 1 at hsum
    dsimp [c]
    rw [habs]
    linarith
  by_cases hc0 : c = 0
  · obtain ⟨x⟩ := hbase
    have hz0 : ∀ i, z i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hz j)).mp
        (hzc.trans hc0) i (Finset.mem_univ i)
    refine ⟨(x, s), ?_⟩
    apply Subtype.ext
    funext j
    cases j with
    | inl i =>
      change c * x.1 i = z i
      rw [hc0, hz0, zero_mul]
    | inr j =>
      fin_cases j
      · simpa [suspensionMap, suspensionCoordinates, a] using hp.1
      · simpa [suspensionMap, suspensionCoordinates, b] using hp.2
  · have hsupp : support (fun i => z i / c) = support z := by
      ext i
      simp [support, hc0]
    have hK : support z ∈ K := by
      rcases hface with he | hK
      · have hz0 : ∀ i, z i = 0 := by
          intro i
          have hnz : i ∉ support z := he ▸ Finset.notMem_empty i
          simpa [support] using hnz
        have : c = 0 := by simpa [hz0] using hzc.symm
        exact (hc0 this).elim
      · exact hK
    let x : GeometricRealization K := ⟨fun i => z i / c,
      mem_geometricCarrier_iff.mpr ⟨fun i => div_nonneg (hz i) hc,
        by rw [← Finset.sum_div, hzc, div_self hc0], hsupp ▸ hK⟩⟩
    refine ⟨(x, s), ?_⟩
    apply Subtype.ext
    funext j
    cases j with
    | inl i =>
      change c * (z i / c) = z i
      exact mul_div_cancel₀ _ hc0
    | inr j =>
      fin_cases j
      · simpa [suspensionMap, suspensionCoordinates, a] using hp.1
      · simpa [suspensionMap, suspensionCoordinates, b] using hp.2

/-- The continuous map descended through the independently defined endpoint relation. -/
def suspensionQuotientMap {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) :
    OrdinarySuspension (GeometricRealization K) → GeometricRealization (join K D2) :=
  Quotient.lift suspensionMap (fun p q h => (suspensionMap_fibres K p q).mpr h)

private theorem suspensionQuotientMap_bijective {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (hbase : Nonempty (GeometricRealization K)) :
    Function.Bijective (suspensionQuotientMap K) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        intro h
        exact Quotient.sound ((suspensionMap_fibres K p q).mp h)
  · intro y
    obtain ⟨p, hp⟩ := suspensionMap_surjective K hbase y
    exact ⟨Quotient.mk _ p, hp⟩

/-- For an arbitrary finite precomplex with nonempty actual realization, its
geometric join with two isolated points is homeomorphic to its ordinary
unreduced suspension. Ghost vertices and disconnected bases are permitted. -/
def joinSuspensionHomeomorph {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) (hbase : Nonempty (GeometricRealization K)) :
    GeometricRealization (join K D2) ≃ₜ OrdinarySuspension (GeometricRealization K) :=
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (suspensionQuotientMap K)
      (suspensionQuotientMap_bijective K hbase))
    (continuous_suspensionMap.quotient_lift _)).symm

end D5.S3.GraphInvariants.Simplicial.FiniteJoinSuspension
