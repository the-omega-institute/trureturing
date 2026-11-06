/- GID: D5/S3/Geometry/FiniteElementaryCollapse
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteElementaryCollapse
   mirror-E: none(waiver:finite-elementary-collapse)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold, mathlib/module/Mathlib.Topology.Order.Lattice]
   utility: none
   digest: An explicit coordinate free-face deformation fixes the entire retained realization on the original labels. -/
/- SOURCE PATCH DRAFT: UNCOMPILED. No Lean/kernel or project acceptance claimed.

   Proposed canonical home: D5/S3/Geometry/FiniteElementaryCollapse.
   Classical elementary free-face collapse in the existing coordinate realization.
   Mathematical specification: section 2 of independent_general_relative_cancellation_proof.txt
   (2026-11-05), SHA256 f9888966c4313557587f6c91f7a185a8aa6de6473219536205db6600e64553ad.
   That proof credits the cancellation proposal as its source. The present source
   uses its barycentric formula globally; no theorem from that review is an axiom.
-/
import D5.S3.Geometry.FiniteCoordinateTruncation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Order.Lattice

/-!
An elementary collapse deletes precisely a nonempty face `lower` and its sole
strict coface `insert apex lower`. Labels are unchanged, including ghost labels.
The empty face is absent, as in `PreAbstractSimplicialComplex`.

The endpoint subtracts the minimum lower-face coordinate at every lower vertex
and transfers their total mass to the apex. On every retained face that minimum
is zero. Thus one global formula gives the relative deformation, including for
a singleton lower face and for complexes with arbitrary additional components.
There is no normalization denominator and no closed-pasting assumption.

This is the local geometric ingredient for relative link lifting and theta
cancellation. Neither the link-collapse sequence nor theta cancellation is
asserted or assumed here. This draft has not been elaborated or compiled.
-/

noncomputable section

open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteElementaryCollapse

open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteCoordinateTruncation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Combinatorial data only: the upper face is the unique strict coface of
the nonempty lower face. No realization or topological conclusion is a field. -/
structure CollapsePair (V : Type*) [Fintype V] [DecidableEq V] where
  ambient : PreAbstractSimplicialComplex V
  lower : Finset V
  apex : V
  lower_nonempty : lower.Nonempty
  apex_notMem : apex ∉ lower
  upper_mem : insert apex lower ∈ ambient
  free : ∀ s ∈ ambient, lower ⊂ s → s = insert apex lower

namespace CollapsePair

variable (P : CollapsePair V)

abbrev upper : Finset V := insert P.apex P.lower

theorem lower_mem : P.lower ∈ P.ambient :=
  (P.ambient.isRelLowerSet_faces P.upper_mem).2
    (subset_insert _ _) P.lower_nonempty

private theorem coface_cases {s : Finset V} (hs : s ∈ P.ambient)
    (hls : P.lower ⊆ s) : s = P.lower ∨ s = P.upper := by
  by_cases he : s = P.lower
  · exact Or.inl he
  · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hls, Ne.symm he⟩))

/-- The retained complex, on the original labels. The following membership
theorem identifies this with deletion of exactly the two designated faces. -/
def retained : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ P.ambient ∧ ¬ P.lower ⊆ s}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(P.ambient.isRelLowerSet_faces hs.1).1, ?_⟩
    intro t hts ht
    exact ⟨(P.ambient.isRelLowerSet_faces hs.1).2 hts ht,
      fun hlt => hs.2 (hlt.trans hts)⟩

theorem mem_retained_iff (s : Finset V) :
    s ∈ P.retained ↔ s ∈ P.ambient ∧ s ≠ P.lower ∧ s ≠ P.upper := by
  constructor
  · rintro ⟨hs, hls⟩
    refine ⟨hs, ?_, ?_⟩
    · intro h
      apply hls
      rw [h]
    · intro h
      apply hls
      rw [h]
      exact subset_insert _ _
  · rintro ⟨hs, hl, hu⟩
    refine ⟨hs, ?_⟩
    intro hls
    exact (P.coface_cases hs hls).elim hl hu

theorem retained_le : P.retained ≤ P.ambient := fun _ hs => hs.1

theorem retained_nonempty {s : Finset V} (hs : s ∈ P.retained) : s.Nonempty :=
  (P.retained.isRelLowerSet_faces hs).1

theorem retained_downward {s t : Finset V} (hs : s ∈ P.retained)
    (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ P.retained :=
  (P.retained.isRelLowerSet_faces hs).2 hts ht

@[simp] theorem empty_not_mem_retained : (∅ : Finset V) ∉ P.retained := by
  intro h
  exact Finset.not_nonempty_empty (P.retained_nonempty h)

/-- This minimum is taken over a genuinely nonempty finite face. -/
def minimum (x : V → ℝ) : ℝ := P.lower.inf' P.lower_nonempty x

private theorem minimum_nonneg {x : V → ℝ} (hx : Probability x) :
    0 ≤ P.minimum x :=
  le_inf' _ _ (fun v _ => hx.1 v)

private theorem minimum_le (x : V → ℝ) {v : V} (hv : v ∈ P.lower) :
    P.minimum x ≤ x v := inf'_le _ hv

private theorem continuous_minimum : Continuous P.minimum :=
  Continuous.finset_inf'_apply _ (fun v _ => continuous_apply v)

private theorem minimum_eq_zero_of_missing {s : Finset V} {x : V → ℝ}
    (hx : x ∈ faceSimplex s) (hls : ¬ P.lower ⊆ s) : P.minimum x = 0 := by
  classical
  have hw : ∃ v ∈ P.lower, v ∉ s := by
    by_contra h
    apply hls
    intro v hv
    by_contra hvs
    exact h ⟨v, hv, hvs⟩
  obtain ⟨v, hv, hvs⟩ := hw
  apply le_antisymm _ (P.minimum_nonneg ⟨hx.1, hx.2.1⟩)
  simpa only [hx.2.2 v hvs] using P.minimum_le x hv

/-- The actual endpoint in the original coordinate space. -/
def endpoint (x : V → ℝ) (v : V) : ℝ :=
  x v + (if v = P.apex then (P.lower.card : ℝ) * P.minimum x else 0) -
    (if v ∈ P.lower then P.minimum x else 0)

private theorem endpoint_eq_self {x : V → ℝ} (hm : P.minimum x = 0) :
    P.endpoint x = x := by
  funext v
  simp [endpoint, hm]

private theorem endpoint_probability {x : V → ℝ} (hx : Probability x) :
    Probability (P.endpoint x) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v = P.apex
    · subst v
      simpa only [endpoint, if_pos rfl, if_neg P.apex_notMem, sub_zero] using
        add_nonneg (hx.1 P.apex)
          (mul_nonneg (Nat.cast_nonneg P.lower.card) (P.minimum_nonneg hx))
    · by_cases hvl : v ∈ P.lower
      · simpa only [endpoint, if_neg hv, if_pos hvl, add_zero] using
          sub_nonneg.mpr (P.minimum_le x hvl)
      · simpa only [endpoint, if_neg hv, if_neg hvl, add_zero, sub_zero] using hx.1 v
  · simp [endpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, hx.2]

private theorem continuous_endpoint : Continuous P.endpoint := by
  apply continuous_pi
  intro v
  have ha : Continuous (fun x : V → ℝ =>
      if v = P.apex then (P.lower.card : ℝ) * P.minimum x else 0) := by
    split_ifs
    · exact continuous_const.mul P.continuous_minimum
    · exact continuous_const
  have hl : Continuous (fun x : V → ℝ =>
      if v ∈ P.lower then P.minimum x else 0) := by
    split_ifs
    · exact P.continuous_minimum
    · exact continuous_const
  exact ((continuous_apply v).add ha).sub hl

private theorem endpoint_mem_upper {x : V → ℝ} (hx : x ∈ faceSimplex P.upper) :
    P.endpoint x ∈ faceSimplex P.upper := by
  have hp := P.endpoint_probability ⟨hx.1, hx.2.1⟩
  refine ⟨hp.1, hp.2, ?_⟩
  intro v hv
  have hva : v ≠ P.apex := by
    intro h
    apply hv
    simp [upper, h]
  have hvl : v ∉ P.lower := fun h => hv (mem_insert_of_mem h)
  simp [endpoint, hva, hvl, hx.2.2 v hv]

private theorem endpoint_fixed {x : V → ℝ} (hx : x ∈ realization P.retained) :
    P.endpoint x = x := by
  obtain ⟨s, hs, hxs⟩ := (realization_mem_iff _ _).1 hx
  exact P.endpoint_eq_self (P.minimum_eq_zero_of_missing hxs hs.2)

/-- Freeness controls every intermediate point, including points whose
original face is the removed lower face and whose apex coordinate is zero. -/
private theorem mix_mem_ambient (t : I) (x : Space P.ambient) :
    mix t x.val (P.endpoint x.val) ∈ realization P.ambient := by
  obtain ⟨s, hs, hx⟩ := (realization_mem_iff _ _).1 x.property
  by_cases hls : P.lower ⊆ s
  · have hsu : s ⊆ P.upper := by
      rcases P.coface_cases hs hls with he | he
      · rw [he]
        exact subset_insert _ _
      · rw [he]
    have hxu : x.val ∈ faceSimplex P.upper :=
      ⟨hx.1, hx.2.1, fun v hv => hx.2.2 v (fun h => hv (hsu h))⟩
    have hy := P.endpoint_mem_upper hxu
    have hp := probability_mix ⟨hxu.1, hxu.2.1⟩ ⟨hy.1, hy.2.1⟩ t
    apply (realization_mem_iff _ _).2
    refine ⟨P.upper, P.upper_mem, hp.1, hp.2, ?_⟩
    intro v hv
    simp [mix, hxu.2.2 v hv, hy.2.2 v hv]
  · rw [P.endpoint_eq_self (P.minimum_eq_zero_of_missing hx hls)]
    have he : mix t x.val x.val = x.val := by
      funext v
      simp only [mix]
      ring
    rw [he]
    exact x.property

/-- At the endpoint an attained minimum supplies a missing lower vertex. -/
private theorem endpoint_zero (x : V → ℝ) :
    ∃ v ∈ P.lower, P.endpoint x v = 0 := by
  obtain ⟨v, hv, hm⟩ := exists_mem_eq_inf' P.lower_nonempty x
  change P.minimum x = x v at hm
  have hva : v ≠ P.apex := fun h => P.apex_notMem (h ▸ hv)
  exact ⟨v, hv, by simp [endpoint, hva, hv, hm]⟩

/-- The endpoint belongs to the exact retained realization, not merely to a
space of the same homotopy type. Nonempty support is proved from total mass one. -/
theorem endpoint_mem_retained (x : Space P.ambient) :
    P.endpoint x.val ∈ realization P.retained := by
  have hy : P.endpoint x.val ∈ realization P.ambient := by
    simpa using P.mix_mem_ambient (1 : I) x
  obtain ⟨s, hs, hys⟩ := (realization_mem_iff _ _).1 hy
  have hp : Probability (P.endpoint x.val) := ⟨hys.1, hys.2.1⟩
  have hsupport : support (P.endpoint x.val) ⊆ s := by
    intro v hv
    by_contra hvs
    exact (mem_support _ _).1 hv (hys.2.2 v hvs)
  have hface : support (P.endpoint x.val) ∈ P.ambient :=
    (P.ambient.isRelLowerSet_faces hs).2 hsupport (support_nonempty hp)
  have hretained : support (P.endpoint x.val) ∈ P.retained := by
    refine ⟨hface, ?_⟩
    intro hls
    obtain ⟨v, hv, hvz⟩ := P.endpoint_zero x.val
    exact (mem_support _ _).1 (hls hv) hvz
  apply (realization_mem_iff _ _).2
  refine ⟨support (P.endpoint x.val), hretained, hp.1, hp.2, ?_⟩
  intro v hv
  by_contra hvz
  exact hv ((mem_support _ _).2 hvz)

/-- The library's actual subcomplex inclusion, with unchanged coordinates. -/
abbrev inclusion : C(Space P.retained, Space P.ambient) :=
  realizationInclusion P.retained_le

/-- The explicit coordinate retraction onto the exact retained complex. -/
def retraction : C(Space P.ambient, Space P.retained) where
  toFun x := ⟨P.endpoint x.val, P.endpoint_mem_retained x⟩
  continuous_toFun :=
    (P.continuous_endpoint.comp continuous_subtype_val).subtype_mk _

theorem retraction_inclusion (y : Space P.retained) :
    P.retraction (P.inclusion y) = y := by
  apply Subtype.ext
  change P.endpoint y.val = y.val
  exact P.endpoint_fixed y.property

/-- Strong deformation retraction relative to every retained point, with the
actual inclusion as the backward map. -/
def collapseHomotopy :
    (ContinuousMap.id (Space P.ambient)).HomotopyRel
      (P.inclusion.comp P.retraction)
      {x | x.val ∈ realization P.retained} where
  toHomotopy := straight _ _ (by
    intro t x
    change mix t x.val (P.endpoint x.val) ∈ realization P.ambient
    exact P.mix_mem_ambient t x)
  prop' t x hx := by
    apply Subtype.ext
    change mix t x.val (P.endpoint x.val) = x.val
    rw [P.endpoint_fixed hx]
    funext v
    simp only [mix]
    ring

/-- The homotopy has precisely the reviewed barycentric coordinate formula
at every point of the ambient realization, without a face-dependent branch. -/
theorem collapseHomotopy_coordinate (t : I) (x : Space P.ambient) (v : V) :
    (P.collapseHomotopy (t, x)).val v =
      x.val v + (if v = P.apex then
        (t : ℝ) * (P.lower.card : ℝ) * P.minimum x.val else 0) -
      (if v ∈ P.lower then (t : ℝ) * P.minimum x.val else 0) := by
  change mix t x.val (P.endpoint x.val) v = _
  unfold mix endpoint
  split_ifs <;> ring

/-- The forward map is the proved retraction; its inverse is the actual
coordinate inclusion, not a replacement homeomorphic model. -/
def collapseEquiv : Space P.ambient ≃ₕ Space P.retained where
  toFun := P.retraction
  invFun := P.inclusion
  left_inv := ⟨P.collapseHomotopy.toHomotopy.symm⟩
  right_inv := by
    have he : P.retraction.comp P.inclusion = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro y
      exact P.retraction_inclusion y
    rw [he]

end CollapsePair
end D5.S3.Geometry.FiniteElementaryCollapse
