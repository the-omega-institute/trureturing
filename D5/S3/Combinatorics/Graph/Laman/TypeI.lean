/- GID: D5/S3/Combinatorics/Graph/Laman/TypeI
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/TypeI
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.CosetCover, mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Type I Henneberg rigidity preservation by a finite-dimensional off-line placement. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver API adaptations, imports, and unused-declaration removal.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.Framework
import D5.S3.Combinatorics.Graph.Laman.Moves
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open scoped Pointwise

namespace AffineSubspace

variable {k V : Type*} [DivisionRing k] [Infinite k]
    [AddCommGroup V] [Module k V]
    {s : Finset (AffineSubspace k V)}

/-- A vector space over an infinite division ring cannot be a finite union of proper
affine subspaces. -/
private theorem biUnion_ne_univ_of_top_notMem (hs : ⊤ ∉ s) :
    ⋃ p ∈ s, (p : Set V) ≠ Set.univ := by
  intro hcovers
  classical
  -- Drop empty affine subspaces from the cover; they contribute nothing.
  set s' : Finset (AffineSubspace k V) :=
    s.filter (fun p : AffineSubspace k V => (p : Set V).Nonempty) with hs'_def
  have hs'_sub : s' ⊆ s := Finset.filter_subset _ _
  have h_top_notmem' : ⊤ ∉ s' := fun h => hs (hs'_sub h)
  have hs'_cov : ⋃ p ∈ s', (p : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s, (p : Set V) := hcovers ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    exact Set.mem_iUnion₂.mpr
      ⟨p, Finset.mem_filter.mpr ⟨hp, ⟨x, hxp⟩⟩, hxp⟩
  -- Choose a basepoint for each non-empty subspace.
  choose b hb using fun p (hp : p ∈ s') => (Finset.mem_filter.mp hp).2
  -- Each non-empty `p ∈ s'` is the coset `b p hp +ᵥ p.direction.toAddSubgroup`.
  have hcoset : ∀ p (hp : p ∈ s'),
      (p : Set V) = b p hp +ᵥ (p.direction.toAddSubgroup : Set V) := by
    intro p hp
    ext x
    rw [Set.mem_vadd_set]
    refine ⟨fun hx => ⟨x - b p hp, ?_, by simp⟩, ?_⟩
    · have := AffineSubspace.vsub_mem_direction hx (hb p hp)
      simpa using this
    · rintro ⟨d, hd, rfl⟩
      have : d +ᵥ b p hp ∈ p :=
        AffineSubspace.vadd_mem_of_mem_direction (by simpa using hd) (hb p hp)
      simpa [add_comm] using this
  -- Re-express the cover with cosets of direction submodules, indexed by `s'.attach`.
  have h_addcov : ⋃ q ∈ s'.attach, b q.1 q.2 +ᵥ
      (q.1.direction.toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ p ∈ s', (p : Set V) := hs'_cov ▸ Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, ?_⟩
    rw [hcoset p hp] at hxp
    exact hxp
  -- Apply the additive coset-cover theorem and contradict.
  obtain ⟨q, _hq_mem, _hq_fi⟩ :=
    AddSubgroup.exists_finiteIndex_of_leftCoset_cover h_addcov
  set p := q.1 with hp_def
  have hp_in_s' : p ∈ s' := q.2
  have hp_ne_top : p ≠ ⊤ := fun h => h_top_notmem' (h ▸ hp_in_s')
  have hdir_ne_top : p.direction ≠ ⊤ := by
    intro hdir
    apply hp_ne_top
    rw [← AffineSubspace.mk'_eq (hb p hp_in_s'), hdir]
    simp
  have : Finite (V ⧸ p.direction) := AddSubgroup.finite_quotient_of_finiteIndex
  have : Nontrivial (V ⧸ p.direction) :=
    Submodule.Quotient.nontrivial_iff.mpr hdir_ne_top
  have : Infinite (V ⧸ p.direction) := Module.Free.infinite k (V ⧸ p.direction)
  exact not_finite (V ⧸ p.direction)

end AffineSubspace

section ProperAffineSpan

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

open Module in
/-- A finite set in a vector space whose cardinality does not exceed `finrank` has an affine
span that is not the whole space (in infinite dimension `finrank` is `0`, so the set is
empty). Generalizes "a single point spans no more than itself" and "two points span at most a
line" — useful for ruling out `affineSpan k s = ⊤` from a cardinality bound, e.g., the
proper-affine-subspaces side-condition of `AffineSubspace.biUnion_ne_univ_of_top_notMem`. -/
private theorem AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
    {s : Set V} (hsf : s.Finite) (hs : s.ncard ≤ finrank k V) :
    affineSpan k s ≠ ⊤ := by
  intro h_top
  rcases s.eq_empty_or_nonempty with rfl | hs_ne
  · -- `s = ∅`: `affineSpan = ⊥ ≠ ⊤`.
    exact AffineSubspace.bot_ne_top _ _ _ ((AffineSubspace.span_empty k V V) ▸ h_top)
  · -- `s` nonempty: `finrank (vectorSpan k s) + 1 ≤ s.ncard`, but `vectorSpan = ⊤` from
    -- `h_top` would force `finrank V + 1 ≤ s.ncard ≤ finrank V`, contradiction.
    have : Fintype s := hsf.fintype
    have : Nonempty s := hs_ne.to_subtype
    have h_le : finrank k (vectorSpan k s) + 1 ≤ s.ncard := by
      have h := finrank_vectorSpan_range_add_one_le k (Subtype.val : s → V)
      rw [Subtype.range_val] at h
      rwa [Set.ncard_eq_toFinset_card s hsf, hsf.card_toFinset]
    rw [(AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top _ _ _ h_top), finrank_top] at h_le
    omega

end ProperAffineSpan

public section

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*}

namespace Henneberg

/-- Injectivity of an `Option`-extended placement: if `p` is injective and the new value `q`
sits outside `Set.range p`, the function `fun w : Option V => w.elim q p` is injective.

The `Option`-extension shape comes from the Henneberg moves: `none` represents the fresh vertex,
placed at `q`; `some _` keeps the old placement. The 4-way `rintro` proof recurs in every
unconditional rigidity-preservation theorem (`typeI`/`typeII_isGenericallyRigidInj_two`); this
helper factors it. -/
private lemma injective_option_elim {V α : Type*}
    {p : V → α} (hp : Function.Injective p) {q : α} (hq : q ∉ Set.range p) :
    Function.Injective (fun w : Option V => w.elim q p) := by
  rintro (_ | u) (_ | v) h
  · rfl
  · exact (hq ⟨v, h.symm⟩).elim
  · exact (hq ⟨u, h⟩).elim
  · exact congrArg some (hp h)

/-- In `EuclideanSpace ℝ (Fin 2)`, every line `Submodule.span ℝ {v}` (with `v ≠ 0`) is a proper
subspace, so admits a non-member. The off-line construction in `exists_off_line_off_finite_dim_two`
and the perturbation direction in `exists_nonCollinear_rigid_placement_dim_two` both
need this; the helper consolidates the `finrank_span_singleton` / `finrank_euclideanSpace_fin` /
`SetLike.exists_not_mem_of_ne_top` chain. -/
private lemma exists_not_mem_span_singleton_dim_two
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0) :
    ∃ w : EuclideanSpace ℝ (Fin 2),
      w ∉ Submodule.span ℝ ({v} : Set _) := by
  refine SetLike.exists_notMem_of_ne_top _ ?_
  intro h_top
  have h1 := finrank_span_singleton (K := ℝ) hv
  rw [h_top, finrank_top] at h1
  have h2 := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)
  omega

/-- Inner-product perpendicularity transports across a shared "target". If `sx = sy` and the
displacement `xn - sx` is `⟪v, ·⟫`-perpendicular and similarly for `yn - sy`, then `xn - yn` is
too. Used in the Henneberg move-rigidity injectivity steps to recover
`⟪direction, x none - y none⟫ = 0` from the two new-edge constraints together with the on-`some`
agreement `x ∘ some = y ∘ some`. -/
private lemma inner_sub_perp_of_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v xn yn sx sy : E} (hs : sx = sy)
    (hx : ⟪v, xn - sx⟫_ℝ = 0) (hy : ⟪v, yn - sy⟫_ℝ = 0) : ⟪v, xn - yn⟫_ℝ = 0 := by
  subst hs
  simp only [show xn - yn = (xn - sx) - (yn - sx) by abel, inner_sub_right, hx, hy, sub_zero]

/-- In `EuclideanSpace ℝ (Fin 2)`, a vector `u` orthogonal to two linearly independent vectors is
zero. The size-2 LI family spans (`Fin 2`'s cardinality matches `finrank`), so the orthogonal
complement is `⊥`. -/
private lemma eq_zero_of_orthogonal_dim_two
    {v₁ v₂ u : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![v₁, v₂])
    (h₁ : ⟪v₁, u⟫_ℝ = 0) (h₂ : ⟪v₂, u⟫_ℝ = 0) : u = 0 := by
  have h_span_top : Submodule.span ℝ (Set.range ![v₁, v₂]) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank (by simp)
  have h_ortho : Submodule.span ℝ (Set.range ![v₁, v₂]) ⟂ Submodule.span ℝ ({u} : Set _) := by
    rw [Submodule.isOrtho_span]
    rintro w ⟨i, rfl⟩ v rfl
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  rwa [h_span_top, Submodule.isOrtho_top_left, Submodule.span_singleton_eq_bot] at h_ortho

/-- **Conditional Type I rigidity preservation in dim 2.** If `p : Framework V 2` is
infinitesimally rigid for `G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex
for which the displacements `q - p a` and `q - p b` are linearly independent, then the extended
placement `fun w => w.elim q p` is infinitesimally rigid for `typeI G a b`.

The rank-nullity heart of `typeI_isGenericallyRigidInj_two`. The proof builds a linear injection
from `ker ((typeI G a b).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via the restriction
`x ↦ x ∘ some`: it lands in the right kernel because every `G`-edge lifts to a `typeI G a b`-edge
with the same rigidity-row formula, and it is injective because the two new edges through `none`
pin down `x none` completely whenever `q - p a` and `q - p b` are linearly independent. -/
theorem typeI_isInfinitesimallyRigid_extend [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b : V}
    {q : EuclideanSpace ℝ (Fin 2)}
    (hLI : LinearIndependent ℝ ![q - p a, q - p b]) :
    (typeI G a b).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- The restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`: every `G`-edge `s(u, v)`
  -- lifts to `s(some u, some v) ∈ (typeI G a b).edgeSet` with the same rigidity-row formula.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeI G a b).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_some : s(some u, some v) ∈ (typeI G a b).edgeSet := he
      have key := congr_fun hx ⟨s(some u, some v), h_some⟩
      simp only [rigidityMap_apply, Pi.zero_apply] at key
      simpa [rigidityMap_apply, hp_ext_def] using key
  -- Kernel-to-kernel linear map: precomposition by `some`, restricted to send `ker (typeI _)`
  -- into `ker G`.
  let restrict : LinearMap.ker ((typeI G a b).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    ((LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)).comp
        (LinearMap.ker ((typeI G a b).RigidityMap p_ext)).subtype).codRestrict
      (LinearMap.ker (G.RigidityMap p)) (fun x => h_into x.1 x.2)
  -- Injectivity: any two kernel elements agreeing on `some _` agree at `none` too, because the
  -- two new edges through `none` orthogonalize `x.1 none - y.1 none` against the LI pair
  -- `(q - p a, q - p b)`, forcing the difference to vanish.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Extract the two new-edge constraints for both `x` and `y`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeI G a b).edgeSet := by simp
    have h_b_edge : s((none : Option V), some b) ∈ (typeI G a b).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxb := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some b), h_b_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyb := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some b), h_b_edge⟩
    -- Unfold `p_ext` (`none ↦ q`, `some _ ↦ p _`) inside the inner products.
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxb hya hyb
    have h_perp_a := inner_sub_perp_of_eq (h_some a) hxa hya
    have h_perp_b := inner_sub_perp_of_eq (h_some b) hxb hyb
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_b)
  -- Rank-nullity: `finrank (ker (typeI _)) ≤ finrank (ker G) ≤ 3`.
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given two distinct points `pa, pb` and a finite "to-avoid" set
`S`, there is a point `q ∉ S` with `q - pa` and `q - pb` linearly independent. The geometric
content is "off the line through `pa` and `pb`, and off `S`".

The argument routes through `AffineSubspace.biUnion_ne_univ_of_top_notMem`
(mirrored under `CombinatorialRigidity/Mathlib/.../Cover.lean`, the affine analogue of
mathlib's `Subspace.biUnion_ne_univ_of_top_notMem`): a vector space over an infinite
division ring is not covered by finitely many proper affine subspaces, applied to the
cover `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}`. The LI condition
`(q - pa, q - pb)` then follows from `q` being off the line via a single row-op on
`(q - pa, pb - pa)`.

Used by `typeI_isGenericallyRigidInj_two` with `S = Set.range p` to get a `q` outside
the image of `p`, and by `typeI_edgeSetRowIndependent_lift` (`MatroidIdentification.lean`) with
`S = ∅` (row-independence does not need an injective extended placement). -/
lemma exists_off_line_off_finite_dim_two
    (pa pb : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ q : EuclideanSpace ℝ (Fin 2),
      LinearIndependent ℝ ![q - pa, q - pb] ∧ q ∉ S := by
  classical
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Build the cover `{affineSpan {pa, pb}} ∪ {affineSpan {s} | s ∈ S}` of proper affine
  -- subspaces, and apply the affine analogue of `Subspace.biUnion_ne_univ_of_top_notMem`.
  set L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    affineSpan ℝ ({pa, pb} : Set _) with hL_def
  set s_cover : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    insert L (hS.toFinset.image (fun s => affineSpan ℝ ({s} : Set _)))
  have hno_top : ⊤ ∉ s_cover := by
    have h_fr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := finrank_euclideanSpace_fin
    rw [Finset.mem_insert]
    rintro (h_L | h_sing)
    · -- Pair: `({pa, pb} : Set _).ncard = 2 ≤ 2 = finrank`.
      exact AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
        (Set.toFinite _) (by rw [Set.ncard_pair hab, h_fr]) h_L.symm
    · rcases Finset.mem_image.mp h_sing with ⟨s, _, hs_eq⟩
      exact AffineSubspace.affineSpan_ne_top_of_ncard_le_finrank
        (Set.toFinite _) (by rw [Set.ncard_singleton s, h_fr]; omega) hs_eq
  have h_cover := AffineSubspace.biUnion_ne_univ_of_top_notMem hno_top
  rw [Set.ne_univ_iff_exists_notMem] at h_cover
  obtain ⟨q, hq⟩ := h_cover
  rw [Set.mem_iUnion₂] at hq
  push Not at hq
  have hqL : q ∉ L := hq L (Finset.mem_insert_self _ _)
  have hqS : q ∉ S := fun h_in =>
    hq (affineSpan ℝ ({q} : Set _))
      (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨q, hS.mem_toFinset.mpr h_in, rfl⟩))
      ((AffineSubspace.mem_affineSpan_singleton _ _).mpr rfl)
  refine ⟨q, ?_, hqS⟩
  -- LI of `![q - pa, q - pb]`: from off-line, get `q - pa ∉ ℝ ∙ (pb - pa)`,
  -- then row-op via `LinearIndependent.pair_add_smul_add_smul_iff`.
  have hq_off : (q - pa) ∉ Submodule.span ℝ ({pb - pa} : Set _) := by
    intro h_in
    rw [Submodule.mem_span_singleton] at h_in
    obtain ⟨r, hr⟩ := h_in
    apply hqL
    rw [hL_def, show q = (q - pa) +ᵥ pa from by simp, vadd_left_mem_affineSpan_pair]
    exact ⟨r, hr⟩
  have hLI_qpa_d :
      LinearIndependent ℝ (![q - pa, pb - pa] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd, fun a h_eq => hq_off ?_⟩
    rw [Submodule.mem_span_singleton]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h_eq
    exact ⟨a, h_eq⟩
  have h_form :
      (![q - pa, q - pb] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ![(1 : ℝ) • (q - pa) + (0 : ℝ) • (pb - pa),
          (1 : ℝ) • (q - pa) + (-1 : ℝ) • (pb - pa)] := by
    ext i
    fin_cases i <;> simp
  rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
  exact ⟨hLI_qpa_d, by norm_num⟩

/-- **Type I preserves injective generic rigidity in dim 2.** Given an injectively generically
rigid `G` in dim 2 and `a ≠ b` in `V`, the Henneberg Type I extension `typeI G a b` is again
injectively generically rigid in dim 2. The proof picks a `q : EuclideanSpace ℝ (Fin 2)` off both
the line through `p a, p b` (via `exists_off_line_off_finite_dim_two`) and the image of `p`, then
appeals to `typeI_isInfinitesimallyRigid_extend` for rigidity of the extended placement
`fun w => w.elim q p` and to the off-image condition for its injectivity. -/
theorem typeI_isGenericallyRigidInj_two [Finite V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b : V} (hab : a ≠ b) :
    (typeI G a b).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj⟩ := hG
  have hpab : p a ≠ p b := fun h => hab (hp_inj h)
  obtain ⟨q, hLI, hq_notmem⟩ :=
    exists_off_line_off_finite_dim_two (p a) (p b) hpab (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p, typeI_isInfinitesimallyRigid_extend hp_rig hLI,
    injective_option_elim hp_inj hq_notmem⟩

