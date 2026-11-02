/- GID: D5/S3/Combinatorics/Graph/Laman/HennebergRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/HennebergRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.CosetCover, mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2]
   utility: none
   digest: Type I and Type II Henneberg rigidity preservation in the real plane. -/
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
import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

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

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {x₀ : X}
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {V : Type*} [Finite V]

/-- If a family `F : X → V → α` of `V`-tuples (with `V` a finite type and `α` Hausdorff)
is *componentwise continuous* at a base point `x₀` and *injective* at `x₀`, then it is
injective on a neighborhood of `x₀`.

Each pair `(u, v)` with `u ≠ v` contributes a `ContinuousAt.prodMk`-driven eventuality
that `(F x u, F x v)` stays off the diagonal (closed in `α × α` by Hausdorffness);
`Finset.eventually_all` aggregates the finitely many pair-eventualities into a single
neighborhood. -/
private theorem Injective.eventually_of_continuousAt {F : X → V → α}
    (hcont : ∀ v, ContinuousAt (fun x => F x v) x₀) (hinj : Injective (F x₀)) :
    ∀ᶠ x in 𝓝 x₀, Injective (F x) := by
  have : Fintype V := Fintype.ofFinite V
  have h_each : ∀ uv ∈ (Finset.univ : Finset (V × V)),
      ∀ᶠ x in 𝓝 x₀, uv.1 ≠ uv.2 → F x uv.1 ≠ F x uv.2 := by
    rintro ⟨u, v⟩ _
    by_cases huv : u = v
    · exact .of_forall (fun _ h => absurd huv h)
    have h_ne : F x₀ u ≠ F x₀ v := fun h => huv (hinj h)
    have h_prod : ContinuousAt (fun x => (F x u, F x v)) x₀ :=
      (hcont u).prodMk (hcont v)
    have h_compl : (Set.diagonal α)ᶜ ∈ 𝓝 (F x₀ u, F x₀ v) :=
      isClosed_diagonal.isOpen_compl.mem_nhds h_ne
    filter_upwards [h_prod h_compl] with x hx _ using hx
  filter_upwards [Finset.univ.eventually_all.mpr h_each] with x hx u v heq
  by_contra h_uv
  exact hx (u, v) (Finset.mem_univ _) h_uv heq

/-- One-coordinate perturbation form of `Function.Injective.eventually_of_continuousAt`.
If `p₀ : V → α` is injective on a finite type `V` (with `α` Hausdorff) and `f : X → α`
is a continuous deformation through `f x₀ = p₀ c` of the `c`-th coordinate, then
`Function.update p₀ c (f x)` is injective for `x` in a neighborhood of `x₀`.

Used to lift "injective at the base placement" through a one-vertex `Function.update`
perturbation in Henneberg-move generic-placement arguments. -/
private theorem Injective.eventually_update_of_continuousAt [DecidableEq V] {p₀ : V → α}
    (hp₀ : Injective p₀) {c : V} {f : X → α}
    (hf : ContinuousAt f x₀) (hf0 : f x₀ = p₀ c) :
    ∀ᶠ x in 𝓝 x₀, Injective (update p₀ c (f x)) := by
  have h_eq0 : update p₀ c (f x₀) = p₀ := by
    funext v
    by_cases hvc : v = c
    · subst hvc; simp [hf0]
    · simp [update_of_ne hvc]
  have hcont : ∀ v, ContinuousAt (fun x => update p₀ c (f x) v) x₀ := by
    intro v
    by_cases hvc : v = c
    · subst hvc; simpa using hf
    · simpa [update_of_ne hvc] using (continuousAt_const : ContinuousAt (fun _ : X => p₀ v) x₀)
  have hinj₀ : Injective (update p₀ c (f x₀)) := by rw [h_eq0]; exact hp₀
  exact Injective.eventually_of_continuousAt (F := fun x => update p₀ c (f x)) hcont hinj₀

end Function

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
lemma exists_not_mem_span_singleton_dim_two
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
the image of `p`. -/
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

/-! ### Type II preservation of rigidity in dim 2

Whiteley's argument (his proof of the Edge `d`-Split Theorem 11.1.7, 1996; Jordán 2016, Lemma
1.2.3, cites it): place the new vertex `q` on the *line* through `p a` and `p b`. The three new
edges' constraints then split into a "deleted-edge recovery" (the constraint
`⟪p a - p b, x (some a) - x (some b)⟫ = 0` falls out of the new edges at `none ↔ some a` and
`none ↔ some b`, both lying along the common direction `p b - p a`) and an "injectivity" piece
(the new edge at `none ↔ some c`, in an independent direction, pins `x none`).

The argument requires `p a, p b, p c` to be **non-collinear** — otherwise `q - p c` also lies in
the `p b - p a` direction, the LI condition fails, and the extended placement is not
rigid (a 1-parameter family of "vertical" infinitesimal motions of `none` is unconstrained).
The conditional theorem below takes the appropriate `q` as input; the unconditional wrapper
strengthens the input rigid placement to one with non-collinear `(p a, p b, p c)` via the
perturbation helper `exists_nonCollinear_rigid_placement_dim_two`, which uses openness of
infinitesimal rigidity (`IsInfinitesimallyRigid.eventually` in `Framework.lean`). -/

/-- **Algebraic backbone of the typeII conditional cores.** Given the collinear extension
condition `q - p' a = s • (p' b - p' a)` for the typeII new vertex, the two new-edge inner
products at `none ↔ some a` and `none ↔ some b` combine linearly to recover the deleted-edge
inner product at `s(a, b)`:

  `(s − 1) · ⟪q − p' a, x none − x (some a)⟫_ℝ − s · ⟪q − p' b, x none − x (some b)⟫_ℝ
   = s(s − 1) · ⟪p' a − p' b, x (some a) − x (some b)⟫_ℝ`

valid for any motion `x : Framework (Option V) d`. The consumer is
`typeII_isInfinitesimallyRigid_extend`: both new-edge inner products vanish at a kernel
element, and dividing by `s(s − 1) ≠ 0` recovers the deleted-edge constraint.

Proof: derive `q - p' b = (s − 1) • (p' b - p' a)` from `hcoll` by `q − p' b = (q − p' a) −
(p' b − p' a)`, factor both inner-product scalars via `real_inner_smul_left`, and finish by
`linear_combination` over the `⟪p' b − p' a, ·⟫`-linearity identity that pulls the inner
arguments together and flips the sign once. -/
lemma typeII_collinear_inner_combo {V : Type*} {d : ℕ}
    {p' : Framework V d} {q : EuclideanSpace ℝ (Fin d)} {s : ℝ} {a b : V}
    (hcoll : q - p' a = s • (p' b - p' a))
    (x : Framework (Option V) d) :
    (s - 1) * ⟪q - p' a, x none - x (some a)⟫_ℝ
        - s * ⟪q - p' b, x none - x (some b)⟫_ℝ
      = s * (s - 1) * ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
  have hcoll_b : q - p' b = (s - 1) • (p' b - p' a) := by
    have heq : q - p' b = (q - p' a) - (p' b - p' a) := by abel
    simp only [heq, hcoll, sub_smul, one_smul]
  rw [hcoll, hcoll_b, real_inner_smul_left, real_inner_smul_left]
  have h_eq :
      ⟪p' b - p' a, x none - x (some a)⟫_ℝ - ⟪p' b - p' a, x none - x (some b)⟫_ℝ
        = ⟪p' a - p' b, x (some a) - x (some b)⟫_ℝ := by
    simp only [← inner_sub_right,
        show (x none - x (some a)) - (x none - x (some b))
          = x (some b) - x (some a) from by abel,
        show (p' b - p' a) = -(p' a - p' b) from by abel,
        show (x (some b) - x (some a)) = -(x (some a) - x (some b)) from by abel,
        inner_neg_neg]
  linear_combination s * (s - 1) * h_eq

/-- **Conditional Type II rigidity preservation in dim 2.** If `p` is infinitesimally rigid for
`G` and `q : EuclideanSpace ℝ (Fin 2)` is a placement of the new vertex satisfying
the collinearity condition `q - p a = α • (p b - p a)` with `α ≠ 0, 1` (so `q` is on the line
through `p a, p b`, distinct from both) AND the linear-independence condition
`LinearIndependent ℝ ![q - p a, q - p c]` (the new vertex's direction to `p c` is off the line),
then the extended placement `fun w => w.elim q p` is infinitesimally rigid for `typeII G a b c`.

The rank-nullity heart of `typeII_isGenericallyRigidInj_two_of_nonCollinear`. The proof builds a
linear injection from `ker ((typeII G a b c).RigidityMap p_ext)` into `ker (G.RigidityMap p)` via
the restriction `x ↦ x ∘ some`. The new ingredient over typeI is that for the deleted edge
`s(a, b)` (no corresponding typeII edge), the kernel constraint is recovered from the two
collinear-direction new edges at `none ↔ some a` and `none ↔ some b`. The statement does not
ask `G.Adj a b`: when `ab` is not an edge of `G` there is no such constraint to recover. -/
theorem typeII_isInfinitesimallyRigid_extend [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp : G.IsInfinitesimallyRigid p) {a b c : V}
    {q : EuclideanSpace ℝ (Fin 2)} {α : ℝ}
    (hα0 : α ≠ 0) (hα1 : α ≠ 1) (hcoll : q - p a = α • (p b - p a))
    (hLI : LinearIndependent ℝ ![q - p a, q - p c]) :
    (typeII G a b c).IsInfinitesimallyRigid (fun w : Option V => w.elim q p) := by
  set p_ext : Framework (Option V) 2 := fun w : Option V => w.elim q p with hp_ext_def
  -- Restriction map `x ↦ x ∘ some` lands in `ker (G.RigidityMap p)`.
  have h_into : ∀ x : Framework (Option V) 2,
      x ∈ LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →
        x ∘ some ∈ LinearMap.ker (G.RigidityMap p) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    -- Kernel constraints at the two collinear-direction new edges `none ↔ some a` and
    -- `none ↔ some b`; plug into `typeII_collinear_inner_combo` to recover the deleted-edge
    -- constraint at `s(a, b)` via `α(α - 1) ≠ 0`.
    have hxa := congr_fun hx ⟨s(none, some a), by simp⟩
    have hxb := congr_fun hx ⟨s(none, some b), by simp⟩
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxb
    have h_combo := typeII_collinear_inner_combo hcoll x
    rw [hxa, hxb] at h_combo
    simp only [mul_zero, sub_zero] at h_combo
    have h_deleted : ⟪p a - p b, x (some a) - x (some b)⟫_ℝ = 0 :=
      (mul_eq_zero.mp h_combo.symm).resolve_left
        (mul_ne_zero hα0 (sub_ne_zero.mpr hα1))
    -- Edge-membership check.
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have h_uv : G.Adj u v := he
      by_cases h_eq : s(u, v) = s(a, b)
      · -- Deleted edge. `RigidityMap` is built via `Sym2.lift` (`Framework.lean`), so it's
        -- already Sym2-invariant in the edge: rewriting the edge subtype `⟨s(u, v), he⟩ =
        -- ⟨s(a, b), _⟩` via `Subtype.ext h_eq` replaces what would otherwise be a two-way
        -- `Sym2.eq_iff` orientation case split in the unfolded inner-product form.
        rw [show (⟨s(u, v), he⟩ : G.edgeSet) = ⟨s(a, b), h_eq ▸ he⟩ from Subtype.ext h_eq]
        simp only [rigidityMap_apply, Pi.zero_apply, Function.comp_apply]
        exact h_deleted
      · -- Non-deleted edge: lift to typeII edge.
        have h_typeII : s(some u, some v) ∈ (typeII G a b c).edgeSet :=
          show (typeII G a b c).Adj (some u) (some v) from ⟨h_uv, h_eq⟩
        have key := congr_fun hx ⟨s(some u, some v), h_typeII⟩
        simp only [rigidityMap_apply, Pi.zero_apply] at key
        simpa [rigidityMap_apply, Function.comp_apply, hp_ext_def] using key
  -- Kernel-to-kernel linear map: precomposition by `some`, restricted to send
  -- `ker (typeII _)` into `ker G`.
  let restrict : LinearMap.ker ((typeII G a b c).RigidityMap p_ext) →ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    ((LinearMap.funLeft ℝ (EuclideanSpace ℝ (Fin 2)) (some : V → Option V)).comp
        (LinearMap.ker ((typeII G a b c).RigidityMap p_ext)).subtype).codRestrict
      (LinearMap.ker (G.RigidityMap p)) (fun x => h_into x.1 x.2)
  -- Injectivity: the new edges at `none ↔ some a` and `none ↔ some c` orthogonalize
  -- `x.1 none - y.1 none` against the LI pair `(q - p a, q - p c)`.
  have h_inj : Function.Injective restrict := by
    intro x y hxy
    apply Subtype.ext
    funext w
    have h_some : ∀ v, x.1 (some v) = y.1 (some v) := fun v =>
      congr_fun (congrArg Subtype.val hxy) v
    rcases w with _ | v
    swap
    · exact h_some v
    -- Case `w = none`. Use new-edge constraints at `none ↔ some a` and `none ↔ some c`.
    have h_a_edge : s((none : Option V), some a) ∈ (typeII G a b c).edgeSet := by simp
    have h_c_edge : s((none : Option V), some c) ∈ (typeII G a b c).edgeSet := by simp
    have hxa := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some a), h_a_edge⟩
    have hxc := congr_fun (LinearMap.mem_ker.mp x.2) ⟨s(none, some c), h_c_edge⟩
    have hya := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some a), h_a_edge⟩
    have hyc := congr_fun (LinearMap.mem_ker.mp y.2) ⟨s(none, some c), h_c_edge⟩
    simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def,
      Option.elim_none, Option.elim_some] at hxa hxc hya hyc
    have h_perp_a := inner_sub_perp_of_eq (h_some a) hxa hya
    have h_perp_c := inner_sub_perp_of_eq (h_some c) hxc hyc
    exact sub_eq_zero.mp (eq_zero_of_orthogonal_dim_two hLI h_perp_a h_perp_c)
  -- Rank-nullity: `finrank (ker (typeII _)) ≤ finrank (ker G) ≤ 3`.
  exact (LinearMap.finrank_le_finrank_of_injective h_inj).trans hp

/-- In `EuclideanSpace ℝ (Fin 2)`, given distinct points `pa, pb`, a third point `pc` with
`(pa, pb, pc)` non-collinear, and a finite "to-avoid" set `S`, there is a `q := pa + α • (pb - pa)`
on the line through `pa, pb` (with `α ≠ 0, 1`) such that `q ∉ S` and
`LinearIndependent ℝ ![q - pa, q - pc]`. The geometric content is: parametrize the line through
`pa, pb` by `α`; the LI condition is automatic from `(pa, pb, pc)` non-collinearity for any
`α ≠ 0`; the off-set and `α ≠ 1` conditions are each violated by at most finitely many `α`. -/
private lemma exists_typeII_q_on_line_dim_two
    (pa pb pc : EuclideanSpace ℝ (Fin 2)) (hab : pa ≠ pb)
    (hLI_abc : LinearIndependent ℝ ![pb - pa, pc - pa])
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    ∃ (α : ℝ) (q : EuclideanSpace ℝ (Fin 2)),
      α ≠ 0 ∧ α ≠ 1 ∧ q - pa = α • (pb - pa) ∧
      LinearIndependent ℝ ![q - pa, q - pc] ∧ q ∉ S := by
  have hd : pb - pa ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  -- Parametrize the line: `f α := pa + α • (pb - pa)`.
  set f : ℝ → EuclideanSpace ℝ (Fin 2) := fun α => pa + α • (pb - pa) with hf_def
  have hf_inj : Function.Injective f := fun _ _ h =>
    smul_left_injective ℝ hd (add_left_cancel h)
  -- The "bad" `α`-set: `{0, 1} ∪ f⁻¹(S)`.
  set bad : Set ℝ := ({0, 1} : Set ℝ) ∪ (f ⁻¹' S) with hbad_def
  have hbad_fin : bad.Finite :=
    ((Set.finite_singleton _).insert _).union (hS.preimage hf_inj.injOn)
  obtain ⟨α, hα⟩ := hbad_fin.exists_notMem
  have hα0 : α ≠ 0 := fun h => hα (by simp [hbad_def, h])
  have hα1 : α ≠ 1 := fun h => hα (by simp [hbad_def, h])
  have hq_notmem : f α ∉ S := fun h_mem => hα (by simp [hbad_def, h_mem])
  refine ⟨α, f α, hα0, hα1, ?_, ?_, hq_notmem⟩
  · -- `f α - pa = α • (pb - pa)` by definition.
    simp [hf_def]
  · -- LI of `![q - pa, q - pc]`: stage as a row-op on `![pb - pa, pc - pa]`.
    have h_form :
        (![f α - pa, f α - pc] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![α • (pb - pa) + (0 : ℝ) • (pc - pa),
            α • (pb - pa) + (-1 : ℝ) • (pc - pa)] := by
      ext i
      fin_cases i <;> simp [hf_def]
      abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨hLI_abc, ?_⟩
    intro h_eq
    apply hα0
    linarith

/-- **Type II preserves injective generic rigidity in dim 2, given non-collinear neighbors.**
Given an injectively generically rigid `G` in dim 2 *witnessed by a placement* `p` *for which*
`(p a, p b, p c)` *is non-collinear*, the Type II extension `typeII G a b c` is again
injectively generically rigid in dim 2.

The non-collinearity hypothesis is essential — see the section docstring above. Removing it
requires an openness-of-rigidity argument (any rigid placement can be perturbed to a non-collinear
one while preserving rigidity); the perturbation is packaged in
`exists_nonCollinear_rigid_placement_dim_two`, which the unconditional
`typeII_isGenericallyRigidInj_two` below uses. -/
theorem typeII_isGenericallyRigidInj_two_of_nonCollinear [Finite V] {G : SimpleGraph V}
    {p : Framework V 2} (hp_rig : G.IsInfinitesimallyRigid p) (hp_inj : Function.Injective p)
    {a b c : V} (hLI_abc : LinearIndependent ℝ ![p b - p a, p c - p a]) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  have hpab : p a ≠ p b := fun h => hLI_abc.ne_zero 0 (by simp [h])
  obtain ⟨α, q, hα0, hα1, hcoll, hLI, hq_notmem⟩ :=
    exists_typeII_q_on_line_dim_two (p a) (p b) (p c) hpab hLI_abc (Set.range p)
      (Set.finite_range p)
  exact ⟨fun w : Option V => w.elim q p,
    typeII_isInfinitesimallyRigid_extend hp_rig hα0 hα1 hcoll hLI,
    injective_option_elim hp_inj hq_notmem⟩

/-- **Non-collinear placement via `Function.update`-perturbation in dim 2.** Core of
`exists_nonCollinear_rigid_placement_dim_two` (rigidity and injectivity). Given a
placement `p₀` with `p₀ b - p₀ a ≠ 0`, a property `P` preserved on a neighborhood of `t = 0`
along the one-vertex perturbation `t ↦ Function.update p₀ c (p₀ c + t • w)` for a direction
`w` outside `span {p₀ b - p₀ a}`, produce a placement `p` with `P p` and the non-collinearity
`LinearIndependent ℝ ![p b - p a, p c - p a]`.

If `p₀` is itself non-collinear, return it (with `P p₀` extracted from `hP_ev` via
`Filter.Eventually.self_of_nhds` at `t = 0`). Otherwise `p₀ c - p₀ a = δ • (p₀ b - p₀ a)` for some
`δ` (via `LinearIndependent.pair_iff'` at the non-zero direction); LI of the perturbed pair for
any `t ≠ 0` follows from `pair_add_smul_add_smul_iff` against the auxiliary
`![w, p₀ b - p₀ a]` LI. A witness `t ≠ 0` in the `P`-preservation neighborhood exists because
`𝓝[≠] 0` is `NeBot` in `ℝ`.

The rigid-placement consumer supplies `hP_ev` by pulling back
`IsInfinitesimallyRigid.eventually` through continuity of
the update and `.and`-conjoining
`Function.Injective.eventually_update_of_continuousAt` (whose `Function.update` shape is what
forces the eventually-on-`t` rather than eventually-on-`p` form here). -/
lemma exists_nonCollinear_update_perturbation_dim_two {V : Type*} [DecidableEq V]
    {P : Framework V 2 → Prop} {p₀ : Framework V 2}
    {a b c : V} (hac : a ≠ c) (hbc : b ≠ c)
    (hd_ne_zero : p₀ b - p₀ a ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2))
    (hw_outside : w ∉ Submodule.span ℝ ({p₀ b - p₀ a} : Set _))
    (hP_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
        P (Function.update p₀ c (p₀ c + t • w))) :
    ∃ p : Framework V 2, P p ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  -- Auxiliary LI `![w, p₀ b - p₀ a]`, used to invoke `pair_add_smul_add_smul_iff`.
  have h_LI_w_d : LinearIndependent ℝ
      (![w, p₀ b - p₀ a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) := by
    rw [linearIndependent_fin2]
    refine ⟨hd_ne_zero, fun s heq => hw_outside ?_⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨s, heq⟩
  -- Name the perturbation; record its pointwise identities.
  let p_t : ℝ → Framework V 2 := fun t => Function.update p₀ c (p₀ c + t • w)
  have h_p_t_c : ∀ t, p_t t c = p₀ c + t • w := fun _ => Function.update_self c _ p₀
  have h_p_t_ne : ∀ t (v : V), v ≠ c → p_t t v = p₀ v :=
    fun _ v hvc => Function.update_of_ne hvc _ p₀
  have h_p_t_a : ∀ t, p_t t a = p₀ a := fun t => h_p_t_ne t a hac
  have h_p_t_b : ∀ t, p_t t b = p₀ b := fun t => h_p_t_ne t b hbc
  have h_p_t_zero : p_t 0 = p₀ := by
    funext v
    by_cases hvc : v = c
    · rw [hvc, h_p_t_c]; simp
    · rw [h_p_t_ne 0 v hvc]
  -- LI branch: `p₀` already non-collinear, return it (extract `P p₀` at `t = 0`).
  by_cases hLI₀ : LinearIndependent ℝ ![p₀ b - p₀ a, p₀ c - p₀ a]
  · exact ⟨p₀, h_p_t_zero ▸ hP_ev.self_of_nhds, hLI₀⟩
  -- Collinear branch: factor `p₀ c - p₀ a = δ • (p₀ b - p₀ a)` via `pair_iff'`.
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, p₀ c - p₀ a = δ • (p₀ b - p₀ a) := by
    rw [LinearIndependent.pair_iff' hd_ne_zero] at hLI₀
    push Not at hLI₀
    exact hLI₀.imp fun _ h => h.symm
  -- LI of the perturbed pair for any `t ≠ 0`.
  have h_LI_perturbed : ∀ t : ℝ, t ≠ 0 →
      LinearIndependent ℝ ![p_t t b - p_t t a, p_t t c - p_t t a] := by
    intro t ht_ne
    have h_form :
        (![p_t t b - p_t t a, p_t t c - p_t t a] : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
          ![(0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a),
            t • w + δ • (p₀ b - p₀ a)] := by
      funext i
      fin_cases i
      · change p_t t b - p_t t a = (0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a)
        simp [h_p_t_a t, h_p_t_b t]
      · change p_t t c - p_t t a = t • w + δ • (p₀ b - p₀ a)
        simp only [h_p_t_a t, h_p_t_c t,
          show (p₀ c + t • w) - p₀ a = (p₀ c - p₀ a) + t • w from by abel, hδ]
        abel
    rw [h_form, LinearIndependent.pair_add_smul_add_smul_iff]
    refine ⟨h_LI_w_d, ?_⟩
    simp [ht_ne.symm]
  -- Pick a `t ≠ 0` in the `P`-neighborhood.
  have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ), P (p_t t) ∧ t ≠ 0 := by
    filter_upwards [hP_ev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t hP_t ht_ne
    exact ⟨hP_t, ht_ne⟩
  obtain ⟨t, hP_t, ht_ne⟩ := h_combined.exists
  exact ⟨p_t t, hP_t, h_LI_perturbed t ht_ne⟩

/-- **Openness-of-rigidity helper: produce a non-collinear rigid placement.** Given any injective
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, there is an injective rigid
placement `p` for which `(p a, p b, p c)` is non-collinear (i.e.,
`LinearIndependent ℝ ![p b - p a, p c - p a]`).

The proof: if the IH placement `p₀` already has the LI condition, use it. Otherwise, pick a
direction `w ∉ span (p₀ b - p₀ a)` and perturb `p₀ c` to `p₀ c + t • w`. By
`IsInfinitesimallyRigid.eventually` and `Function.Injective.eventually_update_of_continuousAt`,
the perturbed placement stays rigid and injective on an open neighborhood of `t = 0`; the
shared core `exists_nonCollinear_update_perturbation_dim_two` selects a `t ≠ 0` that also gives
non-collinearity.

By openness of infinitesimal rigidity it closes the collinearity gap: it lifts
`typeII_isGenericallyRigidInj_two_of_nonCollinear` to the unconditional
`typeII_isGenericallyRigidInj_two` below. -/
private lemma exists_nonCollinear_rigid_placement_dim_two [Finite V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigidInj 2) {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p : Framework V 2, G.IsInfinitesimallyRigid p ∧ Function.Injective p ∧
      LinearIndependent ℝ ![p b - p a, p c - p a] := by
  classical
  obtain ⟨p₀, hp₀_rig, hp₀_inj⟩ := h
  have hd_ne_zero : p₀ b - p₀ a ≠ 0 :=
    sub_ne_zero.mpr fun heq => hab (hp₀_inj heq.symm)
  obtain ⟨w, hw_outside⟩ := exists_not_mem_span_singleton_dim_two hd_ne_zero
  -- Continuity of the perturbation; the `t = 0` instance reduces to `p₀`.
  have h_p_t_cont : Continuous
      (fun t : ℝ => Function.update p₀ c (p₀ c + t • w)) := by fun_prop
  have h_p_t_zero : Function.update p₀ c (p₀ c + (0 : ℝ) • w) = p₀ := by
    simp
  -- Rigidity preservation along the update (pull back `IsInfinitesimallyRigid.eventually`).
  have h_rig_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      G.IsInfinitesimallyRigid (Function.update p₀ c (p₀ c + t • w)) := by
    have h_ev_p := hp₀_rig.eventually
    rw [← h_p_t_zero] at h_ev_p
    exact h_p_t_cont.continuousAt.tendsto.eventually h_ev_p
  -- Injectivity preservation along the update.
  have h_inj_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      Function.Injective (Function.update p₀ c (p₀ c + t • w)) :=
    hp₀_inj.eventually_update_of_continuousAt (f := fun t => p₀ c + t • w)
      (by fun_prop) (by simp)
  obtain ⟨p, ⟨hrig, hinj⟩, hLI⟩ :=
    exists_nonCollinear_update_perturbation_dim_two
      (P := fun p => G.IsInfinitesimallyRigid p ∧ Function.Injective p)
      hac hbc hd_ne_zero w hw_outside (h_rig_ev.and h_inj_ev)
  exact ⟨p, hrig, hinj, hLI⟩

/-- **Type II preserves injective generic rigidity in dim 2 (unconditional).** Given an injectively
generically rigid `G` in dim 2 and three distinct vertices `a, b, c`, the Type II Henneberg
extension `typeII G a b c` is again injectively generically rigid in dim 2.

The proof passes the IH through `exists_nonCollinear_rigid_placement_dim_two` to obtain a placement
on which `(p a, p b, p c)` is non-collinear (the original IH placement may have a collinear
triple, in which case we move the placement of `c` in a direction off the line through `p a, p b`
to break collinearity while preserving rigidity, by openness of infinitesimal rigidity), then
invokes the conditional `typeII_isGenericallyRigidInj_two_of_nonCollinear`. -/
theorem typeII_isGenericallyRigidInj_two [Finite V] {G : SimpleGraph V}
    (hG : G.IsGenericallyRigidInj 2) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (typeII G a b c).IsGenericallyRigidInj 2 := by
  obtain ⟨p, hp_rig, hp_inj, hLI⟩ :=
    exists_nonCollinear_rigid_placement_dim_two hG hab hac hbc
  exact typeII_isGenericallyRigidInj_two_of_nonCollinear hp_rig hp_inj hLI

end Henneberg

end SimpleGraph
