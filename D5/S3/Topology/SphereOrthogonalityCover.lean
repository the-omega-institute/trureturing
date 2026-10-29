/- GID: D5/S3/Topology/SphereOrthogonalityCover
   generality: G
   mirror-B: D5/B/S3/Topology/SphereOrthogonalityCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.PartitionOfUnity, mathlib/module/Mathlib.Geometry.Manifold.Instances.Sphere]
   utility: none
   digest: Perpendicular-circle restriction and the finite acute-cover obstruction force at least six open orthogonality-free colors on the two-sphere. -/

import D5.S3.Topology.SphereBrouwerObstruction
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Tactic

/-! # Acute components and multiplicity in sphere covers -/

set_option autoImplicit false

open Set Metric Module
open scoped InnerProductSpace Topology

noncomputable section

namespace D5.S3.Topology.SphereOrthogonalityCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A set of unit vectors contains no orthogonal pair. -/
def OrthogonalityFree (U : Set (sphere (0 : E) 1)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ⟪(x : E), (y : E)⟫_ℝ ≠ 0

/-- Every actual connected component of an orthogonality-free set of unit vectors is acute. -/
theorem component_inner_pos {U : Set (sphere (0 : E) 1)} (hU : OrthogonalityFree U)
    {a x y : sphere (0 : E) 1}
    (hx : x ∈ connectedComponentIn U a) (hy : y ∈ connectedComponentIn U a) :
    0 < ⟪(x : E), (y : E)⟫_ℝ := by
  apply isPreconnected_connectedComponentIn.lt_of_ne
    ((continuous_const.inner continuous_subtype_val).continuousOn)
    (fun z hz => hU x (connectedComponentIn_subset U a hx) z
      (connectedComponentIn_subset U a hz)) ?_ hy
  refine ⟨x, hx, ?_⟩
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp x.property]
  norm_num

open Classical in
/-- Extending a unit vector by an orthonormal basis of its perpendicular space forces one
distinct absent color per perpendicular direction. -/
theorem cover_color_multiplicity {n k : ℕ} [Fact (finrank ℝ E = n + 1)]
    (U : Fin k → Set (sphere (0 : E) 1))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hfree : ∀ i, OrthogonalityFree (U i))
    (x : sphere (0 : E) 1) :
    (Finset.univ.filter fun i => x ∈ U i).card + n ≤ k := by
  classical
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere x)
  let v : Fin n → sphere (0 : E) 1 := fun j =>
    ⟨(b j : E), mem_sphere_zero_iff_norm.mpr (b.orthonormal.norm_eq_one j)⟩
  choose c hc using fun j => hcover (v j)
  have hc_inj : Function.Injective c := by
    intro i j hij
    by_contra hne
    apply hfree (c i) (v i) (hc i) (v j) (hij ▸ hc j)
    exact b.orthonormal.inner_eq_zero hne
  have hc_absent : ∀ j, x ∉ U (c j) := by
    intro j hx
    apply hfree (c j) x hx (v j) (hc j)
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (b j).property
  have hcard : n ≤ (Finset.univ.filter fun i => x ∉ U i).card := by
    calc
      n = (Finset.univ.image c).card := by rw [Finset.card_image_of_injective _ hc_inj]; simp
      _ ≤ (Finset.univ.filter fun i => x ∉ U i).card :=
        Finset.card_le_card (by
          intro i hi
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_absent j⟩)
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x ∈ U i)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

open Classical in
/-- A finite open orthogonality-free cover has a finite refinement by distinct actual
components. At every point the component-to-color map is injective. -/
theorem exists_finite_acute_refinement [CompactSpace (sphere (0 : E) 1)]
    [LocallyConnectedSpace (sphere (0 : E) 1)] {k : ℕ}
    (U : Fin k → Set (sphere (0 : E) 1)) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hfree : ∀ i, OrthogonalityFree (U i)) :
    ∃ t : Finset (Fin k × Set (sphere (0 : E) 1)),
      (∀ j ∈ t, IsOpen j.2 ∧ j.2.Nonempty ∧ j.2 ⊆ U j.1 ∧
        ∀ x ∈ j.2, ∀ y ∈ j.2, 0 < ⟪(x : E), (y : E)⟫_ℝ) ∧
      (∀ x, ∃ j ∈ t, x ∈ j.2) ∧
      ∀ x, (t.filter fun j => x ∈ j.2).card ≤
        (Finset.univ.filter fun i => x ∈ U i).card := by
  classical
  let A := {j : Fin k × Set (sphere (0 : E) 1) |
    ∃ a ∈ U j.1, j.2 = connectedComponentIn (U j.1) a}
  have hAo : ∀ j : A, IsOpen j.val.2 := by
    intro j
    obtain ⟨a, _, heq⟩ := j.property
    rw [heq]
    exact (hopen j.val.1).connectedComponentIn
  have hAc : (univ : Set (sphere (0 : E) 1)) ⊆ ⋃ j : A, j.val.2 := by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨⟨(i, connectedComponentIn (U i) x), x, hi, rfl⟩,
      mem_connectedComponentIn hi⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun j : A => j.val.2) hAo hAc
  let t := s.image Subtype.val
  have ht : ∀ j ∈ t, j ∈ A := by
    intro j hj
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
    exact a.property
  refine ⟨t, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨a, ha, heq⟩ := ht j hj
    rw [heq]
    exact ⟨(hopen j.1).connectedComponentIn,
      ⟨a, mem_connectedComponentIn ha⟩, connectedComponentIn_subset _ _,
      fun _ hx _ hy => component_inner_pos (hfree j.1) hx hy⟩
  · intro x
    obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨j.val, Finset.mem_image.mpr ⟨j, hj, rfl⟩, hx⟩
  · intro x
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro j hj
      obtain ⟨hjt, hx⟩ := Finset.mem_filter.mp hj
      obtain ⟨a, ha, heq⟩ := ht j hjt
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        connectedComponentIn_subset _ _ (heq ▸ hx)⟩
    · intro j hj l hl heq
      obtain ⟨hjt, hx⟩ := Finset.mem_filter.mp hj
      obtain ⟨hlt, hy⟩ := Finset.mem_filter.mp hl
      obtain ⟨a, ha, hja⟩ := ht j hjt
      obtain ⟨b, hb, hlb⟩ := ht l hlt
      apply Prod.ext heq
      calc
        j.2 = connectedComponentIn (U j.1) x :=
          hja.trans (connectedComponentIn_eq (hja ▸ hx))
        _ = connectedComponentIn (U l.1) x := by rw [heq]
        _ = l.2 := (hlb.trans (connectedComponentIn_eq (hlb ▸ hy))).symm

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The following definition is adapted from TauCeti/Analysis/Normed/Module/Normalize.lean,
revision 5a01f5fe3621126cccf9ba22e700493cbc7b7156. Changes: private visibility,
receiving namespace and explicit qualified normalization names.
The complete license is docs/reports/polarization-suppliers/tauceti-LICENSE.txt.
-/
private def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨NormedSpace.normalize (f y),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (h0 y))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [NormedSpace.normalize]
    exact ((continuous_norm.comp hf).inv₀
      (fun y => norm_ne_zero_iff.mpr (h0 y))).smul hf

/-- A finite acute open cover gives a sphere map homotopic to the identity. At each point
its value lies in the span of the representatives of the sets containing that point. -/
theorem acute_cover_normalized_map {ι : Type*} [Fintype ι]
    (V : ι → Set (sphere (0 : E) 1)) (hopen : ∀ i, IsOpen (V i))
    (hcover : ∀ x, ∃ i, x ∈ V i) (c : ι → sphere (0 : E) 1) (hc : ∀ i, c i ∈ V i)
    (hacute : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, 0 < ⟪(x : E), (y : E)⟫_ℝ) :
    ∃ g : C(sphere (0 : E) 1, sphere (0 : E) 1),
      (ContinuousMap.id _).Homotopic g ∧
      ∀ x, (g x : E) ∈ Submodule.span ℝ ((fun i => (c i : E)) '' {i | x ∈ V i}) := by
  classical
  obtain ⟨ψ, hψ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ V hopen
    (fun x _ => mem_iUnion.mpr (hcover x))
  have hsupport : ∀ i x, ψ i x ≠ 0 → x ∈ V i := by
    intro i x hx
    exact hψ i (subset_closure (show x ∈ Function.support (ψ i) from hx))
  let F : sphere (0 : E) 1 → E := fun x => ∑ i, ψ i x • (c i : E)
  have hF : Continuous F := by
    exact continuous_finsetSum _ fun i _ => (ψ i).continuous.smul continuous_const
  have hpos : ∀ x : sphere (0 : E) 1, 0 < ⟪(x : E), F x⟫_ℝ := by
    intro x
    change 0 < ⟪(x : E), ∑ i, ψ i x • (c i : E)⟫_ℝ
    simp only [inner_sum, inner_smul_right]
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : ψ i x = 0
      · simp [hi]
      · exact mul_nonneg (ψ.nonneg i x) (hacute i x (hsupport i x hi) (c i) (hc i)).le
    · obtain ⟨i, hi⟩ := ψ.exists_pos (mem_univ x)
      exact ⟨i, Finset.mem_univ _,
        mul_pos hi (hacute i x (hsupport i x hi.ne') (c i) (hc i))⟩
  have hnz : ∀ x, F x ≠ 0 := by
    intro x hx
    have := hpos x
    rw [hx, inner_zero_right] at this
    exact lt_irrefl _ this
  let g := normalizeToSphere F hF hnz
  refine ⟨g, ?_, ?_⟩
  · let L : unitInterval × sphere (0 : E) 1 → E := fun z =>
      (1 - (z.1 : ℝ)) • (z.2 : E) + (z.1 : ℝ) • F z.2
    have hL : Continuous L := by fun_prop
    have hLnz : ∀ z, L z ≠ 0 := by
      rintro ⟨t, x⟩ hz
      have hinner : 0 < ⟪(x : E), L (t, x)⟫_ℝ := by
        simp only [L, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
          mem_sphere_zero_iff_norm.mp x.property, one_pow, mul_one]
        by_cases ht : (t : ℝ) = 0
        · simp [ht]
        · have hp := mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht)) (hpos x)
          linarith [t.property.2]
      rw [hz, inner_zero_right] at hinner
      exact lt_irrefl _ hinner
    let H := normalizeToSphere L hL hLnz
    refine ⟨{ toContinuousMap := H, map_zero_left := ?_, map_one_left := ?_ }⟩
    · intro x
      apply Subtype.ext
      change NormedSpace.normalize (L (0, x)) = (x : E)
      simpa [L] using NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp x.property)
    · intro x
      apply Subtype.ext
      change NormedSpace.normalize (L (1, x)) = NormedSpace.normalize (F x)
      simp [L]
  · intro x
    change ‖F x‖⁻¹ • F x ∈ _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro i _
    by_cases hi : ψ i x = 0
    · simp [hi]
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, hsupport i x hi, rfl⟩)

open Classical in
/-- A sphere map supported pointwise on fewer representatives than the ambient dimension
omits a point, since a finite union of proper linear subspaces cannot cover a real vector space. -/
theorem map_omits_point_of_small_spans [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (V : ι → Set (sphere (0 : E) 1))
    (c : ι → E) (g : C(sphere (0 : E) 1, sphere (0 : E) 1))
    (hdim : 0 < finrank ℝ E)
    (hcard : ∀ x, (Finset.univ.filter fun i => x ∈ V i).card < finrank ℝ E)
    (hspan : ∀ x, (g x : E) ∈ Submodule.span ℝ (c '' {i | x ∈ V i})) :
    ∃ p : sphere (0 : E) 1, ∀ x, g x ≠ p := by
  classical
  let A := {s : Finset ι // s.card < finrank ℝ E}
  let P : A → Submodule ℝ E := fun s => Submodule.span ℝ (c '' (s.val : Set ι))
  have hP : ∀ s, P s ≠ ⊤ := by
    intro s
    apply ne_of_lt
    apply span_lt_top_of_ncard_lt_finrank (s.val.finite_toSet.image c)
    exact lt_of_le_of_lt (by
      simpa only [Finset.coe_sort_coe, Set.ncard_coe_finset] using
        Set.ncard_image_le s.val.finite_toSet (f := c)) s.property
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top P hP
  have hv0 : v ≠ 0 := by
    intro hz
    exact hv ⟨∅, by simpa using hdim⟩ (hz ▸ (P _).zero_mem)
  let p : sphere (0 : E) 1 :=
    ⟨NormedSpace.normalize v, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hv0)⟩
  refine ⟨p, ?_⟩
  intro x hx
  let s : A := ⟨Finset.univ.filter fun i => x ∈ V i, hcard x⟩
  apply hv s
  have hset : (s.val : Set ι) = {i | x ∈ V i} := by ext; simp [s]
  change v ∈ Submodule.span ℝ (c '' (s.val : Set ι))
  rw [hset]
  have hmem := (Submodule.span ℝ (c '' {i | x ∈ V i})).smul_mem ‖v‖ (hspan x)
  simpa only [hx, p, Subtype.coe_mk, NormedSpace.norm_smul_normalize] using hmem

private theorem nullhomotopic_of_misses_point
    (g : C(sphere (0 : E) 1, sphere (0 : E) 1))
    (p : sphere (0 : E) 1) (hp : ∀ x, g x ≠ p) : g.Nullhomotopic := by
  let e := stereographic (mem_sphere_zero_iff_norm.mp p.property)
  letI : ContractibleSpace e.target :=
    (convex_univ : Convex ℝ (univ : Set (ℝ ∙ (p : E))ᗮ)).contractibleSpace univ_nonempty
  letI : ContractibleSpace e.source := e.toHomeomorphSourceTarget.contractibleSpace
  have hsource : ∀ x, g x ∈ e.source := by
    intro x
    simpa only [e, stereographic_source, mem_compl_iff, mem_singleton_iff] using hp x
  let f : C(sphere (0 : E) 1, e.source) :=
    ⟨fun x => ⟨g x, hsource x⟩, g.continuous.subtype_mk hsource⟩
  let inclusion : C(e.source, sphere (0 : E) 1) := ⟨Subtype.val, continuous_subtype_val⟩
  exact ((id_nullhomotopic e.source).comp_right inclusion).comp_left f

open Classical in
/-- An acute finite open cover with point multiplicities strictly below the ambient dimension
would make the sphere contractible. -/
theorem acute_cover_contractible_of_multiplicity_lt [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (V : ι → Set (sphere (0 : E) 1))
    (hopen : ∀ i, IsOpen (V i)) (hcover : ∀ x, ∃ i, x ∈ V i)
    (c : ι → sphere (0 : E) 1) (hc : ∀ i, c i ∈ V i)
    (hacute : ∀ i, ∀ x ∈ V i, ∀ y ∈ V i, 0 < ⟪(x : E), (y : E)⟫_ℝ)
    (hdim : 0 < finrank ℝ E)
    (hcard : ∀ x, (Finset.univ.filter fun i => x ∈ V i).card < finrank ℝ E) :
    ContractibleSpace (sphere (0 : E) 1) := by
  obtain ⟨g, hid, hspan⟩ := acute_cover_normalized_map V hopen hcover c hc hacute
  obtain ⟨p, hp⟩ := map_omits_point_of_small_spans V (fun i => (c i : E)) g hdim hcard hspan
  obtain ⟨q, hq⟩ := nullhomotopic_of_misses_point g p hp
  exact (contractible_iff_id_nullhomotopic _).mpr ⟨q, hid.trans hq⟩

open Classical in
/-- An open orthogonality-free cover whose point multiplicities are below the ambient
dimension would contract the sphere. The finite acute refinement is constructed. -/
theorem open_cover_contractible_of_multiplicity_lt {n k : ℕ} [Fact (finrank ℝ E = n + 1)]
    (U : Fin k → Set (sphere (0 : E) 1)) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hfree : ∀ i, OrthogonalityFree (U i))
    (hmult : ∀ x, (Finset.univ.filter fun i => x ∈ U i).card < n + 1) : ContractibleSpace (sphere (0 : E) 1) := by
  classical
  letI : FiniteDimensional ℝ E :=
    FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  letI : LocallyConnectedSpace (sphere (0 : E) 1) :=
    ChartedSpace.locallyConnectedSpace (H := EuclideanSpace ℝ (Fin n))
      (M := sphere (0 : E) 1)
  obtain ⟨t, ht, htc, htm⟩ := exists_finite_acute_refinement U hopen hcover hfree
  let V : t → Set (sphere (0 : E) 1) := fun j => j.val.2
  choose c hc using fun j : t => (ht j.val j.property).2.1
  have hVc : ∀ x, ∃ j, x ∈ V j := by
    intro x
    obtain ⟨j, hj, hx⟩ := htc x
    exact ⟨⟨j, hj⟩, hx⟩
  have hdim : finrank ℝ E = n + 1 := Fact.out
  apply acute_cover_contractible_of_multiplicity_lt V
    (fun j => (ht j.val j.property).1) hVc c hc
    (fun j => (ht j.val j.property).2.2.2)
  · rw [hdim]
    omega
  · intro x
    have hbound := hmult x
    have hrefine := htm x
    have heq : (Finset.univ.filter fun j : t => x ∈ V j).card =
        (t.filter fun j => x ∈ j.2).card := by
      change (t.attach.filter fun j : t => x ∈ j.val.2).card = _
      simpa only [Finset.card_map, Finset.card_attach] using
        congrArg Finset.card (Finset.filter_attach
          (fun j : Fin k × Set (sphere (0 : E) 1) => x ∈ j.2) t)
    rw [heq, hdim]
    omega

/-- The orthogonal-complement count supplies the general low-color obstruction. -/
theorem low_color_cover_contractible {n k : ℕ} [Fact (finrank ℝ E = n + 1)]
    (U : Fin k → Set (sphere (0 : E) 1)) (hopen : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hfree : ∀ i, OrthogonalityFree (U i))
    (hk : k ≤ 2 * n) : ContractibleSpace (sphere (0 : E) 1) := by
  classical
  apply open_cover_contractible_of_multiplicity_lt (n := n) U hopen hcover hfree
  intro x
  have := cover_color_multiplicity (n := n) U hcover hfree x
  omega

/-- Every finite relatively open orthogonality-free cover of the real unit sphere in
ambient dimension `n ≥ 2` has at least `2*n - 1` members. -/
theorem sphere_open_orthogonality_free_cover_lower_bound {n k : ℕ} (hn : 2 ≤ n)
    (U : Fin k → Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hfree : ∀ i, OrthogonalityFree (U i)) : 2 * n - 1 ≤ k := by
  by_contra hk
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1) :=
    ⟨by simp only [finrank_euclideanSpace_fin]; omega⟩
  apply SphereBrouwerObstruction.not_contractible_unit_sphere n (by omega)
  apply low_color_cover_contractible (n := n - 1) U hopen hcover hfree
  omega

open Classical in
/-- Restriction to the perpendicular unit circle requires at least three absent colors. -/
theorem sphere_three_absent_colors {k : ℕ}
    (U : Fin k → Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hfree : ∀ i, OrthogonalityFree (U i))
    (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    3 ≤ (Finset.univ.filter fun i => x ∉ U i).card := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  letI : Fact (finrank ℝ E = 2 + 1) := ⟨by simp [E]⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere x)
  let f : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → sphere (0 : E) 1 :=
    fun y => ⟨(b.repr.symm y.val : E), by
      rw [mem_sphere_zero_iff_norm]
      change ‖b.repr.symm y.val‖ = 1
      rw [b.repr.symm.norm_map, mem_sphere_zero_iff_norm.mp y.property]⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (b.repr.symm.continuous.comp continuous_subtype_val)
  have hperp : ∀ y, ⟪(x : E), (f y : E)⟫_ℝ = 0 := by
    intro y
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm y.val).property
  let t := Finset.univ.filter fun i => x ∉ U i
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let V : Fin (Fintype.card t) → Set (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    fun j => f ⁻¹' U (e j).val
  have hVcover : ∀ y, ∃ j, y ∈ V j := by
    intro y
    obtain ⟨i, hi⟩ := hcover (f y)
    have hx : x ∉ U i := fun hxi => hfree i x hxi (f y) hi (hperp y)
    let j : t := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    refine ⟨e.symm j, ?_⟩
    simpa [V, j] using hi
  have hVfree : ∀ j, OrthogonalityFree (V j) := by
    intro j y hy z hz hzero
    apply hfree (e j).val (f y) hy (f z) hz
    change ⟪b.repr.symm y.val, b.repr.symm z.val⟫_ℝ = 0
    rwa [b.repr.symm.inner_map_map]
  have h := sphere_open_orthogonality_free_cover_lower_bound (n := 2) (by omega)
    V (fun j => (hopen _).preimage hf) hVcover hVfree
  simpa only [Fintype.card_coe, Nat.reduceMul, Nat.reduceSub] using h

/-- Every finite relatively open orthogonality-free cover of the real two-sphere has at
least six members. The perpendicular circle supplies the strengthened point multiplicity. -/
theorem sphere_two_open_orthogonality_free_cover_lower_six {k : ℕ}
    (U : Fin k → Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hfree : ∀ i, OrthogonalityFree (U i)) : 6 ≤ k := by
  classical
  by_contra hk
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  apply SphereBrouwerObstruction.not_contractible_unit_sphere 3 (by omega)
  apply open_cover_contractible_of_multiplicity_lt (n := 2) U hopen hcover hfree
  intro x
  have habsent := sphere_three_absent_colors U hopen hcover hfree x
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i => x ∈ U i)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

end D5.S3.Topology.SphereOrthogonalityCover
