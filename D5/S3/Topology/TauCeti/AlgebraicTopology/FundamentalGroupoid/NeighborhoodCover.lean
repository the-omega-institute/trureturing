/- GID: D5/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover
   generality: G
   mirror-B: D5/B/S3/Topology/TauCeti/AlgebraicTopology/FundamentalGroupoid/NeighborhoodCover
   mirror-E: none(waiver:arbitrary-neighborhood-cover)
   anchors: []
   utility: none
   digest: Arbitrary neighborhood covers glue strict fundamental-groupoid functors and their open Cech cocone is an ordinary colimit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: The Tau Ceti contributors; Kim Morrison; Lean FRO, LLC
This owner receives the arbitrary-neighborhood-cover fundamental-groupoid gluing theorem and
its ordinary finite-intersection Cech colimit consumer from the Tau Ceti source at the
immutable source revision recorded in docs/reports/licenses/tauceti-sphere-port-LICENSE.txt.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import D5.S3.Topology.TauCeti.Topology.UnitInterval
import D5.S3.Topology.TauCeti.Topology.Homotopy.Path
universe u v

noncomputable section

open Function Set Metric Topology

namespace TauCeti
theorem lebesgue_number_lemma_of_metric_of_mem_nhds {α : Type*} {ι : Sort*} [PseudoMetricSpace α]
    {s : Set α} {c : ι → Set α} (hs : IsCompact s) (hc : ∀ x ∈ s, ∃ i, c i ∈ 𝓝 x) :
    ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric hs (c := fun i ↦ interior (c i))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 <| (hc x hx).imp fun _ ↦ mem_interior_iff_mem_nhds.2
  exact ⟨δ, hδ, fun x hx ↦ (h x hx).imp fun _ hi ↦ hi.trans interior_subset⟩

end TauCeti
open CategoryTheory
namespace Path.Homotopic.Quotient
@[simp]
theorem cast_mem_arrows_iff
    {X : Type*} [TopologicalSpace X]
    {S : CategoryTheory.Subgroupoid (_root_.FundamentalGroupoid X)} {a b a' b' : X}
    (q : Path.Homotopic.Quotient a b) (ha : a' = a) (hb : b' = b) :
    (q.cast (x' := a') (y' := b') ha hb :
        _root_.FundamentalGroupoid.mk a' ⟶ _root_.FundamentalGroupoid.mk b') ∈
        S.arrows (_root_.FundamentalGroupoid.mk a') (_root_.FundamentalGroupoid.mk b') ↔
      (q : _root_.FundamentalGroupoid.mk a ⟶ _root_.FundamentalGroupoid.mk b) ∈
        S.arrows (_root_.FundamentalGroupoid.mk a) (_root_.FundamentalGroupoid.mk b) := by
  subst ha hb
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
end Path.Homotopic.Quotient
namespace ContinuousMap
theorem fundamentalGroupoid_map_obj_injective {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace A] (f : C(X, A)) (hf : Function.Injective f) :
    Function.Injective (_root_.FundamentalGroupoid.map f).obj := by
  rintro ⟨a⟩ ⟨b⟩ h
  exact congrArg _root_.FundamentalGroupoid.mk (hf (congrArg _root_.FundamentalGroupoid.as h))
end ContinuousMap

open CategoryTheory TopologicalSpace

namespace TauCeti.TopCat
abbrev CechIndex (ι : Type u) := OrderDual {s : Finset ι // s.Nonempty}
namespace CechIndex
variable {ι : Type u}
def singleton (i : ι) : CechIndex ι :=
  OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩
@[simp]
lemma coe_singleton (i : ι) : (singleton i).1 = {i} := (rfl)
@[simp]
lemma le_iff {s t : CechIndex ι} : s ≤ t ↔ t.1 ⊆ s.1 := Iff.rfl
end CechIndex
variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)
def cechIntersection (s : CechIndex ι) : Opens X :=
  s.1.inf U
@[simp]
lemma mem_cechIntersection (x : X) (s : CechIndex ι) :
    x ∈ cechIntersection U s ↔ ∀ i ∈ s.1, x ∈ U i := by
  simp [← SetLike.mem_coe, cechIntersection, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
@[simp]
lemma cechIntersection_singleton (i : ι) :
    cechIntersection U (CechIndex.singleton i) = U i :=
  Finset.inf_singleton
lemma cechIntersection_mono {s t : CechIndex ι} (h : s ≤ t) :
    cechIntersection U s ≤ cechIntersection U t :=
  Finset.inf_mono h
def cechOpenDiagram : CechIndex ι ⥤ Opens X where
  obj := cechIntersection U
  map f := homOfLE (cechIntersection_mono U f.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
@[simp]
lemma cechOpenDiagram_obj (s : CechIndex ι) :
    (cechOpenDiagram U).obj s = cechIntersection U s := (rfl)
@[simp]
lemma cechOpenDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    (cechOpenDiagram U).map f =
      eqToHom (cechOpenDiagram_obj U s) ≫ homOfLE (cechIntersection_mono U f.le) ≫
        eqToHom (cechOpenDiagram_obj U t).symm :=
  Subsingleton.elim _ _
def cechTopDiagram : CechIndex ι ⥤ TopCat :=
  cechOpenDiagram U ⋙ Opens.toTopCat X
@[simp]
lemma cechTopDiagram_obj (s : CechIndex ι) :
    (cechTopDiagram U).obj s = TopCat.of (cechIntersection U s) := (rfl)
@[simp]
lemma cechTopDiagram_map_apply {s t : CechIndex ι} (f : s ⟶ t)
    (x : TopCat.of (cechIntersection U s)) :
    eqToHom (cechTopDiagram_obj U t)
        ((cechTopDiagram U).map f (eqToHom (cechTopDiagram_obj U s).symm x)) =
      ⟨x.1, cechIntersection_mono U f.le x.2⟩ :=
  Opens.toTopCat_map X (f := (cechOpenDiagram U).map f)
def cechInclusion (s : CechIndex ι) : (cechTopDiagram U).obj s ⟶ X :=
  Opens.inclusion' (cechIntersection U s)
@[simp]
lemma cechInclusion_apply (s : CechIndex ι) (x : TopCat.of (cechIntersection U s)) :
    cechInclusion U s (eqToHom (cechTopDiagram_obj U s).symm x) = x.1 :=
  congrFun Opens.coe_inclusion' x
@[simp, reassoc]
lemma cechTopDiagram_map_comp_inclusion {s t : CechIndex ι} (f : s ⟶ t) :
    (cechTopDiagram U).map f ≫ cechInclusion U t = cechInclusion U s := by
  ext x
  exact (cechInclusion_apply U t _).trans (congrArg Subtype.val (cechTopDiagram_map_apply U f x))
def cechInclusionNatTrans :
    cechTopDiagram U ⟶ (Functor.const (CechIndex ι)).obj X where
  app := cechInclusion U
  naturality _ _ f := cechTopDiagram_map_comp_inclusion U f
@[simp]
lemma cechInclusionNatTrans_app (s : CechIndex ι) :
    (cechInclusionNatTrans U).app s = cechInclusion U s := (rfl)
lemma exists_mem_cechIntersection_singleton (hU : IsOpenCover U) (x : X) :
    ∃ i, x ∈ cechIntersection U (CechIndex.singleton i) := by
  simpa using hU.exists_mem x

end TauCeti.TopCat

open CategoryTheory Set Topology
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}

namespace TauCeti
namespace FundamentalGroupoid
open _root_.FundamentalGroupoid
private theorem mk_mem_iSup_im {x y : X} (γ : Path x y) {i : ι} (hγ : range γ ⊆ U i) :
    (Path.Homotopic.Quotient.mk γ : mk x ⟶ mk y) ∈
      (⨆ j, Subgroupoid.im (map (ContinuousMap.subtypeVal (U j)))
        (ContinuousMap.fundamentalGroupoid_map_obj_injective
          (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)).arrows (mk x) (mk y) := by
  refine (Subgroupoid.le_iff _ _).1 (le_iSup (fun j ↦ Subgroupoid.im
    (map (ContinuousMap.subtypeVal (U j)))
      (ContinuousMap.fundamentalGroupoid_map_obj_injective
        (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)) i) ?_
  have hmem : ∀ t, γ t ∈ U i := fun t ↦ hγ ⟨t, rfl⟩
  have hx : x ∈ U i := γ.source ▸ hmem 0
  have hy : y ∈ U i := γ.target ▸ hmem 1
  have h := Subgroupoid.Map.Arrows.im (φ := map (ContinuousMap.subtypeVal (U i)))
    (hφ := ContinuousMap.fundamentalGroupoid_map_obj_injective
      (ContinuousMap.subtypeVal (U i)) Subtype.val_injective) (S := ⊤)
    (Path.Homotopic.Quotient.mk (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hmem)) trivial
  rw [map_map, ← Path.Homotopic.Quotient.mk_map] at h
  have hp : (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) hmem).map
      (ContinuousMap.subtypeVal (U i)).continuous = γ :=
    Path.map_codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) γ hmem
  rw [hp] at h
  exact h
private theorem mk_concat_mem_iSup_im (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (hF : ∀ k, ∃ i, range (F k) ⊆ U i) :
    (Path.Homotopic.Quotient.mk (Path.concat p F) : mk (p 0) ⟶ mk (p (Fin.last n))) ∈
      (⨆ j, Subgroupoid.im (map (ContinuousMap.subtypeVal (U j)))
        (ContinuousMap.fundamentalGroupoid_map_obj_injective
          (ContinuousMap.subtypeVal (U j)) Subtype.val_injective)).arrows
        (mk (p 0)) (mk (p (Fin.last n))) := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := hU (p 0)
    rw [Path.concat_zero]
    exact mk_mem_iSup_im _ (by simpa using mem_of_mem_nhds hi)
  | succ n ih =>
    obtain ⟨i, hi⟩ := hF (Fin.last n)
    rw [Path.concat_succ]
    exact Subgroupoid.mul _ (ih (p ∘ Fin.castSucc) (fun k ↦ F k.castSucc) fun k ↦ hF k.castSucc)
      (mk_mem_iSup_im _ hi)
theorem iSup_im_map_subtypeVal_eq_top (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) :
    ⨆ i, Subgroupoid.im (map (ContinuousMap.subtypeVal (U i)))
      (ContinuousMap.fundamentalGroupoid_map_obj_injective
        (ContinuousMap.subtypeVal (U i)) Subtype.val_injective) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨⟨x⟩, ⟨y⟩, f⟩ -
  induction f using Path.Homotopic.Quotient.ind with | mk γ =>
  obtain ⟨n, t, ht0, htn, -, ht⟩ := γ.exists_monotone_range_subpath_subset fun s ↦ by
    obtain ⟨i, hi⟩ := hU (γ s)
    exact ⟨i, γ.continuous.continuousAt.preimage_mem_nhds hi⟩
  have hsub := mk_concat_mem_iSup_im hU (γ ∘ t) (fun k ↦ γ.subpath (t k.castSucc) (t k.succ)) ht
  rw [Path.Homotopic.Quotient.eq.2 (Path.Homotopic.concat_subpath γ t)] at hsub
  have hγ : ∀ (a b : I) (ha : a = 0) (hb : b = 1),
      γ = (γ.subpath a b).cast (by simp [ha]) (by simp [hb]) := by
    rintro _ _ rfl rfl
    rw [Path.subpath_zero_one]
    rfl
  rw [hγ _ _ ht0 htn, Path.Homotopic.Quotient.mk_cast]
  exact (Path.Homotopic.Quotient.cast_mem_arrows_iff _ _ _).2 hsub
theorem functor_ext (hU : ∀ x, ∃ i, U i ∈ 𝓝 x) {D : Type*} [Category D]
    {F G : _root_.FundamentalGroupoid X ⥤ D}
    (h : ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ F =
      map (ContinuousMap.subtypeVal (U i)) ⋙ G) :
    F = G := by
  have hobj : ∀ c, F.obj c = G.obj c := by
    rintro ⟨x⟩
    obtain ⟨i, hi⟩ := hU x
    have hx := CategoryTheory.Functor.congr_obj (h i) (mk ⟨x, mem_of_mem_nhds hi⟩)
    change F.obj (mk x) = G.obj (mk x) at hx
    exact hx
  let S : Subgroupoid (_root_.FundamentalGroupoid X) :=
    { arrows := fun c d ↦ {f | F.map f = eqToHom (hobj c) ≫ G.map f ≫ eqToHom (hobj d).symm}
      inv := fun {c d f} hf ↦ by
        simp only [mem_ofPred_eq, Groupoid.inv_eq_inv, Functor.map_inv] at hf ⊢
        simp [hf]
      mul := fun {c d e f} hf {g} hg ↦ by
        simp only [mem_ofPred_eq, Functor.map_comp] at hf hg ⊢
        simp [hf, hg] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← iSup_im_map_subtypeVal_eq_top hU]
    refine iSup_le fun i ↦ ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨a, b, g⟩ -
    exact CategoryTheory.Functor.congr_hom (h i) g
  refine CategoryTheory.Functor.ext hobj fun c d f ↦ ?_
  have hf : f ∈ S.arrows c d := by
    rw [hS]
    trivial
  exact hf
end FundamentalGroupoid

end TauCeti
section
open CategoryTheory Set Topology Metric
open scoped unitInterval

namespace TauCeti.FundamentalGroupoid
open _root_.FundamentalGroupoid
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}
  {D : Type*} [Category D]

section Partition
private def pt (N k : ℕ) : I := Set.Icc.addNSMul zero_le_one (1 / N : ℝ) k
private lemma coe_pt {N k : ℕ} (hk : k ≤ N) : (pt N k : ℝ) = k / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : k = 0 := by omega
    rw [pt, Set.Icc.addNSMul_zero]
    simp
  rw [pt, Set.Icc.addNSMul, projIcc_of_mem]
  · simp [div_eq_mul_inv]
  · simp only [zero_add, nsmul_eq_mul, mem_Icc]
    refine ⟨by positivity, ?_⟩
    rw [mul_one_div, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast hk
private lemma pt_zero (N : ℕ) : pt N 0 = 0 := by
  apply Subtype.ext
  exact Set.Icc.addNSMul_zero (a := (0 : ℝ)) (b := 1) (δ := (1 / N : ℝ)) zero_le_one
private lemma pt_self {N : ℕ} (hN : N ≠ 0) : pt N N = 1 := by
  apply Subtype.ext
  rw [coe_pt le_rfl]
  simp [hN]
private lemma pt_eq_one {N k : ℕ} (hN : N ≠ 0) (hk : N ≤ k) : pt N k = 1 := by
  rw [pt, Set.Icc.addNSMul, projIcc_of_right_le]
  · rfl
  · rw [zero_add, nsmul_eq_mul, mul_one_div, le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hk
private lemma pt_mono (N : ℕ) : Monotone (pt N) :=
  Set.Icc.monotone_addNSMul _ (by positivity)
private lemma pt_mul {M N k : ℕ} (hM : M ≠ 0) (hk : k ≤ N) : pt (M * N) (M * k) = pt N k := by
  apply Subtype.ext
  rw [coe_pt hk, coe_pt (Nat.mul_le_mul_left M hk)]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast hM)]
private lemma abs_sub_pt_le {N k : ℕ} {t : I} (ht : t ∈ Icc (pt N k) (pt N (k + 1))) :
    |(t : ℝ) - pt N k| ≤ 1 / N :=
  Set.Icc.abs_sub_addNSMul_le _ (by positivity) k ht
private lemma coe_convexComb_pt {N k : ℕ} (hk : k < N) (t : I) :
    (Icc.convexComb (pt N k) (pt N (k + 1)) t : ℝ) = (k + t) / N := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hk).ne'
  rw [Icc.coe_convexComb, coe_pt hk.le, coe_pt hk]
  push_cast
  field_simp
  ring
private lemma mem_Icc_pt {N k : ℕ} : pt N k ∈ Icc (pt N k) (pt N (k + 1)) :=
  left_mem_Icc.2 (pt_mono N k.le_succ)
private lemma mem_Icc_pt_succ {N k : ℕ} : pt N (k + 1) ∈ Icc (pt N k) (pt N (k + 1)) :=
  right_mem_Icc.2 (pt_mono N k.le_succ)
private lemma convexComb_mem_Icc_pt (N k : ℕ) (u : I) :
    Icc.convexComb (pt N k) (pt N (k + 1)) u ∈ Icc (pt N k) (pt N (k + 1)) :=
  ⟨Icc.le_convexComb (pt_mono N k.le_succ) u, Icc.convexComb_le (pt_mono N k.le_succ) u⟩
private lemma trans_pt_left {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ} (hk : k ≤ N) :
    γ.trans δ (pt (N + N) k) = γ (pt N k) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : k = 0 := by omega
    simp [pt_zero]
  have _ : (0 : ℝ) < N := by exact_mod_cast hN
  refine Path.trans_apply_of_le γ δ ?_ (pt N k) ?_
  · rw [coe_pt (by omega : k ≤ N + N)]
    push_cast
    field_simp
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  · rw [coe_pt (by omega : k ≤ N + N), coe_pt hk]
    push_cast
    field_simp
    ring
private lemma trans_pt_right {x y z : X} (γ : Path x y) (δ : Path y z) {N : ℕ} (hN : N ≠ 0)
    (k : ℕ) : γ.trans δ (pt (N + N) (N + k)) = δ (pt N k) := by
  rcases le_or_gt k N with hk | hk
  · have _ : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    refine Path.trans_apply_of_ge γ δ ?_ (pt N k) ?_
    · rw [coe_pt (by omega : N + k ≤ N + N)]
      push_cast
      field_simp
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
      nlinarith
    · rw [coe_pt (by omega : N + k ≤ N + N), coe_pt hk]
      push_cast
      field_simp
      ring
  · rw [pt_eq_one (by omega) (by omega), pt_eq_one hN hk.le, Path.target, Path.target]
private lemma trans_subpath_left {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ} (hk : k < N)
    (t : I) : (γ.trans δ).subpath (pt (N + N) k) (pt (N + N) (k + 1)) t =
      γ.subpath (pt N k) (pt N (k + 1)) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hk
  refine Path.trans_apply_of_le γ δ ?_ (Icc.convexComb (pt N k) (pt N (k + 1)) t) ?_
  · rw [coe_convexComb_pt (by omega : k < N + N)]
    push_cast
    field_simp
    have ht : (t : ℝ) ≤ 1 := t.2.2
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    have hk1 : (k : ℝ) + 1 ≤ N := by
      exact_mod_cast (Nat.succ_le_of_lt hk)
    nlinarith
  · rw [coe_convexComb_pt (by omega : k < N + N), coe_convexComb_pt hk]
    push_cast
    field_simp
    ring
private lemma trans_subpath_right {x y z : X} (γ : Path x y) (δ : Path y z) {N k : ℕ}
    (hk : k < N) (t : I) :
    (γ.trans δ).subpath (pt (N + N) (N + k)) (pt (N + N) (N + k + 1)) t =
      δ.subpath (pt N k) (pt N (k + 1)) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hk
  refine Path.trans_apply_of_ge γ δ ?_ (Icc.convexComb (pt N k) (pt N (k + 1)) t) ?_
  · rw [coe_convexComb_pt (by omega : N + k < N + N)]
    push_cast
    field_simp
    have ht : (0 : ℝ) ≤ t := t.2.1
    have hk' : (k : ℝ) < N := by exact_mod_cast hk
    nlinarith
  · rw [coe_convexComb_pt (by omega : N + k < N + N), coe_convexComb_pt hk]
    push_cast
    field_simp
    ring
private def colSeg {x y : X} {p q : Path x y} (H : p.Homotopy q) (N l k : ℕ) :
    Path (H.eval (pt N l) (pt N k)) (H.eval (pt N (l + 1)) (pt N k)) where
  toFun u := H (Icc.convexComb (pt N l) (pt N (l + 1)) u, pt N k)
  continuous_toFun := H.continuous.comp ((Icc.continuous_convexComb _ _).prodMk continuous_const)
  source' := by simp
  target' := by simp

end Partition
variable (hU : ∀ x, ∃ i, U i ∈ 𝓝 x)

section Fine
variable (U) in
private def IsFine {x y : X} (γ : Path x y) (N : ℕ) : Prop :=
  ∀ k, ∃ i, ∀ t ∈ Icc (pt N k) (pt N (k + 1)), γ t ∈ U i
private lemma IsFine.subpath_mem {x y : X} {γ : Path x y} {N : ℕ} (h : IsFine U γ N) (k : ℕ) :
    ∃ i, ∀ t, γ.subpath (pt N k) (pt N (k + 1)) t ∈ U i :=
  (h k).imp fun _ hi ↦ Path.subpath_apply_mem hi mem_Icc_pt mem_Icc_pt_succ
include hU
private lemma exists_isFine {x y : X} (γ : Path x y) :
    ∃ N₀, ∀ N, N₀ ≤ N → N ≠ 0 ∧ IsFine U γ N := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds isCompact_univ
    (c := fun i ↦ γ ⁻¹' U i) fun t _ ↦
      (hU (γ t)).imp fun _ ↦ γ.continuous.continuousAt.preimage_mem_nhds
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n + 1, fun N hN ↦ ⟨by omega, fun k ↦ ?_⟩⟩
  obtain ⟨i, hi⟩ := h (pt N k) (mem_univ _)
  refine ⟨i, fun t ht ↦ hi ?_⟩
  rw [mem_ball, Subtype.dist_eq, Real.dist_eq]
  exact (abs_sub_pt_le ht).trans_lt <|
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hN)).trans_lt hn
private lemma exists_isFine_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    ∃ N, N ≠ 0 ∧ ∀ l k, ∃ i, ∀ t ∈ Icc (pt N l) (pt N (l + 1)),
      ∀ s ∈ Icc (pt N k) (pt N (k + 1)), H (t, s) ∈ U i := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds isCompact_univ
    (c := fun i ↦ H ⁻¹' U i) fun ts _ ↦
      (hU (H ts)).imp fun _ ↦ H.continuous.continuousAt.preimage_mem_nhds
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hN : (1 / ((n + 1 : ℕ) : ℝ)) < δ := by exact_mod_cast hn
  refine ⟨n + 1, n.succ_ne_zero, fun l k ↦ ?_⟩
  obtain ⟨i, hi⟩ := h (pt (n + 1) l, pt (n + 1) k) (mem_univ _)
  refine ⟨i, fun t ht s hs ↦ hi ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq,
    Real.dist_eq]
  exact ⟨(abs_sub_pt_le ht).trans_lt hN, (abs_sub_pt_le hs).trans_lt hN⟩

end Fine

section Construction
variable (F : ∀ i, _root_.FundamentalGroupoid (U i) ⥤ D)
  (hF : ∀ i j, map (ContinuousMap.inclusion (inter_subset_left : U i ∩ U j ⊆ U i)) ⋙ F i =
    map (ContinuousMap.inclusion (inter_subset_right : U i ∩ U j ⊆ U j)) ⋙ F j)
private def glueObj (x : X) : D :=
  (F (hU x).choose).obj (mk ⟨x, mem_of_mem_nhds (hU x).choose_spec⟩)
include hF
private lemma obj_eq (i : ι) {x : X} (hx : x ∈ U i) :
    (F i).obj (mk ⟨x, hx⟩) = glueObj hU F x :=
  Functor.congr_obj (hF i (hU x).choose) (mk ⟨x, hx, mem_of_mem_nhds (hU x).choose_spec⟩)
private def locVal (i : ι) {x y : X} (P : Path x y) (hP : ∀ t, P t ∈ U i) :
    glueObj hU F x ⟶ glueObj hU F y :=
  eqToHom (obj_eq hU F hF i (P.source ▸ hP 0)).symm ≫
    (F i).map (Path.Homotopic.Quotient.mk
      (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP)) ≫
    eqToHom (obj_eq hU F hF i (P.target ▸ hP 1))
private lemma locVal_congr_index (i j : ι) {x y : X} (P : Path x y) (hi : ∀ t, P t ∈ U i)
    (hj : ∀ t, P t ∈ U j) : locVal hU F hF i P hi = locVal hU F hF j P hj := by
  have hx : x ∈ U i ∩ U j := P.source ▸ ⟨hi 0, hj 0⟩
  have hy : y ∈ U i ∩ U j := P.target ▸ ⟨hi 1, hj 1⟩
  have h := Functor.congr_hom (hF i j) (Path.Homotopic.Quotient.mk
    (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (fun t ↦ ⟨hi t, hj t⟩)) :
      _root_.FundamentalGroupoid.mk ⟨x, hx⟩ ⟶ _root_.FundamentalGroupoid.mk ⟨y, hy⟩)
  have hPi : (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun t ↦ ⟨hi t, hj t⟩).map
      (ContinuousMap.inclusion inter_subset_left).continuous =
      P.codRestrict (x := ⟨x, hx.1⟩) (y := ⟨y, hy.1⟩) hi := by
    ext t
    exact (Path.codRestrict_coe (s := U i ∩ U j) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) P
        (fun t ↦ ⟨hi t, hj t⟩) t).trans
      (Path.codRestrict_coe (x := ⟨x, hx.1⟩) (y := ⟨y, hy.1⟩) P hi t).symm
  have hPj : (P.codRestrict (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) fun t ↦ ⟨hi t, hj t⟩).map
      (ContinuousMap.inclusion inter_subset_right).continuous =
      P.codRestrict (x := ⟨x, hx.2⟩) (y := ⟨y, hy.2⟩) hj := by
    ext t
    exact (Path.codRestrict_coe (s := U i ∩ U j) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) P
        (fun t ↦ ⟨hi t, hj t⟩) t).trans
      (Path.codRestrict_coe (x := ⟨x, hx.2⟩) (y := ⟨y, hy.2⟩) P hj t).symm
  have h' : ((F i).map (Path.Homotopic.Quotient.mk (P.codRestrict hi) :
        mk (⟨x, hx.1⟩ : U i) ⟶ mk (⟨y, hy.1⟩ : U i))) =
      eqToHom ((obj_eq hU F hF i hx.1).trans (obj_eq hU F hF j hx.2).symm) ≫
        (F j).map (Path.Homotopic.Quotient.mk (P.codRestrict hj) :
          mk (⟨x, hx.2⟩ : U j) ⟶ mk (⟨y, hy.2⟩ : U j)) ≫
        eqToHom ((obj_eq hU F hF j hy.2).trans (obj_eq hU F hF i hy.1).symm) := by
    rw [← hPi, ← hPj]
    exact h
  simp only [locVal]
  rw [h']
  simp
private lemma locVal_trans (i : ι) {x y z : X} (P : Path x y) (Q : Path y z)
    (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) (hPQ : ∀ t, P.trans Q t ∈ U i) :
    locVal hU F hF i (P.trans Q) hPQ = locVal hU F hF i P hP ≫ locVal hU F hF i Q hQ := by
  have h : (P.trans Q).codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hPQ =
      (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP).trans
        (Q.codRestrict (x := ⟨y, P.target ▸ hP 1⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hQ) := by
    ext t
    simp only [Path.codRestrict_coe, Path.trans_apply]
    split_ifs <;> simp
  simp only [locVal, h, Path.Homotopic.Quotient.mk_trans]
  rw [← comp_eq, Functor.map_comp]
  simp
private lemma locVal_comp_eq_of_trans (i : ι) {x y z : X} (P : Path x y) (Q : Path y z)
    (R : Path x z) (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) (hR : ∀ t, R t ∈ U i)
    (h : Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          (P.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨y, P.target ▸ hP 1⟩) hP))
        (Path.Homotopic.Quotient.mk
          (Q.codRestrict (x := ⟨y, P.target ▸ hP 1⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hQ)) =
      Path.Homotopic.Quotient.mk
        (R.codRestrict (x := ⟨x, P.source ▸ hP 0⟩) (y := ⟨z, Q.target ▸ hQ 1⟩) hR)) :
    locVal hU F hF i P hP ≫ locVal hU F hF i Q hQ = locVal hU F hF i R hR := by
  simp only [locVal, ← h]
  rw [← comp_eq, Functor.map_comp]
  simp
private lemma locVal_congr (i : ι) {x y x' y' : X} (P : Path x y) (Q : Path x' y')
    (hx : x = x') (hy : y = y') (h : ∀ t, P t = Q t) (hP : ∀ t, P t ∈ U i)
    (hQ : ∀ t, Q t ∈ U i) :
    locVal hU F hF i P hP =
      eqToHom (congrArg (glueObj hU F) hx) ≫ locVal hU F hF i Q hQ ≫
        eqToHom (congrArg (glueObj hU F) hy).symm := by
  subst hx hy
  obtain rfl : P = Q := Path.ext (funext h)
  simp
private lemma locVal_eq_of_simplyConnected (i : ι) {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (g : C(Y, X)) (hg : ∀ y, g y ∈ U i) {y₀ y₁ : Y}
    (α β : Path y₀ y₁) {x₀ x₁ : X} (P Q : Path x₀ x₁) (hPα : ∀ t, P t = g (α t))
    (hQβ : ∀ t, Q t = g (β t)) (hP : ∀ t, P t ∈ U i) (hQ : ∀ t, Q t ∈ U i) :
    locVal hU F hF i P hP = locVal hU F hF i Q hQ := by
  have hx : x₀ = g y₀ := by rw [← P.source, hPα, α.source]
  have hy : x₁ = g y₁ := by rw [← P.target, hPα, α.target]
  subst hx hy
  obtain rfl : P = α.map g.continuous := Path.ext (funext hPα)
  obtain rfl : Q = β.map g.continuous := Path.ext (funext hQβ)
  let g' : C(Y, U i) := ⟨fun y ↦ ⟨g y, hg y⟩, g.continuous.codRestrict hg⟩
  have hα : (α.map g.continuous).codRestrict (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) hP =
      α.map g'.continuous := by
    ext t
    exact Path.codRestrict_coe (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) _ hP t
  have hβ : (β.map g.continuous).codRestrict (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) hQ =
      β.map g'.continuous := by
    ext t
    exact Path.codRestrict_coe (x := ⟨g y₀, hg y₀⟩) (y := ⟨g y₁, hg y₁⟩) _ hQ t
  simp only [locVal, hα, hβ,
    Path.Homotopic.Quotient.eq.2 ((SimplyConnectedSpace.paths_homotopic α β).map g')]
private lemma locVal_refl (i : ι) (x : X) (h : ∀ t, Path.refl x t ∈ U i) :
    locVal hU F hF i (Path.refl x) h = 𝟙 _ := by
  have hr : (Path.refl x).codRestrict (x := ⟨x, h 0⟩) (y := ⟨x, h 0⟩) h =
      Path.refl (⟨x, h 0⟩ : U i) := by
    ext t
    exact Path.codRestrict_coe (x := ⟨x, h 0⟩) (y := ⟨x, h 0⟩) _ h t
  have hid : (Path.Homotopic.Quotient.mk (Path.refl (⟨x, h 0⟩ : U i)) :
      _root_.FundamentalGroupoid.mk (⟨x, h 0⟩ : U i) ⟶
        _root_.FundamentalGroupoid.mk (⟨x, h 0⟩ : U i)) =
      𝟙 (mk (⟨x, h 0⟩ : U i)) :=
    (id_eq_path_refl _).symm
  simp [locVal, hr, hid]
private lemma locVal_eq_eqToHom (i : ι) {x y : X} (P : Path x y) (hP : ∀ t, P t ∈ U i)
    (hconst : ∀ t, P t = x) :
    locVal hU F hF i P hP = eqToHom (congrArg (glueObj hU F) (P.target ▸ hconst 1).symm) := by
  have hy : y = x := P.target ▸ hconst 1
  rw [locVal_congr hU F hF i P (Path.refl x) rfl hy hconst hP fun _ ↦ P.source ▸ hP 0,
    locVal_refl]
  simp
private def pathVal {x y : X} (P : Path x y) (h : ∃ i, ∀ t, P t ∈ U i) :
    glueObj hU F x ⟶ glueObj hU F y :=
  locVal hU F hF h.choose P h.choose_spec
private lemma pathVal_eq (i : ι) {x y : X} (P : Path x y) (h : ∃ i, ∀ t, P t ∈ U i)
    (hi : ∀ t, P t ∈ U i) : pathVal hU F hF P h = locVal hU F hF i P hi :=
  locVal_congr_index hU F hF _ _ P _ _
private lemma pathVal_eq_eqToHom {x y : X} (P : Path x y) (hP : ∃ i, ∀ t, P t ∈ U i)
    (hconst : ∀ t, P t = x) :
    pathVal hU F hF P hP = eqToHom (congrArg (glueObj hU F) (P.target ▸ hconst 1).symm) := by
  obtain ⟨i, hi⟩ := hP
  rw [pathVal_eq hU F hF i P _ hi]
  exact locVal_eq_eqToHom hU F hF i P hi hconst
private lemma pathVal_subpath_trans {x y : X} (γ : Path x y) (i : ι) {lo hi : I}
    (hγ : ∀ t ∈ Icc lo hi, γ t ∈ U i) {a b c : I} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi)
    (hc : c ∈ Icc lo hi) (hab : ∃ i, ∀ t, γ.subpath a b t ∈ U i)
    (hbc : ∃ i, ∀ t, γ.subpath b c t ∈ U i) (hac : ∃ i, ∀ t, γ.subpath a c t ∈ U i) :
    pathVal hU F hF (γ.subpath a b) hab ≫ pathVal hU F hF (γ.subpath b c) hbc =
      pathVal hU F hF (γ.subpath a c) hac := by
  rw [pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ ha hb),
    pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ hb hc),
    pathVal_eq hU F hF i _ _ (Path.subpath_apply_mem hγ ha hc)]
  have hlohi : lo ≤ hi := ha.1.trans ha.2
  obtain ⟨a', rfl⟩ : ∃ a', Icc.convexComb lo hi a' = a := ⟨_, (Icc.eq_convexComb ha.1 ha.2).symm⟩
  obtain ⟨b', rfl⟩ : ∃ b', Icc.convexComb lo hi b' = b := ⟨_, (Icc.eq_convexComb hb.1 hb.2).symm⟩
  obtain ⟨c', rfl⟩ : ∃ c', Icc.convexComb lo hi c' = c := ⟨_, (Icc.eq_convexComb hc.1 hc.2).symm⟩
  have haU : γ (Icc.convexComb lo hi a') ∈ U i := hγ _ ha
  have hbU : γ (Icc.convexComb lo hi b') ∈ U i := hγ _ hb
  have hcU : γ (Icc.convexComb lo hi c') ∈ U i := hγ _ hc
  let g : C(I, X) := γ.toContinuousMap.comp ⟨_, Icc.continuous_convexComb lo hi⟩
  let g' : C(I, U i) := ⟨fun t ↦ ⟨g t,
    hγ _ ⟨Icc.le_convexComb hlohi t, Icc.convexComb_le hlohi t⟩⟩,
    g.continuous.codRestrict _⟩
  let p : Path (g' 0) (g' 1) := Path.id.map g'.continuous
  have hp : ∀ t, (p t : X) = γ (Icc.convexComb lo hi t) := fun _ ↦ rfl
  have hpa : (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i) = p a' := Subtype.ext (hp a').symm
  have hpb : (⟨γ (Icc.convexComb lo hi b'), hbU⟩ : U i) = p b' := Subtype.ext (hp b').symm
  have hpc : (⟨γ (Icc.convexComb lo hi c'), hcU⟩ : U i) = p c' := Subtype.ext (hp c').symm
  let qab : Path (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi b'), hbU⟩ :=
    (γ.subpath (Icc.convexComb lo hi a') (Icc.convexComb lo hi b')).codRestrict
      (Path.subpath_apply_mem hγ ha hb)
  let qbc : Path (⟨γ (Icc.convexComb lo hi b'), hbU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi c'), hcU⟩ :=
    (γ.subpath (Icc.convexComb lo hi b') (Icc.convexComb lo hi c')).codRestrict
      (Path.subpath_apply_mem hγ hb hc)
  let qac : Path (⟨γ (Icc.convexComb lo hi a'), haU⟩ : U i)
      ⟨γ (Icc.convexComb lo hi c'), hcU⟩ :=
    (γ.subpath (Icc.convexComb lo hi a') (Icc.convexComb lo hi c')).codRestrict
      (Path.subpath_apply_mem hγ ha hc)
  have hab' : (p.subpath a' b').cast hpa hpb = qab := by
    ext t
    change γ (Icc.convexComb lo hi (Icc.convexComb a' b' t)) =
      γ (Icc.convexComb (Icc.convexComb lo hi a') (Icc.convexComb lo hi b') t)
    congr 1
    apply Subtype.ext
    simp only [Icc.coe_convexComb]
    ring_nf
  have hbc' : (p.subpath b' c').cast hpb hpc = qbc := by
    ext t
    change γ (Icc.convexComb lo hi (Icc.convexComb b' c' t)) =
      γ (Icc.convexComb (Icc.convexComb lo hi b') (Icc.convexComb lo hi c') t)
    congr 1
    apply Subtype.ext
    simp only [Icc.coe_convexComb]
    ring_nf
  have hac' : (p.subpath a' c').cast hpa hpc = qac := by
    ext t
    change γ (Icc.convexComb lo hi (Icc.convexComb a' c' t)) =
      γ (Icc.convexComb (Icc.convexComb lo hi a') (Icc.convexComb lo hi c') t)
    congr 1
    apply Subtype.ext
    simp only [Icc.coe_convexComb]
    ring_nf
  have hquot : Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk qab)
      (Path.Homotopic.Quotient.mk qbc) = Path.Homotopic.Quotient.mk qac := by
    rw [← hab', ← hbc', ← hac']
    exact Path.Homotopic.Quotient.subpath_cast_trans p a' b' c' hpa hpb hpc
  exact locVal_comp_eq_of_trans hU F hF i _ _ _ _ _ _ hquot
private lemma pathVal_congr {x y x' y' : X} (P : Path x y) (Q : Path x' y') (hx : x = x')
    (hy : y = y') (h : ∀ t, P t = Q t) (hP : ∃ i, ∀ t, P t ∈ U i) (hQ : ∃ i, ∀ t, Q t ∈ U i) :
    pathVal hU F hF P hP =
      eqToHom (congrArg (glueObj hU F) hx) ≫ pathVal hU F hF Q hQ ≫
        eqToHom (congrArg (glueObj hU F) hy).symm := by
  obtain ⟨i, hi⟩ := hQ
  rw [pathVal_eq hU F hF i P hP fun t ↦ h t ▸ hi t, pathVal_eq hU F hF i Q _ hi]
  exact locVal_congr hU F hF i P Q hx hy h _ hi
private def segVal {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (k : ℕ) :
    glueObj hU F (γ (pt N k)) ⟶ glueObj hU F (γ (pt N (k + 1))) :=
  pathVal hU F hF (γ.subpath (pt N k) (pt N (k + 1))) (h.subpath_mem k)
private lemma map_segVal_eq {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (i : ι)
    {lo hi : I} (hγ : ∀ t ∈ Icc lo hi, γ t ∈ U i) {a b : ℕ} (hab : a ≤ b)
    (hpt : ∀ j, a ≤ j → j ≤ b → pt N j ∈ Icc lo hi) :
    Functor.OfSequence.map (segVal hU F hF γ h) a b hab =
      pathVal hU F hF (γ.subpath (pt N a) (pt N b))
        ⟨i, Path.subpath_apply_mem hγ (hpt a le_rfl hab) (hpt b hab le_rfl)⟩ := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Functor.OfSequence.map_id, pathVal_eq hU F hF i _ _
      (Path.subpath_apply_mem hγ (hpt a le_rfl le_rfl) (hpt a le_rfl le_rfl)),
      locVal_eq_eqToHom hU F hF i _ _ fun t ↦ by simp]
    simp
  | succ b hab ih =>
    rw [Functor.OfSequence.map_comp _ a b (b + 1) hab b.le_succ,
      ih fun j hj hj' ↦ hpt j hj (by omega), Functor.OfSequence.map_le_succ, segVal,
      pathVal_subpath_trans hU F hF γ i hγ (hpt a le_rfl (by omega)) (hpt b hab (by omega))
        (hpt (b + 1) (by omega) le_rfl)]
private def liftN {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0) :
    glueObj hU F x ⟶ glueObj hU F y :=
  eqToHom (by rw [pt_zero, γ.source]) ≫
    Functor.OfSequence.map (segVal hU F hF γ h) 0 N N.zero_le ≫
      eqToHom (by rw [pt_self hN, γ.target])
private lemma liftN_eq_locVal {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0)
    (i : ι) (hγ : ∀ t, γ t ∈ U i) : liftN hU F hF γ h hN = locVal hU F hF i γ hγ := by
  have hmem : ∀ t, γ.subpath (pt N 0) (pt N N) t ∈ U i := fun _ ↦ hγ _
  rw [liftN, map_segVal_eq hU F hF γ h i (lo := 0) (hi := 1) (fun t _ ↦ hγ t) (Nat.zero_le N)
    fun j _ _ ↦ ⟨unitInterval.nonneg', unitInterval.le_one'⟩, pathVal_eq hU F hF i _ _ hmem,
    locVal_congr hU F hF i _ γ (by rw [pt_zero, γ.source]) (by rw [pt_self hN, γ.target])
      (fun t ↦ by simp [Path.subpath, pt_zero, pt_self hN]) hmem hγ]
  simp
private lemma liftN_congr {x y : X} (γ : Path x y) {N N' : ℕ} (hNN' : N = N') (h : IsFine U γ N)
    (h' : IsFine U γ N') (hN : N ≠ 0) (hN' : N' ≠ 0) :
    liftN hU F hF γ h hN = liftN hU F hF γ h' hN' := by
  subst hNN'
  rfl
private lemma liftN_mul {x y : X} (γ : Path x y) {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : IsFine U γ N) (h' : IsFine U γ (M * N)) :
    liftN hU F hF γ h' (mul_ne_zero hM hN) = liftN hU F hF γ h hN := by
  have key : ∀ k (hk : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF γ h') 0 (M * k) (M * k).zero_le =
        eqToHom (by rw [pt_zero, pt_zero]) ≫
          Functor.OfSequence.map (segVal hU F hF γ h) 0 k k.zero_le ≫
            eqToHom (by rw [pt_mul hM hk]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      obtain ⟨i, hi⟩ := h k
      rw [Functor.OfSequence.map_comp _ 0 (M * k) (M * (k + 1)) (M * k).zero_le
          (Nat.mul_le_mul_left M k.le_succ),
        map_segVal_eq hU F hF γ h' i hi (Nat.mul_le_mul_left M k.le_succ) fun j hj hj' ↦
          ⟨pt_mul hM (k.le_succ.trans hk) ▸ pt_mono _ hj, pt_mul hM hk ▸ pt_mono _ hj'⟩,
        ih (by omega), Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_le_succ, segVal,
        pathVal_congr hU F hF _ _ (by rw [pt_mul hM (k.le_succ.trans hk)])
          (by rw [pt_mul hM hk]) (fun t ↦ by rw [pt_mul hM (k.le_succ.trans hk), pt_mul hM hk]) _
          (h.subpath_mem k)]
      simp
  rw [liftN, liftN, key N le_rfl]
  simp
private def lift {x y : X} (γ : Path x y) : glueObj hU F x ⟶ glueObj hU F y :=
  liftN hU F hF γ ((exists_isFine hU γ).choose_spec _ le_rfl).2
    ((exists_isFine hU γ).choose_spec _ le_rfl).1
private lemma lift_eq_liftN {x y : X} (γ : Path x y) {N : ℕ} (h : IsFine U γ N) (hN : N ≠ 0) :
    lift hU F hF γ = liftN hU F hF γ h hN := by
  have hspec := (exists_isFine hU γ).choose_spec
  have hN₀ := (hspec _ le_rfl).1
  rw [lift, ← liftN_mul hU F hF γ hN hN₀ _
      (hspec _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN))).2,
    ← liftN_mul hU F hF γ hN₀ hN h (hspec _ (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hN))).2]
  exact liftN_congr hU F hF γ (Nat.mul_comm _ _) _ _ _ _
private lemma lift_eq_locVal {x y : X} (γ : Path x y) (i : ι) (hγ : ∀ t, γ t ∈ U i) :
    lift hU F hF γ = locVal hU F hF i γ hγ := by
  obtain ⟨N₀, hN₀⟩ := exists_isFine hU γ
  rw [lift_eq_liftN hU F hF γ (hN₀ N₀ le_rfl).2 (hN₀ N₀ le_rfl).1, liftN_eq_locVal]
private lemma lift_refl (x : X) : lift hU F hF (Path.refl x) = 𝟙 _ := by
  obtain ⟨i, hi⟩ := hU x
  rw [lift_eq_locVal hU F hF _ i fun _ ↦ mem_of_mem_nhds hi, locVal_refl]
private lemma lift_trans {x y z : X} (γ : Path x y) (δ : Path y z) :
    lift hU F hF (γ.trans δ) = lift hU F hF γ ≫ lift hU F hF δ := by
  obtain ⟨N₁, h₁⟩ := exists_isFine hU γ
  obtain ⟨N₂, h₂⟩ := exists_isFine hU δ
  obtain ⟨N₃, h₃⟩ := exists_isFine hU (γ.trans δ)
  set N := N₁ + N₂ + N₃
  obtain ⟨hN, hγ⟩ := h₁ N (by omega)
  obtain ⟨-, hδ⟩ := h₂ N (by omega)
  obtain ⟨hNN, hγδ⟩ := h₃ (N + N) (by omega)
  have first : ∀ k (hk : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) 0 k k.zero_le =
        eqToHom (by rw [pt_zero, pt_zero, Path.source, Path.source]) ≫
          Functor.OfSequence.map (segVal hU F hF γ hγ) 0 k k.zero_le ≫
            eqToHom (by rw [trans_pt_left γ δ hk]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      rw [Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ,
        Functor.OfSequence.map_le_succ, Functor.OfSequence.map_le_succ, ih (by omega), segVal,
        segVal,
        pathVal_congr hU F hF _ _ (trans_pt_left γ δ (by omega)) (trans_pt_left γ δ hk)
          (trans_subpath_left γ δ (by omega)) _ (hγ.subpath_mem k)]
      simp
  have second : ∀ k (_ : k ≤ N),
      Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) N (N + k) (N.le_add_right k) =
        eqToHom (by rw [← trans_pt_right γ δ hN 0, Nat.add_zero]) ≫
          Functor.OfSequence.map (segVal hU F hF δ hδ) 0 k k.zero_le ≫
            eqToHom (by rw [trans_pt_right γ δ hN]) := by
    intro k hk
    induction k with
    | zero => simp [Functor.OfSequence.map_id]
    | succ k ih =>
      have step : Functor.OfSequence.map (segVal hU F hF (γ.trans δ) hγδ) (N + k) (N + (k + 1))
          (by omega) = segVal hU F hF (γ.trans δ) hγδ (N + k) :=
        Functor.OfSequence.map_le_succ _ (N + k)
      rw [Functor.OfSequence.map_comp _ N (N + k) (N + (k + 1)) (N.le_add_right k) (by omega),
        Functor.OfSequence.map_comp _ 0 k (k + 1) k.zero_le k.le_succ, step,
        Functor.OfSequence.map_le_succ, ih (by omega), segVal,
        segVal, pathVal_congr hU F hF _ _ (trans_pt_right γ δ hN k)
          (trans_pt_right γ δ hN (k + 1)) (trans_subpath_right γ δ (by omega)) _
          (hδ.subpath_mem k)]
      simp
  rw [lift_eq_liftN hU F hF _ hγδ hNN, lift_eq_liftN hU F hF _ hγ hN,
    lift_eq_liftN hU F hF _ hδ hN, liftN, liftN, liftN,
    Functor.OfSequence.map_comp _ 0 N (N + N) N.zero_le (N.le_add_right N), first N le_rfl,
    second N le_rfl]
  simp
private lemma pathVal_cell {x y : X} {p q : Path x y} (H : p.Homotopy q) (N l k : ℕ) (i : ι)
    (hi : ∀ t ∈ Icc (pt N l) (pt N (l + 1)), ∀ s ∈ Icc (pt N k) (pt N (k + 1)), H (t, s) ∈ U i)
    (h₁ : ∃ i, ∀ t, (H.eval (pt N l)).subpath (pt N k) (pt N (k + 1)) t ∈ U i)
    (h₂ : ∃ i, ∀ t, colSeg H N l (k + 1) t ∈ U i) (h₃ : ∃ i, ∀ t, colSeg H N l k t ∈ U i)
    (h₄ : ∃ i, ∀ t, (H.eval (pt N (l + 1))).subpath (pt N k) (pt N (k + 1)) t ∈ U i) :
    pathVal hU F hF _ h₁ ≫ pathVal hU F hF _ h₂ = pathVal hU F hF _ h₃ ≫ pathVal hU F hF _ h₄ := by
  have : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have m₁ : ∀ t, (H.eval (pt N l)).subpath (pt N k) (pt N (k + 1)) t ∈ U i := fun t ↦ by
    simpa [Path.subpath] using hi _ mem_Icc_pt _ (convexComb_mem_Icc_pt N k t)
  have m₂ : ∀ t, colSeg H N l (k + 1) t ∈ U i := fun t ↦
    hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt_succ
  have m₃ : ∀ t, colSeg H N l k t ∈ U i := fun t ↦
    hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt
  have m₄ : ∀ t, (H.eval (pt N (l + 1))).subpath (pt N k) (pt N (k + 1)) t ∈ U i := fun t ↦ by
    simpa [Path.subpath] using hi _ mem_Icc_pt_succ _ (convexComb_mem_Icc_pt N k t)
  rw [pathVal_eq hU F hF i _ _ m₁, pathVal_eq hU F hF i _ _ m₂, pathVal_eq hU F hF i _ _ m₃,
    pathVal_eq hU F hF i _ _ m₄, ← locVal_trans hU F hF i _ _ m₁ m₂ (range_subset_iff.1 <|
      (Path.trans_range _ _).trans_subset <| union_subset (range_subset_iff.2 m₁)
        (range_subset_iff.2 m₂)),
    ← locVal_trans hU F hF i _ _ m₃ m₄ (range_subset_iff.1 <|
      (Path.trans_range _ _).trans_subset <| union_subset (range_subset_iff.2 m₃)
        (range_subset_iff.2 m₄))]
  let g : C(I × I, X) := H.toContinuousMap.comp
    ((ContinuousMap.mk _ (Icc.continuous_convexComb (pt N l) (pt N (l + 1)))).prodMap
      (ContinuousMap.mk _ (Icc.continuous_convexComb (pt N k) (pt N (k + 1)))))
  refine locVal_eq_of_simplyConnected hU F hF i g
    (fun z ↦ hi _ (convexComb_mem_Icc_pt N l z.1) _ (convexComb_mem_Icc_pt N k z.2))
    (((Path.refl 0).trans Path.id).prod (Path.id.trans (Path.refl 1)))
    ((Path.id.trans (Path.refl 1)).prod ((Path.refl 0).trans Path.id)) _ _ (fun t ↦ ?_)
    (fun t ↦ ?_) _ _ <;>
  · rw [Path.trans_apply]
    split_ifs with h <;> rw [one_div] at h <;> simp [g, colSeg, Path.subpath, Path.trans_apply, h]
private lemma lift_eq_of_homotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    lift hU F hF p = lift hU F hF q := by
  obtain ⟨N, hN, hcell⟩ := exists_isFine_homotopy hU H
  have hrow : ∀ l, IsFine U (H.eval (pt N l)) N := fun l k ↦
    (hcell l k).imp fun i hi s hs ↦ by simpa using hi _ mem_Icc_pt s hs
  have hcol : ∀ l k, ∃ i, ∀ t, colSeg H N l k t ∈ U i := fun l k ↦
    (hcell l k).imp fun i hi t ↦ hi _ (convexComb_mem_Icc_pt N l t) _ mem_Icc_pt
  have hstep : ∀ l, liftN hU F hF _ (hrow l) hN = liftN hU F hF _ (hrow (l + 1)) hN := by
    intro l
    have hsq : Functor.OfSequence.map (segVal hU F hF _ (hrow l)) 0 N N.zero_le ≫
        pathVal hU F hF (colSeg H N l N) (hcol l N) =
          pathVal hU F hF (colSeg H N l 0) (hcol l 0) ≫
            Functor.OfSequence.map (segVal hU F hF _ (hrow (l + 1))) 0 N N.zero_le :=
      (NatTrans.ofSequence (F := Functor.ofSequence (segVal hU F hF _ (hrow l)))
        (G := Functor.ofSequence (segVal hU F hF _ (hrow (l + 1))))
        (fun k ↦ pathVal hU F hF (colSeg H N l k) (hcol l k)) fun k ↦ by
          obtain ⟨i, hi⟩ := hcell l k
          rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
          exact pathVal_cell hU F hF H N l k i hi _ _ _ _).naturality (homOfLE N.zero_le)
    rw [pathVal_eq_eqToHom hU F hF (colSeg H N l 0) _ fun t ↦ by simp [colSeg, pt_zero],
      pathVal_eq_eqToHom hU F hF (colSeg H N l N) _ fun t ↦ by simp [colSeg, pt_self hN],
      comp_eqToHom_iff] at hsq
    rw [liftN, liftN, hsq]
    simp
  have hall : ∀ l, liftN hU F hF _ (hrow 0) hN = liftN hU F hF _ (hrow l) hN := fun l ↦ by
    induction l with
    | zero => rfl
    | succ l ih => exact ih.trans (hstep l)
  calc lift hU F hF p = lift hU F hF (H.eval (pt N 0)) := by rw [pt_zero, Path.Homotopy.eval_zero]
    _ = lift hU F hF (H.eval (pt N N)) := by
      rw [lift_eq_liftN hU F hF _ (hrow 0) hN, lift_eq_liftN hU F hF _ (hrow N) hN, hall N]
    _ = lift hU F hF q := by rw [pt_self hN, Path.Homotopy.eval_one]
def glue : _root_.FundamentalGroupoid X ⥤ D where
  obj x := glueObj hU F x.as
  map {x y} := Quotient.lift (lift hU F hF (x := x.as) (y := y.as))
    fun _ _ h ↦ lift_eq_of_homotopy hU F hF h.some
  map_id x := lift_refl hU F hF x.as
  map_comp := by
    rintro _ _ _ ⟨γ⟩ ⟨δ⟩
    exact lift_trans hU F hF γ δ
@[simp] theorem map_subtypeVal_comp_glue (i : ι) :
    map (ContinuousMap.subtypeVal (U i)) ⋙ glue hU F hF = F i := by
  refine CategoryTheory.Functor.ext (fun a ↦ (obj_eq hU F hF i a.as.2).symm) fun a b γ ↦ ?_
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  let γ' := γ.map continuous_subtype_val
  have hγ' : ∀ t, γ' t ∈ U i := fun t ↦ (γ t).2
  have hγ : γ'.codRestrict (x := a.as) (y := b.as) hγ' = γ := by
    ext t
    exact Path.codRestrict_coe (x := a.as) (y := b.as) _ _ t
  have key : locVal hU F hF i γ' hγ' = eqToHom (obj_eq hU F hF i a.as.2).symm ≫
      (F i).map (Path.Homotopic.Quotient.mk γ) ≫ eqToHom (obj_eq hU F hF i b.as.2) := by
    unfold locVal
    rw [hγ]
  exact (lift_eq_locVal hU F hF γ' i hγ').trans key
theorem eq_glue {G : _root_.FundamentalGroupoid X ⥤ D}
    (hG : ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ G = F i) : G = glue hU F hF :=
  functor_ext hU fun i ↦ (hG i).trans (map_subtypeVal_comp_glue hU F hF i).symm

end Construction
theorem existsUnique_extension {X : Type*} [TopologicalSpace X] {ι : Type*}
    {U : ι → Set X} {D : Type*} [Category D]
    (hU : ∀ x, ∃ i, U i ∈ 𝓝 x)
    (F : ∀ i, _root_.FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, map (ContinuousMap.inclusion (inter_subset_left : U i ∩ U j ⊆ U i)) ⋙ F i =
      map (ContinuousMap.inclusion (inter_subset_right : U i ∩ U j ⊆ U j)) ⋙ F j) :
    ∃! G : _root_.FundamentalGroupoid X ⥤ D,
      ∀ i, map (ContinuousMap.subtypeVal (U i)) ⋙ G = F i := by
  refine ⟨glue hU F hF, fun i ↦ map_subtypeVal_comp_glue hU F hF i, ?_⟩
  intro G hG
  exact eq_glue hU F hF hG

end TauCeti.FundamentalGroupoid

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

namespace TauCeti.FundamentalGroupoid
open TauCeti.TopCat
variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)
def cechDiagram : CechIndex ι ⥤ Grpd :=
  cechTopDiagram U ⋙ _root_.FundamentalGroupoid.fundamentalGroupoidFunctor
@[simp]
lemma cechDiagram_obj (s : CechIndex ι) :
    (cechDiagram U).obj s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj
        (TopCat.of (cechIntersection U s)) := by
  rw [cechDiagram, Functor.comp_obj, cechTopDiagram_obj]
@[simp]
lemma cechDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    eqToHom (cechDiagram_obj U s).symm ≫ (cechDiagram U).map f ≫
        eqToHom (cechDiagram_obj U t) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (eqToHom (cechTopDiagram_obj U s).symm ≫ (cechTopDiagram U).map f ≫
          eqToHom (cechTopDiagram_obj U t)) := by
  unfold cechDiagram
  simp only [Functor.comp_map, Functor.map_comp, eqToHom_map]
def cechCocone : Cocone (cechDiagram U) :=
  _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.mapCocone
    (Cocone.mk X (cechInclusionNatTrans U))
@[simp]
lemma cechCocone_pt : (cechCocone U).pt =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X := by
  rfl
@[simp]
lemma cechCocone_ι_app (s : CechIndex ι) :
    eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s ≫
        eqToHom (cechCocone_pt U) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s) := by
  simp only [cechCocone, Functor.mapCocone_ι_app, cechInclusionNatTrans_app, Functor.map_comp,
    eqToHom_map]
  rfl
lemma map_subtypeVal_eq_cechCocone_ι_app (s : CechIndex ι) :
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X))) =
      eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s := by
  have hinc : eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s =
      (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X)) :
        TopCat.of (cechIntersection U s) ⟶ X) := by
    ext x
    exact cechInclusion_apply U s x
  have hpt : eqToHom (cechCocone_pt U) = 𝟙 ((cechCocone U).pt) := rfl
  rw [← hinc, ← cechCocone_ι_app, hpt]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

end TauCeti.FundamentalGroupoid

open CategoryTheory Limits TopologicalSpace Topology
open scoped FundamentalGroupoid

namespace TauCeti.FundamentalGroupoid
open TauCeti.TopCat _root_.FundamentalGroupoid
variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)
private def coconeLeg (c : Cocone (cechDiagram U)) (s : CechIndex ι) :
    fundamentalGroupoidFunctor.obj (TopCat.of (cechIntersection U s)) ⟶ c.pt :=
  eqToHom (cechDiagram_obj U s).symm ≫ c.ι.app s
private lemma map_inclusion_comp_coconeLeg (c : Cocone (cechDiagram U)) {s t : CechIndex ι}
    (f : s ⟶ t) :
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (SetLike.coe_subset_coe.2 (cechIntersection_mono U f.le)))) ≫ coconeLeg U c t =
      coconeLeg U c s := by
  have hmap : eqToHom (cechTopDiagram_obj U s).symm ≫ (cechTopDiagram U).map f ≫
      eqToHom (cechTopDiagram_obj U t) = TopCat.ofHom (ContinuousMap.inclusion
        (SetLike.coe_subset_coe.2 (cechIntersection_mono U f.le))) := by
    ext x
    exact congrArg Subtype.val (cechTopDiagram_map_apply U f x)
  have h := cechDiagram_map U f
  rw [hmap] at h
  rw [coconeLeg, coconeLeg, ← h, ← c.w f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
variable {U}
private lemma exists_cechIntersection_singleton_mem_nhds (hU : IsOpenCover U) (x : X) :
    ∃ i, (cechIntersection U (CechIndex.singleton i) : Set X) ∈ 𝓝 x := by
  obtain ⟨i, hi⟩ := exists_mem_cechIntersection_singleton U hU x
  exact ⟨i, (cechIntersection U _).isOpen.mem_nhds hi⟩
private lemma coconeLeg_singleton_compat (c : Cocone (cechDiagram U)) (i j : ι) :
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (Set.inter_subset_left : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
          cechIntersection U (CechIndex.singleton j) ⊆ _))) ≫
      coconeLeg U c (CechIndex.singleton i) =
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (Set.inter_subset_right : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
          cechIntersection U (CechIndex.singleton j) ⊆ _))) ≫
      coconeLeg U c (CechIndex.singleton j) := by
  classical
  let s : CechIndex ι := OrderDual.toDual ⟨{i, j}, Finset.insert_nonempty i {j}⟩
  have hs : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
      cechIntersection U (CechIndex.singleton j) ⊆ cechIntersection U s := fun x hx ↦ by
    simp only [SetLike.mem_coe, mem_cechIntersection, CechIndex.coe_singleton,
      Finset.mem_singleton, forall_eq, Set.mem_inter_iff] at hx ⊢
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact hx.1
    · exact Finset.mem_singleton.1 hk ▸ hx.2
  have key : ∀ k (_ : s ⟶ CechIndex.singleton k)
      (h : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
        cechIntersection U (CechIndex.singleton j) ⊆ cechIntersection U (CechIndex.singleton k)),
      fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        coconeLeg U c (CechIndex.singleton k) =
      fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion hs)) ≫
        coconeLeg U c s := fun k f h ↦ by
    rw [← map_inclusion_comp_coconeLeg U c f, ← Functor.map_comp_assoc, ← TopCat.ofHom_comp]
    rfl
  refine (key i (homOfLE (CechIndex.le_iff.2 ?_)) _).trans
    (key j (homOfLE (CechIndex.le_iff.2 ?_)) _).symm <;>
    rw [CechIndex.coe_singleton, Finset.singleton_subset_iff]
  exacts [Finset.mem_insert_self i {j}, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)]
private theorem cechExtension (hU : IsOpenCover U) (c : Cocone (cechDiagram U)) :
    ∃! G : fundamentalGroupoidFunctor.obj X ⟶ c.pt,
      ∀ i, fundamentalGroupoidFunctor.map (TopCat.ofHom
        (ContinuousMap.subtypeVal (cechIntersection U (CechIndex.singleton i) : Set X))) ≫ G =
        coconeLeg U c (CechIndex.singleton i) :=
  existsUnique_extension (exists_cechIntersection_singleton_mem_nhds hU)
    (fun i ↦ coconeLeg U c (CechIndex.singleton i)) (coconeLeg_singleton_compat c)

def isColimitCechCocone (hU : IsOpenCover U) : IsColimit (cechCocone U) where
  desc c := (cechExtension hU c).choose
  fac c s := by
    obtain ⟨i, hi⟩ := (OrderDual.ofDual s).2
    let f : s ⟶ CechIndex.singleton i := homOfLE (CechIndex.le_iff.2
      (by rw [CechIndex.coe_singleton]; exact Finset.singleton_subset_iff.2 hi))
    let e := cechExtension hU c
    let G := e.choose
    have hG : fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.subtypeVal
        (cechIntersection U (CechIndex.singleton i) : Set X))) ≫ G =
        coconeLeg U c (CechIndex.singleton i) := (e.choose_spec).1 i
    have key := map_inclusion_comp_coconeLeg U c f
    rw [← hG, ← Category.assoc, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.subtypeVal_comp_inclusion, map_subtypeVal_eq_cechCocone_ι_app] at key
    exact (cancel_epi _).1 ((Category.assoc _ _ _).symm.trans key)
  uniq c m hm := by
    let e := cechExtension hU c
    change m = e.choose
    apply (e.choose_spec).2 m
    intro i
    rw [map_subtypeVal_eq_cechCocone_ι_app]
    exact (Category.assoc _ _ _).trans (congrArg _ (hm _))

end TauCeti.FundamentalGroupoid
end
