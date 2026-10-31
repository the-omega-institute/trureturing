/- GID: D5/S3/Combinatorics/Partitions/SpechtKostka
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtKostka
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected tableau and Schur suppliers for the ordinary Specht Frobenius comparison. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected declarations from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Namespaces and root references adapted to the existing D5 source chain.
License, selection, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtTableauGeometry
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Data.Finsupp.Multiset
import Mathlib.SetTheory.Cardinal.Finite

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace SemistandardYoungTableau
open _root_.SemistandardYoungTableau

variable {μ : YoungDiagram}

noncomputable def content (T : _root_.SemistandardYoungTableau μ) : ℕ →₀ ℕ :=
  (μ.cells.val.map fun c => T c.1 c.2).toFinsupp

theorem content_apply (T : _root_.SemistandardYoungTableau μ) (i : ℕ) :
    content T i = (μ.cells.filter fun c => T c.1 c.2 = i).card := by
  rw [content, Multiset.toFinsupp_apply, Multiset.count_map]
  simp [Finset.card, Finset.filter_val, eq_comm]

@[simp]
theorem support_content (T : _root_.SemistandardYoungTableau μ) :
    (content T).support = μ.cells.image fun c => T c.1 c.2 := by
  rw [content, Multiset.toFinsupp_support, Multiset.toFinset_map, Finset.val_toFinset]

theorem le_entry (T : _root_.SemistandardYoungTableau μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    i ≤ T i j := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hm : (m, j) ∈ μ := μ.up_left_mem (Nat.le_succ m) le_rfl h
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hm) (T.col_strict (Nat.lt_succ_self m) h))

theorem filter_entry_lt_subset_filter_fst_lt (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    (μ.cells.filter fun c => T c.1 c.2 < k) ⊆ μ.cells.filter fun c => c.1 < k := by
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_le_of_lt (le_entry T (by simpa using hc.1)) hc.2⟩

theorem sum_content_eq_card_filter (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i = (μ.cells.filter fun c => T c.1 c.2 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => T c.1 c.2 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => T c.1 c.2 < k).filter fun c => T c.1 c.2 = i).card := by
      refine Finset.card_eq_sum_card_fiberwise fun c hc => ?_
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, content T i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i < k := Finset.mem_range.mp hi
      rw [content_apply]
      refine congrArg Finset.card (Finset.ext fun c => ?_)
      simp only [Finset.mem_filter, and_assoc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2 ▸ hik, h.2⟩⟩

theorem sum_content_eq_card {T : _root_.SemistandardYoungTableau μ} {N : ℕ}
    (hN : ∀ c ∈ μ.cells, T c.1 c.2 < N) :
    ∑ i ∈ Finset.range N, content T i = μ.card := by
  rw [sum_content_eq_card_filter, Finset.filter_true_of_mem hN]

theorem sum_content_le_sum_take_rowLens (T : _root_.SemistandardYoungTableau μ) (k : ℕ) :
    ∑ i ∈ Finset.range k, content T i ≤ (μ.rowLens.take k).sum := by
  rw [sum_content_eq_card_filter, YoungDiagram.sum_take_rowLens_eq_card_filter_fst]
  exact Finset.card_le_card (filter_entry_lt_subset_filter_fst_lt T k)

@[simp]
theorem content_highestWeight (μ : YoungDiagram) :
    ⇑(content (_root_.SemistandardYoungTableau.highestWeight μ)) = μ.rowLen := by
  funext i
  rw [content_apply, μ.rowLen_eq_card]
  refine congrArg Finset.card (Finset.ext fun c => ?_)
  simp only [_root_.YoungDiagram.mem_row_iff,
    _root_.SemistandardYoungTableau.highestWeight_apply]
  aesop

theorem eq_highestWeight_of_content_eq_rowLen {T : _root_.SemistandardYoungTableau μ}
    (h : ⇑(content T) = μ.rowLen) : T = _root_.SemistandardYoungTableau.highestWeight μ := by
  have key : ∀ i j : ℕ, (i, j) ∈ μ → T i j = i := by
    intro i j hij
    have hcards : (μ.cells.filter fun c => T c.1 c.2 < i + 1).card =
        (μ.cells.filter fun c => c.1 < i + 1).card := by
      rw [← sum_content_eq_card_filter, ← YoungDiagram.sum_range_rowLen_eq_card_filter_fst]
      exact Finset.sum_congr rfl fun k _ => congrFun h k
    have hsets := Finset.eq_of_subset_of_card_le
      (filter_entry_lt_subset_filter_fst_lt T (i + 1)) hcards.ge
    have hmem : ((i, j) : ℕ × ℕ) ∈ μ.cells.filter fun c => T c.1 c.2 < i + 1 := by
      rw [hsets, Finset.mem_filter]
      exact ⟨hij, Nat.lt_succ_self i⟩
    exact le_antisymm (Nat.lt_succ_iff.mp (Finset.mem_filter.mp hmem).2) (le_entry T hij)
  ext i j
  by_cases hij : (i, j) ∈ μ
  · rw [key i j hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_left hij]
  · rw [T.zeros hij, _root_.SemistandardYoungTableau.highestWeight_apply, ite_eq_right hij]

instance finite_content_eq (μ : YoungDiagram) (w : ℕ → ℕ) :
    Finite {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w} := by
  by_cases hne : Nonempty {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}
  swap
  · rw [not_nonempty_iff] at hne
    infer_instance
  obtain ⟨T₀, hT₀⟩ := hne.some
  have hmem : ∀ T : _root_.SemistandardYoungTableau μ, ⇑(content T) = w →
      ∀ c ∈ μ.cells, T c.1 c.2 ∈ μ.cells.image fun d => T₀ d.1 d.2 := by
    intro T hT c hc
    rw [← support_content T₀, DFunLike.coe_injective (hT₀.trans hT.symm), support_content T]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  refine Finite.of_injective
    (fun (T : {T : _root_.SemistandardYoungTableau μ // ⇑(content T) = w}) (c : ↥μ.cells) =>
      (⟨T.1 (c : ℕ × ℕ).1 (c : ℕ × ℕ).2, hmem T.1 T.2 _ c.2⟩ :
        ↥(μ.cells.image fun d => T₀ d.1 d.2))) fun T T' hTT' => ?_
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
  by_cases hij : (i, j) ∈ μ
  · exact congrArg Subtype.val (congrFun hTT' ⟨(i, j), hij⟩)
  · rw [T.1.zeros hij, T'.1.zeros hij]

end SemistandardYoungTableau

namespace TauCeti

open _root_.YoungDiagram (ofPartition)

abbrev BoundedSSYT (n : ℕ) (μ : YoungDiagram) : Type :=
  {T : _root_.SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n}

namespace BoundedSSYT

variable {n : ℕ} {μ : YoungDiagram}

theorem entry_lt (T : BoundedSSYT n μ) {i c : ℕ} (h : (i, c) ∈ μ) : T.1 i c < n :=
  T.2 i c h

theorem isEmpty_of_lt_colLen (h : n < μ.colLen 0) : IsEmpty (BoundedSSYT n μ) := by
  refine ⟨fun T => absurd (entry_lt T (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)) (not_lt.mpr ?_)⟩
  exact SemistandardYoungTableau.le_entry T.1 (_root_.YoungDiagram.mem_iff_lt_colLen.mpr h)

instance (n : ℕ) : Unique (BoundedSSYT n (⊥ : YoungDiagram)) where
  default := ⟨_root_.SemistandardYoungTableau.highestWeight ⊥, fun _ _ hic => absurd hic (by simp)⟩
  uniq T := Subtype.ext <| _root_.SemistandardYoungTableau.ext fun _ _ => by
    rw [T.1.zeros (by simp), _root_.SemistandardYoungTableau.highestWeight_apply,
      ite_eq_right (by simp)]

end BoundedSSYT

instance finite_boundedSSYT (n : ℕ) (μ : YoungDiagram) : Finite (BoundedSSYT n μ) := by
  refine Finite.of_injective (β := μ.cells → Fin n)
    (fun T x => ⟨T.1 x.1.1 x.1.2, T.2 _ _ ((_root_.YoungDiagram.mem_cells _).mp x.2)⟩) ?_
  rintro ⟨T, hT⟩ ⟨T', hT'⟩ h
  refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i c => ?_)
  by_cases hc : (i, c) ∈ μ
  · exact congrArg Fin.val (congrFun h ⟨(i, c), (_root_.YoungDiagram.mem_cells _).mpr hc⟩)
  · rw [T.zeros hc, T'.zeros hc]

noncomputable instance (n : ℕ) (μ : YoungDiagram) : Fintype (BoundedSSYT n μ) := .ofFinite _

noncomputable def diagramKostkaNumber (μ : YoungDiagram) (w : ℕ → ℕ) : ℕ :=
  Nat.card {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w}

theorem diagramKostkaNumber_def (μ : YoungDiagram) (w : ℕ → ℕ) :
    diagramKostkaNumber μ w =
      Nat.card
        {T : _root_.SemistandardYoungTableau μ // ⇑(SemistandardYoungTableau.content T) = w} :=
  (rfl)

theorem diagramKostkaNumber_ne_zero_iff {μ : YoungDiagram} {w : ℕ → ℕ} :
    diagramKostkaNumber μ w ≠ 0 ↔
      ∃ T : _root_.SemistandardYoungTableau μ, ⇑(SemistandardYoungTableau.content T) = w := by
  rw [diagramKostkaNumber_def, Nat.card_ne_zero]
  exact ⟨fun h => h.1.elim fun T => ⟨T.1, T.2⟩, fun ⟨T, hT⟩ => ⟨⟨⟨T, hT⟩⟩, inferInstance⟩⟩

@[simp]
theorem diagramKostkaNumber_rowLen (μ : YoungDiagram) : diagramKostkaNumber μ μ.rowLen = 1 := by
  rw [diagramKostkaNumber_def, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun T T' => Subtype.ext ?_⟩,
    ⟨⟨_root_.SemistandardYoungTableau.highestWeight μ,
      SemistandardYoungTableau.content_highestWeight μ⟩⟩⟩
  rw [SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T.2,
    SemistandardYoungTableau.eq_highestWeight_of_content_eq_rowLen T'.2]

theorem sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero {μ : YoungDiagram} {w : ℕ → ℕ}
    (h : diagramKostkaNumber μ w ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, w i ≤ (μ.rowLens.take k).sum := by
  obtain ⟨T, hT⟩ := diagramKostkaNumber_ne_zero_iff.mp h
  calc
    ∑ i ∈ Finset.range k, w i = ∑ i ∈ Finset.range k, SemistandardYoungTableau.content T i :=
      Finset.sum_congr rfl fun i _ => (congrFun hT i).symm
    _ ≤ (μ.rowLens.take k).sum := SemistandardYoungTableau.sum_content_le_sum_take_rowLens T k

noncomputable def kostkaNumber {n : ℕ} (μ ν : n.Partition) : ℕ :=
  diagramKostkaNumber (ofPartition μ) (ofPartition ν).rowLen

theorem kostkaNumber_def {n : ℕ} (μ ν : n.Partition) :
    kostkaNumber μ ν = diagramKostkaNumber (ofPartition μ) (ofPartition ν).rowLen := (rfl)

@[simp]
theorem kostkaNumber_self {n : ℕ} (μ : n.Partition) : kostkaNumber μ μ = 1 :=
  (kostkaNumber_def μ μ).trans (diagramKostkaNumber_rowLen _)

theorem dominates_of_kostkaNumber_ne_zero {n : ℕ} {μ ν : n.Partition}
    (h : kostkaNumber μ ν ≠ 0) : Dominates μ ν := by
  refine dominates_iff.mpr fun k => ?_
  rw [kostkaNumber_def] at h
  have hk := sum_le_sum_take_rowLens_of_diagramKostkaNumber_ne_zero h k
  rwa [YoungDiagram.sum_range_rowLen_eq_card_filter_fst,
    ← YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    _root_.YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    _root_.YoungDiagram.rowLens_ofPartition_eq_sort_parts] at hk

theorem kostkaNumber_eq_zero_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (h : ¬ Dominates μ ν) : kostkaNumber μ ν = 0 :=
  not_not.mp fun h' => h (dominates_of_kostkaNumber_ne_zero h')

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
