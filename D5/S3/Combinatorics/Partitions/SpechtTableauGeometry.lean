/- GID: D5/S3/Combinatorics/Partitions/SpechtTableauGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtTableauGeometry
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
import D5.S3.Combinatorics.Partitions.SpechtYoungPolynomialGram
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Sort

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace YoungDiagram
open _root_.YoungDiagram

theorem rowLen_injective : Function.Injective _root_.YoungDiagram.rowLen := by
  intro μ ν h
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, congrFun h i]

theorem card_eq_sum_range_rowLen (μ : _root_.YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := by
  rw [sum_range_rowLen_eq_card_filter_fst]
  refine (congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)).symm
  exact lt_of_lt_of_le ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
    (μ.colLen_anti 0 c.snd c.snd.zero_le)) hN

theorem card_filter_cells (μ : _root_.YoungDiagram) (p : ℕ × ℕ → Prop) [DecidablePred p] {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    (μ.cells.filter p).card
      = ∑ i ∈ Finset.range N, ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).card := by
  have hcells : μ.cells.filter p
      = (Finset.range N).biUnion fun i =>
          ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).image fun j => (i, j) := by
    ext c
    obtain ⟨i, j⟩ := c
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      _root_.YoungDiagram.mem_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, hp⟩
      refine ⟨i, lt_of_lt_of_le (lt_of_lt_of_le (_root_.YoungDiagram.mem_iff_lt_colLen.mp hij)
        (μ.colLen_anti 0 j j.zero_le)) hN, j, ⟨?_, hp⟩, rfl, rfl⟩
      exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij
    · rintro ⟨i', -, j', ⟨hj', hp⟩, rfl, rfl⟩
      exact ⟨_root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj', hp⟩
  rw [hcells, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  · intro y _ z _ hyz
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    rintro c ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact hyz (congrArg Prod.fst hj').symm

theorem rowLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i := by
  rcases Nat.eq_zero_or_pos (ν.rowLen i) with h0 | h0
  · omega
  · have hmem : ((i, ν.rowLen i - 1) : ℕ × ℕ) ∈ ν :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)
    omega

theorem le_of_forall_rowLen_le {μ ν : YoungDiagram} (h : ∀ i, ν.rowLen i ≤ μ.rowLen i) : ν ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h i))

theorem colLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (j : ℕ) : ν.colLen j ≤ μ.colLen j := by
  rw [← _root_.YoungDiagram.rowLen_transpose, ← _root_.YoungDiagram.rowLen_transpose]
  exact rowLen_le_of_le (_root_.YoungDiagram.transpose_mono h) j

theorem le_rowLen_of_forall_mem {ν : YoungDiagram} {i k : ℕ}
    (h : ∀ j < k, ((i, j) : ℕ × ℕ) ∈ ν) : k ≤ ν.rowLen i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h (k - 1) (by omega))
    omega

theorem finite_Iic (μ : YoungDiagram) : (Set.Iic μ).Finite := by
  have hinj : Set.InjOn _root_.YoungDiagram.cells (Set.Iic μ) :=
    fun _ _ _ _ h => _root_.YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (μ.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨ξ, hξ, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun c hc => Set.mem_Iic.mp hξ hc)

end YoungDiagram

namespace YoungDiagram
open _root_.YoungDiagram

@[simp]
theorem colLen_zero_ofPartition {n : ℕ} (ν : n.Partition) :
    (ofPartition ν).colLen 0 = ν.parts.card := by
  rw [← length_rowLens, rowLens_ofPartition_eq_sort_parts, Multiset.length_sort]

theorem ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) :=
  fun _ _ h => equivPartition.symm.injective (Subtype.ext h)

end YoungDiagram

namespace TauCeti

end TauCeti

namespace SemistandardYoungTableau
open _root_.SemistandardYoungTableau

variable {μ : YoungDiagram}

theorem entry_le_of_le (T : SemistandardYoungTableau μ) {i₁ i₂ j₁ j₂ : ℕ} (hi : i₁ ≤ i₂)
    (hj : j₁ ≤ j₂) (hc : ((i₂, j₂) : ℕ × ℕ) ∈ μ) : T i₁ j₁ ≤ T i₂ j₂ :=
  (T.row_weak_of_le hj (μ.up_left_mem hi le_rfl hc)).trans (T.col_weak hi hc)

end SemistandardYoungTableau

namespace YoungDiagram
open _root_.YoungDiagram

variable {n : ℕ}

def ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) : _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens (List.ofFn f) hf.sortedGE_ofFn

@[simp]
theorem rowLen_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (ofRowLensFin f hf).rowLen i = f i := by
  have h : (i : ℕ) < (List.ofFn f).length := by simp
  simpa [ofRowLensFin] using
    _root_.YoungDiagram.rowLen_ofRowLens (w := List.ofFn f) (hw := hf.sortedGE_ofFn) ⟨i, h⟩

@[simp]
theorem rowLen_ofRowLensFin_eq_zero_of_le (f : Fin n → ℕ) (hf : Antitone f) {i : ℕ} (hi : n ≤ i) :
    (ofRowLensFin f hf).rowLen i = 0 := by
  by_contra h
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  grind [ofRowLensFin, _root_.YoungDiagram.mem_ofRowLens, List.length_ofFn]

theorem colLen_zero_ofRowLensFin_le (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  grind [_root_.YoungDiagram.mem_iff_lt_rowLen, rowLen_ofRowLensFin_eq_zero_of_le]

@[simp]
theorem card_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).card = ∑ i, f i := by
  rw [card_eq_sum_range_rowLen _ (colLen_zero_ofRowLensFin_le f hf),
    ← Fin.sum_univ_eq_sum_range (fun i => (ofRowLensFin f hf).rowLen i) n]
  exact Finset.sum_congr rfl fun i _ => rowLen_ofRowLensFin f hf i

end YoungDiagram

open Equiv

variable {n : ℕ} {α : Type*}

theorem StrictAnti.add_sub_le_nat {η : Fin n → ℕ} (hη : StrictAnti η) {i j : Fin n}
    (hij : i ≤ j) : η j + ((j : ℕ) - (i : ℕ)) ≤ η i := by
  obtain ⟨j, hj⟩ := j
  simp only [Fin.le_def] at hij
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have := hη (Fin.mk_lt_mk.mpr k.lt_succ_self : (⟨k, by omega⟩ : Fin n) < ⟨k + 1, hj⟩)
    grind

theorem Function.Injective.exists_strictAnti_comp [LinearOrder α] {f : Fin n → α}
    (hf : Function.Injective f) : ∃ τ : Perm (Fin n), StrictAnti (f ∘ τ) := by
  have hmono : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  refine ⟨Fin.revPerm.trans (Tuple.sort f), fun i j hij => ?_⟩
  simpa using hmono (Fin.rev_lt_rev.mpr hij)

theorem StrictAnti.perm_eq [PartialOrder α] {f : Fin n → α} {τ₁ τ₂ : Perm (Fin n)}
    (h₁ : StrictAnti (f ∘ τ₁)) (h₂ : StrictAnti (f ∘ τ₂)) : τ₁ = τ₂ :=
  Equiv.ext <| congrFun <| ((τ₁.injective_comp f).mp h₁.injective).comp_left
    (Tuple.unique_antitone h₁.antitone h₂.antitone)

namespace YoungDiagram
open _root_.YoungDiagram

variable {μ : YoungDiagram} {r i j : ℕ}

def betaNumber (μ : YoungDiagram) (r i : ℕ) : ℕ := μ.rowLen i + (r - 1 - i)

theorem betaNumber_def (μ : YoungDiagram) (r i : ℕ) :
    μ.betaNumber r i = μ.rowLen i + (r - 1 - i) := (rfl)

theorem betaNumber_lt_betaNumber (μ : YoungDiagram) (hij : i < j) (hj : j < r) :
    μ.betaNumber r j < μ.betaNumber r i := by
  have := μ.rowLen_anti i j hij.le
  simp only [betaNumber_def]
  omega

grind_pattern betaNumber_lt_betaNumber => μ.betaNumber r i, μ.betaNumber r j

theorem eq_of_betaNumber_eq {ν : YoungDiagram} (hμ : μ.colLen 0 ≤ r) (hν : ν.colLen 0 ≤ r)
    (h : ∀ i < r, μ.betaNumber r i = ν.betaNumber r i) : μ = ν := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < r
  · have := h i hi
    rw [betaNumber_def, betaNumber_def] at this
    omega
  · rw [rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi)),
      rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]

theorem strictAnti_betaNumber (μ : YoungDiagram) (r : ℕ) :
    StrictAnti fun j : Fin r => μ.betaNumber r j :=
  fun _ j hij => μ.betaNumber_lt_betaNumber (Fin.lt_def.mp hij) j.isLt

theorem exists_eq_betaNumber_of_strictAnti {r : ℕ} {η : Fin r → ℕ} (hη : StrictAnti η) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ r ∧ ∀ j : Fin r, μ.betaNumber r j = η j := by
  have hshift : ∀ j : Fin r, r - 1 - (j : ℕ) ≤ η j := by
    intro j
    have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    set L : Fin r := ⟨r - 1, by omega⟩ with _hLdef
    have hLval : (L : ℕ) = r - 1 := rfl
    have hle : j ≤ L := Fin.le_def.mpr (by rw [hLval]; omega)
    have hgap := hη.add_sub_le_nat hle
    rw [hLval] at hgap
    omega
  have hanti : Antitone fun j : Fin r => η j - (r - 1 - (j : ℕ)) := by
    intro i j hij
    dsimp only
    have hgap := hη.add_sub_le_nat hij
    have hi := hshift i
    have hj := hshift j
    have _ : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hij
    have _ : (j : ℕ) < r := j.isLt
    omega
  refine ⟨ofRowLensFin _ hanti, colLen_zero_ofRowLensFin_le _ hanti, fun j => ?_⟩
  rw [betaNumber_def, rowLen_ofRowLensFin]
  have := hshift j
  omega

open Finset

theorem sum_betaNumber (μ : YoungDiagram) {r : ℕ} (hμ : μ.colLen 0 ≤ r) :
    ∑ j : Fin r, μ.betaNumber r j = μ.card + ∑ j : Fin r, (r - 1 - (j : ℕ)) := by
  simp only [betaNumber_def]
  rw [Finset.sum_add_distrib, card_eq_sum_range_rowLen μ hμ,
    Fin.sum_univ_eq_sum_range (fun i => μ.rowLen i) r]

end YoungDiagram

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
