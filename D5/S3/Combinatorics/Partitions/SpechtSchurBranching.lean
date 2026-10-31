/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurBranching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurBranching
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
import D5.S3.Combinatorics.Partitions.SpechtSchurTableaux

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace YoungDiagram
open _root_.YoungDiagram

variable {μ ν : _root_.YoungDiagram}

def InterlacedBy (μ ν : _root_.YoungDiagram) : Prop :=
  ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i

@[simp]
theorem interlacedBy_iff :
    InterlacedBy μ ν ↔ ∀ i, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i :=
  Iff.rfl

theorem InterlacedBy.rowLen_succ_le (h : InterlacedBy μ ν) (i : ℕ) :
    μ.rowLen (i + 1) ≤ ν.rowLen i :=
  (h i).1

theorem InterlacedBy.rowLen_le (h : InterlacedBy μ ν) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i :=
  (h i).2

theorem InterlacedBy.le (h : InterlacedBy μ ν) : ν ≤ μ :=
  le_of_forall_rowLen_le h.rowLen_le

theorem InterlacedBy.mem_of_lt (h : InterlacedBy μ ν) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hc : ((i₂, j) : ℕ × ℕ) ∈ μ) : ((i₁, j) : ℕ × ℕ) ∈ ν :=
  _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le
      ((μ.rowLen_anti (i₁ + 1) i₂ hi).trans (h.rowLen_succ_le i₁)))

noncomputable def interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    Finset _root_.YoungDiagram :=
  Set.Finite.toFinset (s := {ν : _root_.YoungDiagram | InterlacedBy μ ν ∧ ν.colLen 0 ≤ n})
    ((finite_Iic μ).subset fun _ h => Set.mem_Iic.mpr h.1.le)

@[simp]
theorem mem_interlacingShapes {n : ℕ} :
    ν ∈ interlacingShapes n μ ↔ InterlacedBy μ ν ∧ ν.colLen 0 ≤ n :=
  Set.Finite.mem_toFinset _

theorem sum_interlacingShapes_eq_sum_piFinset {M : Type*} [AddCommMonoid M] {n : ℕ}
    (hμ : μ.colLen 0 ≤ n + 1) (f : (Fin n → ℕ) → M) :
    ∑ ν ∈ interlacingShapes n μ, f (fun j => ν.rowLen j) =
      ∑ r ∈ Fintype.piFinset fun j : Fin n => Finset.Icc (μ.rowLen ((j : ℕ) + 1)) (μ.rowLen j),
        f r := by
  refine Finset.sum_bij (fun ν _ j => ν.rowLen j) (fun ν hν => ?_) (fun ν₁ hν₁ ν₂ hν₂ h => ?_)
    (fun r hr => ?_) fun _ _ => rfl
  · obtain ⟨hint, -⟩ := mem_interlacingShapes.mp hν
    exact Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr (interlacedBy_iff.mp hint j)
  · refine rowLen_injective (funext fun i => ?_)
    rcases lt_or_ge i n with hi | hi
    · exact congrFun h ⟨i, hi⟩
    · rw [rowLen_eq_zero_of_colLen_le ((mem_interlacingShapes.mp hν₁).2.trans hi),
        rowLen_eq_zero_of_colLen_le ((mem_interlacingShapes.mp hν₂).2.trans hi)]
  · have hr' : ∀ j : Fin n, μ.rowLen ((j : ℕ) + 1) ≤ r j ∧ r j ≤ μ.rowLen j := fun j =>
      Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hr j)
    have hanti : Antitone r := fun j k hjk => by
      rcases hjk.eq_or_lt with rfl | hlt
      · exact le_rfl
      · exact ((hr' k).2.trans (μ.rowLen_anti _ _ (Nat.succ_le_of_lt hlt))).trans (hr' j).1
    refine ⟨ofRowLensFin r hanti, mem_interlacingShapes.mpr
      ⟨interlacedBy_iff.mpr fun i => ?_, colLen_zero_ofRowLensFin_le r hanti⟩,
      funext fun j => rowLen_ofRowLensFin r hanti j⟩
    rcases lt_or_ge i n with hi | hi
    · have h := rowLen_ofRowLensFin r hanti ⟨i, hi⟩
      rw [Fin.val_mk] at h
      rw [h]
      exact hr' ⟨i, hi⟩
    · rw [rowLen_ofRowLensFin_eq_zero_of_le r hanti hi,
        rowLen_eq_zero_of_colLen_le (hμ.trans (by omega))]
      exact ⟨le_rfl, Nat.zero_le _⟩

end YoungDiagram

namespace TauCeti

theorem forall_betaNumber_le_iff_interlacedBy {N : ℕ} {μ ν : YoungDiagram}
    (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) :
    (∀ i j : Fin N, ν.betaNumber N j ≤ μ.betaNumber N i ↔ i ≤ j) ↔
      μ.InterlacedBy ν := by
  simp only [YoungDiagram.betaNumber_def, YoungDiagram.interlacedBy_iff]
  constructor
  · intro h i
    have h' : ∀ a b : ℕ, a < N → b < N →
        (ν.rowLen b + (N - 1 - b) ≤ μ.rowLen a + (N - 1 - a) ↔ a ≤ b) := by
      intro a b ha hb
      simpa [Fin.le_def] using h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨?_, ?_⟩
    · by_cases hi : i + 1 < N
      · have hlt := ((h' (i + 1) i hi (by omega)).not).mpr (by omega)
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans (by omega))]
        exact Nat.zero_le _
    · by_cases hi : i < N
      · have := (h' i i hi hi).mpr le_rfl
        omega
      · rw [YoungDiagram.rowLen_eq_zero_of_colLen_le (hν.trans (by omega))]
        exact Nat.zero_le _
  · intro h i j
    rw [Fin.le_def]
    have hiN : (i : ℕ) < N := i.isLt
    have hjN : (j : ℕ) < N := j.isLt
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · by_contra hij
      have h1 : μ.rowLen i ≤ μ.rowLen ((j : ℕ) + 1) := μ.rowLen_anti _ _ (by omega)
      have h2 : μ.rowLen ((j : ℕ) + 1) ≤ ν.rowLen j := (h j).1
      omega
    · have h1 : ν.rowLen j ≤ μ.rowLen j := (h j).2
      have h2 : μ.rowLen j ≤ μ.rowLen i := μ.rowLen_anti _ _ hle
      omega

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

def restrictShape (T : BoundedSSYT (n + 1) μ) : _root_.YoungDiagram where
  cells := μ.cells.filter fun c => T.1 c.1 c.2 < n
  isLowerSet := by
    rintro c d hdc hc
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hc ⊢
    exact ⟨μ.isLowerSet hdc hc.1,
      lt_of_le_of_lt (SemistandardYoungTableau.entry_le_of_le T.1 hdc.1 hdc.2 hc.1) hc.2⟩

@[simp]
theorem mem_restrictShape {T : BoundedSSYT (n + 1) μ} {i j : ℕ} :
    ((i, j) : ℕ × ℕ) ∈ restrictShape T ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n :=
  Finset.mem_filter

theorem mem_iff_of_restrictShape_eq {T : BoundedSSYT (n + 1) μ} (hν : restrictShape T = ν)
    {i j : ℕ} : ((i, j) : ℕ × ℕ) ∈ ν ↔ ((i, j) : ℕ × ℕ) ∈ μ ∧ T.1 i j < n := by
  subst hν; exact mem_restrictShape

theorem restrictShape_le (T : BoundedSSYT (n + 1) μ) : restrictShape T ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact (mem_restrictShape.mp hc).1

theorem interlacedBy_restrictShape (T : BoundedSSYT (n + 1) μ) :
    YoungDiagram.InterlacedBy μ (restrictShape T) :=
  fun i => ⟨YoungDiagram.le_rowLen_of_forall_mem fun j hj => by
      have hc : ((i + 1, j) : ℕ × ℕ) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj
      have hlt : T.1 i j < T.1 (i + 1) j := T.1.col_strict (Nat.lt_succ_self i) hc
      have hbound : T.1 (i + 1) j < n + 1 := entry_lt T hc
      exact mem_restrictShape.mpr ⟨μ.up_left_mem (Nat.le_succ i) le_rfl hc, by omega⟩,
    YoungDiagram.rowLen_le_of_le (restrictShape_le T) i⟩

theorem colLen_zero_restrictShape_le (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ restrictShape T :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  obtain ⟨hμ, hlt⟩ := mem_restrictShape.mp hmem
  exact absurd (SemistandardYoungTableau.le_entry T.1 hμ) (by omega)

theorem restrictShape_mem_interlacingShapes (T : BoundedSSYT (n + 1) μ) :
    restrictShape T ∈ YoungDiagram.interlacingShapes n μ :=
  YoungDiagram.mem_interlacingShapes.mpr
    ⟨interlacedBy_restrictShape T, colLen_zero_restrictShape_le T⟩

private def restrictTableau (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) : _root_.SemistandardYoungTableau ν where
  entry := fun i j => if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.row_weak hj ((mem_iff_of_restrictShape_eq hν).mp hc).1
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := ν.up_left_mem hi.le le_rfl hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact T.1.col_strict hi ((mem_iff_of_restrictShape_eq hν).mp hc).1
  zeros' := fun {_ _} hc => ite_eq_right hc

private theorem restrictTableau_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    restrictTableau T ν hν i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  (rfl)

def restrict (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram) (hν : restrictShape T = ν) :
    BoundedSSYT n ν :=
  ⟨restrictTableau T ν hν, fun i j hc => by
    rw [restrictTableau_apply, ite_eq_left hc]
    exact ((mem_iff_of_restrictShape_eq hν).mp hc).2⟩

@[simp]
theorem restrict_apply (T : BoundedSSYT (n + 1) μ) (ν : _root_.YoungDiagram)
    (hν : restrictShape T = ν) (i j : ℕ) :
    (restrict T ν hν).1 i j = if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else 0 :=
  restrictTableau_apply T ν hν i j

@[simp]
theorem content_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) {i : ℕ}
    (hi : i < n) :
    SemistandardYoungTableau.content (restrict T ν hν).1 i
      = SemistandardYoungTableau.content T.1 i := by
  rw [SemistandardYoungTableau.content_apply, SemistandardYoungTableau.content_apply]
  have hcells : (ν.cells.filter fun c => (restrict T ν hν).1 c.1 c.2 = i)
      = μ.cells.filter fun c => T.1 c.1 c.2 = i := by
    ext c
    obtain ⟨a, b⟩ := c
    simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells, restrict_apply]
    grind [mem_iff_of_restrictShape_eq]
  rw [hcells]

private def extendTableau (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    _root_.SemistandardYoungTableau μ where
  entry := fun i j =>
    if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0
  row_weak' := fun {i j₁ j₂} hj hc => by
    by_cases hc₂ : ((i, j₂) : ℕ × ℕ) ∈ ν
    · have hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν := ν.up_left_mem le_rfl hj.le hc₂
      rw [ite_eq_left hc₁, ite_eq_left hc₂]
      exact T.1.row_weak hj hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      by_cases hc₁ : ((i, j₁) : ℕ × ℕ) ∈ ν
      · rw [ite_eq_left hc₁]
        exact (entry_lt T hc₁).le
      · rw [ite_eq_right hc₁, ite_eq_left (μ.up_left_mem le_rfl hj.le hc)]
  col_strict' := fun {i₁ i₂ j} hi hc => by
    have hc₁ : ((i₁, j) : ℕ × ℕ) ∈ ν := h.mem_of_lt hi hc
    rw [ite_eq_left hc₁]
    by_cases hc₂ : ((i₂, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₂]
      exact T.1.col_strict hi hc₂
    · rw [ite_eq_right hc₂, ite_eq_left hc]
      exact entry_lt T hc₁
  zeros' := fun {_ _} hc => by
    rw [ite_eq_right fun hν => hc (h.le hν), ite_eq_right hc]

private theorem extendTableau_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν)
    (i j : ℕ) :
    extendTableau h T i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  (rfl)

def extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) : BoundedSSYT (n + 1) μ :=
  ⟨extendTableau h T, fun i j hc => by
    rw [extendTableau_apply]
    by_cases hc₁ : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hc₁]
      exact Nat.lt_succ_of_lt (entry_lt T hc₁)
    · rw [ite_eq_right hc₁, ite_eq_left hc]
      exact Nat.lt_succ_self n⟩

@[simp]
theorem extend_apply (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) (i j : ℕ) :
    (extend h T).1 i j =
      if ((i, j) : ℕ × ℕ) ∈ ν then T.1 i j else if ((i, j) : ℕ × ℕ) ∈ μ then n else 0 :=
  extendTableau_apply h T i j

@[simp]
theorem restrictShape_extend (h : YoungDiagram.InterlacedBy μ ν) (T : BoundedSSYT n ν) :
    restrictShape (extend h T) = ν := by
  ext c
  obtain ⟨i, j⟩ := c
  simp only [_root_.YoungDiagram.mem_cells, mem_restrictShape, extend_apply]
  grind [IsConcreteLE.le_iff.mp h.le, entry_lt]

def fiberEquiv (h : YoungDiagram.InterlacedBy μ ν) :
    {T : BoundedSSYT (n + 1) μ // restrictShape T = ν} ≃ BoundedSSYT n ν where
  toFun T := restrict T.1 ν T.2
  invFun T := ⟨extend h T, restrictShape_extend h T⟩
  left_inv := by
    rintro ⟨T, hT⟩
    refine Subtype.ext (Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_))
    rw [extend_apply, restrict_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      by_cases hμ : ((i, j) : ℕ × ℕ) ∈ μ
      · rw [ite_eq_left hμ]
        have hnot : ¬ T.1 i j < n := fun hlt => hν ((mem_iff_of_restrictShape_eq hT).mpr ⟨hμ, hlt⟩)
        have hlt := entry_lt T hμ
        have heq : T.1 i j = n := by omega
        exact heq.symm
      · rw [ite_eq_right hμ]
        exact (T.1.zeros hμ).symm
  right_inv := by
    intro T
    refine Subtype.ext (_root_.SemistandardYoungTableau.ext fun i j => ?_)
    rw [restrict_apply, extend_apply]
    by_cases hν : ((i, j) : ℕ × ℕ) ∈ ν
    · rw [ite_eq_left hν, ite_eq_left hν]
    · rw [ite_eq_right hν]
      exact (T.1.zeros hν).symm

theorem sum_eq_sum_interlacingShapes {M : Type*} [AddCommMonoid M] (n : ℕ)
    (μ : _root_.YoungDiagram) (f : ∀ ν : _root_.YoungDiagram, BoundedSSYT n ν → M) :
    ∑ T : BoundedSSYT (n + 1) μ, f (restrictShape T) (restrict T (restrictShape T) rfl)
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν, f ν T := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun T _ => restrictShape_mem_interlacingShapes T)
    (fun T => f (restrictShape T) (restrict T (restrictShape T) rfl))]
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [Finset.sum_subtype (p := fun T : BoundedSSYT (n + 1) μ => restrictShape T = ν) _
    (fun T => by simp)]
  refine Fintype.sum_equiv (fiberEquiv (YoungDiagram.mem_interlacingShapes.mp hν).1) _ _
    fun T => ?_
  obtain ⟨T, hT⟩ := T
  subst hT
  rfl

end BoundedSSYT

end TauCeti

namespace TauCeti

open MvPolynomial

variable {R : Type*} [CommSemiring R]

namespace BoundedSSYT

variable {n : ℕ} {μ ν : _root_.YoungDiagram}

theorem weight_restrict (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) (i : Fin n) :
    weight (restrict T ν hν) i = weight T i.castSucc := by
  rw [weight_apply, weight_apply, Fin.val_castSucc, content_restrict T hν i.isLt]

theorem card_add_weight_last (T : BoundedSSYT (n + 1) μ) :
    (restrictShape T).card + weight T (Fin.last n) = μ.card := by
  have hsum : ∑ i, weight T i = μ.card := sum_weight T
  rw [Fin.sum_univ_castSucc] at hsum
  rw [← hsum, ← sum_weight (restrict T _ rfl)]
  exact congrArg (· + weight T (Fin.last n))
    (Finset.sum_congr rfl fun i _ => weight_restrict T rfl i)

theorem weight_eq_mapDomain_add_single (T : BoundedSSYT (n + 1) μ) (hν : restrictShape T = ν) :
    weight T = Finsupp.mapDomain Fin.castSucc (weight (restrict T ν hν))
      + Finsupp.single (Fin.last n) (weight T (Fin.last n)) := by
  ext i
  induction i using Fin.lastCases with
  | last =>
    rw [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.mapDomain_of_notMem_range _ _
        (by rintro ⟨j, hj⟩; exact absurd hj (Fin.castSucc_lt_last j).ne),
      zero_add]
  | cast j =>
    have hne : Fin.castSucc j ≠ Fin.last n := (Fin.castSucc_lt_last j).ne
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n),
      Finsupp.single_eq_of_ne hne, add_zero, weight_restrict T hν j]

theorem card_weight_eq_sum_interlacingShapes (μ : YoungDiagram) (c : Fin (n + 1) → ℕ) :
    Nat.card {T : BoundedSSYT (n + 1) μ // ⇑(weight T) = c} =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ with ν.card + c (Fin.last n) = μ.card,
        Nat.card {T : BoundedSSYT n ν // ⇑(weight T) = fun i => c i.castSucc} := by
  classical
  have key (T : BoundedSSYT (n + 1) μ) : ⇑(weight T) = c ↔
      (⇑(weight (restrict T (restrictShape T) rfl)) = fun i => c i.castSucc) ∧
        (restrictShape T).card + c (Fin.last n) = μ.card := by
    have hlast := card_add_weight_last T
    simp only [funext_iff, Fin.forall_fin_succ', weight_restrict]
    exact and_congr_right fun _ => by omega
  calc Nat.card {T : BoundedSSYT (n + 1) μ // ⇑(weight T) = c}
      = ∑ T : BoundedSSYT (n + 1) μ,
          if (⇑(weight (restrict T (restrictShape T) rfl)) = fun i => c i.castSucc) ∧
            (restrictShape T).card + c (Fin.last n) = μ.card then 1 else 0 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
        exact Finset.sum_congr rfl fun T _ => if_congr (key T) rfl rfl
    _ = ∑ ν ∈ YoungDiagram.interlacingShapes n μ, ∑ T : BoundedSSYT n ν,
          if (⇑(weight T) = fun i => c i.castSucc) ∧ ν.card + c (Fin.last n) = μ.card
          then 1 else 0 :=
        sum_eq_sum_interlacingShapes n μ fun ν T =>
          if (⇑(weight T) = fun i => c i.castSucc) ∧ ν.card + c (Fin.last n) = μ.card then 1 else 0
    _ = _ := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun ν _ => ?_
        by_cases h : ν.card + c (Fin.last n) = μ.card
        · simp only [h, and_true, ↓reduceIte]
          rw [← Finset.card_filter, ← Fintype.card_subtype, Nat.card_eq_fintype_card]
        · simp [h]

end BoundedSSYT

theorem diagramSchurPoly_eq_sum_interlacingShapes (n : ℕ) (μ : _root_.YoungDiagram) :
    diagramSchurPoly (n + 1) R μ
      = ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
          X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (diagramSchurPoly n R ν) := by
  have key : ∀ T : BoundedSSYT (n + 1) μ,
      (monomial (BoundedSSYT.weight T) (1 : R))
        = X (Fin.last n) ^ (μ.card - (BoundedSSYT.restrictShape T).card) *
            rename Fin.castSucc
              (monomial (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) (1 : R)) := by
    intro T
    have hcard := BoundedSSYT.card_add_weight_last T
    have hexp : μ.card - (BoundedSSYT.restrictShape T).card
        = BoundedSSYT.weight T (Fin.last n) := by omega
    have hw : BoundedSSYT.weight T
        = Finsupp.single (Fin.last n) (BoundedSSYT.weight T (Fin.last n))
          + Finsupp.mapDomain Fin.castSucc
              (BoundedSSYT.weight (BoundedSSYT.restrict T _ rfl)) :=
      (BoundedSSYT.weight_eq_mapDomain_add_single T rfl).trans (add_comm _ _)
    rw [rename_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul, hexp]
    exact congrArg (monomial · (1 : R)) hw
  rw [diagramSchurPoly_eq_sum, Finset.sum_congr rfl fun T _ => key T,
    BoundedSSYT.sum_eq_sum_interlacingShapes n μ fun ν S =>
      X (Fin.last n) ^ (μ.card - ν.card) * rename Fin.castSucc (monomial (BoundedSSYT.weight S) 1)]
  exact Finset.sum_congr rfl fun ν _ => by
    rw [← Finset.mul_sum, ← map_sum, diagramSchurPoly_eq_sum]

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
