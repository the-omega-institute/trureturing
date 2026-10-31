/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungDominance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungDominance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Column antisymmetrizers force dominance on genuine maps out of the Specht span. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations, namespaces, exact D5 supplier qualifications and
explicit normalization at missing source convenience interfaces. Immutable locators,
license, consumers and retirement against OUR Mathlib pin are recorded in
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
SOURCE ONLY: no native elaboration, axiom closure, proof-term liveness, admission,
validated Reg, emission, freeze, deposit, PR or CI is claimed. Unfinished audit:
https://github.com/the-omega-institute/trureturing/issues/24542.
Necessary Young-rule construction for the full ordinary HSW theorem; not standalone
firstfreeze content. Young/Kostka equality and both weighted ordinary sums remain open.
utility: none: general unbounded partitions and representation spaces, no enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtFixedTabloidPowerSum
import D5.S3.Combinatorics.Partitions.SpechtAbsoluteIrreducibility
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Lex

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace YoungDiagram
private theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_range_rowLen_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, μ.rowLen i = (μ.cells.filter fun c => c.1 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, μ.rowLen i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells,
        _root_.YoungDiagram.mem_row_iff]
      aesop

theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [_root_.YoungDiagram.rowLens, ← List.map_take, List.take_range, sum_list_range,
    ← sum_range_rowLen_eq_card_filter_fst]
  have hsub : Finset.range (min k (μ.colLen 0)) ⊆ Finset.range k := fun i hi =>
    Finset.mem_range.mpr (lt_min_iff.mp (Finset.mem_range.mp hi)).1
  refine Finset.sum_subset hsub fun i hi hi' => ?_
  exact rowLen_eq_zero_of_colLen_le
    (by simpa [lt_min_iff, Finset.mem_range.mp hi] using Finset.mem_range.not.mp hi')

theorem card_filter_fst_lt_filter_snd_eq (lam : YoungDiagram) (k j : ℕ) :
    (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j).card
      = min k (lam.colLen j) := by
  have himg : (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j)
      = (Finset.range (min k (lam.colLen j))).image fun i => (i, j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, lt_min_iff,
      _root_.YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, hk⟩, hj⟩
      refine ⟨c.1, ⟨hk, ?_⟩, ?_⟩
      · exact _root_.YoungDiagram.mem_iff_lt_colLen.mp (hj ▸ hc)
      · rw [← hj]
    · rintro ⟨i, ⟨hik, hicol⟩, rfl⟩
      exact ⟨⟨_root_.YoungDiagram.mem_iff_lt_colLen.mpr hicol, hik⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h, Finset.card_range]

theorem card_filter_le_sum_take_rowLens {α : Type*} [Fintype α] (lam : YoungDiagram)
    (r : α → ℕ) (f : α → ℕ × ℕ) (hmem : ∀ a, f a ∈ lam.cells) (hinj : Function.Injective f)
    (hcol : ∀ a b, r a = r b → (f a).2 = (f b).2 → a = b) (k : ℕ) :
    (Finset.univ.filter fun a => r a < k).card ≤ (lam.rowLens.take k).sum := by
  classical
  rw [sum_take_rowLens_eq_card_filter_fst]
  -- Every column index in sight is smaller than the length of the top row.
  have hlt : ∀ c ∈ lam.cells, c.2 ∈ Finset.range (lam.rowLen 0) := by
    intro c hc
    refine Finset.mem_range.mpr (lt_of_lt_of_le ?_ (lam.rowLen_anti 0 c.1 c.1.zero_le))
    exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp ((_root_.YoungDiagram.mem_cells c).mp hc)
  -- Split both sides into their columns.
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => (f a).2)
      (t := Finset.range (lam.rowLen 0)) fun a _ => hlt _ (hmem a),
    Finset.card_eq_sum_card_fiberwise (f := fun c : ℕ × ℕ => c.2)
      (t := Finset.range (lam.rowLen 0)) fun c hc =>
      hlt c (Finset.mem_filter.mp hc).1]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [card_filter_fst_lt_filter_snd_eq lam k j]
  have hfib : ∀ a ∈ ((Finset.univ.filter fun a => r a < k).filter fun a => (f a).2 = j : Finset α),
      r a < k ∧ (f a).2 = j := by
    intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  -- In a fixed column, the elements are separated by their rows, and they fit in the column.
  refine le_min (le_of_le_of_eq ?_ (Finset.card_range k))
    (le_of_le_of_eq ?_ lam.colLen_eq_card.symm)
  · refine Finset.card_le_card_of_injOn r (fun a ha => ?_) fun a ha b hb hab => ?_
    · exact Finset.mem_range.mpr (hfib a ha).1
    · exact hcol a b hab (((hfib a ha).2).trans (hfib b hb).2.symm)
  · refine Finset.card_le_card_of_injOn f (fun a ha => ?_) hinj.injOn
    exact _root_.YoungDiagram.mem_col_iff.mpr
      ⟨(_root_.YoungDiagram.mem_cells _).mp (hmem a), (hfib a ha).2⟩

end YoungDiagram
namespace TauCeti
open YoungTableau
def Dominates {n : ℕ} (μ ν : n.Partition) : Prop :=
  ∀ k : ℕ,
    ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum

theorem dominates_iff {n : ℕ} {μ ν : n.Partition} :
    Dominates μ ν ↔
      ∀ k : ℕ,
        ((ν.parts.sort (· ≥ ·)).take k).sum ≤
          ((μ.parts.sort (· ≥ ·)).take k).sum :=
  Iff.rfl

private abbrev sortedParts {n : ℕ} (μ : n.Partition) : List ℕ :=
  μ.parts.sort (· ≥ ·)

private theorem sortedParts_sum {n : ℕ} (μ : n.Partition) : (sortedParts μ).sum = n := by
  calc
    (sortedParts μ).sum = (↑(sortedParts μ) : Multiset ℕ).sum :=
      (Multiset.sum_coe _).symm
    _ = μ.parts.sum := congrArg Multiset.sum (Multiset.sort_eq μ.parts (· ≥ ·))
    _ = n := μ.parts_sum

private theorem lex_lt_of_prefix_sum_le {l₁ l₂ : List ℕ} (hsum : l₁.sum = l₂.sum)
    (hpos₁ : ∀ i ∈ l₁, 0 < i) (hpos₂ : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum) (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => exact (hne rfl).elim
      | cons b l₂ =>
          have hb : 0 < b := hpos₂ b (by simp)
          simp only [List.sum_nil, List.sum_cons] at hsum
          omega
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          have ha : 0 < a := hpos₁ a (by simp)
          simp only [List.sum_cons, List.sum_nil] at hsum
          omega
      | cons b l₂ =>
          have hba : b ≤ a := by
            simpa only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
              add_zero] using hle 1
          rcases hba.eq_or_lt with hba | hba
          · subst b
            apply List.Lex.cons
            apply ih
            · simpa only [List.sum_cons, Nat.add_left_cancel_iff] using hsum
            · intro i hi
              exact hpos₁ i (by simp [hi])
            · intro i hi
              exact hpos₂ i (by simp [hi])
            · intro k
              simpa only [List.take_succ_cons, List.sum_cons, Nat.add_le_add_iff_left] using
                hle (k + 1)
            · intro h
              exact hne (congrArg (List.cons a) h)
          · exact List.Lex.rel hba

private theorem lex_lt_of_dominates_of_ne {n : ℕ} {μ ν : n.Partition}
    (hdom : Dominates μ ν) (hne : μ ≠ ν) :
    sortedParts ν < sortedParts μ := by
  apply lex_lt_of_prefix_sum_le (sortedParts_sum μ |>.trans (sortedParts_sum ν).symm)
  · intro i hi
    exact μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · intro i hi
    exact ν.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hi)
  · exact hdom
  · intro h
    apply hne
    apply Nat.Partition.ext
    calc
      μ.parts = ↑(sortedParts μ) := (Multiset.sort_eq μ.parts (· ≥ ·)).symm
      _ = ↑(sortedParts ν) := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
      _ = ν.parts := Multiset.sort_eq ν.parts (· ≥ ·)

theorem Dominates.antisymm {n : ℕ} {μ ν : n.Partition}
    (hμν : Dominates μ ν) (hνμ : Dominates ν μ) : μ = ν := by
  by_contra hne
  have hν_lt_μ := lex_lt_of_dominates_of_ne hμν hne
  have hμ_lt_ν := lex_lt_of_dominates_of_ne hνμ (Ne.symm hne)
  exact hν_lt_μ.asymm hμ_lt_ν

theorem card_filter_youngBlock_lt {n : ℕ} (μ : n.Partition) (k : ℕ) :
    (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) < k).card =
      ((μ.parts.sort (· ≥ ·)).take k).sum := by
  classical
  -- Each block of `μ` is the fiber of `youngBlock μ` over its label, and has the size of a part.
  have hfiber : ∀ i : ℕ, (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) = i).card =
      (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro i
    by_cases hi : i < (μ.parts.sort (· ≥ ·)).length
    · rw [List.getD_eq_getElem _ _ hi, ← Fintype.card_subtype]
      refine (Fintype.card_congr ((youngBlockEquiv μ ⟨i, hi⟩).trans
        (Equiv.subtypeEquivRight fun x => ?_))).symm.trans (Fintype.card_fin _)
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi), Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      exact fun x _ h => hi (h ▸ (youngBlock μ x).2)
  -- A partial sum of a list is the sum of its first entries, read off with `List.getD`.
  have hsum : ∀ m : ℕ, ((μ.parts.sort (· ≥ ·)).take m).sum =
      ∑ i ∈ Finset.range m, (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      rcases lt_or_ge m (μ.parts.sort (· ≥ ·)).length with h | h
      · rw [List.sum_take_succ _ _ h, List.getD_eq_getElem _ _ h]
      · rw [List.take_of_length_le h, List.take_of_length_le (h.trans (Nat.le_succ m)),
          List.getD_eq_default _ _ h, add_zero]
  -- Split the labels into blocks, and the partial sum into parts.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin n => (youngBlock μ x : ℕ)) (t := Finset.range k) (fun x hx => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simpa using hx),
    hsum k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hfiber i]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun h => h ▸ Finset.mem_range.mp hi

private theorem stabilizer_quotientGroup_mk_youngSubgroup {n : ℕ}
    (μ : n.Partition) (g : Equiv.Perm (Fin n)) :
    MulAction.stabilizer (Equiv.Perm (Fin n)) (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) =
      fiberSubgroup (youngBlock μ ∘ ⇑(g⁻¹)) := by
  have hs : (g : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) =
      g • ((1 : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
  rw [hs, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_quotient, youngSubgroup_eq_fiberSubgroup]
  apply fiberSubgroup_map_conj
  intro a b
  simp

theorem dominates_of_youngBlock_colIndex_injective {lam : YoungDiagram} (t : YoungTableau lam)
    (μ : lam.card.Partition) (g : Equiv.Perm (Fin lam.card))
    (h : ∀ x y, youngBlock μ (g⁻¹ x) = youngBlock μ (g⁻¹ y) → colIndex t x = colIndex t y →
      x = y) :
    Dominates (shapePartition lam) μ := by
  classical
  refine dominates_iff.mpr fun k => ?_
  rw [shapePartition_parts_sort, ← card_filter_youngBlock_lt μ k]
  -- Transport the count along `g`, then feed it to the counting core.
  have hcard : (Finset.univ.filter fun x : Fin lam.card => (youngBlock μ x : ℕ) < k).card =
      (Finset.univ.filter fun x : Fin lam.card => (youngBlock μ (g⁻¹ x) : ℕ) < k).card :=
    Finset.card_equiv (g : Equiv.Perm (Fin lam.card)) fun x => by
      simp [Equiv.Perm.inv_def]
  rw [hcard]
  refine YoungDiagram.card_filter_le_sum_take_rowLens lam (fun x => (youngBlock μ (g⁻¹ x) : ℕ))
    (fun x => ((t.symm x : ↥lam.cells) : ℕ × ℕ)) (fun x => (t.symm x).2)
    (fun x y hxy => t.symm.injective (Subtype.ext hxy)) (fun x y hr hc => ?_) k
  exact h x y (Fin.ext hr) (by simpa only [colIndex_def] using hc)

theorem dominates_of_forall_swap_smul_ne {lam : YoungDiagram} (t : YoungTableau lam)
    (μ : lam.card.Partition) (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)
    (h : ∀ x y : Fin lam.card, x ≠ y → colIndex t x = colIndex t y → Equiv.swap x y • q ≠ q) :
    Dominates (shapePartition lam) μ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine dominates_of_youngBlock_colIndex_injective t μ g fun x y hr hc => ?_
  by_contra hxy
  refine h x y hxy hc ?_
  -- the transposition preserves the rows of the tabloid, hence lies in its stabilizer
  have hmem : Equiv.swap x y ∈
      MulAction.stabilizer (Equiv.Perm (Fin lam.card))
        ((g : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)) := by
    rw [stabilizer_quotientGroup_mk_youngSubgroup]
    exact swap_mem_fiberSubgroup hr
  exact MulAction.mem_stabilizer_iff.mp hmem

theorem dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition)
    (q : Equiv.Perm (Fin lam.card) ⧸ youngSubgroup μ)
    (h : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t)
      (MonoidAlgebra.single q 1) ≠ 0) :
    Dominates (shapePartition lam) μ :=
  dominates_of_forall_swap_smul_ne t μ q fun _ _ hxy hcol hfix =>
    h (asAlgebraHom_columnAntisymmetrizer_single_eq_zero t μ q (swap_mem_colSubgroup hcol)
      (Equiv.Perm.sign_swap hxy) hfix)

namespace YoungTableau
theorem asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition) (h : ¬Dominates (shapePartition lam) μ)
    (x : (permutationModule μ).V) :
    (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) x = 0 := by
  have hx : x ∈ Submodule.span ℚ (Set.range (permutationModuleBasis μ)) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨q, rfl⟩ := hw
    rw [MonoidAlgebra.basis_apply]
    by_contra hne
    exact h (dominates_of_asAlgebraHom_columnAntisymmetrizer_ne_zero t μ q hne)
  | zero => rw [map_zero]
  | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
  | smul r u _ hu => rw [map_smul, hu, smul_zero]

theorem dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero {lam : YoungDiagram}
    (t : YoungTableau lam) (μ : lam.card.Partition) {x : (permutationModule μ).V}
    (hx : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) x ≠ 0) :
    Dominates (shapePartition lam) μ := by
  by_contra h
  exact hx (asAlgebraHom_columnAntisymmetrizer_apply_eq_zero_of_not_dominates t μ h x)

end YoungTableau
theorem isIrreducible_spechtSubrepresentation (μ : YoungDiagram) :
    (spechtSubrepresentation μ).toRepresentation.IsIrreducible :=
  D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom (isAtom_spechtSubrepresentation μ)

variable {lam : YoungDiagram}
attribute [local instance] YoungTableau.decidablePredMemColSubgroup
theorem dominates_of_intertwiningMap_ne_zero (μ : lam.card.Partition)
    {f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ} (hf : f ≠ 0) :
    Dominates (shapePartition lam) μ := by
  obtain ⟨t⟩ := YoungTableau.nonempty lam
  obtain ⟨e, he, hbe⟩ := exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid t
  have : (spechtSubrepresentation lam).toRepresentation.IsIrreducible :=
    isIrreducible_spechtSubrepresentation lam
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  -- the signed sum of the column translates of `e` is the polytabloid, hence nonzero
  set E : (spechtSubrepresentation lam).toSubmodule :=
    ∑ q : colSubgroup t, ((Equiv.Perm.sign (q : Equiv.Perm (Fin lam.card)) : ℤ) : ℚ) •
      (spechtSubrepresentation lam).toRepresentation q ⟨e, he⟩ with hE
  -- the action on the Specht module is the restriction of the ambient action
  have hact : ∀ (g : Equiv.Perm (Fin lam.card)) (v : (spechtSubrepresentation lam).toSubmodule),
      ((spechtSubrepresentation lam).toRepresentation g v :
          (permutationModule (shapePartition lam)).V) =
        (permutationModule (shapePartition lam)).ρ g v :=
    fun g v =>
      LinearMap.coe_restrict_apply ((spechtSubrepresentation lam).apply_mem_toSubmodule g) v
  have hEcoe : (E : (permutationModule (shapePartition lam)).V) = polytabloid t := by
    rw [hE, ← hbe, asAlgebraHom_columnAntisymmetrizer_apply]
    push_cast
    exact Finset.sum_congr rfl fun q _ => by rw [hact]
  have hEne : E ≠ 0 := fun h =>
    polytabloid_ne_zero t (by rw [← hEcoe, h, ZeroMemClass.coe_zero])
  -- and `f` carries it to `b_t` applied to `f ⟨e, he⟩`
  have hfE : (permutationModule μ).ρ.asAlgebraHom (columnAntisymmetrizer t) (f ⟨e, he⟩) = f E := by
    rw [asAlgebraHom_columnAntisymmetrizer_apply, hE, map_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [map_smul, f.isIntertwining]
  refine dominates_of_asAlgebraHom_columnAntisymmetrizer_apply_ne_zero t μ
    (x := f ⟨e, he⟩) ?_
  rw [hfE]
  exact fun h => hEne (hinj (h.trans (map_zero f).symm))

theorem intertwiningMap_eq_zero_of_not_dominates (μ : lam.card.Partition)
    (h : ¬Dominates (shapePartition lam) μ)
    (f : Representation.IntertwiningMap (spechtSubrepresentation lam).toRepresentation
      (permutationModule μ).ρ) :
    f = 0 := by
  by_contra hf
  exact h (dominates_of_intertwiningMap_ne_zero μ hf)

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
