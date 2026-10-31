/- GID: D5/S3/Combinatorics/Partitions/SpechtMonomialCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtMonomialCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sorted monomial coordinates in arbitrary finite alphabets for the fixed-tabloid Frobenius step. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected A17.2PORT from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Changes: selected declarations and surrounding namespaces; exact pinned Mathlib
and existing D5 suppliers are reused. Library/FiniteGroups/tauceti2026spechtpolytabloids.md
records immutable locators, license, consumers and retirement against OUR Mathlib pin.
SOURCE ONLY: no Lean/Lake invocation, native elaboration, axiom closure, proof-term
liveness, admission, validated Reg, emission, firstfreeze, deposit, PR or CI claim.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
These are necessary suppliers/comparisons for the full HSW target. No independent
firstfreeze or new-content qualification is claimed. Both original ordinary weighted
identities remain unfinished. No character is defined by a polynomial coefficient.
utility: none: arbitrary degrees and finite alphabets, no bounded enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtPolytabloid
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Finsupp.Multiset

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid

noncomputable section
open scoped BigOperators
namespace YoungDiagram
open _root_.YoungDiagram

theorem rowLen_eq_zero_of_colLen_le {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))) (Nat.not_lt.mpr hi)

theorem getD_rowLens (μ : YoungDiagram) (i : ℕ) : μ.rowLens.getD i 0 = μ.rowLen i := by
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, _root_.YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
      rowLen_eq_zero_of_colLen_le
        (le_of_eq_of_le _root_.YoungDiagram.length_rowLens.symm (Nat.le_of_not_lt hi))]

@[simp]
theorem rowLen_ofPartition {n : ℕ} (ν : n.Partition) (i : ℕ) :
    (ofPartition ν).rowLen i = (ν.parts.sort (· ≥ ·)).getD i 0 := by
  rw [← getD_rowLens, rowLens_ofPartition_eq_sort_parts]

end YoungDiagram

namespace TauCeti
open _root_.Equiv _root_.YoungDiagram Finset MvPolynomial

theorem prod_map_X_eq_monomial {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp (1 : R) := by
  rw [Finset.prod_multiset_map_count, ← prod_X_pow_eq_monomial, Multiset.toFinsupp_support]
  exact Finset.prod_congr rfl fun a _ => by rw [Multiset.toFinsupp_apply]

variable (N : ℕ) (μ : YoungDiagram)

noncomputable def rowLenWeight : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin N => μ.rowLen i

@[simp]
theorem rowLenWeight_apply (i : Fin N) : rowLenWeight N μ i = μ.rowLen i :=
  (rfl)

variable {σ : Type*} [Fintype σ] {n : ℕ}

noncomputable def partWeight (σ : Type*) [Fintype σ] {n : ℕ} (ν : n.Partition) : σ →₀ ℕ :=
  Finsupp.mapDomain (Fintype.equivFin σ).symm (rowLenWeight (Fintype.card σ) (ofPartition ν))

@[simp]
theorem partWeight_apply (ν : n.Partition) (x : σ) :
    partWeight σ ν x = (ofPartition ν).rowLen (Fintype.equivFin σ x) := by
  conv_lhs => rw [partWeight, ← (Fintype.equivFin σ).symm_apply_apply x]
  rw [Finsupp.mapDomain_apply_of_injective (Fintype.equivFin σ).symm.injective, rowLenWeight_apply]

private theorem exists_perm_comp_eq {β : Type*} {f g : σ → β}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) :
    ∃ e : Equiv.Perm σ, g ∘ e = f := by
  classical
  have hcard : ∀ b : β, Fintype.card {x : σ // f x = b} = Fintype.card {x : σ // g x = b} := by
    intro b
    have hb := congrArg (Multiset.count b) h
    rw [Multiset.count_map, Multiset.count_map] at hb
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa only [Finset.card, Finset.filter_val, eq_comm (a := b)] using hb
  exact ⟨Equiv.ofFiberEquiv fun b => Fintype.equivOfCardEq (hcard b),
    funext fun x => Equiv.ofFiberEquiv_map _ x⟩

theorem card_toMultiset_eq_degree (d : σ →₀ ℕ) : Multiset.card d.toMultiset = d.degree := by
  rw [Finsupp.card_toMultiset, Finsupp.degree_apply]
  rfl

noncomputable def weightSym (d : σ →₀ ℕ) (h : d.degree = n) : Sym σ n :=
  ⟨d.toMultiset, (card_toMultiset_eq_degree d).trans h⟩

@[simp]
theorem coe_weightSym (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightSym d h : Multiset σ) = d.toMultiset :=
  (rfl)

noncomputable def weightPartition (d : σ →₀ ℕ) (h : d.degree = n) : n.Partition :=
  Nat.Partition.ofSym (weightSym d h)

variable [DecidableEq σ]

@[simp]
theorem weightPartition_parts (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightPartition d h).parts = Multiset.map d d.support.val := by
  have hdedup : d.toMultiset.dedup = d.support.val :=
    congrArg Finset.val (Finsupp.toFinset_toMultiset d)
  -- `Nat.Partition.ofSym` is a bare structure instance, carrying no lemma for its `parts` field,
  -- so the only way in is to unfold it (and `weightPartition`) definitionally.
  change d.toMultiset.dedup.map (fun a => Multiset.count a d.toMultiset) = _
  rw [hdedup]
  exact Multiset.map_congr rfl fun a _ => Finsupp.count_toMultiset d a

theorem card_parts_weightPartition_le (d : σ →₀ ℕ) (h : d.degree = n) :
    (weightPartition d h).parts.card ≤ Fintype.card σ := by
  rw [weightPartition_parts, Multiset.card_map]
  exact Finset.card_le_univ d.support

private theorem map_univ_val (d : σ →₀ ℕ) :
    Multiset.map d univ.val
      = Multiset.map d d.support.val
        + Multiset.replicate (Fintype.card σ - d.support.card) 0 := by
  classical
  have hval : (univ : Finset σ).val = d.support.val + d.supportᶜ.val := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_val,
      add_tsub_cancel_of_le (Finset.val_le_iff.mpr d.support.subset_univ)]
  have hzero : Multiset.map d d.supportᶜ.val
      = Multiset.replicate (Fintype.card σ - d.support.card) 0 := by
    rw [Multiset.map_congr rfl (g := fun _ => (0 : ℕ)) fun x hx =>
      Finsupp.notMem_support_iff.mp (Finset.mem_compl.mp hx), Multiset.map_const']
    exact congrArg (Multiset.replicate · 0) (Finset.card_compl d.support)
  rw [hval, Multiset.map_add, hzero]

private theorem map_univ_val_partWeight (ν : n.Partition)
    (hν : ν.parts.card ≤ Fintype.card σ) :
    Multiset.map (partWeight σ ν) univ.val
      = ν.parts + Multiset.replicate (Fintype.card σ - ν.parts.card) 0 := by
  have hlen : (ν.parts.sort (· ≥ ·)).length = ν.parts.card := Multiset.length_sort _
  -- The alphabet is indexed by `Fin (Fintype.card σ)`, hence by `List.range (Fintype.card σ)`.
  have hval : Multiset.map (Fin.val : Fin (Fintype.card σ) → ℕ) (univ : Finset _).val
      = Multiset.range (Fintype.card σ) := by
    rw [← Finset.range_val, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ, Finset.map_val]
    rfl
  have hreindex : Multiset.map (partWeight σ ν) univ.val
      = ((List.range (Fintype.card σ)).map
          fun i => (ν.parts.sort (· ≥ ·)).getD i 0 : List ℕ) := by
    calc Multiset.map (partWeight σ ν) univ.val
        = Multiset.map ((fun i : ℕ => (ν.parts.sort (· ≥ ·)).getD i 0) ∘
            ((Fin.val : Fin (Fintype.card σ) → ℕ) ∘ (Fintype.equivFin σ))) univ.val :=
          Multiset.map_congr rfl fun x _ => by
            rw [partWeight_apply, YoungDiagram.rowLen_ofPartition]; rfl
      _ = ((List.range (Fintype.card σ)).map
            fun i => (ν.parts.sort (· ≥ ·)).getD i 0 : List ℕ) := by
          rw [← Multiset.map_map, ← Multiset.map_map, Multiset.map_univ_val_equiv, hval]
          rfl
  -- Sorted decreasingly, the exponents are the parts of `ν` followed by zeros.
  have hlist : ((List.range (Fintype.card σ)).map fun i => (ν.parts.sort (· ≥ ·)).getD i 0)
      = ν.parts.sort (· ≥ ·)
        ++ List.replicate (Fintype.card σ - (ν.parts.sort (· ≥ ·)).length) 0 := by
    refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
    rw [List.getElem_map, List.getElem_range]
    rcases lt_or_ge i (ν.parts.sort (· ≥ ·)).length with hi | hi
    · rw [List.getElem_append_left hi, List.getD_eq_getElem _ _ hi]
    · rw [List.getElem_append_right hi, List.getElem_replicate,
        List.getD_eq_default _ _ hi]
  rw [hreindex, hlist, ← Multiset.coe_add, Multiset.sort_eq, Multiset.coe_replicate, hlen]

theorem exists_perm_mapDomain_eq_partWeight (d : σ →₀ ℕ) (h : d.degree = n) :
    ∃ e : Equiv.Perm σ, Finsupp.mapDomain e d = partWeight σ (weightPartition d h) := by
  obtain ⟨e, he⟩ := exists_perm_comp_eq (f := ⇑d) (g := ⇑(partWeight σ (weightPartition d h)))
    (by rw [map_univ_val d, map_univ_val_partWeight _ (card_parts_weightPartition_le d h),
      weightPartition_parts, Multiset.card_map]; rfl)
  refine ⟨e, Finsupp.ext fun y => ?_⟩
  rw [← Finsupp.equivMapDomain_eq_mapDomain (e : σ ≃ σ) d, Finsupp.equivMapDomain_apply]
  have hy := congrFun he (e.symm y)
  rw [Function.comp_apply, Equiv.apply_symm_apply] at hy
  exact hy.symm

variable (R : Type*) [CommSemiring R]

@[simp]
theorem coeff_msymm_eq_zero_of_degree_ne (ν : n.Partition) {d : σ →₀ ℕ} (h : d.degree ≠ n) :
    (msymm σ R ν).coeff d = 0 := by
  rw [msymm, coeff_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [prod_map_X_eq_monomial, coeff_monomial, ite_eq_right]
  rintro rfl
  exact h (by rw [← card_toMultiset_eq_degree, Multiset.toFinsupp_toMultiset]; exact s.1.2)

@[simp]
theorem coeff_msymm (ν : n.Partition) {d : σ →₀ ℕ} (h : d.degree = n) :
    (msymm σ R ν).coeff d = if weightPartition d h = ν then 1 else 0 := by
  have hinj : ∀ s : Sym σ n, Multiset.toFinsupp (s : Multiset σ) = d ↔ s = weightSym d h :=
    fun s => by rw [Multiset.toFinsupp_eq_iff, ← Sym.coe_inj, coe_weightSym]
  rw [msymm, coeff_sum]
  simp only [prod_map_X_eq_monomial, coeff_monomial]
  by_cases hν : weightPartition d h = ν
  · rw [ite_eq_left hν,
      Finset.sum_eq_single (⟨weightSym d h, hν⟩ : {a : Sym σ n // Nat.Partition.ofSym a = ν})]
    · exact ite_eq_left ((hinj _).mpr rfl)
    · rintro ⟨s, hs⟩ - hne
      exact ite_eq_right fun hcoeff => hne (Subtype.ext ((hinj s).mp hcoeff))
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · refine (Finset.sum_eq_zero fun s _ => ite_eq_right fun hcoeff => hν ?_).trans
      (ite_eq_right hν).symm
    -- `weightPartition d h` is `Nat.Partition.ofSym (weightSym d h)` by definition, and `s` ranges
    -- over the multisets of letters whose partition is `ν`.
    exact (congrArg (fun t : Sym σ n => Nat.Partition.ofSym t)
      ((hinj s.1).mp hcoeff)).symm.trans s.2

variable {R}

theorem coeff_eq_coeff_partWeight [DecidableEq σ] {p : MvPolynomial σ R} (hp : p.IsSymmetric)
    {d : σ →₀ ℕ} (hd : d.degree = n) :
    p.coeff d = p.coeff (partWeight σ (weightPartition d hd)) := by
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d hd
  conv_rhs => rw [← he, ← hp e]
  exact (coeff_rename_mapDomain _ e.injective _ _).symm

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
