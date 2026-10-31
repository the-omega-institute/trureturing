/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurKostka
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurKostka
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
import D5.S3.Combinatorics.Partitions.SpechtSchurPieri

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

open MvPolynomial Finset

namespace TauCeti

open _root_.YoungDiagram (ofPartition card_ofPartition)

variable {R : Type*} [CommSemiring R]

open scoped Classical in
private theorem card_weight_eq_sum_partition {k n : ℕ} (c : Fin (k + 1) → ℕ)
    (μ : (n + c (Fin.last k)).Partition) :
    Nat.card {T : BoundedSSYT (k + 1) (ofPartition μ) // ⇑(BoundedSSYT.weight T) = c} =
      ∑ ν : n.Partition with (ofPartition μ).InterlacedBy (ofPartition ν),
        Nat.card {T : BoundedSSYT k (ofPartition ν) //
          ⇑(BoundedSSYT.weight T) = fun i => c i.castSucc} := by
  classical
  rw [BoundedSSYT.card_weight_eq_sum_interlacingShapes]
  symm
  refine sum_bij_ne_zero (fun ν _ _ => ofPartition ν) (fun ν hν hne => ?_)
    (fun ν₁ _ _ ν₂ _ _ h => YoungDiagram.ofPartition_injective h) (fun ν hν hne => ?_)
    fun _ _ _ => rfl
  · refine mem_filter.mpr ⟨YoungDiagram.mem_interlacingShapes.mpr
      ⟨(mem_filter.mp hν).2, not_lt.mp fun hlt => hne ?_⟩, ?_⟩
    · have := BoundedSSYT.isEmpty_of_lt_colLen hlt
      exact Nat.card_of_isEmpty
    · rw [card_ofPartition, card_ofPartition]
  · obtain ⟨hν, hcard⟩ := mem_filter.mp hν
    have hn : ν.card = n := by rw [card_ofPartition] at hcard; omega
    refine ⟨ν.toPartition hn, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_, ?_⟩
    · rw [_root_.YoungDiagram.ofPartition_toPartition]
      exact (YoungDiagram.mem_interlacingShapes.mp hν).1
    · rwa [_root_.YoungDiagram.ofPartition_toPartition]
    · exact _root_.YoungDiagram.ofPartition_toPartition hn

open scoped Classical in
private theorem prod_hsymm_eq_sum_card_smul (N : ℕ) :
    ∀ (k : ℕ) (c : Fin k → ℕ) (n : ℕ), ∑ i, c i = n →
      ∏ i, hsymm (Fin N) R (c i) = ∑ μ : n.Partition,
        (Nat.card {T : BoundedSSYT k (ofPartition μ) // ⇑(BoundedSSYT.weight T) = c} : R) •
          diagramSchurPoly N R (ofPartition μ)
  | 0, c, n, hc => by
    rw [Fin.sum_univ_zero] at hc
    subst hc
    have hbot : ofPartition (default : Nat.Partition 0) = ⊥ :=
      _root_.YoungDiagram.ext ((Finset.card_eq_zero.mp (card_ofPartition _)).trans
        _root_.YoungDiagram.cells_bot.symm)
    have hcard : Nat.card {T : BoundedSSYT 0 (ofPartition (default : Nat.Partition 0)) //
        ⇑(BoundedSSYT.weight T) = c} = 1 := by
      rw [hbot, Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun T T' => Subtype.ext (Subsingleton.elim _ _)⟩,
        ⟨⟨default, Subsingleton.elim _ _⟩⟩⟩
    rw [Fin.prod_univ_zero, Fintype.sum_unique, hcard, hbot, diagramSchurPoly_bot, Nat.cast_one,
      one_smul]
  | k + 1, c, n, hc => by
    rw [Fin.sum_univ_castSucc] at hc
    subst hc
    have pieri (ν : (∑ i : Fin k, c i.castSucc).Partition) :
        hsymm (Fin N) R (c (Fin.last k)) * diagramSchurPoly N R (ofPartition ν) =
          ∑ μ : (∑ i : Fin k, c i.castSucc + c (Fin.last k)).Partition with
            (ofPartition μ).InterlacedBy (ofPartition ν), diagramSchurPoly N R (ofPartition μ) := by
      have h := hsymm_mul_diagramSchurPoly (R := R) (N := N) (ofPartition ν) (c (Fin.last k))
      rwa [card_ofPartition] at h
    rw [Fin.prod_univ_castSucc, prod_hsymm_eq_sum_card_smul N k _ _ rfl, mul_comm, mul_sum]
    simp_rw [mul_smul_comm, pieri, Finset.smul_sum, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun μ _ => ?_
    rw [card_weight_eq_sum_partition, Nat.cast_sum, sum_smul, sum_filter]

theorem prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly {N k n : ℕ} (d : Fin k →₀ ℕ)
    (hd : d.degree = n) :
    ∏ i, hsymm (Fin N) R (d i) = ∑ μ : n.Partition,
      (diagramKostkaNumber (ofPartition μ) (Finsupp.mapDomain Fin.val d) : R) •
        diagramSchurPoly N R (ofPartition μ) := by
  rw [prod_hsymm_eq_sum_card_smul N k d n ((Finsupp.degree_eq_sum d).symm.trans hd)]
  refine sum_congr rfl fun μ _ => ?_
  rw [← BoundedSSYT.card_weight_eq,
    Nat.card_congr (Equiv.subtypeEquivRight fun T => DFunLike.coe_fn_eq)]

theorem prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly {σ : Type*} [Fintype σ]
    [DecidableEq σ] {k n : ℕ} (d : Fin k →₀ ℕ) (hd : d.degree = n) :
    ∏ i, hsymm σ R (d i) = ∑ μ : n.Partition,
      (diagramKostkaNumber (ofPartition μ) (Finsupp.mapDomain Fin.val d) : R) •
        schurPoly σ R μ := by
  have h := prod_hsymm_eq_sum_diagramKostkaNumber_smul_diagramSchurPoly (R := R)
    (N := Fintype.card σ) d hd
  apply_fun rename (Fintype.equivFin σ).symm at h
  rw [map_prod, map_sum] at h
  simp only [rename_hsymm, map_smul, ← schurPoly_eq_rename] at h
  exact h

theorem hsymmPart_eq_sum_kostkaNumber_smul_schurPoly (σ : Type*) [Fintype σ] [DecidableEq σ]
    {n : ℕ} (ν : n.Partition) :
    hsymmPart σ R ν = ∑ μ : n.Partition, (kostkaNumber μ ν : R) • schurPoly σ R μ := by

  set l := (ofPartition ν).rowLens with hl
  have hl_apply (i : Fin l.length) : rowLenWeight l.length (ofPartition ν) i = l[i.1] := by
    rw [rowLenWeight_apply, ← YoungDiagram.getD_rowLens]
    exact List.getD_eq_getElem l 0 i.2
  have hdeg : (rowLenWeight l.length (ofPartition ν)).degree = n := by
    rw [Finsupp.degree_eq_sum]
    simp only [hl_apply]
    refine (Fin.sum_univ_fun_getElem l id).trans ?_
    rw [List.map_id, hl, _root_.YoungDiagram.sum_rowLens_eq_card, card_ofPartition]
  have hprod : hsymmPart σ R ν = ∏ i, hsymm σ R (rowLenWeight l.length (ofPartition ν) i) := by
    simp only [hl_apply]
    rw [Fin.prod_univ_fun_getElem, hsymmPart, hl, _root_.YoungDiagram.rowLens_ofPartition_eq_sort_parts,
      ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.sort_eq]
  rw [hprod, prod_hsymm_eq_sum_diagramKostkaNumber_smul_schurPoly _ hdeg,
    mapDomain_rowLenWeight (by rw [hl, _root_.YoungDiagram.length_rowLens])]
  simp only [kostkaNumber_def]

theorem coeff_hsymmPart {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ} (ν : n.Partition)
    (d : σ →₀ ℕ) :
    (hsymmPart σ R ν).coeff d =
      ∑ μ : n.Partition, (kostkaNumber μ ν * diagramKostkaNumber (ofPartition μ)
        (Finsupp.mapDomain (fun x => (Fintype.equivFin σ x : ℕ)) d) : R) := by
  rw [hsymmPart_eq_sum_kostkaNumber_smul_schurPoly, coeff_sum]
  exact sum_congr rfl fun μ _ => by rw [coeff_smul, coeff_schurPoly, smul_eq_mul]

theorem coeff_hsymmPart_partWeight {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (ν ξ : n.Partition) (h : (ofPartition ξ).colLen 0 ≤ Fintype.card σ) :
    (hsymmPart σ R ν).coeff (partWeight σ ξ) =
      ∑ μ : n.Partition, (kostkaNumber μ ν * kostkaNumber μ ξ : R) := by
  rw [coeff_hsymmPart]
  exact sum_congr rfl fun μ _ => by
    rw [← coeff_schurPoly (R := R) μ, coeff_schurPoly_partWeight μ ξ h]

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
