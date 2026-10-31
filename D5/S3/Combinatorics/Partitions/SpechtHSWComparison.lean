/- GID: D5/S3/Combinatorics/Partitions/SpechtHSWComparison
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtHSWComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal three-row ordinary Specht traces equal the existing HSW Frobenius coefficients. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected and adapted from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
License, exact selections and consumers: Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtFrobeniusFormula
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti
open Equiv MvPolynomial

/-- The HSW descending Vandermonde is precisely the staircase alternant (2,1,0). -/
private theorem hsw_vandermonde3_eq_alternant :
    D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3 = alternant (Fin 3) ℤ (fun j => 3 - 1 - (j : ℕ)) := by
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3, alternant_def, Matrix.det_fin_three]
  norm_num [Matrix.of_apply]
  ring

private theorem schurPoly_fin {R : Type*} [CommSemiring R] {n : ℕ}
    (N : ℕ) (μ : n.Partition) :
    schurPoly (Fin N) R μ = diagramSchurPoly N R (_root_.YoungDiagram.ofPartition μ) := by
  rw [schurPoly_eq_rename, rename_diagramSchurPoly]

/-- Vandermonde coefficient isolation uses literal partitions, including zero-padded rows. -/
theorem coeff_hsw_vandermonde_mul_schurPoly {n : ℕ} (μ ν : n.Partition)
    (hμ : μ.parts.card ≤ 3) :
    (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.vandermonde3 * schurPoly (Fin 3) ℤ ν).coeff
        (Finsupp.equivFunOnFinite.symm fun i : Fin 3 =>
          (_root_.YoungDiagram.ofPartition μ).rowLen i + (2 - (i : ℕ))) =
      if μ = ν then 1 else 0 := by
  classical
  have hμ' : (_root_.YoungDiagram.ofPartition μ).colLen 0 ≤ 3 := by
    rwa [YoungDiagram.colLen_zero_ofPartition]
  by_cases hν : ν.parts.card ≤ 3
  · have hν' : (_root_.YoungDiagram.ofPartition ν).colLen 0 ≤ 3 := by
      rwa [YoungDiagram.colLen_zero_ofPartition]
    rw [hsw_vandermonde3_eq_alternant, schurPoly_fin, mul_comm,
      diagramSchurPoly_mul_alternant 3 _ hν']
    change (alternant (Fin 3) ℤ
      (fun i => (_root_.YoungDiagram.ofPartition ν).betaNumber 3 i)).coeff
        (Finsupp.equivFunOnFinite.symm fun i : Fin 3 =>
          (_root_.YoungDiagram.ofPartition μ).betaNumber 3 i) = _
    by_cases h : μ = ν
    · subst ν
      simpa using coeff_alternant_of_injective (σ := Fin 3) (R := ℤ)
        (YoungDiagram.strictAnti_betaNumber (_root_.YoungDiagram.ofPartition μ) 3).injective
        (1 : Perm (Fin 3))
    · rw [if_neg h, coeff_alternant]
      apply Finset.sum_eq_zero
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      change ((fun i : Fin 3 => (_root_.YoungDiagram.ofPartition μ).betaNumber 3 i) ∘ e) =
        (fun i : Fin 3 => (_root_.YoungDiagram.ofPartition ν).betaNumber 3 i) at he'
      have hs : StrictAnti
          ((fun i : Fin 3 => (_root_.YoungDiagram.ofPartition μ).betaNumber 3 i) ∘ e) := by
        rw [he']
        exact YoungDiagram.strictAnti_betaNumber _ 3
      have heq : e = 1 := StrictAnti.perm_eq hs
        (by simpa using YoungDiagram.strictAnti_betaNumber (_root_.YoungDiagram.ofPartition μ) 3)
      have hdiag : _root_.YoungDiagram.ofPartition μ = _root_.YoungDiagram.ofPartition ν := by
        apply YoungDiagram.eq_of_betaNumber_eq hμ' hν'
        intro j hj
        have hj' := congrFun he' (⟨j, hj⟩ : Fin 3)
        simpa [heq] using hj'
      exact (h (YoungDiagram.ofPartition_injective hdiag)).elim
  · have hne : μ ≠ ν := fun h => hν (h ▸ hμ)
    rw [(schurPoly_eq_zero_iff (σ := Fin 3) (R := ℤ) ν).mpr
      (by simpa only [Fintype.card_fin, YoungDiagram.colLen_zero_ofPartition] using
        Nat.lt_of_not_ge hν)]
    simp [hne]

/-- The existing integer coefficient equals the integer character of the same literal shape.
The power-sum comparison has no degree/alphabet bound. -/
theorem spechtCharValue_eq_hsw_frobChar {n : ℕ} (μ ρ : n.Partition)
    (hμ : μ.parts.card ≤ 3) {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    spechtCharValue μ ρ =
      D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar (fun i : Fin 3 => (_root_.YoungDiagram.ofPartition μ).rowLen i) τ := by
  classical
  have hp : D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.powerSumProd τ = psumPart (Fin 3) ℤ ρ := by
    rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.powerSumProd, psumPart, ← hτ, Multiset.map_coe, Multiset.prod_coe]
  rw [D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar, hp, psumPart_eq_sum_spechtCharValue_smul_schurPoly ℤ,
    Finset.mul_sum, coeff_sum]
  simp_rw [mul_smul_comm, coeff_smul, coeff_hsw_vandermonde_mul_schurPoly μ _ hμ]
  simp

/-- The actual ordinary trace of the independently constructed same-partition complex
polytabloid representation is the coefficient used by D5.S3.Combinatorics.Partitions.HemmerStraubWestrem. Fixed points are retained in hπ. -/
theorem spechtTrace_eq_hsw_frobChar {n : ℕ} (μ ρ : n.Partition) (hμ : μ.parts.card ≤ 3)
    (π : Perm (Fin n)) (hπ : π.partition.parts = ρ.parts)
    {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar (fun i : Fin 3 => (_root_.YoungDiagram.ofPartition μ).rowLen i) τ : ℂ) := by
  obtain ⟨_, _, htrace⟩ := (spechtCharValue_ordinaryTrace μ ρ).2
  rw [htrace π hπ, spechtCharValue_eq_hsw_frobChar μ ρ hμ hτ]

/-- The literal partition of a decreasing triple. Empty rows are omitted by rowLens;
no relabelling of the irreducible representations is used. -/
def triplePartition {n : ℕ} (a : Fin 3 → ℕ) (ha : Antitone a) (hsum : ∑ i, a i = n) :
    n.Partition :=
  (YoungDiagram.ofRowLensFin a ha).toPartition
    ((YoungDiagram.card_ofRowLensFin a ha).trans hsum)

/-- The shape has exactly the positive row lengths, and its first three rows are the
original triple, with every later row zero. This includes the all-zero triple. -/
theorem triplePartition_shape {n : ℕ} (a : Fin 3 → ℕ) (ha : Antitone a)
    (hsum : ∑ i, a i = n) :
    (triplePartition a ha hsum).parts = (YoungDiagram.ofRowLensFin a ha).rowLens ∧
      (∀ i : Fin 3, (_root_.YoungDiagram.ofPartition (triplePartition a ha hsum)).rowLen i = a i) ∧
      (∀ i : ℕ, 3 ≤ i →
        (_root_.YoungDiagram.ofPartition (triplePartition a ha hsum)).rowLen i = 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    rw [triplePartition, _root_.YoungDiagram.ofPartition_toPartition]
    exact YoungDiagram.rowLen_ofRowLensFin a ha i
  · intro i hi
    rw [triplePartition, _root_.YoungDiagram.ofPartition_toPartition]
    exact YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le a ha hi

/-- Actual ordinary character interpretation for the exact padded three-row input of HSW.
There is no parity restriction on the rows or on the degree. -/
theorem spechtTrace_triplePartition_eq_hsw_frobChar {n : ℕ}
    (a : Fin 3 → ℕ) (ha : Antitone a) (hsum : ∑ i, a i = n) (ρ : n.Partition)
    (π : Perm (Fin n)) (hπ : π.partition.parts = ρ.parts)
    {τ : List ℕ} (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ (triplePartition a ha hsum)).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar a τ : ℂ) := by
  have hshape := triplePartition_shape a ha hsum
  have hheight : (triplePartition a ha hsum).parts.card ≤ 3 := by
    rw [hshape.1]
    change (YoungDiagram.ofRowLensFin a ha).rowLens.length ≤ 3
    rw [_root_.YoungDiagram.length_rowLens]
    exact YoungDiagram.colLen_zero_ofRowLensFin_le a ha
  have h := spechtTrace_eq_hsw_frobChar (triplePartition a ha hsum) ρ hheight π hπ hτ
  have hrows : (fun i : Fin 3 =>
      (_root_.YoungDiagram.ofPartition (triplePartition a ha hsum)).rowLen i) = a :=
    funext hshape.2.1
  rw [hrows] at h
  exact h

end TauCeti
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
