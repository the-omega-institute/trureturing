/- GID: D5/S3/Combinatorics/Partitions/PartitionAlternantCoefficients
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/PartitionAlternantCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Alternant coefficients distinguish literal partition labels at every finite row bound. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the complete license at
Library/FiniteGroups/tauceti2026partitionalternants.md.
Authors of the selected upstream proofs: The Tau Ceti contributors

PORT: TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156, selected declarations
from Symmetric/Alternant and Young/{Diagram,BetaNumbers,Partitions}.
Exact source ranges and license chain are retained in the Library note.
Retire each port when OUR lake-manifest.json-pinned Mathlib contains an equivalent
statement with the same hypotheses, and the replacement passes native checking at
that pin. Upstream acceptance alone is not the retirement condition.

Source preparation only: no native compatibility, axiom closure or registration
validation is asserted. The ordinary complex Specht trace comparison remains open.
The sole public theorem has a proposed content witness: a permutation relating two
strictly decreasing beta-number lists forces equality of the original partitions;
thus every off-diagonal coefficient vanishes. The proof must be checked natively.
All private upstream helpers are consumed along this theorem's proof path.
utility: none because this is a universal coefficient identity, not enumeration,
a checker, a numeric reduction or a certified instance.
-/

import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Omega

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.PartitionAlternantCoefficients

open MvPolynomial Equiv Finset

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

private noncomputable def alternant (α : σ → ℕ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det

variable {σ R}

private theorem alternant_def (α : σ → ℕ) :
    alternant σ R α = (Matrix.of fun i j => (X i : MvPolynomial σ R) ^ α j).det :=
  (rfl)

private theorem alternant_eq_sum (α : σ → ℕ) :
    alternant σ R α = ∑ τ : Perm σ, Perm.sign τ • ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i := by
  simp only [alternant_def, Matrix.det_apply, Matrix.of_apply]

private theorem coeff_alternant (α : σ → ℕ) (d : σ →₀ ℕ) :
    (alternant σ R α).coeff d =
      ∑ τ ∈ univ.filter (fun τ : Perm σ => ⇑d ∘ ⇑τ = α), ((Perm.sign τ : ℤ) : R) := by
  rw [alternant_eq_sum, coeff_sum, sum_filter]
  refine sum_congr rfl fun τ _ => ?_
  have hprod : ∏ i, (X (τ i) : MvPolynomial σ R) ^ α i = ∏ k, (X k) ^ α (τ.symm k) := by
    rw [← Equiv.prod_comp τ fun k => (X k : MvPolynomial σ R) ^ α (τ.symm k)]
    simp
  have hiff : d = Finsupp.indicator (univ : Finset σ) (fun k _ => α (τ.symm k)) ↔
      ⇑d ∘ ⇑τ = α := by
    constructor
    · rintro rfl
      funext i
      simp
    · intro h
      ext k
      simp [← h]
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R), coeff_C_mul,
    hprod, coeff_prod_X_pow]
  by_cases h : ⇑d ∘ ⇑τ = α <;> simp [hiff, h]

private theorem coeff_alternant_of_injective {α : σ → ℕ} (hα : Function.Injective α) (τ : Perm σ) :
    (alternant σ R α).coeff (Finsupp.equivFunOnFinite.symm (α ∘ τ)) =
      ((Perm.sign τ : ℤ) : R) := by
  rw [coeff_alternant, sum_eq_single τ⁻¹]
  · simp
  · intro ρ hρ hne
    have hρ' : (α ∘ τ) ∘ ρ = α := by simpa using (mem_filter.1 hρ).2
    refine absurd ?_ hne
    ext i
    have hi : τ (ρ i) = i := hα (congrFun hρ' i)
    exact Perm.eq_inv_iff_eq.2 hi
  · intro h
    refine absurd (mem_filter.2 ⟨mem_univ _, ?_⟩) h
    funext i
    simp

namespace YoungDiagram

open _root_.YoungDiagram

variable {μ : _root_.YoungDiagram} {r i j : ℕ}

private theorem rowLen_eq_zero_of_colLen_le {μ : _root_.YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))) (Nat.not_lt.mpr hi)

private theorem rowLen_injective : Function.Injective _root_.YoungDiagram.rowLen := by
  intro μ ν h
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, congrFun h i]

private def betaNumber (μ : _root_.YoungDiagram) (r i : ℕ) : ℕ := μ.rowLen i + (r - 1 - i)

private theorem betaNumber_def (μ : _root_.YoungDiagram) (r i : ℕ) :
    μ.betaNumber r i = μ.rowLen i + (r - 1 - i) := (rfl)

private theorem betaNumber_lt_betaNumber (μ : _root_.YoungDiagram) (hij : i < j) (hj : j < r) :
    μ.betaNumber r j < μ.betaNumber r i := by
  have := μ.rowLen_anti i j hij.le
  simp only [betaNumber_def]
  omega

-- The antecedents of `betaNumber_lt_betaNumber` mention no beta-number, so the `@[grind →]`
-- pattern does not exist; the useful trigger is a pair of beta-numbers sharing a bound, which is
-- what makes `grind` derive `βᵢ ≠ βⱼ` and `βᵢ - βⱼ ≠ 0` on its own.

private theorem eq_of_betaNumber_eq {ν : _root_.YoungDiagram} (hμ : μ.colLen 0 ≤ r) (hν : ν.colLen 0 ≤ r)
    (h : ∀ i < r, μ.betaNumber r i = ν.betaNumber r i) : μ = ν := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < r
  · have := h i hi
    rw [betaNumber_def, betaNumber_def] at this
    omega
  · rw [rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.not_lt.mp hi)),
      rowLen_eq_zero_of_colLen_le (hν.trans (Nat.not_lt.mp hi))]

private theorem strictAnti_betaNumber (μ : _root_.YoungDiagram) (r : ℕ) :
    StrictAnti fun j : Fin r => μ.betaNumber r j :=
  fun _ j hij => μ.betaNumber_lt_betaNumber (Fin.lt_def.mp hij) j.isLt

private theorem ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) :=
  fun _ _ h => equivPartition.symm.injective (Subtype.ext h)

end YoungDiagram

/-- Shifted row lengths isolate the coefficient of the literal partition label.
The degree and alphabet size are independent; the row bounds include zero padding. -/
theorem partition_alternant_coefficient (N n : ℕ) (μ ν : Nat.Partition n)
    (hμ : (_root_.YoungDiagram.ofPartition μ).colLen 0 ≤ N)
    (hν : (_root_.YoungDiagram.ofPartition ν).colLen 0 ≤ N) :
    ((Matrix.of fun i j : Fin N => (X i : MvPolynomial (Fin N) R) ^
        ((_root_.YoungDiagram.ofPartition ν).rowLen j + (N - 1 - (j : ℕ)))).det).coeff
      (Finsupp.equivFunOnFinite.symm fun j : Fin N =>
        (_root_.YoungDiagram.ofPartition μ).rowLen j + (N - 1 - (j : ℕ))) =
      if ν = μ then 1 else 0 := by
  classical
  change (alternant (Fin N) R
    (fun j => YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition ν) N j)).coeff
      (Finsupp.equivFunOnFinite.symm fun j : Fin N =>
        YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition μ) N j) = _
  by_cases h : ν = μ
  · subst ν
    simpa [Function.comp_def] using coeff_alternant_of_injective (R := R)
      (YoungDiagram.strictAnti_betaNumber (_root_.YoungDiagram.ofPartition μ) N).injective
      (1 : Perm (Fin N))
  · rw [if_neg h, coeff_alternant]
    apply Finset.sum_eq_zero
    intro τ hτ
    have hp : (fun j : Fin N =>
        YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition μ) N (τ j)) =
        (fun j : Fin N => YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition ν) N j) := by
      simpa [Function.comp_def] using (Finset.mem_filter.mp hτ).2
    have hperm : List.Perm
        (List.ofFn (fun j : Fin N =>
          YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition ν) N j))
        (List.ofFn (fun j : Fin N =>
          YoungDiagram.betaNumber (_root_.YoungDiagram.ofPartition μ) N j)) := by
      rw [← hp]
      exact τ.ofFn_comp_perm _
    have hlist := hperm.eq_of_sortedGE
      (YoungDiagram.strictAnti_betaNumber (_root_.YoungDiagram.ofPartition ν) N).antitone.sortedGE_ofFn
      (YoungDiagram.strictAnti_betaNumber (_root_.YoungDiagram.ofPartition μ) N).antitone.sortedGE_ofFn
    have heq := List.ofFn_injective hlist
    have hd : _root_.YoungDiagram.ofPartition ν = _root_.YoungDiagram.ofPartition μ :=
      YoungDiagram.eq_of_betaNumber_eq hν hμ fun i hi => congrFun heq ⟨i, hi⟩
    exact (h (YoungDiagram.ofPartition_injective hd)).elim

end D5.S3.Combinatorics.Partitions.PartitionAlternantCoefficients
