/- GID: D5/S3/Combinatorics/Partitions/SpechtYoungTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtYoungTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Young dominance and diagonal dimensions for the same actual complex ordinary Specht traces. -/

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
import D5.S3.Combinatorics.Partitions.SpechtYoungMultiplicity
import D5.S3.Combinatorics.Partitions.SpechtFrobeniusPairing

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace TauCeti
open _root_.Equiv CategoryTheory
variable {n : ℕ}
@[simp]
theorem toPartition_eq_shapePartition (μ : YoungDiagram) : μ.toPartition rfl = shapePartition μ :=
  (rfl)

@[simp]
theorem ofPartition_shapePartition (μ : YoungDiagram) :
    YoungDiagram.ofPartition (shapePartition μ) = μ :=
  YoungDiagram.ofPartition_toPartition rfl

theorem char_permutationModule {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    (permutationModule μ).ρ.character σ =
      (Nat.card
        {q : Equiv.Perm (Fin n) ⧸ youngSubgroup μ // σ • q = q} : ℚ) := by
  let : Finite (Equiv.Perm (Fin n) ⧸ youngSubgroup μ) := inferInstance
  exact char_ofMulAction ℚ _ σ

private theorem spechtChar_eq_of_isConj (μ : n.Partition) {σ τ : Perm (Fin n)}
    (h : IsConj σ τ) : spechtChar μ σ = spechtChar μ τ := by
  rw [← spechtCharConjClasses_mk μ σ, ← spechtCharConjClasses_mk μ τ,
    ConjClasses.mk_eq_mk_iff_isConj.mpr h]

theorem spechtChar_shapePartition (D : YoungDiagram) (σ : Equiv.Perm (Fin D.card)) :
    (spechtChar (shapePartition D) σ : ℚ) =
      (spechtSubrepresentation D).toRepresentation.character σ := by
  rw [spechtChar_cast]
  change (spechtSubrepresentation (YoungDiagram.ofPartition (shapePartition D))).toRepresentation.character
    ((finCongr (YoungDiagram.card_ofPartition (shapePartition D)).symm).permCongr σ) = _
  -- transport along an equality of diagrams is the identity once the equality is `rfl`
  suffices h : ∀ (D' : YoungDiagram), D' = D → ∀ (p : D.card = D'.card),
      (spechtSubrepresentation D').toRepresentation.character ((finCongr p).permCongr σ) =
        (spechtSubrepresentation D).toRepresentation.character σ from
    h _ (ofPartition_shapePartition D) _
  rintro D' rfl p
  rw [finCongr_refl, Equiv.permCongr_def, Equiv.refl_symm, Equiv.refl_trans, Equiv.trans_refl]

theorem sum_spechtChar_shapePartition_mul_char_permutationModule (D : YoungDiagram)
    (μ : D.card.Partition) :
    ∑ π, (spechtChar (shapePartition D) π : ℚ) * (permutationModule μ).ρ.character π =
      D.card.factorial * spechtMultiplicity D μ := by
  letI : Invertible (Nat.card (Perm (Fin D.card)) : ℚ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (spechtSubrepresentation D).toRepresentation (permutationModule μ).ρ
  change (Nat.card (Perm (Fin D.card)) : ℚ)⁻¹ * _ = (spechtMultiplicity D μ : ℚ) at h
  rw [Nat.card_perm, Nat.card_fin] at h
  have hfac : (D.card.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  rw [← h, mul_inv_cancel_left₀ hfac]
  -- a permutation is conjugate to its inverse, so the Specht character does not see the inverse
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [mul_comm, ← spechtChar_shapePartition, spechtChar_eq_of_isConj _
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr (Equiv.Perm.cycleType_inv π).symm)]

private theorem sum_spechtChar_mul_char_permutationModule_eq_zero {l ν : n.Partition}
    (h : ¬Dominates l ν) :
    ∑ π, (spechtChar l π : ℚ) * (permutationModule ν).ρ.character π = 0 := by
  obtain ⟨D, hc, rfl⟩ : ∃ (D : YoungDiagram) (hc : D.card = n), D.toPartition hc = l :=
    ⟨_, _, YoungDiagram.toPartition_ofPartition (p := l)⟩
  subst hc
  rw [toPartition_eq_shapePartition] at h ⊢
  rw [sum_spechtChar_shapePartition_mul_char_permutationModule,
    spechtMultiplicity_eq_zero_of_not_dominates ν h, Nat.cast_zero, mul_zero]

private theorem sum_spechtChar_mul_char_permutationModule_self (l : n.Partition) :
    ∑ π, (spechtChar l π : ℚ) * (permutationModule l).ρ.character π = n.factorial := by
  obtain ⟨D, hc, rfl⟩ : ∃ (D : YoungDiagram) (hc : D.card = n), D.toPartition hc = l :=
    ⟨_, _, YoungDiagram.toPartition_ofPartition (p := l)⟩
  subst hc
  rw [toPartition_eq_shapePartition, sum_spechtChar_shapePartition_mul_char_permutationModule,
    spechtMultiplicity_self, Nat.cast_one, mul_one]

/-- Rational pairing and actual complex trace agree under the exact rational-to-complex map.
Both sides use the independently constructed same-labelled Specht module. -/
private theorem ratCast_sum_spechtChar_mul_char_permutationModule (μ ν : n.Partition) :
    algebraMap ℚ ℂ (∑ π : Perm (Fin n),
      (spechtChar μ π : ℚ) * (permutationModule ν).ρ.character π) =
    ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
      (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℂ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [map_mul, char_permutationModule]
  change algebraMap ℚ ℂ (spechtChar μ π : ℚ) *
      algebraMap ℚ ℂ (Nat.card {q : Perm (Fin n) ⧸ youngSubgroup ν // π • q = q} : ℚ) =
    (spechtModuleℂ μ).character π * _
  rw [character_spechtModuleℂ_intCast]
  simp only [map_intCast, map_natCast]

/-- The actual complex Young multiplicity vanishes outside the dominance cone. -/
theorem finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero {μ ν : n.Partition}
    (h : ¬Dominates μ ν) :
    Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ ν) = 0 := by
  have hq := sum_spechtChar_mul_char_permutationModule_eq_zero h
  have hc := congrArg (algebraMap ℚ ℂ) hq
  rw [ratCast_sum_spechtChar_mul_char_permutationModule,
    sum_spechtTrace_mul_card_fixedPoints, map_zero] at hc
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  exact_mod_cast (mul_eq_zero.mp hc).resolve_left hf

/-- The actual complex Young multiplicity of the same literal shape is one. -/
theorem finrank_hom_spechtModuleℂ_permutationModuleℂ_self (μ : n.Partition) :
    Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ μ) = 1 := by
  have hc := congrArg (algebraMap ℚ ℂ)
    (sum_spechtChar_mul_char_permutationModule_self μ)
  rw [ratCast_sum_spechtChar_mul_char_permutationModule,
    sum_spechtTrace_mul_card_fixedPoints] at hc
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hm : (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ μ) : ℂ) = 1 := by
    apply mul_left_cancel₀ hf
    simpa only [map_natCast, mul_one] using hc
  exact_mod_cast hm


/-- Isomorphic actual complex Specht modules have the same Young-diagram label.
The diagonal Young multiplicity and the dominance zeros distinguish the labels. -/
theorem spechtModuleℂ_iso_iff (μ ν : n.Partition) :
    Nonempty (spechtModuleℂ μ ≅ spechtModuleℂ ν) ↔ μ = ν := by
  constructor
  · rintro ⟨i⟩
    have hd {ρ κ : n.Partition} (j : spechtModuleℂ ρ ≅ spechtModuleℂ κ) :
        Dominates ρ κ := by
      by_contra h
      have he := (CategoryTheory.Linear.homCongr ℂ j (Iso.refl (permutationModuleℂ κ))).finrank_eq
      rw [finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero h,
        finrank_hom_spechtModuleℂ_permutationModuleℂ_self] at he
      exact Nat.zero_ne_one he
    exact (hd i).antisymm (hd i.symm)
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Genuine ordinary-trace row orthogonality for the preserved same-shape complex modules.
Simplicity is used by the pinned FDRep character orthogonality theorem; the Young-rule
triangularity above supplies the literal shape comparison in its isomorphism test. -/
theorem sum_spechtTrace_mul_spechtTrace_inv (μ ν : n.Partition) :
    (∑ π : Perm (Fin n),
      LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
        LinearMap.trace ℂ _ ((spechtModuleℂ ν).ρ π⁻¹)) =
      if μ = ν then (n.factorial : ℂ) else 0 := by
  classical
  letI : Invertible (Nat.card (Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := FDRep.char_orthonormal (spechtModuleℂ μ) (spechtModuleℂ ν)
  rw [spechtModuleℂ_iso_iff, Nat.card_perm, Nat.card_fin] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have htrace : (n.factorial : ℂ)⁻¹ *
      (∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
        LinearMap.trace ℂ _ ((spechtModuleℂ ν).ρ π⁻¹)) =
        (if μ = ν then (1 : ℂ) else 0) := by
    by_cases he : μ = ν
    · simpa only [if_pos he] using h
    · simpa only [if_neg he] using h
  calc
    _ = (n.factorial : ℂ) * ((n.factorial : ℂ)⁻¹ *
        ∑ π : Perm (Fin n), LinearMap.trace ℂ _ ((spechtModuleℂ μ).ρ π) *
          LinearMap.trace ℂ _ ((spechtModuleℂ ν).ρ π⁻¹)) :=
      (mul_inv_cancel_left₀ hf _).symm
    _ = (n.factorial : ℂ) * (if μ = ν then (1 : ℂ) else 0) := by rw [htrace]
    _ = _ := by split_ifs <;> simp

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
