/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Finite slash sums and the permutation interface for Hecke operators

An analytic Hecke operator is a finite sum of slash translates.  The
double-coset calculation supplies the finite permutation of representatives
which is needed for invariance.  This file isolates that finite algebraic
step from the still-missing analytic double-coset construction in Mathlib.
-/

open scoped BigOperators ModularForm

namespace D5.S1.NumberTheory.ModularForms

noncomputable section

variable {β G α I : Type*} [Monoid G] [AddCommGroup α]
  [SlashAction β G α] [Fintype I]

/-- The finite sum of slash translates indexed by a chosen representative family. -/
def finiteSlashSum (k : β) (f : α) (rep : I → G) : α :=
  ∑ i, SlashAction.map k (rep i) f

@[simp]
theorem finiteSlashSum_zero (k : β) (rep : I → G) :
    finiteSlashSum k (0 : α) rep = 0 := by
  simp [finiteSlashSum]

theorem finiteSlashSum_add (k : β) (f g : α) (rep : I → G) :
    finiteSlashSum k (f + g) rep =
      finiteSlashSum k f rep + finiteSlashSum k g rep := by
  simp only [finiteSlashSum, SlashAction.add_slash, Finset.sum_add_distrib]

/-- A finite permutation of representatives makes the slash sum invariant.

The hypothesis is the exact algebraic output needed from a double-coset
decomposition: after right multiplication by gamma, each translated summand is
identified with the summand at a permuted representative. -/
theorem finiteSlashSum_slash_of_perm
    (k : β) (f : α) (rep : I → G) (γ : G) (σ : Equiv.Perm I)
    (hperm : ∀ i, SlashAction.map k (rep i * γ) f =
      SlashAction.map k (rep (σ i)) f) :
    SlashAction.map k γ (finiteSlashSum k f rep) =
      finiteSlashSum k f rep := by
  rw [finiteSlashSum, SlashAction.sum_slash]
  calc
    (∑ i, SlashAction.map k γ (SlashAction.map k (rep i) f)) =
        ∑ i, SlashAction.map k (rep i * γ) f := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← SlashAction.slash_mul]
    _ = ∑ i, SlashAction.map k (rep (σ i)) f := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hperm i
    _ = ∑ i, SlashAction.map k (rep i) f := by
      simpa using (Equiv.sum_comp σ
        (fun i : I => SlashAction.map k (rep i) f))

/-- The permutation interface in the form supplied by a double-coset
decomposition.  A right translate of each representative differs from the
permuted representative by a left element of the invariant subgroup. -/
theorem finiteSlashSum_slash_of_subgroup_perm
    (H : Submonoid G) (k : β) (f : α) (rep : I → G) (γ : G) (σ : Equiv.Perm I)
    (hInv : ∀ h : G, h ∈ H → SlashAction.map k h f = f)
    (hrep : ∀ i, ∃ h : H, rep i * γ = (h : G) * rep (σ i)) :
    SlashAction.map k γ (finiteSlashSum k f rep) =
      finiteSlashSum k f rep := by
  apply finiteSlashSum_slash_of_perm k f rep γ σ
  intro i
  obtain ⟨h, hh⟩ := hrep i
  rw [hh, SlashAction.slash_mul, hInv h h.property]

end

end D5.S1.NumberTheory.ModularForms

#print axioms D5.S1.NumberTheory.ModularForms.finiteSlashSum_slash_of_perm
#print axioms D5.S1.NumberTheory.ModularForms.finiteSlashSum_slash_of_subgroup_perm
