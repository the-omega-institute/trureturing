/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/LatinCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Row and column injectivity and the three array outcomes. -/

import Mathlib.Data.Fintype.EquivFin

namespace MaLatin

def Latin {n : ℕ} (A : Fin n → Fin n → α) : Prop :=
  (∀ i, Function.Injective (A i)) ∧ (∀ j, Function.Injective fun i => A i j)

def Rainbow {n : ℕ} (A : Fin n → Fin n → α) : Prop :=
  ∃ p : Equiv.Perm (Fin n), Function.Injective fun i => A i (p i)

def EqualColumns {n : ℕ} (A : Fin n → Fin n → α) : Prop :=
  ∀ c d r, ∃ s, A r c = A s d

def Motif (A : Fin 4 → Fin 4 → α) : Prop :=
  ∃ r₀ r₁ r₂ c₀ c₁ c₂ : Fin 4,
    r₀ ≠ r₁ ∧ r₀ ≠ r₂ ∧ r₁ ≠ r₂ ∧ c₀ ≠ c₁ ∧ c₀ ≠ c₂ ∧ c₁ ≠ c₂ ∧
    A r₁ c₀ = A r₀ c₁ ∧ A r₁ c₁ = A r₀ c₂ ∧ A r₁ c₂ = A r₀ c₀ ∧
    A r₂ c₀ = A r₀ c₂ ∧ A r₂ c₂ ≠ A r₀ c₁

def allFin {n : ℕ} (f : Fin n → Bool) := (List.finRange n).all f

def anyFin {n : ℕ} (f : Fin n → Bool) := (List.finRange n).any f

theorem allFin_true {n : ℕ} {f : Fin n → Bool} :
    allFin f = true ↔ ∀ i, f i = true := by
  simp [allFin, List.all_eq_true]

theorem anyFin_true {n : ℕ} {f : Fin n → Bool} :
    anyFin f = true ↔ ∃ i, f i = true := by
  simp [anyFin, List.any_eq_true]

def injectiveB {n : ℕ} (p : Fin n → Fin n) : Bool :=
  allFin fun i => allFin fun j => if i < j then decide (p i ≠ p j) else true

theorem injective_of_injectiveB {n : ℕ} {p : Fin n → Fin n}
    (hp : injectiveB p = true) : Function.Injective p := by
  simp only [injectiveB, allFin_true] at hp
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hji
  · have hh := hp i j
    simp [hij, h] at hh
  · exact hij
  · have hh := hp j i
    simp [hji, h] at hh

end MaLatin
