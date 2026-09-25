/- GID: D5/S3/Combinatorics/Posets/PPartitions/Definitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Posets/PPartitions/Definitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Sort]
   utility: none
   digest: Labelled posets have bounded partitions, extensions, chambers and W-polynomials. -/

import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Posets.PPartitions

open scoped BigOperators
noncomputable section

universe u

variable {α : Type u} [Fintype α] [PartialOrder α]

/-- A bounded positive `P`-partition. A value `v : Fin bound` represents the
positive integer `v + 1`; hence `bound = q + 1` represents `1, ..., q + 1`. -/
def PPartition (ω : α → ℕ) (bound : ℕ) : Type u :=
  {p : α → Fin bound //
    (∀ ⦃x y : α⦄, x ≤ y → p y ≤ p x) ∧
      ∀ ⦃x y : α⦄, x < y → ω y < ω x → p y < p x}

noncomputable instance (ω : α → ℕ) (bound : ℕ) : Fintype (PPartition ω bound) :=
  by
    classical
    exact Fintype.ofInjective (fun p => p.1) fun _ _ h => Subtype.ext h

/-- All linear extensions, represented by enumerations rather than by one chosen order. -/
def EnumeratingExtension (α : Type u) [Fintype α] [PartialOrder α] : Type u :=
  {e : Fin (Fintype.card α) ≃ α //
    ∀ ⦃x y : α⦄, x < y → e.symm x < e.symm y}

instance : CoeFun (EnumeratingExtension α) (fun _ => Fin (Fintype.card α) → α) :=
  ⟨fun e => e.1⟩

noncomputable instance : Fintype (EnumeratingExtension α) := by
  classical
  exact Fintype.ofInjective (fun e => e.1) fun _ _ h => Subtype.ext h

def descent (ω : α → ℕ) (e : EnumeratingExtension α)
    (i : Fin (Fintype.card α - 1)) : Prop :=
  ω (e ⟨i.val, by omega⟩) > ω (e ⟨i.val + 1, by omega⟩)

open Classical in
def descentFinset (ω : α → ℕ) (e : EnumeratingExtension α) :
    Finset (Fin (Fintype.card α - 1)) :=
  Finset.univ.filter (descent ω e)

def descentCard (ω : α → ℕ) (e : EnumeratingExtension α) : ℕ :=
  (descentFinset ω e).card

/-- The weakly decreasing chamber belonging to an extension, with a forced
strict drop at every descent of its label word. -/
def Chamber (ω : α → ℕ) (e : EnumeratingExtension α) (bound : ℕ) : Type :=
  {s : Fin (Fintype.card α) → Fin bound //
    Antitone s ∧ ∀ i, descent ω e i → s ⟨i.val + 1, by omega⟩ < s ⟨i.val, by omega⟩}

noncomputable instance (ω : α → ℕ) (e : EnumeratingExtension α) (bound : ℕ) :
    Fintype (Chamber ω e bound) :=
  Fintype.ofInjective (fun s => s.1) fun _ _ h => Subtype.ext h

/-- The actual finite descent enumerator over all linear extensions. -/
def WPolynomial (ω : α → ℕ) : Polynomial ℤ :=
  ∑ e : EnumeratingExtension α, Polynomial.X ^ descentCard ω e

end

end D5.S3.Combinatorics.Posets.PPartitions
