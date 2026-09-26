/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/FiniteSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/FiniteSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original dependent finite support construction -/

/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
Faithful excerpt port of `Algorithm/Data/DFinsupp/Defs.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

/-! Modified from `Mathlib.Data.DFinsupp.Basic` (upstream attribution). -/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable {d : ∀ i, β i} {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i}
variable (β)

/-- A dependent function `Π i, β i` with finite support, with notation `Π₀' i, [β i, d i]`.

Note that `DFinsupp'.support` is the preferred API for accessing the support of the function,
`DFinsupp'.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure DFinsupp' (d : ∀ i, β i) : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp'`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp'`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = d i }

variable {β}

/--
`Π₀' i, [β i, d i]` denotes the type of dependent functions with finite support `DFinsupp β d`.
-/
notation3 "Π₀' "(...)", ""[" β:(scoped β => β) ", " d:(scoped d => d) "]" => DFinsupp' β d

/--
`ι →₀' [β, d]` denotes the type of functions with finite support
`DFinsupp' (fun _ : ι ↦ β) (fun _ : ι ↦ d)`.
-/
notation3 ι " →₀' ""[" β ", " d "]" => DFinsupp' (fun _ : ι ↦ β) (fun _ : ι ↦ d)

namespace DFinsupp'

section Basic

instance instDFunLike : DFunLike (Π₀' i, [β i, d i]) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀' i, [β i, d i]` and
  `Π i, β i`. (All dependent functions on a finite type are finitely supported.) -/
def equivFunOnFintype [Fintype ι] : (Π₀' i, [β i, d i]) ≃ ∀ i, β i
    where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl
  right_inv _ := rfl

variable [DecidableEq ι]

section SupportBasic

variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

/-- Set `{i | f x ≠ d i}` as a `Finset`. -/
def support (f : Π₀' i, [β i, d i]) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ d i) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩


end SupportBasic
end Basic
end DFinsupp'
