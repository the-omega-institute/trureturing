/- GID: D5/S3/ConceptDynamics/Faithfulness/FiniteQuotientHopficity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/FiniteQuotientHopficity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Surjective endomorphisms of finitely generated residually finite groups are injective. -/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.ResiduallyFinite

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in
docs/reports/licenses/TauCeti-LICENSE.txt.
Authors: The Tau Ceti contributors
Adapted from TauCeti at revision d91980bdc255e6e50506be147ad9bcb88eb9fcc0:
TauCeti/GroupTheory/ResiduallyFinite.lean and the finite_monoidHom instance in
TauCeti/GroupTheory/Finiteness.lean.
Source: https://github.com/TauCetiProject/TauCeti/tree/d91980bdc255e6e50506be147ad9bcb88eb9fcc0
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity

universe u v

/-- A homomorphism is determined by its values on a finite generating set. -/
private instance finite_monoidHom {M : Type u} {N : Type v}
    [MulOneClass M] [IsMulFG M] [MulOneClass N] [Finite N] : Finite (M →* N) := by
  obtain ⟨S, hSfin, hS⟩ := Monoid.exists_finite_of_isMulFG M
  have := hSfin.to_subtype
  refine Finite.of_injective (fun f : M →* N => fun s : S => f s) fun f g hfg => ?_
  exact MonoidHom.eq_of_eqOn_denseM hS fun s hs => congr_fun hfg ⟨s, hs⟩

/-- **Malcev's theorem.** Every surjective endomorphism of a finitely generated
residually finite group is injective. -/
theorem surjective_endomorphism_injective {G : Type u} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G] {f : G →* G} (hf : Function.Surjective f) :
    Function.Injective f := by
  refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
  by_contra hx1
  obtain ⟨N, hxN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem x hx1
  have : Finite (G ⧸ N.toSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  have hinj : Function.Injective fun ψ : G →* G ⧸ N.toSubgroup => ψ.comp f :=
    fun ψ χ h => (MonoidHom.cancel_right hf).mp h
  obtain ⟨ψ, hψ⟩ := Finite.surjective_of_injective hinj (QuotientGroup.mk' N.toSubgroup)
  have hπ : (QuotientGroup.mk' N.toSubgroup) x = 1 := by
    rw [← hψ, MonoidHom.comp_apply, hx, map_one]
  exact hxN ((QuotientGroup.eq_one_iff x).mp hπ)

end D5.S3.ConceptDynamics.Faithfulness.FiniteQuotientHopficity
