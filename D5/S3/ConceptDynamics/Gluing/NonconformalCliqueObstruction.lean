/- GID: D5/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Gluing/NonconformalCliqueObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Pi, mathlib/module/Mathlib.Logic.Equiv.Fintype]
   utility: none
   digest: Nonconformal cliques obstruct global tuples despite complete pairwise consistency. -/

import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fintype

/-! Finite nonconformal clique obstruction with unrestricted non-clique coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Gluing.NonconformalCliqueObstruction

universe u v

/-- Only the clique coordinates must have distinct values; all other coordinates are free. -/
def InjectiveOnClique {V : Type v} (C : Finset V) (U : Set V) (q : ℕ)
    (r : U → Fin q) : Prop :=
  Function.Injective (fun x : {a : V // a ∈ U ∧ a ∈ C} => r ⟨x.val, x.property.1⟩)

/-- The full finite relation of tuples injective on the clique part of the scope. -/
noncomputable def cliqueRows {V : Type v} [Finite V] (C : Finset V) (U : Set V)
    (q : ℕ) : Finset (U → Fin q) := by
  classical
  letI := Fintype.ofFinite V
  exact (Set.toFinite {r : U → Fin q | InjectiveOnClique C U q r}).toFinset

private theorem scope_embedding {V : Type v} [Finite V] (C : Finset V) (U : Set V)
    (hU : ¬ (↑C : Set V) ⊆ U) :
    Nonempty ({a : V // a ∈ U ∧ a ∈ C} ↪ Fin (C.card - 1)) := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨x, hx, hxU⟩ := Set.not_subset.mp hU
  let f : {a : V // a ∈ U ∧ a ∈ C} → C := fun y => ⟨y.val, y.property.2⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg (fun z : C => z.val) h)
  have hmiss : (⟨x, hx⟩ : C) ∉ Set.range f := by
    rintro ⟨y, hy⟩
    have he : y.val = x := congrArg (fun z : C => z.val) hy
    exact hxU (he ▸ y.property.1)
  have hlt := Fintype.card_lt_of_injective_of_notMem f hf hmiss
  rw [Fintype.card_coe] at hlt
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin] using Nat.le_sub_one_of_lt hlt

/-- Extend a complete overlap tuple, including its unconstrained non-clique coordinates. -/
private theorem extend_overlap {V : Type v} [Finite V] (C : Finset V)
    (U W : Set V) (q : ℕ) (hq : 0 < q)
    (j : {a : V // a ∈ W ∧ a ∈ C} ↪ Fin q)
    (r : U → Fin q) (hr : InjectiveOnClique C U q r) :
    ∃ s : W → Fin q, InjectiveOnClique C W q s ∧
      ∀ x : {a : V // a ∈ U ∧ a ∈ W},
        s ⟨x.val, x.property.2⟩ = r ⟨x.val, x.property.1⟩ := by
  classical
  let A := {a : V // (a ∈ U ∧ a ∈ W) ∧ a ∈ C}
  let f : A → Fin q := fun x => j ⟨x.val, x.property.1.2, x.property.2⟩
  let g : A → Fin q := fun x => r ⟨x.val, x.property.1.1⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {a : V // a ∈ W ∧ a ∈ C} => z.val) (j.injective h))
  have hg : Function.Injective g := by
    intro x y h
    have he := hr (a₁ := ⟨x.val, x.property.1.1, x.property.2⟩)
      (a₂ := ⟨y.val, y.property.1.1, y.property.2⟩) h
    exact Subtype.ext
      (congrArg (fun z : {a : V // a ∈ U ∧ a ∈ C} => z.val) he)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let s : W → Fin q := fun x =>
    if hxC : x.val ∈ C then σ (j ⟨x.val, x.property, hxC⟩)
    else if hxU : x.val ∈ U then r ⟨x.val, hxU⟩ else ⟨0, hq⟩
  refine ⟨s, ?_, ?_⟩
  · intro x y h
    have he : σ (j x) = σ (j y) := by
      simpa only [s, dite_eq_left x.property.2, dite_eq_left y.property.2] using h
    exact j.injective (σ.injective he)
  · intro x
    by_cases hxC : x.val ∈ C
    · simpa only [s, dite_eq_left hxC, f, g] using
        hσ (⟨x.val, x.property, hxC⟩ : A)
    · simp only [s, dite_eq_right hxC, dite_eq_left x.property.1]

/-- A nonconformal clique obstructs global realization despite complete pairwise consistency.
The scope index type is arbitrary; only the variable carrier is required to be finite. -/
theorem nonconformal_clique_obstruction (E : Type u) (V : Type v) [Finite V]
    (S : E → Set V) (C : Finset V) (hC : 3 ≤ C.card)
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ∃ e, x ∈ S e ∧ y ∈ S e)
    (hproper : ∀ e, ¬ (↑C : Set V) ⊆ S e) :
    ∃ R : (e : E) → Finset (S e → Fin (C.card - 1)),
      (∀ e, (R e).Nonempty) ∧
      (∀ e f,
        (fun (r : S e → Fin (C.card - 1)) (x : {a : V // a ∈ S e ∧ a ∈ S f}) =>
          r ⟨x.val, x.property.1⟩) '' (R e : Set (S e → Fin (C.card - 1))) =
        (fun (r : S f → Fin (C.card - 1)) (x : {a : V // a ∈ S e ∧ a ∈ S f}) =>
          r ⟨x.val, x.property.2⟩) '' (R f : Set (S f → Fin (C.card - 1)))) ∧
      ¬ ∃ g : V → Fin (C.card - 1),
        ∀ e, (fun x : S e => g x.val) ∈ R e := by
  classical
  letI := Fintype.ofFinite V
  let q := C.card - 1
  have hq : 0 < q := by omega
  let R : (e : E) → Finset (S e → Fin q) := fun e => cliqueRows C (S e) q
  have mem_R (e : E) (r : S e → Fin q) : r ∈ R e ↔ InjectiveOnClique C (S e) q r := by
    simp only [R, cliqueRows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have extend (e f : E) (r : S e → Fin q) (hr : r ∈ R e) :
      ∃ s : S f → Fin q, s ∈ R f ∧
        ∀ x : {a : V // a ∈ S e ∧ a ∈ S f},
          s ⟨x.val, x.property.2⟩ = r ⟨x.val, x.property.1⟩ := by
    obtain ⟨j⟩ := scope_embedding C (S f) (hproper f)
    obtain ⟨s, hs, hsr⟩ := extend_overlap C (S e) (S f) q hq j r ((mem_R e r).mp hr)
    exact ⟨s, (mem_R f s).mpr hs, hsr⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · intro e
    obtain ⟨j⟩ := scope_embedding C (S e) (hproper e)
    let r : S e → Fin q := fun x =>
      if hx : x.val ∈ C then j ⟨x.val, x.property, hx⟩ else ⟨0, hq⟩
    refine ⟨r, (mem_R e r).mpr ?_⟩
    intro x y h
    exact j.injective (by simpa only [r, dite_eq_left x.property.2, dite_eq_left y.property.2] using h)
  · intro e f
    apply Set.Subset.antisymm
    · rintro t ⟨r, hr, rfl⟩
      obtain ⟨s, hs, hsr⟩ := extend e f r hr
      exact ⟨s, hs, funext hsr⟩
    · rintro t ⟨r, hr, rfl⟩
      obtain ⟨s, hs, hsr⟩ := extend f e r hr
      refine ⟨s, hs, ?_⟩
      funext x
      exact hsr ⟨x.val, x.property.2, x.property.1⟩
  · rintro ⟨g, hg⟩
    have hinj : Function.Injective (fun x : C => g x.val) := by
      intro x y hxy
      by_contra hne
      have hval : x.val ≠ y.val := fun he => hne (Subtype.ext he)
      obtain ⟨e, hxe, hye⟩ := hpair x.val x.property y.val y.property hval
      have he := (mem_R e _).mp (hg e)
      have h := he (a₁ := ⟨x.val, hxe, x.property⟩) (a₂ := ⟨y.val, hye, y.property⟩) hxy
      exact hne (Subtype.ext
        (congrArg (fun z : {a : V // a ∈ S e ∧ a ∈ C} => z.val) h))
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_coe, Fintype.card_fin] at hcard
    omega

end D5.S3.ConceptDynamics.Gluing.NonconformalCliqueObstruction
