import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices

/-! Full source telescopes and actual dependent-family readouts; 
four-slot certificates remain unresolved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices

open _root_.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
open _root_.D5.S3.ConceptDynamics.InformationEscape
open scoped BigOperators

universe u v

/-- The complete universe-polymorphic source telescope is retained for this attempt. -/
abbrev massScope := type_of% (@repeated_colour_mass_le_outdegree.{u,v})
abbrev classesScope := type_of% (@exists_three_disjoint_classes.{u,v})
abbrev coreScope := type_of% (@deterministic_rainbow_choice_core.{u,v})

/-- All vertex and colour carriers and the finite vertex dictionary remain parameters. -/
abbrev massSignature : DependentFamily.Signature where
  Params := Σ V : Type u, Σ C : Type v, Fintype V
  State p := Digraph p.1 × (p.1 → p.1 → p.2.1) × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def massActual : DependentFamily.Realization massSignature.{u,v} :=
  DependentFamily.realize massSignature
    (fun _ p s => by
      letI : Fintype p.1 := p.2.2
      exact ∑ w : p.1, (repeated s.1 s.2.1 s.2.2 w).card)
    (fun e => nomatch e)

/-- The observed total mass is substituted into the entire original theorem statement. -/
def massArena : DependentFamily.Arena where
  signature := massSignature.{u,v}
  Law R := ∀ {V : Type u} {C : Type v} [f : Fintype V]
    (G : Digraph V) (c : V → V → C), OutProper G c → ∀ u : V,
      R.readout () ⟨V, C, f⟩ (G, c, u) ≤ (outNeighbors G u).card

theorem mass_source_bridge : massScope.{u,v} ↔ massArena.{u,v}.Law massActual.{u,v} := by
  constructor <;> intro h <;> exact @h

theorem mass_actual_positive : massArena.{u,v}.Law massActual :=
  mass_source_bridge.mp (@repeated_colour_mass_le_outdegree.{u,v})

/-- Explicitly unresolved: no family registration is claimed until intervention,
sensitivity, observational-dependence and source-selection evidence are supplied. -/
def massCertificate : Option (DependentFamily.Registration massArena.{u,v} massScope.{u,v}) := none


#print axioms mass_source_bridge

/-- The source class predicate with its only observation made explicit. -/
def observedClasses {V : Type u} {C : Type v} (A : Finset V)
    (support : V → Finset (V ⊕ C)) (T : Fin 3 → Finset V) : Prop :=
  (∀ i, T i ⊆ A) ∧
  (∀ x, x ∈ A ↔ ∃ i, x ∈ T i) ∧
  (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
  (∀ i, (T i : Set V).Pairwise (fun x y => Disjoint (support x) (support y))) ∧
  (∑ i : Fin 3, (T i).card) = A.card

abbrev classesSignature : DependentFamily.Signature where
  Params := (Type u) × (Type v)
  State p := Finset p.1 × (p.1 → p.2) × (p.1 → p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Finset (p.1 ⊕ p.2)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def classesActual : DependentFamily.Realization classesSignature.{u,v} :=
  DependentFamily.realize classesSignature
    (fun _ _ s => taggedSupport s.2.1 s.2.2) (fun e => nomatch e)

def classesArena : DependentFamily.Arena where
  signature := classesSignature.{u,v}
  Law R := ∀ {V : Type u} {C : Type v} (A : Finset V) (a b : V → C),
    Set.InjOn a A → Set.InjOn b A → ∃ T : Fin 3 → Finset V,
      observedClasses A (R.readout () (V, C) (A, a, b)) T

theorem classes_source_bridge : classesScope.{u,v} ↔ classesArena.{u,v}.Law classesActual.{u,v} := by
  constructor <;> intro h <;> exact @h

theorem classes_actual_positive : classesArena.{u,v}.Law classesActual :=
  classes_source_bridge.mp (@exists_three_disjoint_classes.{u,v})

def classesFamilyCertificate :
    Option (DependentFamily.Registration classesArena.{u,v} classesScope.{u,v}) := none

abbrev coreSignature : DependentFamily.Signature where
  Params := Σ V : Type u, Σ C : Type v, Fintype V
  State p := Digraph p.1 × (p.1 → p.1 → p.2.1) × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → p.1 → Finset (p.1 ⊕ p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def coreActual : DependentFamily.Realization coreSignature.{u,v} :=
  DependentFamily.realize coreSignature
    (fun _ _ s w => taggedSupport (s.2.1 s.2.2) (fun x => s.2.1 x w))
    (fun e => nomatch e)

def coreArena : DependentFamily.Arena where
  signature := coreSignature.{u,v}
  Law R := ∀ {V : Type u} {C : Type v} [f : Fintype V]
    (G : Digraph V) (c : V → V → C), OutProper G c → InProper G c →
    (∀ x, ¬ G.Adj x x) → ∀ ν : ℝ, 0 < ν → 0 < Fintype.card V → ∀ u : V,
      let n : ℝ := Fintype.card V
      let B := exceptions G c u (ν * n / 16)
      (B.card : ℝ) < 16 / ν ∧
      ∀ w, u ≠ w → w ∉ B → ∀ A : Finset V, A ⊆ twoStep G u w →
        ν * n / 4 ≤ (A.card : ℝ) →
        ∃ T : Fin 3 → Finset V,
          observedClasses (rainbow c u w A) (R.readout () ⟨V, C, f⟩ (G, c, u) w) T ∧
          3 * ν * n / 16 ≤ ((rainbow c u w A).card : ℝ) ∧
          (∀ x ∈ rainbow c u w A,
            G.Adj u x ∧ G.Adj x w ∧ u ≠ x ∧ x ≠ w ∧ u ≠ w ∧ c u x ≠ c x w ∧
              (R.readout () ⟨V, C, f⟩ (G, c, u) w x).card = 3)

theorem core_source_bridge : coreScope.{u,v} ↔ coreArena.{u,v}.Law coreActual.{u,v} := by
  constructor <;> intro h <;> exact @h

theorem core_actual_positive : coreArena.{u,v}.Law coreActual :=
  core_source_bridge.mp (@deterministic_rainbow_choice_core.{u,v})

def coreFamilyCertificate :
    Option (DependentFamily.Registration coreArena.{u,v} coreScope.{u,v}) := none

#print axioms classes_source_bridge
#print axioms core_source_bridge

end Reg.D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
