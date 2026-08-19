/- GID: D5/S3/ObserverMemory/Knowledge/FiniteCapacity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/FiniteCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite knowledge dimension equals the number of realized readout classes. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-18):
   * Loogle and pinned-Mathlib searches returned exact hits
     `LinearMap.finrank_range_of_inj`, `Module.finrank_fintype_fun_eq_card`,
     `Fintype.card_le_of_surjective`, and `Function.FactorsThrough`; each is
     applied below.
   * A shaped Loogle query for the complete knowledge-space dimension formula
     returned no exact theorem. Repository search found the existing
     factorization-based knowledge predicate, but no dimension theorem. -/

namespace D5.S3.ObserverMemory.Knowledge.FiniteCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Pull a complex observable on the realized readout classes back to the world space. -/
def pullbackOnRange {X Y : Type*} (q : X -> Y) :
    (Set.range q -> ℂ) →ₗ[ℂ] (X -> ℂ) where
  toFun observable x := observable ⟨q x, Set.mem_range_self x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Complex-valued knowledge consists exactly of observables pulled back from realized readouts. -/
def KnowledgeSpace {X Y : Type*} (q : X -> Y) : Submodule ℂ (X -> ℂ) :=
  LinearMap.range (pullbackOnRange q)

private theorem pullback_on_range_injective {X Y : Type*} (q : X -> Y) :
    Function.Injective (pullbackOnRange q) := by
  intro first second heq
  funext observed
  obtain ⟨x, hx⟩ := observed.property
  have hobserved : (⟨q x, Set.mem_range_self x⟩ : Set.range q) = observed :=
    Subtype.ext hx
  have hvalue := congrFun heq x
  change first ⟨q x, Set.mem_range_self x⟩ =
    second ⟨q x, Set.mem_range_self x⟩ at hvalue
  rwa [← hobserved]

/-- Membership in the linear knowledge space is exactly constancy on every readout fiber. -/
theorem mem_knowledgeSpace_iff_factorsThrough {X Y : Type*}
    (q : X -> Y) (f : X -> ℂ) :
    f ∈ KnowledgeSpace q ↔ f.FactorsThrough q := by
  constructor
  · rintro ⟨observable, rfl⟩
    intro x y hxy
    change observable ⟨q x, Set.mem_range_self x⟩ =
      observable ⟨q y, Set.mem_range_self y⟩
    congr
  · intro hfactor
    let observable : Set.range q -> ℂ := fun observed =>
      Function.extend q f (fun _ => 0) observed.1
    refine ⟨observable, ?_⟩
    funext x
    exact hfactor.extend_apply (fun _ => 0) x

/-- The dimension of complex knowledge is the number of realized readout classes. -/
theorem knowledge_space_finrank {X Y : Type*} [Finite X] [Finite Y]
    (q : X -> Y) :
    Module.finrank ℂ (KnowledgeSpace q) = Nat.card (Set.range q) := by
  classical
  letI : Fintype (Set.range q) := Fintype.ofFinite (Set.range q)
  rw [KnowledgeSpace, LinearMap.finrank_range_of_inj (pullback_on_range_injective q),
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

private def rangeMap {X Y₀ Y₁ : Type*} (q₀ : X -> Y₀) (q₁ : X -> Y₁)
    (forget : Y₀ -> Y₁) (hfactor : q₁ = forget ∘ q₀) :
    Set.range q₀ -> Set.range q₁ := fun observed =>
  ⟨forget observed.1, by
    obtain ⟨x, hx⟩ := observed.property
    refine ⟨x, ?_⟩
    rw [hfactor, Function.comp_apply, hx]⟩

private theorem rangeMap_surjective {X Y₀ Y₁ : Type*}
    (q₀ : X -> Y₀) (q₁ : X -> Y₁) (forget : Y₀ -> Y₁)
    (hfactor : q₁ = forget ∘ q₀) :
    Function.Surjective (rangeMap q₀ q₁ forget hfactor) := by
  intro observed
  obtain ⟨x, hx⟩ := observed.property
  refine ⟨⟨q₀ x, Set.mem_range_self x⟩, ?_⟩
  apply Subtype.ext
  change forget (q₀ x) = observed.1
  calc
    forget (q₀ x) = q₁ x := by
      simpa only [Function.comp_apply] using congrFun hfactor x |>.symm
    _ = observed.1 := hx

/-- For finite world and readout types, both knowledge dimensions count realized classes.
Under a coarse factor readout, the later dimension cannot increase and the capacity loss is the
difference between the two realized-class counts. -/
theorem finite_knowledge_capacity
    {X Y₀ Y₁ : Type*} [Finite X] [Finite Y₀] [Finite Y₁]
    (q₀ : X -> Y₀) (q₁ : X -> Y₁) (forget : Y₀ -> Y₁)
    (hfactor : q₁ = forget ∘ q₀) :
    Module.finrank ℂ (KnowledgeSpace q₀) = Nat.card (Set.range q₀) ∧
      Module.finrank ℂ (KnowledgeSpace q₁) = Nat.card (Set.range q₁) ∧
      Module.finrank ℂ (KnowledgeSpace q₁) ≤ Module.finrank ℂ (KnowledgeSpace q₀) ∧
      Module.finrank ℂ (KnowledgeSpace q₀) - Module.finrank ℂ (KnowledgeSpace q₁) =
        Nat.card (Set.range q₀) - Nat.card (Set.range q₁) := by
  classical
  letI : Fintype (Set.range q₀) := Fintype.ofFinite (Set.range q₀)
  letI : Fintype (Set.range q₁) := Fintype.ofFinite (Set.range q₁)
  have hcapacity₀ := knowledge_space_finrank q₀
  have hcapacity₁ := knowledge_space_finrank q₁
  have hclasses : Fintype.card (Set.range q₁) ≤ Fintype.card (Set.range q₀) :=
    Fintype.card_le_of_surjective (rangeMap q₀ q₁ forget hfactor)
      (rangeMap_surjective q₀ q₁ forget hfactor)
  refine ⟨hcapacity₀, hcapacity₁, ?_, ?_⟩
  · simpa only [hcapacity₀, hcapacity₁, Nat.card_eq_fintype_card] using hclasses
  · rw [hcapacity₀, hcapacity₁]

/-- The finite hypotheses and the coarse-factor condition are jointly inhabited. -/
example :
    Module.finrank ℂ (KnowledgeSpace (id : Fin 2 -> Fin 2)) = 2 ∧
      Module.finrank ℂ (KnowledgeSpace (fun _ : Fin 2 => ())) = 1 ∧
      Module.finrank ℂ (KnowledgeSpace (fun _ : Fin 2 => ())) ≤
        Module.finrank ℂ (KnowledgeSpace (id : Fin 2 -> Fin 2)) ∧
      Module.finrank ℂ (KnowledgeSpace (id : Fin 2 -> Fin 2)) -
          Module.finrank ℂ (KnowledgeSpace (fun _ : Fin 2 => ())) = 2 - 1 := by
  simpa using finite_knowledge_capacity
    (id : Fin 2 -> Fin 2) (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) rfl

#print axioms mem_knowledgeSpace_iff_factorsThrough
#print axioms knowledge_space_finrank
#print axioms finite_knowledge_capacity

end

end D5.S3.ObserverMemory.Knowledge.FiniteCapacity
