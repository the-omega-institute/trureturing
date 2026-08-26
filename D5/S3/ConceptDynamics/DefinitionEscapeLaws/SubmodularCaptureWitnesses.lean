/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/SubmodularCaptureWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Named witnesses pin all eight capture clauses and the three required premise attacks. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCapture

/- Library-search audit trail (2026-08-26):
   * Shape search `rg -n 'Set \(X × X\)|Set \(.*×.*\)'
     D5/S3/ConceptDynamics --glob '*.lean'` found `defectRelation`,
     `conceptKernel`, and `jointKernel`. This witness module imports and uses
     the canonical declarations; it defines no relation, residual, kernel,
     readout, union, intersection, weight structure, or capture function.
   * Synonym searches `rg -n -i 'witness|counterexample|nonvacuous|premise|
     subset|constant zero|blind pair|attack|正见证|反侧见证|空合取项'
     D5 Blueprint` found the neighboring witness-consumer pattern in
     `DirectlyProvableLawWitnesses` and the canonical weak-weight attack
     `marginal_capture_law_not_implied_by_escape_weight`. The latter is
     consumed below rather than restated under another mathematical name.
   * Neighbor inspection `ls D5/S3/ConceptDynamics/DefinitionEscapeLaws` and
     `git grep -n -E '^def |^  def |^structure |^  structure ' --
     D5/S3/ConceptDynamics | head -60` found no witness package for section
     4.4. This file therefore adds named propositions and one fail-closed
     consumer, but no domain vocabulary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCapture
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A baseline defect pair invisible to every constant candidate remains a
defect after any fixed-language selection. The proof consumes clause eight of
`submodular_capture`. -/
theorem fixed_language_blind_pair_persists_witness :
    let definitions : Unit -> Concept Bool Unit := fun _ _ => ()
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    forall S : Set Unit,
      (false, true) ∈ defectRelation q target ∧
      (forall definition,
        definitions definition false = definitions definition true) ∧
      (false, true) ∈ defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target := by
  classical
  dsimp only
  let definitions : Unit -> Concept Bool Unit := fun _ _ => ()
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  let edge : Bool × Bool := (false, true)
  let nu : EscapeWeight (Bool × Bool) :=
    { mass := fun set =>
        (@ite Real (edge ∈ set) (Classical.propDecidable _) 1 0)
      empty_mass := by simp
      mass_nonnegative := by intro set; split_ifs <;> norm_num }
  have additive : forall left right : Set (Bool × Bool), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right := by
    intro left right disjoint
    have notBoth : ¬(edge ∈ left ∧ edge ∈ right) := by
      rintro ⟨inLeft, inRight⟩
      exact Set.disjoint_left.1 disjoint inLeft inRight
    dsimp only [nu]
    by_cases inLeft : edge ∈ left <;> by_cases inRight : edge ∈ right <;>
      simp_all [Set.mem_union]
  have positive : 0 < nu.mass (defectRelation q target) := by
    norm_num [nu, edge, q, target, defectRelation]
  have laws := submodular_capture definitions q target (fun _ => 1) nu
    positive additive
  intro S
  have baseline : edge ∈ defectRelation q target := by
    exact ⟨rfl, Bool.false_ne_true⟩
  have blind : forall definition,
      definitions definition edge.1 = definitions definition edge.2 := by
    intro definition
    rfl
  exact ⟨baseline, blind,
    laws.2.2.2.2.2.2.2 S edge baseline blind⟩

/-- If the inclusion premise is removed, the required marginal direction is
false in the same three-edge source model: the larger set is deliberately put
on the left, while the candidate remains absent from the right-hand set. -/
theorem subset_premise_is_necessary_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then
        (Prod.snd : Concept (Bool × Bool) Bool)
      else (Prod.fst : Concept (Bool × Bool) Bool)
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let firstEdge := ((false, false), (true, false))
    let secondEdge := ((false, false), (false, true))
    let overlapEdge := ((false, false), (true, true))
    let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
      { mass := fun set =>
          (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
          (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
        empty_mass := by simp
        mass_nonnegative := by intro set; split_ifs <;> norm_num }
    let F := fun S : Set Bool =>
      capturedEscapeMass S definitions q target nu
    ¬({false} : Set Bool) ⊆ ∅ ∧
      true ∉ (∅ : Set Bool) ∧
      ¬(F ({false} ∪ {true}) - F {false} >=
        F ((∅ : Set Bool) ∪ {true}) - F ∅) := by
  classical
  dsimp only
  let definitions : Bool -> Concept (Bool × Bool) Bool :=
    fun index => if index then
      (Prod.snd : Concept (Bool × Bool) Bool)
    else (Prod.fst : Concept (Bool × Bool) Bool)
  let q : Concept (Bool × Bool) Unit := fun _ => ()
  let target : Concept (Bool × Bool) (Bool × Bool) := id
  let firstEdge := ((false, false), (true, false))
  let secondEdge := ((false, false), (false, true))
  let overlapEdge := ((false, false), (true, true))
  let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
    { mass := fun set =>
        (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
        (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
      empty_mass := by simp
      mass_nonnegative := by intro set; split_ifs <;> norm_num }
  let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
  have values :
      F {false} = 2 ∧ F {true} = 2 ∧ F Set.univ = 3 := by
    simpa [F, definitions, q, target, nu, firstEdge, secondEdge,
      overlapEdge] using
        finite_capture_values_witness.2.2.2.2
  have unionEq : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext item
    cases item <;> simp
  have emptyCapture : F ∅ = 0 := by
    simp [F, capturedEscapeMass]
  change ¬({false} : Set Bool) ⊆ ∅ ∧
    true ∉ (∅ : Set Bool) ∧
    ¬(F ({false} ∪ {true}) - F {false} >=
      F ((∅ : Set Bool) ∪ {true}) - F ∅)
  refine ⟨?_, by simp, ?_⟩
  · intro subset
    exact (by simpa using subset (by simp : false ∈ ({false} : Set Bool)))
  · rw [unionEq, Set.empty_union, emptyCapture, values.1, values.2.1,
      values.2.2]
    norm_num

/-- Finite additivity does not itself exclude the constant-zero weight. The
source's nondegeneracy premise rejects it even though the baseline residual is
genuinely nonempty. -/
theorem constant_zero_weight_is_rejected_witness :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let nu : EscapeWeight (Bool × Bool) :=
      { mass := fun _ => 0
        empty_mass := rfl
        mass_nonnegative := fun _ => le_rfl }
    (defectRelation q target).Nonempty ∧
      (forall left right : Set (Bool × Bool), Disjoint left right ->
        nu.mass (left ∪ right) = nu.mass left + nu.mass right) ∧
      ¬0 < nu.mass (defectRelation q target) := by
  dsimp only
  refine ⟨⟨(false, true), rfl, Bool.false_ne_true⟩, ?_, by norm_num⟩
  intro left right disjoint
  norm_num

/-- The weak `EscapeWeight` interface alone does not force diminishing
capture. This named witness directly reuses the canonical countermodel. -/
theorem finite_additivity_is_necessary_witness :
    ∃ nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)),
      ¬marginalCaptureLaw (∅ : Set Bool) {false}
        (fun index => if index then
          (Prod.snd : Concept (Bool × Bool) Bool)
        else (Prod.fst : Concept (Bool × Bool) Bool))
        (fun _ : Bool × Bool => ()) id true nu :=
  marginal_capture_law_not_implied_by_escape_weight

/-- Every named witness is consumed at its complete statement. The first
conjunct is the seven-clause quantitative model; the second projects the blind
boundary from clause eight; the final three conjuncts are the inclusion,
nondegeneracy, and additivity attacks. -/
theorem submodular_capture_witnesses_nonvacuous :
    (let definitions : Bool -> Concept (Bool × Bool) Bool :=
       fun index => if index then
         (Prod.snd : Concept (Bool × Bool) Bool)
       else (Prod.fst : Concept (Bool × Bool) Bool)
     let q : Concept (Bool × Bool) Unit := fun _ => ()
     let target : Concept (Bool × Bool) (Bool × Bool) := id
     let firstEdge := ((false, false), (true, false))
     let secondEdge := ((false, false), (false, true))
     let overlapEdge := ((false, false), (true, true))
     let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
       { mass := fun set =>
           (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
         empty_mass := by simp
         mass_nonnegative := by intro set; split_ifs <;> norm_num }
     let cost : Bool -> Real := fun _ => 1
     let M := fun S : Set Bool =>
       residualEscapeMass S definitions q target nu
     let F := fun S : Set Bool =>
       capturedEscapeMass S definitions q target nu
     let captured := fun S : Set Bool =>
       defectRelation q target ∩
         ⋃ definition ∈ S,
           ({pair : (Bool × Bool) × (Bool × Bool) |
             Setoid.ker (definitions definition) pair.1 pair.2} :
             Set ((Bool × Bool) × (Bool × Bool)))ᶜ
     (M ∅ = nu.mass (defectRelation
       (conceptJoin q
         (jointReadout (fun item : (∅ : Set Bool) => definitions item.1)))
       target) ∧ 0 < M ∅ ∧ M ∅ = 3) ∧
     (F {false} = M ∅ - M {false} ∧ F {false} = 2) ∧
     (F {false} = nu.mass (captured {false}) ∧
       nu.mass (captured {false}) = 2) ∧
     (F ∅ <= F {false} ∧ F ∅ < F {false}) ∧
     (F ({false} ∪ {true}) + F ({false} ∩ {true}) <=
         F {false} + F {true} ∧
       F ({false} ∪ {true}) + F ({false} ∩ {true}) <
         F {false} + F {true}) ∧
     (F ((∅ : Set Bool) ∪ {true}) - F ∅ >=
         F ({false} ∪ {true}) - F {false} ∧
       F ((∅ : Set Bool) ∪ {true}) - F ∅ >
         F ({false} ∪ {true}) - F {false}) ∧
     ((forall definition,
         (M ∅ - M (∅ ∪ {definition})) / cost definition <=
           (M ∅ - M (∅ ∪ {false})) / cost false) <->
       (forall definition,
         (F (∅ ∪ {definition}) - F ∅) / cost definition <=
           (F (∅ ∪ {false}) - F ∅) / cost false))) ∧
    (let definitions : Unit -> Concept Bool Unit := fun _ _ => ()
     let q : Concept Bool Unit := fun _ => ()
     let target : Concept Bool Bool := id
     forall S : Set Unit,
       (false, true) ∈ defectRelation q target ∧
       (forall definition,
         definitions definition false = definitions definition true) ∧
       (false, true) ∈ defectRelation
         (conceptJoin q
           (jointReadout (fun item : S => definitions item.1))) target) ∧
    (let definitions : Bool -> Concept (Bool × Bool) Bool :=
       fun index => if index then
         (Prod.snd : Concept (Bool × Bool) Bool)
       else (Prod.fst : Concept (Bool × Bool) Bool)
     let q : Concept (Bool × Bool) Unit := fun _ => ()
     let target : Concept (Bool × Bool) (Bool × Bool) := id
     let firstEdge := ((false, false), (true, false))
     let secondEdge := ((false, false), (false, true))
     let overlapEdge := ((false, false), (true, true))
     let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
       { mass := fun set =>
           (@ite Real (firstEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (secondEdge ∈ set) (Classical.propDecidable _) 1 0) +
           (@ite Real (overlapEdge ∈ set) (Classical.propDecidable _) 1 0)
         empty_mass := by simp
         mass_nonnegative := by intro set; split_ifs <;> norm_num }
     let F := fun S : Set Bool =>
       capturedEscapeMass S definitions q target nu
     ¬({false} : Set Bool) ⊆ ∅ ∧
       true ∉ (∅ : Set Bool) ∧
       ¬(F ({false} ∪ {true}) - F {false} >=
         F ((∅ : Set Bool) ∪ {true}) - F ∅)) ∧
    (let q : Concept Bool Unit := fun _ => ()
     let target : Concept Bool Bool := id
     let nu : EscapeWeight (Bool × Bool) :=
       { mass := fun _ => 0
         empty_mass := rfl
         mass_nonnegative := fun _ => le_rfl }
     (defectRelation q target).Nonempty ∧
       (forall left right : Set (Bool × Bool), Disjoint left right ->
         nu.mass (left ∪ right) = nu.mass left + nu.mass right) ∧
       ¬0 < nu.mass (defectRelation q target)) ∧
    (∃ nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)),
      ¬marginalCaptureLaw (∅ : Set Bool) {false}
        (fun index => if index then
          (Prod.snd : Concept (Bool × Bool) Bool)
        else (Prod.fst : Concept (Bool × Bool) Bool))
        (fun _ : Bool × Bool => ()) id true nu) := by
  exact ⟨finite_capture_laws_nonvacuous,
    fixed_language_blind_pair_persists_witness,
    subset_premise_is_necessary_witness,
    constant_zero_weight_is_rejected_witness,
    finite_additivity_is_necessary_witness⟩

#print axioms submodular_capture_witnesses_nonvacuous

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses
