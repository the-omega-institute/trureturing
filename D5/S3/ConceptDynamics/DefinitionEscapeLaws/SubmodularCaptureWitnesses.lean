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
  have laws := submodular_capture definitions q target (fun _ => 1) nu
    (by intro definition; norm_num) additive
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

/-- The constant-zero weight satisfies every ambient premise even though the
baseline residual is genuinely nonempty. This pins the absence of a global
strict-positivity premise from the source theorem. -/
theorem constant_zero_weight_is_admissible_witness :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let cost : Unit -> Real := fun _ => 0
    let nu : EscapeWeight (Bool × Bool) :=
      { mass := fun _ => 0
        empty_mass := rfl
        mass_nonnegative := fun _ => le_rfl }
    (defectRelation q target).Nonempty ∧
      (forall definition, 0 <= cost definition) ∧
      (forall left right : Set (Bool × Bool), Disjoint left right ->
        nu.mass (left ∪ right) = nu.mass left + nu.mass right) ∧
      ¬0 < nu.mass (defectRelation q target) := by
  dsimp only
  refine ⟨⟨(false, true), rfl, Bool.false_ne_true⟩, ?_, ?_, by norm_num⟩
  · intro definition
    norm_num
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

/-- C1's false neighbor denies the exact residual-mass formula. The first
conjunct of `submodular_capture` refutes that denial in every additive model. -/
theorem clause_one_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (S : Set I) (sourceDomainFinite : S.Finite) :
    ¬(residualEscapeMass S definitions q target nu ≠
      nu.mass (defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target)) := by
  intro denial
  exact denial ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).1 S sourceDomainFinite)

/-- C2's false neighbor denies the source definition `F(S) = M(empty)-M(S)`.
The second conjunct refutes that denial under the unchanged premises. -/
theorem clause_two_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (S : Set I) (sourceDomainFinite : S.Finite) :
    ¬(capturedEscapeMass S definitions q target nu ≠
      residualEscapeMass ∅ definitions q target nu -
        residualEscapeMass S definitions q target nu) := by
  intro denial
  exact denial ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.1 S sourceDomainFinite)

/-- C3's false neighbor denies the captured-union expansion. The third
conjunct refutes that denial for every selection and additive mass. -/
theorem clause_three_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (S : Set I) (sourceDomainFinite : S.Finite) :
    let captured := fun selection : Set I =>
      defectRelation q target ∩
        ⋃ definition ∈ selection,
          ({pair : X × X |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set (X × X))ᶜ
    ¬(capturedEscapeMass S definitions q target nu ≠ nu.mass (captured S)) := by
  dsimp only
  intro denial
  exact denial ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.1 S sourceDomainFinite)

/-- C4's false neighbor is strict decrease along an inclusion. Monotonicity
universally refutes this strict reverse inequality. -/
theorem clause_four_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    {A B : Set I} (aSourceDomainFinite : A.Finite)
    (bSourceDomainFinite : B.Finite) (subset : A ⊆ B) :
    ¬capturedEscapeMass B definitions q target nu <
      capturedEscapeMass A definitions q target nu := by
  exact not_lt_of_ge ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.1 aSourceDomainFinite
      bSourceDomainFinite subset)

/-- C5's false neighbor makes the four-term submodular inequality strictly
point in the opposite direction. Submodularity universally refutes it. -/
theorem clause_five_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (A B : Set I) (aSourceDomainFinite : A.Finite)
    (bSourceDomainFinite : B.Finite) :
    ¬capturedEscapeMass A definitions q target nu +
        capturedEscapeMass B definitions q target nu <
      capturedEscapeMass (A ∪ B) definitions q target nu +
        capturedEscapeMass (A ∩ B) definitions q target nu := by
  exact not_lt_of_ge ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.2.1 A B aSourceDomainFinite
      bSourceDomainFinite)

/-- C6's false neighbor asserts strictly increasing marginal capture while
retaining both inclusion and freshness. Diminishing returns refutes it in every
model satisfying the unchanged premises. -/
theorem clause_six_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    {A B : Set I} (definition : I) (bSourceDomainFinite : B.Finite)
    (subset : A ⊆ B)
    (fresh : definition ∉ B) :
    ¬capturedEscapeMass (A ∪ {definition}) definitions q target nu -
        capturedEscapeMass A definitions q target nu <
      capturedEscapeMass (B ∪ {definition}) definitions q target nu -
        capturedEscapeMass B definitions q target nu := by
  exact not_lt_of_ge ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.2.2.1 definition
      bSourceDomainFinite subset fresh)

/-- C7's false neighbor denies the residual-score/capture-score equivalence.
The algebraic rewrite refutes that denial for arbitrary costs, including zero. -/
theorem clause_seven_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (S : Set I) (next : I) (sourceDomainFinite : S.Finite) :
    let M := fun selection : Set I =>
      residualEscapeMass selection definitions q target nu
    let F := fun selection : Set I =>
      capturedEscapeMass selection definitions q target nu
    ¬(¬((forall definition,
        (M S - M (S ∪ {definition})) / cost definition <=
          (M S - M (S ∪ {next})) / cost next) <->
      (forall definition,
        (F (S ∪ {definition}) - F S) / cost definition <=
          (F (S ∪ {next}) - F S) / cost next))) := by
  dsimp only
  intro denial
  exact denial ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.2.2.2.1 S next
      sourceDomainFinite)

/-- C8's false neighbor flips only the conclusion's membership to
nonmembership. Under the unchanged theorem premises and blind-pair hypotheses,
that neighboring proposition is universally false for arbitrary, not merely
finite, pointwise selections. -/
theorem clause_eight_false_neighbor_witness
    {I X C Target : Type*} {V : I -> Type*}
    (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (cost : I -> Real) (nu : EscapeWeight (X × X))
    (cost_nonnegative : forall definition, 0 <= cost definition)
    (mass_additive : forall left right : Set (X × X), Disjoint left right ->
      nu.mass (left ∪ right) = nu.mass left + nu.mass right)
    (S : Set I) (pair : X × X)
    (baseline : pair ∈ defectRelation q target)
    (blind : forall definition,
      definitions definition pair.1 = definitions definition pair.2) :
    ¬(pair ∉ defectRelation
      (conceptJoin q
        (jointReadout (fun item : S => definitions item.1))) target) := by
  intro denial
  exact denial ((submodular_capture definitions q target cost nu
    cost_nonnegative mass_additive).2.2.2.2.2.2.2 S pair baseline blind)

/-- Every named witness is consumed at its complete statement: the quantitative
model, blind pair, premise attacks, admissible zero mass, and all eight false
neighbors. -/
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
     let cost : Unit -> Real := fun _ => 0
     let nu : EscapeWeight (Bool × Bool) :=
       { mass := fun _ => 0
         empty_mass := rfl
         mass_nonnegative := fun _ => le_rfl }
     (defectRelation q target).Nonempty ∧
       (forall definition, 0 <= cost definition) ∧
       (forall left right : Set (Bool × Bool), Disjoint left right ->
         nu.mass (left ∪ right) = nu.mass left + nu.mass right) ∧
       ¬0 < nu.mass (defectRelation q target)) ∧
    (∃ nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)),
      ¬marginalCaptureLaw (∅ : Set Bool) {false}
        (fun index => if index then
          (Prod.snd : Concept (Bool × Bool) Bool)
        else (Prod.fst : Concept (Bool × Bool) Bool))
        (fun _ : Bool × Bool => ()) id true nu) ∧
    (forall {I X C Target : Type*} {V : I -> Type*}
      (definitions : forall i, Concept X (V i))
      (q : Concept X C) (target : Concept X Target)
      (cost : I -> Real) (nu : EscapeWeight (X × X))
      (cost_nonnegative : forall definition, 0 <= cost definition)
      (mass_additive : forall left right : Set (X × X),
        Disjoint left right ->
          nu.mass (left ∪ right) = nu.mass left + nu.mass right),
      let M := fun S : Set I =>
        residualEscapeMass S definitions q target nu
      let F := fun S : Set I =>
        capturedEscapeMass S definitions q target nu
      let captured := fun S : Set I =>
        defectRelation q target ∩
          ⋃ definition ∈ S,
            ({pair : X × X |
              Setoid.ker (definitions definition) pair.1 pair.2} :
              Set (X × X))ᶜ
      (forall S, S.Finite ->
        ¬(M S ≠ nu.mass (defectRelation
          (conceptJoin q
            (jointReadout (fun item : S => definitions item.1))) target))) ∧
      (forall S, S.Finite -> ¬(F S ≠ M ∅ - M S)) ∧
      (forall S, S.Finite -> ¬(F S ≠ nu.mass (captured S))) ∧
      (forall {A B}, A.Finite -> B.Finite -> A ⊆ B -> ¬F B < F A) ∧
      (forall A B, A.Finite -> B.Finite ->
        ¬F A + F B < F (A ∪ B) + F (A ∩ B)) ∧
      (forall {A B} (definition : I), B.Finite -> A ⊆ B -> definition ∉ B ->
        ¬F (A ∪ {definition}) - F A <
          F (B ∪ {definition}) - F B) ∧
      (forall S next, S.Finite ->
        ¬(¬((forall definition,
            (M S - M (S ∪ {definition})) / cost definition <=
              (M S - M (S ∪ {next})) / cost next) <->
          (forall definition,
            (F (S ∪ {definition}) - F S) / cost definition <=
              (F (S ∪ {next}) - F S) / cost next))))) ∧
    (forall {I X C Target : Type*} {V : I -> Type*}
      (definitions : forall i, Concept X (V i))
      (q : Concept X C) (target : Concept X Target)
      (cost : I -> Real) (nu : EscapeWeight (X × X))
      (_cost_nonnegative : forall definition, 0 <= cost definition)
      (_mass_additive : forall left right : Set (X × X),
        Disjoint left right ->
          nu.mass (left ∪ right) = nu.mass left + nu.mass right)
      (S : Set I) (pair : X × X),
      pair ∈ defectRelation q target ->
      (forall definition,
        definitions definition pair.1 = definitions definition pair.2) ->
      ¬(pair ∉ defectRelation
        (conceptJoin q
          (jointReadout (fun item : S => definitions item.1))) target)) := by
  refine ⟨finite_capture_laws_nonvacuous,
    fixed_language_blind_pair_persists_witness,
    subset_premise_is_necessary_witness,
    constant_zero_weight_is_admissible_witness,
    finite_additivity_is_necessary_witness, ?_,
    clause_eight_false_neighbor_witness⟩
  intro I X C Target V definitions q target cost nu
    costNonnegative massAdditive
  dsimp only
  exact ⟨
    fun S sourceFinite => clause_one_false_neighbor_witness definitions q target
      cost nu costNonnegative massAdditive S sourceFinite,
    fun S sourceFinite => clause_two_false_neighbor_witness definitions q target
      cost nu costNonnegative massAdditive S sourceFinite,
    fun S sourceFinite => clause_three_false_neighbor_witness definitions q target
      cost nu costNonnegative massAdditive S sourceFinite,
    fun {_A _B} aFinite bFinite subset =>
      clause_four_false_neighbor_witness definitions q target cost nu
        costNonnegative massAdditive aFinite bFinite subset,
    fun A B aFinite bFinite => clause_five_false_neighbor_witness definitions q
      target cost nu costNonnegative massAdditive A B aFinite bFinite,
    fun {_A _B} definition bFinite subset fresh =>
      clause_six_false_neighbor_witness definitions q target cost nu
        costNonnegative massAdditive definition bFinite subset fresh,
    fun S next sourceFinite => clause_seven_false_neighbor_witness definitions q
      target cost nu costNonnegative massAdditive S next sourceFinite⟩

#print axioms submodular_capture_witnesses_nonvacuous

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses
