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

/-- C1's false neighbor ignores the selected definition. The displayed edge
lies in the baseline residual and is removed by the selected first coordinate,
so the two residual sets cannot be equal. -/
theorem clause_one_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let edge := ((false, false), (true, false))
    let selectedResidual := defectRelation
      (conceptJoin q
        (jointReadout (fun item : ({false} : Set Bool) => definitions item.1)))
      target
    edge ∈ defectRelation q target ∧
      edge ∉ selectedResidual ∧
      selectedResidual ≠ defectRelation q target := by
  classical
  dsimp only
  have baseline :
      ((false, false), (true, false)) ∈
        defectRelation (fun _ : Bool × Bool => ()) id := by
    exact ⟨rfl, by decide⟩
  have removed :
      ((false, false), (true, false)) ∉
        defectRelation
          (conceptJoin (fun _ : Bool × Bool => ())
            (jointReadout
              (fun item : ({false} : Set Bool) =>
                if item.1 then Prod.snd else Prod.fst))) id := by
    rintro ⟨joined, _targetDifferent⟩
    have sameReadout := congrArg Prod.snd joined
    let item : ({false} : Set Bool) := ⟨false, by simp⟩
    have sameFirst := congrFun sameReadout item
    norm_num [conceptJoin, jointReadout, item] at sameFirst
  refine ⟨baseline, removed, ?_⟩
  intro residualUnchanged
  exact removed (residualUnchanged.symm ▸ baseline)

/-- C2's false neighbor reverses the defining subtraction. Nonconstant
residual mass makes the wrong direction disagree with `F = M(empty) - M`. -/
theorem clause_two_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
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
    let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
    let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
    M ∅ ≠ M {false} ∧
      F {false} = M ∅ - M {false} ∧
      ¬F {false} = M {false} - M ∅ := by
  classical
  dsimp only
  let definitions : Bool -> Concept (Bool × Bool) Bool :=
    fun index => if index then Prod.snd else Prod.fst
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
  let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
  let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
  change M ∅ ≠ M {false} ∧
    F {false} = M ∅ - M {false} ∧
    ¬F {false} = M {false} - M ∅
  have values : M ∅ = 3 ∧ M {false} = 1 ∧ F {false} = 2 := by
    simpa [M, F, definitions, q, target, nu, firstEdge, secondEdge,
      overlapEdge] using
        ⟨finite_capture_values_witness.1,
          finite_capture_values_witness.2.1,
          finite_capture_values_witness.2.2.2.2.1⟩
  rw [values.1, values.2.1, values.2.2]
  norm_num

/-- C3's false neighbor replaces the captured union by an intersection.
The first-coordinate edge is cut by one selected definition but not the other,
so pointwise intersection cannot replace pointwise union. -/
theorem clause_three_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let firstEdge := ((false, false), (true, false))
    let capturedUnion := fun S : Set Bool =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    let capturedIntersection := fun S : Set Bool =>
      defectRelation q target ∩
        ⋂ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    firstEdge ∈ capturedUnion Set.univ ∧
      firstEdge ∉ capturedIntersection Set.univ ∧
      capturedIntersection Set.univ ≠ capturedUnion Set.univ := by
  classical
  dsimp only
  have capturedByUnion :
      ((false, false), (true, false)) ∈
        defectRelation (fun _ : Bool × Bool => ()) id ∩
          ⋃ definition ∈ (Set.univ : Set Bool),
            ({pair : (Bool × Bool) × (Bool × Bool) |
              Setoid.ker (if definition then Prod.snd else Prod.fst)
                pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ := by
    simp [defectRelation, Setoid.ker_def]
  have notCapturedByIntersection :
      ((false, false), (true, false)) ∉
        defectRelation (fun _ : Bool × Bool => ()) id ∩
          ⋂ definition ∈ (Set.univ : Set Bool),
            ({pair : (Bool × Bool) × (Bool × Bool) |
              Setoid.ker (if definition then Prod.snd else Prod.fst)
                pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ := by
    simp [defectRelation, Setoid.ker_def]
  refine ⟨capturedByUnion, notCapturedByIntersection, ?_⟩
  intro equalSets
  exact notCapturedByIntersection (equalSets ▸ capturedByUnion)

/-- C4's false neighbor reverses the structural inclusion of captured sets.
It fails before any mass is evaluated, including for a zero-mass weight. -/
theorem clause_four_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let firstEdge := ((false, false), (true, false))
    let captured := fun S : Set Bool =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    firstEdge ∈ captured {false} ∧
      firstEdge ∉ captured ∅ ∧
      ¬captured {false} ⊆ captured ∅ := by
  classical
  dsimp only
  have capturedBySelection :
      ((false, false), (true, false)) ∈
        defectRelation (fun _ : Bool × Bool => ()) id ∩
          ⋃ definition ∈ ({false} : Set Bool),
            ({pair : (Bool × Bool) × (Bool × Bool) |
              Setoid.ker (if definition then Prod.snd else Prod.fst)
                pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ := by
    simp [defectRelation, Setoid.ker_def]
  have notCapturedByEmpty :
      ((false, false), (true, false)) ∉
        defectRelation (fun _ : Bool × Bool => ()) id ∩
          ⋃ definition ∈ (∅ : Set Bool),
            ({pair : (Bool × Bool) × (Bool × Bool) |
              Setoid.ker (if definition then Prod.snd else Prod.fst)
                pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ := by
    simp
  refine ⟨capturedBySelection, notCapturedByEmpty, ?_⟩
  intro reverseSubset
  exact notCapturedByEmpty (reverseSubset capturedBySelection)

/-- C5's false neighbor distributes capture through index intersection as an
equality. Separate singleton definitions can both cut the same edge even when
their index intersection is empty. -/
theorem clause_five_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let overlapEdge := ((false, false), (true, true))
    let captured := fun S : Set Bool =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    overlapEdge ∈ captured {false} ∩ captured {true} ∧
      overlapEdge ∉ captured ({false} ∩ {true}) ∧
      captured ({false} ∩ {true}) ≠ captured {false} ∩ captured {true} := by
  classical
  dsimp only
  have capturedByBoth :
      ((false, false), (true, true)) ∈
        (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ ({false} : Set Bool),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) ∩
          (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ ({true} : Set Bool),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) := by
    simp [defectRelation, Setoid.ker_def]
  have notCapturedByIntersection :
      ((false, false), (true, true)) ∉
        defectRelation (fun _ : Bool × Bool => ()) id ∩
          ⋃ definition ∈ (({false} : Set Bool) ∩ {true}),
            ({pair : (Bool × Bool) × (Bool × Bool) |
              Setoid.ker (if definition then Prod.snd else Prod.fst)
                pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ := by
    simp
  refine ⟨capturedByBoth, notCapturedByIntersection, ?_⟩
  intro equalSets
  exact notCapturedByIntersection (equalSets.symm ▸ capturedByBoth)

/-- C6's false neighbor reverses inclusion between newly captured edge sets.
The overlap edge is new over the empty selection but no longer new after the
first coordinate has already been selected. -/
theorem clause_six_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
    let q : Concept (Bool × Bool) Unit := fun _ => ()
    let target : Concept (Bool × Bool) (Bool × Bool) := id
    let overlapEdge := ((false, false), (true, true))
    let captured := fun S : Set Bool =>
      defectRelation q target ∩
        ⋃ definition ∈ S,
          ({pair : (Bool × Bool) × (Bool × Bool) |
            Setoid.ker (definitions definition) pair.1 pair.2} :
            Set ((Bool × Bool) × (Bool × Bool)))ᶜ
    let newlyCaptured := fun S : Set Bool =>
      captured (S ∪ {true}) \ captured S
    overlapEdge ∈ newlyCaptured ∅ ∧
      overlapEdge ∉ newlyCaptured {false} ∧
      ¬newlyCaptured ∅ ⊆ newlyCaptured {false} := by
  classical
  dsimp only
  have newOverEmpty :
      ((false, false), (true, true)) ∈
        (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ ((∅ : Set Bool) ∪ {true}),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) \
          (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ (∅ : Set Bool),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) := by
    simp [defectRelation, Setoid.ker_def]
  have notNewOverFirst :
      ((false, false), (true, true)) ∉
        (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ (({false} : Set Bool) ∪ {true}),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) \
          (defectRelation (fun _ : Bool × Bool => ()) id ∩
            ⋃ definition ∈ ({false} : Set Bool),
              ({pair : (Bool × Bool) × (Bool × Bool) |
                Setoid.ker (if definition then Prod.snd else Prod.fst)
                  pair.1 pair.2} : Set ((Bool × Bool) × (Bool × Bool)))ᶜ) := by
    simp [defectRelation, Setoid.ker_def]
  refine ⟨newOverEmpty, notNewOverFirst, ?_⟩
  intro reverseSubset
  exact notNewOverFirst (reverseSubset newOverEmpty)

/-- C7's supporting algebraic rewrite is pinned against three structural
miswirings: moving the denominator to the chosen candidate, changing the
chosen candidate between the two predicates, and treating zero cost as if the
rewrite failed. The nonconstant cost prevents constant-denominator masking. -/
theorem clause_seven_false_neighbor_witness :
    let definitions : Bool -> Concept (Bool × Bool) Bool :=
      fun index => if index then Prod.snd else Prod.fst
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
    let cost : Bool -> Real := fun index => if index then 2 else 1
    let zeroCost : Bool -> Real := fun index => if index then 0 else 1
    let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
    let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
    let residualScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
      forall definition,
        (M ∅ - M {definition}) / candidateCost definition ≤
          (M ∅ - M {next}) / candidateCost next
    let captureScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
      forall definition,
        (F {definition} - F ∅) / candidateCost definition ≤
          (F {next} - F ∅) / candidateCost next
    let wrongDenominator := fun (candidateCost : Bool -> Real) (next : Bool) =>
      forall definition,
        (F {definition} - F ∅) / candidateCost next ≤
          (F {next} - F ∅) / candidateCost next
    (residualScore cost true ↔ captureScore cost true) ∧
      ¬(residualScore cost true ↔ wrongDenominator cost true) ∧
      ¬(residualScore cost false ↔ captureScore cost true) ∧
      zeroCost true = 0 ∧
      ¬residualScore zeroCost true ∧
      ¬captureScore zeroCost true ∧
      (residualScore zeroCost true ↔ captureScore zeroCost true) := by
  classical
  dsimp only
  let definitions : Bool -> Concept (Bool × Bool) Bool :=
    fun index => if index then Prod.snd else Prod.fst
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
  let cost : Bool -> Real := fun index => if index then 2 else 1
  let zeroCost : Bool -> Real := fun index => if index then 0 else 1
  let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
  let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
  let residualScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
    forall definition,
      (M ∅ - M {definition}) / candidateCost definition ≤
        (M ∅ - M {next}) / candidateCost next
  let captureScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
    forall definition,
      (F {definition} - F ∅) / candidateCost definition ≤
        (F {next} - F ∅) / candidateCost next
  let wrongDenominator := fun (candidateCost : Bool -> Real) (next : Bool) =>
    forall definition,
      (F {definition} - F ∅) / candidateCost next ≤
        (F {next} - F ∅) / candidateCost next
  change (residualScore cost true ↔ captureScore cost true) ∧
    ¬(residualScore cost true ↔ wrongDenominator cost true) ∧
    ¬(residualScore cost false ↔ captureScore cost true) ∧
    zeroCost true = 0 ∧
    ¬residualScore zeroCost true ∧
    ¬captureScore zeroCost true ∧
    (residualScore zeroCost true ↔ captureScore zeroCost true)
  have values :
      M ∅ = 3 ∧ M {false} = 1 ∧ M {true} = 1 ∧
        F ∅ = 0 ∧ F {false} = 2 ∧ F {true} = 2 := by
    have allValues := finite_capture_values_witness
    refine ⟨allValues.1, allValues.2.1, allValues.2.2.1, ?_,
      allValues.2.2.2.2.1, allValues.2.2.2.2.2.1⟩
    simp [F, capturedEscapeMass]
  simp only [residualScore, captureScore, wrongDenominator, Bool.forall_bool]
  rw [values.1, values.2.1, values.2.2.1, values.2.2.2.1,
    values.2.2.2.2.1, values.2.2.2.2.2]
  norm_num [cost, zeroCost]

theorem clause_eight_false_neighbor_witness :
    let blindDefinitions : Unit -> Concept Bool Unit := fun _ _ => ()
    let blindQ : Concept Bool Unit := fun _ => ()
    let blindTarget : Concept Bool Bool := id
    (false, true) ∈ defectRelation
      (conceptJoin blindQ
        (jointReadout
          (fun item : (Set.univ : Set Unit) => blindDefinitions item.1)))
      blindTarget :=
  (fixed_language_blind_pair_persists_witness (Set.univ : Set Unit)).2.2

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
    (let definitions : Bool -> Concept (Bool × Bool) Bool :=
       fun index => if index then Prod.snd else Prod.fst
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
     let M := fun S : Set Bool => residualEscapeMass S definitions q target nu
     let F := fun S : Set Bool => capturedEscapeMass S definitions q target nu
     let captured := fun S : Set Bool =>
       defectRelation q target ∩
         ⋃ definition ∈ S,
           ({pair : (Bool × Bool) × (Bool × Bool) |
             Setoid.ker (definitions definition) pair.1 pair.2} :
             Set ((Bool × Bool) × (Bool × Bool)))ᶜ
     let capturedIntersection := fun S : Set Bool =>
       defectRelation q target ∩
         ⋂ definition ∈ S,
           ({pair : (Bool × Bool) × (Bool × Bool) |
             Setoid.ker (definitions definition) pair.1 pair.2} :
             Set ((Bool × Bool) × (Bool × Bool)))ᶜ
     let selectedResidual := defectRelation
       (conceptJoin q
         (jointReadout (fun item : ({false} : Set Bool) => definitions item.1)))
       target
     let newlyCaptured := fun S : Set Bool =>
       captured (S ∪ {true}) \ captured S
     let cost : Bool -> Real := fun index => if index then 2 else 1
     let zeroCost : Bool -> Real := fun index => if index then 0 else 1
     let residualScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
       forall definition,
         (M ∅ - M {definition}) / candidateCost definition <=
           (M ∅ - M {next}) / candidateCost next
     let captureScore := fun (candidateCost : Bool -> Real) (next : Bool) =>
       forall definition,
         (F {definition} - F ∅) / candidateCost definition <=
           (F {next} - F ∅) / candidateCost next
     let wrongDenominator := fun (candidateCost : Bool -> Real) (next : Bool) =>
       forall definition,
         (F {definition} - F ∅) / candidateCost next <=
           (F {next} - F ∅) / candidateCost next
     (firstEdge ∈ defectRelation q target ∧
       firstEdge ∉ selectedResidual ∧
       selectedResidual ≠ defectRelation q target) ∧
     (M ∅ ≠ M {false} ∧
       F {false} = M ∅ - M {false} ∧
       ¬F {false} = M {false} - M ∅) ∧
     (firstEdge ∈ captured Set.univ ∧
       firstEdge ∉ capturedIntersection Set.univ ∧
       capturedIntersection Set.univ ≠ captured Set.univ) ∧
     (firstEdge ∈ captured {false} ∧
       firstEdge ∉ captured ∅ ∧
       ¬captured {false} ⊆ captured ∅) ∧
     (overlapEdge ∈ captured {false} ∩ captured {true} ∧
       overlapEdge ∉ captured ({false} ∩ {true}) ∧
       captured ({false} ∩ {true}) ≠ captured {false} ∩ captured {true}) ∧
     (overlapEdge ∈ newlyCaptured ∅ ∧
       overlapEdge ∉ newlyCaptured {false} ∧
       ¬newlyCaptured ∅ ⊆ newlyCaptured {false}) ∧
     ((residualScore cost true <-> captureScore cost true) ∧
       ¬(residualScore cost true <-> wrongDenominator cost true) ∧
       ¬(residualScore cost false <-> captureScore cost true) ∧
       zeroCost true = 0 ∧
       ¬residualScore zeroCost true ∧
       ¬captureScore zeroCost true ∧
       (residualScore zeroCost true <-> captureScore zeroCost true)) ∧
     (let blindDefinitions : Unit -> Concept Bool Unit := fun _ _ => ()
      let blindQ : Concept Bool Unit := fun _ => ()
      let blindTarget : Concept Bool Bool := id
      (false, true) ∈ defectRelation
        (conceptJoin blindQ
          (jointReadout
            (fun item : (Set.univ : Set Unit) => blindDefinitions item.1)))
        blindTarget)) := by
  exact ⟨finite_capture_laws_nonvacuous,
    fixed_language_blind_pair_persists_witness,
    subset_premise_is_necessary_witness,
    constant_zero_weight_is_admissible_witness,
    finite_additivity_is_necessary_witness,
    ⟨clause_one_false_neighbor_witness,
      clause_two_false_neighbor_witness,
      clause_three_false_neighbor_witness,
      clause_four_false_neighbor_witness,
      clause_five_false_neighbor_witness,
      clause_six_false_neighbor_witness,
      clause_seven_false_neighbor_witness,
      clause_eight_false_neighbor_witness⟩⟩

#print axioms submodular_capture_witnesses_nonvacuous

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SubmodularCaptureWitnesses
