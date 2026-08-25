/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLawWitnesses
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLawWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ten named witnesses make all eight packaged DECT laws mechanically nonvacuous. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLaws

/- Library-search audit trail (2026-08-25):
   * Shape searches `rg -n 'Set \(X × X\)' D5/S3/ConceptDynamics` and
     `rg -n '⋂ ' D5/S3/ConceptDynamics` found the canonical `defectRelation`,
     `jointKernel`, and the dependent residual already imported from
     `DirectlyProvableLaws`; this witness-only module introduces no relation,
     residual, kernel, readout, family, union, or intersection definition.
   * Synonym searches for witness/example/counterexample, nonvacuous/nonvacuity,
     guard/presence consumer, and 正见证/反侧见证/非空洞/存在性消费者 found
     adjacent named witnesses such as `strict_growth_witness` and
     `projection_configuration_is_nonvacuous`, but no existing package that
     consumes the ten DECT witnesses or projects all eight conjuncts.
   * `ls D5/S3/ConceptDynamics/DefinitionEscapeLaws`,
     `ls D5/S3/ConceptDynamics/DefinitionEscape`, and
     `git grep -n '^def \|^  def ' -- D5/S3/ConceptDynamics | head -60`
     established the neighboring vocabulary. The only prior module in this
     bucket is `DirectlyProvableLaws`; its three dependent-family definitions
     and eight-conjunct theorem are imported rather than restated.
   * `grep -nE '^(theorem|def|structure|abbrev)'
     D5/S3/ConceptDynamics/DefinitionEscapeLaws/DirectlyProvableLaws.lean`
     found the three dependent definitions, four bridge/obstruction theorems,
     `directly_provable_laws`, and the nine named false-neighbor declarations.
     None names or consumes the positive witnesses introduced here. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLawWitnesses

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLaws
open MeasureTheory

/-- Clause 1 is exercised on a genuinely nonempty joined residual. -/
theorem clause1_nonvacuity_witness :
    (defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) =
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
        {pair : Bool × Bool |
          Setoid.ker (fun _ : Bool => false) pair.1 pair.2}) ∧
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) := by
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  constructor
  · exact laws.1
      (fun _ : Bool => ()) (fun _ : Bool => false) (id : Concept Bool Bool)
  · exact ⟨rfl, Bool.false_ne_true⟩

/-- Clause 2 recovers a nonconstant target through the identity readout. -/
theorem clause2_nonvacuity_witness :
    defectRelation (id : Concept Bool Bool) (id : Concept Bool Bool) = ∅ ∧
      Function.FactorsThrough (id : Concept Bool Bool)
        (id : Concept Bool Bool) := by
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have factors : Function.FactorsThrough (id : Concept Bool Bool)
      (id : Concept Bool Bool) := by
    intro _ _ sameValue
    exact sameValue
  exact ⟨(laws.2.1 (id : Concept Bool Bool) (id : Concept Bool Bool)).2 factors,
    factors⟩

/-- Clause 3 leaves a nonempty defect unchanged by a redundant readout. -/
theorem clause3_nonvacuity_witness :
    Function.FactorsThrough (fun _ : Bool => false) (fun _ : Bool => ()) ∧
    defectRelation
        (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
        (id : Concept Bool Bool) =
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∧
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) := by
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have redundant :
      Function.FactorsThrough (fun _ : Bool => false) (fun _ : Bool => ()) := by
    intro _ _ _
    rfl
  refine ⟨redundant, laws.2.2.1
    (fun _ : Bool => ()) (fun _ : Bool => false)
    (id : Concept Bool Bool) redundant, ?_⟩
  exact ⟨rfl, Bool.false_ne_true⟩

/-- Clause 3 uses fiber constancy, which is strictly weaker than a total
factorization through the baseline codomain on an empty state space. -/
theorem clause3_fiber_constancy_not_refines_witness :
    let q : Concept Empty Unit := fun state => state.elim
    let definition : Concept Empty Empty := fun state => state.elim
    let target : Concept Empty Unit := fun state => state.elim
    Function.FactorsThrough definition q ∧
      ¬Refines definition q ∧
      defectRelation (conceptJoin q definition) target =
        defectRelation q target := by
  dsimp only
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have fiberConstant :
      Function.FactorsThrough
        (fun state : Empty => (state.elim : Empty))
        (fun state : Empty => (state.elim : Unit)) := by
    intro left
    exact left.elim
  have noTotalFactor :
      ¬Refines (fun state : Empty => (state.elim : Empty))
        (fun state : Empty => (state.elim : Unit)) := by
    rintro ⟨factor, _⟩
    exact (factor ()).elim
  exact ⟨fiberConstant, noTotalFactor, laws.2.2.1
    (fun state : Empty => (state.elim : Unit))
    (fun state : Empty => (state.elim : Empty))
    (fun state : Empty => (state.elim : Unit)) fiberConstant⟩

/-- Clause 4 obstructs finite and arbitrary subfamilies on a blind pair. -/
theorem clause4_nonvacuity_witness :
    (dependentBlindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
      (∀ (n : Nat) (codes : Fin n → Unit),
        ¬∃ recover : (Unit × (Fin n → Bool)) → Bool,
          (id : Concept Bool Bool) = recover ∘
            dependentLanguageExtension (fun _ : Bool => ())
              (fun i => (fun _ : Unit => fun _ : Bool => false) (codes i))) ∧
      (∀ Delta : Set Unit,
        ¬∃ recover : (Unit × (Delta → Bool)) → Bool,
          (id : Concept Bool Bool) = recover ∘
            dependentLanguageExtension (fun _ : Bool => ())
              (fun code : Delta =>
                (fun _ : Unit => fun _ : Bool => false) code.1)) ∧
      ¬dependentFiniteSelectionSufficient
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool) := by
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have residual :
      (dependentBlindResidual
        (fun _ : Unit => fun _ : Bool => false)
        (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty := by
    refine ⟨(false, true), ⟨rfl, Bool.false_ne_true⟩, ?_⟩
    simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
    intro gamma
    cases gamma
    trivial
  exact ⟨residual, laws.2.2.2.1
    (fun _ : Unit => fun _ : Bool => false)
    (fun _ : Bool => ()) (id : Concept Bool Bool) residual⟩

/-- Clause 5 finitely closes a nonempty baseline defect with the identity
definition from a singleton package. -/
theorem clause5_nonvacuity_witness :
    (defectRelation (fun _ : Bool => ())
      (id : Concept Bool Bool)).Nonempty ∧
    dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ ∧
    ∃ (n : Nat) (codes : Fin n → Unit),
      defectRelation
        (dependentLanguageExtension (fun _ : Bool => ())
          (fun i => (fun _ : Unit => (id : Concept Bool Bool)) (codes i)))
        (id : Concept Bool Bool) = ∅ := by
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have baselineDefect :
      (defectRelation (fun _ : Bool => ())
        (id : Concept Bool Bool)).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have noBlindPair :
      dependentBlindResidual (fun _ : Unit => (id : Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro pair ⟨baseline, pairInKernel⟩
    have allDefinitionsEqual :
        ∀ gamma : Unit,
          (id : Concept Bool Bool) pair.1 = id pair.2 := by
      simpa only [jointKernel, conceptKernel, Set.mem_iInter,
        Set.mem_setOf_eq] using pairInKernel
    exact baseline.2 (allDefinitionsEqual ())
  exact ⟨baselineDefect, noBlindPair, laws.2.2.2.2.1
    (fun _ : Unit => (id : Concept Bool Bool))
    (fun _ : Bool => ()) (id : Concept Bool Bool) noBlindPair⟩

/-- The adjacent captured-mass inequality is strict on two overlapping cuts.
This witness is not a witness for source clause 6. -/
theorem adjacent_capture_submodularity_strict_witness :
    letI : MeasurableSpace Bool := ⊤
    let nu : Measure Bool := Measure.count
    let residual : Set Bool := Set.univ
    let cut : Bool → Set Bool := fun _ => Set.univ
    let captured := fun S : Set Bool =>
      residual ∩ ⋃ definition ∈ S, cut definition
    nu (captured ({false} ∪ {true})) +
      nu (captured ({false} ∩ {true})) <
      nu (captured {false}) + nu (captured {true}) := by
  classical
  norm_num [Measure.count_apply_finite, Set.iUnion_const,
    Set.mem_inter_iff, Set.mem_iUnion]

/-- Clause 7 has a nonzero one-step defect for coordinate preparation followed
by a coordinate swap. -/
theorem clause7_nonvacuity_witness :
    let projection : Real × Real → Real := Prod.fst
    let update : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
    let prepare : Real → Real × Real := fun value => (value, 0)
    Function.RightInverse prepare projection ∧
      dist (projection (update (0, 1)))
          ((projection ∘ update ∘ prepare) (projection (0, 1))) =
        dist (projection (update (0, 1)))
          (projection (update ((prepare ∘ projection) (0, 1)))) ∧
      dist (projection (update (0, 1)))
          ((projection ∘ update ∘ prepare) (projection (0, 1))) = 1 := by
  dsimp only
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have rightInverse : Function.RightInverse
      (fun value : Real => (value, 0)) Prod.fst := fun _ => rfl
  refine ⟨rightInverse, laws.2.2.2.2.2.1
    (Prod.fst : Real × Real → Real)
    (fun pair : Real × Real => (pair.2, pair.1))
    (fun value : Real => (value, 0)) rightInverse (0, 1), ?_⟩
  norm_num [Real.dist_eq]

/-- Clause 8 has a nonzero semigroup defect after two coordinate swaps. -/
theorem clause8_nonvacuity_witness :
    let swap : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
    let projection : Real × Real → Real := Prod.fst
    let evolution : Nat → Real × Real → Real × Real := fun n => swap^[n]
    let prepare : Real → Real × Real := fun value => (value, 0)
    Function.RightInverse prepare projection ∧
      (∀ t s x, evolution (t + s) x = evolution t (evolution s x)) ∧
      dist (projection (evolution (1 + 1) (prepare 1)))
          (projection (evolution 1
            (prepare (projection (evolution 1 (prepare 1)))))) =
        dist (projection (evolution 1 (evolution 1 (prepare 1))))
          (projection (evolution 1
            ((prepare ∘ projection) (evolution 1 (prepare 1))))) ∧
      dist (projection (evolution (1 + 1) (prepare 1)))
          (projection (evolution 1
            (prepare (projection (evolution 1 (prepare 1)))))) = 1 := by
  dsimp only
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have rightInverse : Function.RightInverse
      (fun value : Real => (value, 0)) Prod.fst := fun _ => rfl
  have semigroup : ∀ t s x,
      ((fun pair : Real × Real => (pair.2, pair.1))^[t + s]) x =
        ((fun pair : Real × Real => (pair.2, pair.1))^[t])
          (((fun pair : Real × Real => (pair.2, pair.1))^[s]) x) := by
    intro t s x
    exact Function.iterate_add_apply
      (fun pair : Real × Real => (pair.2, pair.1)) t s x
  refine ⟨rightInverse, semigroup, laws.2.2.2.2.2.2.1
    (Prod.fst : Real × Real → Real)
    (fun n => (fun pair : Real × Real => (pair.2, pair.1))^[n])
    (fun value : Real => (value, 0)) rightInverse semigroup 1 1 1, ?_⟩
  norm_num [Function.iterate_succ_apply, Real.dist_eq]

/-- Clause 9 is tight for the identity Lipschitz map and two unit errors. -/
theorem clause9_nonvacuity_witness :
    let first : Real → Real := id
    let second : Real → Real := id
    let direct : Real → Real := fun _ => 2
    LipschitzWith (1 : NNReal) second ∧
      dist (first 0) 1 ≤ 1 ∧
      dist (second 1) (direct 0) ≤ 1 ∧
      dist (second (first 0)) (direct 0) ≤
        (1 : NNReal) * (1 : Real) + 1 ∧
      dist (second (first 0)) (direct 0) =
        (1 : NNReal) * (1 : Real) + 1 := by
  dsimp only
  have laws := directly_provable_laws.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  have firstError : dist ((id : Real → Real) 0) 1 ≤ 1 := by
    norm_num [Real.dist_eq]
  have secondError :
      dist ((id : Real → Real) 1) ((fun _ : Real => 2) 0) ≤ 1 := by
    norm_num [Real.dist_eq]
  refine ⟨LipschitzWith.id, firstError, secondError,
    laws.2.2.2.2.2.2.2 (id : Real → Real) (id : Real → Real)
      (fun _ : Real => 2) 1 1 1 LipschitzWith.id 0 1 firstError secondError, ?_⟩
  norm_num [Real.dist_eq]

/-- Every named witness is a required dependency. Deleting any one leaves this
consumer with an unresolved reference. The first eight source-law positions
are represented in source order; the adjacent capture witness is last and is
not promoted to source clause 6. -/
theorem directly_provable_laws_witnesses_nonvacuous :
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) ∧
    Function.FactorsThrough (id : Concept Bool Bool) (id : Concept Bool Bool) ∧
    (false, true) ∈ defectRelation
      (conceptJoin (fun _ : Bool => ()) (fun _ : Bool => false))
      (id : Concept Bool Bool) ∧
    (¬Refines (fun state : Empty => (state.elim : Empty))
      (fun state : Empty => (state.elim : Unit))) ∧
    (dependentBlindResidual
      (fun _ : Unit => fun _ : Bool => false)
      (fun _ : Bool => ()) (id : Concept Bool Bool)).Nonempty ∧
    (defectRelation (fun _ : Bool => ())
      (id : Concept Bool Bool)).Nonempty ∧
    (let projection : Real × Real → Real := Prod.fst
     let update : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
     let prepare : Real → Real × Real := fun value => (value, 0)
     dist (projection (update (0, 1)))
       ((projection ∘ update ∘ prepare) (projection (0, 1))) = 1) ∧
    (let swap : Real × Real → Real × Real := fun pair => (pair.2, pair.1)
     let projection : Real × Real → Real := Prod.fst
     let evolution : Nat → Real × Real → Real × Real := fun n => swap^[n]
     let prepare : Real → Real × Real := fun value => (value, 0)
     dist (projection (evolution (1 + 1) (prepare 1)))
       (projection (evolution 1
         (prepare (projection (evolution 1 (prepare 1)))))) = 1) ∧
    (let first : Real → Real := id
     let second : Real → Real := id
     let direct : Real → Real := fun _ => 2
     dist (second (first 0)) (direct 0) =
       (1 : NNReal) * (1 : Real) + 1) ∧
    (letI : MeasurableSpace Bool := ⊤
     let nu : Measure Bool := Measure.count
     let residual : Set Bool := Set.univ
     let cut : Bool → Set Bool := fun _ => Set.univ
     let captured := fun S : Set Bool =>
       residual ∩ ⋃ definition ∈ S, cut definition
     nu (captured ({false} ∪ {true})) +
       nu (captured ({false} ∩ {true})) <
       nu (captured {false}) + nu (captured {true})) := by
  exact ⟨clause1_nonvacuity_witness.2,
    clause2_nonvacuity_witness.2,
    clause3_nonvacuity_witness.2.2,
    clause3_fiber_constancy_not_refines_witness.2.1,
    clause4_nonvacuity_witness.1,
    clause5_nonvacuity_witness.1,
    clause7_nonvacuity_witness.2.2,
    clause8_nonvacuity_witness.2.2.2,
    clause9_nonvacuity_witness.2.2.2.2,
    adjacent_capture_submodularity_strict_witness⟩

#print axioms directly_provable_laws_witnesses_nonvacuous
end D5.S3.ConceptDynamics.DefinitionEscapeLaws.DirectlyProvableLawWitnesses
