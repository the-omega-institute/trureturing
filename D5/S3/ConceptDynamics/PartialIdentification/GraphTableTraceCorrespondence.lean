/- GID: D5/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/GraphTableTraceCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parent-ordered traces forget arbitrary initial states, and one graph-table model realizes every hard-intervention world from one fixed canonical seed. -/

import D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics

/- The exogenous state is a complete family of graph-local response tables.
   Initialization is one fixed explicit seed, independent of the encoded model. -/
def graphTableModel
    {n : Nat} {X : Type*}
    (order : List (Fin n)) (order_nodup : order.Nodup)
    (order_complete : ∀ v, v ∈ order)
    (parents : Fin n → Finset (Fin n))
    (seed : Fin n → X) :
    StructuralModel n X ((v : Fin n) → (parents v → X) → X) where
  order := order
  order_nodup := order_nodup
  order_complete := order_complete
  parents := parents
  equation := fun v parentValues tables => tables v parentValues
  initial := fun _ => seed

/- The stronger arbitrary-start result.  Agreement on the processed prefix is
   propagated through each update; topological parent locality makes the next
   equation input agree even when the two initial states differ. -/
theorem evaluation_witness_result_unique_from_arbitrary_start
    {n : Nat} {X U : Type*}
    (model : StructuralModel n X U) (topological : TopologicalOrder model)
    (intervention : Finset (Fin n)) (assigned : Fin n → X) (u : U)
    {state₁ state₂ first second : Fin n → X}
    (hfirst : EvaluationWitness model intervention assigned u
      model.order state₁ first)
    (hsecond : EvaluationWitness model intervention assigned u
      model.order state₂ second) :
    first = second := by
  have aux : ∀ (remaining pre : List (Fin n)) (state₁ state₂ first₂ second₂ : Fin n → X),
      model.order = pre ++ remaining →
      (∀ w, w ∈ pre → state₁ w = state₂ w) →
      EvaluationWitness model intervention assigned u remaining state₁ first₂ →
      EvaluationWitness model intervention assigned u remaining state₂ second₂ →
      first₂ = second₂ := by
    intro remaining
    induction remaining with
    | nil =>
        intro pre state₁ state₂ first₂ second₂ _horder _hagrees h₁ h₂
        have hstates : state₁ = state₂ := by
          funext w
          apply _hagrees w
          have horder' : model.order = pre := by simpa using _horder
          rw [← horder']
          exact model.order_complete w
        have h₁' : first₂ = state₁ := by simpa [EvaluationWitness] using h₁
        have h₂' : second₂ = state₂ := by simpa [EvaluationWitness] using h₂
        exact h₁'.trans (hstates.trans h₂'.symm)
    | cons v remaining ih =>
        intro pre state₁ state₂ first₂ second₂ horder hagrees h₁ h₂
        rcases h₁ with ⟨_parents₁, next₁, hnext₁, htail₁⟩
        rcases h₂ with ⟨_parents₂, next₂, hnext₂, htail₂⟩
        subst next₁
        subst next₂
        have htop := topological pre remaining v
          (by simpa [List.append_assoc] using horder)
        have hparent : ∀ parent : model.parents v,
            state₁ parent.1 = state₂ parent.1 := by
          intro parent
          exact hagrees parent.1 (htop parent).1
        have hequation :
            intervenedEquation model intervention assigned v state₁ u =
              intervenedEquation model intervention assigned v state₂ u := by
          by_cases hv : v ∈ intervention
          · simp [intervenedEquation, hv]
          · simp only [intervenedEquation, hv, ↓reduceIte]
            congr 1
            funext parent
            exact hparent parent
        have hnotmem : v ∉ pre := by
          intro hv
          have hnodup : (pre ++ v :: remaining).Nodup := by
            simpa [horder] using model.order_nodup
          have hprefix := (List.nodup_append.mp hnodup).2
          have hmem : v ∈ v :: remaining := by simp
          exact (hprefix.2 v hv v hmem) rfl
        have hnext_agree : ∀ w, w ∈ pre ++ [v] →
            (Function.update state₁ v
              (intervenedEquation model intervention assigned v state₁ u)) w =
            (Function.update state₂ v
              (intervenedEquation model intervention assigned v state₂ u)) w := by
          intro w hw
          by_cases hwv : w = v
          · subst w
            simp [hequation]
          · have hwpre : w ∈ pre := by
              simpa [List.mem_append, hwv] using hw
            simp [Function.update_of_ne hwv, hagrees w hwpre]
        apply ih (pre ++ [v])
          (Function.update state₁ v
            (intervenedEquation model intervention assigned v state₁ u))
          (Function.update state₂ v
            (intervenedEquation model intervention assigned v state₂ u))
          first₂ second₂ (by simpa [List.append_assoc] using horder)
          (by
            intro w hw
            exact hnext_agree w hw)
          htail₁ htail₂
  exact aux model.order [] state₁ state₂ first second rfl
    (by simp) hfirst hsecond

/- One encoding at the original shared exogenous state serves every hard
   intervention. The realized model has the same graph and order, but its fixed
   explicit initialization need not agree with the original initialization. -/
theorem graph_table_shared_seed_trace_correspondence
    {n : Nat} {X U : Type*}
    (model : StructuralModel n X U) (topological : TopologicalOrder model)
    (u : U) (seed : Fin n → X) :
    let realized := graphTableModel model.order model.order_nodup
      model.order_complete model.parents seed
    let tables := fun (v : Fin n) (pa : model.parents v → X) => model.equation v pa u
    ∀ (intervention : Finset (Fin n)) (assigned : Fin n → X),
      ∃! canonical : Fin n → X,
        EvaluationWitness realized intervention assigned tables model.order seed canonical ∧
        ∀ (state result : Fin n → X),
          EvaluationWitness model intervention assigned u model.order state result →
          result = canonical := by
  dsimp only
  let realized := graphTableModel model.order model.order_nodup
    model.order_complete model.parents seed
  let tables := fun (v : Fin n) (pa : model.parents v → X) => model.equation v pa u
  have realized_topological : TopologicalOrder realized := topological
  intro intervention assigned
  have transport : ∀ (remaining : List (Fin n)) (state result : Fin n → X),
      EvaluationWitness model intervention assigned u remaining state result →
      EvaluationWitness realized intervention assigned tables remaining state result := by
    intro remaining
    induction remaining with
    | nil => intro state result h; exact h
    | cons v remaining ih =>
        intro state result h
        rcases h with ⟨parents_done, next, hnext, htail⟩
        refine ⟨parents_done, next, ?_, ih next result htail⟩
        exact hnext
  obtain ⟨canonical, hcanonical, hcanonical_unique⟩ :=
    parent_ordered_structure_evaluation_semantics realized realized_topological
      intervention assigned tables
  refine ⟨canonical, ⟨hcanonical, ?_⟩, ?_⟩
  · intro state result hresult
    exact evaluation_witness_result_unique_from_arbitrary_start
      realized realized_topological intervention assigned tables
      (transport model.order state result hresult) hcanonical
  · intro other hother
    exact hcanonical_unique other hother.1

#print axioms evaluation_witness_result_unique_from_arbitrary_start
#print axioms graph_table_shared_seed_trace_correspondence

end D5.S3.ConceptDynamics.PartialIdentification.GraphTableTraceCorrespondence
