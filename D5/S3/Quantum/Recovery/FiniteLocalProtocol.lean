/- GID: D5/S3/Quantum/Recovery/FiniteLocalProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalProtocol
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual finite local completely positive instrument trees conserve complete-subtree trace on every matrix. -/

import D5.S3.Quantum.Recovery.RetainedLocalProtocol


namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
variable {A : Type} [Fintype A] [DecidableEq A]
variable {R : Type} [Fintype R] {Feedback : Type}

/-- Complete-subtree conservation on every complex matrix, not only states.
    Local conservation is an instrument field; subtree conservation is derived. -/
theorem complete_subtree_trace {d : A → ℕ} (T : Tree Feedback d) (X : State R d) :
    terminalTrace T X = Matrix.trace X := by
  induction T with
  | leaf => simp [terminalTrace, terminalOutputs]
  | @node d J child ih =>
    have local_total (X : State R d) : ∑ y, Matrix.trace (step J y X) = Matrix.trace X := by
      let e := inputSplit R d J.actor
      have branch (y : Fin J.outcomes) : Matrix.trace (step J y X) =
          ∑ r : Rest R d J.actor, Matrix.trace (action (J.operation y)
            (fun i j => X (e.symm (i,r)) (e.symm (j,r)))) := by
        unfold Matrix.trace
        rw [← (outputSplit R J y).symm.sum_comp]
        rw [Fintype.sum_prod_type]
        simp only [Matrix.diag_apply, step,
          Equiv.apply_symm_apply]
        exact Finset.sum_comm
      simp_rw [branch]
      rw [Finset.sum_comm]
      calc
        _ = ∑ r : Rest R d J.actor, Matrix.trace
            (fun i j => X (e.symm (i,r)) (e.symm (j,r))) :=
          Finset.sum_congr rfl (fun r _ => J.trace_preserving _)
        _ = Matrix.trace X := by
          unfold Matrix.trace
          rw [← e.symm.sum_comp]
          conv_rhs => rw [Fintype.sum_prod_type]
          simp only [Matrix.diag_apply]
          exact Finset.sum_comm
    change ((List.flatten (List.ofFn (fun y =>
      (terminalOutputs (child y) (step J y X)).map
        (fun z => { z with history := y.val :: z.history })))).map
      (fun z => Matrix.trace z.state)).sum = _
    simp only [List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_map,
      List.sum_ofFn, Function.comp_def]
    change (∑ y, terminalTrace (child y) (step J y X)) = _
    simp_rw [ih]
    exact local_total X


end D5.S3.Quantum.Recovery.FiniteLocalProtocol
