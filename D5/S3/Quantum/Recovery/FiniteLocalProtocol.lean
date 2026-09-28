/- GID: D5/S3/Quantum/Recovery/FiniteLocalProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FiniteLocalProtocol
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual finite local completely positive instrument trees conserve complete-subtree trace on every matrix. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic


namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
variable {A : Type} [Fintype A] [DecidableEq A]
abbrev Coordinates (d : A → ℕ) := (a : A) → Fin (d a)
abbrev State (R : Type) (d : A → ℕ) := Matrix (R × Coordinates d) (R × Coordinates d) ℂ
abbrev LocalState (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev Rest (R : Type) (d : A → ℕ) (a : A) :=
  R × ((b : { b // b ≠ a }) → Fin (d b))

/-- A spectator (the system and any reference) is never acted upon. -/
noncomputable def inputSplit (R : Type) (d : A → ℕ) (a : A) :
    (R × Coordinates d) ≃ Fin (d a) × Rest R d a :=
  (Equiv.prodCongr (Equiv.refl R) (Equiv.piSplitAt a (fun b => Fin (d b)))).trans
    { toFun := fun x => (x.2.1, x.1, x.2.2)
      invFun := fun x => (x.2.1, x.1, x.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable def action {m n : ℕ}
    (φ : CompletelyPositiveMap (CStarMatrix (Fin m) (Fin m) ℂ)
      (CStarMatrix (Fin n) (Fin n) ℂ)) (X : LocalState m) : LocalState n :=
  CStarMatrix.ofMatrix.symm (φ (CStarMatrix.ofMatrix X))

structure Instrument (d : A → ℕ) where
  actor : A
  outcomes : ℕ
  output : Fin outcomes → A → ℕ
  unchanged : ∀ y b, b ≠ actor → output y b = d b
  operation : (y : Fin outcomes) →
    CompletelyPositiveMap (CStarMatrix (Fin (d actor)) (Fin (d actor)) ℂ)
      (CStarMatrix (Fin (output y actor)) (Fin (output y actor)) ℂ)
  trace_preserving : ∀ X : LocalState (d actor),
    ∑ y, Matrix.trace (action (operation y) X) = Matrix.trace X

noncomputable def outputSplit (R : Type) {d : A → ℕ}
    (J : Instrument d) (y : Fin J.outcomes) :
    (R × Coordinates (J.output y)) ≃ Fin (J.output y J.actor) × Rest R d J.actor :=
  (inputSplit R (J.output y) J.actor).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl R)
      (Equiv.piCongrRight (fun b =>
        Equiv.cast (congrArg Fin (J.unchanged y b b.property))))))

variable {R : Type} [Fintype R]

/-- The other holders' row and column coordinates are fixed while the actor's
    entire local matrix is passed to its coarse CP map. No Kraus label occurs. -/
noncomputable def step {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes)
    (X : State R d) : State R (J.output y) := fun p q =>
  let e := inputSplit R d J.actor
  let f := outputSplit R J y
  action (J.operation y)
    (fun i j => X (e.symm (i, (f p).2)) (e.symm (j, (f q).2))) (f p).1 (f q).1

inductive Tree (Feedback : Type) : (A → ℕ) → Type
  | leaf {d} (feedback : Feedback) : Tree Feedback d
  | node {d} (instrument : Instrument d)
      (child : (y : Fin instrument.outcomes) → Tree Feedback (instrument.output y)) :
        Tree Feedback d

/-- Histories contain precisely observed outcomes. Feedback is attached to leaves. -/
structure Terminal (Feedback R : Type) (A : Type) where
  history : List ℕ
  feedback : Feedback
  dimensions : A → ℕ
  state : State R dimensions

variable {Feedback : Type}

/-- The returned matrices retain all accessible memories. Different terminals
    may have different dimensions. The list enumerates observed histories only. -/
noncomputable def terminalOutputs {d : A → ℕ} :
    Tree Feedback d → State R d → List (Terminal Feedback R A)
  | .leaf f, X => [⟨[], f, d, X⟩]
  | .node J child, X => (List.ofFn (fun y =>
      (terminalOutputs (child y) (step J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

noncomputable def terminalTrace {d : A → ℕ} (T : Tree Feedback d) (X : State R d) : ℂ :=
  ((terminalOutputs T X).map (fun z => Matrix.trace z.state)).sum

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

/-- Independent local auxiliary states. Their density matrices, rather than
    purification witnesses, are part of the physical protocol data. -/
structure ProductAncillas (A : Type) where
  dimension : A → ℕ
  density : (a : A) →
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState (Fin (dimension a))

/-- Append the independent mixed auxiliaries, leaving the source/reference
    matrix unrestricted. Finite product coordinates are only a local reindexing. -/
noncomputable def appendAncillas {H : A → ℕ} (η : ProductAncillas A)
    (X : State R H) : State R (fun a => H a * η.dimension a) := fun p q =>
  X (p.1, fun a => (finProdFinEquiv.symm (p.2 a)).1)
    (q.1, fun a => (finProdFinEquiv.symm (q.2 a)).1) *
    ∏ a, (η.density a).1 (finProdFinEquiv.symm (p.2 a)).2
      (finProdFinEquiv.symm (q.2 a)).2

structure Protocol (Feedback : Type) (H : A → ℕ) where
  ancillas : ProductAncillas A
  tree : Tree Feedback (fun a => H a * ancillas.dimension a)

noncomputable def Protocol.run {H : A → ℕ} (P : Protocol Feedback H)
    (X : State R H) : List (Terminal Feedback R A) :=
  terminalOutputs P.tree (appendAncillas P.ancillas X)

end D5.S3.Quantum.Recovery.FiniteLocalProtocol
