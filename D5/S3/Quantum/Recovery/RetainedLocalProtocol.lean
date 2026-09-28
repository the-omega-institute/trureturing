/- GID: D5/S3/Quantum/Recovery/RetainedLocalProtocol
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/RetainedLocalProtocol
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Retaining inaccessible Kraus outputs reproduces every actual coarse prefix and terminal on all matrices. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Recovery.FiniteLocalProtocol
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Recovery.FiniteLocalProtocol
open scoped BigOperators
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel
variable {A : Type} [Fintype A] [DecidableEq A]
variable {R : Type} [Fintype R] {Feedback : Type}

abbrev Hidden {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :=
  Fin (J.output y J.actor) × Fin (d J.actor)

noncomputable def chosenKraus {d : A → ℕ} (J : Instrument d) (y : Fin J.outcomes) :
    Hidden J y → Matrix (Fin (J.output y J.actor)) (Fin (d J.actor)) ℂ :=
  (krausRepresentation (J.operation y)).val

abbrev RetainedState (R G : Type) (d : A → ℕ) :=
  Matrix ((R × Coordinates d) × G) ((R × Coordinates d) × G) ℂ

noncomputable def traceGarbage {G : Type} [Fintype G] {d : A → ℕ}
    (X : RetainedState R G d) : State R d := fun p q => ∑ g, X (p,g) (q,g)

/-- Coherent local dilation. Old garbage coordinates are passed unchanged to
both input entries; only the new hidden coordinate selects a Kraus operator.
Neither hidden coordinate is an argument of the observed tree's child function. -/
noncomputable def retainedStep {G : Type} {d : A → ℕ}
    (J : Instrument d) (y : Fin J.outcomes) (X : RetainedState R G d) :
    RetainedState R (Hidden J y × G) (J.output y) := fun p q =>
  let e := inputSplit R d J.actor
  let f := outputSplit R J y
  ∑ i, ∑ j, chosenKraus J y p.2.1 (f p.1).1 i *
    X (e.symm (i,(f p.1).2),p.2.2) (e.symm (j,(f q.1).2),q.2.2) *
    star (chosenKraus J y q.2.1 (f q.1).1 j)

/-- Garbage is traced only at leaves, after the whole retained execution.
The accumulating hidden type never changes the observed control tree. -/
noncomputable def retainedOutputs {d : A → ℕ} (T : Tree Feedback d) :
    {G : Type} → [Fintype G] → RetainedState R G d → List (Terminal Feedback R A) :=
  match T with
  | .leaf f => fun X => [⟨[], f, d, traceGarbage X⟩]
  | .node J child => fun X => (List.ofFn (fun y =>
      (retainedOutputs (child y) (retainedStep J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- Every observed prefix, including root and early leaves. -/
noncomputable def coarsePrefixes {d : A → ℕ} (T : Tree Feedback d)
    (X : State R d) : List (Terminal (Option Feedback) R A) :=
  match T with
  | .leaf f => [⟨[], some f, d, X⟩]
  | .node J child => ⟨[], none, d, X⟩ ::
      (List.ofFn (fun y => (coarsePrefixes (child y) (step J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- Prefix observations trace a copy for reporting only. Recursion passes the
untraced retained state to the next edge. -/
noncomputable def retainedPrefixes {d : A → ℕ} (T : Tree Feedback d) :
    {G : Type} → [Fintype G] → RetainedState R G d →
      List (Terminal (Option Feedback) R A) :=
  match T with
  | .leaf f => fun X => [⟨[], some f, d, traceGarbage X⟩]
  | .node J child => fun X => ⟨[], none, d, traceGarbage X⟩ ::
      (List.ofFn (fun y => (retainedPrefixes (child y) (retainedStep J y X)).map
        (fun z => { z with history := y.val :: z.history }))).flatten

/-- All-matrix recursive faithfulness, with arbitrary untouched spectator and
arbitrary initial correlations with finite inaccessible garbage. -/
theorem recursive_coarse_retained {d : A → ℕ} (T : Tree Feedback d) :
    ∀ {G : Type} [Fintype G] (X : RetainedState R G d),
      retainedOutputs T X = terminalOutputs T (traceGarbage X) ∧
      retainedPrefixes T X = coarsePrefixes T (traceGarbage X) := by
  induction T with
  | leaf f => intro G _ X; exact ⟨rfl, rfl⟩
  | @node d J child ih =>
    intro G _ X
    have edge (y : Fin J.outcomes) :
        traceGarbage (retainedStep J y X) = step J y (traceGarbage X) := by
      have exactK := (krausRepresentation (J.operation y)).property
      ext p q
      dsimp only [step, action]
      rw [exactK]
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      change (∑ kg : Hidden J y × G, ∑ i, ∑ j,
        chosenKraus J y kg.1 (outputSplit R J y p).1 i *
          X ((inputSplit R d J.actor).symm (i,(outputSplit R J y p).2),kg.2)
            ((inputSplit R d J.actor).symm (j,(outputSplit R J y q).2),kg.2) *
          star (chosenKraus J y kg.1 (outputSplit R J y q).1 j)) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _
      simp only [traceGarbage, Finset.mul_sum, Finset.sum_mul, chosenKraus]
      conv_rhs => rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    constructor
    · simp only [retainedOutputs, terminalOutputs]
      congr 1
      apply congrArg List.ofFn
      funext y
      rw [(ih y _).1, edge]
    · simp only [retainedPrefixes, coarsePrefixes]
      congr 2
      apply congrArg List.ofFn
      funext y
      rw [(ih y _).2, edge]

end D5.S3.Quantum.Recovery.FiniteLocalProtocol
