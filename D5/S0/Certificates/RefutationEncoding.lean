/- GID: D5/S0/Certificates/RefutationEncoding
   generality: G
   mirror-B: D5/B/S0/Certificates/RefutationEncoding
   mirror-E: none(waiver:one-way-unsat-semantics)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: Refutation encodings require only the model-to-SAT direction needed for sound UNSAT lower bounds, while exact encodings additionally recover mathematical models from satisfying assignments. -/

import D5.S0.Automata.TypedStableRightCongruence
import D5.S0.Certificates.DFAIdentificationCNF
import D5.S0.Certificates.LRATUnsatisfiable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.RefutationEncoding

open D5.S0.Automata.LabeledPrefixTree
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.IdentificationColoring
open D5.S0.Automata.TypedStableRightCongruence
open D5.S0.Certificates.DFAIdentificationCNF
open D5.S0.Certificates.LRATUnsatisfiable

universe u v w x

/-- A proof-carrying formula used only for refutation. Every mathematical model
must induce a satisfying assignment. Satisfying assignments may include
spurious relaxed models. -/
structure RefutationEncoding (Problem : Prop) where
  formula : Sat.Fmla
  model_to_sat : Problem → Satisfiable formula

namespace RefutationEncoding

/-- Pull a refutation encoding back along a proved implication. -/
def contramap {StrongProblem WeakProblem : Prop}
    (encoding : RefutationEncoding WeakProblem)
    (forget : StrongProblem → WeakProblem) :
    RefutationEncoding StrongProblem where
  formula := encoding.formula
  model_to_sat model := encoding.model_to_sat (forget model)

/-- A kernel-checked refutation of a one-way encoding is already sufficient to
exclude the mathematical problem. No SAT-to-model theorem is needed. -/
theorem false_of_refutation
    {Problem : Prop}
    (encoding : RefutationEncoding Problem)
    (refutation : Refutation encoding.formula) :
    ¬Problem := by
  intro model
  obtain ⟨valuation, satisfies⟩ := encoding.model_to_sat model
  exact (refutation.sound valuation) satisfies

end RefutationEncoding

/-- An exact encoding adds the converse semantic direction. -/
structure ExactEncoding (Problem : Prop)
    extends RefutationEncoding Problem where
  sat_to_model : Satisfiable toRefutationEncoding.formula → Problem

namespace ExactEncoding

/-- Exact encodings recover the older bidirectional certified interface. -/
def toCertifiedEncoding {Problem : Prop}
    (encoding : ExactEncoding Problem) :
    CertifiedEncoding Problem where
  formula := encoding.formula
  sound := encoding.sat_to_model
  complete := encoding.model_to_sat

/-- Exact encodings characterize satisfiability by the mathematical problem. -/
theorem satisfiable_iff
    {Problem : Prop} (encoding : ExactEncoding Problem) :
    Satisfiable encoding.formula ↔ Problem :=
  ⟨encoding.sat_to_model, encoding.model_to_sat⟩

end ExactEncoding

/-- A formula whose every stable-right coloring yields a satisfying assignment. -/
abbrev StableRightColoringRefutationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) :=
  RefutationEncoding
    (Nonempty (TypedStableRightColoring sample base Color))

/-- Any refutation encoding for stable right colorings is automatically a
refutation encoding for exact identifications, because every identification
induces such a coloring. -/
def identificationEncodingOfStableRightColoringEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (encoding :
      StableRightColoringRefutationEncoding sample base Color) :
    RefutationEncoding (Nonempty (Identification sample base Color)) :=
  encoding.contramap fun identification =>
    match identification with
    | ⟨witness⟩ =>
        ⟨TypedStableRightColoring.ofIdentification witness⟩

/-- Refuting a stable-right-coloring encoding rules out every exact
identification on the same color carrier. -/
theorem no_identification_of_stable_right_coloring_refutation
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (encoding :
      StableRightColoringRefutationEncoding sample base Color)
    (refutation : Refutation encoding.formula) :
    ¬Nonempty (Identification sample base Color) :=
  RefutationEncoding.false_of_refutation
    (identificationEncodingOfStableRightColoringEncoding
      sample base Color encoding)
    refutation

#print axioms RefutationEncoding.false_of_refutation
#print axioms ExactEncoding.satisfiable_iff
#print axioms no_identification_of_stable_right_coloring_refutation

end D5.S0.Certificates.RefutationEncoding
