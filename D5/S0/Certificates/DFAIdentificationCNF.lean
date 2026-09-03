/- GID: D5/S0/Certificates/DFAIdentificationCNF
   generality: G
   mirror-B: D5/B/S0/Certificates/DFAIdentificationCNF
   mirror-E: none(waiver:certified-cnf-interface)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: Exact and refutation-only CNF interfaces separate untrusted formula generation from the semantic direction required by each proof. -/

import D5.S0.Automata.TypedStableRightCongruence
import Mathlib.Tactic.Sat.FromLRAT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.DFAIdentificationCNF

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.LabeledPrefixTree
open D5.S0.Automata.IdentificationColoring
open D5.S0.Automata.TypedStableRightCongruence

universe u v w x

/-- Propositional satisfiability for Mathlib's canonical CNF carrier. -/
def Satisfiable (formula : Sat.Fmla) : Prop :=
  ∃ valuation : Sat.Valuation,
    Sat.Valuation.satisfies_fmla valuation formula

/-- A refutation-oriented encoding only certifies the direction needed for a
lower bound: every mathematical witness gives a satisfying valuation. Hence a
kernel-checked refutation of the formula excludes the mathematical problem. -/
structure RefutationEncoding (Problem : Prop) where
  formula : Sat.Fmla
  complete : Problem → Satisfiable formula

namespace RefutationEncoding

/-- Pull an encoding back along a proved implication. This permits a relaxed or
quotient-level formula to refute a stronger machine-existence problem. -/
def pullback {Problem EncodedProblem : Prop}
    (encoding : RefutationEncoding EncodedProblem)
    (implication : Problem → EncodedProblem) :
    RefutationEncoding Problem where
  formula := encoding.formula
  complete witness := encoding.complete (implication witness)

/-- Equivalent problems share the same refutation formula. -/
def transport {Problem EquivalentProblem : Prop}
    (encoding : RefutationEncoding Problem)
    (equivalence : Problem ↔ EquivalentProblem) :
    RefutationEncoding EquivalentProblem :=
  encoding.pullback equivalence.mpr

end RefutationEncoding

/-- An exact proof-carrying encoding certifies both decoding and encoding. This
stronger interface is appropriate when satisfiable formulas will be used as
positive witnesses. -/
structure CertifiedEncoding (Problem : Prop) extends RefutationEncoding Problem where
  sound : Satisfiable formula → Problem

namespace CertifiedEncoding

/-- The certified formula is satisfiable exactly when its mathematical problem
has a witness. -/
theorem satisfiable_iff
    {Problem : Prop} (encoding : CertifiedEncoding Problem) :
    Satisfiable encoding.formula ↔ Problem :=
  ⟨encoding.sound, encoding.complete⟩

/-- Exact encodings can be transported across a proved equivalence without
changing their CNF bytes. -/
def transport {Problem EquivalentProblem : Prop}
    (encoding : CertifiedEncoding Problem)
    (equivalence : Problem ↔ EquivalentProblem) :
    CertifiedEncoding EquivalentProblem where
  formula := encoding.formula
  sound satisfiable := equivalence.mp (encoding.sound satisfiable)
  complete witness := encoding.complete (equivalence.mpr witness)

end CertifiedEncoding

/-- The exact semantic target of a finite DFA-identification formula. -/
abbrev IdentificationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) :=
  CertifiedEncoding (Nonempty (Identification sample base Color))

/-- The weaker interface sufficient to refute every identification on a fixed
color carrier. -/
abbrev IdentificationRefutationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) :=
  RefutationEncoding (Nonempty (Identification sample base Color))

/-- A certified identification formula is satisfiable exactly when the labeled
prefix family has a valid coloring over the selected color type. -/
theorem identification_formula_satisfiable_iff
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (encoding : IdentificationEncoding sample base Color) :
    Satisfiable encoding.formula ↔
      Nonempty (Identification sample base Color) :=
  encoding.satisfiable_iff

/-- Any future optimized APTA encoding can be admitted by proving equivalence
to the machine-realization semantics already frozen in the automata layer. -/
def ofMachineRealizationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (encoding :
      CertifiedEncoding
        (∃ machine : TypedPartialDFAO base Output Color,
          Nonempty (PrefixRealization sample machine) ∧
            FitsSample machine)) :
    IdentificationEncoding sample base Color :=
  encoding.transport
    (identification_iff_machine_realization sample base Color).symm

/-- A formula complete for stable right congruences is already complete for
full identifications because every identification forgets to such a
congruence. No SAT-to-machine decoding theorem is required for this use. -/
def ofStableRightCongruenceRefutationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (encoding :
      RefutationEncoding
        (Nonempty (StableRightCongruence sample base Color))) :
    IdentificationRefutationEncoding sample base Color :=
  encoding.pullback fun identification => by
    rcases identification with ⟨witness⟩
    exact ⟨identificationToStableRightCongruence witness⟩

#print axioms RefutationEncoding.pullback
#print axioms CertifiedEncoding.satisfiable_iff
#print axioms identification_formula_satisfiable_iff
#print axioms ofStableRightCongruenceRefutationEncoding

end D5.S0.Certificates.DFAIdentificationCNF
