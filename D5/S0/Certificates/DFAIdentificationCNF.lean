/- GID: D5/S0/Certificates/DFAIdentificationCNF
   generality: G
   mirror-B: D5/B/S0/Certificates/DFAIdentificationCNF
   mirror-E: none(waiver:certified-cnf-interface)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   digest: Certified CNF encodings separate untrusted formula generation from sound and complete identification semantics. -/

import D5.S0.Automata.IdentificationColoring
import Mathlib.Tactic.Sat.FromLRAT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.DFAIdentificationCNF

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.LabeledPrefixTree
open D5.S0.Automata.IdentificationColoring

universe u v w x

/-- Propositional satisfiability for Mathlib's canonical CNF carrier. -/
def Satisfiable (formula : Sat.Fmla) : Prop :=
  ∃ valuation : Sat.Valuation,
    Sat.Valuation.satisfies_fmla valuation formula

/-- A proof-carrying CNF encoding. Formula construction and SAT solving may be
untrusted; admission requires proofs of both semantic directions. -/
structure CertifiedEncoding (Problem : Prop) where
  formula : Sat.Fmla
  sound : Satisfiable formula → Problem
  complete : Problem → Satisfiable formula

namespace CertifiedEncoding

/-- The certified formula is satisfiable exactly when its mathematical problem
has a witness. -/
theorem satisfiable_iff
    {Problem : Prop} (encoding : CertifiedEncoding Problem) :
    Satisfiable encoding.formula ↔ Problem :=
  ⟨encoding.sound, encoding.complete⟩

/-- Certified encodings can be transported across a proved equivalence without
changing their CNF bytes. -/
def transport {Problem EquivalentProblem : Prop}
    (encoding : CertifiedEncoding Problem)
    (equivalence : Problem ↔ EquivalentProblem) :
    CertifiedEncoding EquivalentProblem where
  formula := encoding.formula
  sound satisfiable := equivalence.mp (encoding.sound satisfiable)
  complete witness := encoding.complete (equivalence.mpr witness)

end CertifiedEncoding

/-- The semantic target of a finite DFA-identification formula. -/
abbrev IdentificationEncoding
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) :=
  CertifiedEncoding (Nonempty (Identification sample base Color))

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
            FitsSample sample machine)) :
    IdentificationEncoding sample base Color :=
  encoding.transport
    (identification_iff_machine_realization sample base Color).symm

#print axioms CertifiedEncoding.satisfiable_iff
#print axioms identification_formula_satisfiable_iff

end D5.S0.Certificates.DFAIdentificationCNF
