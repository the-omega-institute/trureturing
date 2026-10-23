import D5.S0.Computability.PreorderTreeEvaluation
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.PreorderTreeEvaluation

open _root_.D5.S0.Computability.PreorderTreeEvaluation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- The parameter ranges over every leaf carrier, including empty ones. -/
abbrev codecSignature : Signature where
  Params := Type
  State A := Word A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ A := Option (FreeMagma A)
  Anchor := Empty
  finiteAnchor := inferInstance

def codecActual : Realization codecSignature := realize codecSignature
  (fun _ _ w => parse w) (fun e => nomatch e)

def codecRejected : Realization codecSignature := realize codecSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev codecArena : Arena where
  signature := codecSignature
  Law R := ∀ (A : Type) (w : Word A) (t : FreeMagma A),
    R.readout () A w = some t ↔ w = word t

private theorem codec_rejected : ¬ codecArena.Law codecRejected := by
  intro h
  have bad := (h Bool (word (.of false)) (.of false)).mpr rfl
  cases bad

def codecEvidence : Registration codecArena (codecArena.Law codecActual) where
  actual := codecActual
  bridge := Iff.rfl
  variation := ⟨fun _ w t => preorder_codec w t,codecRejected,codec_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codecRejected,?_,rfl,codec_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨Bool,word (.of false),word (.of true),?_⟩
    change parse (word (.of false)) ≠ parse (word (.of true))
    rw [(preorder_codec _ _).mpr rfl, (preorder_codec _ _).mpr rfl]
    intro h
    have ht := Option.some.inj h
    cases ht

/- This proof retains the complete polymorphic codec telescope. The evaluator
   and fold audits still require whole-family parameterization of every
   primitive codable carrier and constructor operation. The list-algorithm
   audit retains arbitrary coding, decidable equality and decidable primitive
   recursive relations, with the insertion element as a runtime input. Contract source
   selection and raw occurrence binding remain unregistered for all four
   source theorems; no declared_validated status is claimed. -/

end Reg.D5.S0.Computability.PreorderTreeEvaluation
