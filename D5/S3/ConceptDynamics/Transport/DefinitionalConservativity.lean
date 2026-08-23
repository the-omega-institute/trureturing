/- GID: D5/S3/ConceptDynamics/Transport/DefinitionalConservativity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/DefinitionalConservativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Definitional extensions obtained by expanding every axiom and rule are conservative on the old language. -/

/- Library-search audit trail (2026-08-21):
   * Repository searches for definitional conservativity, formula expansion,
     proof translation, and pullback derivations found no exact theorem.
   * Pinned Mathlib searches found category-theoretic conservative-functor
     declarations only; they do not express proof-theoretic definitional
     conservativity, so no exact library hit was applicable.
   * The proof below is a direct induction on the source derivation, using
     List.mem_map and the section law for the old-language embedding.
-/

import Mathlib.Data.List.Basic

noncomputable section

namespace D5.S3.ConceptDynamics.Transport.DefinitionalConservativity

structure Calculus (Sentence : Type*) where
  axioms : Sentence -> Prop
  rule : List Sentence -> Sentence -> Prop

inductive Derivation {Sentence : Type*} (calculus : Calculus Sentence) :
    Sentence -> Prop
  | baseAxiom {sentence : Sentence} :
      calculus.axioms sentence -> Derivation calculus sentence
  | baseRule {premises : List Sentence} {conclusion : Sentence} :
      calculus.rule premises conclusion ->
      (forall premise, premise ∈ premises -> Derivation calculus premise) ->
      Derivation calculus conclusion

def pullbackCalculus {Base Extended : Type*}
    (base : Calculus Base) (expand : Extended -> Base) : Calculus Extended where
  axioms sentence := base.axioms (expand sentence)
  rule premises conclusion := base.rule (premises.map expand) (expand conclusion)

private theorem translate_derivation {Base Extended : Type*}
    (base : Calculus Base) (expand : Extended -> Base)
    {sentence : Extended} :
    Derivation (pullbackCalculus base expand) sentence ->
      Derivation base (expand sentence) := by
  intro derivation
  induction derivation with
  | baseAxiom haxiom =>
      exact Derivation.baseAxiom haxiom
  | @baseRule premises conclusion hrule hpremises ih =>
      refine @Derivation.baseRule Base base (premises.map expand)
        (expand conclusion) hrule ?_
      intro premiseBase membership
      rcases List.mem_map.mp membership with ⟨premise, premiseMembership, rfl⟩
      exact ih premise premiseMembership

theorem definitional_conservativity {Base Extended : Type*}
    (base : Calculus Base) (expand : Extended -> Base) (embed : Base -> Extended)
    (section_law : forall sentence, expand (embed sentence) = sentence)
    {sentence : Base}
    (extended_derivation :
      Derivation (pullbackCalculus base expand) (embed sentence)) :
    Derivation base sentence := by
  rw [← section_law sentence]
  exact translate_derivation base expand extended_derivation

#print axioms definitional_conservativity

end D5.S3.ConceptDynamics.Transport.DefinitionalConservativity
