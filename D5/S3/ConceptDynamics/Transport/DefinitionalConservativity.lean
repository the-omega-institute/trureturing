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
import OmegaMath.Data.SnocList

/-! Conservativity under expansion of axioms and inference rules. -/

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

/-- A derivable sentence belongs to every family closed under the given axioms
and inference rules. -/
def StrictDerivation {Sentence : Type u}
    (axioms : Sentence → Prop) (rule : Omega.SnocList Sentence → Sentence → Prop)
    (sentence : Sentence) : Prop :=
  ∀ family : Sentence → Prop,
    (∀ s, axioms s → family s) →
    (∀ premises conclusion, rule premises conclusion →
      (∀ premise, premises.Mem premise → family premise) → family conclusion) →
    family sentence

private theorem translate_derivation {Base : Type u} {Extended : Type v}
    (axioms : Base → Prop) (rule : Omega.SnocList Base → Base → Prop)
    (expand : Extended → Base) {sentence : Extended}
    (extended : StrictDerivation (fun s => axioms (expand s))
      (fun premises s => rule (premises.map expand) (expand s)) sentence) :
    StrictDerivation axioms rule (expand sentence) :=
  fun family includeAxiom includeRule =>
    extended (fun s => family (expand s)) (fun s evidence => includeAxiom (expand s) evidence)
      (fun premises conclusion evidence derive =>
        includeRule (premises.map expand) (expand conclusion) evidence (fun premise member =>
          (premises.exists_of_mem_map expand premise member).elim (fun original found =>
            Omega.Eq.subst family found.right (derive original found.left))))

/-- Expanding the axioms and rules of a definitional extension preserves old
sentences derivable in the extension. -/
theorem definitional_conservativity {Base : Type u} {Extended : Type v}
    (axioms : Base → Prop) (rule : Omega.SnocList Base → Base → Prop)
    (expand : Extended → Base) (embed : Base → Extended)
    (sectionLaw : ∀ s, Omega.Eq (expand (embed s)) s) {sentence : Base}
    (extended : StrictDerivation (fun s => axioms (expand s))
      (fun premises s => rule (premises.map expand) (expand s)) (embed sentence)) :
    StrictDerivation axioms rule sentence :=
  Omega.Eq.subst (StrictDerivation axioms rule) (sectionLaw sentence)
    (translate_derivation axioms rule expand extended)

end D5.S3.ConceptDynamics.Transport.DefinitionalConservativity
