/- GID: D5/S0/Rewriting/NormalizationSystem
   generality: G
   mirror-B: D5/B/S0/Rewriting/NormalizationSystem
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Terminating locally confluent rewrite systems expose one canonical certified normalizer. -/

import D5.S0.Rewriting.NormalFormFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Rewriting.NormalizationSystem

universe u

/-- A rewrite relation together with the hypotheses required by Newman's lemma. -/
structure System (α : Type u) where
  step : α → α → Prop
  termination : WellFounded (Function.swap step)
  localConfluence : ∀ h a b, step h a → step h b →
    ∃ c, Relation.ReflTransGen step a c ∧ Relation.ReflTransGen step b c

namespace System

/-- The reflexive-transitive reduction relation of a normalization system. -/
def Reachable {α : Type u} (S : System α) : α → α → Prop :=
  Relation.ReflTransGen S.step

/-- The canonical normal form selected by the existing Newman construction. -/
noncomputable def normalForm {α : Type u} (S : System α) (a : α) : α :=
  NormalFormFunction.nf S.step S.termination S.localConfluence a

/-- Every source reaches its canonical normal form. -/
theorem reaches_normalForm {α : Type u} (S : System α) (a : α) :
    S.Reachable a (S.normalForm a) :=
  (NormalFormFunction.nf_spec S.step S.termination S.localConfluence a).1

/-- The canonical endpoint is irreducible. -/
theorem normalForm_isNormal {α : Type u} (S : System α) (a : α) :
    NormalFormConfluence.IsNormalForm S.step (S.normalForm a) :=
  (NormalFormFunction.nf_spec S.step S.termination S.localConfluence a).2

/-- Canonical normalization is idempotent. -/
@[simp]
theorem normalForm_idempotent {α : Type u} (S : System α) (a : α) :
    S.normalForm (S.normalForm a) = S.normalForm a :=
  NormalFormFunction.nf_idempotent S.step S.termination S.localConfluence a

/-- Generated-equivalent sources have the same canonical normal form. -/
theorem normalForm_eq_of_eqvGen {α : Type u} (S : System α) {a b : α}
    (hab : Relation.EqvGen S.step a b) :
    S.normalForm a = S.normalForm b :=
  NormalFormFunction.nf_eq_of_eqvGen S.step S.termination S.localConfluence hab

end System

/-- A proposed normalizer carries both reachability and irreducibility certificates. -/
structure CertifiedNormalizer {α : Type u} (S : System α) where
  run : α → α
  reaches : ∀ a, S.Reachable a (run a)
  normal : ∀ a, NormalFormConfluence.IsNormalForm S.step (run a)

namespace CertifiedNormalizer

/-- The canonical Newman normal-form function is a certified normalizer. -/
noncomputable def canonical {α : Type u} (S : System α) : CertifiedNormalizer S where
  run := S.normalForm
  reaches := S.reaches_normalForm
  normal := S.normalForm_isNormal

/-- Every certified normalizer computes the canonical normal form. -/
theorem run_eq_normalForm {α : Type u} {S : System α}
    (N : CertifiedNormalizer S) : N.run = S.normalForm := by
  funext a
  exact NormalFormConfluence.normal_form_unique_of_confluent
    (D5.S0.Rewriting.NewmanConfluence.newman_confluent
      S.step S.termination S.localConfluence)
    (N.reaches a) (S.reaches_normalForm a)
    (N.normal a) (S.normalForm_isNormal a)

/-- Any two certified normalizers agree extensionally. -/
theorem run_unique {α : Type u} {S : System α}
    (N M : CertifiedNormalizer S) : N.run = M.run :=
  N.run_eq_normalForm.trans M.run_eq_normalForm.symm

end CertifiedNormalizer

/-- Top-level restatement: any two certified normalizers of one system agree
extensionally. -/
theorem certified_normalizer_run_unique {α : Type u} {S : System α}
    (N M : CertifiedNormalizer S) : N.run = M.run :=
  CertifiedNormalizer.run_unique N M

#print axioms System.normalForm_idempotent
#print axioms System.normalForm_eq_of_eqvGen
#print axioms CertifiedNormalizer.run_eq_normalForm
#print axioms CertifiedNormalizer.run_unique
#print axioms certified_normalizer_run_unique

end D5.S0.Rewriting.NormalizationSystem
