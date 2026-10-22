import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Circle.DyadicPrefix

/-!
The three public source telescopes retain all natural parameters and all original
hypotheses. State families are infinite, and occurrence states retain the actual
Fin u subset and list. The readout observes the actual scalar mass; whole-family
variation, sensitivity and observational dependence are proved below. The shared
dependent template is enrolled by Reg.Support.DependentFamily. Raw compiled
source-occurrence reconstruction/sourceSelection remains unspecified, so these
are registration attempts and do not assert a validated binding.
-/

namespace Reg.D5.S3.Combinatorics.Circle.DyadicPrefix

open _root_.D5.S3.Combinatorics.Circle.DyadicPrefix
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false

private abbrev signature (P : Type) (State : P → Type) : DependentFamily.Signature where
  Params := P
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual {P : Type} {State : P → Type} (f : ∀ p, State p → ℕ) :
    DependentFamily.Realization (signature P State) :=
  DependentFamily.realize (signature P State) (fun _ p x => f p x) (fun a => nomatch a)

private abbrev rejected {P : Type} {State : P → Type} :
    DependentFamily.Realization (signature P State) :=
  DependentFamily.realize (signature P State) (fun _ _ _ => 0) (fun a => nomatch a)

private abbrev arena {P : Type} (State : P → Type)
    (law : DependentFamily.Realization (signature P State) → Prop) : DependentFamily.Arena :=
  ⟨signature P State, law⟩

private def familyEvidence {P : Type} {State : P → Type}
    (f : ∀ p, State p → ℕ)
    (law : DependentFamily.Realization (signature P State) → Prop)
    {source : Prop} (bridge : source ↔ law (actual f)) (positive : source)
    (bad : ¬ law rejected) (p : P) (x y : State p) (hxy : f p x ≠ f p y) :
    DependentFamily.Registration (arena State law) source where
  actual := actual f
  bridge := bridge
  variation := ⟨bridge.mp positive, rejected, bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hji
      exact False.elim (hji (Subsingleton.elim j i))
    · intro a
      exact Empty.elim a
  dependence := fun _ => ⟨p, x, y, hxy⟩

namespace Quotient

structure Inputs where
  u : ℕ
  v : ℕ
  a : ℕ
  q : ℕ

def premise (p : Inputs) : Prop :=
  0 < p.u ∧ 0 < p.v ∧ 0 < p.a ∧ Odd p.q ∧
    (2 ^ p.v - 1) * p.q ≤ (2 ^ p.u - 1) * p.a

def capacity (p : Inputs) := 2 ^ (p.u - 1) * p.a + (p.q - 1) / 2

def law (r : DependentFamily.Realization (signature Inputs (fun _ => ℕ))) : Prop :=
  ∀ p, premise p →
    2 ^ (p.v - 1) * p.q ≤ r.readout () p (p.a * (capacity p / p.a)) ∧
    r.readout () p (p.a * (capacity p / p.a)) ≤ capacity p

abbrev sourceScope := type_of% (@quotient_separation)

theorem bridge : sourceScope ↔ law (actual (fun _ x => x)) := by
  constructor
  · intro h p hp
    exact h p.u p.v p.a p.q hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  · intro h u v a q hu hv ha ho hpq
    exact h ⟨u, v, a, q⟩ ⟨hu, hv, ha, ho, hpq⟩

def base : Inputs := ⟨1, 1, 1, 1⟩

theorem base_premise : premise base := by norm_num [premise, base, odd_iff_exists_bit1]

theorem rejected_law : ¬ law rejected := by
  intro h
  have hz := (h base base_premise).1
  norm_num [base, rejected, DependentFamily.realize] at hz

def evidence : DependentFamily.Registration (arena (fun _ : Inputs => ℕ) law) sourceScope :=
  familyEvidence (fun _ x => x) law bridge (@quotient_separation) rejected_law
    base 0 1 (by decide)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@quotient_separation) (DependentFamily.Realization (signature Inputs (fun _ => ℕ))) Type Unit where
  unitName := `D5.S3.Combinatorics.Circle.DyadicPrefix.quotient_separation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.DyadicPrefix.Quotient.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena (fun _ => ℕ) law⟩
  objectArena := .source ⟨arena (fun _ => ℕ) law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (arena (fun _ => ℕ) law) ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize (signature Inputs (fun _ => ℕ))
    (fun _ _ x => x) (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Quotient

namespace Occurrences

structure Inputs where
  u : ℕ
  v : ℕ
  a : ℕ
  q : ℕ
  hu : 0 < u
  hv : 0 < v

def State (p : Inputs) := ℕ × Finset (Fin p.u) × List (Fin p.u)

def premise (p : Inputs) : Prop :=
  0 < p.a ∧ Odd p.q ∧ (2 ^ p.v - 1) * p.q ≤ (2 ^ p.u - 1) * p.a

def law (r : DependentFamily.Realization (signature Inputs State)) : Prop :=
  ∀ p, premise p → ∃ U S order, PrefixSelection p.u p.v p.a p.q
    (2 ^ (p.u - 1) * p.a + (p.q - 1) / 2) p.hu p.hv
    (r.readout () p (U, S, order)) S order

abbrev sourceScope := type_of% (@occurrence_prefix)

theorem bridge : sourceScope ↔ law (actual (fun _ x => x.1)) := by
  constructor
  · intro h p hp
    exact h p.u p.v p.a p.q p.hu p.hv hp.1 hp.2.1 hp.2.2
  · intro h u v a q hu hv ha ho hpq
    exact h ⟨u, v, a, q, hu, hv⟩ ⟨ha, ho, hpq⟩

def base : Inputs := ⟨1, 1, 1, 1, by decide, by decide⟩

theorem base_premise : premise base := by norm_num [premise, base, odd_iff_exists_bit1]

theorem rejected_law : ¬ law rejected := by
  intro h
  obtain ⟨U, S, order, hmass⟩ := h base base_premise
  have hz := hmass.1
  norm_num [base, rejected, DependentFamily.realize] at hz

def evidence : DependentFamily.Registration (arena State law) sourceScope :=
  familyEvidence (fun _ x => x.1) law bridge (@occurrence_prefix) rejected_law
    base (0, ∅, []) (1, ∅, []) (by decide)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@occurrence_prefix) (DependentFamily.Realization (signature Inputs State)) Type Unit where
  unitName := `D5.S3.Combinatorics.Circle.DyadicPrefix.occurrence_prefix.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.DyadicPrefix.Occurrences.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena State law⟩
  objectArena := .source ⟨arena State law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (arena State law) ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize (signature Inputs State)
    (fun _ _ x => x.1) (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Occurrences

namespace Source

structure Inputs where
  u : ℕ
  v : ℕ
  a : ℕ
  q : ℕ
  b : ℕ
  N : ℕ
  C : ℕ
  hu : 0 < u
  hv : 0 < v

def State (p : Inputs) := ℕ × Finset (Fin p.u) × List (Fin p.u)

def premise (p : Inputs) : Prop :=
  0 < p.a ∧ 0 < p.q ∧ 0 < p.b ∧ p.a ≤ p.b ∧ p.N = 2 * p.C + 1 ∧
    p.N = 2 ^ p.u * p.a + p.q ∧ p.N = 2 ^ p.v * p.q + p.b

def facts (p : Inputs) : Prop :=
  Odd p.q ∧
    (((2 ^ p.u - 1) * p.a : ℕ) : ℤ) - (((2 ^ p.v - 1) * p.q : ℕ) : ℤ) =
      (p.b : ℤ) - p.a ∧
    (2 ^ p.v - 1) * p.q ≤ (2 ^ p.u - 1) * p.a ∧
    p.C = 2 ^ (p.u - 1) * p.a + (p.q - 1) / 2 ∧
    2 ^ (p.u - 1) * p.a ≤ p.C ∧ 2 ^ (p.v - 1) * p.q ≤ p.C

def law (r : DependentFamily.Realization (signature Inputs State)) : Prop :=
  ∀ p, premise p → facts p ∧ ∃ U S order,
    PrefixSelection p.u p.v p.a p.q p.C p.hu p.hv (r.readout () p (U, S, order)) S order

abbrev sourceScope := type_of% (@two_run_prefix)

theorem bridge : sourceScope ↔ law (actual (fun _ x => x.1)) := by
  constructor
  · intro h p hp
    obtain ⟨ho, hb, hpq, hc, hl, hm, hw⟩ :=
      h p.u p.v p.a p.q p.b p.N p.C p.hu p.hv hp.1 hp.2.1 hp.2.2.1
        hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2
    exact ⟨⟨ho, hb, hpq, hc, hl, hm⟩, hw⟩
  · intro h u v a q b N C hu hv ha hq hb hba hn h1 h2
    obtain ⟨⟨ho, hbal, hpq, hc, hl, hm⟩, hw⟩ :=
      h ⟨u, v, a, q, b, N, C, hu, hv⟩ ⟨ha, hq, hb, hba, hn, h1, h2⟩
    exact ⟨ho, hbal, hpq, hc, hl, hm, hw⟩

def base : Inputs := ⟨1, 1, 1, 1, 1, 3, 1, by decide, by decide⟩

theorem base_premise : premise base := by norm_num [premise, base]

theorem rejected_law : ¬ law rejected := by
  intro h
  obtain ⟨U, S, order, hmass⟩ := (h base base_premise).2
  have hz := hmass.1
  norm_num [base, rejected, DependentFamily.realize] at hz

def evidence : DependentFamily.Registration (arena State law) sourceScope :=
  familyEvidence (fun _ x => x.1) law bridge (@two_run_prefix) rejected_law
    base (0, ∅, []) (1, ∅, []) (by decide)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@two_run_prefix) (DependentFamily.Realization (signature Inputs State)) Type Unit where
  unitName := `D5.S3.Combinatorics.Circle.DyadicPrefix.two_run_prefix.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.DyadicPrefix.Source.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena State law⟩
  objectArena := .source ⟨arena State law⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (arena State law) ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize (signature Inputs State)
    (fun _ _ x => x.1) (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Source

end Reg.D5.S3.Combinatorics.Circle.DyadicPrefix
