/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The DESC commitment has exactly five indexed atoms and its stated scope boundary. -/

import D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentSettlement
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-08-27):
   * `rg -n -i 'SpectrumCommitmentScope|spectrum_commitment_atom_family_and_scope|
     spectrum_atom_index_bijective|inductive SpectrumAtom|largerBoundaryLanguage'
     D5 --glob '*.lean'` found no existing atom-family or scope declaration.
   * The frozen `SpectrumCommitmentSettlement` module owns the seven-field
     record and fixed-cutoff functions. This module instantiates that record;
     it does not define a competing commitment or settlement mechanism.
   * Searches of pinned Mathlib v4.31.0 for `SpectrumCommitment`,
     `SpectrumAtom`, and the combined five-atom scope statement found no hit.
     `Fintype.bijective_iff_injective_and_card` and `Fintype.card_fin` supply
     the generic finite-cardinality bridge used below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope

open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentSettlement

-- Lean 4.33's stricter type check breaks mathlib's `Fintype` deriving handler.
section
set_option backward.isDefEq.respectTransparency.types false

/-- The five frozen DESC v1.0 theorem atoms, in T1--T5 order. -/
inductive SpectrumAtom
  | t1
  | t2
  | t3
  | t4
  | t5
  deriving DecidableEq, Fintype

end

/-- Scope classes distinguished by the local commitment. -/
inductive ScopeClass
  | finiteLanguage
  | countableLanguage
  | largerBoundaryLanguage
  deriving DecidableEq

/-- The unique position of each named DESC atom in the frozen five-atom
settlement family. -/
def SpectrumAtom.index : SpectrumAtom -> Fin 5
  | .t1 => 0
  | .t2 => 1
  | .t3 => 2
  | .t4 => 3
  | .t5 => 4

/-- All five named atoms form the local atom family. -/
def allSpectrumAtoms : Finset SpectrumAtom := Finset.univ

/-- Main-theorem scopes are finite or countable. The T4 boundary atom also
admits the explicitly larger countermodel scope. -/
def scopePermitted : SpectrumAtom -> ScopeClass -> Bool
  | .t4, .largerBoundaryLanguage => true
  | _, .largerBoundaryLanguage => false
  | _, .finiteLanguage => true
  | _, .countableLanguage => true

/-- Instantiate the frozen seven-field commitment with the named DESC atom
family and its scope contract, leaving the sibling metadata fields explicit. -/
def descSpectrumCommitment
    {Baseline WeightSpec TestPlan : Type*}
    (baseline : Baseline) (weightSpec : WeightSpec) (testPlan : TestPlan) :
    SpectrumCommitment
      (Finset SpectrumAtom)
      (SpectrumAtom -> ScopeClass -> Bool)
      Baseline WeightSpec TestPlan :=
  localSpectrumCommitment
    allSpectrumAtoms scopePermitted baseline weightSpec testPlan

/-- The named T1--T5 atoms index the frozen five settlement positions without
collision or omission. -/
theorem spectrum_atom_index_bijective :
    Function.Bijective SpectrumAtom.index := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro left right equalIndex
    cases left <;> cases right <;> simp_all [SpectrumAtom.index]
  · decide

/-- The local commitment contains exactly the five T1--T5 atoms. Every atom
admits finite and countable theorem scopes, while a larger boundary scope is
admitted exactly for T4. -/
theorem spectrum_commitment_atom_family_and_scope
    {Baseline WeightSpec TestPlan : Type*}
    (baseline : Baseline) (weightSpec : WeightSpec) (testPlan : TestPlan) :
    let commitment := descSpectrumCommitment baseline weightSpec testPlan
    commitment.atomFamily.card = 5 /\
      Function.Bijective SpectrumAtom.index /\
      (forall atom, atom ∈ commitment.atomFamily) /\
      (forall atom,
        commitment.scope atom .finiteLanguage = true /\
          commitment.scope atom .countableLanguage = true) /\
      commitment.scope .t4 .largerBoundaryLanguage = true /\
      (forall atom,
        commitment.scope atom .largerBoundaryLanguage = true <->
          atom = .t4) := by
  dsimp only [descSpectrumCommitment, localSpectrumCommitment]
  refine ⟨?_, spectrum_atom_index_bijective, ?_, ?_, ?_, ?_⟩
  · decide
  · intro atom
    exact Finset.mem_univ atom
  · intro atom
    cases atom <;> decide
  · rfl
  · intro atom
    cases atom <;> decide

/- The atom family is inhabited and the larger-language branch is genuinely
selective rather than a vacuous all-scopes predicate. -/
example : SpectrumAtom := .t1

example :
    scopePermitted .t4 .largerBoundaryLanguage = true /\
      scopePermitted .t1 .largerBoundaryLanguage = false := by
  decide

/- The generic theorem has a concrete, premise-free Unit instantiation. -/
example :
    let commitment := descSpectrumCommitment () () ()
    commitment.atomFamily.card = 5 :=
  (spectrum_commitment_atom_family_and_scope () () ()).1

#print axioms spectrum_commitment_atom_family_and_scope

end D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
