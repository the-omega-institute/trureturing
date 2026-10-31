import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.TauCeti.Algebra.Homology.OrderedCechCover

/-!
# Exact source family for the ordered cover augmentation

The original telescope retains all three universes, all category dictionaries,
the actual cover and the actual augmentation. The readout tests the forward map
of a candidate homotopy equivalence against that augmentation. The exact source
binding and family-law equivalence are partial evidence. Whole-family variation,
sensitivity, actual observational dependence and raw source selection are not
asserted; this source declares no completed four-slot registration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open CategoryTheory Limits
open _root_.TauCeti.OrderedCover
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Reg.D5.S3.Topology.TauCeti.Algebra.Homology.OrderedCechCover

abbrev sourceScope.{w, v, u} := type_of% (@_root_.TauCeti.OrderedCover.augmentation_homotopy_equiv.{w, v, u})

theorem source_actual.{w, v, u} : sourceScope.{w, v, u} :=
  @_root_.TauCeti.OrderedCover.augmentation_homotopy_equiv.{w, v, u}

structure Inputs.{w, v, u} where
  C : Type u
  category : Category.{v} C
  coproducts : @HasCoproducts.{w, v, u} C category
  preadditive : @Preadditive C category
  zero : @HasZeroObject C category
  iota : Type w
  A : Type w
  order : LinearOrder iota
  R : C
  P : iota → Set A
  cover : ⋃ i, P i = Set.univ

attribute [instance] Inputs.category Inputs.coproducts Inputs.preadditive Inputs.zero Inputs.order

def Candidate.{w, v, u} (p : Inputs.{w, v, u}) :=
  HomotopyEquiv (complex p.R p.P) ((ChainComplex.single₀ p.C).obj (∐ fun _ : p.A ↦ p.R))

def certificate.{w, v, u} (p : Inputs.{w, v, u}) (E : Candidate p) : Prop :=
  E.hom = augmentation p.R p.P

def signature.{w, v, u} : DependentFamily.Signature where
  Params := Inputs.{w, v, u}
  State := Candidate
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ ↦ Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{w, v, u} : DependentFamily.Realization signature.{w, v, u} :=
  DependentFamily.realize signature (fun _ p E ↦ certificate p E) (fun e ↦ nomatch e)

def arena.{w, v, u} : DependentFamily.Arena where
  signature := signature.{w, v, u}
  Law r := ∀ p, ∃ E, r.readout () p E

theorem source_bridge.{w, v, u} : sourceScope.{w, v, u} ↔ arena.{w, v, u}.Law actual := by
  constructor
  · intro h p
    letI := p.category
    letI := p.coproducts
    letI := p.preadditive
    letI := p.zero
    letI := p.order
    exact h p.R p.P p.cover
  · intro h C category coproducts iota A R P preadditive order zero cover
    exact h ⟨C, category, coproducts, preadditive, zero, iota, A, order, R, P, cover⟩

theorem actual_positive.{w, v, u} : arena.{w, v, u}.Law actual :=
  source_bridge.mp source_actual

end Reg.D5.S3.Topology.TauCeti.Algebra.Homology.OrderedCechCover
