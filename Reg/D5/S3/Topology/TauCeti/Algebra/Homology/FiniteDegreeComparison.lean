import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.TauCeti.Algebra.Homology.FiniteDegreeComparison

/-!
# Original source family for finite-degree bicomplex comparison

The telescope retains independent object and morphism universes, the category
and abelian dictionaries, the natural cutoff, both native bicomplexes and the
actual morphism. Both triangular column hypotheses belong to the law. The
readout observes the actual total homology isomorphisms and boundary epimorphism.

The source equivalence and actual positive law are supplied. Whole-family
variation, role sensitivity, actual observational dependence, enrolled source
selection and raw occurrence reconstruction are not supplied. These source
bridges do not constitute a completed four-slot registration. The missing
evidence is specified in
https://github.com/the-omega-institute/trureturing/issues/24858#issuecomment-6553560856.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open CategoryTheory HomologicalComplex
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Reg.D5.S3.Topology.TauCeti.Algebra.Homology.FiniteDegreeComparison

abbrev sourceScope.{v, u} :=
  type_of% (@HomologicalComplex₂.finite_degree_comparison_total_map.{v, u})

theorem source_actual.{v, u} : sourceScope.{v, u} :=
  @HomologicalComplex₂.finite_degree_comparison_total_map.{v, u}

structure Inputs.{v, u} where
  C : Type u
  category : Category.{v} C
  abelian : @Abelian C category
  k : ℕ
  K : letI := category; letI := abelian
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  L : letI := category; letI := abelian
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)

attribute [instance] Inputs.category Inputs.abelian

abbrev State.{v, u} (p : Inputs.{v, u}) := p.K ⟶ p.L

def isoPremise.{v, u} (p : Inputs.{v, u}) (φ : State p) : Prop :=
  ∀ a b : ℕ, a + b ≤ p.k → IsIso (homologyMap (φ.f a) b)

def epiPremise.{v, u} (p : Inputs.{v, u}) (φ : State p) : Prop :=
  ∀ a b : ℕ, a + b = p.k + 1 → Epi (homologyMap (φ.f a) b)

def signature.{v, u} : DependentFamily.Signature where
  Params := Inputs.{v, u}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ ↦ (ℕ → Prop) × Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{v, u} : DependentFamily.Realization signature.{v, u} :=
  DependentFamily.realize signature
    (fun _ (p : Inputs.{v, u}) (φ : State p) ↦
      letI := p.category
      letI := p.abelian
      (fun n ↦ IsIso (homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n),
        Epi (homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) (p.k + 1))))
    (fun e ↦ nomatch e)

def arena.{v, u} : DependentFamily.Arena where
  signature := signature.{v, u}
  Law r := ∀ p φ, isoPremise p φ → epiPremise p φ →
    (∀ n, n ≤ p.k → (r.readout () p φ).1 n) ∧ (r.readout () p φ).2

theorem source_bridge.{v, u} : sourceScope.{v, u} ↔ arena.{v, u}.Law actual := by
  constructor
  · intro h p φ hi he
    exact h p.k φ hi he
  · intro h C category abelian K L k φ hi he
    exact h ⟨C, category, abelian, k, K, L⟩ φ hi he

theorem actual_positive.{v, u} : arena.{v, u}.Law actual :=
  source_bridge.mp source_actual

end Reg.D5.S3.Topology.TauCeti.Algebra.Homology.FiniteDegreeComparison
