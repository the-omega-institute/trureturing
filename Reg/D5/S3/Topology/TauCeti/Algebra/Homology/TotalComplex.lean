import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex

/-!
# Original source family for row-to-total comparison

The telescope retains independent object and morphism universes, both category
dictionaries, both first-quadrant bicomplexes, the actual morphism and its row
premise. The readout observes the map induced by that morphism on native total
homology. The row premise belongs to the law, not to the state space.

The exact source equivalence and positive law are supplied. Whole-family
variation, sensitivity, actual observational dependence, enrolled source
selection and raw occurrence reconstruction are unfinished. No completed
four-slot registration is asserted. The remaining obligations are described in
https://github.com/the-omega-institute/trureturing/issues/24858.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open CategoryTheory HomologicalComplex
open _root_.D5.S3.ConceptDynamics.InformationEscape

namespace Reg.D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex

abbrev sourceScope.{v, u} :=
  type_of% (@HomologicalComplex₂.quasiIso_total_map_of_rows.{v, u})

theorem source_actual.{v, u} : sourceScope.{v, u} :=
  @HomologicalComplex₂.quasiIso_total_map_of_rows.{v, u}

structure Inputs.{v, u} where
  C : Type u
  category : Category.{v} C
  abelian : @Abelian C category
  K : letI := category; letI := abelian
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)
  L : letI := category; letI := abelian
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)

attribute [instance] Inputs.category Inputs.abelian

abbrev State.{v, u} (p : Inputs.{v, u}) := p.K ⟶ p.L

def rowPremise.{v, u} (p : Inputs.{v, u}) (φ : State p) : Prop :=
  ∀ q : ℕ, QuasiIso (((eval p.C (ComplexShape.down ℕ) q).mapHomologicalComplex
    (ComplexShape.down ℕ)).map φ)

def signature.{v, u} : DependentFamily.Signature where
  Params := Inputs.{v, u}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ ↦ ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{v, u} : DependentFamily.Realization signature.{v, u} :=
  DependentFamily.realize signature
    (fun _ (p : Inputs.{v, u}) (φ : State p) n ↦
      letI := p.category
      letI := p.abelian
      IsIso (homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n))
    (fun e ↦ nomatch e)

def arena.{v, u} : DependentFamily.Arena where
  signature := signature.{v, u}
  Law r := ∀ p φ, rowPremise p φ → ∀ n, r.readout () p φ n

theorem source_bridge.{v, u} : sourceScope.{v, u} ↔ arena.{v, u}.Law actual := by
  constructor
  · intro h p φ hφ n
    letI := p.category
    letI := p.abelian
    change IsIso (homologyMap (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n)
    have : QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
      h φ hφ
    infer_instance
  · intro h C category abelian K L φ hφ
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact h ⟨C, category, abelian, K, L⟩ φ hφ n

theorem actual_positive.{v, u} : arena.{v, u}.Law actual :=
  source_bridge.mp source_actual

end Reg.D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex


/-! # Source scopes of the exposed homology-transfer interfaces

These exact source types and their positive evidence retain all category,
shape, degree and short-exactness parameters. They supply no variation,
sensitivity, observational dependence or completed registration. The existing
row-to-total source family and its issue reference remain unchanged. The
exposed source obligations are specified in
https://github.com/the-omega-institute/trureturing/issues/24858#issuecomment-6553560856.
-/

namespace Reg.D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex.Exposed

abbrev epi_transfer_scope.{a, b, c} :=
  type_of% (@HomologicalComplex.HomologySequence.epi_homologyMap_τ₂.{a, b, c})
theorem epi_transfer_actual.{a, b, c} : epi_transfer_scope.{a, b, c} :=
  @HomologicalComplex.HomologySequence.epi_homologyMap_τ₂.{a, b, c}

abbrev iso_transfer_scope.{a, b, c} :=
  type_of% (@HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂.{a, b, c})
theorem iso_transfer_actual.{a, b, c} : iso_transfer_scope.{a, b, c} :=
  @HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂.{a, b, c}

abbrev epi_extension_scope.{a, b, c, d} := type_of% (@HomologicalComplex.epi_homologyMap_extendMap_iff.{a, b, c, d})
theorem epi_extension_actual.{a, b, c, d} : epi_extension_scope.{a, b, c, d} :=
  @HomologicalComplex.epi_homologyMap_extendMap_iff.{a, b, c, d}

abbrev iso_extension_zero_scope.{a, b, c, d} :=
  type_of% (@HomologicalComplex.isIso_homologyMap_extendMap_of_forall_ne.{a, b, c, d})
theorem iso_extension_zero_actual.{a, b, c, d} : iso_extension_zero_scope.{a, b, c, d} :=
  @HomologicalComplex.isIso_homologyMap_extendMap_of_forall_ne.{a, b, c, d}

abbrev short_exact_scope.{a, b} := type_of% (@HomologicalComplex₂.rowZeroShortComplex_shortExact.{a, b})
theorem short_exact_actual.{a, b} : short_exact_scope.{a, b} :=
  @HomologicalComplex₂.rowZeroShortComplex_shortExact.{a, b}

end Reg.D5.S3.Topology.TauCeti.Algebra.Homology.TotalComplex.Exposed
