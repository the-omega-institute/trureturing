import D5.S3.Quantum.Foundation.HitSectionGeneration
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact original-domain source reconstruction for finite pure generation and all
three section conclusions. Whole-family variation, sensitivity, observational
dependence and raw source selection for a complete four-slot registration remain
unresolved; these bridges do not assert declared_validated registration. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.HitSectionGeneration

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.HitSectionGeneration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  V : Type v
  [add : NormedAddCommGroup V]
  [space : NormedSpace ℝ V]
  [finite : FiniteDimensional ℝ V]
  cone : PointedCone ℝ V
  unit : V →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

namespace PureGeneration

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Set P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P S => base P.cone P.unit ∩ S) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    O.readout () P Set.univ = convexHull ℝ (pure P.cone P.unit)

abbrev sourceScope : Prop := type_of% (@base_eq_convexHull_pure.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hu
    simpa [actual, realize] using @h P.V P.add P.space P.cone P.unit P.finite hc hu
  · intro h V add space C u finite hc hu
    simpa [actual, realize] using h (@Inputs.mk V add space finite C u) hc hu

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@base_eq_convexHull_pure.{v})

end PureGeneration

namespace Section

abbrev signature : Signature where
  Params := Inputs.{v}
  State P := Submodule ℝ P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Set P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} :=
  realize signature (fun _ P S => base P.cone P.unit ∩ (S : Set P.V))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    ∀ (a : pure P.cone P.unit), Hit P.cone P.unit a →
    ∀ (S : Submodule ℝ P.V), neighbors P.cone P.unit a ⊆ S →
    (O.readout () P S).extremePoints ℝ = pure P.cone P.unit ∩ S ∧
    O.readout () P S = convexHull ℝ (pure P.cone P.unit ∩ S) ∧
    (P.cone : Set P.V) ∩ S =
      (PointedCone.hull ℝ (pure P.cone P.unit ∩ S) : Set P.V)

abbrev sourceScope : Prop := type_of% (@hit_section_generation.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hu a hh S hS
    exact @h P.V P.add P.space P.cone P.unit P.finite hc hu a hh S hS
  · intro h V add space C u finite hc hu a hh S hS
    exact h (@Inputs.mk V add space finite C u) hc hu a hh S hS

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@hit_section_generation.{v})

end Section

#print axioms base_eq_convexHull_pure
#print axioms hit_section_generation
#print axioms PureGeneration.source_bridge
#print axioms Section.source_bridge

end Reg.D5.S3.Quantum.Foundation.HitSectionGeneration
