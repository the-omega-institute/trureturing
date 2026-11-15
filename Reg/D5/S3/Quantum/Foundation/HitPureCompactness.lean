import D5.S3.Quantum.Foundation.HitPureCompactness
import Reg.D5.S3.Quantum.Foundation.HitSectionGeneration

/-! Exact source reconstruction for original all-label Hit compactness.
Whole-family intervention, sensitivity, observational dependence and raw source
selection remain unresolved; these bridges do not assert declared_validated
four-slot registration. -/

noncomputable section
universe v

namespace Reg.D5.S3.Quantum.Foundation.HitPureCompactness

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.HitSectionGeneration
open _root_.D5.S3.Quantum.Foundation.HitPureCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.HitSectionGeneration

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
  realize signature (fun _ P S => pure P.cone P.unit ∩ S) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{v}
  Law O := ∀ P : Inputs.{v},
    IsClosed (P.cone : Set P.V) →
    (∀ x ∈ P.cone, x ≠ 0 → 0 < P.unit x) →
    Submodule.span ℝ (P.cone : Set P.V) = ⊤ →
    (∀ a : pure P.cone P.unit, Hit P.cone P.unit a) →
    IsClosed (O.readout () P Set.univ) ∧ IsCompact (O.readout () P Set.univ)

abbrev sourceScope : Prop := type_of% (@hit_pure_closed_compact.{v})

theorem source_bridge : sourceScope.{v} ↔ arena.{v}.Law actual.{v} := by
  constructor
  · intro h P hc hu hg hh
    simpa [actual, realize] using @h P.V P.add P.space P.finite P.cone P.unit hc hu hg hh
  · intro h V add space finite C u hc hu hg hh
    simpa [actual, realize] using h (@Inputs.mk V add space finite C u) hc hu hg hh

theorem actual_positive : arena.{v}.Law actual.{v} :=
  source_bridge.mp (@hit_pure_closed_compact.{v})

#print axioms hit_pure_closed_compact
#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Quantum.Foundation.HitPureCompactness
