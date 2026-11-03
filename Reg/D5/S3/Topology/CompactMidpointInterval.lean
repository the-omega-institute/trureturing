import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.CompactMidpointInterval

/-!
# Source family for compact midpoint intervals

The source family retains the space universe, its extended metric and compact
topology, and both selected endpoints. The identity readout preserves the
entire candidate map and every time pair. The source bridge and positive law
are partial audit evidence. A four-slot registration additionally requires
whole-family variation, sensitivity, observational dependence, and the raw
source-coordinate reconstruction and occurrence ties.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal

noncomputable section

namespace Reg.D5.S3.Topology.CompactMidpointInterval

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev sourceScope.{u} :=
  type_of% (@_root_.D5.S3.Topology.CompactMidpointInterval.compact_midpoints_isometric_interval.{u})

structure Inputs.{u} where
  Y : Type u
  metric : EMetricSpace Y
  compact : @CompactSpace Y metric.toUniformSpace.toTopologicalSpace
  first : Y
  last : Y

abbrev length.{u} (P : Inputs.{u}) : ℝ :=
  letI := P.metric
  (edist P.first P.last).toReal

abbrev maps.{u} (P : Inputs.{u}) := Set.Icc (0 : ℝ) (length P) → P.Y

abbrev signature.{u} : Signature where
  Params := Inputs.{u}
  State := maps
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => maps
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u} : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev arena.{u} : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.metric
    (∀ a b : P.Y, edist a b < ⊤ →
      ∃ z : P.Y, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2) →
    edist P.first P.last < ⊤ →
    ∃ f : maps P, Isometry (R.readout () P f) ∧
      R.readout () P f ⟨0, ⟨le_rfl, ENNReal.toReal_nonneg⟩⟩ = P.first ∧
      R.readout () P f
        ⟨length P, ⟨ENNReal.toReal_nonneg, le_rfl⟩⟩ = P.last

theorem source_bridge.{u} : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.metric
    letI := P.compact
    exact fun hmid hfinite => h hmid P.first P.last hfinite
  · intro h Y metric compact hmid a b hfinite
    exact h ⟨Y, metric, compact, a, b⟩ hmid hfinite

theorem actual_positive.{u} : arena.{u}.Law actual.{u} :=
  source_bridge.mp
    (@_root_.D5.S3.Topology.CompactMidpointInterval.compact_midpoints_isometric_interval.{u})

#print axioms source_bridge
#print axioms actual_positive

end Reg.D5.S3.Topology.CompactMidpointInterval
