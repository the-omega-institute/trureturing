import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ChainSourceLocalIsometry

/-! The full source family and identity readout retain the complete maps at all
positive and zero radii. Source equivalence and the actual law are partial
registration evidence; variation, sensitivity and source binding remain separate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace Reg.D5.S3.Topology.ChainSourceLocalIsometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev sourceScope.{u,v,w,z} := type_of%
  (@_root_.D5.S3.Topology.ChainSourceLocalIsometry.original_chain_local_source_isometry.{u,v,w,z})

structure Inputs.{u,v,w,z} where
  I : Type u
  J : Type v
  X : I → Type w
  metric : ∀ i, EMetricSpace (X i)
  Y : Type z
  outputMetric : EMetricSpace Y
  G : @_root_.D5.S3.Topology.FiniteOrbitChainMetric.Datum I J X metric
  q : Sigma X → Y
  U : Set (Sigma X)
  point : Sigma X

abbrev maps.{u,v,w,z} (P : Inputs.{u,v,w,z}) :=
  letI := P.metric
  (r : ℝ≥0) → Metric.eball P.point.2 (r : ℝ≥0∞) → P.Y

abbrev signature.{u,v,w,z} : Signature where
  Params := Inputs.{u,v,w,z}
  State := maps
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => maps
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,v,w,z} : Realization signature.{u,v,w,z} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev canonicalMap.{u,v,w,z} (P : Inputs.{u,v,w,z}) : maps P :=
  letI := P.metric
  fun _ x => P.q ⟨P.point.1,x.val⟩

abbrev arena.{u,v,w,z} : Arena where
  signature := signature.{u,v,w,z}
  Law R := ∀ P : Inputs.{u,v,w,z},
    letI := P.metric
    letI := P.outputMetric
    (∀ a b, edist (P.q a) (P.q b) = P.G.distance a b) →
    IsOpen P.U →
    (∀ j (x : P.G.dom j), (⟨P.G.src j,x.val⟩ : Sigma P.X) ∉ P.U) →
    (∀ j (x : P.G.ran j), (⟨P.G.dst j,x.val⟩ : Sigma P.X) ∉ P.U) →
    P.point ∈ P.U →
    ∃ r : ℝ≥0, 0 < r ∧ Isometry (R.readout () P (canonicalMap P) r)

theorem source_bridge.{u,v,w,z} : sourceScope.{u,v,w,z} ↔ arena.{u,v,w,z}.Law actual.{u,v,w,z} := by
  constructor
  · intro h P
    letI := P.metric
    letI := P.outputMetric
    intro hq hU hs ht ha
    exact h P.G P.q hq P.U hU hs ht P.point ha
  · intro h I J X metric G Y outputMetric q hq U hU hs ht a ha
    exact h ⟨I,J,X,metric,Y,outputMetric,G,q,U,a⟩ hq hU hs ht ha

theorem actual_positive.{u,v,w,z} : arena.{u,v,w,z}.Law actual.{u,v,w,z} :=
  source_bridge.mp
    (@_root_.D5.S3.Topology.ChainSourceLocalIsometry.original_chain_local_source_isometry.{u,v,w,z})

#print axioms source_bridge
#print axioms actual_positive
end Reg.D5.S3.Topology.ChainSourceLocalIsometry
