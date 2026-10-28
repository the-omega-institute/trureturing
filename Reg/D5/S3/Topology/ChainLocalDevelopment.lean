import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ChainLocalDevelopment

/-! The original source family and identity readout preserve all candidate maps.
The source equivalence and positive law are partial registration evidence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace Reg.D5.S3.Topology.ChainLocalDevelopment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev sourceScope.{u,v,w,z} := type_of%
  (@_root_.D5.S3.Topology.ChainLocalDevelopment.local_development_distance_le.{u,v,w,z})

structure Inputs.{u,v,w,z} where
  I : Type u
  J : Type v
  X : I → Type w
  metric : ∀ i, EMetricSpace (X i)
  Y : Type z
  outputMetric : EMetricSpace Y
  G : @_root_.D5.S3.Topology.FiniteOrbitChainMetric.Datum I J X metric
  center : Sigma X
  f : Sigma X → Y
  radius : ℝ≥0

abbrev maps.{u,v,w,z} (P : Inputs.{u,v,w,z}) := Sigma P.X → P.Y

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

abbrev arena.{u,v,w,z} : Arena where
  signature := signature.{u,v,w,z}
  Law R := ∀ P : Inputs.{u,v,w,z},
    letI := P.metric
    letI := P.outputMetric
    (∀ b c, P.G.Rel b c → P.f b = P.f c) →
    0 < P.radius →
    (∀ i (c : P.X i), P.G.Rel P.center ⟨i,c⟩ → ∀ x y : P.X i,
      edist c x < (P.radius : ℝ≥0∞)+P.radius+P.radius →
      edist c y < (P.radius : ℝ≥0∞)+P.radius+P.radius →
      edist (P.f ⟨i,x⟩) (P.f ⟨i,y⟩) ≤ edist x y) →
    (∀ j (c : P.X (P.G.src j)), P.G.Rel P.center ⟨P.G.src j,c⟩ →
      ∀ x : P.G.dom j,
      edist c x.val < (P.radius : ℝ≥0∞)+P.radius+P.radius → c ∈ P.G.dom j) →
    (∀ j (c : P.X (P.G.dst j)), P.G.Rel P.center ⟨P.G.dst j,c⟩ →
      ∀ x : P.G.ran j,
      edist c x.val < (P.radius : ℝ≥0∞)+P.radius+P.radius → c ∈ P.G.ran j) →
    ∀ (x y : Sigma P.X) (cx : P.X x.1) (cy : P.X y.1),
    P.G.Rel P.center ⟨x.1,cx⟩ → P.G.Rel P.center ⟨y.1,cy⟩ →
    edist cx x.2 < (P.radius : ℝ≥0∞) → edist cy y.2 < (P.radius : ℝ≥0∞) →
    edist (R.readout () P P.f x) (R.readout () P P.f y) ≤ P.G.distance x y

theorem source_bridge.{u,v,w,z} : sourceScope.{u,v,w,z} ↔ arena.{u,v,w,z}.Law actual.{u,v,w,z} := by
  constructor
  · intro h P
    letI := P.metric
    letI := P.outputMetric
    intro hd hr hLip hF hB x y cx cy hcx hcy hx hy
    exact h P.G P.center P.f hd P.radius hr hLip hF hB x y cx cy hcx hcy hx hy
  · intro h I J X metric G Y outputMetric a f hdesc r hr hLip hF hB x y cx cy hcx hcy hx hy
    exact h ⟨I,J,X,metric,Y,outputMetric,G,a,f,r⟩ hdesc hr hLip hF hB x y cx cy hcx hcy hx hy

theorem actual_positive.{u,v,w,z} : arena.{u,v,w,z}.Law actual.{u,v,w,z} :=
  source_bridge.mp
    (@_root_.D5.S3.Topology.ChainLocalDevelopment.local_development_distance_le.{u,v,w,z})

#print axioms source_bridge
#print axioms actual_positive
end Reg.D5.S3.Topology.ChainLocalDevelopment
