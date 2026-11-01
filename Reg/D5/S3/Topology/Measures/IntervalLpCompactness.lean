import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.IntervalLpCompactness

/-!
# Dependent source families for interval mesh approximation and compactness

Both families retain the target universe, the original normed-space and
completeness dictionaries, real interval data and the complete function or
Lp-set state. The identity observations preserve the actual source objects.
The equivalence bridges and positive laws are partial audit evidence.
Whole-family variation, sensitivity, observational dependence and exact raw
sourceSelection evidence are additional obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal

namespace Reg.D5.S3.Topology.Measures.IntervalLpCompactness

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Topology.Measures.IntervalLpCompactness

universe u

structure SpaceData where
  E : Type u
  normed : NormedAddCommGroup E
  scalar : letI := normed; NormedSpace ℝ E
  complete : letI := normed; CompleteSpace E

namespace Mesh

structure Inputs where
  space : SpaceData.{u}
  width : ℝ
  count : ℕ
  exponent : ℝ

abbrev functions (P : Inputs.{u}) := ℝ → P.space.E

abbrev signature : Signature where
  Params := Inputs.{u}
  State := functions
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => functions
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    0 < P.width → ∀ f : functions P,
    IntegrableOn f (Ioc 0 (P.count*P.width)) → StronglyMeasurable f → 1 ≤ P.exponent →
    ∫⁻ t in Ioc 0 (P.count*P.width),
      ‖R.readout () P f t - meshAverage P.width P.count (R.readout () P f) t‖ₑ ^ P.exponent ≤
    (ENNReal.ofReal P.width)⁻¹ * (2 *
      ∫⁻ h in Ioc 0 P.width, ∫⁻ t in Ioc 0 (P.count*P.width-h),
        ‖R.readout () P f (t+h) - R.readout () P f t‖ₑ ^ P.exponent)

abbrev sourceScope := type_of% (@mesh_error_le.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    intro hd f hf hm hq
    exact h hd P.count hf hm hq
  · intro h E normed scalar complete d hd N f hf hm q hq
    exact h ⟨⟨E,normed,scalar,complete⟩,d,N,q⟩ hd f hf hm hq

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@mesh_error_le.{u})

end Mesh

namespace Compactness

structure Inputs where
  space : SpaceData.{u}
  time : ℝ
  exponent : ℝ≥0∞
  atLeastOne : Fact (1 ≤ exponent)

abbrev family (P : Inputs.{u}) :=
  letI := P.space.normed
  letI := P.atLeastOne
  Set (Lp P.space.E P.exponent (volume.restrict (Ioc 0 P.time)))

abbrev signature : Signature where
  Params := Inputs.{u}
  State := family
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => family
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ S => S) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    letI := P.atLeastOne
    0 < P.time → P.exponent ≠ ∞ → ∀ S : family P,
    (∀ a b : ℝ, 0 ≤ a → a < b → b ≤ P.time →
      IsCompact (closure ((fun f : Lp P.space.E P.exponent (volume.restrict (Ioc 0 P.time)) =>
        ∫ t in Ioc a b, f t) '' S))) →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < h → h < δ → h < P.time →
        ∀ f ∈ S, eLpNorm (fun t => f (t+h)-f t) P.exponent
          (volume.restrict (Ioc 0 (P.time-h))) < ENNReal.ofReal ε) →
    IsCompact (closure (R.readout () P S))

abbrev sourceScope := type_of% (@isCompact_closure_of_integrals_translations.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    letI := P.atLeastOne
    exact fun hT hp S hint htrans => h hT hp S hint htrans
  · intro h E normed scalar complete p atLeastOne T hT hp S hint htrans
    exact h ⟨⟨E,normed,scalar,complete⟩,T,p,atLeastOne⟩ hT hp S hint htrans

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@isCompact_closure_of_integrals_translations.{u})

end Compactness

end Reg.D5.S3.Topology.Measures.IntervalLpCompactness
