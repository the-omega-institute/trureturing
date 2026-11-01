import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.IntervalLInfinityRepresentative

/-!
# Source families for interval-average consistency and continuous representatives

The parameters retain arbitrary target universes, normed-space and completeness dictionaries,
and all real interval data. The states are the original functions or sets of L-infinity classes.
The identity readouts reconstruct the full source statements. The positive laws and equivalence
bridges below do not establish whole-family variation or sensitivity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace Reg.D5.S3.Topology.Measures.IntervalLInfinityRepresentative

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Topology.Measures.IntervalLInfinityRepresentative

universe u

structure SpaceData where
  E : Type u
  normed : NormedAddCommGroup E
  scalar : letI := normed; NormedSpace ℝ E
  complete : letI := normed; CompleteSpace E

namespace Averages

structure Inputs where
  space : SpaceData.{u}
  time : ℝ
  scale : ℝ
  error : ℝ
  leftA : ℝ
  rightA : ℝ
  leftB : ℝ
  rightB : ℝ

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
  realize signature (fun _ _ f => f) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    ∀ f : functions P, StronglyMeasurable f → 0 ≤ P.error →
    IntegrableOn f (Ioc 0 P.time) →
    (∀ h : ℝ, 0 < h → h < P.scale → h < P.time →
      eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (P.time-h))) <
        ENNReal.ofReal P.error) →
    0 ≤ P.leftA → P.leftA < P.rightA → P.rightA ≤ P.time →
    0 ≤ P.leftB → P.leftB < P.rightB → P.rightB ≤ P.time →
    (∀ x ∈ Ioc P.leftA P.rightA, ∀ y ∈ Ioc P.leftB P.rightB, |y-x| < P.scale) →
    dist (⨍ x in Ioc P.leftA P.rightA, R.readout () P f x)
      (⨍ y in Ioc P.leftB P.rightB, R.readout () P f y) ≤ P.error

abbrev sourceScope := type_of% (@local_average_consistency.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    intro f hf he hi ht ha hab hb hc hcd hd hclose
    exact h hf he hi ht ha hab hb hc hcd hd hclose
  · intro h E normed scalar complete f hf T δ ε he hi ht a b c d ha hab hb hc hcd hd hclose
    exact h ⟨⟨E,normed,scalar,complete⟩,T,δ,ε,a,b,c,d⟩
      f hf he hi ht ha hab hb hc hcd hd hclose

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@local_average_consistency.{u})

theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let P : Inputs.{u} :=
    ⟨⟨ULift.{u} ℝ,inferInstance,inferInstance,inferInstance⟩,1,1,1,0,1,0,1⟩
  refine ⟨P,fun _ => ⟨0⟩,fun t => ⟨t⟩,?_⟩
  intro heq
  have he := congrArg (fun f : functions P => (f 1).down) heq
  exact zero_ne_one he

end Averages

namespace Representatives

structure Inputs where
  space : SpaceData.{u}
  time : ℝ

abbrev family (P : Inputs.{u}) :=
  letI := P.space.normed
  Set (Lp P.space.E ∞ (volume.restrict (Ioc 0 P.time)))

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
  realize signature (fun _ _ S => S) (fun a => nomatch a)

abbrev conclusion (P : Inputs.{u}) (hT : 0 < P.time) (S : family P) : Prop :=
  letI := P.space.normed
  letI := P.space.scalar
  letI := P.space.complete
  ∃ R : S → C(Icc (0 : ℝ) P.time, P.space.E),
    (∀ f : S, (fun t => R f (projIcc 0 P.time hT.le t))
      =ᵐ[volume.restrict (Ioc 0 P.time)] (f.1 : ℝ → P.space.E)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ f : S,
      ∀ x y : Icc (0 : ℝ) P.time, dist x y < η → dist (R f x) (R f y) < ε) ∧
    (∀ f : S, ∀ g : C(Icc (0 : ℝ) P.time, P.space.E),
      (fun t => g (projIcc 0 P.time hT.le t))
        =ᵐ[volume.restrict (Ioc 0 P.time)] (f.1 : ℝ → P.space.E) → g = R f) ∧
    (∀ f : S, ∀ v : ℝ → P.space.E,
      v =ᵐ[volume.restrict (Ioc 0 P.time)] (f.1 : ℝ → P.space.E) →
      ((fun t => R f (projIcc 0 P.time hT.le t))
        =ᵐ[volume.restrict (Ioc 0 P.time)] v) ∧
      ∀ h : ℝ, 0 < h → h < P.time →
        eLpNorm (fun t => v (t+h)-v t) ∞ (volume.restrict (Ioc 0 (P.time-h))) =
          eLpNorm (fun t => f.1 (t+h)-f.1 t) ∞ (volume.restrict (Ioc 0 (P.time-h))))

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    ∀ hT : 0 < P.time, ∀ S : family P,
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ f ∈ S, ∀ h : ℝ, 0 < h → h < δ → h < P.time →
        eLpNorm (fun t => f (t+h)-f t) ∞ (volume.restrict (Ioc 0 (P.time-h))) <
          ENNReal.ofReal ε) →
    conclusion P hT (R.readout () P S)

abbrev sourceScope := type_of% (@exists_continuous_representatives.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.space.normed
    letI := P.space.scalar
    letI := P.space.complete
    exact fun hT S ht => h hT S ht
  · intro h E normed scalar complete T hT S ht
    exact h ⟨⟨E,normed,scalar,complete⟩,T⟩ hT S ht

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@exists_continuous_representatives.{u})

theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  let P : Inputs.{u} := ⟨⟨ULift.{u} ℝ,inferInstance,inferInstance,inferInstance⟩,1⟩
  refine ⟨P,∅,{0},?_⟩
  change (∅ : family P) ≠ {0}
  exact Set.empty_ne_singleton 0

end Representatives

end Reg.D5.S3.Topology.Measures.IntervalLInfinityRepresentative
