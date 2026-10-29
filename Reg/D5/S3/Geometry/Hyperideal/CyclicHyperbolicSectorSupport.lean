import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ENNReal
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

abbrev cylindricalLiftScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cylindrical_lift)
abbrev cylindricalCoshDistanceScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cylindrical_cosh_distance)
abbrev cylindricalAxisScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cylindrical_axis)
abbrev cylindricalReconstructScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cylindrical_reconstruct)
abbrev turnLiftScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.turn_lift)
abbrev sectorAngleScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.sector_angle)
abbrev cylindricalMemSectorScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cylindrical_mem_sector)

universe u

namespace ShortRun

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.short_angle_forward_run.{u})

structure Inputs where
  I : Type u
  next : I → I
  alpha : I → ℝ
  positive : ∀ i, 0 < alpha i
  small : ∀ i, alpha i < Real.pi

structure Run (P : Inputs.{u}) where
  m : ℕ
  i : P.I
  rp : ℝ
  z : ℝ
  tp : ℝ
  rq : ℝ
  w : ℝ
  tq : ℝ
  positiveStart : 0 < rp
  positiveFinish : 0 < rq
  startAngle : tp ∈ Icc 0 (P.alpha i)
  finishAngle : tq ∈ Icc 0 (P.alpha (P.next^[m] i))
  short : runWidth P.next P.alpha i m + tq - tp < Real.pi

abbrev start (P : Inputs.{u}) (r : Run P) : Sigma (fun i => sector (P.alpha i)) :=
  ⟨r.i, ⟨cylindricalPoint r.rp r.z r.tp,
    cylindrical_mem_sector r.rp r.z r.tp (P.alpha r.i)
      r.positiveStart.le (P.small r.i) r.startAngle⟩⟩

abbrev finish (P : Inputs.{u}) (r : Run P) : Sigma (fun i => sector (P.alpha i)) :=
  ⟨P.next^[r.m] r.i, ⟨cylindricalPoint r.rq r.w r.tq,
    cylindrical_mem_sector r.rq r.w r.tq (P.alpha (P.next^[r.m] r.i))
      r.positiveFinish.le (P.small _) r.finishAngle⟩⟩

abbrev signature : Signature where
  Params := Inputs.{u}
  State := Run
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ P r =>
    ENNReal.ofReal (dist (cylindricalPoint r.rp r.z r.tp)
      (cylindricalPoint r.rq r.w (runWidth P.next P.alpha r.i r.m + r.tq))))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) (r : Run P),
    (sectorDatum P.next P.alpha P.positive P.small).Chain
      (start P r) (finish P r) (R.readout () P r)

theorem source_bridge : sourceScope.{u} ↔ (arena.{u}).Law (actual.{u}) := by
  constructor
  · intro h P r
    exact @h P.I P.next P.alpha P.positive P.small r.m r.i
      r.rp r.z r.tp r.rq r.w r.tq r.positiveStart r.positiveFinish
      r.startAngle r.finishAngle r.short
  · intro h I next alpha ha hapi m i rp z tp rq w tq hrp hrq htp htq hshort
    exact h ⟨I, next, alpha, ha, hapi⟩
      ⟨m, i, rp, z, tp, rq, w, tq, hrp, hrq, htp, htq, hshort⟩

theorem actual_positive : (arena.{u}).Law (actual.{u}) :=
  (source_bridge.{u}).mp
    (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.short_angle_forward_run.{u})

#print axioms source_bridge
#print axioms actual_positive

end ShortRun

namespace FoldBound

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.fold_distance_lower.{u})

structure Inputs where
  I : Type u
  next : I → I
  alpha : I → ℝ
  positive : ∀ i, 0 < alpha i
  small : ∀ i, alpha i < Real.pi
  A : ℝ
  reference : ℝ
  offset : I → ℝ
  shift : ∀ i, ((offset i + alpha i : ℝ) : AddCircle A) =
    (offset (next i) : AddCircle A)

abbrev points (P : Inputs.{u}) := Sigma (fun i => sector (P.alpha i))

abbrev signature : Signature where
  Params := Inputs.{u}
  State := fun P => points P × points P
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun role P endpoints =>
    if role = 0 then
      edist (fold P.alpha P.A P.reference P.offset endpoints.1)
        (fold P.alpha P.A P.reference P.offset endpoints.2)
    else (sectorDatum P.next P.alpha P.positive P.small).distance endpoints.1 endpoints.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (P : Inputs.{u}) (endpoints : points P × points P),
    R.readout 0 P endpoints ≤ R.readout 1 P endpoints

theorem source_bridge : sourceScope.{u} ↔ (arena.{u}).Law (actual.{u}) := by
  constructor
  · intro h P endpoints
    exact @h P.I P.next P.alpha P.positive P.small P.A P.reference P.offset P.shift
      endpoints.1 endpoints.2
  · intro h I next alpha ha hapi A reference offset hshift p q
    exact h ⟨I, next, alpha, ha, hapi, A, reference, offset, hshift⟩ (p, q)

theorem actual_positive : (arena.{u}).Law (actual.{u}) :=
  (source_bridge.{u}).mp
    (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.fold_distance_lower.{u})

#print axioms source_bridge
#print axioms actual_positive

end FoldBound
end Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorSupport
