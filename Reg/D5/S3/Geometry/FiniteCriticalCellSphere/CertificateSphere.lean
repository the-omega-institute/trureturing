/- SOURCE STATUS: UNCOMPILED. Seven original-certificate direct operand preparations;
   complete four-slot families, source selection, enrollment and binding remain open. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCriticalCellSphere.CertificateSphere

noncomputable section
open Set
open scoped unitInterval ContinuousMap
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteCriticalCellSphere
open _root_.D5.S3.Geometry.FiniteCriticalCellSphere.Certificate
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteConeUnionWedge
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open _root_.D5.S3.Geometry.FiniteSimplexBoundarySphere (barycenterPoint)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Geometry.FiniteCriticalCellSphere.DirectOperands
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev originalMapsSource := type_of% (@Certificate.sphere_maps.{u})
def originalForward (c : FiniteAlexanderDualCollapse.Certificate V) := (sphereEquivalence c).forward
def originalBackward (c : FiniteAlexanderDualCollapse.Certificate V) := (sphereEquivalence c).backward

abbrev originalRepresentativeSource := type_of% (@Certificate.sphere_representative.{u})
def originalRepresentative (c : FiniteAlexanderDualCollapse.Certificate V)
    (hm : 2 ≤ c.lambda.card) (x : (attachment c).Disk) :=
  (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn x))

abbrev originalPolesSource := type_of% (@Certificate.sphere_poles.{u})
def originalCenter (c : FiniteAlexanderDualCollapse.Certificate V) (hm : 2 ≤ c.lambda.card) :=
  (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn barycenterPoint))
def originalBoundary (c : FiniteAlexanderDualCollapse.Certificate V)
    (hm : 2 ≤ c.lambda.card) (x : (attachment c).Disk) (hx : FiniteSimplexBoundarySphere.boundary x) :=
  (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn x))

abbrev originalBasedSource := type_of% (@Certificate.sphere_based_laws.{u})
def originalBaseForward (c : FiniteAlexanderDualCollapse.Certificate V) := (sphereEquivalence c).forward (apex c)
def originalBaseBackward (c : FiniteAlexanderDualCollapse.Certificate V) := (sphereEquivalence c).backward (spherePoint c)
def originalLeftLoop (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) :=
  (sphereEquivalence c).left (t, (apex c))
def originalRightLoop (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) :=
  (sphereEquivalence c).right (t, (spherePoint c))

abbrev retainedSource := type_of% (@Certificate.reduction_fixed.{u})
def retained (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) (x : Space c.X) :=
  c.reductionSDR.homotopy (t, c.reduction.inclusion x)

abbrev originalCoordinatesSource := type_of% (@Certificate.disk_original_coordinates.{u})
def originalInside (c : FiniteAlexanderDualCollapse.Certificate V) (x : (attachment c).Disk)
    (i : c.lambda) := (c.reduction.inclusion ((attachment c).diskIn x)).1 i.1
def originalOutside (c : FiniteAlexanderDualCollapse.Certificate V) (x : (attachment c).Disk)
    (v : V) (hv : v ∉ c.lambda) := (c.reduction.inclusion ((attachment c).diskIn x)).1 v

abbrev ambientGhostSource := type_of% (@Certificate.ambient_ghost.{u})
def ambientGhost (c : FiniteAlexanderDualCollapse.Certificate V) (x : Space c.K)
    (v : V) (hv : v ∉ insert c.a c.W) := x.1 v

end Reg.D5.S3.Geometry.FiniteCriticalCellSphere.DirectOperands
