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
def originalForward (c : FiniteAlexanderDualCollapse.Certificate V) := c.sphereEquivalence.forward
def originalBackward (c : FiniteAlexanderDualCollapse.Certificate V) := c.sphereEquivalence.backward

abbrev originalRepresentativeSource := type_of% (@Certificate.sphere_representative.{u})
def originalRepresentative (c : FiniteAlexanderDualCollapse.Certificate V)
    (hm : 2 ≤ c.lambda.card) (x : c.attachment.Disk) :=
  c.sphereEquivalence.forward (c.reduction.inclusion (c.attachment.diskIn x))

abbrev originalPolesSource := type_of% (@Certificate.sphere_poles.{u})
def originalCenter (c : FiniteAlexanderDualCollapse.Certificate V) (hm : 2 ≤ c.lambda.card) :=
  c.sphereEquivalence.forward (c.reduction.inclusion (c.attachment.diskIn barycenterPoint))
def originalBoundary (c : FiniteAlexanderDualCollapse.Certificate V)
    (hm : 2 ≤ c.lambda.card) (x : c.attachment.Disk) (hx : FiniteSimplexBoundarySphere.boundary x) :=
  c.sphereEquivalence.forward (c.reduction.inclusion (c.attachment.diskIn x))

abbrev originalBasedSource := type_of% (@Certificate.sphere_based_laws.{u})
def originalBaseForward (c : FiniteAlexanderDualCollapse.Certificate V) := c.sphereEquivalence.forward c.apex
def originalBaseBackward (c : FiniteAlexanderDualCollapse.Certificate V) := c.sphereEquivalence.backward c.spherePoint
def originalLeftLoop (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) :=
  c.sphereEquivalence.left (t, c.apex)
def originalRightLoop (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) :=
  c.sphereEquivalence.right (t, c.spherePoint)

abbrev retainedSource := type_of% (@Certificate.reduction_fixed.{u})
def retained (c : FiniteAlexanderDualCollapse.Certificate V) (t : I) (x : Space c.X) :=
  c.reductionSDR.homotopy (t, c.reduction.inclusion x)

abbrev originalCoordinatesSource := type_of% (@Certificate.disk_original_coordinates.{u})
def originalInside (c : FiniteAlexanderDualCollapse.Certificate V) (x : c.attachment.Disk)
    (i : c.lambda) := (c.reduction.inclusion (c.attachment.diskIn x)).1 i.1
def originalOutside (c : FiniteAlexanderDualCollapse.Certificate V) (x : c.attachment.Disk)
    (v : V) (hv : v ∉ c.lambda) := (c.reduction.inclusion (c.attachment.diskIn x)).1 v

abbrev ambientGhostSource := type_of% (@Certificate.ambient_ghost.{u})
def ambientGhost (c : FiniteAlexanderDualCollapse.Certificate V) (x : Space c.K)
    (v : V) (hv : v ∉ insert c.a c.W) := x.1 v

end Reg.D5.S3.Geometry.FiniteCriticalCellSphere.DirectOperands
