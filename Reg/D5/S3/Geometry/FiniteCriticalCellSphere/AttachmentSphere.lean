/- SOURCE STATUS: UNCOMPILED. This is source-fidelity preparation, not a
   declared_validated record. No source occurrence selectors are invented.
   The CutPositive family below attempts all mathematical family obligations
   with the ORIGINAL Law telescope and actual scalar cut operand. Every other
   target has a direct actual-operand preparation below; their four-slot
   mathematical audits and native source binding remain individually open.
   An operand inventory is explicitly NOT registration completion. -/
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentSphere

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

namespace Reg.D5.S3.Geometry.FiniteCriticalCellSphere.CutPositive
universe u

/-- Mathematical adapter only: Parameters packages V, its dictionaries and A.
The original source has {V : Type u} [Fintype V] [DecidableEq V]
(A : @Attachment V finite decEq) (s : I), with no Nonempty V or Parameters binder.
Selected-instance/proof/dictionary exclusion, dependency closure and native
State/Output/readout/Params correspondence are unresolved. This adapter supplies
no exact source-generated parameter layout. -/
structure Parameters where
  V : Type u
  finite : Fintype V
  decEq : DecidableEq V
  attachment : @Attachment V finite decEq

attribute [instance] Parameters.finite Parameters.decEq

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := I
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Read the actual scalar cut operand; do not read truth of cut_pos. -/
def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.attachment.cut s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  /- Law mirrors the ORIGINAL telescope. This does not identify Parameters with
     the native source-generated Params shape. -/
  Law R := ∀ {V : Type u} [finite : Fintype V] [decEq : DecidableEq V]
    (A : Attachment V) (s : I), 0 < R.readout () ⟨V, finite, decEq, A⟩ s

private theorem bridge :
    (type_of% (@Attachment.cut_pos.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro source V finite decEq A s
    exact source A s
  · intro law V finite decEq A s
    exact law A s

private abbrev TestV : Type u := ULift.{u} Bool
private def testA : Attachment TestV where
  P := cone (⟨false⟩ : TestV) ⊥
  X := cone (⟨false⟩ : TestV) ⊥ ⊔
    FiniteAlexanderDualCollapse.simplex {⟨true⟩}
  face := {⟨true⟩}
  face_nonempty := Finset.singleton_nonempty _
  union_eq := rfl
  intersection_eq := by
    apply SetLike.coe_injective
    ext s
    constructor
    · rintro ⟨hp, hs⟩
      obtain ⟨v, hv⟩ := hs.1
      have he : v = (⟨true⟩ : TestV) := Finset.mem_singleton.mp (hs.2 hv)
      have hn : v ≠ (⟨false⟩ : TestV) := by rw [he]; decide
      have hv' : v ∈ s.erase (⟨false⟩ : TestV) := Finset.mem_erase.mpr ⟨hn, hv⟩
      rcases hp.2 with hz | hb
      · rw [hz] at hv'
        exact (Finset.notMem_empty v hv').elim
      · exact hb.elim
    · intro hs
      have hp := Finset.card_pos.mpr hs.1
      have hl := Finset.card_lt_card hs.2
      simp only [Finset.card_singleton] at hl
      omega
  p := conePoint (⟨false⟩ : TestV) ⊥
  contraction := coneContraction (⟨false⟩ : TestV) ⊥

private def testP : Parameters.{u} := ⟨TestV, inferInstance, inferInstance, testA⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law testA (0 : I)
  change (0 : ℝ) < 0 at h
  exact (lt_irrefl 0) h

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨testP, (0 : I), (1 : I), ?_⟩
  intro h
  change testA.cut 0 = testA.cut 1 at h
  norm_num [Attachment.cut] at h

/-- Full mathematical family attempt. No compiled enrollment or source binding
receipt is asserted by constructing this source term. -/
def family : Registration arena.{u} (type_of% (@Attachment.cut_pos.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@Attachment.cut_pos.{u}), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

/-- Exact selector/binder identity and source correspondence remain unresolved.
source.selection_missing is expected if the absent-selector branch is reached;
no native branch was run. Missing fields supply no audit or enrollment evidence. -/
def registration_attempt :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@Attachment.cut_pos.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCriticalCellSphere.CutPositive.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCriticalCellSphere.CutPositive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => p.attachment.cut s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.FiniteCriticalCellSphere.CutPositive

namespace Reg.D5.S3.Geometry.FiniteCriticalCellSphere.DirectOperands
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/- These are actual source operands in the original binder types. They are
   NOT alternate Laws, truth observations, packed states, pair wrappers,
   occurrence selectors, or completed registrations. Each exact source scope
   is named separately so unresolved audits cannot disappear into a count. -/
abbrev collarCoreSource := type_of% (@Attachment.collar_core.{u})
def collarCore (A : Attachment V) (s : I) (x : Space A.P) :=
  A.collar (s, A.coreIn x)

abbrev collarInnerSource := type_of% (@Attachment.collar_inner.{u})
def collarInner (A : Attachment V) (s : I) (x : A.Disk) (hx : A.rho x ≤ A.cut s) :=
  A.collar (s, A.diskIn x)

abbrev collarOuterSource := type_of% (@Attachment.collar_outer.{u})
def collarOuter (A : Attachment V) (s : I) (x : A.Disk) (hx : A.cut s ≤ A.rho x) :=
  A.collar (s, A.diskIn x)

abbrev collarLawsSource := type_of% (@Attachment.collar_laws.{u})
def collarAtZero (A : Attachment V) (x : Space A.X) := A.collar (0, x)
def collarAtBase (A : Attachment V) (s : I) := A.collar (s, A.basepoint)

abbrev quotientRepresentativeSource := type_of% (@Attachment.quotient_representative.{u})
def quotientForward (A : Attachment V) (x : Space A.X) := A.quotientEquivalence.forward x
def quotientBackward (A : Attachment V) (x : Space A.X) := A.quotientEquivalence.backward (A.q x)

abbrev inverseInnerSource := type_of% (@Attachment.quotientInverse_inner.{u})
def inverseInner (A : Attachment V) (x : A.Disk) (hx : A.rho x ≤ (1 / 2 : ℝ)) :=
  A.quotientInverse (A.q (A.diskIn x))

abbrev inverseBarycenterSource := type_of% (@Attachment.quotientInverse_barycenter.{u})
def inverseBarycenter (A : Attachment V) := A.quotientInverse (A.q (A.diskIn barycenterPoint))

abbrev multiRepresentativeSource := type_of% (@Attachment.multiSphere_representative.{u})
def multiRepresentative (A : Attachment V) (hm : 2 ≤ A.face.card) (x : A.Disk) :=
  A.multiSphereHomeomorph hm (A.q (A.diskIn x))

abbrev multiCoreSource := type_of% (@Attachment.multiSphere_core.{u})
def multiCore (A : Attachment V) (hm : 2 ≤ A.face.card) (x : Space A.P) :=
  A.multiSphereHomeomorph hm (A.q (A.coreIn x))

abbrev multiPolesSource := type_of% (@Attachment.multiSphere_poles.{u})
def multiCenter (A : Attachment V) (hm : 2 ≤ A.face.card) :=
  A.multiSphereHomeomorph hm (A.q (A.diskIn barycenterPoint))
def multiBoundary (A : Attachment V) (hm : 2 ≤ A.face.card) (x : A.Disk)
    (hx : FiniteSimplexBoundarySphere.boundary x) :=
  A.multiSphereHomeomorph hm (A.q (A.diskIn x))

abbrev singletonCollarSource := type_of% (@Attachment.singleton_collar.{u})
def singletonCollar (A : Attachment V) (hm : A.face.card = 1) (s : I) (x : A.Disk) :=
  A.collar (s, A.diskIn x)

abbrev singletonPointsSource := type_of% (@Attachment.singletonSphere_points.{u})
def singletonCore (A : Attachment V) (hm : A.face.card = 1) :=
  A.singletonSphere0Homeomorph hm (A.q A.basepoint)
def singletonDisk (A : Attachment V) (hm : A.face.card = 1) (x : A.Disk) :=
  A.singletonSphere0Homeomorph hm (A.q (A.diskIn x))

abbrev attachmentMapsSource := type_of% (@Attachment.sphere_maps.{u})
def attachmentForward (A : Attachment V) := A.sphereEquivalence.forward
def attachmentBackward (A : Attachment V) := A.sphereEquivalence.backward

abbrev diskCoordinatesSource := type_of% (@Attachment.diskIn_coordinates.{u})
def diskInside (A : Attachment V) (x : A.Disk) (i : A.face) := (A.diskIn x).1 i.1
def diskOutside (A : Attachment V) (x : A.Disk) (v : V) (hv : v ∉ A.face) := (A.diskIn x).1 v


/- These fourteen direct-operand preparations and CutPositive remain unaudited. -/
end Reg.D5.S3.Geometry.FiniteCriticalCellSphere.DirectOperands
