/- GID: D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere
   mirror-E: none(waiver:finite-critical-cell-sphere)
   anchors: [mathlib/module/Mathlib.Topology.CompactOpen, mathlib/module/Mathlib.Topology.Piecewise]
   utility: none
   digest: Literal attachment quotients, the separate singleton branch, and based sphere comparison. -/
import D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar
import D5.S3.Geometry.FiniteComponentClosure.BasedJoin

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteCriticalCellSphere
open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteSimplexBoundarySphere (faceCoordinateHomeomorph BoundaryQuotient)

open private
  pasteClosed
  pasteClosed_left
  pasteClosed_right
  from D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Attachment
variable (A : Attachment V)

/-- The genuine map from the full-boundary quotient to X/P; for a singleton
it is deliberately NOT called an equivalence. -/
def simplexQuotientToQ : C(BoundaryQuotient A.face, A.Q) :=
  { toFun := Quotient.lift (fun x => A.q (A.diskIn x)) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact Quotient.sound (Or.inr
          ⟨(A.diskIn_mem_core_iff x).mpr hx, (A.diskIn_mem_core_iff y).mpr hy⟩))
    continuous_toFun := (A.q.continuous.comp A.diskIn.continuous).quotient_lift _ }

private def boundaryVertex (hm : 2 ≤ Fintype.card A.face) : A.BDisk :=
  ⟨FiniteSimplexBoundarySphere.vertex (Classical.choice (inferInstance : Nonempty A.face)),
    FiniteSimplexBoundarySphere.vertex_boundary hm _⟩

private def boundaryClass (hm : 2 ≤ Fintype.card A.face) : BoundaryQuotient A.face :=
  Quotient.mk _ (A.boundaryVertex hm).1

private def classCore (hm : 2 ≤ Fintype.card A.face) : C(A.coreSet, BoundaryQuotient A.face) :=
  ContinuousMap.const _ (A.boundaryClass hm)

private def classDisk : C(A.diskSet, BoundaryQuotient A.face) :=
  ⟨fun x => Quotient.mk _ (A.diskRestrict x),
    continuous_quotient_mk'.comp A.diskRestrict.continuous⟩

private theorem class_seam (hm : 2 ≤ Fintype.card A.face) (x : Space A.X)
    (hp : x ∈ A.coreSet) (hd : x ∈ A.diskSet) :
    A.classCore hm ⟨x, hp⟩ = A.classDisk ⟨x, hd⟩ := by
  apply Quotient.sound
  apply Or.inr
  refine ⟨(A.boundaryVertex hm).2, ?_⟩
  apply (A.diskIn_mem_core_iff _).mp
  rw [A.diskIn_restrict]
  exact hp

private def classMap (hm : 2 ≤ Fintype.card A.face) : C(Space A.X, BoundaryQuotient A.face) :=
  pasteClosed A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
    (A.classCore hm) A.classDisk (A.class_seam hm)

private theorem classMap_core (hm : 2 ≤ Fintype.card A.face)
    (x : Space A.X) (hx : x ∈ A.coreSet) : A.classMap hm x = A.boundaryClass hm :=
  pasteClosed_left _ _ _ _ _ _ _ _ x hx

private theorem classMap_disk (hm : 2 ≤ Fintype.card A.face) (x : A.Disk) :
    A.classMap hm (A.diskIn x) = Quotient.mk _ x := by
  have h := pasteClosed_right A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
    (A.classCore hm) A.classDisk (A.class_seam hm)
    (A.diskIn x) (faceCoordinateHomeomorph A.face x).2
  change A.classMap hm (A.diskIn x) = Quotient.mk _
    (A.diskRestrict ⟨A.diskIn x, (faceCoordinateHomeomorph A.face x).2⟩) at h
  rw [A.restrict_diskIn x] at h
  exact h

private def qToSimplexQuotient (hm : 2 ≤ Fintype.card A.face) :
    C(A.Q, BoundaryQuotient A.face) :=
  { toFun := Quotient.lift (A.classMap hm) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact (A.classMap_core hm x hx).trans (A.classMap_core hm y hy).symm)
    continuous_toFun := (A.classMap hm).continuous.quotient_lift _ }

private theorem classMap_toQ (hm : 2 ≤ Fintype.card A.face) (x : Space A.X) :
    A.simplexQuotientToQ (A.classMap hm x) = A.q x := by
  rcases A.cover x with hp | hd
  · rw [A.classMap_core hm x hp]
    apply Quotient.sound
    exact Or.inr ⟨(A.diskIn_mem_core_iff _).mpr (A.boundaryVertex hm).2, hp⟩
  · have hx : A.diskIn (A.diskRestrict ⟨x, hd⟩) = x := A.diskIn_restrict ⟨x, hd⟩
    calc
      A.simplexQuotientToQ (A.classMap hm x) =
          A.simplexQuotientToQ (A.classMap hm (A.diskIn (A.diskRestrict ⟨x, hd⟩))) :=
        congrArg (fun y => A.simplexQuotientToQ (A.classMap hm y)) hx.symm
      _ = A.q (A.diskIn (A.diskRestrict ⟨x, hd⟩)) := by rw [A.classMap_disk]; rfl
      _ = A.q x := congrArg A.q hx

/-- Both directions are literal quotient lifts of actual coordinate maps.
The proof needs a genuine boundary point, hence the explicit m>=2 premise. -/
def quotientSimplexHomeomorph (hm : 2 ≤ Fintype.card A.face) :
    A.Q ≃ₜ BoundaryQuotient A.face where
  toFun := A.qToSimplexQuotient hm
  invFun := A.simplexQuotientToQ
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h x => exact A.classMap_toQ hm x
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h x => exact A.classMap_disk hm x
  continuous_toFun := (A.qToSimplexQuotient hm).continuous
  continuous_invFun := A.simplexQuotientToQ.continuous

/-- Actual Euclidean endpoint, composed with the current rational Psi comparison. -/
def multiSphereHomeomorph (hm : 2 ≤ A.face.card) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have hc : Fintype.card A.face - 1 = A.face.card - 1 := congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  exact hc ▸ (A.quotientSimplexHomeomorph hm').trans
    (FiniteSimplexBoundarySphere.simplexBoundaryStdSphere hm')

/- The ordinary boundary is empty in the singleton branch. Its simplex
   quotient has one point; X/P instead retains the nonempty core class too. -/
private def singletonVertex : A.Disk :=
  FiniteSimplexBoundarySphere.vertex (Classical.choice (inferInstance : Nonempty A.face))

private theorem singleton_coordinate (hm : A.face.card = 1) (x : A.Disk) (i : A.face) :
    x.1 i = 1 := by
  have hc : Fintype.card A.face = 1 := by simpa using hm
  letI : Subsingleton A.face := Fintype.card_le_one_iff_subsingleton.mp hc.le
  letI : Unique A.face := ⟨⟨Classical.choice (inferInstance : Nonempty A.face)⟩,
    fun _ => Subsingleton.elim _ _⟩
  simpa only [Finset.univ_unique, Finset.sum_singleton,
    Subsingleton.elim (default : A.face) i] using x.2.2

private theorem singleton_disk_eq (hm : A.face.card = 1) (x : A.Disk) :
    x = A.singletonVertex := by
  apply Subtype.ext
  ext i
  exact (A.singleton_coordinate hm x i).trans
    (A.singleton_coordinate hm A.singletonVertex i).symm

private theorem singleton_no_boundary (hm : A.face.card = 1) (x : A.Disk) :
    ¬ FiniteSimplexBoundarySphere.boundary x := by
  rintro ⟨i, hi⟩
  exact one_ne_zero ((A.singleton_coordinate hm x i).symm.trans hi)

private def boolCore : C(A.coreSet, Bool) := ContinuousMap.const _ false
private def boolDisk : C(A.diskSet, Bool) := ContinuousMap.const _ true

private theorem bool_seam (hm : A.face.card = 1) (x : Space A.X)
    (hp : x ∈ A.coreSet) (hd : x ∈ A.diskSet) :
    A.boolCore ⟨x, hp⟩ = A.boolDisk ⟨x, hd⟩ := by
  have hb : FiniteSimplexBoundarySphere.boundary (A.diskRestrict ⟨x, hd⟩) := by
    apply (A.diskIn_mem_core_iff _).mp
    rw [A.diskIn_restrict]
    exact hp
  exact (A.singleton_no_boundary hm _ hb).elim

private def boolMap (hm : A.face.card = 1) : C(Space A.X, Bool) :=
  pasteClosed A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
    A.boolCore A.boolDisk (A.bool_seam hm)

private theorem boolMap_core (hm : A.face.card = 1) (x : Space A.P) :
    A.boolMap hm (A.coreIn x) = false :=
  pasteClosed_left A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
    A.boolCore A.boolDisk (A.bool_seam hm) (A.coreIn x) x.2

private theorem boolMap_disk (hm : A.face.card = 1) (x : A.Disk) :
    A.boolMap hm (A.diskIn x) = true :=
  pasteClosed_right A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
    A.boolCore A.boolDisk (A.bool_seam hm) (A.diskIn x) (faceCoordinateHomeomorph A.face x).2

private def qBool (hm : A.face.card = 1) : C(A.Q, Bool) :=
  { toFun := Quotient.lift (A.boolMap hm) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · have he (z : Space A.X) (hz : z ∈ A.coreSet) : A.boolMap hm z = false :=
          pasteClosed_left _ _ _ _ _ _ _ _ z hz
        exact (he x hx).trans (he y hy).symm)
    continuous_toFun := (A.boolMap hm).continuous.quotient_lift _ }

private def boolToQ : C(Bool, A.Q) :=
  ⟨fun b => if b then A.q (A.diskIn A.singletonVertex) else A.q A.basepoint,
    continuous_of_discreteTopology⟩

/-- The two classes are the nonempty core and the isolated original vertex. -/
def singletonQuotientHomeomorph (hm : A.face.card = 1) : A.Q ≃ₜ Bool where
  toFun := A.qBool hm
  invFun := A.boolToQ
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h x =>
      rcases A.cover x with hp | hd
      · have he : A.qBool hm (A.q x) = false :=
          pasteClosed_left A.coreSet A.diskSet A.core_closed A.disk_closed A.cover
            A.boolCore A.boolDisk (A.bool_seam hm) x hp
        change A.boolToQ (A.qBool hm (A.q x)) = A.q x
        rw [he]
        apply Quotient.sound
        exact Or.inr ⟨A.p.2, hp⟩
      · have hx := A.diskIn_restrict ⟨x, hd⟩
        change A.diskIn (A.diskRestrict ⟨x, hd⟩) = x at hx
        rw [← hx]
        change A.boolToQ (A.boolMap hm (A.diskIn (A.diskRestrict ⟨x, hd⟩))) = _
        rw [A.boolMap_disk]
        change A.q (A.diskIn A.singletonVertex) = A.q (A.diskIn (A.diskRestrict ⟨x, hd⟩))
        exact congrArg (fun y => A.q (A.diskIn y))
          (A.singleton_disk_eq hm (A.diskRestrict ⟨x, hd⟩)).symm
  right_inv := by
    intro b
    cases b
    · exact A.boolMap_core hm A.p
    · exact A.boolMap_disk hm A.singletonVertex
  continuous_toFun := (A.qBool hm).continuous
  continuous_invFun := A.boolToQ.continuous

/-- Reuse the original Bool-to-twoPoints realization adapter and its existing
Euclidean S0 comparison. No second plus/minus sphere theory is introduced. -/
def singletonSphere0Homeomorph (hm : A.face.card = 1) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere 0 :=
  ((A.singletonQuotientHomeomorph hm).trans
    FiniteComponentClosure.boolTwoPointHomeomorph).trans
    FiniteComponentClosure.twoPointSphereHomeomorph

/-- Only the natural-number dimension is transported. -/
def singletonSphereHomeomorph (hm : A.face.card = 1) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hd : A.face.card - 1 = 0 := by omega
  exact hd.symm ▸ A.singletonSphere0Homeomorph hm

/-- Comparison for every allowed nonempty face, with a separate singleton branch. -/
def sphereHomeomorph : A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  classical
  exact if hm : A.face.card = 1 then A.singletonSphereHomeomorph hm
    else A.multiSphereHomeomorph (by have h := Finset.card_pos.mpr A.face_nonempty; omega)

/-- The point determined by the unchanged quotient of the original included p. -/
def sphereBasepoint : EuclideanSphereJoin.StdSphere (A.face.card - 1) :=
  A.sphereHomeomorph (A.q A.basepoint)

/-- Compose using the original basedTrans and basedHomeomorphism.
The maps are h after q and quotientInverse after h.symm. The homotopies
use HomotopyRel.trans; no equality with an unpaused collar is asserted. -/
def sphereEquivalence : SingletonRetractionBasedInverse.BasedEquivalence
    A.basepoint A.sphereBasepoint :=
  FiniteComponentClosure.basedTrans A.quotientEquivalence
    (FiniteComponentClosure.basedHomeomorphism A.sphereHomeomorph
      (A.q A.basepoint) A.sphereBasepoint rfl)

end Attachment
end D5.S3.Geometry.FiniteCriticalCellSphere
