/- GID: D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere
   mirror-E: none(waiver:finite-critical-cell-sphere)
   anchors: [mathlib/module/Mathlib.Topology.CompactOpen, mathlib/module/Mathlib.Topology.Piecewise]
   utility: none
   digest: The literal finite attachment collar, core quotient and both nonempty-face Euclidean sphere branches. -/


import D5.S3.Geometry.FiniteAlexanderDualCollapse
import D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar
import D5.S3.Geometry.FiniteSimplexBoundarySphere
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise
import Mathlib.Data.Fintype.Card

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteCriticalCellSphere
open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteRelativeSimplicialCollapse
open FiniteSimplexBoundarySphere (Simplex E barycenter barycenterPoint
  faceCoordinateHomeomorph minCoord sigma cardR minCoord_le minCoord_attained
  sigma_nonneg sigma_eq_zero_iff cardR_pos cardR_ne
  continuous_minCoord barycenter_gauge BoundaryQuotient)


open private D5.S3.Geometry.FiniteCriticalCellSphere.pasteClosed D5.S3.Geometry.FiniteCriticalCellSphere.pasteClosed_left D5.S3.Geometry.FiniteCriticalCellSphere.pasteClosed_right D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.diskRestrict D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.diskIn_restrict D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.restrict_diskIn D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.cover D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.core_closed D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.disk_closed D5.S3.Geometry.FiniteCriticalCellSphere.Attachment.diskIn_mem_core_iff from D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar

variable {V : Type*} [Fintype V] [DecidableEq V]


/- Transporting along an actual homeomorphism retains both displayed based
   homotopies, including their pointwise fixed-basepoint equations. -/
private def postHomeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {x : X} {y : Y}
    (B : SingletonRetractionBasedInverse.BasedEquivalence x y) (e : Y ≃ₜ Z) :
    SingletonRetractionBasedInverse.BasedEquivalence x (e y) where
  forward := (toContinuousMap e).comp B.forward
  backward := B.backward.comp (toContinuousMap e.symm)
  forward_point := congrArg e B.forward_point
  backward_point := by change B.backward (e.symm (e y)) = x; rw [e.symm_apply_apply, B.backward_point]
  left :=
    { toFun := B.left
      continuous_toFun := B.left.continuous
      map_zero_left := by
        intro a
        change B.left (0, a) = B.backward (e.symm (e (B.forward a)))
        rw [e.symm_apply_apply]; exact B.left.apply_zero a
      map_one_left := B.left.apply_one
      prop' := by
        intro t a ha
        change B.left (t, a) = B.backward (e.symm (e (B.forward a)))
        rw [e.symm_apply_apply]
        exact B.left.eq_fst t ha }
  right :=
    { toFun z := e (B.right (z.1, e.symm z.2))
      continuous_toFun := e.continuous.comp (B.right.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := by intro a; exact congrArg e (B.right.apply_zero (e.symm a))
      map_one_left := by
        intro a
        change e (B.right (1, e.symm a)) = a
        rw [B.right.apply_one]
        exact e.apply_symm_apply a
      prop' := by
        intro t a ha
        obtain rfl := Set.mem_singleton_iff.mp ha
        change e (B.right (t, e.symm (e y))) =
          e (B.forward (B.backward (e.symm (e y))))
        rw [e.symm_apply_apply]
        exact congrArg e (B.right.eq_fst t (by simp)) }

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

/-- The rational representative with only the finite-cardinality index rewritten.
No ambient label is used in this reindexing except the labels of face. -/
def spherePsi (hm : 2 ≤ A.face.card) (x : A.Disk) :
    EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have hc : Fintype.card A.face - 1 = A.face.card - 1 := congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  exact hc ▸ FiniteSimplexBoundarySphere.reindexSphere
      (FiniteSimplexBoundarySphere.stdIndex hm') (FiniteSimplexBoundarySphere.psi hm' x)

def sphereNorth (hm : 2 ≤ A.face.card) : EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have hc : Fintype.card A.face - 1 = A.face.card - 1 := congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  exact hc ▸ FiniteSimplexBoundarySphere.reindexSphere
      (FiniteSimplexBoundarySphere.stdIndex hm') (FiniteSimplexBoundarySphere.north (Λ := A.face))

def sphereSouth (hm : 2 ≤ A.face.card) : EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have hc : Fintype.card A.face - 1 = A.face.card - 1 := congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  exact hc ▸ FiniteSimplexBoundarySphere.reindexSphere
      (FiniteSimplexBoundarySphere.stdIndex hm') (FiniteSimplexBoundarySphere.south (Λ := A.face))

/-- Actual Euclidean endpoint, composed with the frozen rational Psi map. -/
def multiSphereHomeomorph (hm : 2 ≤ A.face.card) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have hc : Fintype.card A.face - 1 = A.face.card - 1 := congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  exact hc ▸ (A.quotientSimplexHomeomorph hm').trans
    (FiniteSimplexBoundarySphere.simplexBoundaryStdSphere hm')

private theorem sphereTransport_apply {X : Type*} [TopologicalSpace X]
    {n m : Nat} (h : n = m) (e : X ≃ₜ EuclideanSphereJoin.StdSphere n) (x : X) :
    (h ▸ e : X ≃ₜ EuclideanSphereJoin.StdSphere m) x =
      (h ▸ e x : EuclideanSphereJoin.StdSphere m) := by
  subst m
  rfl

/-- Exact representative law, using rational Psi and the L2 isometric reindexing. -/
theorem multiSphere_representative (hm : 2 ≤ A.face.card) (x : A.Disk) :
    A.multiSphereHomeomorph hm (A.q (A.diskIn x)) = A.spherePsi hm x := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have he := FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_representative hm' x
  have hc : A.classMap hm' (A.diskIn x) = Quotient.mk _ x := A.classMap_disk hm' x
  have hc' : Fintype.card A.face - 1 = A.face.card - 1 :=
    congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  unfold multiSphereHomeomorph spherePsi
  dsimp only
  rw [sphereTransport_apply]
  apply congrArg (fun y : EuclideanSphereJoin.StdSphere (Fintype.card A.face - 1) =>
    (hc' ▸ y : EuclideanSphereJoin.StdSphere (A.face.card - 1)))
  change FiniteSimplexBoundarySphere.simplexBoundaryStdSphere hm'
    (A.classMap hm' (A.diskIn x)) = _
  rw [hc]
  exact he

/-- The collapsed P point is the actual south point. -/
theorem multiSphere_core (hm : 2 ≤ A.face.card) (x : Space A.P) :
    A.multiSphereHomeomorph hm (A.q (A.coreIn x)) = A.sphereSouth hm := by
  have hm' : 2 ≤ Fintype.card A.face := by simpa using hm
  have he := FiniteSimplexBoundarySphere.simplexBoundaryStdSphere_boundary
    hm' (A.boundaryVertex hm').1 (A.boundaryVertex hm').2
  have hc := A.classMap_core hm' (A.coreIn x) x.2
  have hc' : Fintype.card A.face - 1 = A.face.card - 1 :=
    congrArg (fun n => n - 1) (Fintype.card_coe A.face)
  unfold multiSphereHomeomorph sphereSouth
  dsimp only
  rw [sphereTransport_apply]
  apply congrArg (fun y : EuclideanSphereJoin.StdSphere (Fintype.card A.face - 1) =>
    (hc' ▸ y : EuclideanSphereJoin.StdSphere (A.face.card - 1)))
  change FiniteSimplexBoundarySphere.simplexBoundaryStdSphere hm'
    (A.classMap hm' (A.coreIn x)) = _
  rw [hc]
  exact he

/-- The barycenter and every boundary representative have their exact pole values. -/
theorem multiSphere_poles (hm : 2 ≤ A.face.card) :
    A.multiSphereHomeomorph hm (A.q (A.diskIn barycenterPoint)) = A.sphereNorth hm ∧
    (∀ x : A.Disk, FiniteSimplexBoundarySphere.boundary x →
      A.multiSphereHomeomorph hm (A.q (A.diskIn x)) = A.sphereSouth hm) := by
  constructor
  · rw [A.multiSphere_representative]
    unfold spherePsi sphereNorth
    dsimp only
    congr 1
    exact congrArg (FiniteSimplexBoundarySphere.reindexSphere _)
      (FiniteSimplexBoundarySphere.psi_barycenter (Λ := A.face) _)
  · intro x hx
    rw [A.multiSphere_representative]
    unfold spherePsi sphereSouth
    dsimp only
    congr 1
    exact congrArg (FiniteSimplexBoundarySphere.reindexSphere _)
      (FiniteSimplexBoundarySphere.psi_boundary (Λ := A.face) _ hx)

/- The singleton branch retains the core point. It never identifies the
   one-point simplex / empty boundary with the two-point sphere. -/
private theorem singleton_disk_eq (hm : A.face.card = 1) (x : A.Disk) :
    x = barycenterPoint := by
  have hc : Fintype.card A.face = 1 := by simpa using hm
  letI : Subsingleton A.face := Fintype.card_le_one_iff_subsingleton.mp hc.le
  letI : Unique A.face := ⟨⟨Classical.choice (inferInstance : Nonempty A.face)⟩,
    fun _ => Subsingleton.elim _ _⟩
  apply Subtype.ext
  ext i
  have hs : x.1 i = 1 := by
    have h := x.2.2
    simpa only [Finset.univ_unique, Finset.sum_singleton, Subsingleton.elim (default : A.face) i] using h
  change x.1 i = (cardR A.face)⁻¹
  rw [hs]
  simp [cardR, hc]

private theorem singleton_no_boundary (hm : A.face.card = 1) (x : A.Disk) :
    ¬ FiniteSimplexBoundarySphere.boundary x := by
  rw [A.singleton_disk_eq hm x]
  rintro ⟨i, hi⟩
  change (cardR A.face)⁻¹ = 0 at hi
  exact (inv_ne_zero (cardR_ne (Λ := A.face))) hi

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
  ⟨fun b => if b then A.q (A.diskIn barycenterPoint) else A.q A.basepoint,
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
        change A.q (A.diskIn barycenterPoint) = A.q (A.diskIn (A.diskRestrict ⟨x, hd⟩))
        exact congrArg (fun y => A.q (A.diskIn y))
          (A.singleton_disk_eq hm (A.diskRestrict ⟨x, hd⟩)).symm
  right_inv := by
    intro b
    cases b
    · exact A.boolMap_core hm A.p
    · exact A.boolMap_disk hm barycenterPoint
  continuous_toFun := (A.qBool hm).continuous
  continuous_invFun := A.boolToQ.continuous

end Attachment

/-- The positive point of the actual one-dimensional Euclidean unit sphere. -/
def s0Positive : EuclideanSphereJoin.StdSphere 0 :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)), by
    change _ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
    norm_num⟩

/-- The negative point is the basepoint in the singleton attachment branch. -/
def s0Negative : EuclideanSphereJoin.StdSphere 0 :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (-1 : ℝ)), by
    change _ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
    rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
    norm_num⟩

private theorem s0_exhaust (y : EuclideanSphereJoin.StdSphere 0) :
    y = s0Positive ∨ y = s0Negative := by
  have hy := y.2
  change y.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 at hy
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one] at hy
  have hs : (y.1 (0 : Fin 1)) ^ 2 = 1 := by simpa using hy
  have hz : (y.1 0 - 1) * (y.1 0 + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hp | hn
  · left
    apply Subtype.ext
    ext i
    have hi : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; omega)
    subst i
    change y.1 0 = 1
    linarith
  · right
    apply Subtype.ext
    ext i
    have hi : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; omega)
    subst i
    change y.1 0 = -1
    linarith

private theorem s0_ne : s0Positive ≠ s0Negative := by
  intro h
  have hv := congrArg (fun y : EuclideanSphereJoin.StdSphere 0 => y.1 0) h
  norm_num [s0Positive, s0Negative] at hv

private def boolSphereEquiv : Bool ≃ EuclideanSphereJoin.StdSphere 0 where
  toFun b := if b then s0Positive else s0Negative
  invFun y := if y = s0Positive then true else false
  left_inv b := by cases b <;> simp [s0_ne, Ne.symm s0_ne]
  right_inv y := by
    rcases s0_exhaust y with rfl | rfl <;> simp [s0_ne, Ne.symm s0_ne]

/-- Compact-to-Hausdorff inverse continuity is used only for the explicit
finite plus/minus bijection, not as an assumed sphere comparison. -/
def boolSphereHomeomorph : Bool ≃ₜ EuclideanSphereJoin.StdSphere 0 :=
  Continuous.homeoOfEquivCompactToT2 (f := boolSphereEquiv) continuous_of_discreteTopology

namespace Attachment
variable (A : Attachment V)

/-- In the singleton branch the actual disk point is fixed at every time;
on the complementary clopen core the same collar is the supplied contraction. -/
theorem singleton_collar (hm : A.face.card = 1) (s : I) (x : A.Disk) :
    A.collar (s, A.diskIn x) = A.diskIn x := by
  have hr : A.rho x = 0 := by
    rw [A.singleton_disk_eq hm x, rho, barycenter_gauge]
    ring
  have hi : A.rho x ≤ A.cut s := by rw [hr]; exact (A.cut_pos s).le
  rw [A.collar_inner s x hi]
  apply congrArg A.diskIn
  exact (A.singleton_disk_eq hm _).trans (A.singleton_disk_eq hm x).symm

/-- The separate actual StdSphere(0) comparison, retaining both classes. -/
def singletonSphere0Homeomorph (hm : A.face.card = 1) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere 0 :=
  (A.singletonQuotientHomeomorph hm).trans boolSphereHomeomorph

/-- Only the natural-number dimension is transported; no point is removed. -/
def singletonSphereHomeomorph (hm : A.face.card = 1) :
    A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  have hd : A.face.card - 1 = 0 := by omega
  exact hd.symm ▸ A.singletonSphere0Homeomorph hm

/-- No empty-boundary simplex quotient is used in this branch. -/
theorem singletonSphere_points (hm : A.face.card = 1) :
    A.singletonSphere0Homeomorph hm (A.q A.basepoint) = s0Negative ∧
    (∀ x : A.Disk, A.singletonSphere0Homeomorph hm (A.q (A.diskIn x)) = s0Positive) := by
  constructor
  · change boolSphereHomeomorph (A.boolMap hm (A.coreIn A.p)) = s0Negative
    rw [A.boolMap_core]; rfl
  · intro x
    change boolSphereHomeomorph (A.boolMap hm (A.diskIn x)) = s0Positive
    rw [A.boolMap_disk]; rfl

/-- Actual comparison for every allowed nonempty face. There is no
negative-dimensional sphere and no assertion about empty-face attachments. -/
def sphereHomeomorph : A.Q ≃ₜ EuclideanSphereJoin.StdSphere (A.face.card - 1) := by
  classical
  exact if hm : A.face.card = 1 then A.singletonSphereHomeomorph hm
    else A.multiSphereHomeomorph (by have h := Finset.card_pos.mpr A.face_nonempty; omega)

/-- The actual point on the actual sphere, fixed by both inverse homotopies. -/
def sphereBasepoint : EuclideanSphereJoin.StdSphere (A.face.card - 1) :=
  A.sphereHomeomorph (A.q A.basepoint)

/-- The two based sphere homotopies are conjugates of the actual collar and
its quotient descent, with the unchanged q as the forward quotient factor. -/
def sphereEquivalence : SingletonRetractionBasedInverse.BasedEquivalence
    A.basepoint A.sphereBasepoint :=
  postHomeomorph A.quotientEquivalence A.sphereHomeomorph

/-- The inverse is still the endpoint collar after the actual quotient/sphere inverse. -/
theorem sphere_maps :
    A.sphereEquivalence.forward = (toContinuousMap A.sphereHomeomorph).comp A.q ∧
    A.sphereEquivalence.backward = A.quotientInverse.comp (toContinuousMap A.sphereHomeomorph.symm) :=
  ⟨rfl, rfl⟩

/-- All original labels are preserved by the disk inclusion. A label outside
face is a zero coordinate, even if it is a vertex elsewhere in X. -/
theorem diskIn_coordinates (x : A.Disk) :
    (∀ i : A.face, (A.diskIn x).1 i.1 = x.1 i) ∧
    (∀ v ∉ A.face, (A.diskIn x).1 v = 0) := by
  constructor
  · intro i
    have h := FiniteSimplexBoundarySphere.faceCoordinateHomeomorph_restrict A.face
      (faceCoordinateHomeomorph A.face x) i
    rw [(faceCoordinateHomeomorph A.face).symm_apply_apply] at h
    exact h.symm
  · exact (faceCoordinateHomeomorph A.face x).2.2.2

end Attachment
end D5.S3.Geometry.FiniteCriticalCellSphere
