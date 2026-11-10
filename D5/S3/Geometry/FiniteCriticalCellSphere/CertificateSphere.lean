/- GID: D5/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteCriticalCellSphere/CertificateSphere
   mirror-E: none(waiver:finite-critical-cell-sphere)
   anchors: [mathlib/module/Mathlib.Topology.CompactOpen]
   utility: none
   digest: The computed finite Alexander certificate supplies the original-K based sphere maps and retained-label equations. -/

/- SOURCE STATUS: UNCOMPILED. No native proof, binding or acceptance evidence. -/
import D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentSphere
import Mathlib.Topology.CompactOpen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteCriticalCellSphere
open FiniteConeCollapse FiniteConeUnionWedge FiniteSimplicialJoin
open FiniteRelativeSimplicialCollapse
open FiniteSimplexBoundarySphere (Simplex E barycenter barycenterPoint
  faceCoordinateHomeomorph minCoord sigma cardR minCoord_le minCoord_attained
  sigma_nonneg sigma_eq_zero_iff cardR_pos cardR_ne
  continuous_minCoord barycenter_gauge BoundaryQuotient)

variable {V : Type*} [Fintype V] [DecidableEq V]

private def basedCompose {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {x : X} {y : Y} {z : Z}
    (B : SingletonRetractionBasedInverse.BasedEquivalence x y)
    (C : SingletonRetractionBasedInverse.BasedEquivalence y z) :
    SingletonRetractionBasedInverse.BasedEquivalence x z := by
  let L : ((B.backward.comp C.backward).comp (C.forward.comp B.forward)).HomotopyRel
      (B.backward.comp B.forward) {x} :=
    { toFun u := B.backward (C.left (u.1, B.forward u.2))
      continuous_toFun := B.backward.continuous.comp (C.left.continuous.comp
        (continuous_fst.prodMk (B.forward.continuous.comp continuous_snd)))
      map_zero_left := fun a => congrArg B.backward (C.left.apply_zero (B.forward a))
      map_one_left := fun a => congrArg B.backward (C.left.apply_one (B.forward a))
      prop' := by
        intro t a ha
        have ha' : a = x := Set.mem_singleton_iff.mp ha
        subst a
        change B.backward (C.left (t, B.forward x)) =
          B.backward (C.backward (C.forward (B.forward x)))
        rw [B.forward_point]
        exact congrArg B.backward (C.left.eq_fst t (by simp)) }
  let R : ((C.forward.comp B.forward).comp (B.backward.comp C.backward)).HomotopyRel
      (C.forward.comp C.backward) {z} :=
    { toFun u := C.forward (B.right (u.1, C.backward u.2))
      continuous_toFun := C.forward.continuous.comp (B.right.continuous.comp
        (continuous_fst.prodMk (C.backward.continuous.comp continuous_snd)))
      map_zero_left := fun a => congrArg C.forward (B.right.apply_zero (C.backward a))
      map_one_left := fun a => congrArg C.forward (B.right.apply_one (C.backward a))
      prop' := by
        intro t a ha
        have ha' : a = z := Set.mem_singleton_iff.mp ha
        subst a
        change C.forward (B.right (t, C.backward z)) =
          C.forward (B.forward (B.backward (C.backward z)))
        rw [C.backward_point]
        exact congrArg C.forward (B.right.eq_fst t (by simp)) }
  exact
    { forward := C.forward.comp B.forward
      backward := B.backward.comp C.backward
      forward_point := by change C.forward (B.forward x) = z; rw [B.forward_point, C.forward_point]
      backward_point := by change B.backward (C.backward z) = x; rw [C.backward_point, B.backward_point]
      left := L.trans B.left
      right := R.trans C.right }

namespace Certificate
open FiniteAlexanderDualCollapse
variable (c : FiniteAlexanderDualCollapse.Certificate V)

/-- Every input is computed by the frozen finite-certificate owner. In
particular collapseP remains a standalone collapse; it is not used inside X. -/
def attachment : Attachment V where
  X := c.X
  P := c.P
  face := c.lambda
  face_nonempty := c.arithmetic.1
  union_eq := c.cell_decomposition
  intersection_eq := c.cell_intersection.1
  p := realizationInclusion (show c.C ≤ c.P from le_sup_right) (conePoint c.a c.Dstar)
  contraction := c.pContraction

/-- The original included apex on the ORIGINAL |K|. -/
def apex : Space c.K :=
  realizationInclusion (show c.C ≤ c.K from le_sup_right) (conePoint c.a c.Dstar)

private theorem apex_inclusion : c.reduction.inclusion (attachment c).basepoint = (apex c) :=
  Subtype.ext rfl

private theorem reduction_apex : c.reductionSDR.retraction (apex c) = (attachment c).basepoint := by
  rw [← (apex_inclusion c)]
  exact c.reductionSDR.retraction_inclusion (attachment c).basepoint

/-- This based reduction uses the computed retraction and literal inclusion,
with the owner's whole-retained-endpoint SDR restricted only for packaging. -/
def reductionEquivalence : SingletonRetractionBasedInverse.BasedEquivalence
    (apex c) (attachment c).basepoint where
  forward := c.reductionSDR.retraction
  backward := c.reduction.inclusion
  forward_point := (reduction_apex c)
  backward_point := (apex_inclusion c)
  left :=
    { toHomotopy := c.reductionSDR.homotopy.toHomotopy.symm
      prop' := by
        intro t x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        change c.reductionSDR.homotopy.toHomotopy.symm (t, (apex c)) =
          c.reduction.inclusion (c.reductionSDR.retraction (apex c))
        rw [(reduction_apex c), (apex_inclusion c)]
        apply c.reductionSDR.homotopy.eq_fst
        exact (attachment c).basepoint.2 }
  right :=
    { toFun z := z.2
      continuous_toFun := continuous_snd
      map_zero_left := fun y => (c.reductionSDR.retraction_inclusion y).symm
      map_one_left := fun _ => rfl
      prop' := by
        intro t y hy
        change y = c.reductionSDR.retraction (c.reduction.inclusion y)
        exact (c.reductionSDR.retraction_inclusion y).symm }

/-- The actual sphere point; for m>=2 it is reindexed south, and for m=1
it is the negative point after the harmless natural-number dimension cast. -/
def spherePoint : EuclideanSphereJoin.StdSphere c.d := (attachment c).sphereBasepoint

/-- Both genuine based continuous-map inverse homotopies for the original K. -/
def sphereEquivalence : SingletonRetractionBasedInverse.BasedEquivalence (apex c) (spherePoint c) :=
  basedCompose (reductionEquivalence c) (attachment c).sphereEquivalence

/-- The maps use the existing reduction retraction/inclusion, the unchanged q,
and the actual quotient-to-Euclidean-sphere comparison. -/
theorem sphere_maps :
    (sphereEquivalence c).forward = (toContinuousMap (attachment c).sphereHomeomorph).comp
      ((attachment c).q.comp c.reductionSDR.retraction) ∧
    (sphereEquivalence c).backward = c.reduction.inclusion.comp
      ((attachment c).quotientInverse.comp (toContinuousMap (attachment c).sphereHomeomorph.symm)) := by
  constructor <;> ext x <;> rfl

/-- Exact original-disk representative equation, including the literal
reduction inclusion rather than any changed attaching map. -/
theorem sphere_representative (hm : 2 ≤ c.lambda.card) (x : (attachment c).Disk) :
    (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn x)) =
      (attachment c).spherePsi hm x := by
  change (attachment c).sphereHomeomorph
    ((attachment c).q (c.reductionSDR.retraction
      (c.reduction.inclusion ((attachment c).diskIn x)))) = _
  rw [c.reductionSDR.retraction_inclusion]
  have hn : (attachment c).face.card ≠ 1 := by
    change c.lambda.card ≠ 1
    omega
  simp only [Attachment.sphereHomeomorph, dif_neg hn]
  exact (attachment c).multiSphere_representative hm x

/-- Exact original barycenter and whole-boundary pole equations for m>=2. -/
theorem sphere_poles (hm : 2 ≤ c.lambda.card) :
    (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn barycenterPoint)) =
      (attachment c).sphereNorth hm ∧
    (∀ x : (attachment c).Disk, FiniteSimplexBoundarySphere.boundary x →
      (sphereEquivalence c).forward (c.reduction.inclusion ((attachment c).diskIn x)) =
        (attachment c).sphereSouth hm) := by
  constructor
  · rw [sphere_representative c hm]
    exact ((attachment c).multiSphere_representative hm barycenterPoint).symm.trans
      ((attachment c).multiSphere_poles hm).1
  · intro x hx
    rw [sphere_representative c hm]
    exact ((attachment c).multiSphere_representative hm x).symm.trans
      (((attachment c).multiSphere_poles hm).2 x hx)

/-- Both original homotopies fix their actual chosen points at every time. -/
theorem sphere_based_laws :
    (sphereEquivalence c).forward (apex c) = (spherePoint c) ∧
    (sphereEquivalence c).backward (spherePoint c) = (apex c) ∧
    (∀ t, (sphereEquivalence c).left (t, (apex c)) = (apex c)) ∧
    (∀ t, (sphereEquivalence c).right (t, (spherePoint c)) = (spherePoint c)) := by
  exact ⟨(sphereEquivalence c).forward_point, (sphereEquivalence c).backward_point,
    fun t => (sphereEquivalence c).left.eq_snd t (by simp),
    fun t => (sphereEquivalence c).right.eq_snd t (by simp)⟩

/-- Reduction continues to fix the WHOLE retained endpoint, not just its apex. -/
theorem reduction_fixed (t : I) (x : Space c.X) :
    c.reductionSDR.homotopy (t, c.reduction.inclusion x) = c.reduction.inclusion x :=
  c.reductionSDR.homotopy.eq_fst t x.2

/-- The original ambient coordinate bridge, including labels outside lambda. -/
theorem disk_original_coordinates (x : (attachment c).Disk) :
    (∀ i : c.lambda, (c.reduction.inclusion ((attachment c).diskIn x)).1 i.1 = x.1 i) ∧
    (∀ v ∉ c.lambda, (c.reduction.inclusion ((attachment c).diskIn x)).1 v = 0) :=
  (attachment c).diskIn_coordinates x

private theorem K_supported :
    FiniteAlexanderDualCollapse.Supported (insert c.a c.W) c.K := by
  intro s hs v hv
  rcases hs with he | hc
  · exact Finset.mem_insert_of_mem (he.2.1 hv)
  · by_cases h : v = c.a
    · exact Finset.mem_insert.mpr (Or.inl h)
    · have hv' : v ∈ s.erase c.a := Finset.mem_erase.mpr ⟨h, hv⟩
      rcases hc.2 with he | hd
      · rw [he] at hv'
        exact (Finset.notMem_empty v hv').elim
      · exact Finset.mem_insert_of_mem (hd.2.1 hv')

/-- A true ambient ghost remains zero in every actual K point, hence in all
constructed K-valued inverse and homotopy outputs. A lambda-exterior label
that is an actual core vertex is intentionally NOT called an ambient ghost. -/
theorem ambient_ghost (x : Space c.K) (v : V) (hv : v ∉ insert c.a c.W) : x.1 v = 0 := by
  obtain ⟨s, hs, hx⟩ := (realization_mem_iff _ _).mp x.2
  exact hx.2.2 v (fun h => hv ((K_supported c) s hs h))

/-- Source-level preservation of the original attaching inclusion: this is
literally the owner's coordinate j, not a replacement null or zero map. -/
def originalAttachingMap : C(Space c.Dstar, Space c.Estar) := c.j

end Certificate
end D5.S3.Geometry.FiniteCriticalCellSphere
