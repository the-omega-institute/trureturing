/- GID: D5/S3/Geometry/Gluing/TruncatedTetrahedronRelativeCW
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/TruncatedTetrahedronRelativeCW
   mirror-E: none(waiver:relative-cw-topological-construction)
   anchors: [mathlib/module/Mathlib.Topology.CWComplex.Classical.Finite]
   utility: none
   digest: Finite raw tetrahedron pairings carry actual relative cells above their closed face skeleton. -/

import D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry
import Mathlib.Topology.CWComplex.Classical.Finite

set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

open Set Metric Topology
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan
  (TruncatedTetrahedron TruncatedPoint)
open D5.S3.Geometry.Gluing.RawFaceLinkPathConnected (sigma frame chi)
open D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
open private paired_twice from D5.S3.Geometry.Gluing.RawFaceLinkPathConnected

open D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry (cell_geometry)
open private Model Model.bulk
  sigma_face
  continuous_q
  step_face
  interior_normal_form
  actual_face_classification
  diskExtend_coe
  diskPartial
  diskPartial_continuousOn
  diskPartial_continuousOn_symm
  polyBall
  polyBall_symm_interior_iff
  polyBall_symm_frontier
  bulkRealize_injective
  bulkHomeomorph
  bulkRealize_strict_iff
  faceBall
  faceRealize
  faceRealize_fixed
  faceRealize_injective
  faceHomeomorph
  capRealize_interior
  hexRealize_faceInterior
  from D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry

attribute [local instance] instT2SpaceTruncatedQuotient

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

variable (P : RawFacePairing T)

/- Full EqvGen, including self-pairings, is used in the next two facts. -/

private theorem hex_same_face_fiber (a b : TruncatedPoint T) (f : Fin 4)
    (ha : FaceInterior a f) (hb : b.1 = a.1) (hbzero : b.2.val f = 0)
    (h : Relation.EqvGen (TruncatedStep P) a b) : b = a := by
  rcases ((actual_face_classification P a b f ha).2.mp h) with he | he
  · exact he
  · have hs : TruncatedStep P a b := ⟨f, ha.1, he⟩
    have hbf := step_face P ha hs
    have hf : f = (P.facePair (a.1, f)).2 := hbf.2 f hbzero
    have ht : b.1 = (P.facePair (a.1, f)).1 :=
      congrArg (fun z : TruncatedPoint T => z.1) he
    exact (P.pairFixedFree (a.1, f) (Prod.ext (ht.symm.trans hb) hf.symm)).elim

def topCharacteristic (t : T) : Disk 3 → (TruncatedQuotient P) := (q P) ∘ bulkDiskPoint t
def faceCharacteristic (k : FaceShape) (t : T) (j : Fin 4) : Disk 2 → (TruncatedQuotient P) :=
  (q P) ∘ faceDiskPoint k t j

private theorem continuous_bulkDiskPoint (t : T) : Continuous (bulkDiskPoint t) :=
  continuous_const.prodMk (bulkHomeomorph.continuous.comp (polyBall Model.bulk).symm.continuous)

private theorem continuous_faceDiskPoint (k : FaceShape) (t : T) (j : Fin 4) :
    Continuous (faceDiskPoint k t j) :=
  (continuous_subtype_val.comp (faceHomeomorph k t j).continuous).comp
    (faceBall k).symm.continuous

private theorem continuous_topCharacteristic (t : T) : Continuous (topCharacteristic P t) :=
  (continuous_q P).comp (continuous_bulkDiskPoint t)

private theorem continuous_faceCharacteristic (k : FaceShape) (t : T) (j : Fin 4) :
    Continuous (faceCharacteristic P k t j) :=
  (continuous_q P).comp (continuous_faceDiskPoint k t j)

private theorem topCharacteristic_fiber (t : T) (x y : Disk 3)
    (hx : x.val ∈ ball 0 1) (h : topCharacteristic P t y = topCharacteristic P t x) : y = x := by
  have hi := (polyBall_symm_interior_iff Model.bulk x).mpr hx
  have hs := (bulkRealize_strict_iff ((polyBall Model.bulk).symm x)).mp hi
  have ha : Interior (bulkDiskPoint t x) := fun i => ne_of_gt (hs i).1
  have he : bulkDiskPoint t y = bulkDiskPoint t x :=
    (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h.symm)
  exact (polyBall Model.bulk).symm.injective
    (bulkRealize_injective (congrArg Prod.snd he))

private theorem faceCharacteristic_fiber (k : FaceShape) (t : T) (j : Fin 4) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) (h : faceCharacteristic P k t j y = faceCharacteristic P k t j x) :
    y = x := by
  have hi := (faceBall_symm_interior_iff k x).mpr hx
  have hr : Relation.EqvGen (TruncatedStep P)
      (faceDiskPoint k t j x) (faceDiskPoint k t j y) := Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h.symm
  have he : faceDiskPoint k t j y = faceDiskPoint k t j x := by
    cases k
    · exact hex_same_face_fiber P _ _ j (hexRealize_faceInterior t j _ hi) rfl
        (faceRealize_fixed .hex t j _) hr
    · exact (interior_normal_form P _ _ (capRealize_interior t j _ hi)).mp hr
  exact (faceBall k).symm.injective (faceRealize_injective k t j he)

/-- Three-dimensional characteristic maps in the full quotient. -/
def topCell (t : T) : PartialEquiv (Fin 3 → ℝ) (TruncatedQuotient P) :=
  diskPartial (topCharacteristic P t) (continuous_topCharacteristic P t) (topCharacteristic_fiber P t)

/-- Directed face maps retain the entire closed cap or original zero face. -/
def directedFaceCell (k : FaceShape) (t : T) (j : Fin 4) :
    PartialEquiv (Fin 2 → ℝ) (TruncatedQuotient P) :=
  diskPartial (faceCharacteristic P k t j) (continuous_faceCharacteristic P k t j)
    (faceCharacteristic_fiber P k t j)

@[simp] private theorem topCell_source (t : T) : (topCell P t).source = ball 0 1 := rfl
private theorem topCell_continuousOn (t : T) : ContinuousOn (topCell P t) (closedBall 0 1) :=
  diskPartial_continuousOn _ _ _
private theorem topCell_continuousOn_symm (t : T) :
    ContinuousOn (topCell P t).symm (topCell P t).target :=
  diskPartial_continuousOn_symm _ _ _
private theorem directedFaceCell_continuousOn (k : FaceShape) (t : T) (j : Fin 4) :
    ContinuousOn (directedFaceCell P k t j) (closedBall 0 1) :=
  diskPartial_continuousOn _ _ _
private theorem directedFaceCell_continuousOn_symm (k : FaceShape) (t : T) (j : Fin 4) :
    ContinuousOn (directedFaceCell P k t j).symm (directedFaceCell P k t j).target :=
  diskPartial_continuousOn_symm _ _ _

@[simp] private theorem topCell_coe_disk (t : T) (x : Disk 3) :
    topCell P t x.val = (q P) (bulkDiskPoint t x) := diskExtend_coe _ x

@[simp] private theorem directedFaceCell_coe_disk (k : FaceShape) (t : T) (j : Fin 4)
    (x : Disk 2) : directedFaceCell P k t j x.val = (q P) (faceDiskPoint k t j x) :=
  diskExtend_coe _ x

private theorem topCell_closed_image (t : T) :
    topCell P t '' closedBall 0 1 = (q P) '' {a : TruncatedPoint T | a.1 = t} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨bulkDiskPoint t ⟨x, hx⟩, rfl, (topCell_coe_disk P t ⟨x, hx⟩).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h, hh⟩ := (cell_geometry P).bulk_reconstruction t
    obtain ⟨x, hx⟩ := h.surjective a.2
    refine ⟨x.val, x.property, ?_⟩
    rw [topCell_coe_disk P, hh x, hx]
    exact congrArg (q P) (Prod.ext ha.symm rfl)

private theorem directedFaceCell_closed_image (k : FaceShape) (t : T) (j : Fin 4) :
    directedFaceCell P k t j '' closedBall 0 1 = (q P) '' faceCarrier k t j := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨faceDiskPoint k t j ⟨x, hx⟩,
      ⟨rfl, faceRealize_fixed k t j _⟩, ?_⟩
    exact (directedFaceCell_coe_disk P k t j ⟨x, hx⟩).symm
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨h, hh⟩ := (cell_geometry P).face_reconstruction k t j
    obtain ⟨x, hx⟩ := h.surjective ⟨a, ha⟩
    refine ⟨x.val, x.property, ?_⟩
    rw [directedFaceCell_coe_disk P, hh x, hx]

private theorem topCell_open_disjoint (t s : T) (hts : t ≠ s) :
    Disjoint (topCell P t '' ball 0 1) (topCell P s '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 3 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 3 := ⟨y, ball_subset_closedBall hy⟩
  have hq : (q P) (bulkDiskPoint t xd) = (q P) (bulkDiskPoint s yd) := by
    rw [← topCell_coe_disk P t xd, ← topCell_coe_disk P s yd]
    exact hxz.trans hyz.symm
  have hs := (bulkRealize_strict_iff ((polyBall Model.bulk).symm xd)).mp
    ((polyBall_symm_interior_iff Model.bulk xd).mpr hx)
  have ha : Interior (bulkDiskPoint t xd) := fun i => ne_of_gt (hs i).1
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) hq)
  exact hts (congrArg (fun z : TruncatedPoint T => z.1) he).symm

private theorem topCell_closed_cover : (⋃ t : T, topCell P t '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨a, rfl⟩ :=
    @Quotient.mk'_surjective _ (Relation.EqvGen.setoid (TruncatedStep P)) z
  apply mem_iUnion.mpr
  refine ⟨a.1, ?_⟩
  rw [topCell_closed_image P]
  exact ⟨a, rfl, rfl⟩


/-- Two directed faces belong to the same free-involution orbit. -/
def pairedFaceSetoid (P : RawFacePairing T) : Setoid (T × Fin 4) where
  r x y := y = x ∨ y = P.facePair x
  iseqv := by
    refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (paired_twice P x).symm
    · intro x y z hxy hyz
      rcases hxy with rfl | rfl
      · exact hyz
      · rcases hyz with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (paired_twice P x)

abbrev PairedFace (P : RawFacePairing T) := Quotient (pairedFaceSetoid P)

/-- A closed original face selected from each actual pairing orbit. -/
def faceRep (r : PairedFace P) : T × Fin 4 := r.out

private theorem face_representatives_separate (r s : PairedFace P)
    (h : faceRep P s = faceRep P r ∨ faceRep P s = P.facePair (faceRep P r)) : s = r := by
  have he : Quotient.mk (pairedFaceSetoid P) (faceRep P r) =
      Quotient.mk (pairedFaceSetoid P) (faceRep P s) := Quotient.sound h
  simpa only [faceRep, Quotient.out_eq] using he.symm

private theorem face_representatives_cover (x : T × Fin 4) :
    ∃ r : PairedFace P, x = faceRep P r ∨ x = P.facePair (faceRep P r) := by
  let r : PairedFace P := Quotient.mk _ x
  exact ⟨r, Quotient.exact (Quotient.out_eq r)⟩

/-- Cap faces are indexed by original corners; zero faces by actual pairing orbits. -/
abbrev SurfaceCell := (T × Fin 4) ⊕ PairedFace P

def surfaceCell : SurfaceCell P → PartialEquiv (Fin 2 → ℝ) (TruncatedQuotient P)
  | .inl (t,j) => directedFaceCell P .cap t j
  | .inr r => directedFaceCell P .hex (faceRep P r).1 (faceRep P r).2

private def surfaceDiskPoint : SurfaceCell P → Disk 2 → TruncatedPoint T
  | .inl (t,j) => faceDiskPoint .cap t j
  | .inr r => faceDiskPoint .hex (faceRep P r).1 (faceRep P r).2

@[simp] private theorem surfaceCell_coe_disk (c : SurfaceCell P) (x : Disk 2) :
    surfaceCell P c x.val = (q P) (surfaceDiskPoint P c x) := by
  cases c with
  | inl tj => exact directedFaceCell_coe_disk P .cap tj.1 tj.2 x
  | inr r => exact directedFaceCell_coe_disk P .hex _ _ x

@[simp] private theorem surfaceCell_source (c : SurfaceCell P) : (surfaceCell P c).source = ball 0 1 := by
  cases c <;> rfl

private theorem surfaceCell_continuousOn (c : SurfaceCell P) :
    ContinuousOn (surfaceCell P c) (closedBall 0 1) := by
  cases c
  · exact directedFaceCell_continuousOn P .cap _ _
  · exact directedFaceCell_continuousOn P .hex _ _

private theorem surfaceCell_continuousOn_symm (c : SurfaceCell P) :
    ContinuousOn (surfaceCell P c).symm (surfaceCell P c).target := by
  cases c
  · exact directedFaceCell_continuousOn_symm P .cap _ _
  · exact directedFaceCell_continuousOn_symm P .hex _ _

private theorem hex_open_pair_tag (a b : TruncatedPoint T) (f g : Fin 4)
    (ha : FaceInterior a f) (hb : FaceInterior b g)
    (h : Relation.EqvGen (TruncatedStep P) a b) :
    (b.1, g) = (a.1, f) ∨ (b.1, g) = P.facePair (a.1, f) := by
  rcases (actual_face_classification P a b f ha).2.mp h with he | he
  · left
    have hbf : b.2.val f = 0 := by rw [he]; exact ha.1
    have hg : g = f := (hb.2 f hbf).symm
    have ht : b.1 = a.1 := congrArg (fun z : TruncatedPoint T => z.1) he
    exact Prod.ext ht hg
  · right
    have hb' := step_face P ha
      (show TruncatedStep P a b from ⟨f, ha.1, he⟩)
    have hbzero : b.2.val (P.facePair (a.1, f)).2 = 0 := hb'.1
    have hg : g = (P.facePair (a.1, f)).2 := (hb.2 _ hbzero).symm
    have ht : b.1 = (P.facePair (a.1, f)).1 :=
      congrArg (fun z : TruncatedPoint T => z.1) he
    exact Prod.ext ht hg

private theorem cap_open_tag (t s : T) (j l : Fin 4)
    (x y : Disk 2) (hx : x.val ∈ ball 0 1)
    (h : (q P) (faceDiskPoint .cap t j x) = (q P) (faceDiskPoint .cap s l y)) :
    (s, l) = (t, j) := by
  have hi := (faceBall_symm_interior_iff .cap x).mpr hx
  have ha := capRealize_interior t j ((faceBall .cap).symm x) hi
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
  have hj : l = j := by
    by_contra hlj
    have hl := ((faceRealize_strict_iff .cap t j _).mp hi l hlj).2
    have hy : (faceDiskPoint .cap s l y).2.val l = 3 / 4 :=
      faceRealize_fixed .cap s l _
    rw [he] at hy
    linarith
  have ht : s = t := congrArg (fun z : TruncatedPoint T => z.1) he
  exact Prod.ext ht hj

private theorem cap_hex_open_ne (t s : T) (j l : Fin 4) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) :
    (q P) (faceDiskPoint .cap t j x) ≠ (q P) (faceDiskPoint .hex s l y) := by
  intro h
  have ha := capRealize_interior t j ((faceBall .cap).symm x)
    ((faceBall_symm_interior_iff .cap x).mpr hx)
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
  have hz : (faceDiskPoint .hex s l y).2.val l = 0 := faceRealize_fixed .hex s l _
  rw [he] at hz
  exact ha l hz

private theorem surface_open_index (c d : SurfaceCell P) (x y : Disk 2)
    (hx : x.val ∈ ball 0 1) (hy : y.val ∈ ball 0 1)
    (h : (q P) (surfaceDiskPoint P c x) = (q P) (surfaceDiskPoint P d y)) : c = d := by
  cases c with
  | inl tj =>
    cases d with
    | inl sl => exact congrArg Sum.inl (cap_open_tag P tj.1 sl.1 tj.2 sl.2 x y hx h).symm
    | inr r => exact (cap_hex_open_ne P tj.1 _ tj.2 _ x y hx h).elim
  | inr r =>
    cases d with
    | inl sl => exact (cap_hex_open_ne P sl.1 _ sl.2 _ y x hy h.symm).elim
    | inr s =>
      have ha := hexRealize_faceInterior
        (faceRep P r).1 (faceRep P r).2
        ((faceBall .hex).symm x) ((faceBall_symm_interior_iff .hex x).mpr hx)
      have hb := hexRealize_faceInterior
        (faceRep P s).1 (faceRep P s).2
        ((faceBall .hex).symm y) ((faceBall_symm_interior_iff .hex y).mpr hy)
      have ht := hex_open_pair_tag P _ _ _ _ ha hb (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
      have hr : s = r := face_representatives_separate P r s (by
        simpa only [faceRealize] using ht)
      exact congrArg Sum.inr hr.symm

private theorem surfaceCell_open_disjoint (c d : SurfaceCell P) (hcd : c ≠ d) :
    Disjoint (surfaceCell P c '' ball 0 1) (surfaceCell P d '' ball 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 2 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 2 := ⟨y, ball_subset_closedBall hy⟩
  apply hcd
  apply surface_open_index P c d xd yd hx hy
  rw [← surfaceCell_coe_disk P c xd, ← surfaceCell_coe_disk P d yd]
  exact hxz.trans hyz.symm

/-- Actual geometric two-dimensional subset; no CW structure on it is assumed. -/
def faceSkeleton : Set (TruncatedQuotient P) := ⋃ c : SurfaceCell P, surfaceCell P c '' closedBall 0 1

private theorem faceSkeleton_closed : IsClosed (faceSkeleton P) :=
  isClosed_iUnion_of_finite fun c =>
    ((isCompact_closedBall _ _).image_of_continuousOn (surfaceCell_continuousOn P c)).isClosed

private theorem top_surface_open_closed_disjoint (t : T) (c : SurfaceCell P) :
    Disjoint (topCell P t '' ball 0 1) (surfaceCell P c '' closedBall 0 1) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  let xd : Disk 3 := ⟨x, ball_subset_closedBall hx⟩
  let yd : Disk 2 := ⟨y, hy⟩
  have hq : (q P) (bulkDiskPoint t xd) = (q P) (surfaceDiskPoint P c yd) := by
    rw [← topCell_coe_disk P t xd, ← surfaceCell_coe_disk P c yd]
    exact hxz.trans hyz.symm
  have hs := (bulkRealize_strict_iff ((polyBall Model.bulk).symm xd)).mp
    ((polyBall_symm_interior_iff Model.bulk xd).mpr hx)
  have ha : Interior (bulkDiskPoint t xd) := fun i => ne_of_gt (hs i).1
  have he := (interior_normal_form P _ _ ha).mp (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) hq)
  cases c with
  | inl tj =>
    have hcap : (surfaceDiskPoint P (.inl tj) yd).2.val tj.2 = 3 / 4 :=
      faceRealize_fixed .cap tj.1 tj.2 _
    rw [he] at hcap
    exact (ne_of_lt (hs tj.2).2) hcap
  | inr r =>
    have hz : (surfaceDiskPoint P (.inr r) yd).2.val (faceRep P r).2 = 0 :=
      faceRealize_fixed .hex _ _ _
    rw [he] at hz
    exact ha _ hz

private theorem topCell_disjoint_faceSkeleton (t : T) :
    Disjoint (topCell P t '' ball 0 1) (faceSkeleton P) := by
  rw [faceSkeleton, disjoint_iUnion_right]
  exact top_surface_open_closed_disjoint P t


private theorem zero_face_mem_faceSkeleton (a : TruncatedPoint T) (j : Fin 4)
    (hz : a.2.val j = 0) : q P a ∈ (faceSkeleton P) := by
  obtain ⟨r, hr | hr⟩ := face_representatives_cover P (a.1,j)
  · apply mem_iUnion.mpr
    refine ⟨Sum.inr r, ?_⟩
    change q P a ∈ directedFaceCell P .hex _ _ '' closedBall 0 1
    rw [directedFaceCell_closed_image P]
    exact ⟨a, ⟨congrArg Prod.fst hr, (congrArg Prod.snd hr) ▸ hz⟩, rfl⟩
  · let b := truncatedMove P j a
    have hp : P.facePair (a.1,j) = faceRep P r := by
      rw [hr]
      exact paired_twice P _
    have hb : b ∈ faceCarrier .hex (faceRep P r).1 (faceRep P r).2 := by
      constructor
      · exact congrArg Prod.fst hp
      · change a.2.val ((sigma P (a.1,j)).symm (faceRep P r).2) = 0
        rw [← hp, ← sigma_face P (a.1,j), Equiv.symm_apply_apply]
        exact hz
    have hab : q P a = q P b := Quotient.sound
      (s := Relation.EqvGen.setoid (TruncatedStep P))
      (Relation.EqvGen.rel _ _ (show TruncatedStep P a b from ⟨j,hz,rfl⟩))
    rw [hab]
    apply mem_iUnion.mpr
    refine ⟨Sum.inr r, ?_⟩
    change q P b ∈ directedFaceCell P .hex _ _ '' closedBall 0 1
    rw [directedFaceCell_closed_image P]
    exact ⟨b,hb,rfl⟩

private theorem cap_face_mem_faceSkeleton (a : TruncatedPoint T) (j : Fin 4)
    (hc : a.2.val j = 3 / 4) : (q P) a ∈ (faceSkeleton P) := by
  apply mem_iUnion.mpr
  refine ⟨Sum.inl (a.1, j), ?_⟩
  change (q P) a ∈ directedFaceCell P .cap a.1 j '' closedBall 0 1
  rw [directedFaceCell_closed_image P]
  exact ⟨a, ⟨rfl, hc⟩, rfl⟩

private theorem top_sphere_has_boundary_coordinate (t : T) (x : Disk 3)
    (hx : x.val ∈ sphere 0 1) :
    ∃ j : Fin 4, (bulkDiskPoint t x).2.val j = 0 ∨
      (bulkDiskPoint t x).2.val j = 3 / 4 := by
  classical
  by_contra hn
  have hs : ∀ j, 0 < (bulkDiskPoint t x).2.val j ∧
      (bulkDiskPoint t x).2.val j < 3 / 4 := by
    intro j
    have hb := (bulkDiskPoint t x).2.property.1 j
    have h0 : (bulkDiskPoint t x).2.val j ≠ 0 := fun he => hn ⟨j, Or.inl he⟩
    have hc : (bulkDiskPoint t x).2.val j ≠ 3 / 4 := fun he => hn ⟨j, Or.inr he⟩
    constructor
    · by_contra hbad
      exact h0 (by linarith)
    · by_contra hbad
      exact hc (by linarith)
  have hi := (bulkRealize_strict_iff ((polyBall Model.bulk).symm x)).mpr hs
  exact disjoint_left.mp disjoint_interior_frontier hi (polyBall_symm_frontier Model.bulk x hx)

/-- Each original three-cell sphere maps into the actual closed face skeleton. -/
private theorem topCell_sphere_mapsTo (t : T) : MapsTo (topCell P t) (sphere 0 1) (faceSkeleton P) := by
  intro x hx
  let xd : Disk 3 := ⟨x, sphere_subset_closedBall hx⟩
  rw [topCell_coe_disk P t xd]
  obtain ⟨j, hj | hj⟩ := top_sphere_has_boundary_coordinate t xd hx
  · exact zero_face_mem_faceSkeleton P _ j hj
  · exact cap_face_mem_faceSkeleton P _ j hj

def HigherCell (n : ℕ) := {t : T // n = 3}

def higherMap (n : ℕ) (i : HigherCell (T := T) n) : PartialEquiv (Fin n → ℝ) (TruncatedQuotient P) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell P t

private theorem higher_finite_cell (n : ℕ) : Finite (HigherCell (T := T) n) := by
  unfold HigherCell
  infer_instance

private theorem higher_eventually_empty : ∀ᶠ n in Filter.atTop, IsEmpty (HigherCell (T := T) n) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨4, ?_⟩
  intro n hn
  refine ⟨?_⟩
  rintro ⟨t, ht⟩
  omega

private theorem higher_source (n : ℕ) (i : HigherCell (T := T) n) : (higherMap P n i).source = ball 0 1 := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_source P t

private theorem higher_continuousOn (n : ℕ) (i : HigherCell (T := T) n) :
    ContinuousOn (higherMap P n i) (closedBall 0 1) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_continuousOn P t

private theorem higher_continuousOn_symm (n : ℕ) (i : HigherCell (T := T) n) :
    ContinuousOn (higherMap P n i).symm (higherMap P n i).target := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_continuousOn_symm P t

private theorem higher_pairwiseDisjoint :
    (univ : Set (Σ n, HigherCell (T := T) n)).PairwiseDisjoint
      (fun ni => higherMap P ni.1 ni.2 '' ball 0 1) := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
  rintro ⟨n, ⟨t, ht⟩⟩ _ ⟨m, ⟨s, hs⟩⟩ _ hne
  subst n
  subst m
  apply topCell_open_disjoint P t s
  intro hts
  apply hne
  subst s
  rfl

private theorem higher_disjointBase (n : ℕ) (i : HigherCell (T := T) n) :
    Disjoint (higherMap P n i '' ball 0 1) (faceSkeleton P) := by
  rcases i with ⟨t, h⟩
  subst n
  exact topCell_disjoint_faceSkeleton P t

private theorem higher_mapsTo (n : ℕ) (i : HigherCell (T := T) n) :
    MapsTo (higherMap P n i) (sphere 0 1)
      ((faceSkeleton P) ∪ ⋃ (m < n) (j : HigherCell (T := T) m), higherMap P m j '' closedBall 0 1) := by
  rcases i with ⟨t, h⟩
  subst n
  intro x hx
  exact Or.inl (topCell_sphere_mapsTo P t hx)

private theorem higher_union :
    (faceSkeleton P) ∪ ⋃ (n : ℕ) (i : HigherCell (T := T) n), higherMap P n i '' closedBall 0 1 = univ := by
  apply eq_univ_of_forall
  intro z
  right
  have hz : z ∈ ⋃ t : T, topCell P t '' closedBall 0 1 := by rw [topCell_closed_cover P]; trivial
  obtain ⟨t, ht⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨3, mem_iUnion.mpr ⟨⟨t, rfl⟩, ht⟩⟩

/-- The original retained quotient as a finite relative CW complex above its closed faces. -/
def relativeCW : RelCWComplex (univ : Set (TruncatedQuotient P)) (faceSkeleton P) :=
  RelCWComplex.mkFinite univ (faceSkeleton P) (HigherCell (T := T)) (higherMap P)
    (higher_eventually_empty (T := T)) (higher_finite_cell (T := T)) (higher_source P) (higher_continuousOn P)
    (higher_continuousOn_symm P) (higher_pairwiseDisjoint P) (higher_disjointBase P)
    (higher_mapsTo P) (faceSkeleton_closed P) (higher_union P)

private theorem relativeCW_finite :
    letI := relativeCW P
    RelCWComplex.Finite (univ : Set (TruncatedQuotient P)) :=
  RelCWComplex.finite_mkFinite univ (faceSkeleton P) (HigherCell (T := T)) (higherMap P)
    (higher_eventually_empty (T := T)) (higher_finite_cell (T := T)) (higher_source P) (higher_continuousOn P)
    (higher_continuousOn_symm P) (higher_pairwiseDisjoint P) (higher_disjointBase P)
    (higher_mapsTo P) (faceSkeleton_closed P) (higher_union P)

/-- Boundary strata of the retained tetrahedra, including every closed-face tie. -/
def retainedBoundary : Set (TruncatedPoint T) :=
  {a | ∃ j : Fin 4, a.2.val j = 0 ∨ a.2.val j = 3 / 4}

private theorem faceSkeleton_eq_boundaryImage :
    faceSkeleton P = q P '' retainedBoundary (T := T) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    cases c with
    | inl tj =>
      change z ∈ directedFaceCell P .cap tj.1 tj.2 '' closedBall 0 1 at hc
      rw [directedFaceCell_closed_image P] at hc
      obtain ⟨a,ha,he⟩ := hc
      exact ⟨a, ⟨tj.2, Or.inr ha.2⟩, he⟩
    | inr r =>
      change z ∈ directedFaceCell P .hex (faceRep P r).1 (faceRep P r).2 '' closedBall 0 1 at hc
      rw [directedFaceCell_closed_image P] at hc
      obtain ⟨a,ha,he⟩ := hc
      exact ⟨a, ⟨(faceRep P r).2, Or.inl ha.2⟩, he⟩
  · rintro ⟨a,⟨j,hj | hj⟩,rfl⟩
    · exact zero_face_mem_faceSkeleton P a j hj
    · exact cap_face_mem_faceSkeleton P a j hj

/-- Geometry of the original full quotient and its actual upper-dimensional cells.
The projection argument identifies the ambient quotient observations used by
these maps. The relative complex adds the original three-cells to the closed
face skeleton. -/
structure UpperGeometry (projection : TruncatedPoint T → TruncatedQuotient P) : Prop where
  interior_fibers : ∀ (a b : TruncatedPoint T), Interior a →
    (projection a = projection b ↔ b = a)
  face_fibers : ∀ (a b : TruncatedPoint T) (f : Fin 4), FaceInterior a f →
    truncatedMove P f a ≠ a ∧
      (projection a = projection b ↔ b = a ∨ b = truncatedMove P f a)
  top_characteristic : ∀ t : T,
    Continuous (topCharacteristic P t) ∧
    (∀ x : Disk 3, topCell P t x.val = projection (bulkDiskPoint t x)) ∧
    (∀ (x y : Disk 3), x.val ∈ ball 0 1 →
      topCharacteristic P t y = topCharacteristic P t x → y = x)
  face_characteristic : ∀ (k : FaceShape) (t : T) (j : Fin 4),
    Continuous (faceCharacteristic P k t j) ∧
    (∀ x : Disk 2, directedFaceCell P k t j x.val = projection (faceDiskPoint k t j x)) ∧
    (∀ (x y : Disk 2), x.val ∈ ball 0 1 →
      faceCharacteristic P k t j y = faceCharacteristic P k t j x → y = x)
  top_charts : ∀ t : T, (topCell P t).source = ball 0 1 ∧
    ContinuousOn (topCell P t) (closedBall 0 1) ∧
    ContinuousOn (topCell P t).symm (topCell P t).target
  face_charts : ∀ c : SurfaceCell P, (surfaceCell P c).source = ball 0 1 ∧
    ContinuousOn (surfaceCell P c) (closedBall 0 1) ∧
    ContinuousOn (surfaceCell P c).symm (surfaceCell P c).target
  top_closed_image : ∀ t : T,
    topCell P t '' closedBall 0 1 = projection '' {a : TruncatedPoint T | a.1 = t}
  directed_face_closed_image : ∀ (k : FaceShape) (t : T) (j : Fin 4),
    directedFaceCell P k t j '' closedBall 0 1 = projection '' faceCarrier k t j
  top_open_disjoint : ∀ (t s : T), t ≠ s →
    Disjoint (topCell P t '' ball 0 1) (topCell P s '' ball 0 1)
  face_open_disjoint : ∀ (c d : SurfaceCell P), c ≠ d →
    Disjoint (surfaceCell P c '' ball 0 1) (surfaceCell P d '' ball 0 1)
  top_closed_cover : (⋃ t : T, topCell P t '' closedBall 0 1) = univ
  skeleton_image : faceSkeleton P = projection '' retainedBoundary (T := T)
  skeleton_closed : IsClosed (faceSkeleton P)
  top_disjoint_skeleton : ∀ t : T,
    Disjoint (topCell P t '' ball 0 1) (faceSkeleton P)
  sphere_attaching : ∀ t : T,
    MapsTo (topCell P t) (sphere 0 1) (faceSkeleton P)
  finite_relative : letI := relativeCW P
    RelCWComplex.Finite (univ : Set (TruncatedQuotient P))

/-- Every finite discrete raw tetrahedron pairing has genuine characteristic
maps on its original retained quotient and a finite relative CW structure above
the actual closed face skeleton. Pairing orbits index the zero faces. -/
theorem upper_geometry : UpperGeometry P (q P) where
  interior_fibers := (cell_geometry P).interior_fibers
  face_fibers := (cell_geometry P).face_fibers
  top_characteristic t := ⟨continuous_topCharacteristic P t,
    topCell_coe_disk P t, topCharacteristic_fiber P t⟩
  face_characteristic k t j := ⟨continuous_faceCharacteristic P k t j,
    directedFaceCell_coe_disk P k t j, faceCharacteristic_fiber P k t j⟩
  top_charts t := ⟨topCell_source P t, topCell_continuousOn P t, topCell_continuousOn_symm P t⟩
  face_charts c := ⟨surfaceCell_source P c,
    surfaceCell_continuousOn P c, surfaceCell_continuousOn_symm P c⟩
  top_closed_image := topCell_closed_image P
  directed_face_closed_image := directedFaceCell_closed_image P
  top_open_disjoint := topCell_open_disjoint P
  face_open_disjoint := surfaceCell_open_disjoint P
  top_closed_cover := topCell_closed_cover P
  skeleton_image := faceSkeleton_eq_boundaryImage P
  skeleton_closed := faceSkeleton_closed P
  top_disjoint_skeleton := topCell_disjoint_faceSkeleton P
  sphere_attaching := topCell_sphere_mapsTo P
  finite_relative := relativeCW_finite P

end D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
