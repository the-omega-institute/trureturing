/- GID: D5/S3/Geometry/Gluing/TruncatedTetrahedronLowerCW
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/TruncatedTetrahedronLowerCW
   mirror-E: none(waiver:lower-cw-topological-construction)
   anchors: [mathlib/module/Mathlib.Topology.CWComplex.Classical.Finite]
   utility: none
   digest: Midpoint subdivision gives lower cells on the original truncated quotient. -/

import D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

/-! Actual vertices and midpoint-subdivided edges of the original truncated quotient. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW

open Set Metric Topology
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedTetrahedron TruncatedPoint)
open D5.S3.Geometry.Gluing.RawFaceLinkPathConnected (sigma)
open D5.S3.Geometry.Gluing.FiniteZeroGuardedClosure
open D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
open D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry (cell_geometry)
open private continuous_q diskPartial diskPartial_continuousOn
  diskPartial_continuousOn_symm diskExtend_coe sigma_face sigma_inverse
  from D5.S3.Geometry.Gluing.TruncatedTetrahedronCellGeometry
attribute [local instance] instT2SpaceTruncatedQuotient

variable {T : Type*} [Fintype T] [TopologicalSpace T] [DiscreteTopology T]

/-- An ordered retained edge occurrence, pointing toward its old truncated vertex. -/
abbrev HalfOccurrence (T : Type*) := T × {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}

private def twoCoords (ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}) (r : ℝ) : Fin 4 → ℝ :=
  fun k => if k = ij.val.1 then r else if k = ij.val.2 then 1-r else 0

private theorem twoCoords_first (ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}) (r : ℝ) :
    twoCoords ij r ij.val.1 = r := by simp [twoCoords]
private theorem twoCoords_second (ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}) (r : ℝ) :
    twoCoords ij r ij.val.2 = 1-r := by simp [twoCoords, Ne.symm ij.property]

private theorem twoCoords_sum (ij : {ij : Fin 4 × Fin 4 // ij.1 ≠ ij.2}) (r : ℝ) :
    ∑ k, twoCoords ij r k = 1 := by
  have he : twoCoords ij r = fun k =>
      (if k = ij.val.1 then r else 0) + (if k = ij.val.2 then 1-r else 0) := by
    funext k
    by_cases hi : k = ij.val.1
    · subst k
      simp [twoCoords,ij.property]
    · simp [twoCoords,hi]
  rw [he,Finset.sum_add_distrib]
  simp


/-- The closed retained halfedge in the original four coordinates. -/
def halfPoint (h : HalfOccurrence T) (r : Set.Icc (1 / 2 : ℝ) (3 / 4)) : TruncatedPoint T :=
  (h.1, ⟨twoCoords h.2 r.val, (by
    intro i
    dsimp [twoCoords]
    split_ifs <;> constructor <;> linarith [r.property.1, r.property.2]), twoCoords_sum h.2 r.val⟩)

def oldPoint (h : HalfOccurrence T) : TruncatedPoint T := halfPoint h ⟨3 / 4, by norm_num⟩
def midPoint (h : HalfOccurrence T) : TruncatedPoint T := halfPoint h ⟨1 / 2, by norm_num⟩

private def reindex (rho : Equiv.Perm (Fin 4)) (a : TruncatedTetrahedron) : TruncatedTetrahedron :=
  ⟨fun i => a.val (rho.symm i), (fun i => a.property.1 _),
    (rho.symm.sum_comp a.val).trans a.property.2⟩

private theorem transport (P : RawFacePairing T) (a b : TruncatedPoint T)
    (h : q P a = q P b) :
    ∃ rho : Equiv.Perm (Fin 4), b.2 = reindex rho a.2 ∧
      ∀ z : TruncatedTetrahedron, (∀ i, a.2.val i = 0 → z.val i = 0) →
        q P (a.1,z) = q P (b.1,reindex rho z) := by
  let S : Set (Fin 4 → ℝ) := {z | (∀ i, 0 ≤ z i ∧ z i ≤ 3 / 4) ∧ (∑ i, z i) = 1}
  have hI : ∀ (rho : Equiv.Perm (Fin 4)) (z : Fin 4 → ℝ),
      z ∈ S → (fun i => z (rho.symm i)) ∈ S := by
    intro rho z hz
    exact ⟨fun i => hz.1 _, (rho.symm.sum_comp z).trans hz.2⟩
  obtain ⟨rho,Z,hg,hz,hb⟩ :=
    ((uniform_transport_and_closed_relation S hI
      (fun x : T × Fin 4 => (P.facePair x).1) (sigma P)).1 a b).mp
        (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) h)
  refine ⟨rho,hb,?_⟩
  intro z hzero
  exact Quotient.sound (s := Relation.EqvGen.setoid (TruncatedStep P))
    (hg z (fun i hi => hzero i (hz i hi)))

private theorem half_zero_iff (h : HalfOccurrence T) (r : Set.Icc (1 / 2 : ℝ) (3 / 4))
    (i : Fin 4) : (halfPoint h r).2.val i = 0 ↔ i ≠ h.2.val.1 ∧ i ≠ h.2.val.2 := by
  dsimp [halfPoint, twoCoords]
  split_ifs <;> simp_all <;> linarith [r.property.1,r.property.2]

private def movedHalf (h : HalfOccurrence T) (u : T) (rho : Equiv.Perm (Fin 4)) : HalfOccurrence T :=
  (u, ⟨(rho h.2.val.1,rho h.2.val.2), fun he => h.2.property (rho.injective he)⟩)

private theorem half_reindex (h : HalfOccurrence T) (u : T) (rho : Equiv.Perm (Fin 4))
    (r : Set.Icc (1 / 2 : ℝ) (3 / 4)) :
    (halfPoint (movedHalf h u rho) r).2 = reindex rho (halfPoint h r).2 := by
  apply Subtype.ext
  funext i
  simp only [halfPoint, movedHalf, reindex, twoCoords]
  have h1 : rho.symm i = h.2.val.1 ↔ i = rho h.2.val.1 := rho.symm_apply_eq
  have h2 : rho.symm i = h.2.val.2 ↔ i = rho h.2.val.2 := rho.symm_apply_eq
  simp only [h1,h2]

private theorem half_parameter (h k : HalfOccurrence T)
    (r s : Set.Icc (1 / 2 : ℝ) (3 / 4)) (rho : Equiv.Perm (Fin 4))
    (he : (halfPoint k s).2 = reindex rho (halfPoint h r).2) : r = s := by
  have hr : r.val ≤ s.val := by
    have hv := congrArg (fun a : TruncatedTetrahedron => a.val (rho h.2.val.1)) he
    change twoCoords k.2 s.val (rho h.2.val.1) =
      twoCoords h.2 r.val (rho.symm (rho h.2.val.1)) at hv
    rw [Equiv.symm_apply_apply, twoCoords_first] at hv
    dsimp [twoCoords] at hv
    split_ifs at hv <;> linarith [s.property.1]
  have hs : s.val ≤ r.val := by
    have hv := congrArg (fun a : TruncatedTetrahedron => a.val k.2.val.1) he
    change twoCoords k.2 s.val k.2.val.1 = twoCoords h.2 r.val (rho.symm k.2.val.1) at hv
    rw [twoCoords_first] at hv
    dsimp [twoCoords] at hv
    split_ifs at hv <;> linarith [r.property.1]
  exact Subtype.ext (le_antisymm hr hs)

private theorem half_support (h k : HalfOccurrence T)
    (r : Set.Icc (1 / 2 : ℝ) (3 / 4)) (hr : 1 / 2 < r.val)
    (he : halfPoint h r = halfPoint k r) : h = k := by
  have ht := congrArg (fun a : TruncatedPoint T => a.1) he
  have hi : h.2.val.1 = k.2.val.1 := by
    have hv := congrArg (fun a : TruncatedPoint T => a.2.val h.2.val.1) he
    change twoCoords h.2 r.val h.2.val.1 = twoCoords k.2 r.val h.2.val.1 at hv
    rw [twoCoords_first] at hv
    dsimp [twoCoords] at hv
    split_ifs at hv with hh hj
    · exact hh
    · linarith
    · linarith
  have hj : h.2.val.2 = k.2.val.2 := by
    have hv := congrArg (fun a : TruncatedPoint T => a.2.val h.2.val.2) he
    change twoCoords h.2 r.val h.2.val.2 = twoCoords k.2 r.val h.2.val.2 at hv
    rw [twoCoords_second] at hv
    dsimp [twoCoords] at hv
    split_ifs at hv with hh hj
    · exact (h.2.property (hi.trans hh.symm)).elim
    · exact hj
    · linarith [r.property.2]
  exact Prod.ext ht (Subtype.ext (Prod.ext hi hj))

private theorem half_transport (P : RawFacePairing T) (h k : HalfOccurrence T)
    (he : q P (oldPoint h) = q P (oldPoint k))
    (r : Set.Icc (1 / 2 : ℝ) (3 / 4)) : q P (halfPoint h r) = q P (halfPoint k r) := by
  obtain ⟨rho,hb,hg⟩ := transport P _ _ he
  let l := movedHalf h k.1 rho
  have hl : halfPoint k ⟨3 / 4, by norm_num⟩ = halfPoint l ⟨3 / 4, by norm_num⟩ :=
    Prod.ext rfl (hb.trans (half_reindex h k.1 rho _).symm)
  have hkl : k = l := half_support k l _ (by norm_num) hl
  have hz : ∀ i, (oldPoint h).2.val i = 0 → (halfPoint h r).2.val i = 0 := by
    intro i hi
    exact (half_zero_iff h r i).mpr ((half_zero_iff h _ i).mp hi)
  have heq := hg (halfPoint h r).2 hz
  change q P (halfPoint h r) = q P (k.1,reindex rho (halfPoint h r).2) at heq
  rw [← half_reindex h k.1 rho r] at heq
  change q P (halfPoint h r) = q P (halfPoint l r) at heq
  simpa only [← hkl] using heq

private theorem half_fiber (P : RawFacePairing T) (h k : HalfOccurrence T)
    (r s : Set.Icc (1 / 2 : ℝ) (3 / 4)) (hr : 1 / 2 < r.val)
    (he : q P (halfPoint h r) = q P (halfPoint k s)) :
    r = s ∧ q P (oldPoint h) = q P (oldPoint k) := by
  obtain ⟨rho,hb,hg⟩ := transport P _ _ he
  have hrs := half_parameter h k r s rho hb
  subst s
  let l := movedHalf h k.1 rho
  have hkl : k = l := half_support k l r hr
    (Prod.ext rfl (hb.trans (half_reindex h k.1 rho r).symm))
  have hz : ∀ i, (halfPoint h r).2.val i = 0 → (oldPoint h).2.val i = 0 := by
    intro i hi
    exact (half_zero_iff h _ i).mpr ((half_zero_iff h r i).mp hi)
  have heq := hg (oldPoint h).2 hz
  change q P (oldPoint h) = q P (k.1,reindex rho (oldPoint h).2) at heq
  change q P (oldPoint h) = q P (k.1,reindex rho (halfPoint h ⟨3 / 4, by norm_num⟩).2) at heq
  rw [← half_reindex h k.1 rho ⟨3 / 4, by norm_num⟩] at heq
  change q P (oldPoint h) = q P (oldPoint l) at heq
  exact ⟨rfl, by simpa only [← hkl] using heq⟩

/-- Actual old-vertex classes also index the directed halfedges. -/
def oldSetoid (P : RawFacePairing T) : Setoid (HalfOccurrence T) :=
  Setoid.comap (fun h => q P (oldPoint h)) ⊥
abbrev OldVertex (P : RawFacePairing T) := Quotient (oldSetoid P)

def midSetoid (P : RawFacePairing T) : Setoid (HalfOccurrence T) :=
  Setoid.comap (fun h => q P (midPoint h)) ⊥
abbrev MidVertex (P : RawFacePairing T) := Quotient (midSetoid P)
abbrev Vertex (P : RawFacePairing T) := OldVertex P ⊕ MidVertex P

private def halfParameter (x : Disk 1) : Set.Icc (1 / 2 : ℝ) (3 / 4) :=
  ⟨5 / 8 + x.val 0 / 8, by
    have hx : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    have h0 : ‖x.val 0‖ ≤ 1 := (norm_le_pi_norm x.val 0).trans hx
    have hb := abs_le.mp (show |x.val 0| ≤ 1 from h0)
    constructor <;> linarith⟩

def halfCharacteristic (P : RawFacePairing T) (v : OldVertex P) : Disk 1 → TruncatedQuotient P :=
  fun x => q P (halfPoint v.out (halfParameter x))

private theorem halfCharacteristic_continuous (P : RawFacePairing T) (v : OldVertex P) :
    Continuous (halfCharacteristic P v) := by
  have hc : Continuous (fun x : Disk 1 => x.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  apply (continuous_q P).comp
  apply Continuous.prodMk continuous_const
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  dsimp [halfPoint, twoCoords, halfParameter]
  split_ifs
  · exact continuous_const.add (hc.div_const _)
  · exact continuous_const.sub (continuous_const.add (hc.div_const _))
  · exact continuous_const

private theorem halfCharacteristic_injective (P : RawFacePairing T) (v : OldVertex P) :
    Function.Injective (halfCharacteristic P v) := by
  intro x y h
  obtain ⟨rho,hb,_⟩ := transport P _ _ h
  have he := congrArg Subtype.val (half_parameter v.out v.out (halfParameter x) (halfParameter y) rho hb)
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  dsimp [halfParameter] at he
  linarith

/-- A genuine closed embedded interval after midpoint subdivision, even with edge inversions. -/
def halfCell (P : RawFacePairing T) (v : OldVertex P) :
    PartialEquiv (Fin 1 → ℝ) (TruncatedQuotient P) :=
  diskPartial (halfCharacteristic P v) (halfCharacteristic_continuous P v)
    (fun _ _ _ h => halfCharacteristic_injective P v h)

private theorem halfCell_coe (P : RawFacePairing T) (v : OldVertex P) (x : Disk 1) :
    halfCell P v x.val = q P (halfPoint v.out (halfParameter x)) := diskExtend_coe _ x


open private paired_twice from D5.S3.Geometry.Gluing.RawFaceLinkPathConnected

/-- The cap corner and the original zero face determine a cap-edge occurrence. -/
abbrev CapOccurrence (T : Type*) := HalfOccurrence T

private def capFrame (c : {uf : Fin 4 × Fin 4 // uf.1 ≠ uf.2}) : Equiv.Perm (Fin 4) :=
  let e := Equiv.swap 0 c.val.1
  (Equiv.swap 1 (e.symm c.val.2)).trans e

private theorem capFrame_values (c : {uf : Fin 4 × Fin 4 // uf.1 ≠ uf.2}) :
    capFrame c 0 = c.val.1 ∧ capFrame c 1 = c.val.2 := by
  rcases c with ⟨⟨u,f⟩,h⟩
  fin_cases u <;> fin_cases f <;> first | exact (h rfl).elim | norm_num [capFrame, Equiv.swap_apply_def]

private theorem disk_one_bounds (x : Disk 1) : -1 ≤ x.val 0 ∧ x.val 0 ≤ 1 := by
  have hx : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  exact abs_le.mp ((norm_le_pi_norm x.val 0).trans hx)

private def capCoords (s : ℝ) : Fin 4 → ℝ := ![3 / 4,0,(1+s)/8,(1-s)/8]

def capPoint (c : CapOccurrence T) (x : Disk 1) : TruncatedPoint T :=
  (c.1, ⟨fun i => capCoords (x.val 0) ((capFrame c.2).symm i), (by
    intro i
    have hb := disk_one_bounds x
    have hb' (k : Fin 4) : 0 ≤ capCoords (x.val 0) k ∧ capCoords (x.val 0) k ≤ 3 / 4 := by
      fin_cases k <;> dsimp [capCoords] <;> constructor <;> linarith
    exact hb' _), (by
    rw [(capFrame c.2).symm.sum_comp]
    simp [capCoords, Fin.sum_univ_four]
    ring)⟩)

private theorem capPoint_at (c : CapOccurrence T) (x : Disk 1) (i : Fin 4) :
    (capPoint c x).2.val (capFrame c.2 i) = capCoords (x.val 0) i := by
  simp [capPoint]

private theorem capPoint_fixed (c : CapOccurrence T) (x : Disk 1) :
    (capPoint c x).2.val c.2.val.1 = 3 / 4 ∧ (capPoint c x).2.val c.2.val.2 = 0 := by
  rw [← (capFrame_values c.2).1, ← (capFrame_values c.2).2]
  norm_num [capPoint_at, capCoords]

private theorem capPoint_max_unique (c : CapOccurrence T) (x : Disk 1) (i : Fin 4)
    (hi : (capPoint c x).2.val i = 3 / 4) : i = c.2.val.1 := by
  obtain ⟨k,rfl⟩ := (capFrame c.2).surjective i
  rw [capPoint_at] at hi
  have hb := disk_one_bounds x
  fin_cases k
  · exact (capFrame_values c.2).1
  all_goals norm_num [capCoords] at hi <;> linarith

private theorem disk_one_open (x : Disk 1) (hx : x.val ∈ ball 0 1) :
    -1 < x.val 0 ∧ x.val 0 < 1 := by
  have hn : ‖x.val‖ < 1 := mem_ball_zero_iff.mp hx
  exact abs_lt.mp ((norm_le_pi_norm x.val 0).trans_lt hn)

private theorem capPoint_faceInterior (c : CapOccurrence T) (x : Disk 1)
    (hx : x.val ∈ ball 0 1) : FaceInterior (capPoint c x) c.2.val.2 := by
  refine ⟨(capPoint_fixed c x).2,?_⟩
  intro i hi
  obtain ⟨k,rfl⟩ := (capFrame c.2).surjective i
  rw [capPoint_at] at hi
  have hb := disk_one_open x hx
  fin_cases k
  · norm_num [capCoords] at hi
  · exact (capFrame_values c.2).2
  all_goals norm_num [capCoords] at hi <;> linarith

private def capMate (P : RawFacePairing T) (c : CapOccurrence T) : CapOccurrence T :=
  ((P.facePair (c.1,c.2.val.2)).1,
    ⟨(sigma P (c.1,c.2.val.2) c.2.val.1, (P.facePair (c.1,c.2.val.2)).2), by
      rw [← sigma_face P (c.1,c.2.val.2)]
      exact fun he => c.2.property ((sigma P _).injective he)⟩)

private theorem capMate_twice (P : RawFacePairing T) (c : CapOccurrence T) :
    capMate P (capMate P c) = c := by
  apply Prod.ext
  · change (P.facePair (P.facePair (c.1,c.2.val.2))).1 = c.1
    rw [paired_twice]
  · apply Subtype.ext
    apply Prod.ext
    · change sigma P (P.facePair (c.1,c.2.val.2))
        (sigma P (c.1,c.2.val.2) c.2.val.1) = c.2.val.1
      rw [sigma_inverse, Equiv.symm_apply_apply]
    · change (P.facePair (P.facePair (c.1,c.2.val.2))).2 = c.2.val.2
      rw [paired_twice]

/-- Pairing orbits of the original cap edges. -/
def capSetoid (P : RawFacePairing T) : Setoid (CapOccurrence T) where
  r c d := d = c ∨ d = capMate P c
  iseqv := by
    refine ⟨fun c => Or.inl rfl,?_,?_⟩
    · intro c d h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (capMate_twice P c).symm
    · intro c d e h1 h2
      rcases h1 with rfl | rfl
      · exact h2
      · rcases h2 with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (capMate_twice P c)

abbrev CapEdge (P : RawFacePairing T) := Quotient (capSetoid P)

private theorem capPoint_equal_index (c d : CapOccurrence T) (x y : Disk 1)
    (hx : x.val ∈ ball 0 1) (hy : y.val ∈ ball 0 1)
    (he : capPoint c x = capPoint d y) : c = d := by
  refine Prod.ext (congrArg (fun a : TruncatedPoint T => a.1) he) ?_
  apply Subtype.ext
  apply Prod.ext
  · apply (capPoint_max_unique d y _)
    rw [← he]
    exact (capPoint_fixed c x).1
  · apply (capPoint_faceInterior d y hy).2
    rw [← he]
    exact (capPoint_fixed c x).2

private theorem capPoint_moved_index (P : RawFacePairing T) (c d : CapOccurrence T)
    (x y : Disk 1) (hy : y.val ∈ ball 0 1)
    (he : capPoint d y = truncatedMove P c.2.val.2 (capPoint c x)) : d = capMate P c := by
  refine Prod.ext (congrArg (fun a : TruncatedPoint T => a.1) he) ?_
  apply Subtype.ext
  apply Prod.ext
  · apply Eq.symm
    apply capPoint_max_unique d y
    rw [he]
    change (capPoint c x).2.val ((sigma P (c.1,c.2.val.2)).symm
      (sigma P (c.1,c.2.val.2) c.2.val.1)) = 3 / 4
    rw [Equiv.symm_apply_apply]
    exact (capPoint_fixed c x).1
  · apply Eq.symm
    apply (capPoint_faceInterior d y hy).2
    rw [he]
    change (capPoint c x).2.val ((sigma P (c.1,c.2.val.2)).symm
      (P.facePair (c.1,c.2.val.2)).2) = 0
    rw [← sigma_face P (c.1,c.2.val.2), Equiv.symm_apply_apply]
    exact (capPoint_fixed c x).2

def capCharacteristic (P : RawFacePairing T) (e : CapEdge P) : Disk 1 → TruncatedQuotient P :=
  fun x => q P (capPoint e.out x)

private theorem capCharacteristic_continuous (P : RawFacePairing T) (e : CapEdge P) :
    Continuous (capCharacteristic P e) := by
  have hc : Continuous (fun x : Disk 1 => x.val 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  apply (continuous_q P).comp
  apply Continuous.prodMk continuous_const
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun x : Disk 1 => capCoords (x.val 0) ((capFrame e.out.2).symm i))
  generalize (capFrame e.out.2).symm i = k
  fin_cases k
  · exact continuous_const
  · exact continuous_const
  · exact (continuous_const.add hc).div_const _
  · exact (continuous_const.sub hc).div_const _

open private hex_same_face_fiber from D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

private theorem capCharacteristic_fiber (P : RawFacePairing T) (e : CapEdge P)
    (x y : Disk 1) (hx : x.val ∈ ball 0 1)
    (he : capCharacteristic P e y = capCharacteristic P e x) : y = x := by
  have hp : capPoint e.out y = capPoint e.out x :=
    hex_same_face_fiber P _ _ e.out.2.val.2
      (capPoint_faceInterior e.out x hx) rfl (capPoint_fixed e.out y).2
      (Quotient.exact (s := Relation.EqvGen.setoid (TruncatedStep P)) he.symm)
  have hv := congrArg (fun a : TruncatedPoint T => a.2.val (capFrame e.out.2 2)) hp
  rw [capPoint_at,capPoint_at] at hv
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  dsimp [capCoords] at hv
  linarith

def capCell (P : RawFacePairing T) (e : CapEdge P) :
    PartialEquiv (Fin 1 → ℝ) (TruncatedQuotient P) :=
  diskPartial (capCharacteristic P e) (capCharacteristic_continuous P e)
    (capCharacteristic_fiber P e)

private theorem capCell_coe (P : RawFacePairing T) (e : CapEdge P) (x : Disk 1) :
    capCell P e x.val = q P (capPoint e.out x) := diskExtend_coe _ x


def vertexPoint (P : RawFacePairing T) : Vertex P → TruncatedQuotient P
  | .inl v => Quotient.lift (fun h => q P (oldPoint h)) (fun _ _ h => h) v
  | .inr v => Quotient.lift (fun h => q P (midPoint h)) (fun _ _ h => h) v

private theorem vertexPoint_injective (P : RawFacePairing T) : Function.Injective (vertexPoint P) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      apply congrArg Sum.inl
      induction v using Quotient.inductionOn with | h v =>
        induction w using Quotient.inductionOn with | h w =>
          exact Quotient.sound (s := oldSetoid P) h
    | inr w =>
      induction v using Quotient.inductionOn with | h v =>
        induction w using Quotient.inductionOn with | h w =>
          obtain ⟨rho,hb,_⟩ := transport P _ _ h
          have hp := congrArg Subtype.val (half_parameter v w ⟨3 / 4,by norm_num⟩ ⟨1 / 2,by norm_num⟩ rho hb)
          norm_num at hp
  | inr v =>
    cases w with
    | inl w =>
      induction v using Quotient.inductionOn with | h v =>
        induction w using Quotient.inductionOn with | h w =>
          obtain ⟨rho,hb,_⟩ := transport P _ _ h
          have hp := congrArg Subtype.val (half_parameter v w ⟨1 / 2,by norm_num⟩ ⟨3 / 4,by norm_num⟩ rho hb)
          norm_num at hp
    | inr w =>
      apply congrArg Sum.inr
      induction v using Quotient.inductionOn with | h v =>
        induction w using Quotient.inductionOn with | h w =>
          exact Quotient.sound (s := midSetoid P) h

def vertexCell (P : RawFacePairing T) (v : Vertex P) :
    PartialEquiv (Fin 0 → ℝ) (TruncatedQuotient P) :=
  diskPartial (fun _ : Disk 0 => vertexPoint P v) continuous_const
    (fun _ _ _ _ => Subsingleton.elim _ _)

private theorem vertexCell_coe (P : RawFacePairing T) (v : Vertex P) (x : Disk 0) :
    vertexCell P v x.val = vertexPoint P v := diskExtend_coe _ x

private theorem vertexCell_image (P : RawFacePairing T) (v : Vertex P) :
    vertexCell P v '' closedBall 0 1 = {vertexPoint P v} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact vertexCell_coe P v ⟨x,hx⟩
  · rintro rfl
    exact ⟨0,by simp,vertexCell_coe P v ⟨0,by simp⟩⟩

private theorem halfParameter_open (x : Disk 1) (hx : x.val ∈ ball 0 1) :
    1 / 2 < (halfParameter x).val ∧ (halfParameter x).val < 3 / 4 := by
  have hb := disk_one_open x hx
  dsimp [halfParameter]
  constructor <;> linarith

private theorem halfCell_open_index (P : RawFacePairing T) (v w : OldVertex P)
    (x y : Disk 1) (hx : x.val ∈ ball 0 1)
    (he : halfCell P v x.val = halfCell P w y.val) : v = w := by
  rw [halfCell_coe,halfCell_coe] at he
  have hh := (half_fiber P v.out w.out _ _ (halfParameter_open x hx).1 he).2
  have hq := Quotient.sound (s := oldSetoid P) hh
  simpa only [Quotient.out_eq] using hq

private theorem capCell_open_index (P : RawFacePairing T) (v w : CapEdge P)
    (x y : Disk 1) (hx : x.val ∈ ball 0 1) (hy : y.val ∈ ball 0 1)
    (he : capCell P v x.val = capCell P w y.val) : v = w := by
  rw [capCell_coe,capCell_coe] at he
  have hf := ((cell_geometry P).face_fibers _ _ v.out.2.val.2
    (capPoint_faceInterior v.out x hx)).2.mp he
  have ho : w.out = v.out ∨ w.out = capMate P v.out := by
    rcases hf with h | h
    · exact Or.inl (capPoint_equal_index v.out w.out x y hx hy h.symm).symm
    · exact Or.inr (capPoint_moved_index P v.out w.out x y hy h)
  have hq := Quotient.sound (s := capSetoid P) ho
  simpa only [Quotient.out_eq] using hq

private theorem half_cap_ne (P : RawFacePairing T) (h : HalfOccurrence T) (c : CapOccurrence T)
    (r : Set.Icc (1 / 2 : ℝ) (3 / 4)) (hr : r.val < 3 / 4) (x : Disk 1) :
    q P (halfPoint h r) ≠ q P (capPoint c x) := by
  intro he
  obtain ⟨rho,hb,_⟩ := transport P _ _ he
  have hv := congrArg (fun a : TruncatedTetrahedron => a.val c.2.val.1) hb
  change (capPoint c x).2.val c.2.val.1 = twoCoords h.2 r.val (rho.symm c.2.val.1) at hv
  rw [(capPoint_fixed c x).1] at hv
  dsimp [twoCoords] at hv
  split_ifs at hv <;> linarith [r.property.1]

private theorem half_vertex_ne (P : RawFacePairing T) (v : OldVertex P) (w : Vertex P)
    (x : Disk 1) (hx : x.val ∈ ball 0 1) : halfCell P v x.val ≠ vertexPoint P w := by
  rw [halfCell_coe]
  intro he
  have hr := halfParameter_open x hx
  cases w with
  | inl w =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨rho,hb,_⟩ := transport P _ _ he
      have hp := congrArg Subtype.val (half_parameter v.out w (halfParameter x) ⟨3 / 4,by norm_num⟩ rho hb)
      norm_num at hp
      linarith
  | inr w =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨rho,hb,_⟩ := transport P _ _ he
      have hp := congrArg Subtype.val (half_parameter v.out w (halfParameter x) ⟨1 / 2,by norm_num⟩ rho hb)
      norm_num at hp
      linarith

private theorem cap_vertex_ne (P : RawFacePairing T) (v : CapEdge P) (w : Vertex P)
    (x : Disk 1) (hx : x.val ∈ ball 0 1) : capCell P v x.val ≠ vertexPoint P w := by
  rw [capCell_coe]
  intro he
  have hi := capPoint_faceInterior v.out x hx
  have hn (h : HalfOccurrence T) (r : Set.Icc (1 / 2 : ℝ) (3 / 4))
      (heq : q P (capPoint v.out x) = q P (halfPoint h r)) : False := by
    obtain ⟨rho,hb,_⟩ := transport P _ _ heq
    have zeros (i : Fin 4) (hz : (halfPoint h r).2.val i = 0) :
        rho.symm i = v.out.2.val.2 := by
      apply hi.2
      have hv := congrArg (fun a : TruncatedTetrahedron => a.val i) hb
      exact hv.symm.trans hz
    have exists_two : ∃ i j : Fin 4, i ≠ j ∧ i ≠ h.2.val.1 ∧ i ≠ h.2.val.2 ∧
        j ≠ h.2.val.1 ∧ j ≠ h.2.val.2 := by
      have hd := h.2.property
      generalize h.2.val.1 = a at *
      generalize h.2.val.2 = b at *
      fin_cases a <;> fin_cases b <;> first | exact (hd rfl).elim | decide
    obtain ⟨i,j,hij,hi1,hi2,hj1,hj2⟩ := exists_two
    exact hij (rho.symm.injective ((zeros i ((half_zero_iff h r i).mpr ⟨hi1,hi2⟩)).trans
      (zeros j ((half_zero_iff h r j).mpr ⟨hj1,hj2⟩)).symm))
  cases w with
  | inl w => induction w using Quotient.inductionOn with | h w => exact hn w _ he
  | inr w => induction w using Quotient.inductionOn with | h w => exact hn w _ he

abbrev Edge (P : RawFacePairing T) := OldVertex P ⊕ CapEdge P

def edgeCell (P : RawFacePairing T) : Edge P → PartialEquiv (Fin 1 → ℝ) (TruncatedQuotient P)
  | .inl v => halfCell P v
  | .inr e => capCell P e

private theorem edge_open_index (P : RawFacePairing T) (v w : Edge P)
    (x y : Disk 1) (hx : x.val ∈ ball 0 1) (hy : y.val ∈ ball 0 1)
    (he : edgeCell P v x.val = edgeCell P w y.val) : v = w := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (halfCell_open_index P v w x y hx he)
    | inr w =>
      rw [edgeCell,edgeCell,halfCell_coe,capCell_coe] at he
      exact (half_cap_ne P v.out w.out _ (halfParameter_open x hx).2 y he).elim
  | inr v =>
    cases w with
    | inl w =>
      rw [edgeCell,edgeCell,capCell_coe,halfCell_coe] at he
      exact (half_cap_ne P w.out v.out _ (halfParameter_open y hy).2 x he.symm).elim
    | inr w => exact congrArg Sum.inr (capCell_open_index P v w x y hx hy he)

private theorem edge_vertex_ne (P : RawFacePairing T) (v : Edge P) (w : Vertex P)
    (x : Disk 1) (hx : x.val ∈ ball 0 1) : edgeCell P v x.val ≠ vertexPoint P w := by
  cases v with
  | inl v => exact half_vertex_ne P v w x hx
  | inr v => exact cap_vertex_ne P v w x hx

/-- The concrete edge locus, retaining the original ambient quotient topology. -/
def edgeSkeleton (P : RawFacePairing T) : Set (TruncatedQuotient P) :=
  (Set.range (vertexPoint P)) ∪ ⋃ e : Edge P, edgeCell P e '' closedBall 0 1

def LowerCell (P : RawFacePairing T) (n : ℕ) :=
  {v : Vertex P // n = 0} ⊕ {e : Edge P // n = 1}

def lowerMap (P : RawFacePairing T) (n : ℕ) (i : LowerCell P n) :
    PartialEquiv (Fin n → ℝ) (TruncatedQuotient P) := by
  rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
  · exact vertexCell P v
  · exact edgeCell P e

private theorem lower_source (P : RawFacePairing T) (n : ℕ) (i : LowerCell P n) :
    (lowerMap P n i).source = ball 0 1 := by
  rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
  · rfl
  · cases e <;> rfl

private theorem lower_continuousOn (P : RawFacePairing T) (n : ℕ) (i : LowerCell P n) :
    ContinuousOn (lowerMap P n i) (closedBall 0 1) := by
  rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
  · exact diskPartial_continuousOn _ _ _
  · cases e <;> exact diskPartial_continuousOn _ _ _

private theorem lower_continuousOn_symm (P : RawFacePairing T) (n : ℕ) (i : LowerCell P n) :
    ContinuousOn (lowerMap P n i).symm (lowerMap P n i).target := by
  rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
  · exact diskPartial_continuousOn_symm _ _ _
  · cases e <;> exact diskPartial_continuousOn_symm _ _ _

private theorem lower_pairwiseDisjoint (P : RawFacePairing T) :
    (univ : Set (Σ n, LowerCell P n)).PairwiseDisjoint
      (fun ni => lowerMap P ni.1 ni.2 '' ball 0 1) := by
  simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
  rintro ⟨n,i⟩ _ ⟨m,j⟩ _ hne
  apply disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have he := hxz.trans hyz.symm
  rcases i with ⟨v,hv⟩ | ⟨v,hv⟩ <;> rcases j with ⟨w,hw⟩ | ⟨w,hw⟩ <;> subst n <;> subst m
  · have hh : vertexPoint P v = vertexPoint P w := by
      rw [← vertexCell_coe P v ⟨x,ball_subset_closedBall hx⟩,
        ← vertexCell_coe P w ⟨y,ball_subset_closedBall hy⟩]
      exact he
    have hvw := vertexPoint_injective P hh
    subst w
    exact hne rfl
  · have hh : edgeCell P w y = vertexPoint P v := by
      rw [← vertexCell_coe P v ⟨x,ball_subset_closedBall hx⟩]
      exact he.symm
    exact edge_vertex_ne P w v ⟨y,ball_subset_closedBall hy⟩ hy hh
  · have hh : edgeCell P v x = vertexPoint P w := by
      rw [← vertexCell_coe P w ⟨y,ball_subset_closedBall hy⟩]
      exact he
    exact edge_vertex_ne P v w ⟨x,ball_subset_closedBall hx⟩ hx hh
  · have hvw := edge_open_index P v w ⟨x,ball_subset_closedBall hx⟩
      ⟨y,ball_subset_closedBall hy⟩ hx hy he
    subst w
    exact hne rfl

private theorem lower_eventually_empty (P : RawFacePairing T) :
    ∀ᶠ n in Filter.atTop, IsEmpty (LowerCell P n) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨2,?_⟩
  intro n hn
  refine ⟨?_⟩
  rintro (⟨v,h⟩ | ⟨e,h⟩) <;> omega

private theorem lower_finite_cell (P : RawFacePairing T) (n : ℕ) : Finite (LowerCell P n) := by
  unfold LowerCell
  infer_instance

private theorem lower_union (P : RawFacePairing T) :
    (⋃ n, ⋃ i : LowerCell P n, lowerMap P n i '' closedBall 0 1) = edgeSkeleton P := by
  ext z
  constructor
  · intro hz
    obtain ⟨n,hi⟩ := mem_iUnion.mp hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hi
    rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
    · left
      change z ∈ vertexCell P v '' closedBall 0 1 at hi
      rw [vertexCell_image] at hi
      exact ⟨v,hi.symm⟩
    · right
      exact mem_iUnion.mpr ⟨e,hi⟩
  · rintro (⟨v,rfl⟩ | hz)
    · refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨.inl ⟨v,rfl⟩,?_⟩⟩
      change vertexPoint P v ∈ vertexCell P v '' closedBall 0 1
      rw [vertexCell_image]
      rfl
    · obtain ⟨e,he⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨1,mem_iUnion.mpr ⟨.inr ⟨e,rfl⟩,he⟩⟩

private theorem disk_one_sphere (x : Disk 1) (hx : x.val ∈ sphere 0 1) :
    x.val 0 = 1 ∨ x.val 0 = -1 := by
  have hn : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have he : ‖x.val‖ = |x.val 0| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact le_rfl
    · exact norm_le_pi_norm x.val 0
  rw [he] at hn
  rcases le_total 0 (x.val 0) with h | h
  · left
    rwa [abs_of_nonneg h] at hn
  · right
    rw [abs_of_nonpos h] at hn
    linarith

private theorem capPoint_endpoint (c : CapOccurrence T) (x : Disk 1)
    (hx : x.val 0 = 1 ∨ x.val 0 = -1) : ∃ h : HalfOccurrence T, capPoint c x = oldPoint h := by
  rcases hx with hx | hx
  · let h : HalfOccurrence T := (c.1,⟨(capFrame c.2 0,capFrame c.2 2),
      fun he => (by decide : (0 : Fin 4) ≠ 2) ((capFrame c.2).injective he)⟩)
    refine ⟨h,Prod.ext rfl (Subtype.ext ?_)⟩
    funext i
    obtain ⟨k,rfl⟩ := (capFrame c.2).surjective i
    rw [capPoint_at]
    fin_cases k <;> simp [h,oldPoint,halfPoint,twoCoords,capCoords,hx,Equiv.apply_eq_iff_eq]
  · let h : HalfOccurrence T := (c.1,⟨(capFrame c.2 0,capFrame c.2 3),
      fun he => (by decide : (0 : Fin 4) ≠ 3) ((capFrame c.2).injective he)⟩)
    refine ⟨h,Prod.ext rfl (Subtype.ext ?_)⟩
    funext i
    obtain ⟨k,rfl⟩ := (capFrame c.2).surjective i
    rw [capPoint_at]
    fin_cases k <;> simp [h,oldPoint,halfPoint,twoCoords,capCoords,hx,Equiv.apply_eq_iff_eq]

private theorem edge_sphere (P : RawFacePairing T) (e : Edge P) :
    MapsTo (edgeCell P e) (sphere 0 1) (Set.range (vertexPoint P)) := by
  intro x hx
  let xd : Disk 1 := ⟨x,sphere_subset_closedBall hx⟩
  have hend := disk_one_sphere xd hx
  cases e with
  | inl v =>
    rcases hend with hp | hm
    · refine ⟨.inl (Quotient.mk (oldSetoid P) v.out),?_⟩
      change q P (oldPoint v.out) = halfCell P v xd.val
      rw [halfCell_coe]
      apply congrArg (q P)
      apply congrArg (halfPoint v.out)
      apply Subtype.ext
      dsimp [halfParameter]
      change xd.val 0 = 1 at hp
      linarith
    · refine ⟨.inr (Quotient.mk (midSetoid P) v.out),?_⟩
      change q P (midPoint v.out) = halfCell P v xd.val
      rw [halfCell_coe]
      apply congrArg (q P)
      apply congrArg (halfPoint v.out)
      apply Subtype.ext
      dsimp [halfParameter]
      change xd.val 0 = -1 at hm
      linarith
  | inr e =>
    obtain ⟨h,hh⟩ := capPoint_endpoint e.out xd hend
    refine ⟨.inl (Quotient.mk (oldSetoid P) h),?_⟩
    change q P (oldPoint h) = capCell P e xd.val
    rw [capCell_coe,hh]

private theorem lower_mapsTo (P : RawFacePairing T) (n : ℕ) (i : LowerCell P n) :
    MapsTo (lowerMap P n i) (sphere 0 1)
      (⋃ (m < n) (j : LowerCell P m), lowerMap P m j '' closedBall 0 1) := by
  rcases i with ⟨v,h⟩ | ⟨e,h⟩ <;> subst n
  · intro x hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    simpa [hx0] using hx
  · intro x hx
    obtain ⟨v,hv⟩ := edge_sphere P e hx
    refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by omega,mem_iUnion.mpr ⟨.inl ⟨v,rfl⟩,?_⟩⟩⟩
    change edgeCell P e x ∈ vertexCell P v '' closedBall 0 1
    rw [vertexCell_image]
    exact hv.symm

/-- The finite CW construction uses the original quotient and only dimensions zero and one. -/
def lowerCW (P : RawFacePairing T) : CWComplex (edgeSkeleton P) :=
  CWComplex.mkFinite (edgeSkeleton P) (LowerCell P) (lowerMap P)
    (lower_eventually_empty P) (lower_finite_cell P) (lower_source P)
    (lower_continuousOn P) (lower_continuousOn_symm P) (lower_pairwiseDisjoint P)
    (lower_mapsTo P) (lower_union P)

private theorem lowerCW_finite (P : RawFacePairing T) :
    letI := lowerCW P
    CWComplex.Finite (edgeSkeleton P) :=
  CWComplex.finite_mkFinite (edgeSkeleton P) (LowerCell P) (lowerMap P)
    (lower_eventually_empty P) (lower_finite_cell P) (lower_source P)
    (lower_continuousOn P) (lower_continuousOn_symm P) (lower_pairwiseDisjoint P)
    (lower_mapsTo P) (lower_union P)

end D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
