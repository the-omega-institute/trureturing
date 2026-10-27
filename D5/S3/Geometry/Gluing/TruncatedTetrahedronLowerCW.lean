/- GID: D5/S3/Geometry/Gluing/TruncatedTetrahedronLowerCW
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/TruncatedTetrahedronLowerCW
   mirror-E: none(waiver:lower-cw-topological-construction)
   anchors: [mathlib/module/Mathlib.Topology.CWComplex.Classical.Finite]
   utility: none
   digest: Midpoint subdivision gives lower cells on the original truncated quotient. -/

import D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

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
  rcases ij with ⟨⟨i,j⟩,h⟩
  fin_cases i <;> fin_cases j <;> simp_all [twoCoords, Fin.sum_univ_four] <;> ring

/-- The closed retained halfedge in the original four coordinates. -/
def halfPoint (h : HalfOccurrence T) (r : Set.Icc (1/2 : ℝ) (3/4)) : TruncatedPoint T :=
  (h.1, ⟨twoCoords h.2 r.val, (by
    intro i
    dsimp [twoCoords]
    split_ifs <;> constructor <;> linarith [r.property.1, r.property.2]), twoCoords_sum h.2 r.val⟩)

def oldPoint (h : HalfOccurrence T) : TruncatedPoint T := halfPoint h ⟨3/4, by norm_num⟩
def midPoint (h : HalfOccurrence T) : TruncatedPoint T := halfPoint h ⟨1/2, by norm_num⟩

private def reindex (rho : Equiv.Perm (Fin 4)) (a : TruncatedTetrahedron) : TruncatedTetrahedron :=
  ⟨fun i => a.val (rho.symm i), (fun i => a.property.1 _),
    (rho.symm.sum_comp a.val).trans a.property.2⟩

private theorem transport (P : RawFacePairing T) (a b : TruncatedPoint T)
    (h : q P a = q P b) :
    ∃ rho : Equiv.Perm (Fin 4), b.2 = reindex rho a.2 ∧
      ∀ z : TruncatedTetrahedron, (∀ i, a.2.val i = 0 → z.val i = 0) →
        q P (a.1,z) = q P (b.1,reindex rho z) := by
  let S : Set (Fin 4 → ℝ) := {z | (∀ i, 0 ≤ z i ∧ z i ≤ 3/4) ∧ (∑ i, z i) = 1}
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

private theorem half_zero_iff (h : HalfOccurrence T) (r : Set.Icc (1/2 : ℝ) (3/4))
    (i : Fin 4) : (halfPoint h r).2.val i = 0 ↔ i ≠ h.2.val.1 ∧ i ≠ h.2.val.2 := by
  dsimp [halfPoint, twoCoords]
  split_ifs <;> simp_all <;> linarith [r.property.1,r.property.2]

private def movedHalf (h : HalfOccurrence T) (u : T) (rho : Equiv.Perm (Fin 4)) : HalfOccurrence T :=
  (u, ⟨(rho h.2.val.1,rho h.2.val.2), fun he => h.2.property (rho.injective he)⟩)

private theorem half_reindex (h : HalfOccurrence T) (u : T) (rho : Equiv.Perm (Fin 4))
    (r : Set.Icc (1/2 : ℝ) (3/4)) :
    (halfPoint (movedHalf h u rho) r).2 = reindex rho (halfPoint h r).2 := by
  apply Subtype.ext
  funext i
  simp only [halfPoint, movedHalf, reindex, twoCoords]
  have h1 : rho.symm i = h.2.val.1 ↔ i = rho h.2.val.1 := rho.symm_apply_eq
  have h2 : rho.symm i = h.2.val.2 ↔ i = rho h.2.val.2 := rho.symm_apply_eq
  rw [h1,h2]

private theorem half_parameter (h k : HalfOccurrence T)
    (r s : Set.Icc (1/2 : ℝ) (3/4)) (rho : Equiv.Perm (Fin 4))
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
    (r : Set.Icc (1/2 : ℝ) (3/4)) (hr : 1/2 < r.val)
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
    (r : Set.Icc (1/2 : ℝ) (3/4)) : q P (halfPoint h r) = q P (halfPoint k r) := by
  obtain ⟨rho,hb,hg⟩ := transport P _ _ he
  let l := movedHalf h k.1 rho
  have hl : halfPoint k ⟨3/4, by norm_num⟩ = halfPoint l ⟨3/4, by norm_num⟩ :=
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
    (r s : Set.Icc (1/2 : ℝ) (3/4)) (hr : 1/2 < r.val)
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
  rw [← half_reindex h k.1 rho ⟨3/4, by norm_num⟩] at heq
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

private def halfParameter (x : Disk 1) : Set.Icc (1/2 : ℝ) (3/4) :=
  ⟨5/8 + x.val 0 / 8, by
    have hx : ‖x.val‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    have h0 : ‖x.val 0‖ ≤ 1 := (norm_le_pi_norm x.val 0).trans hx
    have hb := abs_le.mp (show |x.val 0| ≤ 1 from h0)
    constructor <;> linarith⟩

def halfCharacteristic (P : RawFacePairing T) (v : OldVertex P) : Disk 1 → TruncatedQuotient P :=
  fun x => q P (halfPoint v.out (halfParameter x))

private theorem halfCharacteristic_continuous (P : RawFacePairing T) (v : OldVertex P) :
    Continuous (halfCharacteristic P v) := by
  apply (continuous_q P).comp
  apply Continuous.prodMk continuous_const
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  dsimp [halfPoint, twoCoords, halfParameter]
  split_ifs <;> fun_prop

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

end D5.S3.Geometry.Gluing.TruncatedTetrahedronLowerCW
