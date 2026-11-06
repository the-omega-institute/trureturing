/- GID: D5/S3/Geometry/OriginalLabelTwoSum/ParentCells
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/ParentCells
   mirror-E: none(waiver:original-label-two-sum-parent-cells)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice]
   utility: none
   digest: The original compiler computes its parent core and proves critical nonemptiness, all boundaries, absence and antichains. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Certificates
import D5.S3.Geometry.OriginalLabelTwoSum.Rectangles

/-! UNCOMPILED. This module constructs the literal output families and proves
all critical-face conditions. Compiler consumes these actual families when
assembling the main/core Sequences. No output certificate is an input. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X Y Z : Finset V} {e : V} {K E : Family V}

/-- Exact Cout from the ORIGINAL proof, on the full original parent ground. -/
def parentCore (X Y Z : Finset V) (e : V) (E C : Family V)
    (critical : Finset (Finset V)) (B0 B1 : Family V) : Family V where
  carrier := {s | s ∈ phi X Y Z (restrict X C) (rawLink X e C) E ∨
    ∃ q ∈ critical, (e ∉ q ∧ s ∈ rawJoin (delta q) B0) ∨
      (e ∈ q ∧ s ∈ rawJoin (delta (q.erase e)) B1)}
  lower' := by
    rintro s t h (hb | ⟨q,hq,hq0 | hq1⟩)
    · exact Or.inl ((phi X Y Z (restrict X C) (rawLink X e C) E).lower h hb)
    · exact Or.inr ⟨q,hq,Or.inl ⟨hq0.1,(rawJoin (delta q) B0).lower h hq0.2⟩⟩
    · exact Or.inr ⟨q,hq,Or.inr ⟨hq1.1,(rawJoin (delta (q.erase e)) B1).lower h hq1.2⟩⟩

/-- Ordered-index provenance is retained by the compiler schedules; this finite
set is the actual output critical family, after proving no unwanted inclusions. -/
def parentCritical (e : V) (C A B : Finset (Finset V)) : Finset (Finset V) :=
  C.biUnion (fun q => if e ∈ q then B.image (fun t => q.erase e ∪ t)
    else A.image (fun t => q ∪ t))

/-- Literal critical provenance, consumed by the filling endpoint assembly. -/
theorem mem_parentCritical {C A B : Finset (Finset V)} {s : Finset V} :
    s ∈ parentCritical e C A B ↔
      (∃ q ∈ C, e ∉ q ∧ ∃ t ∈ A, s = q ∪ t) ∨
      (∃ q ∈ C, e ∈ q ∧ ∃ t ∈ B, s = q.erase e ∪ t) := by
  classical
  simp only [parentCritical,Finset.mem_biUnion]
  constructor
  · rintro ⟨q,hq,h⟩
    by_cases he : e ∈ q
    · rw [if_pos he] at h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨q,hq,he,t,ht,rfl⟩
    · rw [if_neg he] at h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨q,hq,he,t,ht,rfl⟩
  · rintro (⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩)
    · exact ⟨q,hq,by rw [if_neg he]; exact Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
    · exact ⟨q,hq,by rw [if_pos he]; exact Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩

private theorem left_support (heX : e ∉ X) {q : Finset V}
    (hq : q ⊆ insert e X) (he : e ∉ q) : q ⊆ X := by
  intro v hv
  exact (Finset.mem_insert.mp (hq hv)).resolve_left (fun h => he (h ▸ hv))

private theorem erase_support {q : Finset V} (hq : q ⊆ insert e X) : q.erase e ⊆ X := by
  intro v hv
  exact (Finset.mem_insert.mp (hq (Finset.mem_of_mem_erase hv))).resolve_left
    (Finset.mem_erase.mp hv).1

private theorem split_parts (hd : Disjoint X Y) {a b : Finset V}
    (ha : a ⊆ X) (hb : b ⊆ Y) :
    (a ∪ b) ∩ X = a ∧ (a ∪ b) ∩ Y = b := by
  have h := join_split hd (K := delta a) (L := delta b)
    (fun _ h => h.trans ha) (fun _ h => h.trans hb) (a ∪ b)
  have hj : a ∪ b ∈ rawJoin (delta a) (delta b) := ⟨a,(by change a ⊆ a; exact le_rfl),b,(by change b ⊆ b; exact le_rfl),rfl⟩
  have hh := h.mp hj
  constructor
  · exact Finset.Subset.antisymm hh.2.1
      (fun v hv => Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hv,ha hv⟩)
  · exact Finset.Subset.antisymm hh.2.2
      (fun v hv => Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hv,hb hv⟩)

private theorem inclusion_parts (hd : Disjoint X Y) {a b c d : Finset V}
    (ha : a ⊆ X) (hb : b ⊆ Y) (hc : c ⊆ X) (hd' : d ⊆ Y)
    (h : a ∪ b ⊆ c ∪ d) : a ⊆ c ∧ b ⊆ d := by
  constructor
  · intro v hv
    rcases Finset.mem_union.mp (h (Finset.mem_union_left _ hv)) with hv' | hv'
    · exact hv'
    · exact False.elim (Finset.disjoint_left.mp hd (ha hv) (hd' hv'))
  · intro v hv
    rcases Finset.mem_union.mp (h (Finset.mem_union_right _ hv)) with hv' | hv'
    · exact False.elim (Finset.disjoint_left.mp hd (hc hv') (hb hv))
    · exact hv'

private theorem proper_factors {s a b : Finset V} (hs : s ⊂ a ∪ b) :
    s = (s ∩ a) ∪ (s ∩ b) ∧ ((s ∩ a) ⊂ a ∨ (s ∩ b) ⊂ b) := by
  have he : s = (s ∩ a) ∪ (s ∩ b) := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter]
    exact ⟨fun hv => (Finset.mem_union.mp (hs.1 hv)).elim
      (fun ha => Or.inl ⟨hv,ha⟩) (fun hb => Or.inr ⟨hv,hb⟩),by tauto⟩
  refine ⟨he,?_⟩
  by_cases ha : s ∩ a = a
  · right
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,?_⟩
    intro hb
    rw [ha,hb] at he
    exact hs.ne he
  · exact Or.inl (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right,ha⟩)

/-- Complete critical-face proof for the COMPUTED Cout. Compiler constructs the
main and separate core lists; neither collapse is a hypothesis here. -/
def parentCellData (c : Certificate (insert e X) K)
    (f0 : Filling Z (E ⊓ delta Z)) (f1 : Filling Y (E ⊔ delta Z))
    (heX : e ∉ X) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    (hE : Supported Y E) :
    CriticalData (parentCore X Y Z e E c.core c.critical f0.collar f1.collar)
      (parentCritical e c.critical f0.critical f1.critical) := by
  have avoidX {q} (hq : q ∈ c.critical) (he : e ∉ q) : q ⊆ X :=
    left_support heX (c.critical_supported q hq) he
  have containX {q} (hq : q ∈ c.critical) : q.erase e ⊆ X :=
    erase_support (c.critical_supported q hq)
  have theta_not_Z {t} (ht : t ∈ f1.critical) : ¬ t ⊆ Z := by
    intro hz
    exact f1.cells.absent t ht (f1.contains (Or.inr hz))
  have coreD : Supported X (restrict X c.core) := fun _ hs => hs.2
  have coreL : Supported X (rawLink X e c.core) := fun _ hs => hs.1
  refine ⟨?_,?_,?_,?_⟩
  · intro s hs
    rcases mem_parentCritical.mp hs with ⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩
    · exact (c.cells.nonempty q hq).mono Finset.subset_union_left
    · exact (f1.cells.nonempty t ht).mono Finset.subset_union_right
  · intro s hs hcore
    rcases mem_parentCritical.mp hs with ⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩
    · have hqX := avoidX hq he
      have htZ := f0.critical_supported t ht
      have htY := htZ.trans hZ
      have parts := split_parts hXY hqX htY
      rcases hcore with hb | ⟨q',hq',h0 | h1⟩
      · have hh := (phi_split X Y Z (restrict X c.core) (rawLink X e c.core) E
          hXY hZ coreD coreL hE _).mp hb
        rw [parts.1,parts.2] at hh
        rcases hh.2 with hh | hh | hh
        · exact c.cells.absent q hq hh.1.1
        · exact c.cells.absent q hq (c.core.lower (Finset.subset_insert e q) hh.2)
        · exact f0.cells.absent t ht (f0.contains ⟨hh,htZ⟩)
      · have hj := (join_split hXY (K := delta q') (L := f0.collar) (fun s hs => hs.trans (avoidX hq' h0.1))
          (fun s hs => (f0.supported s hs).trans hZ) _).mp h0.2
        rw [parts.1,parts.2] at hj
        have hqq := c.cells.antichain q hq q' hq' hj.2.1
        exact f0.cells.absent t ht hj.2.2
      · have hj := (join_split hXY (K := delta (q'.erase e)) (L := f1.collar) (fun s hs => hs.trans (containX hq'))
          f1.supported _).mp h1.2
        rw [parts.1,parts.2] at hj
        have hqq := c.cells.antichain q hq q' hq'
          (hj.2.1.trans (Finset.erase_subset _ _))
        exact he (hqq.symm ▸ h1.1)
    · have hqX := containX hq
      have htY := f1.critical_supported t ht
      have parts := split_parts hXY hqX htY
      rcases hcore with hb | ⟨q',hq',h0 | h1⟩
      · have hh := (phi_split X Y Z (restrict X c.core) (rawLink X e c.core) E
          hXY hZ coreD coreL hE _).mp hb
        rw [parts.1,parts.2] at hh
        rcases hh.2 with hh | hh | hh
        · exact theta_not_Z ht hh.2
        · exact c.cells.absent q hq ((Finset.insert_erase he) ▸ hh.2)
        · exact f1.cells.absent t ht (f1.contains (Or.inl hh))
      · have hj := (join_split hXY (K := delta q') (L := f0.collar) (fun s hs => hs.trans (avoidX hq' h0.1))
          (fun s hs => (f0.supported s hs).trans hZ) _).mp h0.2
        rw [parts.1,parts.2] at hj
        exact theta_not_Z ht (f0.supported t hj.2.2)
      · have hj := (join_split hXY (K := delta (q'.erase e)) (L := f1.collar) (fun s hs => hs.trans (containX hq'))
          f1.supported _).mp h1.2
        rw [parts.1,parts.2] at hj
        exact f1.cells.absent t ht hj.2.2
  · intro s hs w hws
    rcases mem_parentCritical.mp hs with ⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩
    · obtain ⟨hw,hfactor⟩ := proper_factors hws
      rcases hfactor with hx | hy
      · left
        exact Or.inl (Or.inl ⟨w ∩ q,
          ⟨c.cells.boundary q hq _ hx,Finset.inter_subset_right.trans (avoidX hq he)⟩,
          w ∩ t,Finset.inter_subset_right.trans (f0.critical_supported t ht),hw⟩)
      · right
        exact ⟨q,hq,Or.inl ⟨he,w ∩ q,Finset.inter_subset_right,w ∩ t,
          f0.cells.boundary t ht _ hy,hw⟩⟩
    · obtain ⟨hw,hfactor⟩ := proper_factors hws
      rcases hfactor with hx | hy
      · have hproper : insert e (w ∩ q.erase e) ⊂ q := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset_iff.mpr
            ⟨he,Finset.inter_subset_right.trans (Finset.erase_subset _ _)⟩,?_⟩
          intro heq
          have hh := congrArg (fun z : Finset V => z.erase e) heq
          have hnot : e ∉ w ∩ q.erase e := by simp
          rw [Finset.erase_insert hnot] at hh
          exact hx.ne hh
        left
        exact Or.inl (Or.inr ⟨w ∩ q.erase e,
          ⟨Finset.inter_subset_right.trans (containX hq),
            c.cells.boundary q hq _ hproper⟩,
          w ∩ t,Finset.inter_subset_right.trans (f1.critical_supported t ht),hw⟩)
      · right
        exact ⟨q,hq,Or.inr ⟨he,w ∩ q.erase e,Finset.inter_subset_right,w ∩ t,
          f1.cells.boundary t ht _ hy,hw⟩⟩
  · intro s hs w hw hsw
    rcases mem_parentCritical.mp hs with ⟨q,hq,he,t,ht,rfl⟩ | ⟨q,hq,he,t,ht,rfl⟩ <;>
      rcases mem_parentCritical.mp hw with ⟨q',hq',he',t',ht',rfl⟩ | ⟨q',hq',he',t',ht',rfl⟩
    · have hparts := inclusion_parts hXY (avoidX hq he)
        ((f0.critical_supported t ht).trans hZ) (avoidX hq' he')
        ((f0.critical_supported t' ht').trans hZ) hsw
      rw [c.cells.antichain q hq q' hq' hparts.1,
        f0.cells.antichain t ht t' ht' hparts.2]
    · have hparts := inclusion_parts hXY (avoidX hq he)
        ((f0.critical_supported t ht).trans hZ) (containX hq')
        (f1.critical_supported t' ht') hsw
      have hqq := c.cells.antichain q hq q' hq' (hparts.1.trans (Finset.erase_subset _ _))
      exact False.elim (he (hqq.symm ▸ he'))
    · have hparts := inclusion_parts hXY (containX hq) (f1.critical_supported t ht)
        (avoidX hq' he') ((f0.critical_supported t' ht').trans hZ) hsw
      exact False.elim (theta_not_Z ht (hparts.2.trans (f0.critical_supported t' ht')))
    · have hparts := inclusion_parts hXY (containX hq) (f1.critical_supported t ht)
        (containX hq') (f1.critical_supported t' ht') hsw
      have hqq : q = q' := c.cells.antichain q hq q' hq' (by
        rw [← Finset.insert_erase he,← Finset.insert_erase he']
        exact Finset.insert_subset_insert e hparts.1)
      rw [hqq,f1.cells.antichain t ht t' ht' hparts.2]

end D5.S3.Geometry.OriginalLabelTwoSum
