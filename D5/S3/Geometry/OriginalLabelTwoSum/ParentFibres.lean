/- GID: D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/ParentFibres
   mirror-E: none(waiver:original-label-two-sum-parent-fibres)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice]
   utility: none
   digest: Actual critical-fibre boundaries and coface exclusions permit independent native filling and collar batches. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Batch
import D5.S3.Geometry.OriginalLabelTwoSum.ParentCells
import D5.S3.Geometry.OriginalLabelTwoSum.Replay

/-! UNCOMPILED. Every fibre-intersection premise of batchFibre is proved here
from the left critical antichain and all proper boundaries. In particular the
second-to-first interference is absorbed by delta Z, rather than ignored. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- These are literal X-parts; the removed label e is not an output coordinate. -/
def criticalPart (e : V) (q : Finset V) : Finset V :=
  if e ∈ q then q.erase e else q

def localWindow (e : V) (Y Z q : Finset V) : Finset V := if e ∈ q then Y else Z

def localBase (e : V) (Z q : Finset V) (E : Family V) : Family V :=
  if e ∈ q then E ⊔ delta Z else E ⊓ delta Z

private theorem part_supported {e : V} {X q : Finset V}
    (h : q ⊆ insert e X) : criticalPart e q ⊆ X := by
  intro v hv
  by_cases he : e ∈ q
  · rw [criticalPart,if_pos he] at hv
    exact (Finset.mem_insert.mp (h (Finset.mem_of_mem_erase hv))).resolve_left
      (Finset.mem_erase.mp hv).1
  · rw [criticalPart,if_neg he] at hv
    exact (Finset.mem_insert.mp (h hv)).resolve_left (fun heq => he (heq ▸ hv))

private theorem part_subset (e : V) (q : Finset V) : criticalPart e q ⊆ q := by
  by_cases he : e ∈ q <;> simp [criticalPart,he,Finset.erase_subset]

private theorem restore {e : V} {q : Finset V} (he : e ∈ q) :
    insert e (criticalPart e q) = q := by simp [criticalPart,he]

private theorem window_supported {e : V} {Y Z q : Finset V} (hZ : Z ⊆ Y) :
    localWindow e Y Z q ⊆ Y := by
  by_cases he : e ∈ q <;> simp [localWindow,he,hZ]

/-- Boundary and fibre-intersection facts for the COMPUTED Cbase. -/
theorem parent_fibre_base {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K) (heX : e ∉ X)
    (hXY : Disjoint X Y) (hZ : Z ⊆ Y) (hE : Supported Y E)
    {q : Finset V} (hq : q ∈ c.critical) :
    (criticalPart e q ⊆ X) ∧
    Disjoint (criticalPart e q) (localWindow e Y Z q) ∧
    (∀ x ⊂ criticalPart e q, ∀ t ⊆ localWindow e Y Z q,
      x ∪ t ∈ parentOf X Y Z e E c.core) ∧
    (∀ t ⊆ localWindow e Y Z q,
      criticalPart e q ∪ t ∈ parentOf X Y Z e E c.core →
      t ∈ localBase e Z q E) := by
  have ha := part_supported (c.critical_supported q hq)
  have hw := window_supported (e := e) (q := q) hZ
  have hd : Disjoint (criticalPart e q) (localWindow e Y Z q) :=
    hXY.mono ha hw
  refine ⟨ha,hd,?_,?_⟩
  · intro x hx t ht
    by_cases he : e ∈ q
    · have hproper : insert e x ⊂ q := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset_iff.mpr
          ⟨he,hx.1.trans (part_subset e q)⟩,?_⟩
        intro heq
        have hex : e ∉ x := fun h => heX (ha (hx.1 h))
        have hh := congrArg (fun s : Finset V => s.erase e) heq
        rw [Finset.erase_insert hex] at hh
        exact (hx.ne) (by simpa [criticalPart,he] using hh)
      exact Or.inl (Or.inr ⟨x,⟨hx.1.trans ha,c.cells.boundary q hq _ hproper⟩,
        t,by simpa [localWindow,he] using ht,rfl⟩)
    · have hxq : x ⊂ q := by simpa [criticalPart,he] using hx
      exact Or.inl (Or.inl ⟨x,⟨c.cells.boundary q hq _ hxq,hx.1.trans ha⟩,
        t,by simpa [localWindow,he] using ht,rfl⟩)
  · intro t ht hbase
    have htY := ht.trans hw
    have parts :
        (criticalPart e q ∪ t) ∩ X = criticalPart e q ∧
        (criticalPart e q ∪ t) ∩ Y = t := by
      constructor <;> ext v
      · simp only [Finset.mem_inter,Finset.mem_union]
        exact ⟨fun h => h.1.elim id
          (fun hv => False.elim (Finset.disjoint_left.mp hXY h.2 (htY hv))),
          fun hv => ⟨Or.inl hv,ha hv⟩⟩
      · simp only [Finset.mem_inter,Finset.mem_union]
        exact ⟨fun h => h.1.elim
          (fun hv => False.elim (Finset.disjoint_left.mp hXY (ha hv) h.2)) id,
          fun hv => ⟨Or.inr hv,htY hv⟩⟩
    have hh := (phi_split X Y Z (restrict X c.core) (rawLink X e c.core) E
      hXY hZ (fun _ h => h.2) (fun _ h => h.1) hE _).mp hbase
    rw [parts.1,parts.2] at hh
    by_cases he : e ∈ q
    · simp only [localBase,if_pos he]
      rcases hh.2 with h | h | h
      · exact Or.inr h.2
      · exact False.elim (c.cells.absent q hq ((restore he) ▸ h.2))
      · exact Or.inl h
    · simp only [localBase,if_neg he]
      have haeq : criticalPart e q = q := by simp [criticalPart,he]
      refine ⟨?_,by simpa [localWindow,he] using ht⟩
      rcases hh.2 with h | h | h
      · exact False.elim (c.cells.absent q hq (haeq ▸ h.1.1))
      · have hqcore := c.core.lower (Finset.subset_insert e (criticalPart e q)) h.2
        exact False.elim (c.cells.absent q hq (haeq ▸ hqcore))
      · exact h

/-- Exact cross-fibre exclusion. The one direction that can intersect is the
second-kind fibre into a first-kind block, and its right part then lies in Z. -/
theorem parent_fibre_cross {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K) (hXY : Disjoint X Y) (hZ : Z ⊆ Y)
    {q q' : Finset V} (hq : q ∈ c.critical) (hq' : q' ∈ c.critical)
    (hne : q ≠ q') {M : Family V} (hM : Supported (localWindow e Y Z q') M)
    {t : Finset V} (ht : t ⊆ localWindow e Y Z q)
    (hm : criticalPart e q ∪ t ∈ rawJoin (delta (criticalPart e q')) M) :
    t ∈ localBase e Z q E := by
  obtain ⟨x,hx,y,hy,heq⟩ := hm
  have ha := part_supported (c.critical_supported q hq)
  have ha' := part_supported (c.critical_supported q' hq')
  have htY := ht.trans (window_supported (e := e) hZ)
  have hyY := (hM y hy).trans (window_supported (e := e) hZ)
  have hin : criticalPart e q ⊆ criticalPart e q' := by
    intro v hv
    have hh : v ∈ x ∪ y := by rw [← heq]; exact Finset.mem_union_left _ hv
    exact (Finset.mem_union.mp hh).elim (fun hvx => hx hvx)
      (fun hv' => False.elim (Finset.disjoint_left.mp hXY (ha hv) (hyY hv')))
  have hty : t ⊆ y := by
    intro v hv
    have hh : v ∈ x ∪ y := by rw [← heq]; exact Finset.mem_union_right _ hv
    exact (Finset.mem_union.mp hh).elim
      (fun hv' => False.elim (Finset.disjoint_left.mp hXY (ha' (hx hv')) (htY hv))) id
  by_cases he : e ∈ q
  · by_cases he' : e ∈ q'
    · have hqq : q ⊆ q' := by
        rw [← restore he,← restore he']
        exact Finset.insert_subset_insert e hin
      exact False.elim (hne (c.cells.antichain q hq q' hq' hqq))
    · have hz : t ⊆ Z := by
        have hh := hty.trans (hM y hy)
        simpa [localWindow,he'] using hh
      exact (by simpa [localBase,he] using (Or.inr hz : t ∈ E ∨ t ∈ delta Z))
  · have hqq : q ⊆ q' := by
      have haeq : criticalPart e q = q := by simp [criticalPart,he]
      rw [haeq] at hin
      exact hin.trans (part_subset e q')
    exact False.elim (hne (c.cells.antichain q hq q' hq' hqq))

/-- The initial fibre decomposition is PROVED from proper-boundary membership,
not assumed as an endpoint or desired parent row equation. -/
theorem parent_initial_fibres {X Y Z : Finset V} {e : V} {K E : Family V}
    (c : Certificate (insert e X) K) (heX : e ∉ X)
    (is : List (Finset V)) (his : ∀ q, q ∈ is ↔ q ∈ c.critical) :
    parentOf X Y Z e E (endpoint c.core c.critical) =
      parentOf X Y Z e E c.core ⊔ fibreLayers (criticalPart e)
        (fun q => delta (localWindow e Y Z q)) is := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ((⟨x,⟨hx,hxX⟩,t,ht,rfl⟩ | ⟨x,⟨hxX,hx⟩,t,ht,rfl⟩) | hE)
    · rcases hx with hx | ⟨q,hq,hxq⟩
      · exact Or.inl (Or.inl (Or.inl ⟨x,⟨hx,hxX⟩,t,ht,rfl⟩))
      · by_cases he : e ∈ q
        · have hxpart : x ⊆ q.erase e := by
            intro v hv
            exact Finset.mem_erase.mpr ⟨fun heq => heX (heq ▸ hxX hv),hxq hv⟩
          have hproper : x ⊂ q := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hxq,?_⟩
            intro h
            exact heX (hxX (h.symm ▸ he))
          exact Or.inl (Or.inl (Or.inl
            ⟨x,⟨c.cells.boundary q hq x hproper,hxX⟩,t,ht,rfl⟩))
        · exact Or.inr ((mem_fibreLayers _ _ _ _).mpr
            ⟨q,(his q).mpr hq,x,by simpa [criticalPart,he] using hxq,
              t,by simpa [localWindow,he] using ht,rfl⟩)
    · rcases hx with hx | ⟨q,hq,hxq⟩
      · exact Or.inl (Or.inl (Or.inr ⟨x,⟨hxX,hx⟩,t,ht,rfl⟩))
      · have he : e ∈ q := hxq (Finset.mem_insert_self _ _)
        have hxpart : x ⊆ q.erase e := by
          intro v hv
          exact Finset.mem_erase.mpr ⟨fun heq => heX (heq ▸ hxX hv),
            hxq (Finset.mem_insert_of_mem hv)⟩
        exact Or.inr ((mem_fibreLayers _ _ _ _).mpr
          ⟨q,(his q).mpr hq,x,by simpa [criticalPart,he] using hxpart,
            t,by simpa [localWindow,he] using ht,rfl⟩)
    · exact Or.inl (Or.inr hE)
  · rintro (hb | hf)
    · rcases hb with (⟨x,⟨hx,hxX⟩,t,ht,rfl⟩ | ⟨x,⟨hxX,hx⟩,t,ht,rfl⟩) | hE
      · exact Or.inl (Or.inl ⟨x,⟨Or.inl hx,hxX⟩,t,ht,rfl⟩)
      · exact Or.inl (Or.inr ⟨x,⟨hxX,Or.inl hx⟩,t,ht,rfl⟩)
      · exact Or.inr hE
    · obtain ⟨q,hq,x,hx,t,ht,rfl⟩ := (mem_fibreLayers _ _ _ _).mp hf
      have hqc := (his q).mp hq
      have hxX := hx.trans (part_supported (c.critical_supported q hqc))
      by_cases he : e ∈ q
      · exact Or.inl (Or.inr ⟨x,⟨hxX,Or.inr ⟨q,hqc,by
          rw [← restore he]
          exact Finset.insert_subset_insert e hx⟩⟩,
          t,by simpa [localWindow,he] using ht,rfl⟩)
      · exact Or.inl (Or.inl ⟨x,⟨Or.inr ⟨q,hqc,by
          simpa [criticalPart,he] using hx⟩,hxX⟩,
          t,by simpa [localWindow,he] using ht,rfl⟩)

end D5.S3.Geometry.OriginalLabelTwoSum
