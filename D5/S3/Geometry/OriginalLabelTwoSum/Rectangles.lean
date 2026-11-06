/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Rectangles
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Rectangles
   mirror-E: none(waiver:original-label-two-sum-rectangles)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Deletion and link rectangles derive whole-current coface proofs before emitting descending native pairs. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Native

/-! UNCOMPILED. Endpoints here are explicit raw cuts. RectangleEndpoints proves
their equality to the changed Phi states; Replay consumes those proved
identities. No desired endpoint is a premise of these constructors. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem split_union {X Y a b : Finset V} (hd : Disjoint X Y)
    (ha : a ⊆ X) (hb : b ⊆ Y) :
    (a ∪ b) ∩ X = a ∧ (a ∪ b) ∩ Y = b := by
  constructor
  · ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    exact ⟨fun ⟨h,hx⟩ => h.elim id (fun hy =>
      False.elim (Finset.disjoint_left.mp hd hx (hb hy))),fun h => ⟨Or.inl h,ha h⟩⟩
  · ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    exact ⟨fun ⟨h,hy⟩ => h.elim (fun hx =>
      False.elim (Finset.disjoint_left.mp hd (ha hx) hy)) id,fun h => ⟨Or.inr h,hb h⟩⟩

private theorem split_recover {X Y s : Finset V} (hs : s ⊆ X ∪ Y) :
    s = (s ∩ X) ∪ (s ∩ Y) := by
  ext v
  simp only [Finset.mem_union,Finset.mem_inter]
  exact ⟨fun hv => (Finset.mem_union.mp (hs hv)).elim
    (fun h => Or.inl ⟨hv,h⟩) (fun h => Or.inr ⟨hv,h⟩),by tauto⟩

/-- Exact split-coordinate membership of the raw parent, including raw empty. -/
theorem phi_split (X Y Z : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (s : Finset V) : s ∈ phi X Y Z D L E ↔
      s ⊆ X ∪ Y ∧ ((s ∩ X ∈ D ∧ s ∩ Y ⊆ Z) ∨
        s ∩ X ∈ L ∨ s ∩ Y ∈ E) := by
  have dz : Supported Y (delta Z) := fun _ hs => hs.trans hz
  have dy : Supported Y (delta Y) := fun _ hs => hs
  have dx : Supported X (delta X) := fun _ hs => hs
  simp only [phi,LowerSet.mem_sup_iff,
    join_split hd hD dz s,join_split hd hL dy s,join_split hd dx hE s,
    mem_delta]
  have hhX : s ∩ X ⊆ X := Finset.inter_subset_right
  have hhY : s ∩ Y ⊆ Y := Finset.inter_subset_right
  tauto

private theorem pair_cofaces (P : CollapsePair V) {K : Family V}
    (hP : P.ambient = project K) {s : Finset V} (hs : s ∈ K)
    (hls : P.lower ⊆ s) : s = P.lower ∨ s = P.upper := by
  by_cases he : s = P.lower
  · exact Or.inl he
  · exact Or.inr (P.free s (hP.symm ▸ ⟨P.lower_nonempty.mono hls,hs⟩)
      (Finset.ssubset_iff_subset_ne.mpr ⟨hls,Ne.symm he⟩))

open Classical in
/-- The deletion rectangle has no assumed local or parent schedule. All cofaces
are derived from native child freeness, alpha not in L, and raw E downwardness. -/
def deletionRectangle (X Y Z : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (P : CollapsePair V) (hP : P.ambient = project D) (hnL : P.lower ∉ L) :
    Sequence (project (phi X Y Z D L E))
      (project (cut (phi X Y Z D L E)
        (((Z.powerset.filter (fun t => t ∉ E))).image (fun t => P.lower ∪ t)))) := by
  classical
  let F := Z.powerset.filter (fun t => t ∉ E)
  have hF (t) : t ∈ F ↔ t ⊆ Z ∧ t ∉ E := by simp [F]
  have hlD : P.lower ∈ D := (hP ▸ P.lower_mem).2
  have huD : P.upper ∈ D := (hP ▸ P.upper_mem).2
  have hlX := hD _ hlD
  have huX := hD _ huD
  have hvX := huX (Finset.mem_insert_self _ _)
  have hm : ∀ t ∈ F, P.lower ∪ t ∈ phi X Y Z D L E ∧
      insert P.apex (P.lower ∪ t) ∈ phi X Y Z D L E := by
    intro t ht
    have htZ := ((hF t).mp ht).1
    constructor
    · exact Or.inl (Or.inl ⟨P.lower,hlD,t,htZ,rfl⟩)
    · have he : insert P.apex (P.lower ∪ t) = P.upper ∪ t := by
        ext v; simp only [Finset.mem_insert,Finset.mem_union]; tauto
      rw [he]
      exact Or.inl (Or.inl ⟨P.upper,huD,t,htZ,rfl⟩)
  apply rectangle X Y P.lower P.apex hd hlX hvX P.apex_notMem F
    (phi X Y Z D L E) (fun t ht => ((hF t).mp ht).1.trans hz)
    (fun t ht => P.lower_nonempty.mono Finset.subset_union_left) hm
  intro t ht s hs hts
  have hh := (phi_split X Y Z D L E hd hz hD hL hE s).mp hs
  have hax : P.lower ⊆ s ∩ X := fun v hv =>
    Finset.mem_inter.mpr ⟨hts (Finset.mem_union_left _ hv),hlX hv⟩
  have hty : t ⊆ s ∩ Y := fun v hv =>
    Finset.mem_inter.mpr ⟨hts (Finset.mem_union_right _ hv),hz (((hF t).mp ht).1 hv)⟩
  have hnE : s ∩ Y ∉ E := fun h => ((hF t).mp ht).2 (E.lower hty h)
  have hnLink : s ∩ X ∉ L := fun h => hnL (L.lower hax h)
  have hcase : s ∩ X ∈ D ∧ s ∩ Y ⊆ Z :=
    hh.2.resolve_right (fun h => h.elim hnLink hnE)
  refine ⟨s ∩ Y,(hF _).mpr ⟨hcase.2,hnE⟩,hty,?_⟩
  have he := pair_cofaces P hP hcase.1 hax
  rcases he with he | he
  · exact Or.inl ((split_recover hh.1).trans (congrArg (fun a => a ∪ (s ∩ Y)) he))
  · right
    rw [split_recover hh.1,he]
    ext v
    simp only [CollapsePair.upper,Finset.mem_union,Finset.mem_insert]
    tauto

open Classical in
/-- A link projection can have an empty alpha. Its raw coface condition is
obtained from an actual child e-containing pair by the caller. Every emitted
lower is nonempty because each selected tau lies outside delta(Z). -/
def linkRectangle (X Y Z a : Finset V) (u : V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (haX : a ⊆ X) (huX : u ∈ X) (hua : u ∉ a)
    (ha : a ∈ L) (hb : insert u a ∈ L)
    (hfree : ∀ s ∈ L, a ⊆ s → s = a ∨ s = insert u a) :
    Sequence (project (phi X Y Z D L E))
      (project (cut (phi X Y Z D L E)
        ((Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E)).image (fun t => a ∪ t)))) := by
  classical
  let F := Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E)
  have hF (t) : t ∈ F ↔ t ⊆ Y ∧ ¬ t ⊆ Z ∧ t ∉ E := by simp [F]
  have hm : ∀ t ∈ F, a ∪ t ∈ phi X Y Z D L E ∧
      insert u (a ∪ t) ∈ phi X Y Z D L E := by
    intro t ht
    constructor
    · exact Or.inl (Or.inr ⟨a,ha,t,((hF t).mp ht).1,rfl⟩)
    · refine Or.inl (Or.inr ⟨insert u a,hb,t,((hF t).mp ht).1,?_⟩)
      ext v; simp only [Finset.mem_insert,Finset.mem_union]; tauto
  apply rectangle X Y a u hd haX huX hua F (phi X Y Z D L E)
    (fun t ht => ((hF t).mp ht).1) ?_ hm
  · intro t ht
    have htne : t.Nonempty := by
      by_contra h
      have he := Finset.not_nonempty_iff_eq_empty.mp h
      exact ((hF t).mp ht).2.1 (he ▸ Finset.empty_subset Z)
    exact htne.mono Finset.subset_union_right
  · intro t ht s hs hts
    have hh := (phi_split X Y Z D L E hd hz hD hL hE s).mp hs
    have hax : a ⊆ s ∩ X := fun v hv =>
      Finset.mem_inter.mpr ⟨hts (Finset.mem_union_left _ hv),haX hv⟩
    have hty : t ⊆ s ∩ Y := fun v hv =>
      Finset.mem_inter.mpr ⟨hts (Finset.mem_union_right _ hv),((hF t).mp ht).1 hv⟩
    have hnZ : ¬ s ∩ Y ⊆ Z := fun h => ((hF t).mp ht).2.1 (hty.trans h)
    have hnE : s ∩ Y ∉ E := fun h => ((hF t).mp ht).2.2 (E.lower hty h)
    have hlink : s ∩ X ∈ L := hh.2.elim
      (fun h => False.elim (hnZ h.2)) (fun h => h.resolve_right hnE)
    refine ⟨s ∩ Y,(hF _).mpr ⟨Finset.inter_subset_right,hnZ,hnE⟩,hty,?_⟩
    rcases hfree _ hlink hax with he | he
    · exact Or.inl ((split_recover hh.1).trans (congrArg (fun a => a ∪ (s ∩ Y)) he))
    · right
      rw [split_recover hh.1,he]
      ext v; simp only [Finset.mem_union,Finset.mem_insert]; tauto

end D5.S3.Geometry.OriginalLabelTwoSum
