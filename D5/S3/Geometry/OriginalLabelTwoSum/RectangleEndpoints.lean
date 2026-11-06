/- GID: D5/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/RectangleEndpoints
   mirror-E: none(waiver:original-label-two-sum-rectangle-endpoints)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Raw cuts of the two descending rectangles equal the exact changed Phi states. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Rectangles

/-! UNCOMPILED. These endpoint equalities are proved from raw membership; they
are not desired-endpoint hypotheses passed to the rectangle constructors. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem left_of_union_subset {X Y a t s : Finset V}
    (ha : a ⊆ X) (ht : t ⊆ Y) (h : a ∪ t ⊆ s) :
    a ⊆ s ∩ X ∧ t ⊆ s ∩ Y :=
  ⟨fun v hv => Finset.mem_inter.mpr ⟨h (Finset.mem_union_left _ hv),ha hv⟩,
   fun v hv => Finset.mem_inter.mpr ⟨h (Finset.mem_union_right _ hv),ht hv⟩⟩

open Classical in
/-- Exact deletion-rectangle endpoint, including every empty-fibre case. -/
theorem deletionCut (X Y Z a : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (ha : a ⊆ X)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (hnL : a ∉ L) :
    cut (phi X Y Z D L E)
        ((Z.powerset.filter (fun t => t ∉ E)).image (fun t => a ∪ t)) =
      phi X Y Z (cut D {a}) L E := by
  classical
  have hDc : Supported X (cut D {a}) := fun s hs => hD s hs.1
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs,hnot⟩
    have hh := (phi_split X Y Z D L E hd hz hD hL hE s).mp hs
    apply (phi_split X Y Z (cut D {a}) L E hd hz hDc hL hE s).mpr
    refine ⟨hh.1,?_⟩
    rcases hh.2 with hh | hh | hh
    · by_cases he : s ∩ Y ∈ E
      · exact Or.inr (Or.inr he)
      · left
        refine ⟨⟨hh.1,?_⟩,hh.2⟩
        intro b hb hab
        have hba : b = a := by simpa using hb
        subst b
        have hF : s ∩ Y ∈ Z.powerset.filter (fun t => t ∉ E) := by simp [hh.2,he]
        apply hnot (a ∪ (s ∩ Y)) (Finset.mem_image.mpr ⟨s ∩ Y,hF,rfl⟩)
        exact Finset.union_subset (hab.trans Finset.inter_subset_left) Finset.inter_subset_left
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  · intro hs
    have hh := (phi_split X Y Z (cut D {a}) L E hd hz hDc hL hE s).mp hs
    refine ⟨(phi_split X Y Z D L E hd hz hD hL hE s).mpr ⟨hh.1,?_⟩,?_⟩
    · exact hh.2.elim (fun h => Or.inl ⟨h.1.1,h.2⟩) Or.inr
    · intro b hb hbs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hb
      have htf := Finset.mem_filter.mp ht
      have htZ := Finset.mem_powerset.mp htf.1
      have hparts := left_of_union_subset ha (htZ.trans hz) hbs
      rcases hh.2 with h | h | h
      · exact h.1.2 a (by simp) hparts.1
      · exact hnL (L.lower hparts.1 h)
      · exact htf.2 (E.lower hparts.2 h)

open Classical in
/-- Exact link-rectangle endpoint. L<=D accounts for the fibres already retained
in D*delta(Z); an empty projected lower is handled without an ordinary move. -/
theorem linkCut (X Y Z a : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (ha : a ⊆ X)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E) (hLD : L ≤ D) :
    cut (phi X Y Z D L E)
        ((Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E)).image (fun t => a ∪ t)) =
      phi X Y Z D (cut L {a}) E := by
  classical
  have hLc : Supported X (cut L {a}) := fun s hs => hL s hs.1
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs,hnot⟩
    have hh := (phi_split X Y Z D L E hd hz hD hL hE s).mp hs
    apply (phi_split X Y Z D (cut L {a}) E hd hz hD hLc hE s).mpr
    refine ⟨hh.1,?_⟩
    rcases hh.2 with hh | hh | hh
    · exact Or.inl hh
    · by_cases he : s ∩ Y ∈ E
      · exact Or.inr (Or.inr he)
      · by_cases hz' : s ∩ Y ⊆ Z
        · exact Or.inl ⟨hLD hh,hz'⟩
        · right; left
          refine ⟨hh,?_⟩
          intro b hb hab
          have hba : b = a := by simpa using hb
          subst b
          have hF : s ∩ Y ∈ Y.powerset.filter (fun t => ¬ t ⊆ Z ∧ t ∉ E) := by
            simp [Finset.inter_subset_right,hz',he]
          apply hnot (a ∪ (s ∩ Y)) (Finset.mem_image.mpr ⟨s ∩ Y,hF,rfl⟩)
          exact Finset.union_subset (hab.trans Finset.inter_subset_left) Finset.inter_subset_left
    · exact Or.inr (Or.inr hh)
  · intro hs
    have hh := (phi_split X Y Z D (cut L {a}) E hd hz hD hLc hE s).mp hs
    refine ⟨(phi_split X Y Z D L E hd hz hD hL hE s).mpr ⟨hh.1,?_⟩,?_⟩
    · exact hh.2.elim Or.inl (fun h => Or.inr (h.elim (fun h => Or.inl h.1) Or.inr))
    · intro b hb hbs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hb
      have htf := Finset.mem_filter.mp ht
      have htY := Finset.mem_powerset.mp htf.1
      have hparts := left_of_union_subset ha htY hbs
      rcases hh.2 with h | h | h
      · exact htf.2.1 (hparts.2.trans h.2)
      · exact h.2 a (by simp) hparts.1
      · exact htf.2.2 (E.lower hparts.2 h)

/-- Endpoint-transported deletion rule consumes its proved raw equality. -/
def deletionLift (X Y Z : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (P : CollapsePair V) (hP : P.ambient = project D) (hnL : P.lower ∉ L) :
    Sequence (project (phi X Y Z D L E))
      (project (phi X Y Z (cut D {P.lower}) L E)) :=
  (deletionRectangle X Y Z D L E hd hz hD hL hE P hP hnL).cast rfl
    (congrArg project (deletionCut X Y Z P.lower D L E hd hz
      (hD _ (hP ▸ P.lower_mem).2) hD hL hE hnL))

/-- Endpoint-transported link rule consumes its proved raw equality. -/
def linkLift (X Y Z a : Finset V) (u : V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E) (hLD : L ≤ D)
    (haX : a ⊆ X) (huX : u ∈ X) (hua : u ∉ a)
    (ha : a ∈ L) (hb : insert u a ∈ L)
    (hf : ∀ s ∈ L, a ⊆ s → s = a ∨ s = insert u a) :
    Sequence (project (phi X Y Z D L E))
      (project (phi X Y Z D (cut L {a}) E)) :=
  (linkRectangle X Y Z a u D L E hd hz hD hL hE haX huX hua ha hb hf).cast
    rfl (congrArg project (linkCut X Y Z a D L E hd hz haX hD hL hE hLD))

end D5.S3.Geometry.OriginalLabelTwoSum
