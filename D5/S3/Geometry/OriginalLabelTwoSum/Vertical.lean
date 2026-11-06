/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Vertical
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Vertical
   mirror-E: none(waiver:original-label-two-sum-vertical)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A genuine right Gamma yields the vertical parent collapse fixing its entire computed base. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Rectangles
import D5.S3.Geometry.OriginalLabelTwoSum.Fibre

/-! UNCOMPILED. Maximality is the raw coface consequence of a vertical child
pair. Gamma is local to the right original simplex and is an essential input.
It is not inferred from homology or from the existence of a child vertical pair. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Source/endpoints are literal Phi states with the single maximal left fibre
removed. No parent collapse, collar, or endpoint equality is an assumption. -/
def verticalGamma (X Y Z a : Finset V) (D L E : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y)
    (hD : Supported X D) (hL : Supported X L) (hE : Supported Y E)
    (hLD : L ≤ D) (ha : a ∈ L)
    (hmaxD : ∀ s ∈ D, a ⊆ s → s = a)
    (hmaxL : ∀ s ∈ L, a ⊆ s → s = a)
    (hne : a.Nonempty) (hE0 : (∅ : Finset V) ∈ E)
    (G : Sequence (project (delta Y)) (project E)) :
    Sequence (project (phi X Y Z D L E))
      (project (phi X Y Z (cut D {a}) (cut L {a}) E)) := by
  let B := phi X Y Z (cut D {a}) (cut L {a}) E
  have haX := hL a ha
  have hda : Disjoint a Y := hd.mono_left haX
  have cutD : Supported X (cut D {a}) := fun s hs => hD s hs.1
  have cutL : Supported X (cut L {a}) := fun s hs => hL s hs.1
  have hproper : ∀ x ⊂ a, ∀ t ∈ delta Y, x ∪ t ∈ B := by
    intro x hx t ht
    have hxL : x ∈ cut L {a} := ⟨L.lower hx.1 ha,by
      intro z hz
      have he : z = a := by simpa using hz
      subst z
      exact fun hh => (Finset.ne_of_ssubset hx) (Finset.Subset.antisymm hx.1 hh)⟩
    exact Or.inl (Or.inr ⟨x,hxL,t,ht,rfl⟩)
  have hbase : ∀ t ⊆ Y, a ∪ t ∈ B → t ∈ E := by
    intro t ht hs
    have hsplit := (phi_split X Y Z (cut D {a}) (cut L {a}) E hd hz
      cutD cutL hE (a ∪ t)).mp hs
    have hx : (a ∪ t) ∩ X = a := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_union]
      exact ⟨fun ⟨hv,hx⟩ => hv.elim id (fun hv =>
        False.elim (Finset.disjoint_left.mp hd hx (ht hv))),
        fun hv => ⟨Or.inl hv,haX hv⟩⟩
    have hy : (a ∪ t) ∩ Y = t := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_union]
      exact ⟨fun ⟨hv,hy⟩ => hv.elim (fun hv =>
        False.elim (Finset.disjoint_left.mp hd (haX hv) hy)) id,
        fun hv => ⟨Or.inr hv,ht hv⟩⟩
    rw [hx,hy] at hsplit
    rcases hsplit.2 with h | h | h
    · exact False.elim (h.1.2 a (by simp) le_rfl)
    · exact False.elim (h.2 a (by simp) le_rfl)
    · exact h
  have hsource : B ⊔ rawJoin (delta a) (delta Y) = phi X Y Z D L E := by
    apply SetLike.ext
    intro s
    constructor
    · rintro (hB | ⟨x,hx,t,ht,rfl⟩)
      · rcases hB with (⟨x,hx,t,ht,rfl⟩ | ⟨x,hx,t,ht,rfl⟩) | hE'
        · exact Or.inl (Or.inl ⟨x,hx.1,t,ht,rfl⟩)
        · exact Or.inl (Or.inr ⟨x,hx.1,t,ht,rfl⟩)
        · exact Or.inr hE'
      · exact Or.inl (Or.inr ⟨x,L.lower hx ha,t,ht,rfl⟩)
    · rintro ((⟨x,hx,t,ht,rfl⟩ | ⟨x,hx,t,ht,rfl⟩) | hE')
      · by_cases hax : a ⊆ x
        · have he := hmaxD x hx hax
          subst x
          exact Or.inr ⟨a,le_rfl,t,ht.trans hz,rfl⟩
        · exact Or.inl (Or.inl (Or.inl ⟨x,⟨hx,by simpa using hax⟩,t,ht,rfl⟩))
      · by_cases hax : a ⊆ x
        · have he := hmaxL x hx hax
          subst x
          exact Or.inr ⟨a,le_rfl,t,ht,rfl⟩
        · exact Or.inl (Or.inl (Or.inr ⟨x,⟨hx,by simpa using hax⟩,t,ht,rfl⟩))
      · exact Or.inl (Or.inr hE')
  have hend : B ⊔ rawJoin (delta a) E = B := by
    apply sup_eq_left.mpr
    rintro s ⟨x,hx,t,ht,rfl⟩
    exact Or.inr ⟨x,hx.trans haX,t,ht,rfl⟩
  exact (liftFibre (delta Y) E B a Y (by simp [delta]) hE0 G hda
    (fun _ hs => hs) hproper hbase).cast (congrArg project hsource)
      (congrArg project hend)

/-- The separate VOID rule uses an original r in nonempty R. The empty right
fibre emits lower=a, which is genuinely nonempty; it never collapses UNIT to VOID. -/
def verticalVoid (X Y Z R a : Finset V) (D L : Family V)
    (hd : Disjoint X Y) (hz : Z ⊆ Y) (hR : R ⊆ Y) (hRne : R.Nonempty)
    (hD : Supported X D) (hL : Supported X L) (ha : a ∈ L)
    (hmaxD : ∀ s ∈ D, a ⊆ s → s = a)
    (hmaxL : ∀ s ∈ L, a ⊆ s → s = a) (hne : a.Nonempty) :
    Sequence (project (phi X Y Z D L ⊥))
      (project (phi X Y Z (cut D {a}) (cut L {a}) ⊥)) := by
  classical
  let r := hRne.choose
  have hr : r ∈ Y := hR hRne.choose_spec
  have haX := hL a ha
  have hdisj : Disjoint (insert r a) (Y.erase r) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvY
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (Finset.mem_erase.mp hvY).1 rfl
    · exact Finset.disjoint_left.mp hd (haX hv) (Finset.mem_erase.mp hvY).2
  have hra : r ∉ a := fun h => Finset.disjoint_left.mp hd (haX h) hr
  let F := (Y.erase r).powerset
  let Q := phi X Y Z D L (⊥ : Family V)
  have hF (t) : t ∈ F ↔ t ⊆ Y.erase r := by simp [F]
  have hm : ∀ t ∈ F, a ∪ t ∈ Q ∧ insert r (a ∪ t) ∈ Q := by
    intro t ht
    have htY := ((hF t).mp ht).trans (Finset.erase_subset _ _)
    constructor
    · exact Or.inl (Or.inr ⟨a,ha,t,htY,rfl⟩)
    · refine Or.inl (Or.inr ⟨a,ha,insert r t,Finset.insert_subset_iff.mpr ⟨hr,htY⟩,?_⟩)
      ext v; simp only [Finset.mem_insert,Finset.mem_union]; tauto
  have hc : ∀ t ∈ F, ∀ s ∈ Q, a ∪ t ⊆ s →
      ∃ u ∈ F, t ⊆ u ∧ (s = a ∪ u ∨ s = insert r (a ∪ u)) := by
    intro t ht s hs hts
    have hE : Supported Y (⊥ : Family V) := by intro s hs; exact False.elim hs
    have hh := (phi_split X Y Z D L ⊥ hd hz hD hL hE s).mp hs
    have has : a ⊆ s := Finset.subset_union_left.trans hts
    have hax : a ⊆ s ∩ X := fun v hv => Finset.mem_inter.mpr ⟨has hv,haX hv⟩
    have hx : s ∩ X = a := hh.2.elim
      (fun h => hmaxD _ h.1 hax)
      (fun h => h.elim (fun h => hmaxL _ h hax) False.elim)
    have heq : s = a ∪ (s ∩ Y) := by
      ext v
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · intro hv
        rcases Finset.mem_union.mp (hh.1 hv) with hvX | hvY
        · exact Or.inl (hx ▸ Finset.mem_inter.mpr ⟨hv,hvX⟩)
        · exact Or.inr ⟨hv,hvY⟩
      · rintro (hv | hv)
        · exact has hv
        · exact hv.1
    let u := (s ∩ Y).erase r
    refine ⟨u,(hF _).mpr (by
      intro v hv
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,
        (Finset.mem_inter.mp (Finset.mem_erase.mp hv).2).2⟩),?_,?_⟩
    · intro v hv
      have hvY := (Finset.mem_erase.mp (((hF t).mp ht) hv)).2
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (((hF t).mp ht) hv)).1,
        Finset.mem_inter.mpr ⟨hts (Finset.mem_union_right _ hv),hvY⟩⟩
    · by_cases hrs : r ∈ s ∩ Y
      · right
        rw [heq,← Finset.insert_erase hrs]
        ext v; simp only [u,Finset.mem_union,Finset.mem_insert]; tauto
      · left
        simpa [u,Finset.erase_eq_of_not_mem hrs] using heq
  let S := rectangle (insert r a) (Y.erase r) a r hdisj (Finset.subset_insert _ _)
    (by simp) hra F Q (fun t ht => (hF t).mp ht)
    (fun t ht => hne.mono Finset.subset_union_left) hm hc
  have hcut : cut Q (F.image (fun t => a ∪ t)) = cut Q {a} := by
    apply SetLike.ext
    intro s
    constructor
    · rintro ⟨hs,hn⟩
      refine ⟨hs,?_⟩
      intro b hb hbs
      have hba : b = a := by simpa using hb
      subst b
      exact hn a (Finset.mem_image.mpr ⟨∅,(hF _).mpr (Finset.empty_subset _),by simp⟩) hbs
    · rintro ⟨hs,hn⟩
      refine ⟨hs,?_⟩
      intro b hb hbs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hb
      exact hn a (by simp) (Finset.subset_union_left.trans hbs)
  have hend : cut Q {a} = phi X Y Z (cut D {a}) (cut L {a}) ⊥ := by
    apply SetLike.ext
    intro s
    have no_extra {x t : Finset V} (hx : x ⊆ X) (ht : t ⊆ Y)
        (haxt : a ⊆ x ∪ t) : a ⊆ x := by
      intro v hv
      rcases Finset.mem_union.mp (haxt hv) with hvx | hvt
      · exact hvx
      · exact False.elim (Finset.disjoint_left.mp hd (haX hv) (ht hvt))
    constructor
    · rintro ⟨(hD' | hL') | hbot,hn⟩
      · obtain ⟨x,hx,t,ht,rfl⟩ := hD'
        exact Or.inl (Or.inl ⟨x,⟨hx,by
          intro b hb hbx
          have he : b = a := by simpa using hb
          subst b
          exact hn a (by simp) (hbx.trans Finset.subset_union_left)⟩,t,ht,rfl⟩)
      · obtain ⟨x,hx,t,ht,rfl⟩ := hL'
        exact Or.inl (Or.inr ⟨x,⟨hx,by
          intro b hb hbx
          have he : b = a := by simpa using hb
          subst b
          exact hn a (by simp) (hbx.trans Finset.subset_union_left)⟩,t,ht,rfl⟩)
      · obtain ⟨x,hx,t,ht,he⟩ := hbot
        exact False.elim ht
    · rintro ((⟨x,hx,t,ht,rfl⟩ | ⟨x,hx,t,ht,rfl⟩) | ⟨x,hx,t,ht,he⟩)
      · exact ⟨Or.inl (Or.inl ⟨x,hx.1,t,ht,rfl⟩),by
          intro b hb hbs
          have he : b = a := by simpa using hb
          subst b
          exact hx.2 a (by simp) (no_extra (hD _ hx.1) (ht.trans hz) hbs)⟩
      · exact ⟨Or.inl (Or.inr ⟨x,hx.1,t,ht,rfl⟩),by
          intro b hb hbs
          have he : b = a := by simpa using hb
          subst b
          exact hx.2 a (by simp) (no_extra (hL _ hx.1) ht hbs)⟩
      · exact False.elim ht
  exact S.cast rfl (congrArg project (hcut.trans hend))

end D5.S3.Geometry.OriginalLabelTwoSum
