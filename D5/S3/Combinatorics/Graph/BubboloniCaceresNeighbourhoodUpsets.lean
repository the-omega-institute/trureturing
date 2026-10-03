/- GID: D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every neighbourhood-preorder upset is convex under extreme-point generation. -/

/-
proof_shape: result: content (deletion induction and polarity transport of unit covers
  establish the rank-complement identity; inclusion-exclusion then forces actual union closure)
admission_basis: open-problem-resolution (issue #12622; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Computational content: none; the result is a structural theorem over every finite nonempty
  simple graph, not a bounded enumeration, checker, numeric reduction or certified instance.
-/



import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Daniela Bubboloni and José Cáceres, *The neighbourhood convexity*, arXiv:2608.25912v1,
Conclusions and future lines of work: every upset in the neighbourhood preorder of a
neighbourhood convex geometry is neighbourhood-convex. The definitions follow Sections 2.1
and 2.2, Definitions 3, 5, 9 and 28, and Proposition 12. The principal-upset identity from
Lemma 29(iii) is verified locally. The empty-preserving hull differs from double polarity
at the empty set; the rank identity is used only on the image of polarity.
-/

namespace D5.S3.Combinatorics.Graph.BubboloniCaceresNeighbourhoodUpsets

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def closedNeighbourhood (G : SimpleGraph α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun y => x = y ∨ G.Adj x y)

noncomputable def common (G : SimpleGraph α) (X : Finset α) : Finset α := by
  classical
  exact Finset.univ.filter (fun y => ∀ x ∈ X, y ∈ closedNeighbourhood G x)

noncomputable def convex (G : SimpleGraph α) (K : Finset α) : Prop :=
  K = ∅ ∨ ∃ Y, common G Y = K

noncomputable def hull (G : SimpleGraph α) (X : Finset α) : Finset α :=
  if X = ∅ then ∅ else common G (common G X)

noncomputable def extremes (G : SimpleGraph α) (K : Finset α) : Finset α := by
  classical
  exact K.filter (fun x => convex G (K.erase x))

/-- Every neighbourhood-preorder upset is neighbourhood-convex under the full
extreme-point generation hypothesis, at every finite nonempty graph order. -/
theorem result [Nonempty α] (G : SimpleGraph α)
    (geometry : ∀ K, convex G K → hull G (extremes G K) = K)
    (U : Finset α)
    (upset : ∀ x ∈ U, ∀ y, closedNeighbourhood G x ⊆ closedNeighbourhood G y → y ∈ U) :
    convex G U := by
  classical
  let N := common G
  let L : Finset α → Prop := fun K => ∃ Y, N Y = K
  let S := N Finset.univ
  have memN (X : Finset α) (y : α) : y ∈ N X ↔ ∀ x ∈ X, y ∈ closedNeighbourhood G x := by
    simp [N, common]
  have symmetry (x y : α) : y ∈ closedNeighbourhood G x ↔ x ∈ closedNeighbourhood G y := by
    simp only [closedNeighbourhood, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  have anti : Antitone N := by
    intro A B h y hy
    exact (memN A y).mpr (fun x hx => (memN B y).mp hy x (h hx))
  have extensive (X : Finset α) : X ⊆ N (N X) := by
    intro x hx
    apply (memN (N X) x).mpr
    intro y hy
    exact (symmetry x y).mp ((memN X y).mp hy x hx)
  have triple (X : Finset α) : N (N (N X)) = N X :=
    Finset.Subset.antisymm (anti (extensive X)) (extensive (N X))
  have Nunion (X Y : Finset α) : N (X ∪ Y) = N X ∩ N Y := by
    ext y
    simp only [memN, Finset.mem_union, Finset.mem_inter]
    constructor
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
    · rintro ⟨hX, hY⟩ x (hx | hy)
      · exact hX x hx
      · exact hY x hy
  have fixed (K : Finset α) (hK : L K) : N (N K) = K := by
    obtain ⟨Y, rfl⟩ := hK
    exact triple Y
  have image (X : Finset α) : L (N X) := ⟨X, rfl⟩
  have Nempty : N ∅ = Finset.univ := by
    ext x
    simp [memN]
  have top : L Finset.univ := ⟨∅, Nempty⟩
  have bottom : L S := image Finset.univ
  have bottom_subset (K : Finset α) (hK : L K) : S ⊆ K := by
    obtain ⟨Y, rfl⟩ := hK
    exact anti (Finset.subset_univ Y)
  have NS : N S = Finset.univ := fixed Finset.univ top
  have hull_mono : Monotone (hull G) := by
    intro A B h
    by_cases hA : A = ∅
    · simp [hull, hA]
    · have hB : B ≠ ∅ := by
        intro he
        apply hA
        exact Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa [he] using h hx)
      simpa [hull, hA, hB, N] using anti (anti h)
  have hull_fixed (K : Finset α) (hK : convex G K) : hull G K = K := by
    rcases hK with hK | hK
    · simp [hull, hK]
    · by_cases he : K = ∅
      · simp [hull, he]
      · simpa [hull, he, N] using fixed K hK
  have removable {A B : Finset α} (hA : convex G A) (hB : convex G B)
      (hnot : ¬ B ⊆ A) : ∃ x, x ∈ B ∧ x ∉ A ∧ convex G (B.erase x) := by
    by_contra hn
    have hs : extremes G B ⊆ A := by
      intro x hx
      have hx' : x ∈ B ∧ convex G (B.erase x) := by simpa [extremes] using hx
      by_contra hxa
      exact hn ⟨x, hx'.1, hxa, hx'.2⟩
    apply hnot
    calc
      B = hull G (extremes G B) := (geometry B hB).symm
      _ ⊆ hull G A := hull_mono hs
      _ = A := hull_fixed A hA
  have unitcover {A B : Finset α} (hA : L A) (hB : L B)
      (hAB : A ⊆ B) (hnot : ¬ B ⊆ A)
      (cover : ∀ T, L T → A ⊆ T → T ⊆ B → T = A ∨ T = B) :
      ∃ x ∈ B, B.erase x = A := by
    obtain ⟨x, hxB, hxA, hxC⟩ := removable (Or.inr hA) (Or.inr hB) hnot
    have hi : A ⊆ B.erase x := Finset.subset_erase.mpr ⟨hAB, hxA⟩
    have hxL : L (B.erase x) := by
      rcases hxC with he | hl
      · have hAe : A = ∅ := Finset.Subset.antisymm (he ▸ hi) (Finset.empty_subset A)
        exact he.symm ▸ (hAe ▸ hA)
      · exact hl
    rcases cover (B.erase x) hxL hi (Finset.erase_subset x B) with he | he
    · exact ⟨x, hxB, he⟩
    · have hx : x ∈ B.erase x := he.symm ▸ hxB
      exact False.elim ((Finset.mem_erase.mp hx).1 rfl)
  have rank (K : Finset α) :
      L K → K.card + (N K).card = (Finset.univ : Finset α).card + S.card := by
    induction K using Finset.strongInductionOn with
    | _ K ih =>
      intro hK
      by_cases hKS : K = S
      · simp only [hKS, NS]
        omega
      · have hSK := bottom_subset K hK
        have hn : ¬ K ⊆ S := fun h => hKS (Finset.Subset.antisymm h hSK)
        obtain ⟨x, hxK, hxS, hxC⟩ := removable (Or.inr bottom) (Or.inr hK) hn
        let D := K.erase x
        have hSD : S ⊆ D := Finset.subset_erase.mpr ⟨hSK, hxS⟩
        have hD : L D := by
          rcases hxC with he | hl
          · have hSe : S = ∅ := Finset.Subset.antisymm (he ▸ hSD) (Finset.empty_subset S)
            change L (K.erase x)
            rw [he]
            exact hSe ▸ bottom
          · exact hl
        have hDK : D ⊆ K := Finset.erase_subset x K
        have cover : ∀ T, L T → D ⊆ T → T ⊆ K → T = D ∨ T = K := by
          intro T _ hDT hTK
          by_cases hxT : x ∈ T
          · right
            apply Finset.Subset.antisymm hTK
            intro y hy
            by_cases hyx : y = x
            · exact hyx ▸ hxT
            · exact hDT (Finset.mem_erase.mpr ⟨hyx, hy⟩)
          · left
            exact Finset.Subset.antisymm (Finset.subset_erase.mpr ⟨hTK, hxT⟩) hDT
        have dual_not : ¬ N D ⊆ N K := by
          intro h
          have hh := anti h
          rw [fixed K hK, fixed D hD] at hh
          have hx : x ∈ D := hh hxK
          exact (Finset.mem_erase.mp hx).1 rfl
        have dualcover : ∀ T, L T → N K ⊆ T → T ⊆ N D → T = N K ∨ T = N D := by
          intro T hT hKT hTD
          have h1 := anti hTD
          have h2 := anti hKT
          rw [fixed D hD] at h1
          rw [fixed K hK] at h2
          rcases cover (N T) (image T) h1 h2 with he | he
          · right
            have hh := congrArg N he
            rwa [fixed T hT] at hh
          · left
            have hh := congrArg N he
            rwa [fixed T hT] at hh
        obtain ⟨y, hy, he⟩ := unitcover (image K) (image D) (anti hDK) dual_not dualcover
        have rD := ih D (Finset.erase_ssubset hxK) hD
        have cK := Finset.card_erase_add_one hxK
        have cN := Finset.card_erase_add_one hy
        rw [he] at cN
        change D.card + 1 = K.card at cK
        omega
  have intersection {A B : Finset α} (hA : L A) (hB : L B) : L (A ∩ B) := by
    refine ⟨N A ∪ N B, ?_⟩
    rw [Nunion, fixed A hA, fixed B hB]
  have union {A B : Finset α} (hA : L A) (hB : L B) : L (A ∪ B) := by
    have rA := rank A hA
    have rB := rank B hB
    have rD := rank (A ∩ B) (intersection hA hB)
    have rJ := rank (N (N (A ∪ B))) (image (N (A ∪ B)))
    have hN : N (N (N (A ∪ B))) = N A ∩ N B :=
      (triple (A ∪ B)).trans (Nunion A B)
    rw [hN] at rJ
    have uA := Finset.card_union_add_card_inter A B
    have uN := Finset.card_union_add_card_inter (N A) (N B)
    have hm : (N A ∪ N B).card ≤ (N (A ∩ B)).card :=
      Finset.card_le_card (Finset.union_subset
        (anti Finset.inter_subset_left) (anti Finset.inter_subset_right))
    have he : N (N (A ∪ B)) = A ∪ B := by
      apply (Finset.eq_of_subset_of_card_le (extensive (A ∪ B)) ?_).symm
      omega
    exact ⟨N (A ∪ B), he⟩
  have convex_union {A B : Finset α} (hA : convex G A) (hB : convex G B) :
      convex G (A ∪ B) := by
    rcases hA with he | hl
    · simpa [he] using hB
    rcases hB with he | hr
    · rw [he, Finset.union_empty]
      exact Or.inr hl
    exact Or.inr (union hl hr)
  let P : α → Finset α := fun x => Finset.univ.filter
    (fun y => closedNeighbourhood G x ⊆ closedNeighbourhood G y)
  -- The principal-upset identity is the source's Lemma 29(iii), proved here locally.
  have principal (x : α) : convex G (P x) := by
    have single : N {x} = closedNeighbourhood G x := by
      ext y
      simp [memN]
    refine Or.inr ⟨N {x}, ?_⟩
    rw [single]
    change N (closedNeighbourhood G x) = P x
    ext y
    simp only [memN, P, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h z hz
      exact (symmetry z y).mp (h z hz)
    · intro h z hz
      exact (symmetry z y).mpr (h hz)
  have finite_union (T : Finset α) : convex G (T.biUnion P) := by
    induction T using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | @insert x T hx ih =>
      rw [Finset.biUnion_insert]
      exact convex_union (principal x) ih
  have representation : U.biUnion P = U := by
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact upset x hx y (by simpa [P] using hy)
    · intro hy
      exact ⟨y, hy, by simp [P]⟩
  exact representation ▸ finite_union U

end D5.S3.Combinatorics.Graph.BubboloniCaceresNeighbourhoodUpsets
