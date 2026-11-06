/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalMWheel
   generality: G
   digest: Every width wheel as an actual hub-star graph with path-derived rows. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalLabels
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalGlue
import D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel
import D5.S3.Geometry.OriginalLabelTwoSum.Rename
import Mathlib.Combinatorics.SimpleGraph.Star

/-! SOURCE_ONLY_UNCOMPILED. Vertices are the literal hub 0 and rim 1,...,m.
The rows below are proved by uniqueness from explicit two-edge tree walks.
No row, root, spanning-tree or parent correctness is an input field. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel

private theorem label_ne_zero (m : Nat) (i : Fin m) :
    AllMWheel.label m i ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change i.val + 1 = 0 at hv
  omega

private theorem label_injective (m : Nat) : Function.Injective (AllMWheel.label m) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change i.val + 1 = j.val + 1 at hv
  omega

private theorem spoke_eq {m : Nat} (x y : AllMWheel.Label m) :
    s((0 : AllMWheel.Label m),x) = s(0,y) ↔ x = y := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨_,he⟩ | ⟨h0,hx⟩
    · exact he
    · exact hx.trans h0
  · rintro rfl
    rfl

private theorem consecutive_ne (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    AllMWheel.label m i ≠ AllMWheel.label m (AllMWheel.rimIndex m (by omega) i) := by
  intro h
  have hv := congrArg Fin.val (label_injective m h)
  change i.val = (i.val + 1) % m at hv
  have hi := i.isLt
  by_cases hlt : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have he : i.val + 1 = m := by omega
    rw [he,Nat.mod_self] at hv
    omega

def rimGraph (m : Nat) (hm : 3 ≤ m) : SimpleGraph (AllMWheel.Label m) where
  Adj x y := ∃ i : Fin m,
    s(x,y) = s(AllMWheel.label m i,AllMWheel.label m (AllMWheel.rimIndex m (by omega) i))
  symm := ⟨by
    rintro x y ⟨i,hi⟩
    exact ⟨i,Sym2.eq_swap.trans hi⟩⟩
  loopless := ⟨by
    rintro x ⟨i,hi⟩
    rcases Sym2.eq_iff.mp hi with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact consecutive_ne m hm i (hx.symm.trans hy)
    · exact consecutive_ne m hm i (hy.symm.trans hx)⟩

def data (m : Nat) (hm : 3 ≤ m) : GraphData (AllMWheel.Label m) (AllMWheel.Label m) where
  graph := SimpleGraph.starGraph 0 ⊔ rimGraph m hm
  tree := SimpleGraph.starGraph 0
  tree_le := le_sup_left
  isTree := SimpleGraph.isTree_starGraph 0
  ground := AllMWheel.ground m
  edge i := s(0,i)
  tree_edges := by
    intro x y
    rw [SimpleGraph.starGraph_adj]
    constructor
    · rintro ⟨hne,hx | hy⟩
      · subst x
        exact ⟨y,by simp [AllMWheel.ground,Ne.symm hne],rfl⟩
      · subst y
        exact ⟨x,by simp [AllMWheel.ground,hne],Sym2.eq_swap⟩
    · rintro ⟨i,hi,he⟩
      have hn : i ≠ 0 := by simpa [AllMWheel.ground] using hi
      rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hy,hx⟩ <;> subst x <;> subst y
      · exact ⟨Ne.symm hn,Or.inl rfl⟩
      · exact ⟨hn,Or.inr rfl⟩
  labels_injective := by
    intro i _ j _ he
    rcases Sym2.eq_iff.mp he with ⟨_,h⟩ | ⟨h0,hi⟩
    · exact h
    · exact hi.trans h0
  chords := Fin m
  start := AllMWheel.label m
  finish i := AllMWheel.label m (AllMWheel.rimIndex m (by omega) i)
  chord_adj := by intro i; exact Or.inr ⟨i,rfl⟩
  chord_not_tree := by
    intro i
    simp only [SimpleGraph.starGraph_adj]
    exact fun h => h.2.elim (label_ne_zero m i)
      (label_ne_zero m (AllMWheel.rimIndex m (by omega) i))
  chord_cover := by
    intro x y h hn
    rcases h with ht | ⟨i,hi⟩
    · exact False.elim (hn ht)
    · exact ⟨i,hi.symm⟩

def rimPath (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    (data m hm).tree.Walk ((data m hm).start i) ((data m hm).finish i) :=
  .cons (SimpleGraph.starGraph_center_adj' (Ne.symm (label_ne_zero m i)))
    (.cons (SimpleGraph.starGraph_center_adj
      (Ne.symm (label_ne_zero m (AllMWheel.rimIndex m (by omega) i)))) .nil)

theorem rimPath_isPath (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    (rimPath m hm i).IsPath := by
  simp [rimPath, data, SimpleGraph.Walk.isPath_def, label_ne_zero,
    Ne.symm (label_ne_zero m (AllMWheel.rimIndex m (by omega) i)),
    consecutive_ne m hm i]

theorem fundamental_rows (m : Nat) (hm : 3 ≤ m) (i : Fin m) :
    (data m hm).rows.row i = AllMWheel.rimEdge m (by omega) i := by
  have hp := (data m hm).path_eq i (rimPath m hm i) (rimPath_isPath m hm i)
  ext k
  simp only [GraphData.rows, Finset.mem_filter]
  rw [hp]
  have hswap : s(AllMWheel.label m i,(0 : AllMWheel.Label m)) = s(0,AllMWheel.label m i) :=
    Sym2.eq_swap
  change (k ∈ AllMWheel.ground m ∧ s(0,k) ∈ (rimPath m hm i).edges) ↔ _
  simp only [rimPath,data,SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false,hswap,
    spoke_eq,AllMWheel.rimEdge,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    rcases h with rfl | rfl <;> simp [AllMWheel.ground,label_ne_zero]

theorem interface_row (m : Nat) (hm : 3 ≤ m) :
    (data m hm).rows.row (AllMWheel.interfaceRow m hm) = AllMWheel.rim m hm := by
  rw [fundamental_rows]
  have hmod : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  simp [AllMWheel.rimEdge,AllMWheel.interfaceRow,AllMWheel.rimIndex,
    AllMWheel.label,AllMWheel.rim,AllMWheel.firstLabel,AllMWheel.secondLabel,hmod]

theorem uniqueInterface (m : Nat) (hm : 3 ≤ m) :
    (data m hm).UniqueInterface (AllMWheel.interfaceRow m hm) := by
  intro i hi
  have hmod : 1 % m = 1 := Nat.mod_eq_of_lt (by omega)
  have hi' : s(AllMWheel.label m i,AllMWheel.label m (AllMWheel.rimIndex m (by omega) i)) =
      s(AllMWheel.firstLabel m hm,AllMWheel.secondLabel m hm) := by
    simpa [GraphData.kappa,data,AllMWheel.interfaceRow,AllMWheel.label,
      AllMWheel.rimIndex,AllMWheel.firstLabel,AllMWheel.secondLabel,hmod] using hi
  rcases Sym2.eq_iff.mp hi' with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · apply Fin.ext
    have hv := congrArg Fin.val ha
    change i.val + 1 = 1 at hv
    change i.val = 0
    omega
  · have hva := congrArg Fin.val ha
    have hvb := congrArg Fin.val hb
    change i.val + 1 = 2 at hva
    change (i.val + 1) % m + 1 = 1 at hvb
    have hi1 : i.val = 1 := by omega
    rw [hi1,Nat.mod_eq_of_lt (show 1 + 1 < m by omega)] at hvb
    omega

variable {V : Type*} [Fintype V] [DecidableEq V]

def ambientGraph (m : Nat) (hm : 3 ≤ m) (f : AllMWheel.Label m ↪ V) :
    GraphData (AllMWheel.Label m) V := PhysicalLabels.data (data m hm) f s(0,0)

theorem ambient_row (m : Nat) (hm : 3 ≤ m) (f : AllMWheel.Label m ↪ V) (i : Fin m) :
    (ambientGraph m hm f).rows.row i = (AllMWheel.rimEdge m (by omega) i).image f := by
  dsimp only [ambientGraph]
  rw [PhysicalLabels.row,fundamental_rows]

theorem ambient_interface_row (m : Nat) (hm : 3 ≤ m) (f : AllMWheel.Label m ↪ V) :
    (ambientGraph m hm f).rows.row (AllMWheel.interfaceRow m hm) = (AllMWheel.rim m hm).image f := by
  dsimp only [ambientGraph]
  rw [PhysicalLabels.row,interface_row]

theorem ambient_uniqueInterface (m : Nat) (hm : 3 ≤ m) (f : AllMWheel.Label m ↪ V) :
    (ambientGraph m hm f).UniqueInterface (AllMWheel.interfaceRow m hm) :=
  uniqueInterface m hm

theorem zero_outside_ground (m : Nat) (f : AllMWheel.Label m ↪ V) :
    f 0 ∉ (AllMWheel.ground m).image f := by
  rintro hi
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
  have hj0 := f.injective he
  subst j
  simpa [AllMWheel.ground] using hj

theorem ambient_without (m : Nat) (hm : 3 ≤ m) (f : AllMWheel.Label m ↪ V) :
    ((ambientGraph m hm f).rows.without (AllMWheel.interfaceRow m hm)).root =
      renameFamily f (AllMWheel.pathRoot m hm) := by
  apply SetLike.ext
  intro s
  change (∃ i : {i : Fin m // i ≠ AllMWheel.interfaceRow m hm},
      s ⊆ (AllMWheel.ground m).image f \ (ambientGraph m hm f).rows.row i.1) ↔
    ∃ t, (∃ i : {i : Fin m // i ≠ AllMWheel.interfaceRow m hm},
      t ⊆ AllMWheel.ground m \ AllMWheel.rimEdge m (by omega) i.1) ∧ t.image f = s
  simp_rw [ambient_row,← Finset.image_sdiff _ _ f.injective]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp hi
    exact ⟨t,⟨i,ht⟩,he⟩
  · rintro ⟨t,⟨i,ht⟩,rfl⟩
    exact ⟨i,Finset.image_subset_image ht⟩

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel
