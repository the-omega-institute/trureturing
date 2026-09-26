/- GID: D5/S3/Combinatorics/SolidPartitionFirstColumn
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SolidPartitionFirstColumn
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves the first-column conjectures of OEIS A098052 and A098530 (Wouter Meeussen, 2004): the solid partitions of n with exactly four extensions to a solid partition of n + 1, and the solid partitions of n + 1 containing exactly one solid partition of n, are the boxes, so both are counted by tau_4 (A007426). -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: a finite lower set of `ℕ⁴` with
  exactly four extensions (`ext_box`), or with exactly one shrinking (`shrink_box`), is a box. The
  extensions of a box are its four axis cells (`box_ext`); a non-box has a fifth extension, the cell
  of least coordinate sum in its bounding box outside it; a non-box has two cells with nothing above
  them, found by maximizing the coordinate sum; boxes of `n` cells correspond to ordered
  factorizations of `n` (`box_inj`, `card_box`)
admission_basis: open-problem-resolution (issue #10330)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SolidPartitionFirstColumn

/-- A solid partition of `n`, read as its four-dimensional Ferrers diagram: a finite lower set of
`n` cells of `ℕ⁴`. -/
def IsSolidPartition (n : ℕ) (I : Finset (Fin 4 → ℕ)) : Prop :=
  IsLowerSet (I : Set (Fin 4 → ℕ)) ∧ I.card = n

/-- The number of solid partitions of `n + 1` that contain `I`. -/
noncomputable def extensions (n : ℕ) (I : Finset (Fin 4 → ℕ)) : ℕ :=
  {J : Finset (Fin 4 → ℕ) | IsSolidPartition (n + 1) J ∧ I ⊆ J}.ncard

/-- The number of solid partitions of `n` contained in `J`. -/
noncomputable def shrinkings (n : ℕ) (J : Finset (Fin 4 → ℕ)) : ℕ :=
  {I : Finset (Fin 4 → ℕ) | IsSolidPartition n I ∧ I ⊆ J}.ncard

/-- The first column of A098052: solid partitions of `n` that extend in exactly four ways. -/
noncomputable def a098052FirstColumn (n : ℕ) : ℕ :=
  {I : Finset (Fin 4 → ℕ) | IsSolidPartition n I ∧ extensions n I = 4}.ncard

/-- The first column of A098530: solid partitions of `n + 1` that shrink in exactly one way. -/
noncomputable def a098530FirstColumn (n : ℕ) : ℕ :=
  {J : Finset (Fin 4 → ℕ) | IsSolidPartition (n + 1) J ∧ shrinkings n J = 1}.ncard

/-- A007426: the number of ordered factorizations `n = r s t u`. -/
noncomputable def tau4 (n : ℕ) : ℕ :=
  {v : Fin 4 → ℕ | ∏ i, v i = n}.ncard

/-- Meeussen's first-column conjectures in A098052 and A098530. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a098052FirstColumn n = tau4 n ∧ a098530FirstColumn n = tau4 (n + 1)

/-- The box `∏ [0, v i)`. -/
private def box (v : Fin 4 → ℕ) : Finset (Fin 4 → ℕ) :=
  Fintype.piFinset fun i => Finset.range (v i)

theorem result : claim := by
  classical
  have mem_box : ∀ (v c : Fin 4 → ℕ), c ∈ box v ↔ ∀ i, c i < v i := by
    intro v c
    simp [box, Fintype.mem_piFinset]
  have card_box : ∀ v : Fin 4 → ℕ, (box v).card = ∏ i, v i := by
    intro v
    simp [box, Fintype.card_piFinset]
  have lower_box :
      ∀ v : Fin 4 → ℕ, IsLowerSet ((box v : Finset (Fin 4 → ℕ)) : Set (Fin 4 → ℕ)) := by
    intro v a b hba ha
    rw [Finset.mem_coe, mem_box] at ha ⊢
    exact fun i => lt_of_le_of_lt (hba i) (ha i)
  have pos_of_prod : ∀ (v : Fin 4 → ℕ) (n : ℕ), 1 ≤ n → ∏ i, v i = n → ∀ i, 0 < v i := by
    intro v n hn hv i
    rcases Nat.eq_zero_or_pos (v i) with h | h
    · have : ∏ j, v j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h
      omega
    · exact h
  have sum_lt : ∀ a b : Fin 4 → ℕ, a < b → ∑ i, a i < ∑ i, b i := by
    intro a b hab
    rw [Pi.lt_def] at hab
    obtain ⟨hle, i, hi⟩ := hab
    exact Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hi⟩
  -- a positive box is determined by its cells
  have box_inj : ∀ v w : Fin 4 → ℕ, (∀ i, 0 < v i) → (∀ i, 0 < w i) → box v = box w → v = w := by
    have single_mem : ∀ u : Fin 4 → ℕ, (∀ j, 0 < u j) → ∀ i, Pi.single i (u i - 1) ∈ box u := by
      intro u hu i
      rw [mem_box]
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.single_eq_same]
        have := hu j
        omega
      · simp only [Pi.single_eq_of_ne hj]
        exact hu j
    intro v w hv hw h
    funext i
    have h1 := (mem_box w _).1 (h ▸ single_mem v hv i) i
    have h2 := (mem_box v _).1 (h.symm ▸ single_mem w hw i) i
    simp only [Pi.single_eq_same] at h1 h2
    have := hv i
    have := hw i
    omega
  -- inserting two outside cells gives the same set only for the same cell
  have insert_inj : ∀ (I : Finset (Fin 4 → ℕ)) (a b : Fin 4 → ℕ), a ∉ I → insert a I = insert b I →
      a = b := by
    intro I a b ha h
    have : a ∈ insert b I := h ▸ Finset.mem_insert_self a I
    rcases Finset.mem_insert.1 this with h' | h'
    · exact h'
    · exact absurd h' ha
  -- Step 1: a positive box has exactly the four extensions at the axis cells.
  have box_ext : ∀ v : Fin 4 → ℕ, (∀ i, 0 < v i) →
      {J : Finset (Fin 4 → ℕ) | IsSolidPartition ((box v).card + 1) J ∧ box v ⊆ J} =
        Set.range fun i => insert (Pi.single i (v i)) (box v) := by
    intro v hv
    have single_not : ∀ i, Pi.single i (v i) ∉ box v := by
      intro i h
      have := (mem_box v _).1 h i
      simp at this
    ext J
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨hJl, hJc⟩, hsub⟩
      have hcard : (J \ box v).card = 1 := by
        rw [Finset.card_sdiff_of_subset hsub, hJc]
        omega
      obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard
      have hcJ : c ∈ J := (Finset.mem_sdiff.1 (hc ▸ Finset.mem_singleton_self c)).1
      have hcb : c ∉ box v := (Finset.mem_sdiff.1 (hc ▸ Finset.mem_singleton_self c)).2
      have hJeq : J = insert c (box v) := by
        ext x
        rw [Finset.mem_insert]
        constructor
        · intro hx
          by_cases hxb : x ∈ box v
          · exact Or.inr hxb
          · left
            have : x ∈ J \ box v := Finset.mem_sdiff.2 ⟨hx, hxb⟩
            rw [hc] at this
            exact Finset.mem_singleton.1 this
        · rintro (rfl | hx)
          · exact hcJ
          · exact hsub hx
      -- every cell strictly below `c` lies in the box
      have below : ∀ y : Fin 4 → ℕ, y ≤ c → y ≠ c → y ∈ box v := by
        intro y hy hne
        have hyJ : y ∈ J := hJl hy hcJ
        rw [hJeq, Finset.mem_insert] at hyJ
        rcases hyJ with h | h
        · exact absurd h hne
        · exact h
      have hcb' : ∃ j, v j ≤ c j := by
        by_contra hno
        push Not at hno
        exact hcb ((mem_box v c).2 hno)
      obtain ⟨j, hj⟩ := hcb'
      have zero_off : ∀ i, i ≠ j → c i = 0 := by
        intro i hij
        by_contra hci
        have hy := below (Function.update c i 0)
          (fun k => by
            by_cases hk : k = i
            · subst hk; simp
            · simp [Function.update_of_ne hk])
          (fun heq => hci (by
            have := congrFun heq i
            simp at this
            exact this.symm))
        have := (mem_box v _).1 hy j
        rw [Function.update_of_ne (Ne.symm hij)] at this
        omega
      have eq_j : c j = v j := by
        by_contra hne
        have hlt : v j < c j := lt_of_le_of_ne hj (Ne.symm hne)
        have hy := below (Function.update c j (v j))
          (fun k => by
            by_cases hk : k = j
            · subst hk; simp; omega
            · simp [Function.update_of_ne hk])
          (fun heq => by
            have := congrFun heq j
            simp at this
            omega)
        have := (mem_box v _).1 hy j
        simp at this
      refine ⟨j, ?_⟩
      rw [hJeq]
      congr 1
      funext k
      by_cases hk : k = j
      · subst hk; simp [eq_j]
      · simp [Pi.single_eq_of_ne hk, zero_off k hk]
    · rintro ⟨i, rfl⟩
      refine ⟨⟨?_, ?_⟩, Finset.subset_insert _ _⟩
      · intro a b hba ha
        rw [Finset.coe_insert, Set.mem_insert_iff] at ha ⊢
        rcases ha with rfl | ha
        · by_cases hb : b i = v i
          · left
            funext k
            by_cases hk : k = i
            · subst hk; simp [hb]
            · have := hba k
              simp only [Pi.single_eq_of_ne hk] at this ⊢
              omega
          · right
            rw [Finset.mem_coe, mem_box]
            intro k
            by_cases hk : k = i
            · subst hk
              have := hba k
              simp only [Pi.single_eq_same] at this
              omega
            · have := hba k
              simp only [Pi.single_eq_of_ne hk] at this
              have := hv k
              omega
        · exact Or.inr (lower_box v hba ha)
      · rw [Finset.card_insert_of_notMem (single_not i)]
  -- the four axis extensions are distinct
  have axis_inj : ∀ (v : Fin 4 → ℕ) (I : Finset (Fin 4 → ℕ)), (∀ i, 0 < v i) →
      (∀ i, Pi.single i (v i) ∉ I) → Function.Injective fun i => insert (Pi.single i (v i)) I := by
    intro v I hv hnot i i' h
    have := insert_inj I _ _ (hnot i) h
    by_contra hne
    have := congrFun this i
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    have := hv i
    omega
  -- Step 2: four extensions force a box.
  have ext_box : ∀ (n : ℕ) (I : Finset (Fin 4 → ℕ)), 1 ≤ n → IsSolidPartition n I →
      extensions n I = 4 → ∃ v : Fin 4 → ℕ, (∀ i, 0 < v i) ∧ I = box v := by
    intro n I hn ⟨hIl, hIc⟩ hext
    have hne : I.Nonempty := Finset.card_pos.1 (by omega)
    set v : Fin 4 → ℕ := fun i => (I.sup fun c => c i) + 1 with hvdef
    have hvpos : ∀ i, 0 < v i := fun i => Nat.succ_pos _
    have hsub : I ⊆ box v := by
      intro c hc
      rw [mem_box]
      intro i
      have : c i ≤ I.sup fun c => c i := Finset.le_sup (f := fun c => c i) hc
      simp only [hvdef]
      omega
    have single_not : ∀ i, Pi.single i (v i) ∉ I := by
      intro i h
      have := (mem_box v _).1 (hsub h) i
      simp at this
    set S := {J : Finset (Fin 4 → ℕ) | IsSolidPartition (n + 1) J ∧ I ⊆ J} with hSdef
    have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by
      change extensions n I ≠ 0
      omega)
    have ins_mem : ∀ c : Fin 4 → ℕ, c ∉ I →
        IsLowerSet (((insert c I : Finset (Fin 4 → ℕ))) : Set (Fin 4 → ℕ)) → insert c I ∈ S := by
      intro c hc hl
      refine ⟨⟨hl, ?_⟩, Finset.subset_insert _ _⟩
      rw [Finset.card_insert_of_notMem hc, hIc]
    have axis_mem : ∀ i, insert (Pi.single i (v i)) I ∈ S := by
      intro i
      refine ins_mem _ (single_not i) ?_
      intro a b hba ha
      rw [Finset.coe_insert, Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | ha
      · by_cases hb : b i = v i
        · left
          funext k
          by_cases hk : k = i
          · subst hk; simp [hb]
          · have := hba k
            simp only [Pi.single_eq_of_ne hk] at this ⊢
            omega
        · right
          obtain ⟨c, hcI, hcsup⟩ := Finset.exists_mem_eq_sup I hne fun c => c i
          have hvi : v i = c i + 1 := by
            rw [show v i = (I.sup fun c => c i) + 1 from rfl, hcsup]
          apply hIl _ hcI
          rw [Pi.le_def]
          intro k
          have h1 := Pi.le_def.1 hba k
          by_cases hk : k = i
          · rw [hk] at h1 ⊢
            simp only [Pi.single_eq_same] at h1
            omega
          · simp only [Pi.single_eq_of_ne hk] at h1
            omega
      · exact Or.inr (hIl hba ha)
    refine ⟨v, hvpos, ?_⟩
    by_contra hIbox
    have hdiff : (box v \ I).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro h
      exact hIbox (Finset.Subset.antisymm hsub h)
    obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image (box v \ I) (fun c => ∑ i, c i) hdiff
    have hcbox : c ∈ box v := (Finset.mem_sdiff.1 hc).1
    have hcI : c ∉ I := (Finset.mem_sdiff.1 hc).2
    have hcmem : insert c I ∈ S := by
      refine ins_mem c hcI ?_
      intro a b hba ha
      rw [Finset.coe_insert, Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | ha
      · by_cases hb : b = a
        · exact Or.inl hb
        · right
          by_contra hbI
          have hbbox : b ∈ box v := lower_box v hba hcbox
          have := hmin b (Finset.mem_sdiff.2 ⟨hbbox, hbI⟩)
          have := sum_lt b a (lt_of_le_of_ne hba hb)
          omega
      · exact Or.inr (hIl hba ha)
    have hcne : ∀ i, insert c I ≠ insert (Pi.single i (v i)) I := by
      intro i h
      have := insert_inj I _ _ hcI h
      have := (mem_box v _).1 hcbox i
      subst_vars
      simp at this
    have hsubS : insert (insert c I) (Set.range fun i => insert (Pi.single i (v i)) I) ⊆ S := by
      intro J hJ
      rcases Set.mem_insert_iff.1 hJ with rfl | ⟨i, rfl⟩
      · exact hcmem
      · exact axis_mem i
    have hnotin : insert c I ∉ Set.range fun i => insert (Pi.single i (v i)) I := by
      rintro ⟨i, hi⟩
      exact hcne i hi.symm
    have h5 :
        (insert (insert c I) (Set.range fun i => insert (Pi.single i (v i)) I)).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem hnotin (hfin.subset fun J ⟨i, hi⟩ => hi ▸ axis_mem i),
        Set.ncard_range_of_injective (axis_inj v I hvpos single_not)]
      simp
    have := Set.ncard_le_ncard hsubS hfin
    change _ ≤ extensions n I at this
    omega
  -- Step 3: a positive box has exactly one shrinking, removing its top cell.
  have box_shrink : ∀ (n : ℕ) (v : Fin 4 → ℕ), (∀ i, 0 < v i) → (box v).card = n + 1 →
      {I : Finset (Fin 4 → ℕ) | IsSolidPartition n I ∧ I ⊆ box v} =
        {(box v).erase fun i => v i - 1} := by
    intro n v hv hcard
    set t : Fin 4 → ℕ := fun i => v i - 1 with htdef
    have htbox : t ∈ box v := by
      rw [mem_box]
      intro i
      have := hv i
      simp only [htdef]
      omega
    have le_top : ∀ x ∈ box v, x ≤ t := by
      intro x hx i
      have := (mem_box v x).1 hx i
      simp only [htdef]
      omega
    ext I
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hIl, hIc⟩, hsub⟩
      have htI : t ∉ I := by
        intro htI
        have : box v ⊆ I := fun x hx => hIl (le_top x hx) htI
        have := Finset.card_le_card this
        omega
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => htI (h ▸ hx), hsub hx⟩
      · rw [Finset.card_erase_of_mem htbox, hcard, hIc]
        omega
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, Finset.erase_subset _ _⟩
      · intro a b hba ha
        rw [Finset.mem_coe, Finset.mem_erase] at ha ⊢
        refine ⟨?_, lower_box v hba ha.2⟩
        rintro rfl
        exact ha.1 (le_antisymm (le_top a ha.2) hba)
      · rw [Finset.card_erase_of_mem htbox, hcard]
        omega
  -- Step 4: one shrinking forces a box.
  have shrink_box : ∀ (n : ℕ) (J : Finset (Fin 4 → ℕ)), IsSolidPartition (n + 1) J →
      shrinkings n J = 1 → ∃ v : Fin 4 → ℕ, (∀ i, 0 < v i) ∧ J = box v := by
    intro n J ⟨hJl, hJc⟩ hsh
    have hne : J.Nonempty := Finset.card_pos.1 (by omega)
    set S := {I : Finset (Fin 4 → ℕ) | IsSolidPartition n I ∧ I ⊆ J} with hSdef
    have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by
      change shrinkings n J ≠ 0
      omega)
    -- a cell of `J` with nothing of `J` strictly above it can be removed
    have erase_mem : ∀ m ∈ J, (∀ z ∈ J, m ≤ z → z = m) → J.erase m ∈ S := by
      intro m hm hmax
      refine ⟨⟨?_, ?_⟩, Finset.erase_subset _ _⟩
      · intro a b hba ha
        rw [Finset.mem_coe, Finset.mem_erase] at ha ⊢
        refine ⟨?_, hJl hba ha.2⟩
        rintro rfl
        exact ha.1 (hmax a ha.2 hba)
      · rw [Finset.card_erase_of_mem hm, hJc]
        omega
    -- the maximum of the coordinate sum is such a cell
    have top_of_max : ∀ (T : Finset (Fin 4 → ℕ)) (m : Fin 4 → ℕ), m ∈ T → T ⊆ J →
        (∀ z ∈ T, ∑ i, z i ≤ ∑ i, m i) → (∀ z ∈ J, m ≤ z → z ∈ T) → ∀ z ∈ J, m ≤ z → z = m := by
      intro T m hmT hTJ hmax hup z hz hmz
      by_contra hne
      have := hmax z (hup z hz hmz)
      have := sum_lt m z (lt_of_le_of_ne hmz (Ne.symm hne))
      omega
    obtain ⟨m, hmJ, hmmax⟩ := Finset.exists_max_image J (fun c => ∑ i, c i) hne
    have hmtop := top_of_max J m hmJ (Finset.Subset.refl _) hmmax (fun z hz _ => hz)
    have below_m : ∀ y ∈ J, y ≤ m := by
      intro y hy
      by_contra hym
      have hTne : (J.filter fun z => y ≤ z).Nonempty := ⟨y, Finset.mem_filter.2 ⟨hy, le_refl y⟩⟩
      obtain ⟨m', hm'T, hm'max⟩ :=
        Finset.exists_max_image (J.filter fun z => y ≤ z) (fun c => ∑ i, c i) hTne
      have hm'J : m' ∈ J := (Finset.mem_filter.1 hm'T).1
      have hym' : y ≤ m' := (Finset.mem_filter.1 hm'T).2
      have hm'top := top_of_max _ m' hm'T (Finset.filter_subset _ _) hm'max
        (fun z hz hz' => Finset.mem_filter.2 ⟨hz, le_trans hym' hz'⟩)
      have hdist : m' ≠ m := fun h => hym (h ▸ hym')
      have hpair : ({J.erase m, J.erase m'} : Set (Finset (Fin 4 → ℕ))) ⊆ S := by
        intro I hI
        rcases hI with rfl | rfl
        · exact erase_mem m hmJ hmtop
        · exact erase_mem m' hm'J hm'top
      have hneq : J.erase m ≠ J.erase m' := by
        intro h
        have : m ∈ J.erase m' := Finset.mem_erase.2 ⟨Ne.symm hdist, hmJ⟩
        rw [← h] at this
        simp at this
      have := Set.ncard_le_ncard hpair hfin
      rw [Set.ncard_pair hneq] at this
      change _ ≤ shrinkings n J at this
      omega
    refine ⟨fun i => m i + 1, fun i => Nat.succ_pos _, ?_⟩
    ext x
    rw [mem_box]
    constructor
    · intro hx i
      have := Pi.le_def.1 (below_m x hx) i
      omega
    · intro hx
      exact hJl (fun i => Nat.lt_succ_iff.1 (hx i)) hmJ
  -- counting
  intro n hn
  constructor
  · have hset : {I : Finset (Fin 4 → ℕ) | IsSolidPartition n I ∧ extensions n I = 4} =
        box '' {v : Fin 4 → ℕ | ∏ i, v i = n} := by
      ext I
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hI, hext⟩
        obtain ⟨v, hv, rfl⟩ := ext_box n I hn hI hext
        exact ⟨v, by rw [← card_box]; exact hI.2, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        have hvpos := pos_of_prod v n hn hv
        have hc : (box v).card = n := by rw [card_box, hv]
        refine ⟨⟨lower_box v, hc⟩, ?_⟩
        unfold extensions
        rw [← hc, box_ext v hvpos, Set.ncard_range_of_injective
          (axis_inj v (box v) hvpos (fun i h => by
            have := (mem_box v _).1 h i
            simp at this))]
        simp
    have hinj : Set.InjOn box {v : Fin 4 → ℕ | ∏ i, v i = n} := fun v hv w hw h =>
      box_inj v w (pos_of_prod v n hn hv) (pos_of_prod w n hn hw) h
    unfold a098052FirstColumn tau4
    rw [hset, hinj.ncard_image]
  · have hn1 : 1 ≤ n + 1 := by omega
    have hset : {J : Finset (Fin 4 → ℕ) | IsSolidPartition (n + 1) J ∧ shrinkings n J = 1} =
        box '' {v : Fin 4 → ℕ | ∏ i, v i = n + 1} := by
      ext J
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hJ, hsh⟩
        obtain ⟨v, hv, rfl⟩ := shrink_box n J hJ hsh
        exact ⟨v, by rw [← card_box]; exact hJ.2, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        have hvpos := pos_of_prod v (n + 1) hn1 hv
        have hc : (box v).card = n + 1 := by rw [card_box, hv]
        refine ⟨⟨lower_box v, hc⟩, ?_⟩
        unfold shrinkings
        rw [box_shrink n v hvpos hc, Set.ncard_singleton]
    have hinj : Set.InjOn box {v : Fin 4 → ℕ | ∏ i, v i = n + 1} := fun v hv w hw h =>
      box_inj v w (pos_of_prod v (n + 1) hn1 hv) (pos_of_prod w (n + 1) hn1 hw) h
    unfold a098530FirstColumn tau4
    rw [hset, hinj.ncard_image]

end D5.S3.Combinatorics.SolidPartitionFirstColumn
