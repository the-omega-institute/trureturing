/- GID: D5/S3/Combinatorics/SolidPartitionFirstColumn
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SolidPartitionFirstColumn
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: For every dimension d and n >= 1, the d-dimensional partitions of n with exactly d extensions to a partition of n + 1, and those of n + 1 containing exactly one partition of n, are the boxes, so both are counted by the Piltz function tau_d; d = 4 proves the first-column conjectures of OEIS A098052 and A098530 (Wouter Meeussen, 2004) on solid partitions. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: a finite lower set of `ℕ^d` with
  exactly `d` extensions (`ext_box`), or with exactly one shrinking (`shrink_box`), is a box. The
  extensions of a box are its `d` axis cells (`box_ext`); a non-box has a further extension, a
  minimal cell of its bounding box outside it; a non-box has two maximal cells, a maximal cell and
  a maximal cell above any cell not below it; boxes of `n` cells correspond to ordered
  factorizations of `n` into `d` factors (`box_inj`, `card_box`)
admission_basis: escape-witness (issue #10404)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SolidPartitionFirstColumn

/-- A `d`-dimensional partition of `n`, read as its Ferrers diagram: a finite lower set of `n` cells
of `ℕ^d` in the coordinatewise order (`d = 4` gives the solid partitions of A000293). -/
def IsSolidPartition {d : ℕ} (n : ℕ) (I : Finset (Fin d → ℕ)) : Prop :=
  IsLowerSet (I : Set (Fin d → ℕ)) ∧ I.card = n

/-- The number of `d`-dimensional partitions of `n + 1` that contain `I`. -/
noncomputable def extensions {d : ℕ} (n : ℕ) (I : Finset (Fin d → ℕ)) : ℕ :=
  {J : Finset (Fin d → ℕ) | IsSolidPartition (n + 1) J ∧ I ⊆ J}.ncard

/-- The number of `d`-dimensional partitions of `n` contained in `J`. -/
noncomputable def shrinkings {d : ℕ} (n : ℕ) (J : Finset (Fin d → ℕ)) : ℕ :=
  {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ I ⊆ J}.ncard

/-- The `d`-dimensional partitions of `n` that extend in exactly `d` ways; for `d = 4` the first
column of A098052. -/
noncomputable def firstColumn (d n : ℕ) : ℕ :=
  {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ extensions n I = d}.ncard

/-- The `d`-dimensional partitions of `n + 1` that shrink in exactly one way; for `d = 4` the first
column of A098530. -/
noncomputable def shrinkColumn (d n : ℕ) : ℕ :=
  {J : Finset (Fin d → ℕ) | IsSolidPartition (n + 1) J ∧ shrinkings n J = 1}.ncard

/-- The number of ordered factorizations of `n` into `d` factors (the Piltz function; A007426 for
`d = 4`). -/
noncomputable def tau (d n : ℕ) : ℕ :=
  {v : Fin d → ℕ | ∏ i, v i = n}.ncard

/-- The first-column conjectures of A098052 and A098530, in every dimension `d`. -/
def claim : Prop :=
  ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → firstColumn d n = tau d n ∧ shrinkColumn d n = tau d (n + 1)

/-- The box `∏ [0, v i)`. -/
private def box {d : ℕ} (v : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (v i)

theorem result : claim := by
  intro d n hd hn
  classical
  have mem_box : ∀ (v c : Fin d → ℕ), c ∈ box v ↔ ∀ i, c i < v i := by
    intro v c
    simp [box, Fintype.mem_piFinset]
  have card_box : ∀ v : Fin d → ℕ, (box v).card = ∏ i, v i := by
    intro v
    simp [box, Fintype.card_piFinset]
  have lower_box :
      ∀ v : Fin d → ℕ, IsLowerSet ((box v : Finset (Fin d → ℕ)) : Set (Fin d → ℕ)) := by
    intro v a b hba ha
    rw [Finset.mem_coe, mem_box] at ha ⊢
    exact fun i => lt_of_le_of_lt (hba i) (ha i)
  have pos_of_prod : ∀ (v : Fin d → ℕ) (n : ℕ), 1 ≤ n → ∏ i, v i = n → ∀ i, 0 < v i :=
    fun v n hn hv i =>
      Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.1 (by omega) i (Finset.mem_univ i))
  -- a positive box is determined by its cells
  have box_inj : ∀ v w : Fin d → ℕ, (∀ i, 0 < v i) → (∀ i, 0 < w i) → box v = box w → v = w := by
    intro v w hv hw h
    funext i
    have heval := congrArg (fun s : Finset (Fin d → ℕ) => s.image (fun f => f i)) h
    simp only [box] at heval
    rw [Fintype.eval_image_piFinset _ i (fun j _ => Finset.nonempty_range_iff.2 (hv j).ne'),
      Fintype.eval_image_piFinset _ i (fun j _ => Finset.nonempty_range_iff.2 (hw j).ne')] at heval
    exact Finset.strictMono_range.injective heval
  -- Step 1: a positive box has exactly the d extensions at the axis cells.
  have box_ext : ∀ v : Fin d → ℕ, (∀ i, 0 < v i) →
      {J : Finset (Fin d → ℕ) | IsSolidPartition ((box v).card + 1) J ∧ box v ⊆ J} =
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
      obtain ⟨c, hcb, hins⟩ := Finset.exists_eq_insert_iff.2 ⟨hsub, hJc.symm⟩
      have hJeq : J = insert c (box v) := hins.symm
      have hcJ : c ∈ J := hJeq ▸ Finset.mem_insert_self c (box v)
      -- every cell strictly below `c` lies in the box
      have below : ∀ y : Fin d → ℕ, y ≤ c → y ≠ c → y ∈ box v := by
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
        have hy := below (Function.update c i 0) (update_le_self_iff.2 (Nat.zero_le _))
          (Function.update_ne_self_iff.2 (Ne.symm hci))
        have := (mem_box v _).1 hy j
        rw [Function.update_of_ne (Ne.symm hij)] at this
        omega
      have eq_j : c j = v j := by
        by_contra hne
        have hlt : v j < c j := lt_of_le_of_ne hj (Ne.symm hne)
        have hy := below (Function.update c j (v j)) (update_le_self_iff.2 hj)
          (Function.update_ne_self_iff.2 (fun h => hne h.symm))
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
  -- the d axis extensions are distinct
  have axis_inj : ∀ (v : Fin d → ℕ) (I : Finset (Fin d → ℕ)), (∀ i, 0 < v i) →
      (∀ i, Pi.single i (v i) ∉ I) → Function.Injective fun i => insert (Pi.single i (v i)) I := by
    intro v I hv hnot i j h
    exact DFinsupp.single_left_injective (fun k => (hv k).ne')
      (DFunLike.coe_injective ((Finset.insert_inj (hnot i)).1 h))
  -- Step 2: d extensions force a box.
  have ext_box : ∀ (n : ℕ) (I : Finset (Fin d → ℕ)), 1 ≤ n → IsSolidPartition n I →
      extensions n I = d → ∃ v : Fin d → ℕ, (∀ i, 0 < v i) ∧ I = box v := by
    intro n I hn ⟨hIl, hIc⟩ hext
    have hne : I.Nonempty := Finset.card_pos.1 (by omega)
    set v : Fin d → ℕ := fun i => (I.sup fun c => c i) + 1 with hvdef
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
    set S := {J : Finset (Fin d → ℕ) | IsSolidPartition (n + 1) J ∧ I ⊆ J} with hSdef
    have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by
      change extensions n I ≠ 0
      omega)
    have ins_mem : ∀ c : Fin d → ℕ, c ∉ I →
        IsLowerSet (((insert c I : Finset (Fin d → ℕ))) : Set (Fin d → ℕ)) → insert c I ∈ S := by
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
    obtain ⟨c, hc⟩ := Finset.exists_minimal hdiff
    have hcbox : c ∈ box v := (Finset.mem_sdiff.1 hc.1).1
    have hcI : c ∉ I := (Finset.mem_sdiff.1 hc.1).2
    have hcmem : insert c I ∈ S := by
      refine ins_mem c hcI ?_
      intro a b hba ha
      rw [Finset.coe_insert, Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | ha
      · by_cases hbI : b ∈ I
        · exact Or.inr hbI
        · exact Or.inl (le_antisymm hba
            (hc.2 (Finset.mem_sdiff.2 ⟨lower_box v hba hcbox, hbI⟩) hba))
      · exact Or.inr (hIl hba ha)
    have hcne : ∀ i, insert c I ≠ insert (Pi.single i (v i)) I := by
      intro i h
      have := (Finset.insert_inj hcI).1 h
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
        (insert (insert c I) (Set.range fun i => insert (Pi.single i (v i)) I)).ncard = d + 1 := by
      rw [Set.ncard_insert_of_notMem hnotin (hfin.subset fun J ⟨i, hi⟩ => hi ▸ axis_mem i),
        Set.ncard_range_of_injective (axis_inj v I hvpos single_not)]
      simp
    have := Set.ncard_le_ncard hsubS hfin
    change _ ≤ extensions n I at this
    omega
  -- Step 3: a positive box has exactly one shrinking, removing its top cell.
  have box_shrink : ∀ (n : ℕ) (v : Fin d → ℕ), (∀ i, 0 < v i) → (box v).card = n + 1 →
      {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ I ⊆ box v} =
        {(box v).erase fun i => v i - 1} := by
    intro n v hv hcard
    set t : Fin d → ℕ := fun i => v i - 1 with htdef
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
      apply Finset.eq_of_subset_of_card_le (Finset.subset_erase.2 ⟨hsub, htI⟩)
      rw [Finset.card_erase_of_mem htbox, hcard, hIc]
      omega
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, Finset.erase_subset _ _⟩
      · rw [Finset.coe_erase]
        exact (lower_box v).erase fun b hb htb => le_antisymm (le_top b hb) htb
      · rw [Finset.card_erase_of_mem htbox, hcard]
        omega
  -- Step 4: one shrinking forces a box.
  have shrink_box : ∀ (n : ℕ) (J : Finset (Fin d → ℕ)), IsSolidPartition (n + 1) J →
      shrinkings n J = 1 → ∃ v : Fin d → ℕ, (∀ i, 0 < v i) ∧ J = box v := by
    intro n J ⟨hJl, hJc⟩ hsh
    have hne : J.Nonempty := Finset.card_pos.1 (by omega)
    set S := {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ I ⊆ J} with hSdef
    have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by
      change shrinkings n J ≠ 0
      omega)
    -- a maximal cell of `J` can be removed
    have erase_mem : ∀ m, Maximal (· ∈ J) m → J.erase m ∈ S := by
      intro m hm
      refine ⟨⟨?_, ?_⟩, Finset.erase_subset _ _⟩
      · rw [Finset.coe_erase]
        exact hJl.erase fun z hz hmz => le_antisymm (hm.2 hz hmz) hmz
      · rw [Finset.card_erase_of_mem hm.1, hJc]
        omega
    obtain ⟨m, hm⟩ := Finset.exists_maximal hne
    have below_m : ∀ y ∈ J, y ≤ m := by
      intro y hy
      by_contra hym
      obtain ⟨m', hym', hm'⟩ := J.exists_le_maximal hy
      have hdist : m' ≠ m := fun h => hym (h ▸ hym')
      have hpair : ({J.erase m, J.erase m'} : Set (Finset (Fin d → ℕ))) ⊆ S := by
        intro I hI
        rcases hI with rfl | rfl
        · exact erase_mem m hm
        · exact erase_mem m' hm'
      have hneq : J.erase m ≠ J.erase m' := fun h => hdist ((Finset.erase_inj J hm.1).1 h).symm
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
      exact hJl (fun i => Nat.lt_succ_iff.1 (hx i)) hm.1
  -- counting
  constructor
  · have hset : {I : Finset (Fin d → ℕ) | IsSolidPartition n I ∧ extensions n I = d} =
        box '' {v : Fin d → ℕ | ∏ i, v i = n} := by
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
    have hinj : Set.InjOn box {v : Fin d → ℕ | ∏ i, v i = n} := fun v hv w hw h =>
      box_inj v w (pos_of_prod v n hn hv) (pos_of_prod w n hn hw) h
    unfold firstColumn tau
    rw [hset, hinj.ncard_image]
  · have hn1 : 1 ≤ n + 1 := by omega
    have hset : {J : Finset (Fin d → ℕ) | IsSolidPartition (n + 1) J ∧ shrinkings n J = 1} =
        box '' {v : Fin d → ℕ | ∏ i, v i = n + 1} := by
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
    have hinj : Set.InjOn box {v : Fin d → ℕ | ∏ i, v i = n + 1} := fun v hv w hw h =>
      box_inj v w (pos_of_prod v (n + 1) hn1 hv) (pos_of_prod w (n + 1) hn1 hw) h
    unfold shrinkColumn tau
    rw [hset, hinj.ncard_image]

end D5.S3.Combinatorics.SolidPartitionFirstColumn
