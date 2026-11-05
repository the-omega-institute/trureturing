/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualityOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualityOrder
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual frozen-cut signs separate distinct maximum slabs by a minimum slab. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraSlabRunBound
import all D5.S3.Combinatorics.Geometry.MiuraSlabSigns
import all D5.S3.Combinatorics.Geometry.MiuraSlabClassification

/-! Order constraints use actual occupied intervals and signed frozen cuts. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualityOrder
open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema MiuraSlabNeutral
open MiuraSlabIncidence MiuraSlabClassification MiuraSlabSigns MiuraSlabFrozen MiuraSlabCover
variable {m n : ℕ}

private theorem slab_order {h : Cell m n → ℤ} {I J : Interval m}
    (hI : IsRowSlab h I) (hJ : IsRowSlab h J) (hne : I ≠ J) :
    I.last.val < J.first.val ∨ J.last.val < I.first.val := by
  by_cases hf : I.first.val ≤ J.first.val
  · left
    by_contra hnot
    have hjI : I.Contains J.first := by change I.first.val ≤ J.first.val ∧ J.first.val ≤ I.last.val; omega
    exact hne (row_slab_unique hI hJ J.first hjI ⟨le_rfl, J.ordered⟩)
  · right
    by_contra hnot
    have hiJ : J.Contains I.first := by change J.first.val ≤ I.first.val ∧ I.first.val ≤ J.last.val; omega
    exact hne (row_slab_unique hI hJ I.first ⟨le_rfl, I.ordered⟩ hiJ)

private theorem signed_gap_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (f g : Fin m)
    (hf : ¬ RowOccupied h f) (hg : ¬ RowOccupied h g) (hfg : f < g)
    (hgap : ∀ i : Fin m, f < i → i < g → RowOccupied h i)
    (hsf : slope h hn f = -1) (hsg : slope h hn g = 1) :
    ∃ I ∈ minRowSlabs h, f.val < I.first.val ∧ I.last.val < g.val := by
  classical
  obtain ⟨hf0, hf1⟩ := frozen_internal hh hm hn f hf
  obtain ⟨hg0, hg1⟩ := frozen_internal hh hm hn g hg
  have hspace : f.val + 1 < g.val := by
    have he1 := (frozen_cuts hh hm hn f hf).2.2 hf1 ⟨0, hn⟩
    have he2 := (frozen_cuts hh hm hn g hg).2.1 ⟨0, hn⟩
    rw [hsf] at he1
    rw [hsg] at he2
    by_contra hnot
    have hnext : (⟨f.val + 1, hf1⟩ : Fin m) = g := Fin.ext (by change f.val + 1 = g.val; omega)
    have hprev : (⟨g.val - 1, by omega⟩ : Fin m) = f := Fin.ext (by change g.val - 1 = f.val; omega)
    rw [hnext] at he1
    rw [hprev] at he2
    have hfgv : f.val < g.val := hfg
    omega
  let I : Interval m := ⟨⟨f.val + 1, hf1⟩, ⟨g.val - 1, by omega⟩, by
    change f.val + 1 ≤ g.val - 1; omega⟩
  have hI : IsRowSlab h I := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      change f.val + 1 ≤ i.val ∧ i.val ≤ g.val - 1 at hi
      exact hgap i (by change f.val < i.val; omega) (by change i.val < g.val; omega)
    · intro k hk
      have he : k = f := Fin.ext (by change k.val + 1 = f.val + 1 at hk; omega)
      exact he.symm ▸ hf
    · intro k hk
      have he : k = g := Fin.ext (by change g.val - 1 + 1 = k.val at hk; omega)
      exact he.symm ▸ hg
  have hout : RowOutward h I 1 := outward_of_cuts I 1 (by
    intro ht j
    have he := (frozen_cuts hh hm hn f hf).2.2 hf1 j
    rw [hsf] at he
    have hprev : (⟨I.first.val - 1, by omega⟩ : Fin m) = f := Fin.ext (by change f.val + 1 - 1 = f.val; omega)
    rw [hprev]
    change h (f, j) = h (⟨f.val + 1, hf1⟩, j) + 1
    omega) (by
    intro hb j
    have he := (frozen_cuts hh hm hn g hg).2.1 j
    rw [hsg] at he
    have hnext : (⟨I.last.val + 1, hb⟩ : Fin m) = g := Fin.ext (by change g.val - 1 + 1 = g.val; omega)
    have hprev : (⟨g.val - 1, by omega⟩ : Fin m) = I.last := rfl
    rw [hnext]
    exact he)
  refine ⟨I, ?_, ?_, ?_⟩
  · simp only [minRowSlabs, rowSlabs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hI, Or.inl (by change 0 < f.val + 1; omega), hout⟩
  · change f.val < f.val + 1; omega
  · change g.val - 1 < g.val; omega

/-- Two ordered actual maximum row slabs have an actual minimum row slab
strictly between them. The sign change is selected from genuinely frozen rows. -/
theorem minimum_slab_between_maximum_slabs {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (A B : Interval m)
    (hA : A ∈ maxRowSlabs h) (hB : B ∈ maxRowSlabs h)
    (hAB : A.last.val < B.first.val) :
    ∃ I ∈ minRowSlabs h, A.last.val < I.first.val ∧ I.last.val < B.first.val := by
  classical
  have hsA := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
  have hsB := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2
  have ha1 : A.last.val + 1 < m := by have := B.first.isLt; omega
  let a : Fin m := ⟨A.last.val + 1, ha1⟩
  have ha : ¬ RowOccupied h a := hsA.2.2 a rfl
  have hspace : A.last.val + 1 < B.first.val := by
    by_contra hnot
    have he : a = B.first := Fin.ext (by change A.last.val + 1 = B.first.val; omega)
    exact ha (he.symm ▸ hsB.1 B.first ⟨le_rfl, B.ordered⟩)
  let b : Fin m := ⟨B.first.val - 1, by have := B.first.isLt; omega⟩
  have hb : ¬ RowOccupied h b := hsB.2.1 b (by dsimp [b]; omega)
  have hsa : slope h hn a = -1 := by
    have hc := (frozen_cuts hh hm hn a ha).2.1 ⟨0, hn⟩
    have he := (Finset.mem_filter.mp hA).2.2 (A.last, ⟨0, hn⟩) (a, ⟨0, hn⟩)
      ⟨A.ordered, le_rfl⟩ (by change ¬ (A.first.val ≤ A.last.val + 1 ∧ A.last.val + 1 ≤ A.last.val); omega)
      (by simp only [adj, gdist, a]; omega)
    have hp : (⟨a.val - 1, by have := a.isLt; omega⟩ : Fin m) = A.last := Fin.ext (by simp [a])
    rw [hp] at hc
    omega
  have hsb : slope h hn b = 1 := by
    have hb1 : b.val + 1 < m := by dsimp [b]; have := B.first.isLt; omega
    have hc := (frozen_cuts hh hm hn b hb).2.2 hb1 ⟨0, hn⟩
    have he := (Finset.mem_filter.mp hB).2.2 (B.first, ⟨0, hn⟩) (b, ⟨0, hn⟩)
      ⟨le_rfl, B.ordered⟩ (by change ¬ (B.first.val ≤ B.first.val - 1 ∧ B.first.val - 1 ≤ B.last.val); omega)
      (by simp only [adj, gdist, b]; omega)
    have hp : (⟨b.val + 1, hb1⟩ : Fin m) = B.first := Fin.ext (by dsimp [b]; omega)
    rw [hp] at hc
    omega
  have hab : a.val ≤ b.val := by dsimp [a,b]; omega
  let P := Finset.univ.filter (fun i : Fin m => ¬ RowOccupied h i ∧ a ≤ i ∧ i ≤ b ∧ slope h hn i = 1)
  have hbP : b ∈ P := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hb, hab, le_rfl, hsb⟩
  let g := P.min' ⟨b, hbP⟩
  have hgP : g ∈ P := Finset.min'_mem P ⟨b, hbP⟩
  have hg' := (Finset.mem_filter.mp hgP).2
  have hag : a < g := by
    have haEq : a ≠ g := by
      intro he
      have hs := hg'.2.2.2
      rw [← he] at hs
      omega
    exact lt_of_le_of_ne hg'.2.1 haEq
  let L := Finset.univ.filter (fun i : Fin m => ¬ RowOccupied h i ∧ a ≤ i ∧ i < g)
  have haL : a ∈ L := by simp [L, ha, hag]
  let f := L.max' ⟨a, haL⟩
  have hfL : f ∈ L := Finset.max'_mem L ⟨a, haL⟩
  have hf' := (Finset.mem_filter.mp hfL).2
  have hsf : slope h hn f = -1 := by
    rcases (frozen_cuts hh hm hn f hf'.1).1 with he | he
    · have hfP : f ∈ P := by
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hf'.1, hf'.2.1, le_trans (le_of_lt hf'.2.2) hg'.2.2.1, he⟩
      have hle := Finset.min'_le P f hfP
      exact (not_le_of_gt hf'.2.2 hle).elim
    · exact he
  obtain ⟨I, hI, hIf, hIg⟩ := signed_gap_minimum hh hm hn f g hf'.1 hg'.1 hf'.2.2 (by
    intro i hfi hig
    by_contra hi
    have hiL : i ∈ L := by
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hi, le_trans hf'.2.1 (le_of_lt hfi), hig⟩
    have hle := Finset.le_max' L i hiL
    exact (not_le_of_gt hfi hle)) hsf hg'.2.2.2
  refine ⟨I, hI, ?_, ?_⟩
  · have haf : a.val ≤ f.val := hf'.2.1
    dsimp [a] at haf
    omega
  · have hgb : g.val ≤ b.val := hg'.2.2.1
    dsimp [b] at hgb
    omega

/-- A unique minimum row slab and at least two maximum row slabs force both
physical boundary slabs to be maximum type. -/
theorem boundary_maximum_slabs {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hf : ∃ i, ¬ RowOccupied h i)
    (hmin : (minRowSlabs h).card = 1) (hmax : 2 ≤ (maxRowSlabs h).card) :
    ∃ I ∈ maxRowSlabs h, ∃ J ∈ maxRowSlabs h,
      I.Contains ⟨0, by omega⟩ ∧ J.Contains ⟨m - 1, by omega⟩ := by
  classical
  obtain ⟨A, hA, B, hB, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (maxRowSlabs h).card)
  have hsA := (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2
  have hsB := (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).2
  have hmiddle : ∃ K ∈ minRowSlabs h, 0 < K.first.val ∧ K.last.val + 1 < m := by
    rcases slab_order hsA hsB hne with hab | hba
    · obtain ⟨K, hK, hk0, hk1⟩ := minimum_slab_between_maximum_slabs hh hm hn A B hA hB hab
      exact ⟨K, hK, by omega, by have := B.first.isLt; omega⟩
    · obtain ⟨K, hK, hk0, hk1⟩ := minimum_slab_between_maximum_slabs hh hm hn B A hB hA hba
      exact ⟨K, hK, by omega, by have := A.first.isLt; omega⟩
  obtain ⟨K, hK, hK0, hK1⟩ := hmiddle
  obtain ⟨I, ht, hIs⟩ := occupied_row_has_slab h ⟨0, by omega⟩ (boundary_rows_occupied hh hm hn).1
  obtain ⟨J, hb, hJs⟩ := occupied_row_has_slab h ⟨m - 1, by omega⟩ (boundary_rows_occupied hh hm hn).2
  have hI : I ∈ maxRowSlabs h := by
    rcases row_slab_classification hh hm hn hf I hIs with hi | hi | hi
    · have he : I = K := Finset.card_le_one_iff.mp (by omega : (minRowSlabs h).card ≤ 1) hi hK
      subst I
      change K.first.val ≤ 0 ∧ 0 ≤ K.last.val at ht
      omega
    · exact hi
    · obtain ⟨_, s, hs, hi0, _⟩ := Finset.mem_filter.mp hi
      change I.first.val ≤ 0 ∧ 0 ≤ I.last.val at ht
      omega
  have hJ : J ∈ maxRowSlabs h := by
    rcases row_slab_classification hh hm hn hf J hJs with hj | hj | hj
    · have he : J = K := Finset.card_le_one_iff.mp (by omega : (minRowSlabs h).card ≤ 1) hj hK
      subst J
      change K.first.val ≤ m - 1 ∧ m - 1 ≤ K.last.val at hb
      omega
    · exact hj
    · obtain ⟨_, s, hs, hj0, hj1, _⟩ := Finset.mem_filter.mp hj
      change J.first.val ≤ m - 1 ∧ m - 1 ≤ J.last.val at hb
      omega
  exact ⟨I, hI, J, hJ, ht, hb⟩
/-- When there is one minimum row slab there are at most two maximum row
slabs, using a genuine minimum slab between every two ordered maxima. -/
theorem one_minimum_slab_maximum_card_le_two {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) (hmin : (minRowSlabs h).card = 1) :
    (maxRowSlabs h).card ≤ 2 := by
  classical
  obtain ⟨I, hIset⟩ := Finset.card_eq_one.mp hmin
  let f : ↥(maxRowSlabs h) → Bool := fun A => decide (A.val.last.val < I.first.val)
  have hdist (A B : ↥(maxRowSlabs h)) (hab : A.val.last.val < B.val.first.val) : f A ≠ f B := by
    obtain ⟨K, hK, hak, hkb⟩ := minimum_slab_between_maximum_slabs hh hm hn A.val B.val
      A.property B.property hab
    have hKI : K = I := Finset.mem_singleton.mp (hIset ▸ hK)
    subst K
    have hIa : A.val.last.val < I.first.val := hak
    have hIb : ¬ B.val.last.val < I.first.val := by
      have ho := B.val.ordered
      change B.val.first.val ≤ B.val.last.val at ho
      have hi := I.ordered
      change I.first.val ≤ I.last.val at hi
      omega
    simp only [f, hIa, hIb, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]
  have hinj : Function.Injective f := by
    intro A B he
    by_contra hne
    have hne' : A.val ≠ B.val := fun hv => hne (Subtype.ext hv)
    rcases slab_order (Finset.mem_filter.mp (Finset.mem_filter.mp A.property).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp B.property).1).2 hne' with hab | hba
    · exact hdist A B hab he
    · exact hdist B A hba he.symm
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe, Fintype.card_bool] using hc

end D5.S3.Combinatorics.Geometry.MiuraEqualityOrder
