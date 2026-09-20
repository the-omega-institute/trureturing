/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual odd crown blocks have a one-vertex parity majority and are extremal. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCyclePartitions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope


/-- Actual vertices of the specified parity in an actual quotient block. -/
noncomputable def crownBlockParityVertices {n : ℕ}
    (P : ConnectedCyclePartition (2 * n)) (C : Quotient P.toSetoid) (p : ℕ) :
    Finset (Fin (2 * n)) := by
  classical
  exact Finset.univ.filter fun v => Quotient.mk'' v = C ∧ v.val % 2 = p

/-- In an actual connected odd block the two parity counts differ by one.
    A lower majority excludes incoming edges from other blocks; an upper majority
    excludes outgoing edges to other blocks. No orientation is assumed. -/
theorem crownOddBlock_geometry {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n)) (C : Quotient P.toSetoid)
    (hodd : Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1) :
    let E := (crownBlockParityVertices P C 0).card
    let O := (crownBlockParityVertices P C 1).card
    (E = O + 1 ∨ O = E + 1) ∧
      (O < E → ∀ D, crownCycleBlockRel P D C → D = C) ∧
      (E < O → ∀ D, crownCycleBlockRel P C D → D = C) := by
  have crownCycleBlockRel_iff_boundaryCut {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
      (P : ConnectedCyclePartition (2 * n)) (C D : Quotient P.toSetoid) (hne : C ≠ D) :
      crownCycleBlockRel P C D ↔
        ∃ i j : Fin (2 * n),
          Quotient.mk'' i = C ∧ Quotient.mk'' j = D ∧ crownRelation n i j ∧
            ((i ∈ cycleBoundaryCuts P ∧ j = i + 1) ∨
              (j ∈ cycleBoundaryCuts P ∧ i = j + 1)) := by
    constructor
    · rintro ⟨i, j, hi, hj, hij⟩
      have hnrel : ¬ P.toSetoid.r i j := by
        intro hrel
        apply hne
        rw [← hi, ← hj]
        exact Quotient.sound hrel
      refine ⟨i, j, hi, hj, hij, ?_⟩
      rcases hij.2 with hnext | hprev
      · left
        have hsucc : j = i + 1 := by
          apply Fin.ext
          simpa [Fin.add_def] using hnext
        refine ⟨?_, hsucc⟩
        simpa [cycleBoundaryCuts, hsucc] using hnrel
      · right
        have hpred : i = j + 1 := by
          apply Fin.ext
          simp only [Fin.add_def, Fin.val_one',
            Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
          by_cases hi0 : i.val = 0
          · rw [hi0, zero_add, Nat.mod_eq_of_lt (by omega)] at hprev
            rw [hprev, show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
            exact hi0
          · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi0
            have hform : i.val + 2 * n - 1 = (i.val - 1) + 2 * n := by omega
            have himod : ((i.val - 1) + 2 * n) % (2 * n) = i.val - 1 := by
              rw [Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hform, himod] at hprev
            rw [hprev, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]
        refine ⟨?_, hpred⟩
        simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hpred]
        exact fun hji => hnrel (P.toSetoid.symm hji)
    · rintro ⟨i, j, hi, hj, hij, _⟩
      exact ⟨i, j, hi, hj, hij⟩
  classical
  dsimp only
  let V := crownBlockParityVertices P C
  have hmem (v : Fin (2 * n)) (p : ℕ) :
      v ∈ V p ↔ (Quotient.mk'' v : Quotient P.toSetoid) = C ∧ v.val % 2 = p := by
    simp [V, crownBlockParityVertices]
  have hboundary :
      (∀ a ∈ cycleBoundaryCuts P, ∀ b ∈ cycleBoundaryCuts P,
        (Quotient.mk'' a : Quotient P.toSetoid) = C → Quotient.mk'' b = C → a = b) ∧
      (∀ a ∈ cycleBoundaryCuts P, ∀ b ∈ cycleBoundaryCuts P,
        (Quotient.mk'' (a + 1) : Quotient P.toSetoid) = C →
          Quotient.mk'' (b + 1) = C → a = b) := by
    let N := 2 * n
    have hN : 3 ≤ N := by dsimp [N]; omega
    have hexit (a b : Fin N) (ha : a ∈ cycleBoundaryCuts P)
        (hb : b ∈ cycleBoundaryCuts P) (hab : a < b)
        (hrel : P.toSetoid.r a b) : False := by
      have h := cyclePartitionBlock_arc_constant hN P a b hab ha hb a b hrel
      have habv : a.val < b.val := hab
      simp only [lt_self_iff_false, false_and, le_refl, and_true] at h
      exact h.mpr habv
    have hentry (a b : Fin N) (ha : a ∈ cycleBoundaryCuts P)
        (hb : b ∈ cycleBoundaryCuts P) (hab : a < b)
        (hrel : P.toSetoid.r (a + 1) (b + 1)) : False := by
      have h := cyclePartitionBlock_arc_constant hN P a b hab ha hb (a + 1) (b + 1) hrel
      have haVal : (a + 1).val = a.val + 1 := by
        simp [Fin.add_def, Nat.mod_eq_of_lt (show a.val + 1 < N by omega)]
      have hbVal : (b + 1).val = (b.val + 1) % N := by simp [Fin.add_def]
      rw [haVal, hbVal] at h
      have hleft : a.val < a.val + 1 ∧ a.val + 1 ≤ b.val := by
        have : a.val < b.val := hab
        omega
      have hright := h.mp hleft
      by_cases hbLast : b.val + 1 < N
      · rw [Nat.mod_eq_of_lt hbLast] at hright
        omega
      · have : b.val + 1 = N := by omega
        rw [this, Nat.mod_self] at hright
        omega
    constructor
    · intro a ha b hb haC hbC
      rcases lt_trichotomy a b with hab | hab | hab
      · exact (hexit a b ha hb hab (Quotient.exact (haC.trans hbC.symm))).elim
      · exact hab
      · exact (hexit b a hb ha hab (Quotient.exact (hbC.trans haC.symm))).elim
    · intro a ha b hb haC hbC
      rcases lt_trichotomy a b with hab | hab | hab
      · exact (hentry a b ha hb hab (Quotient.exact (haC.trans hbC.symm))).elim
      · exact hab
      · exact (hentry b a hb ha hab (Quotient.exact (hbC.trans haC.symm))).elim
  obtain ⟨hexit, hentry⟩ := hboundary
  have hsucc (v : Fin (2 * n)) : (v + 1).val % 2 = (v.val + 1) % 2 := by
    simp only [Fin.add_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
    exact Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * n)
  have hpred (v : Fin (2 * n)) : (v - 1).val % 2 ≠ v.val % 2 := by
    have h := hsucc (v - 1)
    rw [sub_add_cancel] at h
    omega
  have huncut (v : Fin (2 * n)) (hv : v ∉ cycleBoundaryCuts P) :
      P.toSetoid.r v (v + 1) := by
    simpa [cycleBoundaryCuts] using hv
  have hbound (p q : ℕ) (hpq : p + q = 1) : (V p).card ≤ (V q).card + 1 := by
    let bad := (V p).filter fun v => v ∈ cycleBoundaryCuts P
    have hbad : bad.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact hexit a ha'.2 b hb'.2 ((hmem a p).mp ha'.1).1 ((hmem b p).mp hb'.1).1
    have hgood : ((V p) \ bad).card ≤ (V q).card := by
      apply Finset.card_le_card_of_injOn (fun v : Fin (2 * n) => v + 1)
      · intro v hv
        obtain ⟨hv, hvbad⟩ := Finset.mem_sdiff.mp hv
        obtain ⟨hvC, hvp⟩ := (hmem v p).mp hv
        have hvcut : v ∉ cycleBoundaryCuts P := by
          intro h
          exact hvbad (Finset.mem_filter.mpr ⟨hv, h⟩)
        apply (hmem (v + 1) q).mpr
        refine ⟨(Quotient.sound (huncut v hvcut)).symm.trans hvC, ?_⟩
        rw [hsucc]
        omega
      · intro a _ b _ hab
        exact add_right_cancel hab
    have hcard := Finset.card_le_card_sdiff_add_card (s := V p) (t := bad)
    omega
  have hend (p q : ℕ) (hpq : p + q = 1) (c : Fin (2 * n))
      (hc : c ∈ cycleBoundaryCuts P) :
      ((Quotient.mk'' c : Quotient P.toSetoid) = C ∧ c.val % 2 = q →
        (V p).card ≤ (V q).card) ∧
      ((Quotient.mk'' (c + 1) : Quotient P.toSetoid) = C ∧ (c + 1).val % 2 = q →
        (V p).card ≤ (V q).card) := by
    constructor
    · rintro ⟨hcC, hcq⟩
      apply Finset.card_le_card_of_injOn (fun v : Fin (2 * n) => v + 1)
      · intro v hv
        obtain ⟨hvC, hvp⟩ := (hmem v p).mp hv
        have hvcut : v ∉ cycleBoundaryCuts P := by
          intro h
          have heq := hexit v h c hc hvC hcC
          subst v
          omega
        apply (hmem (v + 1) q).mpr
        refine ⟨(Quotient.sound (huncut v hvcut)).symm.trans hvC, ?_⟩
        rw [hsucc]
        omega
      · intro a _ b _ hab
        exact add_right_cancel hab
    · rintro ⟨hcC, hcq⟩
      apply Finset.card_le_card_of_injOn (fun v : Fin (2 * n) => v - 1)
      · intro v hv
        obtain ⟨hvC, hvp⟩ := (hmem v p).mp hv
        have hvcut : v - 1 ∉ cycleBoundaryCuts P := by
          intro h
          have heq := hentry (v - 1) h c hc (by simpa using hvC) hcC
          have heq' : v = c + 1 := by rw [← heq, sub_add_cancel]
          rw [heq'] at hvp
          omega
        apply (hmem (v - 1) q).mpr
        refine ⟨?_, ?_⟩
        · have hrel := Quotient.sound (huncut (v - 1) hvcut)
          rw [sub_add_cancel] at hrel
          exact hrel.trans hvC
        · have h := hpred v
          have := Nat.mod_lt (v - 1).val (by omega : 0 < 2)
          omega
      · intro a _ b _ hab
        have h := congrArg (fun x : Fin (2 * n) => x + 1) hab
        simpa only [sub_add_cancel] using h
  have hsum : (V 0).card + (V 1).card =
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} := by
    have hdis : Disjoint (V 0) (V 1) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      have := ((hmem v 0).mp hv).2
      have := ((hmem v 1).mp hw).2
      omega
    rw [← Finset.card_union_of_disjoint hdis, Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp only [Finset.mem_union, hmem, Set.mem_toFinset, Set.mem_ofPred_eq]
    have := Nat.mod_lt v.val (by omega : 0 < 2)
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hp : v.val % 2 = 0
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, by omega⟩
  have hbalance : (V 0).card = (V 1).card + 1 ∨ (V 1).card = (V 0).card + 1 := by
    have h0 := hbound 0 1 rfl
    have h1 := hbound 1 0 rfl
    rw [← hsum] at hodd
    omega
  refine ⟨hbalance, ?_, ?_⟩
  · intro hmajor D hDC
    change (V 1).card < (V 0).card at hmajor
    by_contra hne
    obtain ⟨i, j, hi, hj, hij, hcut⟩ :=
      (crownCycleBlockRel_iff_boundaryCut hn P D C hne).mp hDC
    have hjodd : j.val % 2 = 1 := by
      have hie := hij.1
      rcases hcut with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rw [hsucc]
        omega
      · have h := hsucc j
        have := hij.1
        omega
    have hle : (V 0).card ≤ (V 1).card := by
      rcases hcut with ⟨hc, hjnext⟩ | ⟨hc, _⟩
      · exact (hend 0 1 rfl i hc).2 (by simpa only [← hjnext] using And.intro hj hjodd)
      · exact (hend 0 1 rfl j hc).1 ⟨hj, hjodd⟩
    omega
  · intro hmajor D hCD
    change (V 0).card < (V 1).card at hmajor
    by_contra hne
    obtain ⟨i, j, hi, hj, hij, hcut⟩ :=
      (crownCycleBlockRel_iff_boundaryCut hn P C D (Ne.symm hne)).mp hCD
    have hle : (V 1).card ≤ (V 0).card := by
      rcases hcut with ⟨hc, _⟩ | ⟨hc, hinext⟩
      · exact (hend 1 0 rfl i hc).1 ⟨hi, hij.1⟩
      · exact (hend 1 0 rfl j hc).2 (by simpa only [← hinext] using And.intro hi hij.1)
    omega
end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
