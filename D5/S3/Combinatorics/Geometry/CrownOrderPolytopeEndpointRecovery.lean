/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cycle partitions and selected odd blocks are recovered from endpoint mergers. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEndpointMergers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

/-- Remove the endpoints and split the remaining fibers into their actual cycle
    components. This is the partition used in the inverse of Proposition 3.3. -/
def crownSplitEndpointPartition {n : ℕ} (s : Setoid (CrownAugmentedVertex n)) :
    ConnectedCyclePartition (2 * n) where
  toSetoid := (cyclePartitionGraph (Setoid.comap CrownAugmentedVertex.vertex s)).reachableSetoid
  connected h := h.mono fun _ _ hadj => ⟨hadj.reachable, hadj.2⟩

/-- Splitting the merged fibers along crown edges recovers the original partition.
    Extremality prevents an edge between two distinct selected lower blocks or
    between two distinct selected upper blocks. -/
theorem crownSplitEndpointPartition_merge {n : ℕ} (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (selected : Finset (Quotient P.toSetoid))
    (hselected : ∀ C ∈ selected,
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1)
    (hcompatible : crownCycleCompatible P) :
    crownSplitEndpointPartition
      (twoSidedMergeCCP hn P selected hselected hcompatible).toSetoid = P := by
  have crownRelation_symm_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (i j : Fin (2 * n)) :
      crownRelation n i j ∨ crownRelation n j i ↔
        (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    have hs (a : Fin (2 * n)) :
        (a.val + 1) % (2 * n) = if a.val + 1 = 2 * n then 0 else a.val + 1 := by
      split_ifs with h
      · simp [h]
      · exact Nat.mod_eq_of_lt (by omega)
    have hp (a : Fin (2 * n)) :
        (a.val + 2 * n - 1) % (2 * n) = if a.val = 0 then 2 * n - 1 else a.val - 1 := by
      split_ifs with h
      · simp [h, Nat.mod_eq_of_lt (show 2 * n - 1 < 2 * n by omega)]
      · rw [show a.val + 2 * n - 1 = (a.val - 1) + 2 * n by omega]
        simp [Nat.mod_eq_of_lt (show a.val - 1 < 2 * n by omega)]
    rw [SimpleGraph.cycleGraph_adj']
    have hij := Fin.intCast_val_sub_eq_sub_add_ite i j
    have hji := Fin.intCast_val_sub_eq_sub_add_ite j i
    simp only [crownRelation, hs, hp]
    have heven : (2 * n) % 2 = 0 := by omega
    by_cases hij' : j ≤ i <;> by_cases hji' : i ≤ j <;>
      simp only [hij', hji', if_true, if_false] at hij hji <;>
      split_ifs <;> omega
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  let lower := crownSelectedLowerBlocks P selected
  let upper := crownSelectedUpperBlocks P selected
  let s := (twoSidedMergeCCP hn P selected hselected hcompatible).toSetoid
  have hlower : ∀ L ∈ lower, ∀ C, crownCycleBlockRel P C L → C = L := by
    intro L hL
    obtain ⟨hLs, hmajor⟩ := Finset.mem_filter.mp hL
    exact (crownOddBlock_geometry hn P L (hselected L hLs)).2.1 hmajor
  have hupper : ∀ U ∈ upper, ∀ C, crownCycleBlockRel P U C → C = U := by
    intro U hU
    obtain ⟨hUs, hmajor⟩ := Finset.mem_filter.mp hU
    exact (crownOddBlock_geometry hn P U (hselected U hUs)).2.2 hmajor
  have hedge (i j : Fin (2 * n)) (hij : crownRelation n i j)
      (hmerge : s.r (.vertex i) (.vertex j)) : P.toSetoid.r i j := by
    have hrel : crownCycleBlockRel P (Quotient.mk'' i) (Quotient.mk'' j) :=
      ⟨i, j, rfl, rfl, hij⟩
    change twoSidedMergeCode P lower upper (.vertex i) =
      twoSidedMergeCode P lower upper (.vertex j) at hmerge
    apply Quotient.exact
    by_cases hjL : (Quotient.mk'' j : Quotient P.toSetoid) ∈ lower
    · exact hlower _ hjL _ hrel
    by_cases hiU : (Quotient.mk'' i : Quotient P.toSetoid) ∈ upper
    · exact (hupper _ hiU _ hrel).symm
    by_cases hiL : (Quotient.mk'' i : Quotient P.toSetoid) ∈ lower
    · simp only [twoSidedMergeCode, hiL, hjL, if_true, if_false] at hmerge
      split_ifs at hmerge
    by_cases hjU : (Quotient.mk'' j : Quotient P.toSetoid) ∈ upper
    · simp [twoSidedMergeCode, hiL, hiU, hjL, hjU] at hmerge
    simpa [twoSidedMergeCode, hiL, hiU, hjL, hjU] using hmerge
  have hgraph : cyclePartitionGraph (Setoid.comap CrownAugmentedVertex.vertex s) =
      cyclePartitionGraph P.toSetoid := by
    ext i j
    change (s.r (.vertex i) (.vertex j) ∧ (SimpleGraph.cycleGraph (2 * n)).Adj i j) ↔
      (P.toSetoid.r i j ∧ (SimpleGraph.cycleGraph (2 * n)).Adj i j)
    constructor
    · rintro ⟨hm, ha⟩
      refine ⟨?_, ha⟩
      rcases (crownRelation_symm_iff_cycleGraph_adj hn i j).mpr ha with h | h
      · exact hedge i j h hm
      · exact P.toSetoid.symm (hedge j i h (s.symm hm))
    · rintro ⟨hp, ha⟩
      refine ⟨?_, ha⟩
      change twoSidedMergeCode P lower upper (.vertex i) =
        twoSidedMergeCode P lower upper (.vertex j)
      have hq : (Quotient.mk'' i : Quotient P.toSetoid) = Quotient.mk'' j :=
        Quotient.sound hp
      simp only [twoSidedMergeCode, hq]
  have hs : (crownSplitEndpointPartition s).toSetoid = P.toSetoid := by
    apply Setoid.ext
    intro i j
    change (cyclePartitionGraph (Setoid.comap CrownAugmentedVertex.vertex s)).Reachable i j ↔ _
    rw [hgraph]
    refine ⟨?_, P.connected⟩
    rintro ⟨w⟩
    induction w with
    | nil => exact P.toSetoid.refl _
    | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih
  have hext (A B : ConnectedCyclePartition (2 * n))
      (h : A.toSetoid = B.toSetoid) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext _ _ hs
/-- The source pairs before imposing the block-count equation defining each A_k.
    The selected finset is dependent on the original partition's actual quotient. -/
abbrev CrownOddBlockSelection (n : ℕ) :=
  {a : (Σ P : ConnectedCyclePartition (2 * n), Finset (Quotient P.toSetoid)) //
    crownCycleCompatible a.1 ∧ ∀ C ∈ a.2,
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1}

/-- Proposition 3.3(i): the actual endpoint-merger map is injective on compatible
    connected cycle partitions with selected odd blocks. Equality of the recovered
    partitions transports the dependent finsets before their equality is proved. -/
theorem twoSidedMergeCCP_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (fun a : CrownOddBlockSelection n =>
      twoSidedMergeCCP hn a.val.1 a.val.2 a.property.2 a.property.1) := by
  classical
  rintro ⟨⟨P, selected⟩, hP, hselected⟩ ⟨⟨Q, chosen⟩, hQ, hchosen⟩ heq
  have hs := congrArg CrownConnectedCompatiblePartition.toSetoid heq
  have hPQ : P = Q := by
    rw [← crownSplitEndpointPartition_merge hn P selected hselected hP,
      ← crownSplitEndpointPartition_merge hn Q chosen hchosen hQ]
    exact congrArg crownSplitEndpointPartition hs
  cases hPQ
  have hS : selected = chosen := by
    have hmembership (S : Finset (Quotient P.toSetoid))
        (hS : ∀ C ∈ S, Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1)
        (i : Fin (2 * n)) :
        (Quotient.mk'' i : Quotient P.toSetoid) ∈ S ↔
          (twoSidedMergeCCP hn P S hS hP).toSetoid.r .bottom (.vertex i) ∨
          (twoSidedMergeCCP hn P S hS hP).toSetoid.r .top (.vertex i) := by
      have hcover := (twoSidedMergeCCP_card hn P S hS hP).2.1 (Quotient.mk'' i)
      rw [hcover]
      change _ ↔ twoSidedMergeCode P _ _ .bottom = twoSidedMergeCode P _ _ (.vertex i) ∨
        twoSidedMergeCode P _ _ .top = twoSidedMergeCode P _ _ (.vertex i)
      by_cases hL : (Quotient.mk'' i : Quotient P.toSetoid) ∈ crownSelectedLowerBlocks P S
      · simp [twoSidedMergeCode, hL]
      · by_cases hU : (Quotient.mk'' i : Quotient P.toSetoid) ∈ crownSelectedUpperBlocks P S <;>
          simp [twoSidedMergeCode, hL, hU]
    apply Finset.ext
    intro C
    obtain ⟨i, rfl⟩ := Quotient.exists_rep C
    rw [hmembership selected hselected i, hmembership chosen hchosen i]
    rw [hs]
  cases hS
  rfl

/-- The actual inverse splitting preserves compatibility and every middle block.
    A bottom component contains every lower neighbor of each of its upper vertices;
    a top component contains every upper neighbor of each of its lower vertices. -/
theorem crownSplitEndpointPartition_geometry {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n) :
    let Q := crownSplitEndpointPartition P.toSetoid
    crownCycleCompatible Q ∧
      (∀ i j, ¬ P.toSetoid.r (.vertex i) .bottom →
        ¬ P.toSetoid.r (.vertex i) .top →
        (Q.toSetoid.r i j ↔ P.toSetoid.r (.vertex i) (.vertex j))) ∧
      (∀ i j, crownRelation n i j → P.toSetoid.r .bottom (.vertex j) →
        Q.toSetoid.r i j) ∧
      (∀ i j, crownRelation n i j → P.toSetoid.r .top (.vertex i) →
        Q.toSetoid.r i j) := by
  have crownRelation_symm_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (i j : Fin (2 * n)) :
      crownRelation n i j ∨ crownRelation n j i ↔
        (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    have hs (a : Fin (2 * n)) :
        (a.val + 1) % (2 * n) = if a.val + 1 = 2 * n then 0 else a.val + 1 := by
      split_ifs with h
      · simp [h]
      · exact Nat.mod_eq_of_lt (by omega)
    have hp (a : Fin (2 * n)) :
        (a.val + 2 * n - 1) % (2 * n) = if a.val = 0 then 2 * n - 1 else a.val - 1 := by
      split_ifs with h
      · simp [h, Nat.mod_eq_of_lt (show 2 * n - 1 < 2 * n by omega)]
      · rw [show a.val + 2 * n - 1 = (a.val - 1) + 2 * n by omega]
        simp [Nat.mod_eq_of_lt (show a.val - 1 < 2 * n by omega)]
    rw [SimpleGraph.cycleGraph_adj']
    have hij := Fin.intCast_val_sub_eq_sub_add_ite i j
    have hji := Fin.intCast_val_sub_eq_sub_add_ite j i
    simp only [crownRelation, hs, hp]
    have heven : (2 * n) % 2 = 0 := by omega
    by_cases hij' : j ≤ i <;> by_cases hji' : i ≤ j <;>
      simp only [hij', hji', if_true, if_false] at hij hji <;>
      split_ifs <;> omega
  classical
  dsimp only
  let Q := crownSplitEndpointPartition P.toSetoid
  let G := cyclePartitionGraph (Setoid.comap CrownAugmentedVertex.vertex P.toSetoid)
  have hback {i j : Fin (2 * n)} (h : Q.toSetoid.r i j) :
      P.toSetoid.r (.vertex i) (.vertex j) := by
    change G.Reachable i j at h
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact P.toSetoid.refl _
    | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih
  have hedge {i j : Fin (2 * n)} (hij : crownRelation n i j)
      (h : P.toSetoid.r (.vertex i) (.vertex j)) : Q.toSetoid.r i j := by
    exact (show G.Adj i j from
      ⟨h, (crownRelation_symm_iff_cycleGraph_adj hn i j).mp (Or.inl hij)⟩).reachable
  let q : Quotient Q.toSetoid → Quotient P.toSetoid :=
    Quotient.map CrownAugmentedVertex.vertex (fun _ _ h => hback h)
  have hmapRel {C D : Quotient Q.toSetoid} (h : crownCycleBlockRel Q C D) :
      crownPartitionBlockRel P.toSetoid (q C) (q D) := by
    obtain ⟨i, j, rfl, rfl, hij⟩ := h
    exact ⟨.vertex i, .vertex j, rfl, rfl, Or.inr hij⟩
  have hmapLE {C D : Quotient Q.toSetoid} (h : crownCycleBlockLE Q C D) :
      crownPartitionBlockLE P.toSetoid (q C) (q D) := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ h ih => exact ih.tail (hmapRel h)
  have hcompat : crownCycleCompatible Q := by
    intro C D hCD hDC
    induction hCD with
    | refl => rfl
    | @tail E D hCE hED ih =>
        have hEC : crownCycleBlockLE Q E C :=
          (Relation.ReflTransGen.single hED).trans hDC
        have hCEeq := ih hEC
        subst E
        have heq := P.compatible (Relation.ReflTransGen.single (hmapRel hED)) (hmapLE hDC)
        obtain ⟨i, j, rfl, rfl, hij⟩ := hED
        exact Quotient.sound (hedge hij (Quotient.exact heq))
  refine ⟨hcompat, ?_, ?_, ?_⟩
  · intro i j hbottom htop
    refine ⟨hback, ?_⟩
    intro hij
    let S : Set (Fin (2 * n)) := {v | P.toSetoid.r (.vertex i) (.vertex v)}
    have hc := crownPartition_originalBlock_cycleGraph_connected hn P i hbottom htop
    let f : ((SimpleGraph.cycleGraph (2 * n)).induce S) →g G :=
      { toFun := Subtype.val
        map_rel' := fun {a b} hab => ⟨P.toSetoid.trans (P.toSetoid.symm a.2) b.2, hab⟩ }
    exact (hc.preconnected ⟨i, P.toSetoid.refl _⟩ ⟨j, hij⟩).map f
  · intro i j hij hbottom
    apply hedge hij
    apply Quotient.exact
    apply P.compatible
    · exact Relation.ReflTransGen.single ⟨.vertex i, .vertex j, rfl, rfl, Or.inr hij⟩
    · have heq : (Quotient.mk'' (.vertex j) : Quotient P.toSetoid) =
          Quotient.mk'' .bottom := Quotient.sound (P.toSetoid.symm hbottom)
      change crownPartitionBlockLE P.toSetoid (Quotient.mk'' (.vertex j))
        (Quotient.mk'' (.vertex i))
      rw [heq]
      exact Relation.ReflTransGen.single ⟨.bottom, .vertex i, rfl, rfl, trivial⟩
  · intro i j hij htop
    apply hedge hij
    apply Quotient.exact
    apply P.compatible
    · exact Relation.ReflTransGen.single ⟨.vertex i, .vertex j, rfl, rfl, Or.inr hij⟩
    · have heq : (Quotient.mk'' (.vertex i) : Quotient P.toSetoid) =
          Quotient.mk'' .top := Quotient.sound (P.toSetoid.symm htop)
      change crownPartitionBlockLE P.toSetoid (Quotient.mk'' (.vertex j))
        (Quotient.mk'' (.vertex i))
      rw [heq]
      exact Relation.ReflTransGen.single ⟨.vertex j, .top, rfl, rfl, trivial⟩
/-- Every proper component cut from the bottom fiber has one more lower vertex;
    every proper component cut from the top fiber has one more upper vertex.
    In particular these inverse-selected blocks really have odd cardinality. -/
theorem crownSplitEndpointPartition_endpoint_parity {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (C : Quotient (crownSplitEndpointPartition P.toSetoid).toSetoid)
    (hproper : ∃ v : Fin (2 * n), Quotient.mk'' v ≠ C) :
    let Q := crownSplitEndpointPartition P.toSetoid
    let E := (crownBlockParityVertices Q C 0).card
    let O := (crownBlockParityVertices Q C 1).card
    (P.toSetoid.r .bottom (.vertex C.out) → E = O + 1 ∧
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1) ∧
    (P.toSetoid.r .top (.vertex C.out) → O = E + 1 ∧
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 = 1) := by
  have crownRelation_symm_iff_cycleGraph_adj {n : ℕ} (hn : 2 ≤ n)
      (i j : Fin (2 * n)) :
      crownRelation n i j ∨ crownRelation n j i ↔
        (SimpleGraph.cycleGraph (2 * n)).Adj i j := by
    have hs (a : Fin (2 * n)) :
        (a.val + 1) % (2 * n) = if a.val + 1 = 2 * n then 0 else a.val + 1 := by
      split_ifs with h
      · simp [h]
      · exact Nat.mod_eq_of_lt (by omega)
    have hp (a : Fin (2 * n)) :
        (a.val + 2 * n - 1) % (2 * n) = if a.val = 0 then 2 * n - 1 else a.val - 1 := by
      split_ifs with h
      · simp [h, Nat.mod_eq_of_lt (show 2 * n - 1 < 2 * n by omega)]
      · rw [show a.val + 2 * n - 1 = (a.val - 1) + 2 * n by omega]
        simp [Nat.mod_eq_of_lt (show a.val - 1 < 2 * n by omega)]
    rw [SimpleGraph.cycleGraph_adj']
    have hij := Fin.intCast_val_sub_eq_sub_add_ite i j
    have hji := Fin.intCast_val_sub_eq_sub_add_ite j i
    simp only [crownRelation, hs, hp]
    have heven : (2 * n) % 2 = 0 := by omega
    by_cases hij' : j ≤ i <;> by_cases hji' : i ≤ j <;>
      simp only [hij', hji', if_true, if_false] at hij hji <;>
      split_ifs <;> omega
  classical
  dsimp only
  let : NeZero (2 * n) := ⟨by omega⟩
  let Q := crownSplitEndpointPartition P.toSetoid
  let V := crownBlockParityVertices Q C
  have hmem (v : Fin (2 * n)) (p : ℕ) :
      v ∈ V p ↔ (Quotient.mk'' v : Quotient Q.toSetoid) = C ∧ v.val % 2 = p := by
    simp [V, crownBlockParityVertices]
  have hsucc (v : Fin (2 * n)) : (v + 1).val % 2 = (v.val + 1) % 2 := by
    simp only [Fin.add_def, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
    exact Nat.mod_mod_of_dvd _ (by omega : 2 ∣ 2 * n)
  have hpred (v : Fin (2 * n)) : (v - 1).val % 2 ≠ v.val % 2 := by
    have h := hsucc (v - 1)
    rw [sub_add_cancel] at h
    omega
  have huncut (v : Fin (2 * n)) (hv : v ∉ cycleBoundaryCuts Q) :
      Q.toSetoid.r v (v + 1) := by
    simpa [cycleBoundaryCuts] using hv
  have hexit : ∀ a ∈ cycleBoundaryCuts Q, ∀ b ∈ cycleBoundaryCuts Q,
      (Quotient.mk'' a : Quotient Q.toSetoid) = C → Quotient.mk'' b = C → a = b := by
    have hne (a b : Fin (2 * n)) (ha : a ∈ cycleBoundaryCuts Q)
        (hb : b ∈ cycleBoundaryCuts Q) (hab : a < b) (hrel : Q.toSetoid.r a b) : False := by
      have h := cyclePartitionBlock_arc_constant (by omega) Q a b hab ha hb a b hrel
      have habv : a.val < b.val := hab
      simp only [lt_self_iff_false, false_and, le_refl, and_true] at h
      exact h.mpr habv
    intro a ha b hb haC hbC
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hne a b ha hb hab (Quotient.exact (haC.trans hbC.symm))).elim
    · exact hab
    · exact (hne b a hb ha hab (Quotient.exact (hbC.trans haC.symm))).elim
  obtain ⟨c, hcC, hc⟩ : ∃ c : Fin (2 * n),
      (Quotient.mk'' c : Quotient Q.toSetoid) = C ∧ c ∈ cycleBoundaryCuts Q := by
    by_contra hnone
    have hstep (v : Fin (2 * n)) (hv : (Quotient.mk'' v : Quotient Q.toSetoid) = C) :
        (Quotient.mk'' (v + 1) : Quotient Q.toSetoid) = C := by
      have hvcut : v ∉ cycleBoundaryCuts Q := fun h => hnone ⟨v, hv, h⟩
      exact (Quotient.sound (huncut v hvcut)).symm.trans hv
    have hall (k : ℕ) : (Quotient.mk'' (C.out + Fin.ofNat (2 * n) k) :
        Quotient Q.toSetoid) = C := by
      induction k with
      | zero => simp
      | succ k ih =>
          have heq : Fin.ofNat (2 * n) (k + 1) = Fin.ofNat (2 * n) k + 1 := by
            apply Fin.ext
            simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
          simpa only [heq, add_assoc] using hstep _ ih
    obtain ⟨v, hv⟩ := hproper
    apply hv
    have h := hall (v - C.out).val
    simpa using h
  have hsum : (V 0).card + (V 1).card =
      Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} := by
    have hd : Disjoint (V 0) (V 1) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      have := ((hmem v 0).mp hv).2
      have := ((hmem v 1).mp hw).2
      omega
    rw [← Finset.card_union_of_disjoint hd, Set.ncard_eq_toFinset_card']
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
  have hcounts (p q : ℕ) (hpq : p + q = 1)
      (hclosed : ∀ v, (Quotient.mk'' v : Quotient Q.toSetoid) = C → v.val % 2 = q →
        Q.toSetoid.r v (v + 1) ∧ Q.toSetoid.r v (v - 1)) :
      (V p).card = (V q).card + 1 := by
    have hcp : c.val % 2 = p := by
      have hcnot : ¬ Q.toSetoid.r c (c + 1) := by simpa [cycleBoundaryCuts] using hc
      have hcneq : c.val % 2 ≠ q := fun h => hcnot (hclosed c hcC h).1
      omega
    have hcle : (V p).card ≤ (V q).card + 1 := by
      let bad := (V p).filter fun v => v ∈ cycleBoundaryCuts Q
      have hbad : bad.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        obtain ⟨ha, hac⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb, hbc⟩ := Finset.mem_filter.mp hb
        exact hexit a hac b hbc ((hmem a p).mp ha).1 ((hmem b p).mp hb).1
      have hgood : ((V p) \ bad).card ≤ (V q).card := by
        apply Finset.card_le_card_of_injOn (fun v : Fin (2 * n) => v + 1)
        · intro v hv
          obtain ⟨hv, hvbad⟩ := Finset.mem_sdiff.mp hv
          obtain ⟨hvC, hvp⟩ := (hmem v p).mp hv
          have hvcut : v ∉ cycleBoundaryCuts Q := fun h => hvbad (Finset.mem_filter.mpr ⟨hv, h⟩)
          apply (hmem (v + 1) q).mpr
          refine ⟨(Quotient.sound (huncut v hvcut)).symm.trans hvC, ?_⟩
          rw [hsucc]
          omega
        · intro a _ b _ hab
          exact add_right_cancel hab
      have := Finset.card_le_card_sdiff_add_card (s := V p) (t := bad)
      omega
    have hinj : (V q).card ≤ ((V p).erase c).card := by
      apply Finset.card_le_card_of_injOn (fun v : Fin (2 * n) => v - 1)
      · intro v hv
        obtain ⟨hvC, hvq⟩ := (hmem v q).mp hv
        apply Finset.mem_erase.mpr
        refine ⟨?_, (hmem (v - 1) p).mpr ⟨?_, ?_⟩⟩
        · intro heq
          have hv : v = c + 1 := by rw [← heq, sub_add_cancel]
          have hrel : Q.toSetoid.r c (c + 1) := Quotient.exact (hcC.trans (hv ▸ hvC).symm)
          exact (show ¬ Q.toSetoid.r c (c + 1) by simpa [cycleBoundaryCuts] using hc) hrel
        · exact (Quotient.sound (hclosed v hvC hvq).2).symm.trans hvC
        · have := hpred v
          have := Nat.mod_lt (v - 1).val (by omega : 0 < 2)
          omega
      · intro a _ b _ hab
        have h := congrArg (fun x : Fin (2 * n) => x + 1) hab
        simpa only [sub_add_cancel] using h
    have hcard := Finset.card_erase_add_one ((hmem c p).mpr ⟨hcC, hcp⟩)
    omega
  have hback {i j : Fin (2 * n)} (h : Q.toSetoid.r i j) :
      P.toSetoid.r (.vertex i) (.vertex j) := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact P.toSetoid.refl _
    | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih
  have hneighbor (v : Fin (2 * n)) :
      (SimpleGraph.cycleGraph (2 * n)).Adj v (v + 1) ∧
      (SimpleGraph.cycleGraph (2 * n)).Adj v (v - 1) := by
    constructor <;> rw [SimpleGraph.cycleGraph_adj']
    · right
      simp [Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
    · left
      simp [Nat.mod_eq_of_lt (show 1 < 2 * n by omega)]
  have hgeometry := crownSplitEndpointPartition_geometry hn P
  constructor
  · intro hbottom
    have heq := hcounts 0 1 rfl (by
      intro v hvC hvp
      have hv : P.toSetoid.r .bottom (.vertex v) := P.toSetoid.trans hbottom
        (hback (Quotient.exact ((Quotient.out_eq C).trans hvC.symm)))
      have hside (w : Fin (2 * n)) (ha : (SimpleGraph.cycleGraph (2 * n)).Adj v w) :
          Q.toSetoid.r v w := by
        rcases (crownRelation_symm_iff_cycleGraph_adj hn v w).mpr ha with h | h
        · have := h.1
          omega
        · exact Q.toSetoid.symm (hgeometry.2.2.1 w v h hv)
      exact ⟨hside _ (hneighbor v).1, hside _ (hneighbor v).2⟩)
    exact ⟨heq, by rw [← hsum]; omega⟩
  · intro htop
    have heq := hcounts 1 0 rfl (by
      intro v hvC hvp
      have hv : P.toSetoid.r .top (.vertex v) := P.toSetoid.trans htop
        (hback (Quotient.exact ((Quotient.out_eq C).trans hvC.symm)))
      have hside (w : Fin (2 * n)) (ha : (SimpleGraph.cycleGraph (2 * n)).Adj v w)
          (hpar : w.val % 2 ≠ v.val % 2) :
          Q.toSetoid.r v w := by
        rcases (crownRelation_symm_iff_cycleGraph_adj hn v w).mpr ha with h | h
        · exact hgeometry.2.2.2 v w h hv
        · have := h.1
          omega
      exact ⟨hside _ (hneighbor v).1 (by rw [hsucc]; omega),
        hside _ (hneighbor v).2 (hpred v)⟩)
    exact ⟨heq, by rw [← hsum]; omega⟩
/-- Select exactly the components of the two endpoint fibers after removing the
    endpoints. Membership is independent of the chosen quotient representative. -/
noncomputable def crownEndpointComponentSelection {n : ℕ}
    (s : Setoid (CrownAugmentedVertex n)) :
    Finset (Quotient (crownSplitEndpointPartition s).toSetoid) := by
  classical
  exact Finset.univ.filter fun C => s.r .bottom (.vertex C.out) ∨ s.r .top (.vertex C.out)

/-- The inverse source pair, when neither endpoint fiber contains the whole crown.
    Its compatibility and the oddness of every selected component are proved from
    the actual augmented CCP. -/
noncomputable def crownRecoverOddBlockSelection {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∃ v, ¬ P.toSetoid.r .bottom (.vertex v))
    (htop : ∃ v, ¬ P.toSetoid.r .top (.vertex v)) : CrownOddBlockSelection n := by
  classical
  let Q := crownSplitEndpointPartition P.toSetoid
  refine ⟨⟨Q, crownEndpointComponentSelection P.toSetoid⟩,
    (crownSplitEndpointPartition_geometry hn P).1, ?_⟩
  intro C hC
  have hback {i j : Fin (2 * n)} (h : Q.toSetoid.r i j) :
      P.toSetoid.r (.vertex i) (.vertex j) := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact P.toSetoid.refl _
    | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih
  have hproper (e : CrownAugmentedVertex n) (he : P.toSetoid.r e (.vertex C.out))
      (hmiss : ∃ v, ¬ P.toSetoid.r e (.vertex v)) :
      ∃ v : Fin (2 * n), (Quotient.mk'' v : Quotient Q.toSetoid) ≠ C := by
    obtain ⟨v, hv⟩ := hmiss
    refine ⟨v, fun h => hv (P.toSetoid.trans he ?_)⟩
    exact hback (Quotient.exact ((Quotient.out_eq C).trans h.symm))
  have hmem : P.toSetoid.r .bottom (.vertex C.out) ∨ P.toSetoid.r .top (.vertex C.out) := by
    simpa [crownEndpointComponentSelection] using hC
  rcases hmem with h | h
  · exact ((crownSplitEndpointPartition_endpoint_parity hn P C
      (hproper .bottom h hbottom)).1 h).2
  · exact ((crownSplitEndpointPartition_endpoint_parity hn P C
      (hproper .top h htop)).2 h).2

/-- Merging the actual recovered source pair gives back the augmented partition.
    The hypotheses exclude the indiscrete partition and the two source exceptions. -/
theorem twoSidedMergeCCP_recover {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (hseparate : ¬ P.toSetoid.r .bottom .top)
    (hbottom : ∃ v, ¬ P.toSetoid.r .bottom (.vertex v))
    (htop : ∃ v, ¬ P.toSetoid.r .top (.vertex v)) :
    let a := crownRecoverOddBlockSelection hn P hbottom htop
    twoSidedMergeCCP hn a.val.1 a.val.2 a.property.2 a.property.1 = P := by
  classical
  let a := crownRecoverOddBlockSelection hn P hbottom htop
  let Q := crownSplitEndpointPartition P.toSetoid
  let selected := crownEndpointComponentSelection P.toSetoid
  let M := twoSidedMergeCCP hn a.val.1 a.val.2 a.property.2 a.property.1
  have hback {i j : Fin (2 * n)} (h : Q.toSetoid.r i j) :
      P.toSetoid.r (.vertex i) (.vertex j) := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact P.toSetoid.refl _
    | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih
  have hrep (C : Quotient Q.toSetoid) (i : Fin (2 * n))
      (hi : (Quotient.mk'' i : Quotient Q.toSetoid) = C) :
      P.toSetoid.r (.vertex C.out) (.vertex i) :=
    hback (Quotient.exact ((Quotient.out_eq C).trans hi.symm))
  have hproper (C : Quotient Q.toSetoid) (e : CrownAugmentedVertex n)
      (he : P.toSetoid.r e (.vertex C.out))
      (hmiss : ∃ v, ¬ P.toSetoid.r e (.vertex v)) :
      ∃ v : Fin (2 * n), (Quotient.mk'' v : Quotient Q.toSetoid) ≠ C := by
    obtain ⟨v, hv⟩ := hmiss
    exact ⟨v, fun h => hv (P.toSetoid.trans he (hrep C v h))⟩
  have hflags (i : Fin (2 * n)) :
      ((Quotient.mk'' i : Quotient Q.toSetoid) ∈ crownSelectedLowerBlocks Q selected ↔
        P.toSetoid.r .bottom (.vertex i)) ∧
      ((Quotient.mk'' i : Quotient Q.toSetoid) ∈ crownSelectedUpperBlocks Q selected ↔
        P.toSetoid.r .top (.vertex i)) := by
    let C : Quotient Q.toSetoid := Quotient.mk'' i
    have hr := hrep C i rfl
    have hbot : P.toSetoid.r .bottom (.vertex C.out) ↔ P.toSetoid.r .bottom (.vertex i) :=
      ⟨fun h => P.toSetoid.trans h hr, fun h => P.toSetoid.trans h (P.toSetoid.symm hr)⟩
    have htp : P.toSetoid.r .top (.vertex C.out) ↔ P.toSetoid.r .top (.vertex i) :=
      ⟨fun h => P.toSetoid.trans h hr, fun h => P.toSetoid.trans h (P.toSetoid.symm hr)⟩
    have hL (h : P.toSetoid.r .bottom (.vertex C.out)) :
        (crownBlockParityVertices Q C 0).card = (crownBlockParityVertices Q C 1).card + 1 :=
      ((crownSplitEndpointPartition_endpoint_parity hn P C
        (hproper C .bottom h hbottom)).1 h).1
    have hU (h : P.toSetoid.r .top (.vertex C.out)) :
        (crownBlockParityVertices Q C 1).card = (crownBlockParityVertices Q C 0).card + 1 :=
      ((crownSplitEndpointPartition_endpoint_parity hn P C
        (hproper C .top h htop)).2 h).1
    change (C ∈ crownSelectedLowerBlocks Q selected ↔ _) ∧
      (C ∈ crownSelectedUpperBlocks Q selected ↔ _)
    simp only [crownSelectedLowerBlocks, crownSelectedUpperBlocks, Finset.mem_filter,
      selected, crownEndpointComponentSelection, Finset.mem_univ, true_and]
    constructor
    · constructor
      · rintro ⟨h | h, hmajor⟩
        · exact hbot.mp h
        · have := hU h
          omega
      · intro h
        have hb := hbot.mpr h
        exact ⟨Or.inl hb, by have := hL hb; omega⟩
    · constructor
      · rintro ⟨h | h, hmajor⟩
        · have := hL h
          omega
        · exact htp.mp h
      · intro h
        have ht := htp.mpr h
        exact ⟨Or.inr ht, by have := hU ht; omega⟩
  have hmiddle (i j : Fin (2 * n))
      (hbi : ¬ P.toSetoid.r .bottom (.vertex i))
      (hti : ¬ P.toSetoid.r .top (.vertex i)) :
      ((Quotient.mk'' i : Quotient Q.toSetoid) = Quotient.mk'' j ↔
        P.toSetoid.r (.vertex i) (.vertex j)) := by
    rw [Quotient.eq'']
    exact (crownSplitEndpointPartition_geometry hn P).2.1 i j
      (fun h => hbi (P.toSetoid.symm h)) (fun h => hti (P.toSetoid.symm h))
  have hs : M.toSetoid = P.toSetoid := by
    apply Setoid.ext
    intro u v
    change twoSidedMergeCode Q (crownSelectedLowerBlocks Q selected)
      (crownSelectedUpperBlocks Q selected) u =
      twoSidedMergeCode Q (crownSelectedLowerBlocks Q selected)
        (crownSelectedUpperBlocks Q selected) v ↔ P.toSetoid.r u v
    have hbt (i : Fin (2 * n)) :
        ¬ (P.toSetoid.r .bottom (.vertex i) ∧ P.toSetoid.r .top (.vertex i)) :=
      fun h => hseparate (P.toSetoid.trans h.1 (P.toSetoid.symm h.2))
    have hsame (e u v : CrownAugmentedVertex n) (hu : P.toSetoid.r e u) :
        P.toSetoid.r e v ↔ P.toSetoid.r u v :=
      ⟨fun hv => P.toSetoid.trans (P.toSetoid.symm hu) hv,
        fun huv => P.toSetoid.trans hu huv⟩
    cases u with
    | bottom =>
        cases v with
        | bottom => simp [twoSidedMergeCode]
        | top => simp [twoSidedMergeCode, hseparate]
        | vertex j =>
            simp only [twoSidedMergeCode, (hflags j).1, (hflags j).2]
            split_ifs <;> simp_all
    | top =>
        cases v with
        | bottom =>
            simp [twoSidedMergeCode, show ¬ P.toSetoid.r .top .bottom from
              fun h => hseparate (P.toSetoid.symm h)]
        | top => simp [twoSidedMergeCode]
        | vertex j =>
            simp only [twoSidedMergeCode, (hflags j).1, (hflags j).2]
            split_ifs <;> simp_all
    | vertex i =>
        cases v with
        | bottom =>
            simp only [twoSidedMergeCode, (hflags i).1, (hflags i).2]
            split_ifs <;> simp_all [P.toSetoid.comm]
        | top =>
            simp only [twoSidedMergeCode, (hflags i).1, (hflags i).2]
            split_ifs <;> simp_all [P.toSetoid.comm]
        | vertex j =>
            simp only [twoSidedMergeCode, (hflags i).1, (hflags i).2,
              (hflags j).1, (hflags j).2]
            by_cases hbi : P.toSetoid.r .bottom (.vertex i)
            · rw [if_pos hbi, ← hsame .bottom _ _ hbi]
              split_ifs <;> simp_all
            by_cases hti : P.toSetoid.r .top (.vertex i)
            · rw [if_neg hbi, if_pos hti, ← hsame .top _ _ hti]
              split_ifs <;> simp_all
            rw [if_neg hbi, if_neg hti]
            by_cases hbj : P.toSetoid.r .bottom (.vertex j)
            · have hnot : ¬ P.toSetoid.r (.vertex i) (.vertex j) :=
                fun h => hbi (P.toSetoid.trans hbj (P.toSetoid.symm h))
              simp [hbj, hnot]
            by_cases htj : P.toSetoid.r .top (.vertex j)
            · have hnot : ¬ P.toSetoid.r (.vertex i) (.vertex j) :=
                fun h => hti (P.toSetoid.trans htj (P.toSetoid.symm h))
              simp [hbj, htj, hnot]
            simpa [hbj, htj] using hmiddle i j hbi hti
  have hext (A B : CrownConnectedCompatiblePartition n)
      (h : A.toSetoid = B.toSetoid) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext M P hs

/-- The source's A_k, with the actual quotient-block count and selected cardinality. -/
abbrev CrownOddBlockSelectionOfCard (n k : ℕ) :=
  {a : CrownOddBlockSelection n //
    Nat.card (Quotient a.val.1.toSetoid) - a.val.2.card = k - 2}

/-- Proposition 3.3's map with the source and target block counts in the types. -/
noncomputable def crownOddBlockMerge {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k)
    (a : CrownOddBlockSelectionOfCard n k) :
    {P : CrownConnectedCompatiblePartition n // Nat.card (Quotient P.toSetoid) = k} := by
  refine ⟨twoSidedMergeCCP hn a.val.val.1 a.val.val.2 a.val.property.2 a.val.property.1, ?_⟩
  have hc := (twoSidedMergeCCP_card hn a.val.val.1 a.val.val.2
    a.val.property.2 a.val.property.1).2.2
  have ha := a.property
  omega

/-- Proposition 3.3(ii): for k ≥ 3 the actual source map is a bijection.
    A fiber containing every crown vertex would leave at most two quotient blocks,
    so the inverse's endpoint exclusions follow from the given block count. -/
theorem crownOddBlockMerge_bijective {n k : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k) :
    Function.Bijective (crownOddBlockMerge hn (by omega : 2 ≤ k)) := by
  classical
  constructor
  · intro a b hab
    apply Subtype.ext
    apply twoSidedMergeCCP_injective hn
    exact congrArg Subtype.val hab
  · rintro ⟨P, hcard⟩
    have hsmall (hall : (∀ v, P.toSetoid.r .bottom (.vertex v)) ∨
        (∀ v, P.toSetoid.r .top (.vertex v))) : Nat.card (Quotient P.toSetoid) ≤ 2 := by
      let f : Bool → Quotient P.toSetoid := fun b =>
        if b then Quotient.mk'' .top else Quotient.mk'' .bottom
      have hf : Function.Surjective f := by
        intro C
        obtain ⟨u, rfl⟩ := Quotient.exists_rep C
        cases u with
        | bottom => exact ⟨false, rfl⟩
        | top => exact ⟨true, rfl⟩
        | vertex i =>
            rcases hall with h | h
            · exact ⟨false, Quotient.sound (h i)⟩
            · exact ⟨true, Quotient.sound (h i)⟩
      have h := Nat.card_le_card_of_surjective f hf
      simpa using h
    have hbottom : ∃ v, ¬ P.toSetoid.r .bottom (.vertex v) := by
      by_contra h
      have hb : ∀ v, P.toSetoid.r .bottom (.vertex v) := by simpa using h
      have := hsmall (Or.inl hb)
      omega
    have htop : ∃ v, ¬ P.toSetoid.r .top (.vertex v) := by
      by_contra h
      have ht : ∀ v, P.toSetoid.r .top (.vertex v) := by simpa using h
      have := hsmall (Or.inr ht)
      omega
    have hseparate : ¬ P.toSetoid.r .bottom .top := by
      intro h
      obtain ⟨i, hi⟩ := hbottom
      apply hi
      apply Quotient.exact
      apply P.compatible
      · exact Relation.ReflTransGen.single ⟨.bottom, .vertex i, rfl, rfl, trivial⟩
      · exact Relation.ReflTransGen.single
          ⟨.vertex i, .top, rfl, (Quotient.sound h).symm, trivial⟩
    let a := crownRecoverOddBlockSelection hn P hbottom htop
    have hmerge := twoSidedMergeCCP_recover hn P hseparate hbottom htop
    change twoSidedMergeCCP hn a.val.1 a.val.2 a.property.2 a.property.1 = P at hmerge
    have ha : Nat.card (Quotient a.val.1.toSetoid) - a.val.2.card = k - 2 := by
      have hc := (twoSidedMergeCCP_card hn a.val.1 a.val.2 a.property.2 a.property.1).2.2
      rw [hmerge, hcard] at hc
      omega
    exact ⟨⟨a, ha⟩, Subtype.ext hmerge⟩

/-- Exact image of the source map, including its exclusions at k = 2: the endpoints
    are separate and neither endpoint fiber contains all original crown vertices. -/
theorem twoSidedMergeCCP_range_iff {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n) :
    (∃ a : CrownOddBlockSelection n,
      twoSidedMergeCCP hn a.val.1 a.val.2 a.property.2 a.property.1 = P) ↔
      ¬ P.toSetoid.r .bottom .top ∧
        (∃ v, ¬ P.toSetoid.r .bottom (.vertex v)) ∧
        (∃ v, ¬ P.toSetoid.r .top (.vertex v)) := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    let Q := a.val.1
    let selected := a.val.2
    let M := twoSidedMergeCCP hn Q selected a.property.2 a.property.1
    have hseparate : ¬ M.toSetoid.r .bottom .top := by
      change twoSidedMergeCode Q _ _ .bottom ≠ twoSidedMergeCode Q _ _ .top
      simp [twoSidedMergeCode]
    have hfull (e : CrownAugmentedVertex n)
        (hall : ∀ v, M.toSetoid.r e (.vertex v)) : ∀ i j, Q.toSetoid.r i j := by
      have hgraph : cyclePartitionGraph (Setoid.comap CrownAugmentedVertex.vertex M.toSetoid) =
          SimpleGraph.cycleGraph (2 * n) := by
        ext i j
        change (M.toSetoid.r (.vertex i) (.vertex j) ∧ _) ↔ _
        exact and_iff_right (M.toSetoid.trans (M.toSetoid.symm (hall i)) (hall j))
      intro i j
      have hr : (crownSplitEndpointPartition M.toSetoid).toSetoid.r i j := by
        change (cyclePartitionGraph
          (Setoid.comap CrownAugmentedVertex.vertex M.toSetoid)).Reachable i j
        rw [hgraph]
        exact SimpleGraph.cycleGraph_preconnected i j
      have heq := crownSplitEndpointPartition_merge hn Q selected a.property.2 a.property.1
      change crownSplitEndpointPartition M.toSetoid = Q at heq
      exact Eq.mp (congrArg (fun R : ConnectedCyclePartition (2 * n) => R.toSetoid.r i j) heq) hr
    let i : Fin (2 * n) := ⟨0, by omega⟩
    have hselected (he : M.toSetoid.r .bottom (.vertex i) ∨
        M.toSetoid.r .top (.vertex i)) : (Quotient.mk'' i : Quotient Q.toSetoid) ∈ selected := by
      by_contra hS
      have hL : (Quotient.mk'' i : Quotient Q.toSetoid) ∉ crownSelectedLowerBlocks Q selected :=
        fun h => hS (Finset.mem_filter.mp h).1
      have hU : (Quotient.mk'' i : Quotient Q.toSetoid) ∉ crownSelectedUpperBlocks Q selected :=
        fun h => hS (Finset.mem_filter.mp h).1
      rcases he with he | he
      · change twoSidedMergeCode Q _ _ .bottom = twoSidedMergeCode Q _ _ (.vertex i) at he
        simp [twoSidedMergeCode, hL, hU] at he
      · change twoSidedMergeCode Q _ _ .top = twoSidedMergeCode Q _ _ (.vertex i) at he
        simp [twoSidedMergeCode, hL, hU] at he
    have hnotfull (hS : (Quotient.mk'' i : Quotient Q.toSetoid) ∈ selected)
        (hall : ∀ j k, Q.toSetoid.r j k) : False := by
      have hs : {v : Fin (2 * n) | (Quotient.mk'' v : Quotient Q.toSetoid) = Quotient.mk'' i} =
          Set.univ := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact Quotient.sound (hall v i)
      have ho := a.property.2 (Quotient.mk'' i) hS
      change Set.ncard {v : Fin (2 * n) |
        (Quotient.mk'' v : Quotient Q.toSetoid) = Quotient.mk'' i} % 2 = 1 at ho
      rw [hs, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at ho
      omega
    refine ⟨hseparate, ?_, ?_⟩
    · by_contra h
      have hall : ∀ v, M.toSetoid.r .bottom (.vertex v) := by simpa using h
      exact hnotfull (hselected (Or.inl (hall i))) (hfull .bottom hall)
    · by_contra h
      have hall : ∀ v, M.toSetoid.r .top (.vertex v) := by simpa using h
      exact hnotfull (hselected (Or.inr (hall i))) (hfull .top hall)
  · rintro ⟨hseparate, hbottom, htop⟩
    exact ⟨crownRecoverOddBlockSelection hn P hbottom htop,
      twoSidedMergeCCP_recover hn P hseparate hbottom htop⟩

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
