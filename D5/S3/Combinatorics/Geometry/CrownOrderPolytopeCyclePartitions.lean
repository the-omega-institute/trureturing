/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Connected crown partitions are reconstructed exactly from their cyclic boundary cuts. -/

/- Library search (2026-09-19): pinned Mathlib supplies `cycleGraph`, reachability
   setoids, and connected components, but no equivalence between cyclic edge cuts and
   connected vertex partitions.  The construction below uses those graph primitives. -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeCycleCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope


/-- The directed quotient relation induced by the actual crown order on a connected
    cyclic partition. -/
def crownCycleBlockRel {n : ℕ} (P : ConnectedCyclePartition (2 * n))
    (C D : Quotient P.toSetoid) : Prop :=
  ∃ i j : Fin (2 * n),
    Quotient.mk'' i = C ∧ Quotient.mk'' j = D ∧ crownRelation n i j

/- Between distinct quotient blocks, every directed crown relation crosses an actual
   cyclic boundary cut, and every such directed boundary witnesses the quotient relation. -/
/- Reachability in the directed crown relation on cyclic partition blocks. -/
def crownCycleBlockLE {n : ℕ} (P : ConnectedCyclePartition (2 * n))
    (C D : Quotient P.toSetoid) : Prop :=
  Relation.ReflTransGen (crownCycleBlockRel P) C D

/- Compatibility for an unaugmented connected crown partition. -/
def crownCycleCompatible {n : ℕ} (P : ConnectedCyclePartition (2 * n)) : Prop :=
  ∀ {C D : Quotient P.toSetoid}, crownCycleBlockLE P C D →
    crownCycleBlockLE P D C → C = D

/- If every actual boundary cut starts at an even vertex, following cyclic successors
   gives a directed quotient cycle.  The `N - 1` return path includes the two-block case. -/
private theorem not_crownCycleCompatible_of_evenCuts {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (heven : ∀ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) :
    ¬ crownCycleCompatible P := by
  have crownCycleBlockLE_succ_of_evenCuts {n : ℕ} [NeZero (2 * n)]
      (P : ConnectedCyclePartition (2 * n))
      (heven : ∀ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) (i : Fin (2 * n)) :
      crownCycleBlockLE P (Quotient.mk'' i) (Quotient.mk'' (i + 1)) := by
    by_cases hi : i.val % 2 = 0
    · apply Relation.ReflTransGen.single
      refine ⟨i, i + 1, rfl, rfl, hi, Or.inl ?_⟩
      simp [Fin.add_def]
    · have hnotCut : i ∉ cycleBoundaryCuts P := fun hcut => hi (heven i hcut)
      have hsame : P.toSetoid.r i (i + 1) := by
        by_contra hne
        exact hnotCut (by simpa [cycleBoundaryCuts] using hne)
      have hq : Quotient.mk'' i = Quotient.mk'' (i + 1) := Quotient.sound hsame
      unfold crownCycleBlockLE
      rw [hq]
  have hcuts : cycleBoundaryCuts P ≠ ∅ := by
    intro hempty
    obtain ⟨u, v, huv⟩ := hnontrivial
    exact huv ((cycleBoundaryCuts_eq_empty_iff (by omega) P).mp hempty u v)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hcuts
  let C : Quotient P.toSetoid := Quotient.mk'' c
  let D : Quotient P.toSetoid := Quotient.mk'' (c + 1)
  have hCD : C ≠ D := by
    intro h
    have hsame : P.toSetoid.r c (c + 1) := Quotient.exact h
    have hboundary : ¬ P.toSetoid.r c (c + 1) := by
      simpa [cycleBoundaryCuts] using hc
    exact hboundary hsame
  have hforward : crownCycleBlockLE P C D :=
    crownCycleBlockLE_succ_of_evenCuts P heven c
  have hreturn : crownCycleBlockLE P D C := by
    have hreach : ∀ k : ℕ,
        Relation.ReflTransGen (crownCycleBlockRel P) D
          (Quotient.mk'' (c + 1 + Fin.ofNat (2 * n) k)) := by
      intro k
      induction k with
      | zero =>
          simpa [D] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (crownCycleBlockRel P) D D)
      | succ k ih =>
          have hstep := crownCycleBlockLE_succ_of_evenCuts P heven
            (c + 1 + Fin.ofNat (2 * n) k)
          change Relation.ReflTransGen (crownCycleBlockRel P) _ _ at hstep
          simpa [Fin.ofNat, Fin.add_def, add_assoc] using ih.trans hstep
    have hlast := hreach (2 * n - 1)
    have hfin : c + 1 + Fin.ofNat (2 * n) (2 * n - 1) = c := by
      apply Fin.ext
      simp only [Fin.add_def, Fin.val_one', Fin.val_ofNat]
      have hNm1 : (2 * n - 1) % (2 * n) = 2 * n - 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hNm1]
      have hone : 1 % (2 * n) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hone]
      by_cases hlast : c.val = 2 * n - 1
      · rw [hlast]
        have hzero : (2 * n - 1 + 1) % (2 * n) = 0 := by
          rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
        rw [hzero, zero_add, hNm1]
      · have hlt : c.val + 1 < 2 * n := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have hsum : c.val + 1 + (2 * n - 1) = c.val + 2 * n := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt c.isLt]
    change Relation.ReflTransGen (crownCycleBlockRel P) D C
    rw [hfin] at hlast
    simpa [C] using hlast
  intro hcompatible
  exact hCD (hcompatible hforward hreturn)
/- If every actual boundary cut starts at an odd vertex, directed quotient edges
   traverse the cyclic blocks in the opposite direction and again form a cycle. -/
private theorem not_crownCycleCompatible_of_oddCuts {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (hodd : ∀ c ∈ cycleBoundaryCuts P, c.val % 2 = 1) :
    ¬ crownCycleCompatible P := by
  have crownCycleBlockLE_pred_of_oddCuts {n : ℕ} [NeZero (2 * n)]
      (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
      (hodd : ∀ c ∈ cycleBoundaryCuts P, c.val % 2 = 1) (i : Fin (2 * n)) :
      crownCycleBlockLE P (Quotient.mk'' (i + 1)) (Quotient.mk'' i) := by
    by_cases hi : i.val % 2 = 1
    · apply Relation.ReflTransGen.single
      refine ⟨i + 1, i, rfl, rfl, ?_⟩
      have hsucc : (i + 1).val = (i.val + 1) % (2 * n) := by
        simp [Fin.add_def]
      constructor
      · rw [hsucc]
        rw [Nat.mod_mod_of_dvd]
        · omega
        · exact dvd_mul_right 2 n
      · right
        by_cases hwrap : i.val + 1 < 2 * n
        · rw [hsucc, Nat.mod_eq_of_lt hwrap]
          rw [show i.val + 1 + 2 * n - 1 = i.val + 2 * n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        · have hlast : i.val + 1 = 2 * n := by omega
          rw [hsucc, hlast, Nat.mod_self, zero_add,
            Nat.mod_eq_of_lt (show 2 * n - 1 < 2 * n by omega)]
          omega
    · have hnotCut : i ∉ cycleBoundaryCuts P := fun hcut => hi (hodd i hcut)
      have hsame : P.toSetoid.r i (i + 1) := by
        by_contra hne
        exact hnotCut (by simpa [cycleBoundaryCuts] using hne)
      have hq : Quotient.mk'' (i + 1) = Quotient.mk'' i :=
        (Quotient.sound hsame).symm
      unfold crownCycleBlockLE
      rw [hq]
  have hcuts : cycleBoundaryCuts P ≠ ∅ := by
    intro hempty
    obtain ⟨u, v, huv⟩ := hnontrivial
    exact huv ((cycleBoundaryCuts_eq_empty_iff (by omega) P).mp hempty u v)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hcuts
  let C : Quotient P.toSetoid := Quotient.mk'' (c + 1)
  let D : Quotient P.toSetoid := Quotient.mk'' c
  have hCD : C ≠ D := by
    intro h
    have hsame : P.toSetoid.r (c + 1) c := Quotient.exact h
    have hboundary : ¬ P.toSetoid.r c (c + 1) := by
      simpa [cycleBoundaryCuts] using hc
    exact hboundary (P.toSetoid.symm hsame)
  have hforward : crownCycleBlockLE P C D :=
    crownCycleBlockLE_pred_of_oddCuts hn P hodd c
  have hreturn : crownCycleBlockLE P D C := by
    have hreach : ∀ k : ℕ,
        Relation.ReflTransGen (crownCycleBlockRel P) D
          (Quotient.mk'' (c - Fin.ofNat (2 * n) k)) := by
      intro k
      induction k with
      | zero =>
          simpa [D] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen (crownCycleBlockRel P) D D)
      | succ k ih =>
          have hstep := crownCycleBlockLE_pred_of_oddCuts hn P hodd
            (c - Fin.ofNat (2 * n) (k + 1))
          change Relation.ReflTransGen (crownCycleBlockRel P) _ _ at hstep
          have hsource :
              c - Fin.ofNat (2 * n) (k + 1) + 1 =
                c - Fin.ofNat (2 * n) k := by
            have hk : Fin.ofNat (2 * n) (k + 1) =
                Fin.ofNat (2 * n) k + 1 := by
              apply Fin.ext
              simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
            rw [hk]
            abel
          rw [hsource] at hstep
          exact ih.trans hstep
    have hlast := hreach (2 * n - 1)
    have hfin : c - Fin.ofNat (2 * n) (2 * n - 1) = c + 1 := by
      apply Fin.ext
      simp only [Fin.sub_def, Fin.add_def, Fin.val_one', Fin.val_ofNat]
      have hNm1 : (2 * n - 1) % (2 * n) = 2 * n - 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hNm1]
      rw [show 2 * n - (2 * n - 1) = 1 by omega]
      simp [Nat.add_comm]
    change Relation.ReflTransGen (crownCycleBlockRel P) D C
    rw [hfin] at hlast
    simpa [C] using hlast
  intro hcompatible
  exact hCD (hcompatible hforward hreturn)
/- Every nontrivial compatible cyclic crown partition has boundary cuts of both
   parities.  Uniform parity is excluded by the two explicit quotient cycles. -/
private theorem mixedBoundaryCuts_of_crownCycleCompatible {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (hcompatible : crownCycleCompatible P) :
    (∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) ∧
      ∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 1 := by
  have hcuts : cycleBoundaryCuts P ≠ ∅ := by
    intro hempty
    obtain ⟨u, v, huv⟩ := hnontrivial
    exact huv ((cycleBoundaryCuts_eq_empty_iff (by omega) P).mp hempty u v)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hcuts
  have hparity : c.val % 2 = 0 ∨ c.val % 2 = 1 := by omega
  rcases hparity with hcEven | hcOdd
  · refine ⟨⟨c, hc, hcEven⟩, ?_⟩
    by_contra hnone
    push Not at hnone
    have hallEven : ∀ d ∈ cycleBoundaryCuts P, d.val % 2 = 0 := by
      intro d hd
      have hdlt : d.val % 2 < 2 := Nat.mod_lt _ (by omega)
      have hdne : d.val % 2 ≠ 1 := hnone d hd
      omega
    exact not_crownCycleCompatible_of_evenCuts hn P hnontrivial hallEven hcompatible
  · refine ⟨?_, ⟨c, hc, hcOdd⟩⟩
    by_contra hnone
    push Not at hnone
    have hallOdd : ∀ d ∈ cycleBoundaryCuts P, d.val % 2 = 1 := by
      intro d hd
      have hdlt : d.val % 2 < 2 := Nat.mod_lt _ (by omega)
      have hdne : d.val % 2 ≠ 0 := hnone d hd
      omega
    exact not_crownCycleCompatible_of_oddCuts hn P hnontrivial hallOdd hcompatible

/- The arc between an even and a later odd boundary is closed under the actual
   directed crown comparisons: neither of its two boundary edges points out. -/
/- On the quotient of actual connected blocks, entering the arc from an outside
   block is possible, but leaving it along a crown comparison is not. -/
private theorem crownCycleBlockLE_preserves_evenOddArc {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (e o : Fin (2 * n)) (heo : e < o)
    (heCut : e ∈ cycleBoundaryCuts P) (hoCut : o ∈ cycleBoundaryCuts P)
    (he : e.val % 2 = 0) (ho : o.val % 2 = 1)
    (i j : Fin (2 * n))
    (hij : crownCycleBlockLE P (Quotient.mk'' i) (Quotient.mk'' j))
    (hi : e.val < i.val ∧ i.val ≤ o.val) :
    e.val < j.val ∧ j.val ≤ o.val := by
  have crownRelation_preserves_evenOddArc {n : ℕ} (hn : 2 ≤ n)
      (e o i j : Fin (2 * n))
      (he : e.val % 2 = 0) (ho : o.val % 2 = 1)
      (hi : e.val < i.val ∧ i.val ≤ o.val) (hij : crownRelation n i j) :
      e.val < j.val ∧ j.val ≤ o.val := by
    rcases hij with ⟨hieven, hsucc | hpred⟩
    · by_cases hwrap : i.val + 1 < 2 * n
      · rw [Nat.mod_eq_of_lt hwrap] at hsucc
        omega
      · have hlast : i.val + 1 = 2 * n := by omega
        rw [hlast, Nat.mod_self] at hsucc
        have hoddLast : i.val % 2 = 1 := by omega
        omega
    · by_cases hi0 : i.val = 0
      · omega
      · have hform : i.val + 2 * n - 1 = (i.val - 1) + 2 * n := by omega
        rw [hform, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show i.val - 1 < 2 * n by omega)] at hpred
        have hboundary : i.val ≠ e.val + 1 := by
          intro heq
          have hevenNext : i.val % 2 = 1 := by omega
          omega
        omega
  let inside (C : Quotient P.toSetoid) : Prop :=
    ∃ v : Fin (2 * n), Quotient.mk'' v = C ∧ e.val < v.val ∧ v.val ≤ o.val
  have step {C D : Quotient P.toSetoid} (hCD : crownCycleBlockRel P C D)
      (hC : inside C) : inside D := by
    obtain ⟨v, hv, hvArc⟩ := hC
    obtain ⟨u, w, hu, hw, huw⟩ := hCD
    have huArc : e.val < u.val ∧ u.val ≤ o.val :=
      (cyclePartitionBlock_arc_constant (by omega) P e o heo heCut hoCut v u
        (Quotient.exact (hv.trans hu.symm))).mp hvArc
    exact ⟨w, hw, crownRelation_preserves_evenOddArc hn e o u w he ho huArc huw⟩
  have reach {C D : Quotient P.toSetoid} (hCD : crownCycleBlockLE P C D)
      (hC : inside C) : inside D := by
    induction hCD with
    | refl => exact hC
    | tail hCE hED ih => exact step hED ih
  obtain ⟨v, hv, hvArc⟩ := reach hij ⟨i, rfl, hi⟩
  exact (cyclePartitionBlock_arc_constant (by omega) P e o heo heCut hoCut v j
    (Quotient.exact hv)).mp hvArc
/- If the earlier cut is odd and the later cut is even, both boundary
   comparisons point out of the intervening arc, so its complement is closed. -/
private theorem crownCycleBlockLE_preserves_oddEvenArcOutside {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (o e : Fin (2 * n)) (hoe : o < e)
    (hoCut : o ∈ cycleBoundaryCuts P) (heCut : e ∈ cycleBoundaryCuts P)
    (ho : o.val % 2 = 1) (he : e.val % 2 = 0)
    (i j : Fin (2 * n))
    (hij : crownCycleBlockLE P (Quotient.mk'' i) (Quotient.mk'' j))
    (hi : ¬ (o.val < i.val ∧ i.val ≤ e.val)) :
    ¬ (o.val < j.val ∧ j.val ≤ e.val) := by
  have crownRelation_preserves_oddEvenArcOutside {n : ℕ} (hn : 2 ≤ n)
      (o e i j : Fin (2 * n)) (ho : o.val % 2 = 1) (he : e.val % 2 = 0)
      (hi : ¬ (o.val < i.val ∧ i.val ≤ e.val)) (hij : crownRelation n i j) :
      ¬ (o.val < j.val ∧ j.val ≤ e.val) := by
    rcases hij with ⟨hieven, hsucc | hpred⟩
    · by_cases hwrap : i.val + 1 < 2 * n
      · rw [Nat.mod_eq_of_lt hwrap] at hsucc
        have hnotOdd : i.val ≠ o.val := by
          intro h
          omega
        omega
      · have hlast : i.val + 1 = 2 * n := by omega
        rw [hlast, Nat.mod_self] at hsucc
        omega
    · by_cases hi0 : i.val = 0
      · have hlast : (2 * n - 1) % (2 * n) = 2 * n - 1 :=
          Nat.mod_eq_of_lt (by omega)
        have hj : j.val = 2 * n - 1 := by simpa [hi0, hlast] using hpred
        rw [hj]
        omega
      · have hform : i.val + 2 * n - 1 = (i.val - 1) + 2 * n := by omega
        rw [hform, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show i.val - 1 < 2 * n by omega)] at hpred
        have hnotEven : i.val ≠ e.val + 1 := by
          intro h
          omega
        omega
  let outside (C : Quotient P.toSetoid) : Prop :=
    ∃ v : Fin (2 * n), Quotient.mk'' v = C ∧ ¬ (o.val < v.val ∧ v.val ≤ e.val)
  have step {C D : Quotient P.toSetoid} (hCD : crownCycleBlockRel P C D)
      (hC : outside C) : outside D := by
    obtain ⟨v, hv, hvOutside⟩ := hC
    obtain ⟨u, w, hu, hw, huw⟩ := hCD
    have huOutside : ¬ (o.val < u.val ∧ u.val ≤ e.val) :=
      (cyclePartitionBlock_arc_constant (by omega) P o e hoe hoCut heCut v u
        (Quotient.exact (hv.trans hu.symm))).mpr.mt hvOutside
    exact ⟨w, hw, crownRelation_preserves_oddEvenArcOutside hn o e u w ho he
      huOutside huw⟩
  have reach {C D : Quotient P.toSetoid} (hCD : crownCycleBlockLE P C D)
      (hC : outside C) : outside D := by
    induction hCD with
    | refl => exact hC
    | tail hCE hED ih => exact step hED ih
  obtain ⟨v, hv, hvOutside⟩ := reach hij ⟨i, rfl, hi⟩
  exact (cyclePartitionBlock_arc_constant (by omega) P o e hoe hoCut heCut v j
    (Quotient.exact hv)).mpr.mt hvOutside
/- Every comparison across an actual boundary has a one-way barrier.  The
   opposite-parity boundary closes either the intervening arc or its complement;
   the directed edge itself points from the open side to the closed side. -/
private theorem crownCycleBlockRel_no_reverse_of_mixedCuts {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hmixed : (∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) ∧
      ∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 1)
    {C D : Quotient P.toSetoid} (hCD : crownCycleBlockRel P C D)
    (hne : C ≠ D) : ¬ crownCycleBlockLE P D C := by
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
  obtain ⟨⟨e, heCut, heEven⟩, ⟨o, hoCut, hoOdd⟩⟩ := hmixed
  obtain ⟨a, b, ha, hb, hab, hcut⟩ :=
    (crownCycleBlockRel_iff_boundaryCut hn P C D hne).mp hCD
  have hreverse (hDC : crownCycleBlockLE P D C) :
      crownCycleBlockLE P (Quotient.mk'' b) (Quotient.mk'' a) := by
    rw [ha, hb]
    exact hDC
  intro hDC
  rcases hcut with ⟨haCut, rfl⟩ | ⟨hbCut, rfl⟩
  · have haEven : a.val % 2 = 0 := hab.1
    have hnotLast : a.val + 1 < 2 * n := by
      have hlastOdd : (2 * n - 1) % 2 = 1 := by omega
      omega
    have hval : (a + 1).val = a.val + 1 := by
      simp [Fin.add_def, Nat.mod_eq_of_lt hnotLast]
    by_cases hao : a < o
    · have hinside : a.val < (a + 1).val ∧ (a + 1).val ≤ o.val := by omega
      have houtside : ¬ (a.val < a.val ∧ a.val ≤ o.val) := by omega
      exact houtside (crownCycleBlockLE_preserves_evenOddArc hn P a o hao
        haCut hoCut hab.1 hoOdd (a + 1) a (hreverse hDC) hinside)
    · have hoa : o < a := by
        have hne : o ≠ a := by
          intro heq
          subst a
          omega
        exact lt_of_le_of_ne (le_of_not_gt hao) hne
      have houtside : ¬ (o.val < (a + 1).val ∧ (a + 1).val ≤ a.val) := by omega
      have hinside : o.val < a.val ∧ a.val ≤ a.val := by omega
      exact (crownCycleBlockLE_preserves_oddEvenArcOutside hn P o a hoa
        hoCut haCut hoOdd hab.1 (a + 1) a (hreverse hDC) houtside) hinside
  · have hbOdd : b.val % 2 = 1 := by
      have hmod : ((b.val + 1) % (2 * n)) % 2 = 0 := by
        simpa [Fin.add_def] using hab.1
      by_cases hwrap : b.val + 1 < 2 * n
      · rw [Nat.mod_eq_of_lt hwrap] at hmod
        omega
      · have hlast : b.val + 1 = 2 * n := by omega
        omega
    by_cases heb : e < b
    · have hinside : e.val < b.val ∧ b.val ≤ b.val := by omega
      have houtside : ¬ (e.val < (b + 1).val ∧ (b + 1).val ≤ b.val) := by
        have hval : (b + 1).val = (b.val + 1) % (2 * n) := by
          simp [Fin.add_def]
        rw [hval]
        by_cases hwrap : b.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt hwrap]
          omega
        · have hlast : b.val + 1 = 2 * n := by omega
          rw [hlast, Nat.mod_self]
          omega
      exact houtside (crownCycleBlockLE_preserves_evenOddArc hn P e b heb
        heCut hbCut heEven hbOdd b (b + 1) (hreverse hDC) hinside)
    · have hbe : b < e := by
        have hne : b ≠ e := by
          intro heq
          subst e
          omega
        exact lt_of_le_of_ne (le_of_not_gt heb) hne
      have houtside : ¬ (b.val < b.val ∧ b.val ≤ e.val) := by omega
      have hinside : b.val < (b + 1).val ∧ (b + 1).val ≤ e.val := by
        have hlt : b.val + 1 < 2 * n := by omega
        simp [Fin.add_def, Nat.mod_eq_of_lt hlt]
        omega
      exact (crownCycleBlockLE_preserves_oddEvenArcOutside hn P b e hbe
        hbCut heCut hbOdd heEven b (b + 1) (hreverse hDC) houtside) hinside
/- No directed cycle of distinct actual connected blocks survives a mixed-parity
   pair of cuts.  In particular, parallel boundary edges in a two-block quotient
   cannot point in opposite directions. -/
private theorem crownCycleCompatible_of_mixedBoundaryCuts {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hmixed : (∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) ∧
      ∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 1) :
    crownCycleCompatible P := by
  intro C D hCD hDC
  induction hCD with
  | refl => rfl
  | @tail E D hCE hED ih =>
      have hEC : crownCycleBlockLE P E C :=
        (Relation.ReflTransGen.single hED).trans hDC
      have hCEeq : C = E := ih hEC
      subst E
      by_cases hsame : C = D
      · exact hsame
      · exact False.elim ((crownCycleBlockRel_no_reverse_of_mixedCuts
          hn P hmixed hED hsame) hDC)

/- Uniform-parity boundaries pair the vertices of every actual block across
   uncut crown edges.  Hence every quotient fiber has even cardinality. -/
private theorem cycleBlock_even_of_uniformBoundaryCuts {n : ℕ} [NeZero (2 * n)]
    (P : ConnectedCyclePartition (2 * n)) (p : ℕ)
    (hp : p = 0 ∨ p = 1)
    (huniform : ∀ c ∈ cycleBoundaryCuts P, c.val % 2 = p)
    (C : Quotient P.toSetoid) :
    (Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2) = 0 := by
  classical
  let fiber := Finset.univ.filter fun v : Fin (2 * n) => Quotient.mk'' v = C
  have hcard : Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} = fiber.card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext v
    simp [fiber]
  rw [hcard]
  rcases hp with rfl | rfl
  · let e : Fin n × Fin 2 ≃ Fin (2 * n) :=
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))).trans
        (finRotate (2 * n))
    let base := Finset.univ.filter fun i : Fin n =>
      Quotient.mk'' (e (i, 0)) = C
    have hpair (i : Fin n) : P.toSetoid.r (e (i, 0)) (e (i, 1)) := by
      let x : Fin (2 * n) := e (i, 0)
      have hxval : x.val % 2 = 1 := by
        have hi : 2 * i.val + 1 < 2 * n := by omega
        simp [x, e, finProdFinEquiv, finRotate_apply, Fin.add_def,
          Nat.mod_eq_of_lt hi]
      have hxnot : x ∉ cycleBoundaryCuts P := by
        intro hx
        have := huniform x hx
        omega
      have hrel : P.toSetoid.r x (x + 1) := by
        by_contra h
        apply hxnot
        simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      have hnext : e (i, 1) = x + 1 := by
        apply Fin.ext
        simp [e, x, finProdFinEquiv, finRotate_apply, Fin.add_def]
        congr 1
        omega
      rw [show e (i, 0) = x by rfl, hnext]
      exact hrel
    have hmem (i : Fin n) (j : Fin 2) :
        e (i, j) ∈ fiber ↔ i ∈ base := by
      fin_cases j
      · simp [fiber, base]
      · simp only [fiber, base, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => Quotient.sound (hpair i) |>.trans h,
          fun h => (Quotient.sound (hpair i)).symm.trans h⟩
    have heq : fiber.card = (base ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      symm
      exact Finset.card_equiv e fun ij => by simp [hmem]
    rw [heq, Finset.card_product]
    simp
  · let e : Fin n × Fin 2 ≃ Fin (2 * n) :=
      finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))
    let base := Finset.univ.filter fun i : Fin n =>
      Quotient.mk'' (e (i, 0)) = C
    have hpair (i : Fin n) : P.toSetoid.r (e (i, 0)) (e (i, 1)) := by
      let x : Fin (2 * n) := e (i, 0)
      have hxval : x.val % 2 = 0 := by
        simp [x, e, finProdFinEquiv]
      have hxnot : x ∉ cycleBoundaryCuts P := by
        intro hx
        have := huniform x hx
        omega
      have hrel : P.toSetoid.r x (x + 1) := by
        by_contra h
        apply hxnot
        simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h
      have hnext : e (i, 1) = x + 1 := by
        apply Fin.ext
        have hi : 2 * i.val + 1 < 2 * n := by omega
        simp [e, x, finProdFinEquiv, Fin.add_def, Nat.mod_eq_of_lt hi]
        omega
      rw [show e (i, 0) = x by rfl, hnext]
      exact hrel
    have hmem (i : Fin n) (j : Fin 2) :
        e (i, j) ∈ fiber ↔ i ∈ base := by
      fin_cases j
      · simp [fiber, base]
      · simp only [fiber, base, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => Quotient.sound (hpair i) |>.trans h,
          fun h => (Quotient.sound (hpair i)).symm.trans h⟩
    have heq : fiber.card = (base ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      symm
      exact Finset.card_equiv e fun ij => by simp [hmem]
    rw [heq, Finset.card_product]
    simp

private theorem mixedBoundaryCuts_of_oddCycleBlock {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (hodd : ∃ C : Quotient P.toSetoid,
      (Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2) = 1) :
    (∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 0) ∧
      ∃ c ∈ cycleBoundaryCuts P, c.val % 2 = 1 := by
  by_contra hnotMixed
  have hcuts : cycleBoundaryCuts P ≠ ∅ := by
    intro hcuts
    obtain ⟨u, v, huv⟩ := hnontrivial
    exact huv ((cycleBoundaryCuts_eq_empty_iff (by omega) P).mp hcuts u v)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hcuts
  obtain ⟨C, hC⟩ := hodd
  have hcParity : c.val % 2 = 0 ∨ c.val % 2 = 1 := by omega
  rcases hcParity with hcEven | hcOdd
  · have hnoOdd : ¬ ∃ d ∈ cycleBoundaryCuts P, d.val % 2 = 1 := by
      intro h
      exact hnotMixed ⟨⟨c, hc, hcEven⟩, h⟩
    have huniform : ∀ d ∈ cycleBoundaryCuts P, d.val % 2 = 0 := by
      intro d hd
      have hdParity : d.val % 2 = 0 ∨ d.val % 2 = 1 := by omega
      rcases hdParity with h | h
      · exact h
      · exact (hnoOdd ⟨d, hd, h⟩).elim
    have := cycleBlock_even_of_uniformBoundaryCuts P 0 (Or.inl rfl) huniform C
    omega
  · have hnoEven : ¬ ∃ d ∈ cycleBoundaryCuts P, d.val % 2 = 0 := by
      intro h
      exact hnotMixed ⟨h, ⟨c, hc, hcOdd⟩⟩
    have huniform : ∀ d ∈ cycleBoundaryCuts P, d.val % 2 = 1 := by
      intro d hd
      have hdParity : d.val % 2 = 0 ∨ d.val % 2 = 1 := by omega
      rcases hdParity with h | h
      · exact (hnoEven ⟨d, hd, h⟩).elim
      · exact h
    have := cycleBlock_even_of_uniformBoundaryCuts P 1 (Or.inr rfl) huniform C
    omega

/- An arc whose two actual boundary cuts have opposite parities has odd size.
   It is a disjoint union of whole connected blocks, so at least one of those
   actual blocks must have odd cardinality. -/
private theorem oddCycleBlock_of_crownCycleCompatible {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (hcompatible : crownCycleCompatible P) :
    ∃ C : Quotient P.toSetoid,
      (Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2) = 1 := by
  classical
  obtain ⟨⟨e, heCut, heEven⟩, ⟨o, hoCut, hoOdd⟩⟩ :=
    mixedBoundaryCuts_of_crownCycleCompatible hn P hnontrivial hcompatible
  have heo : e ≠ o := by
    intro h
    subst o
    omega
  let a := min e o
  let b := max e o
  have hneVal : e.val ≠ o.val := fun h => heo (Fin.ext h)
  have hab : a < b := by
    simp only [a, b, min_def, max_def]
    split_ifs <;> omega
  have ha : a ∈ cycleBoundaryCuts P := by
    by_cases h : e ≤ o <;> simp [a, min_def, h, heCut, hoCut]
  have hb : b ∈ cycleBoundaryCuts P := by
    by_cases h : e ≤ o <;> simp [b, max_def, h, heCut, hoCut]
  have hpar : a.val % 2 ≠ b.val % 2 := by
    simp only [a, b, min_def, max_def]
    split_ifs <;> omega
  let arc : Finset (Fin (2 * n)) := Finset.Ioc a b
  have hArcOdd : arc.card % 2 = 1 := by
    have hcard : arc.card = b.val - a.val := by simp [arc]
    rw [hcard]
    have haMod : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
    have hbMod : b.val % 2 = 0 ∨ b.val % 2 = 1 := by omega
    rcases haMod with h0 | h1 <;> rcases hbMod with h2 | h3 <;> omega
  by_contra hnone
  have hEven (C : Quotient P.toSetoid) :
      ((Finset.univ.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card % 2) = 0 := by
    have hcard : Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} =
        (Finset.univ.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext v
      simp
    have hlt : ((Finset.univ.filter fun v : Fin (2 * n) =>
        Quotient.mk'' v = C).card % 2) < 2 := Nat.mod_lt _ (by omega)
    have hne : Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2 ≠ 1 :=
      fun hc => hnone ⟨C, hc⟩
    rw [hcard] at hne
    omega
  have hFiberEven (C : Quotient P.toSetoid) :
      ((arc.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card % 2) = 0 := by
    by_cases hex : ∃ v : Fin (2 * n), v ∈ arc ∧ Quotient.mk'' v = C
    · obtain ⟨v, hvArc, hvC⟩ := hex
      have heq : arc.filter (fun w : Fin (2 * n) => Quotient.mk'' w = C) =
          Finset.univ.filter (fun w : Fin (2 * n) => Quotient.mk'' w = C) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hwC
          have hrel : P.toSetoid.r v w := Quotient.exact (hvC.trans hwC.symm)
          have hww : (a.val < v.val ∧ v.val ≤ b.val) ↔
              (a.val < w.val ∧ w.val ≤ b.val) :=
            cyclePartitionBlock_arc_constant (by omega) P a b hab ha hb v w hrel
          exact ⟨(by simpa [arc] using hww.mp (by simpa [arc] using hvArc)), hwC⟩
      rw [heq]
      exact hEven C
    · have heq : arc.filter (fun v : Fin (2 * n) => Quotient.mk'' v = C) = ∅ := by
        ext v
        simpa [Finset.mem_filter] using
          (show ¬ (v ∈ arc ∧ Quotient.mk'' v = C) from
            fun hv => hex ⟨v, hv.1, hv.2⟩)
      simp [heq]
  have hsum : arc.card = ∑ C : Quotient P.toSetoid,
      (arc.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := arc) (t := Finset.univ)
      (f := fun v : Fin (2 * n) => (Quotient.mk'' v : Quotient P.toSetoid))
      (by simp)
  have hsumEven : (∑ C : Quotient P.toSetoid,
      (arc.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card) % 2 = 0 := by
    have aux (s : Finset (Quotient P.toSetoid)) :
        (∑ C ∈ s, (arc.filter fun v : Fin (2 * n) => Quotient.mk'' v = C).card) % 2 = 0 := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert C s hCs ih =>
          simp only [Finset.sum_insert hCs]
          have hC := hFiberEven C
          omega
    exact aux Finset.univ
  rw [hsum] at hArcOdd
  omega

/-- Source Lemma 3.2: a connected partition of the actual crown cycle with at
    least two blocks is compatible exactly when one actual block has odd size. -/
theorem crownCycleCompatible_iff_exists_oddBlock {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v) :
    crownCycleCompatible P ↔
      ∃ C : Quotient P.toSetoid,
        (Set.ncard {v : Fin (2 * n) | Quotient.mk'' v = C} % 2) = 1 := by
  constructor
  · exact oddCycleBlock_of_crownCycleCompatible hn P hnontrivial
  · intro hodd
    exact crownCycleCompatible_of_mixedBoundaryCuts hn P
      (mixedBoundaryCuts_of_oddCycleBlock hn P hnontrivial hodd)

/- Restrict an actual augmented-crown CCP to its original vertices when the
   bottom and top blocks contain no original vertex. -/
private def crownVertexSetoid {n : ℕ} (P : CrownConnectedCompatiblePartition n) :
    Setoid (Fin (2 * n)) where
  r i j := P.toSetoid.r (.vertex i) (.vertex j)
  iseqv :=
    { refl := fun i => P.toSetoid.refl (.vertex i)
      symm := fun h => P.toSetoid.symm h
      trans := fun h₁ h₂ => P.toSetoid.trans h₁ h₂ }

private noncomputable def connectedCyclePartitionOfCrown {n : ℕ} (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∀ i, ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ∀ i, ¬ P.toSetoid.r (.vertex i) .top) :
    ConnectedCyclePartition (2 * n) where
  toSetoid := crownVertexSetoid P
  connected := by
    intro u v huv
    let S : Set (Fin (2 * n)) := {j | P.toSetoid.r (.vertex u) (.vertex j)}
    have hconn := crownPartition_originalBlock_cycleGraph_connected hn P u
      (hbottom u) (htop u)
    let a : S := ⟨u, P.toSetoid.refl _⟩
    let b : S := ⟨v, huv⟩
    obtain ⟨w⟩ := hconn.preconnected a b
    let f : ((SimpleGraph.cycleGraph (2 * n)).induce S) →g
        cyclePartitionGraph (crownVertexSetoid P) :=
      { toFun := fun x => x.1
        map_rel' := by
          intro x y hxy
          exact ⟨P.toSetoid.trans (P.toSetoid.symm x.2) y.2, hxy⟩ }
    change Nonempty ((cyclePartitionGraph (crownVertexSetoid P)).Walk u v)
    have w' := w.map f
    change (cyclePartitionGraph (crownVertexSetoid P)).Walk u v at w'
    exact ⟨w'⟩

private theorem crownCycleCompatible_connectedCyclePartitionOfCrown {n : ℕ}
    (hn : 2 ≤ n) (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∀ i, ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ∀ i, ¬ P.toSetoid.r (.vertex i) .top) :
    crownCycleCompatible (connectedCyclePartitionOfCrown hn P hbottom htop) := by
  let Q := connectedCyclePartitionOfCrown hn P hbottom htop
  let q : Quotient Q.toSetoid → Quotient P.toSetoid :=
    Quotient.map (fun i => CrownAugmentedVertex.vertex i) (by
      intro a b hab
      exact hab)
  have hq_mk (i : Fin (2 * n)) :
      q (Quotient.mk'' i) = Quotient.mk'' (.vertex i) := rfl
  have hmapRel {C D : Quotient Q.toSetoid} (hCD : crownCycleBlockRel Q C D) :
      crownPartitionBlockRel P.toSetoid (q C) (q D) := by
    rcases hCD with ⟨i, j, hi, hj, hij⟩
    refine ⟨.vertex i, .vertex j, ?_, ?_, Or.inr hij⟩
    · rw [← hq_mk, hi]
    · rw [← hq_mk, hj]
  have hmapLE {C D : Quotient Q.toSetoid} (hCD : crownCycleBlockLE Q C D) :
      crownPartitionBlockLE P.toSetoid (q C) (q D) := by
    induction hCD with
    | refl => exact Relation.ReflTransGen.refl
    | tail hCE hED ih => exact ih.tail (hmapRel hED)
  have hqInjective : Function.Injective q := by
    intro C D hCD
    revert hCD
    refine Quotient.inductionOn₂ C D ?_
    intro i j hij
    apply Quotient.sound
    change (Quotient.mk'' (.vertex i) : Quotient P.toSetoid) =
      Quotient.mk'' (.vertex j) at hij
    change P.toSetoid.r (.vertex i) (.vertex j)
    exact @Quotient.exact _ P.toSetoid _ _ hij
  intro C D hCD hDC
  apply hqInjective
  exact P.compatible (hmapLE hCD) (hmapLE hDC)

/- For an actual CCP with singleton augmented endpoint blocks, nontriviality forces
   cyclic boundaries of both parities.  This is the actual-partition half of the
   source's odd-block criterion before boundary gaps are converted to block sizes. -/
private theorem mixedBoundaryCuts_of_crownPartition {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∀ i, ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ∀ i, ¬ P.toSetoid.r (.vertex i) .top)
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r (.vertex u) (.vertex v)) :
    let Q := connectedCyclePartitionOfCrown hn P hbottom htop
    (∃ c ∈ cycleBoundaryCuts Q, c.val % 2 = 0) ∧
      ∃ c ∈ cycleBoundaryCuts Q, c.val % 2 = 1 := by
  let Q := connectedCyclePartitionOfCrown hn P hbottom htop
  exact mixedBoundaryCuts_of_crownCycleCompatible hn Q hnontrivial
    (crownCycleCompatible_connectedCyclePartitionOfCrown hn P hbottom htop)

/- Compatibility and nontriviality exclude both the no-cut and singleton-cut
   exceptions.  This is the cardinality form used by the marked-cut count. -/
theorem cycleBoundaryCuts_card_ge_two_of_crownCycleCompatible
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (P : ConnectedCyclePartition (2 * n))
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r u v)
    (hcompatible : crownCycleCompatible P) :
    2 ≤ (cycleBoundaryCuts P).card := by
  obtain ⟨⟨ce, hce, heven⟩, ⟨co, hco, hodd⟩⟩ :=
    mixedBoundaryCuts_of_crownCycleCompatible hn P hnontrivial hcompatible
  have hne : ce ≠ co := by
    intro h
    subst co
    omega
  have hpair : ({ce, co} : Finset (Fin (2 * n))) ⊆ cycleBoundaryCuts P := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hce
    · exact hco
  have hcard : ({ce, co} : Finset (Fin (2 * n))).card = 2 := by
    simp [hne]
  have hle := Finset.card_le_card hpair
  simpa [hcard] using hle

private theorem cycleBoundaryCuts_card_ge_two_of_crownPartition
    {n : ℕ} [NeZero (2 * n)] (hn : 2 ≤ n)
    (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∀ i, ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ∀ i, ¬ P.toSetoid.r (.vertex i) .top)
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r (.vertex u) (.vertex v)) :
    let Q := connectedCyclePartitionOfCrown hn P hbottom htop
    2 ≤ (cycleBoundaryCuts Q).card := by
  let Q := connectedCyclePartitionOfCrown hn P hbottom htop
  exact cycleBoundaryCuts_card_ge_two_of_crownCycleCompatible hn Q hnontrivial
    (crownCycleCompatible_connectedCyclePartitionOfCrown hn P hbottom htop)

/-- An actual augmented-crown CCP with singleton bottom and top blocks and at
    least two original-vertex blocks has an odd original-vertex block, distinct
    from both augmented endpoint blocks. -/
theorem crownPartition_exists_oddOriginalBlock {n : ℕ} [NeZero (2 * n)]
    (hn : 2 ≤ n) (P : CrownConnectedCompatiblePartition n)
    (hbottom : ∀ i, ¬ P.toSetoid.r (.vertex i) .bottom)
    (htop : ∀ i, ¬ P.toSetoid.r (.vertex i) .top)
    (hnontrivial : ∃ u v, ¬ P.toSetoid.r (.vertex u) (.vertex v)) :
    ∃ C : Quotient P.toSetoid,
      C ≠ crownPartitionBottomBlock P ∧
      C ≠ crownPartitionTopBlock P ∧
      (Set.ncard {i : Fin (2 * n) | Quotient.mk'' (.vertex i) = C} % 2) = 1 := by
  let Q := connectedCyclePartitionOfCrown hn P hbottom htop
  have hcompatible : crownCycleCompatible Q :=
    crownCycleCompatible_connectedCyclePartitionOfCrown hn P hbottom htop
  obtain ⟨C, hC⟩ :=
    (crownCycleCompatible_iff_exists_oddBlock hn Q hnontrivial).mp hcompatible
  revert hC
  refine Quotient.inductionOn C ?_
  intro i hi
  refine ⟨Quotient.mk'' (.vertex i), ?_, ?_, ?_⟩
  · intro h
    exact hbottom i (@Quotient.exact _ P.toSetoid _ _ h)
  · intro h
    exact htop i (@Quotient.exact _ P.toSetoid _ _ h)
  · have hset :
        {v : Fin (2 * n) | (Quotient.mk'' v : Quotient Q.toSetoid) = Quotient.mk'' i} =
          {v : Fin (2 * n) |
            (Quotient.mk'' (.vertex v) : Quotient P.toSetoid) = Quotient.mk'' (.vertex i)} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        apply Quotient.sound
        exact @Quotient.exact _ Q.toSetoid _ _ h
      · intro h
        apply Quotient.sound
        exact @Quotient.exact _ P.toSetoid _ _ h
    rwa [hset] at hi

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration
