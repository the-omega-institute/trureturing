/- GID: D5/S3/Arith/FibonacciAtomic/Scale40BetaGainChildren
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual leaf reports fix beta resources in literal Fibonacci blocks. -/

import D5.S3.Arith.FibonacciAtomic.ActualStrictHistoryCapacity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Scale40BetaGainChildren

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout Positive)
open ActualImageSevenLeafSeparation (thirdImage E A C Nonconflict leafAddresses leafLabel)
open ActualLeafHistoryRigidity
open ActualStrictHistoryCapacity (queue reports)
open ActualJointResponseCostCore (Recipe routeTrace)
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)

/-- The actual beta frontier, using the existing native leaf-address enumeration. -/
def betaLeaves (P : Source) : Finset Address :=
  (leafAddresses P).filter fun u => readout u P = .beta

/-- Only the five-row decoder's actual leaf reports contribute fixed beta addresses. -/
def psi (H : Hist (fun _ : Address => Reply)) : Finset Address :=
  (forcedBlocks (reports H)).biUnion fun b =>
    (betaLeaves b.2.tree).image (b.1 ++ ·)

/-- At any actual strict split with a leaf child, the fixed beta resource grows by
one, two or three. Unit growth is exactly completion of a C whose left A was fixed. -/
theorem result {m : Nat} (F : Fin m → Source) (S : Finset (Fin m))
    (hpos : ∀ i ∈ S, Positive (F i))
    (H : Hist (fun _ : Address => Reply)) (u : Address) (y : Reply)
    (hy : y = .alpha ∨ y = .beta)
    (hleaf : ∃ i ∈ queue F S H, readout u (F i) = y)
    (hstrict : 2 ≤ ((queue F S H).image (fun i => readout u (F i))).card) :
    (∀ i ∈ queue F S H, psi H ⊆ betaLeaves (F i)) ∧
    let w := (psi (H ++ [⟨u, y⟩]) \ psi H).card
    (w = 1 ∨ w = 2 ∨ w = 3) ∧
    (w = 1 ↔ ∃ v : Address, decodeBlock u y = some (v, BlockKind.c) ∧
      (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H)) := by
  classical
  rcases actual_address_geometry with
    ⟨classify, small, rows, decode, blocks, overlap, recovery, absent,
      leafPrefix, contexts, gammaMem, gammaInv, oneAlpha, readAt,
      subtreeAppend, leafSubtree, alphaMem⟩
  have betaMem (P : Source) (x : Address) :
      x ∈ betaLeaves P ↔ readout x P = .beta := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro h
      refine Finset.mem_filter.mpr ⟨?_, h⟩
      exact (ActualImageSevenLeafSeparation.seven_leaf_separation.1 P).2 x |>.mpr
        ⟨false, by simp only [leafLabel, h]⟩
  have compatible (i : Fin m) (hi : i ∈ queue F S H) : Compatible (reports H) (F i) := by
    rcases Finset.mem_filter.mp hi with ⟨hiS, hmatch⟩
    refine ⟨hpos i hiS, ?_⟩
    intro x z hx _
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hx
    cases heq
    exact hmatch e he
  have fixed (i : Fin m) (hi : i ∈ queue F S H) := (blocks _ _ (compatible i hi)).1
  have betaFixed (i : Fin m) (hi : i ∈ queue F S H) : psi H ⊆ betaLeaves (F i) := by
    intro x hx
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    apply (betaMem _ _).mpr
    rw [readAt, fixed i hi b hb]
    exact (betaMem _ _).mp hz
  refine ⟨betaFixed, ?_⟩
  obtain ⟨i, hi, hiy⟩ := hleaf
  obtain ⟨b, hb, _⟩ := decode (F i) (compatible i hi).1 u y hy hiy
  rcases b with ⟨v, k⟩
  rcases hb with ⟨hd, hnew⟩
  have decoderPrefix (x : Address) (z : Reply) (b : Address × BlockKind)
      (h : decodeBlock x z = some b) : b.1.IsPrefix x := by
    cases z with
    | branch => simp [decodeBlock] at h
    | absent => simp [decodeBlock] at h
    | beta =>
      cases hr : x.reverse with
      | nil => simp [decodeBlock, hr] at h
      | cons d t =>
        cases d with
        | true =>
          simp only [decodeBlock, hr, Option.some.injEq] at h
          subst b
          refine ⟨[true], ?_⟩
          simpa using (congrArg List.reverse hr).symm
        | false =>
          cases t with
          | nil => simp [decodeBlock, hr] at h
          | cons d t =>
            cases d with
            | false =>
              simp only [decodeBlock, hr, Option.some.injEq] at h
              subst b
              refine ⟨[false, false], ?_⟩
              simpa [List.reverse_cons, List.append_assoc] using (congrArg List.reverse hr).symm
            | true =>
              simp only [decodeBlock, hr, Option.some.injEq] at h
              subst b
              refine ⟨[true, false], ?_⟩
              simpa [List.reverse_cons, List.append_assoc] using (congrArg List.reverse hr).symm
    | alpha =>
      cases hr : x.reverse with
      | nil => simp [decodeBlock, hr] at h
      | cons d t =>
        cases d with
        | false => simp [decodeBlock, hr] at h
        | true =>
          cases t with
          | nil => simp [decodeBlock, hr] at h
          | cons d t =>
            cases d with
            | false =>
              simp only [decodeBlock, hr, Option.some.injEq] at h
              subst b
              refine ⟨[false, true], ?_⟩
              simpa [List.reverse_cons, List.append_assoc] using (congrArg List.reverse hr).symm
            | true =>
              simp only [decodeBlock, hr, Option.some.injEq] at h
              subst b
              refine ⟨[true, true], ?_⟩
              simpa [List.reverse_cons, List.append_assoc] using (congrArg List.reverse hr).symm
  obtain ⟨z, huz⟩ := decoderPrefix u y (v, k) hd
  have notFixed : ¬ ∀ j ∈ queue F S H, subtree v (F j) = some k.tree := by
    intro hall
    have hconst : ∀ j ∈ queue F S H, readout u (F j) = y := by
      intro j hj
      rw [← huz, readAt, hall j hj]
      have hh := hiy
      rw [← huz, readAt, hnew] at hh
      exact hh
    have hsub : (queue F S H).image (fun j => readout u (F j)) ⊆ {y} := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      simpa using hconst j hj
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have kindInject : Function.Injective BlockKind.tree := by
    intro aKind bKind h
    cases aKind <;> cases bKind <;> try rfl
    all_goals
      have hh := congrArg FreeMagma.length h
      norm_num [BlockKind.tree, A, C, E, FreeMagma.length] at hh
  have oldOverlap (b : Address × BlockKind) (hb : b ∈ forcedBlocks (reports H)) :
      (¬ v.IsPrefix b.1 ∧ ¬ b.1.IsPrefix v) ∨
      (k = .c ∧ b = (v ++ [false], .a)) := by
    have ht (q : BlockKind) : q.tree = A ∨ q.tree = C := by cases q <;> simp [BlockKind.tree]
    rcases overlap (F i) v b.1 k.tree b.2.tree (ht k) (ht b.2)
      hnew (fixed i hi b hb) with same | incomparable | leftA | parentC
    · exfalso
      apply notFixed
      intro j hj
      rw [same.1, same.2]
      exact fixed j hj b hb
    · exact Or.inl incomparable
    · have hk : k = .c := kindInject (leftA.1.trans (show C = BlockKind.c.tree from rfl))
      have hl : b.2 = .a := kindInject (leftA.2.1.trans (show A = BlockKind.a.tree from rfl))
      exact Or.inr ⟨hk, Prod.ext leftA.2.2 hl⟩
    · exfalso
      apply notFixed
      intro j hj
      rw [parentC.2.2, subtreeAppend, fixed j hj b hb, parentC.2.1]
      simp only [Option.bind_some, C, subtree]
      exact congrArg some parentC.1.symm
  have betaLiteral : betaLeaves A = {[false, false], [true]} ∧
      betaLeaves C = {[false, false, false], [false, true], [true, false]} := by
    constructor <;> decide
  have addBlock : forcedBlocks (reports (H ++ [⟨u, y⟩])) =
      insert (v, k) (forcedBlocks (reports H)) := by
    simp [reports, forcedBlocks, List.filterMap_append, hd, Finset.union_comm]
  have psiAppend : psi (H ++ [⟨u, y⟩]) =
      (betaLeaves k.tree).image (v ++ ·) ∪ psi H := by
    simp only [psi, addBlock, Finset.biUnion_insert, Prod.fst, Prod.snd]
  have incomparableLeaves (b : Address × BlockKind)
      (hn : ¬ v.IsPrefix b.1 ∧ ¬ b.1.IsPrefix v) (x : Address)
      (hx : x ∈ (betaLeaves k.tree).image (v ++ ·)) :
      x ∉ (betaLeaves b.2.tree).image (b.1 ++ ·) := by
    intro hbx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hbx
    have hv : v.IsPrefix x := ⟨a, ha⟩
    have hb : b.1.IsPrefix x := ⟨c, hc⟩
    exact (List.prefix_or_prefix_of_prefix hv hb).elim hn.1 hn.2
  have overlapMem (x : Address) (hx : x ∈ (betaLeaves k.tree).image (v ++ ·)) :
      x ∈ psi H ↔ k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H) ∧
        x ∈ ({[false, false, false], [false, true]} : Finset Address).image (v ++ ·) := by
    constructor
    · intro hold
      obtain ⟨b, hb, hbx⟩ := Finset.mem_biUnion.mp hold
      rcases oldOverlap b hb with hn | ⟨hk, he⟩
      · exact False.elim (incomparableLeaves b hn x hx hbx)
      · subst b
        refine ⟨hk, hb, ?_⟩
        simpa [BlockKind.tree, betaLiteral.1, Finset.image_insert, List.append_assoc] using hbx
    · rintro ⟨hk, hb, hx⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨(v ++ [false], .a), hb, ?_⟩
      simpa [BlockKind.tree, betaLiteral.1, Finset.image_insert, List.append_assoc] using hx
  have prefixInject : Function.Injective (v ++ · : Address → Address) :=
    fun _ _ h => List.append_cancel_left h
  have gainSet : psi (H ++ [⟨u, y⟩]) \ psi H =
      (if k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H) then
        ({[true, false]} : Finset Address).image (v ++ ·)
      else (betaLeaves k.tree).image (v ++ ·)) := by
    rw [psiAppend, Finset.union_sdiff_right]
    by_cases hk : k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H)
    · rw [if_pos hk]
      rcases hk with ⟨rfl, hleft⟩
      ext x
      rw [Finset.mem_sdiff]
      by_cases hx : x ∈ (betaLeaves BlockKind.c.tree).image (v ++ ·)
      · rw [overlapMem x hx]
        simp only [hx, hleft, true_and]
        simp only [BlockKind.tree, betaLiteral.2, Finset.mem_image, Finset.mem_insert,
          Finset.mem_singleton] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
          prefixInject.eq_iff]
        rcases ha with rfl | rfl | rfl <;> simp
      · have hn : x ∉ ({[true, false]} : Finset Address).image (v ++ ·) := by
          intro h
          apply hx
          exact Finset.image_subset_image (by simp [BlockKind.tree, betaLiteral.2]) h
        simp only [hx, false_and, hn]
    · rw [if_neg hk]
      ext x
      rw [Finset.mem_sdiff]
      constructor
      · exact And.left
      · intro hx
        refine ⟨hx, ?_⟩
        intro hold
        have hh := (overlapMem x hx).mp hold
        exact hk ⟨hh.1, hh.2.1⟩
  have gainCard : (psi (H ++ [⟨u, y⟩]) \ psi H).card =
      if k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H) then 1
      else if k = .a then 2 else 3 := by
    rw [gainSet]
    split
    · simp only [Finset.card_image_of_injective _ prefixInject, Finset.card_singleton]
    · rw [Finset.card_image_of_injective _ prefixInject]
      cases k <;> simp [BlockKind.tree, betaLiteral]
  have unitIff : (∃ v' : Address, decodeBlock u y = some (v', BlockKind.c) ∧
      (v' ++ [false], BlockKind.a) ∈ forcedBlocks (reports H)) ↔
      k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H) := by
    constructor
    · rintro ⟨v', hd', hleft⟩
      have he := Option.some.inj (hd.symm.trans hd')
      have hv : v = v' := congrArg Prod.fst he
      have hk : k = .c := congrArg Prod.snd he
      subst v'
      exact ⟨hk, hleft⟩
    · rintro ⟨hk, hleft⟩
      exact ⟨v, by simpa only [hk] using hd, hleft⟩
  dsimp only
  rw [gainCard, unitIff]
  by_cases hk : k = .c ∧ (v ++ [false], BlockKind.a) ∈ forcedBlocks (reports H)
  · simp only [hk, if_pos, true_and, Nat.reduceEqDiff, or_true, true_or]
  · rw [if_neg hk]
    cases k with
    | a => simp
    | c =>
      have hn : (v ++ [false], BlockKind.a) ∉ forcedBlocks (reports H) :=
        fun hl => hk ⟨rfl, hl⟩
      simp [hn]

end D5.S3.Arith.FibonacciAtomic.Scale40BetaGainChildren
