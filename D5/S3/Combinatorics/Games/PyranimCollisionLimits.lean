/- GID: D5/S3/Combinatorics/Games/PyranimCollisionLimits
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Games/PyranimCollisionLimits
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rank-block estimates and the root and zero limits for Pyranim collisions. -/

/-
admission_basis: open-problem-resolution (#33556; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/33619
-/

import D5.S3.Combinatorics.Games.PyranimCollisionRoot
import Mathlib.Data.Finset.SDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Rank-block estimates and the root and zero limits for Pyranim collisions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

open Filter Topology

namespace D5.S3.Combinatorics.Games.Pyranim

section

variable {n m : ℕ}

/-- Complete legal paths, with every step counted and the empty ideal as endpoint. -/
private inductive CompletePath : Stable n → ℕ → Prop
  | empty : CompletePath (emptyStable n) 0
  | step {I J : Stable n} {k : ℕ} :
      LegalOption I J → CompletePath J k → CompletePath I (k + 1)

private theorem exists_visible_maximal {I : Stable n} (h : I.val.Nonempty) :
    ∃ c, Visible I c ∧ ∀ u ∈ I.val, c ≤ u → u = c := by
  classical
  letI : Fintype (Interval n) := Fintype.ofFinite (Interval n)
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image I.val.toFinset
    (fun c => c.right - c.left) (Set.toFinset_nonempty.mpr h)
  have htop : ∀ u ∈ I.val, c ≤ u → u = c := by
    intro u hu hcu
    have hm := hmax u (Set.mem_toFinset.mpr hu)
    obtain ⟨hl, hr⟩ := hcu
    have := c.left_le_right
    apply Interval.ext <;> omega
  refine ⟨c, (visible_iff_covers _ _).mpr ⟨Set.mem_toFinset.mp hc, ?_⟩, htop⟩
  rintro ⟨u, _, hu, _, _⟩
  exact hu.2.1.ne (htop u hu.1 hu.2.1.le).symm

private theorem completePath_of_gameIso {I : Stable n} {J : Stable m}
    (h : GameIso I J) {k : ℕ} (p : CompletePath I k) : CompletePath J k := by
  induction p generalizing J with
  | empty =>
    obtain ⟨e, _⟩ := (gameIso_iff _ _).mp h
    have hJ : J = emptyStable m := by
      classical
      by_contra hJ
      obtain ⟨c, hc⟩ : ∃ c : Interval m, c ∈ J.val := by
        by_contra! h
        exact hJ (Subtype.ext (Set.eq_empty_iff_forall_notMem.mpr h))
      obtain ⟨u, hv, _⟩ := exists_visible_maximal ⟨c, hc⟩
      obtain ⟨_, hz, _⟩ := (e.symm ⟨removeChip J u, u, hv, rfl⟩).property
      exact hz.1
    rw [hJ]
    exact CompletePath.empty
  | step hstep _ ih =>
    obtain ⟨e, he⟩ := (gameIso_iff _ _).mp h
    let a := e ⟨_, hstep⟩
    exact CompletePath.step a.property (ih (he ⟨_, hstep⟩))

private theorem completePath_le_chipCount {I : Stable n} {k : ℕ} (p : CompletePath I k) :
    k ≤ chipCount I := by
  induction p with
  | empty => omega
  | step h _ ih => exact Nat.succ_le_of_lt (ih.trans_lt (chipCount_lt_of_option h))

private theorem completePath_chipCount (I : Stable n) : CompletePath I (chipCount I) := by
  induction I using (legalOption_wellFounded n).induction with
  | h I ih =>
    classical
    by_cases hI : I.val.Nonempty
    · obtain ⟨c, hc, hmax⟩ := exists_visible_maximal hI
      have hs : LegalOption I (removeChip I c) := ⟨c, hc, rfl⟩
      have he : chipCount (removeChip I c) + 1 = chipCount I := by
        letI := Fintype.ofFinite (Interval n)
        have hsets : (removeChip I c).val.toFinset = I.val.toFinset.erase c := by
          ext u
          simp only [Set.mem_toFinset, Finset.mem_erase]
          change (u ∈ I.val ∧ ¬ c ≤ u) ↔ u ≠ c ∧ u ∈ I.val
          exact ⟨fun ⟨hu, h⟩ => ⟨fun hEq => h (hEq ▸ le_rfl), hu⟩,
            fun ⟨hne, hu⟩ => ⟨hu, fun h => hne (hmax u hu h)⟩⟩
        unfold chipCount
        rw [hsets, Finset.card_erase_add_one (Set.mem_toFinset.mpr hc.1)]
      rw [← he]
      exact CompletePath.step hs (ih _ hs)
    · have he : I = emptyStable n := Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hI)
      subst I
      have hz : chipCount (emptyStable n) = 0 := by
        classical
        letI : Fintype (Interval n) := Fintype.ofFinite _
        unfold chipCount
        apply Finset.card_eq_zero.mpr
        ext c
        constructor
        · intro hc
          rw [Set.mem_toFinset] at hc
          exact hc.elim
        · intro hc
          exact (Finset.notMem_empty _ hc).elim
      rw [hz]
      exact CompletePath.empty

private theorem chipCount_eq_of_gameIso {I : Stable n} {J : Stable m} (h : GameIso I J) :
    chipCount I = chipCount J :=
  Nat.le_antisymm
    (completePath_le_chipCount (completePath_of_gameIso h (completePath_chipCount I)))
    (completePath_le_chipCount
      (completePath_of_gameIso (gameIso_symm I J h) (completePath_chipCount J)))

end

section

open DyckStep

private def wordBlock (M k : ℕ) (w : List DyckStep) : List DyckStep :=
  (w.drop (k * M)).take M

private theorem wordBlock_split (M k : ℕ) (w : List DyckStep) :
    w = w.take (k * M) ++ wordBlock M k w ++ w.drop ((k + 1) * M) := by
  unfold wordBlock
  rw [Nat.succ_mul, ← List.drop_drop, List.append_assoc, List.take_append_drop,
    List.take_append_drop]

private theorem concat_wordBlock (M k : ℕ) (pre w post : List DyckStep)
    (hp : pre.length = k * M) (hw : w.length = M) :
    wordBlock M k (pre ++ w ++ post) = w := by
  unfold wordBlock
  rw [List.append_assoc, ← hp, List.drop_left, ← hw,
    List.take_append_of_le_length (by rfl), List.take_length]

private theorem early_wordBlock_eq {M j k : ℕ} (h : j < k) (pre x y : List DyckStep)
    (hp : pre.length = k * M) :
    wordBlock M j (pre ++ x) = wordBlock M j (pre ++ y) := by
  unfold wordBlock
  rw [List.take_drop, List.take_drop]
  have hj : j * M + M ≤ pre.length := by
    rw [hp, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ h
  rw [List.take_append_of_le_length hj, List.take_append_of_le_length hj]

private abbrev rankBlockWidth (L : ℕ) := 2 * (L + 1)

private def RankMark (L k : ℕ) (w : List DyckStep) : Prop :=
  ∃ i : Fin (L + 1), wordBlock (rankBlockWidth L) k w = (rankBlock L i).toList

private def HasRankMark (L q : ℕ) (w : List DyckStep) : Prop :=
  ∃ k : ℕ, k < q ∧ RankMark L k w

private theorem rankBlock_toList_injective (L : ℕ) :
    Function.Injective (fun i : Fin (L + 1) => (rankBlock L i).toList) := by
  intro i j h
  have h' := congrArg (fun w : List DyckStep => (w.takeWhile (· == U)).length) h
  have ht (x : Fin (L + 1)) :
      ((rankBlock L x).toList.takeWhile (· == U)).length = x.val + 1 := by
    simp [rankBlock, List.append_assoc]
  rw [ht i, ht j] at h'
  exact Fin.ext (by omega)

private theorem unique_firstMark {L : ℕ} {w : List DyckStep} {k j : ℕ}
    (hk : RankMark L k w) (hj : RankMark L j w)
    (hmin : ∀ z < k, ¬ RankMark L z w) (hmin' : ∀ z < j, ¬ RankMark L z w) :
    k = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hmin' k h hk
  · exact hmin j h hj

/-- Changing the first marked block packs each marked rank fiber into the whole sample space
with a factor of L + 1, uniformly in the prescribed rank. -/
private theorem marked_rank_card_mul_le (n L q size : ℕ) (hfit : q * rankBlockWidth L ≤ 2 * (n + 1)) :
    (L + 1) * Nat.card {I : Stable n // chipCount I = size ∧
      HasRankMark L q (stableEquivDyck n I).val.toList} ≤ Nat.card (Stable n) := by
  classical
  let Fiber := {I : Stable n // chipCount I = size ∧
    HasRankMark L q (stableEquivDyck n I).val.toList}
  let p (I : Fiber) := stableEquivDyck n I.val
  let k (I : Fiber) := Nat.find I.property.2
  let pre (I : Fiber) := (p I).val.toList.take (k I * rankBlockWidth L)
  let post (I : Fiber) := (p I).val.toList.drop ((k I + 1) * rankBlockWidth L)
  have hk (I : Fiber) := Nat.find_spec I.property.2
  have hmin (I : Fiber) (j : ℕ) (hj : j < k I) : ¬ RankMark L j (p I).val.toList := by
    intro h
    exact (Nat.find_min I.property.2 hj) ⟨hj.trans (hk I).1, h⟩
  let old (I : Fiber) := Classical.choose (hk I).2
  have hpre (I : Fiber) : (pre I).length = k I * rankBlockWidth L := by
    have h := Nat.mul_le_mul_right (rankBlockWidth L) (hk I).1.le
    have hlen : (p I).val.toList.length = 2 * (n + 1) := by
      rw [← DyckWord.two_mul_semilength_eq_length, (p I).property]
    exact List.length_take_of_le (hlen ▸ h.trans hfit)
  have hp (I : Fiber) : (p I).val.toList = pre I ++ (rankBlock L (old I)).toList ++ post I := by
    have hold := Classical.choose_spec (hk I).2
    change wordBlock (rankBlockWidth L) (k I) (p I).val.toList = _ at hold
    rw [← hold]
    exact wordBlock_split _ _ _
  let f (x : Fin (L + 1) × Fiber) : DyckAt (n + 1) :=
    exchangeDyck (p x.2) (pre x.2) (post x.2) (rankBlock L (old x.2)) (rankBlock L x.1)
      (hp x.2) ((rankBlock_semilength L _).trans (rankBlock_semilength L _).symm)
  have hf (t : Fin (L + 1)) (I : Fiber) :
      (f (t,I)).val.toList = pre I ++ (rankBlock L t).toList ++ post I := rfl
  have hnew (t : Fin (L + 1)) (I : Fiber) : RankMark L (k I) (f (t,I)).val.toList :=
    ⟨t, (hf t I).symm ▸ concat_wordBlock _ _ _ _ _ (hpre I) (rankBlock_length L t)⟩
  have hminNew (t : Fin (L + 1)) (I : Fiber) (j : ℕ) (hj : j < k I) :
      ¬ RankMark L j (f (t,I)).val.toList := by
    unfold RankMark
    rw [hf, List.append_assoc, early_wordBlock_eq hj _ _
      ((rankBlock L (old I)).toList ++ post I) (hpre I), ← List.append_assoc, ← hp]
    exact hmin I j hj
  have hinj : Function.Injective f := by
    intro ⟨s,I⟩ ⟨t,J⟩ he
    have hw := congrArg (fun p : DyckAt (n + 1) => p.val.toList) he
    have hkEq : k I = k J :=
      unique_firstMark (hnew s I) (hw.symm ▸ hnew t J)
        (hminNew s I) (fun z hz => hw.symm ▸ hminNew t J z hz)
    have hblocks := congrArg (wordBlock (rankBlockWidth L) (k I)) hw
    rw [hf, hf, concat_wordBlock _ _ _ _ _ (hpre I) (rankBlock_length L s), hkEq,
      concat_wordBlock _ _ _ _ _ (hpre J) (rankBlock_length L t)] at hblocks
    have ht : s = t := rankBlock_toList_injective L hblocks
    subst t
    have hpreEq : pre I = pre J := by
      have h := congrArg (List.take (k I * rankBlockWidth L)) hw
      rw [hf, hf, List.append_assoc, List.append_assoc, ← hpre I, List.take_left,
        show (pre I).length = (pre J).length by rw [hpre, hpre, hkEq], List.take_left] at h
      exact h
    have hpostEq : post I = post J := by
      rw [hf, hf, hpreEq] at hw
      exact List.append_cancel_left hw
    have horient : old I = old J := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hlt := rankBlock_strict h (p I) (p J) (pre I) (post I) (hp I)
          (by rw [hpreEq, hpostEq]; exact hp J)
        change chipCount ((stableEquivDyck n).symm (stableEquivDyck n I.val)) <
          chipCount ((stableEquivDyck n).symm (stableEquivDyck n J.val)) at hlt
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, I.property.1, J.property.1] at hlt
        exact (lt_irrefl _ hlt)
      · have hlt := rankBlock_strict h (p J) (p I) (pre I) (post I)
          (by rw [hpreEq, hpostEq]; exact hp J) (hp I)
        change chipCount ((stableEquivDyck n).symm (stableEquivDyck n J.val)) <
          chipCount ((stableEquivDyck n).symm (stableEquivDyck n I.val)) at hlt
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, I.property.1, J.property.1] at hlt
        exact (lt_irrefl _ hlt)
    refine Prod.ext ?_ ?_
    · rfl
    · apply Subtype.ext
      apply (stableEquivDyck n).injective
      apply Subtype.ext
      apply DyckWord.ext
      exact (hp I).trans (by rw [hpreEq, hpostEq, horient, ← hp J])
  have hc := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_prod, Nat.card_fin, ← Nat.card_congr (stableEquivDyck n)] at hc
  exact hc

end

section

open DyckStep

private abbrev WordAt (m : ℕ) := {w : List DyckStep // w.length = m}

private noncomputable def wordAtEquiv (m : ℕ) : (Fin m → DyckStep) ≃ WordAt m :=
  Equiv.ofBijective (fun f => ⟨List.ofFn f, List.length_ofFn⟩)
    ⟨fun _ _ h => List.ofFn_injective (congrArg Subtype.val h), by
      rintro ⟨w, hw⟩
      subst m
      exact ⟨w.get, Subtype.ext (List.ofFn_get w)⟩⟩

private def stepEquivBool : DyckStep ≃ Bool where
  toFun | U => false | D => true
  invFun | false => U | true => D
  left_inv s := by cases s <;> rfl
  right_inv b := by cases b <;> rfl

private instance : Finite DyckStep :=
  Finite.of_injective stepEquivBool stepEquivBool.injective

instance (m : ℕ) : Finite (WordAt m) :=
  Finite.of_injective (wordAtEquiv m).symm (wordAtEquiv m).symm.injective

private theorem wordAt_card (m : ℕ) : Nat.card (WordAt m) = 2 ^ m := by
  rw [← Nat.card_congr (wordAtEquiv m), Nat.card_fun, Nat.card_fin, Nat.card_congr stepEquivBool]
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hb]

private theorem wordAt_card_ne_pivot {M : ℕ} (pivot : WordAt M) :
    Nat.card {w : WordAt M // w ≠ pivot} = 2 ^ M - 1 := by
  classical
  let eqType := {w : WordAt M // ¬ w ≠ pivot}
  let singleton : eqType ≃ Unit :=
    Equiv.ofBijective (fun _ => ()) ⟨fun a b _ =>
      Subtype.ext ((not_not.mp a.property).trans (not_not.mp b.property).symm),
      by intro _; exact ⟨⟨pivot, not_not.mpr rfl⟩, rfl⟩⟩
  have h := Nat.card_congr (Equiv.sumCompl (fun w : WordAt M => w ≠ pivot))
  change Nat.card ({w : WordAt M // w ≠ pivot} ⊕ eqType) = _ at h
  rw [Nat.card_sum, wordAt_card, Nat.card_congr singleton] at h
  have hon : Nat.card Unit = 1 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hon] at h
  omega

private abbrev AvoidingWords {M : ℕ} (pivot : WordAt M) (q r : ℕ) :=
  {w : WordAt (q * M + r) // ∀ k < q, wordBlock M k w.val ≠ pivot.val}

private theorem avoidingWords_card_le {M : ℕ} (pivot : WordAt M) (q r : ℕ) :
    Nat.card (AvoidingWords pivot q r) ≤ (2 ^ M - 1) ^ q * 2 ^ r := by
  induction q with
  | zero =>
    simp only [pow_zero, one_mul]
    have h := Nat.card_le_card_of_injective
      (fun w : AvoidingWords pivot 0 r => (⟨w.val.val, by simpa using w.val.property⟩ : WordAt r))
      (by intro a b h; exact Subtype.ext (Subtype.ext (congrArg
        (fun w : WordAt r => w.val) h)))
    exact h.trans_eq (wordAt_card r)
  | succ q ih =>
    let pre (w : AvoidingWords pivot (q + 1) r) : WordAt M :=
      ⟨w.val.val.take M, List.length_take_of_le (by
        rw [w.val.property, Nat.succ_mul]
        omega)⟩
    let suffix (w : AvoidingWords pivot (q + 1) r) : WordAt (q * M + r) :=
      ⟨w.val.val.drop M, by rw [List.length_drop, w.val.property, Nat.succ_mul]; omega⟩
    let f (w : AvoidingWords pivot (q + 1) r) :
        {u : WordAt M // u ≠ pivot} × AvoidingWords pivot q r :=
      (⟨pre w, fun h => w.property 0 (Nat.succ_pos q)
        (by simpa [wordBlock, pre] using congrArg Subtype.val h)⟩,
       ⟨suffix w, by
        intro k hk he
        apply w.property (k + 1) (Nat.succ_lt_succ hk)
        simpa [wordBlock, suffix, List.drop_drop, Nat.succ_mul, Nat.add_comm] using he⟩)
    have hf : Function.Injective f := by
      intro w z he
      have h₁ := congrArg (fun p : {u : WordAt M // u ≠ pivot} × AvoidingWords pivot q r =>
        p.1.val.val) he
      have h₂ := congrArg (fun p : {u : WordAt M // u ≠ pivot} × AvoidingWords pivot q r =>
        p.2.val.val) he
      change w.val.val.take M = z.val.val.take M at h₁
      change w.val.val.drop M = z.val.val.drop M at h₂
      exact Subtype.ext (Subtype.ext (by
        rw [← List.take_append_drop M w.val.val, h₁, h₂, List.take_append_drop]))
    calc
      _ ≤ Nat.card ({u : WordAt M // u ≠ pivot} × AvoidingWords pivot q r) :=
        Nat.card_le_card_of_injective f hf
      _ = (2 ^ M - 1) * Nat.card (AvoidingWords pivot q r) := by rw [Nat.card_prod, wordAt_card_ne_pivot]
      _ ≤ (2 ^ M - 1) * ((2 ^ M - 1) ^ q * 2 ^ r) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ', Nat.mul_assoc]

private abbrev rankSlots (n L : ℕ) := (2 * (n + 1)) / rankBlockWidth L

private abbrev rankTail (n L : ℕ) := (2 * (n + 1)) % rankBlockWidth L

private theorem rankSlots_width (n L : ℕ) :
    rankSlots n L * rankBlockWidth L + rankTail n L = 2 * (n + 1) := by
  simpa only [rankSlots, rankTail, Nat.mul_comm, Nat.add_comm] using
    Nat.mod_add_div (2 * (n + 1)) (rankBlockWidth L)

/-- Unmarked ideals inject into binary words omitting one fixed block in each slot. -/
private theorem noRankMark_card_le (n L : ℕ) :
    Nat.card {I : Stable n // ¬ HasRankMark L (rankSlots n L) (stableEquivDyck n I).val.toList} ≤
      (2 ^ rankBlockWidth L - 1) ^ rankSlots n L * 2 ^ rankTail n L := by
  let pivot : WordAt (rankBlockWidth L) := ⟨(rankBlock L 0).toList, rankBlock_length L 0⟩
  let f (I : {I : Stable n // ¬ HasRankMark L (rankSlots n L)
      (stableEquivDyck n I).val.toList}) : AvoidingWords pivot (rankSlots n L) (rankTail n L) :=
    ⟨⟨(stableEquivDyck n I.val).val.toList, by
      rw [← DyckWord.two_mul_semilength_eq_length, (stableEquivDyck n I.val).property, rankSlots_width]⟩,
      fun k hk he => I.property ⟨k, hk, 0, he⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply (stableEquivDyck n).injective
    apply Subtype.ext
    apply DyckWord.ext
    exact congrArg (fun w : AvoidingWords pivot (rankSlots n L) (rankTail n L) => w.val.val) he
  exact (Nat.card_le_card_of_injective f hf).trans (avoidingWords_card_le _ _ _)

end

section

open Filter Topology

private theorem collisionPairsEquivFibers_card (n : ℕ) [Fintype (Stable n)] :
    Nat.card (CollisionPairs n) =
      ∑ I : Stable n, Nat.card {J : Stable n // GameIso I J} := by
  let e : CollisionPairs n ≃ (Σ I : Stable n, {J : Stable n // GameIso I J}) :=
    ⟨fun ⟨⟨I,J⟩,h⟩ => ⟨I,J,h⟩, fun ⟨I,J,h⟩ => ⟨⟨I,J⟩,h⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_sigma]

end

section

open Filter Topology

def unmarkedBound (n L : ℕ) : ℕ :=
  (2 ^ rankBlockWidth L - 1) ^ rankSlots n L * 2 ^ rankTail n L

/-- A uniform class-size estimate for every width and every stable ideal.
The second term counts all binary words avoiding a prescribed block in every slot. -/
theorem gameIso_class_card_upper (n L : ℕ) (I : Stable n) :
    (Nat.card {J : Stable n // GameIso I J} : ℝ) ≤
      (Nat.card (Stable n) : ℝ) / ((L : ℝ) + 1) + unmarkedBound n L := by
  classical
  let Class := {J : Stable n // GameIso I J}
  let mark (J : Stable n) := HasRankMark L (rankSlots n L) (stableEquivDyck n J).val.toList
  let Good := {J : Class // mark J.val}
  let Bad := {J : Class // ¬ mark J.val}
  have he : Nat.card Class = Nat.card Good + Nat.card Bad := by
    rw [← Nat.card_congr (Equiv.sumCompl (fun J : Class => mark J.val)), Nat.card_sum]
  have hg : (L + 1) * Nat.card Good ≤ Nat.card (Stable n) := by
    have hi := Nat.card_le_card_of_injective
      (fun J : Good => (⟨J.val.val, (chipCount_eq_of_gameIso J.val.property).symm, J.property⟩ :
        {J : Stable n // chipCount J = chipCount I ∧ mark J}))
      (by
        intro J K h
        exact Subtype.ext (Subtype.ext (congrArg
          (fun X : {X : Stable n // chipCount X = chipCount I ∧ mark X} => X.val) h)))
    have hfit : rankSlots n L * rankBlockWidth L ≤ 2 * (n + 1) := by
      have := rankSlots_width n L
      omega
    exact (Nat.mul_le_mul_left _ hi).trans
      (marked_rank_card_mul_le n L _ (chipCount I) hfit)
  have hb : Nat.card Bad ≤ unmarkedBound n L := by
    have hi := Nat.card_le_card_of_injective
      (fun J : Bad => (⟨J.val.val, J.property⟩ : {J : Stable n // ¬ mark J}))
      (by
        intro J K h
        exact Subtype.ext (Subtype.ext (congrArg
          (fun X : {X : Stable n // ¬ mark X} => X.val) h)))
    exact hi.trans (noRankMark_card_le n L)
  have hgr : (Nat.card Good : ℝ) ≤ (Nat.card (Stable n) : ℝ) / ((L : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).2
    have hh : Nat.card Good * (L + 1) ≤ Nat.card (Stable n) := by simpa only [Nat.mul_comm] using hg
    exact_mod_cast hh
  have hbr : (Nat.card Bad : ℝ) ≤ (unmarkedBound n L : ℝ) := by exact_mod_cast hb
  change (Nat.card Class : ℝ) ≤ _
  rw [he, Nat.cast_add]
  exact add_le_add hgr hbr

private theorem collisionProbability_upper_of_rankBlocks (n L : ℕ) :
    collisionProbability n ≤ 1 / ((L : ℝ) + 1) +
      (unmarkedBound n L : ℝ) / (Nat.card (Stable n) : ℝ) := by
  classical
  letI : Fintype (Stable n) := Fintype.ofFinite _
  let N : ℝ := Nat.card (Stable n)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast stable_card_pos n
  have hc : (Nat.card (CollisionPairs n) : ℝ) ≤
      N * (N / ((L : ℝ) + 1) + unmarkedBound n L) := by
    rw [collisionPairsEquivFibers_card, Nat.cast_sum]
    calc
      _ ≤ ∑ _I : Stable n, (N / ((L : ℝ) + 1) + unmarkedBound n L) :=
        Finset.sum_le_sum (fun I _ => gameIso_class_card_upper n L I)
      _ = _ := by simp [N, ← Nat.card_eq_fintype_card, mul_add]
  change (Nat.card (CollisionPairs n) : ℝ) / N ^ 2 ≤ _
  apply (div_le_iff₀ (by positivity : 0 < N ^ 2)).2
  refine hc.trans_eq ?_
  dsimp [N] at hN ⊢
  field_simp [hN.ne']

private theorem central_catalan_majorant (s : ℕ) :
    4 ^ s ≤ (2 * s + 1) * (s + 1) * catalan s := by
  calc
    4 ^ s = 2 ^ (2 * s) := by rw [pow_mul]; rfl
    _ = ∑ j ∈ Finset.range (2 * s + 1), (2 * s).choose j := (Nat.sum_range_choose _).symm
    _ ≤ ∑ _j ∈ Finset.range (2 * s + 1), s.centralBinom :=
      Finset.sum_le_sum fun j _ => Nat.choose_le_centralBinom j s
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id,
        ← succ_mul_catalan_eq_centralBinom, mul_assoc]

private theorem rankSlots_tendsto (L : ℕ) : Tendsto (fun n : ℕ => rankSlots n L) atTop atTop := by
  refine tendsto_atTop.2 (fun J => ?_)
  filter_upwards [eventually_ge_atTop (J * rankBlockWidth L)] with n hn
  apply (Nat.le_div_iff_mul_le (by dsimp [rankBlockWidth]; omega)).mpr
  omega

/-- At fixed block size the exceptional fraction tends to zero along all widths. -/
private theorem tendsto_unmarkedBound_fraction (L : ℕ) :
    Tendsto (fun n : ℕ => (unmarkedBound n L : ℝ) / (Nat.card (Stable n) : ℝ)) atTop (𝓝 0) := by
  let M := rankBlockWidth L
  let A : ℝ := (2 : ℝ) ^ M
  let rho := (A - 1) / A
  have hM : 0 < M := by dsimp [M, rankBlockWidth]; omega
  have hA : 0 < A := by dsimp [A]; positivity
  have h1A : 1 ≤ A := by dsimp [A]; exact one_le_pow₀ (by norm_num)
  have hrho : 0 ≤ rho := div_nonneg (sub_nonneg.mpr h1A) hA.le
  have hrho' : |rho| < 1 := by
    rw [abs_of_nonneg hrho, div_lt_one hA]
    linarith
  have hlim := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hrho').comp
    (tendsto_add_atTop_nat 1)
  have hposrho : 0 < rho := by
    exact div_pos (sub_pos.mpr (one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hM))) hA
  have hlim' :
      Tendsto (fun q : ℕ => ((M : ℝ) + 1) ^ 2 * ((q : ℝ) + 1) ^ 2 * rho ^ q)
        atTop (𝓝 0) := by
    have hl := hlim.const_mul (((M : ℝ) + 1) ^ 2 / rho)
    rw [mul_zero] at hl
    apply hl.congr
    intro q
    change (((M : ℝ) + 1) ^ 2 / rho) *
      ((↑(q + 1) : ℝ) ^ 2 * rho ^ (q + 1)) = _
    push_cast
    rw [pow_succ]
    field_simp [hposrho.ne']
    exact pow_succ' rho q
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hlim'.comp (rankSlots_tendsto L))
  · exact Filter.Eventually.of_forall (fun _ => by positivity)
  · refine Filter.Eventually.of_forall (fun n => ?_)
    let q := rankSlots n L
    let r := rankTail n L
    let N : ℝ := Nat.card (Stable n)
    have hN : 0 < N := by dsimp [N]; exact_mod_cast stable_card_pos n
    have hdiv : q * M + r = 2 * (n + 1) := rankSlots_width n L
    have hr : r < M := Nat.mod_lt _ hM
    have hlen : 2 * (n + 1) + 1 ≤ (M + 1) * (q + 1) := by
      rw [← hdiv]
      nlinarith
    have hlen2 : n + 2 ≤ (M + 1) * (q + 1) := by omega
    have hbig : (2 : ℝ) ^ (2 * (n + 1)) ≤ (((M : ℝ) + 1) * ((q : ℝ) + 1)) ^ 2 * N := by
      have hc : (2 : ℝ) ^ (2 * (n + 1)) ≤
          (2 * ((n : ℝ) + 1) + 1) * ((n : ℝ) + 2) * N := by
        rw [show N = (catalan (n + 1) : ℝ) by dsimp [N]; exact_mod_cast stableCard n, pow_mul]
        have he := central_catalan_majorant (n + 1)
        exact_mod_cast he
      refine hc.trans ?_
      rw [pow_two]
      gcongr
      · exact_mod_cast hlen
      · exact_mod_cast hlen2
    have heq : (unmarkedBound n L : ℝ) =
        rho ^ q * (2 : ℝ) ^ (2 * (n + 1)) := by
      rw [← hdiv]
      have hsub : (((2 ^ M - 1 : ℕ) : ℝ)) = A - 1 := by
        rw [Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))), Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_one]
      change (((2 ^ M - 1) ^ q * 2 ^ r : ℕ) : ℝ) = _
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, hsub, Nat.cast_ofNat, pow_add,
        Nat.mul_comm q M, pow_mul]
      change (A - 1) ^ q * (2 : ℝ) ^ r = rho ^ q * (A ^ q * (2 : ℝ) ^ r)
      rw [show rho ^ q * (A ^ q * (2 : ℝ) ^ r) = (rho * A) ^ q * (2 : ℝ) ^ r by
        rw [mul_pow, mul_assoc]]
      rw [show rho * A = A - 1 by exact div_mul_cancel₀ _ hA.ne']
    change (unmarkedBound n L : ℝ) / N ≤ ((M : ℝ) + 1) ^ 2 * ((q : ℝ) + 1) ^ 2 * rho ^ q
    rw [heq, div_le_iff₀ hN, ← mul_pow]
    calc
      _ ≤ rho ^ q * ((((M : ℝ) + 1) * ((q : ℝ) + 1)) ^ 2 * N) :=
        mul_le_mul_of_nonneg_left hbig (pow_nonneg hrho _)
      _ = _ := by ring

/-- Uniform independent draws from all stable ideals have vanishing collision probability. -/
theorem tendsto_collisionProbability_zero :
    Tendsto collisionProbability atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun n => hb.trans_le (by unfold collisionProbability; positivity))
  · intro b hb
    obtain ⟨L, hL⟩ := exists_nat_gt (2 / b)
    have hsmall : (1 : ℝ) / ((L : ℝ) + 1) < b / 2 := by
      have hp : 0 < (L : ℝ) + 1 := by positivity
      have hh := (div_lt_iff₀ hb).mp hL
      rw [div_lt_iff₀ hp]
      nlinarith
    have ht := (tendsto_order.1 (tendsto_unmarkedBound_fraction L)).2 (b / 2) (by positivity)
    filter_upwards [ht] with n hn
    have hu := collisionProbability_upper_of_rankBlocks n L
    linarith

/-- The same decay holds for uniformly sampled distinct ordered pairs. -/
theorem tendsto_distinctCollisionProbability_zero :
    Tendsto distinctCollisionProbability atTop (𝓝 0) :=
  tendsto_distinctCollisionProbability_zero_of tendsto_collisionProbability_zero

end

/-- The all-width limits for independent uniform draws and for uniform distinct ordered pairs. -/
theorem result :
    Tendsto (fun n : ℕ => collisionProbability n ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) ∧
    Tendsto collisionProbability atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => distinctCollisionProbability n ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) ∧
    Tendsto distinctCollisionProbability atTop (𝓝 0) :=
  ⟨tendsto_collisionProbability_root, tendsto_collisionProbability_zero,
    tendsto_distinctCollisionProbability_root, tendsto_distinctCollisionProbability_zero⟩

end D5.S3.Combinatorics.Games.Pyranim
