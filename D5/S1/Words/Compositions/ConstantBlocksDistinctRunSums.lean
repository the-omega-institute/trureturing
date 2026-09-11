/- GID: D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/ConstantBlocksDistinctRunSums
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Constant blocks with distinct sums are realizable as distinct maximal run sums. -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace D5.S1.Words.Compositions.ConstantBlocksDistinctRunSums

open scoped BigOperators

/-- A block is encoded by its positive value and positive multiplicity.
Distinct sums forbid repeated identical blocks, so a finite set is sufficient. -/
def HasConstantBlocks (m : Multiset ℕ) : Prop :=
  ∃ s : Finset (ℕ × ℕ), (∀ b ∈ s, 0 < b.1 ∧ 0 < b.2) ∧
    Set.InjOn (fun b : ℕ × ℕ => b.1 * b.2) s ∧
    ∑ b ∈ s, Multiset.replicate b.2 b.1 = m

/-- Sums of the maximal constant runs, including the empty list of sums. -/
def runSums (l : List ℕ) : List ℕ :=
  (l.splitBy (· == ·)).map List.sum

/-- Some ordering of the multiset has pairwise distinct maximal run sums. -/
def HasDistinctRunSums (m : Multiset ℕ) : Prop :=
  ∃ l : List ℕ, (l : Multiset ℕ) = m ∧ (runSums l).Nodup

private theorem fiber_add_le {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) {c d : ℕ} (h : c ≠ d) :
    (s.filter (fun x => f x = c)).card + (s.filter (fun x => f x = d)).card ≤
      s.card := by
  rw [← Finset.card_union_of_disjoint]
  · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact h ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

-- The stronger induction invariant remembers the forbidden first color p.
private theorem order_colors {α : Type*} [DecidableEq α] (f : α → ℕ)
    (s : Finset α) (p : ℕ)
    (h : ∀ c, 2 * (s.filter (fun x => f x = c)).card ≤
      s.card + if c = p then 0 else 1) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧
      (p :: l.map f).IsChain (· ≠ ·) := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s p with
  | h n ih =>
    by_cases he : s = ∅
    · subst s
      exact ⟨[], by simp⟩
    have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    have hel : (s.filter (fun x => f x ≠ p)).Nonempty := by
      by_contra hem
      have hz : (s.filter (fun x => f x ≠ p)).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hem)
      have hc := Finset.card_filter_add_card_filter_not (s := s) (fun x => f x = p)
      change (s.filter (fun x => f x ≠ p)).card = 0 at hz
      rw [hz, add_zero] at hc
      have hp := h p
      simp only [ite_true, add_zero] at hp
      have hnz := Finset.card_pos.mpr hs
      omega
    obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image
      (s.filter (fun x => f x ≠ p)) (fun x => (s.filter (fun y => f y = f x)).card) hel
    obtain ⟨hxs, hxp⟩ := Finset.mem_filter.mp hx
    have hcard := Finset.card_erase_of_mem hxs
    have hsmall : (s.erase x).card < n := by
      have := Finset.card_pos.mpr hs
      omega
    have hnext : ∀ c, 2 * ((s.erase x).filter (fun y => f y = c)).card ≤
        (s.erase x).card + if c = f x then 0 else 1 := by
      intro c
      rw [Finset.filter_erase]
      by_cases hcx : c = f x
      · subst c
        rw [Finset.card_erase_of_mem (show x ∈ s.filter (fun y => f y = f x) from
          Finset.mem_filter.mpr ⟨hxs, rfl⟩)]
        have hc := h (f x)
        simp only [hxp, ite_false, ite_true, add_zero] at hc ⊢
        have hp : 0 < (s.filter (fun y => f y = f x)).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxs, rfl⟩⟩
        omega
      · have hxm : x ∉ s.filter (fun y => f y = c) := by
          simp only [Finset.mem_filter, not_and]
          exact fun _ heq => hcx heq.symm
        rw [Finset.erase_eq_of_notMem hxm]
        simp only [hcx, ite_false]
        have hc : 2 * (s.filter (fun y => f y = c)).card ≤ s.card := by
          by_cases hcp : c = p
          · subst c
            simpa using h p
          by_cases hzero : (s.filter (fun y => f y = c)).card = 0
          · omega
          obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
          obtain ⟨hys, hyc⟩ := Finset.mem_filter.mp hy
          have hym : y ∈ s.filter (fun z => f z ≠ p) :=
            Finset.mem_filter.mpr ⟨hys, by simpa [hyc] using hcp⟩
          have hm := hmax y hym
          rw [hyc] at hm
          have hd := fiber_add_le s f hcx
          omega
        have hnz := Finset.card_pos.mpr hs
        omega
    obtain ⟨l, hl, hls, hlc⟩ := ih _ hsmall (s.erase x) (f x) hnext rfl
    refine ⟨x :: l, ?_, ?_, ?_⟩
    · simp only [List.nodup_cons]
      exact ⟨by simp [← List.mem_toFinset, hls], hl⟩
    · simp [hls, Finset.insert_erase hxs]
    · simpa only [List.map_cons, List.isChain_cons_cons] using
        And.intro (Ne.symm hxp) hlc

private def ValidBlocks (m : Multiset ℕ) (s : Finset (ℕ × ℕ)) : Prop :=
  (∀ b ∈ s, 0 < b.1 ∧ 0 < b.2) ∧
    Set.InjOn (fun b : ℕ × ℕ => b.1 * b.2) s ∧
    ∑ b ∈ s, Multiset.replicate b.2 b.1 = m

-- If one value is overrepresented, merging its largest block with one of
-- its other blocks avoids every existing sum by the pigeonhole principle.
private theorem minimal_balanced {m : Multiset ℕ} {s : Finset (ℕ × ℕ)}
    (hv : ValidBlocks m s)
    (hmin : ∀ t, ValidBlocks m t → s.card ≤ t.card) (v : ℕ) :
    2 * (s.filter (fun b => b.1 = v)).card ≤ s.card + 1 := by
  classical
  let w : ℕ × ℕ → ℕ := fun b => b.1 * b.2
  let t := s.filter (fun b => b.1 = v)
  let o := s.filter (fun b => b.1 ≠ v)
  obtain ⟨hp, hi, hm⟩ := hv
  change Set.InjOn w s at hi
  by_contra hbad
  change ¬ 2 * t.card ≤ s.card + 1 at hbad
  have hcounts : t.card + o.card = s.card :=
    Finset.card_filter_add_card_filter_not (s := s) (fun b => b.1 = v)
  have ht : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image t w ht
  obtain ⟨has, hav⟩ := Finset.mem_filter.mp ha
  have hchoice : ∃ b ∈ t.erase a, w a + w b ∉ s.image w := by
    by_contra hn
    push Not at hn
    have hsub : ((t.erase a).image (fun b => w a + w b)) ⊆ o.image w := by
      intro z hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨c, hc, he⟩ := Finset.mem_image.mp (hn b hb)
      refine Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩, he⟩
      intro hcv
      have hcm := hamax c (Finset.mem_filter.mpr ⟨hc, hcv⟩)
      have hbs := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)).1
      have hbp : 0 < w b := Nat.mul_pos (hp b hbs).1 (hp b hbs).2
      omega
    have hci : ((t.erase a).image (fun b => w a + w b)).card = (t.erase a).card := by
      apply Finset.card_image_of_injOn
      intro b hb c hc he
      exact hi ((Finset.mem_filter.mp (Finset.mem_of_mem_erase hb)).1)
        ((Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1) (Nat.add_left_cancel he)
    have hle := (Finset.card_le_card hsub).trans (Finset.card_image_le)
    rw [hci, Finset.card_erase_of_mem ha] at hle
    change ¬ 2 * t.card ≤ s.card + 1 at hbad
    omega
  obtain ⟨b, hb, hnew⟩ := hchoice
  obtain ⟨hba, hbt⟩ := Finset.mem_erase.mp hb
  obtain ⟨hbs, hbv⟩ := Finset.mem_filter.mp hbt
  let z : ℕ × ℕ := (v, a.2 + b.2)
  have hwz : w z = w a + w b := by
    dsimp [w, z]
    rw [hav, hbv, Nat.mul_add]
  have hzs : z ∉ s := by
    intro hz
    exact hnew (Finset.mem_image.mpr ⟨z, hz, hwz⟩)
  let u := (s.erase a).erase b
  have hus : u ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hzu : z ∉ u := fun hz => hzs (hus hz)
  have hbe : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hba, hbs⟩
  have hv' : ValidBlocks m (insert z u) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨by change 0 < v; exact hav ▸ (hp a has).1,
          by dsimp [z]; have := (hp a has).2; omega⟩
      · exact hp c (hus hc)
    · intro c hc d hd he
      rcases Finset.mem_insert.mp hc with rfl | hc
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · rfl
        · exact False.elim (hnew (Finset.mem_image.mpr
            ⟨d, hus hd, (show w z = w d from he).symm.trans hwz⟩))
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · exact False.elim (hnew (Finset.mem_image.mpr
            ⟨c, hus hc, (show w c = w z from he).trans hwz⟩))
        · exact hi (hus hc) (hus hd) he
    · let parts : ℕ × ℕ → Multiset ℕ := fun b => Multiset.replicate b.2 b.1
      have hzparts : parts z = parts a + parts b := by
        dsimp [parts, z]
        rw [hav, hbv, Multiset.replicate_add]
      have he1 := Finset.sum_erase_add s parts has
      have he2 := Finset.sum_erase_add (s.erase a) parts hbe
      change ∑ c ∈ insert z u, parts c = m
      rw [Finset.sum_insert hzu, hzparts]
      calc
        parts a + parts b + ∑ c ∈ u, parts c =
            (∑ c ∈ u, parts c) + parts b + parts a := by ac_rfl
        _ = m := by rw [he2, he1]; exact hm
  have hle := hmin (insert z u) hv'
  rw [Finset.card_insert_of_notMem hzu] at hle
  have hc1 := Finset.card_erase_of_mem has
  have hc2 := Finset.card_erase_of_mem hbe
  change ((s.erase a).erase b).card + 1 ≥ s.card at hle
  have htwo : 2 ≤ s.card := by
    have := Finset.card_pos.mpr (show (s.erase a).Nonempty from ⟨b, hbe⟩)
    omega
  omega

private theorem exists_balanced {m : Multiset ℕ} (hm : HasConstantBlocks m) :
    ∃ s : Finset (ℕ × ℕ), ValidBlocks m s ∧
      ∀ v, 2 * (s.filter (fun b => b.1 = v)).card ≤ s.card + 1 := by
  classical
  change ∃ s, ValidBlocks m s at hm
  obtain ⟨s, hs⟩ := hm
  have hex : ∃ k, ∃ t, ValidBlocks m t ∧ t.card = k := ⟨s.card, s, hs, rfl⟩
  obtain ⟨t, ht, he⟩ := Nat.find_spec hex
  refine ⟨t, ht, minimal_balanced ht ?_⟩
  intro u hu
  rw [he]
  exact Nat.find_min' hex ⟨u, hu, rfl⟩

private theorem coe_flatten (l : List (List ℕ)) :
    (l.flatten : Multiset ℕ) = (l.map (fun (b : List ℕ) => (b : Multiset ℕ))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatten_cons, List.map_cons, List.sum_cons, ← Multiset.coe_add, ih]

private theorem replicate_chain (n v : ℕ) :
    (List.replicate n v).IsChain (fun a b => (a == b) = true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.replicate_succ, List.isChain_cons_cons, beq_self_eq_true,
        true_and] using ih

private theorem split_replicates (l : List (ℕ × ℕ))
    (hp : ∀ b ∈ l, 0 < b.2) (hc : (l.map Prod.fst).IsChain (· ≠ ·)) :
    ((l.map (fun b => List.replicate b.2 b.1)).flatten).splitBy (· == ·) =
      l.map (fun b => List.replicate b.2 b.1) := by
  apply List.splitBy_flatten
  · intro he
    obtain ⟨b, hb, he⟩ := List.mem_map.mp he
    have hn := List.length_pos_iff_ne_nil.mpr (show List.replicate b.2 b.1 ≠ [] from
      by simpa using Nat.ne_of_gt (hp b hb))
    simp [he] at hn
  · intro r hr
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
    exact replicate_chain _ _
  · rw [List.isChain_map] at hc ⊢
    apply hc.imp_of_mem_imp
    intro a b ha hb hab
    have hna : List.replicate a.2 a.1 ≠ [] := by simpa using Nat.ne_of_gt (hp a ha)
    have hnb : List.replicate b.2 b.1 ≠ [] := by simpa using Nat.ne_of_gt (hp b hb)
    exact ⟨hna, hnb, by simpa using hab⟩

private theorem blocks_to_runs {m : Multiset ℕ} (hm : HasConstantBlocks m) :
    HasDistinctRunSums m := by
  classical
  obtain ⟨s, ⟨hp, hi, hs⟩, hb⟩ := exists_balanced hm
  have hbal : ∀ c, 2 * (s.filter (fun b => b.1 = c)).card ≤
      s.card + if c = 0 then 0 else 1 := by
    intro c
    split_ifs with hc
    · subst c
      have he : s.filter (fun b => b.1 = 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro b hbs he
        have := (hp b hbs).1
        omega
      simp [he]
    · exact hb c
  obtain ⟨l, hl, hls, hc⟩ := order_colors Prod.fst s 0 hbal
  have hlp : ∀ b ∈ l, 0 < b.2 := by
    intro b hb
    exact (hp b (by simpa [← hls] using hb)).2
  refine ⟨(l.map (fun b => List.replicate b.2 b.1)).flatten, ?_, ?_⟩
  · rw [coe_flatten]
    simp only [List.map_map, Function.comp_def, Multiset.coe_replicate]
    rw [← List.sum_toFinset _ hl, hls]
    exact hs
  · unfold runSums
    rw [split_replicates l hlp hc.of_cons]
    simp only [List.map_map, Function.comp_def, List.sum_replicate, smul_eq_mul,
      Nat.mul_comm]
    apply hl.map_on
    intro a ha b hb he
    exact hi (by simpa [← hls] using ha) (by simpa [← hls] using hb) he

private theorem constant_eq_replicate {r : List ℕ} (hr : r.IsChain (· = ·)) :
    r = List.replicate r.length (r.headD 0) := by
  cases r with
  | nil => rfl
  | cons a t =>
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · exact ((List.pairwise_cons.mp hr.pairwise).1 b hb).symm

private theorem runs_to_blocks {m : Multiset ℕ} (hp : ∀ x ∈ m, 0 < x)
    (hm : HasDistinctRunSums m) : HasConstantBlocks m := by
  classical
  obtain ⟨l, hl, hn⟩ := hm
  let rs := l.splitBy (· == ·)
  let encode : List ℕ → ℕ × ℕ := fun r => (r.headD 0, r.length)
  let bs := rs.map encode
  have hr : ∀ r ∈ rs, r = List.replicate r.length (r.headD 0) := by
    intro r hmem
    apply constant_eq_replicate
    exact (List.isChain_of_mem_splitBy hmem).imp (by simp)
  have he : bs.map (fun b => b.1 * b.2) = rs.map List.sum := by
    dsimp [bs]
    rw [List.map_map]
    apply List.map_congr_left
    intro r hmem
    change r.headD 0 * r.length = r.sum
    conv_rhs => rw [hr r hmem]
    simp [Nat.mul_comm]
  have hbn : (bs.map (fun b => b.1 * b.2)).Nodup := by
    rw [he]
    exact hn
  have hb : bs.Nodup := hbn.of_map _
  refine ⟨bs.toFinset, ?_, ?_, ?_⟩
  · intro b hbs
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hbs)
    have hne : r ≠ [] := List.ne_nil_of_mem_splitBy hmem
    refine ⟨?_, List.length_pos_iff_ne_nil.mpr hne⟩
    apply hp
    rw [← hl]
    change r.headD 0 ∈ l
    rw [← List.flatten_splitBy (· == ·) l]
    apply List.mem_flatten.mpr
    refine ⟨r, hmem, ?_⟩
    cases r with
    | nil => exact False.elim (hne rfl)
    | cons a t => simp
  · intro a ha b hb heq
    exact List.inj_on_of_nodup_map hbn (List.mem_toFinset.mp ha)
      (List.mem_toFinset.mp hb) heq
  · rw [List.sum_toFinset _ hb]
    dsimp [bs]
    rw [List.map_map]
    have heparts : rs.map (fun r => Multiset.replicate r.length (r.headD 0)) =
        rs.map (fun (r : List ℕ) => (r : Multiset ℕ)) := by
      apply List.map_congr_left
      intro r hmem
      rw [← Multiset.coe_replicate, ← hr r hmem]
    change (rs.map (fun r => Multiset.replicate r.length (r.headD 0))).sum = m
    rw [heparts, ← coe_flatten, List.flatten_splitBy]
    exact hl

/-- Pointwise form of the A382427 conjecture, also stated in its complement A381717. -/
theorem constantBlocks_iff_distinctRunSums {n : ℕ} (p : Nat.Partition n) :
    HasConstantBlocks p.parts ↔ HasDistinctRunSums p.parts :=
  ⟨blocks_to_runs, runs_to_blocks (fun _ hx => p.parts_pos hx)⟩

open Classical in
/-- A382427 counts the same partitions by constant blocks and by maximal runs. -/
theorem card_constantBlocks_eq_distinctRunSums (n : ℕ) :
    (Finset.univ.filter (fun p : Nat.Partition n => HasConstantBlocks p.parts)).card =
      (Finset.univ.filter (fun p : Nat.Partition n => HasDistinctRunSums p.parts)).card := by
  classical
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    constantBlocks_iff_distinctRunSums]

#print axioms constantBlocks_iff_distinctRunSums
#print axioms card_constantBlocks_eq_distinctRunSums

end D5.S1.Words.Compositions.ConstantBlocksDistinctRunSums
