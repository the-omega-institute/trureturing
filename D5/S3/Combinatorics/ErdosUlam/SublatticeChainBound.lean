/- GID: D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/ErdosUlam/SublatticeChainBound
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.claim; result=D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.result; claim=D5/S3/Combinatorics/ErdosUlam/SublatticeChainBound.claim
   digest: Every odd dimension at least eleven improves the prefix-chain guarantee by one member. -/


import D5.S3.Combinatorics.ErdosUlam.SublatticeRankRigidity
import D5.S3.Combinatorics.ErdosUlam.SublatticeConstructions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Count
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.ByContra

set_option maxRecDepth 1000000

namespace D5.S3.Combinatorics.ErdosUlam.SublatticeChainBound

open D5.S3.Combinatorics.ErdosUlam.SublatticeDefs
open D5.S3.Combinatorics.ErdosUlam.SublatticeRankRigidity
open D5.S3.Combinatorics.ErdosUlam.SublatticeConstructions
open Finset

/-- Three consecutive occurrences of one colour with equal gaps. -/
def ConsecutiveAP (g : ℕ → Bool) (n : ℕ) : Prop :=
  ∃ a b c, a < b ∧ b < c ∧ c ≤ n ∧ a + c = 2 * b ∧
    g a = g b ∧ g b = g c ∧
    (∀ r, a < r → r < b → g r ≠ g b) ∧
    (∀ r, b < r → r < c → g r ≠ g b)

/-- Exactly six true ranks in twelve consecutive positions. -/
def BalancedWindow (g : ℕ → Bool) (b : ℕ) : Prop :=
  ((Finset.range 12).filter (fun i => g (b + i) = true)).card = 6

private def revPrefix (g : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => g k :: revPrefix g k

private theorem revPrefix_length (g : ℕ → Bool) (k : ℕ) :
    (revPrefix g k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [revPrefix, ih]

private theorem revPrefix_get (g : ℕ → Bool) (k i : ℕ) (h : i < k) :
    (revPrefix g k).getD i false = g (k - 1 - i) := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp [revPrefix]
    | succ i => simpa [revPrefix, Nat.sub_sub, Nat.add_comm] using ih i (by omega)

private theorem revPrefix_take (g : ℕ → Bool) (b l : ℕ) :
    (revPrefix g (b + l)).take l = revPrefix (fun i => g (b + i)) l := by
  induction l with
  | zero => simp [revPrefix]
  | succ l ih =>
    change g (b + l) :: (revPrefix g (b + l)).take l =
      g (b + l) :: revPrefix (fun i => g (b + i)) l
    rw [ih]

private theorem revPrefix_count (g : ℕ → Bool) (k : ℕ) :
    (revPrefix g k).count true = ((Finset.range k).filter (fun i => g i = true)).card := by
  induction k with
  | zero => simp [revPrefix]
  | succ k ih =>
    rw [revPrefix, Finset.range_add_one, Finset.filter_insert]
    cases h : g k <;> simp [h, ih, Finset.mem_filter]

private def wordAP (w : List Bool) : Prop :=
  ∃ a ∈ Finset.range w.length, ∃ b ∈ Finset.range w.length,
    ∃ c ∈ Finset.range w.length, a < b ∧ b < c ∧ a + c = 2 * b ∧
    w.getD a false = w.getD b false ∧ w.getD b false = w.getD c false ∧
    (∀ r ∈ Finset.range w.length, a < r → r < b → w.getD r false ≠ w.getD b false) ∧
    (∀ r ∈ Finset.range w.length, b < r → r < c → w.getD r false ≠ w.getD b false)

private instance (w : List Bool) : Decidable (wordAP w) := by
  unfold wordAP
  infer_instance

private def patterns : List (List Bool) :=
  [[false, false, false], [true, true, true],
   [false, true, false, true, false], [true, false, true, false, true],
   [false, true, true, false, true, true, false],
   [true, false, false, true, false, false, true]]

private theorem patterns_AP : ∀ w ∈ patterns, wordAP w := by decide +kernel

private def goodEnd (w : List Bool) : Prop :=
  (∀ p ∈ patterns, w.take p.length ≠ p) ∧
  (w.length < 12 ∨ (w.take 12).count true ≠ 6)

private instance (w : List Bool) : Decidable (goodEnd w) := by
  unfold goodEnd
  infer_instance

private def extensions : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (extensions k).flatMap fun w =>
    ([false :: w, true :: w]).filter fun v => decide (goodEnd v)

private theorem extensions_fifteen : extensions 15 = [] := by decide +kernel

private theorem extensions_fourteen :
    ∀ w ∈ extensions 14, w.count true ≠ 7 := by decide +kernel

private theorem revPrefix_in_extensions (g : ℕ → Bool) (k : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ k → goodEnd (revPrefix g j)) :
    revPrefix g k ∈ extensions k := by
  induction k with
  | zero => simp [revPrefix, extensions]
  | succ k ih =>
    rw [extensions]
    apply List.mem_flatMap.mpr
    refine ⟨revPrefix g k, ih (fun j hj hjk => h j hj (by omega)), ?_⟩
    have hg := h (k + 1) (by omega) (by omega)
    cases he : g k <;> simpa [extensions, revPrefix, he] using hg

private theorem forbidden_AP (g : ℕ → Bool) (k n : ℕ) (hk : k ≤ n + 1)
    (p : List Bool) (hp : p ∈ patterns) (he : (revPrefix g k).take p.length = p) :
    ConsecutiveAP g n := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, heq, habc, hbcc, hleft, hright⟩ :=
    patterns_AP p hp
  have hlen : p.length ≤ k := by
    have := congrArg List.length he
    simp [revPrefix_length] at this
    omega
  have ha' : a < p.length := Finset.mem_range.mp ha
  have hb' : b < p.length := Finset.mem_range.mp hb
  have hc' : c < p.length := Finset.mem_range.mp hc
  have hv (i : ℕ) (hi : i < p.length) : p.getD i false = g (k - 1 - i) := by
    rw [← he]
    change ((revPrefix g k).take p.length)[i]?.getD false = _
    rw [List.getElem?_take_of_lt hi]
    exact revPrefix_get g k i (by omega)
  refine ⟨k - 1 - c, k - 1 - b, k - 1 - a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · rw [hv b hb', hv c hc'] at hbcc
    exact hbcc.symm
  · rw [hv a ha', hv b hb'] at habc
    exact habc.symm
  · intro r hr hr'
    have hi : k - 1 - r < p.length := by omega
    have hri := hright (k - 1 - r) (Finset.mem_range.mpr hi) (by omega) (by omega)
    have hei : k - 1 - (k - 1 - r) = r := by omega
    rw [hv _ hi, hv b hb', hei] at hri
    exact hri
  · intro r hr hr'
    have hi : k - 1 - r < p.length := by omega
    have hri := hleft (k - 1 - r) (Finset.mem_range.mpr hi) (by omega) (by omega)
    have hei : k - 1 - (k - 1 - r) = r := by omega
    rw [hv _ hi, hv b hb', hei] at hri
    exact hri

private theorem revPrefix_good (g : ℕ → Bool) (n k : ℕ) (hk : k ≤ n + 1)
    (ha : ¬ ConsecutiveAP g n)
    (hw : ¬ ∃ b, b + 11 ≤ n ∧ BalancedWindow g b) : goodEnd (revPrefix g k) := by
  constructor
  · intro p hp he
    exact ha (forbidden_AP g k n hk p hp he)
  · by_cases hlt : k < 12
    · exact Or.inl (by simpa [revPrefix_length] using hlt)
    · right
      intro hc
      have he : k = (k - 12) + 12 := by omega
      rw [he, revPrefix_take, revPrefix_count] at hc
      exact hw ⟨k - 12, by omega, hc⟩

/-- The rank-word alternative for every odd number of ranks at least twelve. -/
theorem rank_word_lemma (g : ℕ → Bool) (n : ℕ) (hn : 11 ≤ n) (hodd : Odd n)
    (hbalance : ((Finset.range (n + 1)).filter (fun i => g i = true)).card =
      (n + 1) / 2) :
    ConsecutiveAP g n ∨ ∃ b, b + 11 ≤ n ∧ BalancedWindow g b := by
  classical
  by_contra h
  have ha : ¬ ConsecutiveAP g n := fun ha => h (Or.inl ha)
  have hw : ¬ ∃ b, b + 11 ≤ n ∧ BalancedWindow g b := fun hw => h (Or.inr hw)
  have hg (k : ℕ) (hk : k ≤ n + 1) : revPrefix g k ∈ extensions k :=
    revPrefix_in_extensions g k (fun j _ hj => revPrefix_good g n j (by omega) ha hw)
  by_cases hl : 14 ≤ n
  · have hm := hg 15 (by omega)
    rw [extensions_fifteen] at hm
    simp at hm
  · obtain ⟨m, hm⟩ := hodd
    have casesN : n = 11 ∨ n = 13 := by omega
    rcases casesN with rfl | rfl
    · exact hw ⟨0, by omega, by simpa [BalancedWindow] using hbalance⟩
    · have hc := extensions_fourteen (revPrefix g 14) (hg 14 (by omega))
      rw [revPrefix_count] at hc
      exact hc (by simpa using hbalance)


private def baseFamilies : List (List ℕ) := [
  [0,7,56,63,448,455,504,511],
  [3,31,227,255,1795,1823,2019,2047],
  [1,15,113,127,897,911,1009,1023],
  [0,1,30,31,480,481,510,511],
  [0,7,120,127,1920,1927,2040,2047],
  [0,7,56,63,1984,1991,2040,2047],
  [0,3,7,63,963,967,1023],
  [1,7,15,127,1927,1935,2047],
  [0,3,31,127,899,927,1023],
  [1,3,31,481,483,511,2047]]

private def apTriples : List (ℕ × ℕ × ℕ) :=
  (List.range 12).flatMap fun a => (List.range 6).filterMap fun d =>
    if a + 2*(d+1) < 12 then some (a, a+d+1, a+2*(d+1)) else none

private abbrev APValid (p : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.2.2 ≤ 11 ∧ t.1+t.2.2=2*t.2.1 ∧
  p.testBit t.1 = p.testBit t.2.1 ∧ p.testBit t.2.1 = p.testBit t.2.2 ∧
  ∀ r ∈ List.range 12, t.1 < r → r < t.2.2 → p.testBit r = p.testBit t.2.1 → r=t.2.1

private def checkAP (p : ℕ) (t : ℕ × ℕ × ℕ) : Bool := decide (APValid p t)

private def checkMono (p : ℕ) (l : List ℕ) (b : Bool) : Bool :=
  l.all (fun m => p.testBit (weight 11 m) == b)

private def balancedPatterns : List ℕ :=
  (List.range 4096).filter (fun p => weight 12 p == 6)

set_option maxHeartbeats 0 in
private theorem family_checks : baseFamilies.all (fun l =>
    decide (l.Nodup ∧ 7 ≤ l.length ∧ (∀ m ∈ l, m < 2048) ∧ (∀ a ∈ l, ∀ b ∈ l, a ||| b ∈ l ∧ a &&& b ∈ l))) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem patterns_checked : balancedPatterns.all (fun p =>
    apTriples.any (checkAP p) ||
      baseFamilies.any (fun l => [false,true].any (checkMono p l))) = true := by
  decide +kernel

/-- Every balanced rank colouring in dimension eleven has seven monochromatic members. -/
theorem balanced_rank_base (g : ℕ → Bool)
    (hbal : ((range 12).filter (fun r => g r = true)).card = 6) :
    ∃ L : Finset (Finset (Fin 11)), IsSublattice L ∧
      Monochromatic (fun A => g A.card) L ∧ 7 ≤ L.card := by
  classical
  obtain ⟨pat, hpat⟩ := decode_surjective 12
    (univ.filter (fun r : Fin 12 => g r.val = true))
  have hbit : ∀ r, r < 12 → pat.val.testBit r = g r := by
    intro r hr
    have he := Finset.ext_iff.mp hpat ⟨r, hr⟩
    exact Bool.eq_iff_iff.mpr (by simpa [decode] using he)
  change decode 12 pat.val = _ at hpat
  have hweight : weight 12 pat.val = 6 := by
    rw [← decode_card, hpat]
    have he : (univ.filter (fun r : Fin 12 => g r.val = true)).card =
        ((range 12).filter (fun r => g r = true)).card := by
      apply card_bij (fun r _ => r.val)
      · intro r hr
        simp only [mem_filter, mem_univ, true_and] at hr
        exact mem_filter.mpr ⟨mem_range.mpr r.isLt, hr⟩
      · intro r hr t ht he; exact Fin.ext he
      · intro r hr
        obtain ⟨hr, hg⟩ := mem_filter.mp hr
        exact ⟨⟨r, mem_range.mp hr⟩, by simp [hg], rfl⟩
    exact he.trans hbal
  have hp : pat.val ∈ balancedPatterns := by
    simp [balancedPatterns, hweight]
  have hcovered := List.all_eq_true.mp patterns_checked pat.val hp
  have hor : apTriples.any (checkAP pat.val) = true ∨
      baseFamilies.any (fun l => [false,true].any (checkMono pat.val l)) = true := by
    simpa only [Bool.or_eq_true_iff] using hcovered
  rcases hor with hap | hfam
  · obtain ⟨⟨a,b,c⟩, ht, hv⟩ := List.any_eq_true.mp hap
    have hv' := of_decide_eq_true hv
    dsimp only [APValid] at hv'
    obtain ⟨hab,hbc,hcn,heq,ha,hc,hgap⟩ := hv'
    have hgn : ∀ r, a < r → r < c → g r = g b → r=b := by
      intro r har hrc hg
      apply hgap r (List.mem_range.mpr (by omega)) har hrc
      simpa [hbit r (by omega), hbit b (by omega)] using hg
    obtain ⟨L,hL,hm,hsize⟩ := diamond_sublattice 11 a b c g (g b)
      hab hbc hcn heq (by simpa [hbit a (by omega), hbit b (by omega)] using ha)
      rfl (by simpa [hbit b (by omega), hbit c (by omega)] using hc.symm) hgn
    have hcount : ((range 12).filter (fun r => g r = g b)).card = 6 := by
      cases hb : g b with
      | true => simpa [hb] using hbal
      | false =>
        have h := card_filter_add_card_filter_not (s := range 12) (fun r => g r = true)
        have he : (range 12).filter (fun r => ¬ g r = true) =
            (range 12).filter (fun r => g r = false) := by
          ext r; cases g r <;> simp
        rw [he, hbal] at h
        simp only [card_range] at h
        omega
    exact ⟨L,hL,hm,by simpa [hcount] using hsize⟩
  · obtain ⟨l, hl, hmono⟩ := List.any_eq_true.mp hfam
    obtain ⟨color, _, hm⟩ := List.any_eq_true.mp hmono
    obtain ⟨hnd,hlen,hbounds,hclosed⟩ :=
      of_decide_eq_true (List.all_eq_true.mp family_checks l hl)
    refine ⟨l.toFinset.image (decode 11), family_sublattice 11 (by
      intro he; simp [he] at hlen) hclosed, ⟨color, ?_⟩, ?_⟩
    · intro A hA
      obtain ⟨m,hmem,rfl⟩ := mem_image.mp hA
      have hml : m ∈ l := by simpa using hmem
      have hmc := List.all_eq_true.mp hm m hml
      have hw : weight 11 m < 12 := by
        have := card_le_univ (decode 11 m)
        rw [decode_card] at this
        simp only [Fintype.card_fin] at this
        omega
      change g (decode 11 m).card = color
      rw [decode_card, ← hbit _ hw]
      simpa using hmc
    · rw [family_card 11 hnd (by simpa using hbounds)]
      exact hlen

/-- The literal minimum over all two-colourings of the largest monochromatic sublattice. -/
noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact (univ : Finset (Finset (Fin n) → Bool)).inf' univ_nonempty
    (fun χ => (univ : Finset (Finset (Finset (Fin n)))).sup
      (fun L => if IsSublattice L ∧ Monochromatic χ L then L.card else 0))

/-- For natural n, (n+2)/2 is the natural-number value of ceil((n+1)/2). -/
def claim : Prop := ∀ n : ℕ, f n = (n + 2) / 2


/-- The chain guarantee improves by one in every odd dimension at least eleven. -/
theorem odd_lower_bound (n : ℕ) (hn : 11 ≤ n) (hodd : Odd n) :
    (n + 3) / 2 ≤ f n := by
  classical
  have harith : (n + 3) / 2 = (n + 1) / 2 + 1 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  apply Finset.le_inf'
  intro χ hχ
  have hexists : ∃ L, IsSublattice L ∧ Monochromatic χ L ∧ (n+3)/2 ≤ L.card := by
    by_contra he
    have hs : ∀ L, IsSublattice L → Monochromatic χ L → L.card ≤ (n+1)/2 := by
      intro L hL hm
      by_contra hc
      exact he ⟨L, hL, hm, by omega⟩
    let g : ℕ → Bool := fun r => χ (initialSegment n r)
    have hrank : ∀ A, χ A = g A.card := by
      intro A
      apply rank_rigidity hodd χ hs
      exact (prefix_card n A.card (by simpa using card_le_univ A)).symm
    have hbal : ∀ color, ((range (n+1)).filter (fun r => g r = color)).card = (n+1)/2 :=
      balanced_prefixes hodd χ hs
    have hmono : ∀ L, Monochromatic (fun A : Finset (Fin n) => g A.card) L →
        Monochromatic χ L := by
      intro L hm
      obtain ⟨color,hc⟩ := hm
      exact ⟨color, fun A hA => (hrank A).trans (hc A hA)⟩
    rcases rank_word_lemma g n hn hodd (hbal true) with hap | hwindow
    · obtain ⟨a,b,c,hab,hbc,hcn,heq,ha,hc,hleft,hright⟩ := hap
      have hgap : ∀ r, a < r → r < c → g r = g b → r = b := by
        intro r har hrc hg
        by_contra hne
        by_cases hrb : r < b
        · exact hleft r har hrb hg
        · exact hright r (by omega) hrc hg
      obtain ⟨L,hL,hm,hsize⟩ := diamond_sublattice n a b c g (g b)
        hab hbc hcn heq ha rfl hc.symm hgap
      exact he ⟨L,hL,hmono L hm,by rw [harith]; simpa [hbal] using hsize⟩
    · obtain ⟨b,hbn,hwindow⟩ := hwindow
      obtain ⟨L,hL,⟨color,hc⟩,hsize⟩ := balanced_rank_base (fun r => g (b+r)) hwindow
      have hcount : ((range 12).filter (fun r => g (b+r) = color)).card = 6 := by
        have ht : ((range 12).filter (fun r => g (b+r) = true)).card = 6 := hwindow
        cases color with
        | true => exact ht
        | false =>
          have h := card_filter_add_card_filter_not (s := range 12) (fun r => g (b+r) = true)
          have he : (range 12).filter (fun r => ¬ g (b+r) = true) =
              (range 12).filter (fun r => g (b+r) = false) := by
            ext r; cases g (b+r) <;> simp
          rw [he, ht] at h
          simp only [card_range] at h
          omega
      obtain ⟨M,hM,hm,hlarge⟩ := interval_sublattice n b 11 g color hbn L hL hc
        (by simpa [hcount] using hsize)
      exact he ⟨M,hM,hmono M hm,by rw [harith]; simpa [hbal] using hlarge⟩
  obtain ⟨L,hL,hm,hsize⟩ := hexists
  exact hsize.trans (Finset.le_sup_of_le (Finset.mem_univ L) (by simp [hL, hm]))

/-- Dimension eleven refutes the proposed universal formula. -/
theorem result : ¬ claim := by
  intro h
  have hbound : 7 ≤ f 11 := odd_lower_bound 11 (by decide) (by decide)
  have h11 : f 11 = 6 := h 11
  exact (by decide : ¬ (7 ≤ 6)) (h11 ▸ hbound)

end D5.S3.Combinatorics.ErdosUlam.SublatticeChainBound
