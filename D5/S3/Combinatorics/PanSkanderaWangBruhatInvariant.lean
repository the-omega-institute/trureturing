/- GID: D5/S3/Combinatorics/PanSkanderaWangBruhatInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PanSkanderaWangBruhatInvariant
   mirror-E: none(waiver:direct-Lean-proof-of-the-pan-skandera-wang-bruhat-conjecture)
   anchors: [mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Selection invariance survives reverse-complementation and matched insertion. -/

import D5.S3.Combinatorics.PanSkanderaWangBruhatDefs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PanSkanderaWangBruhat

/-- Zero-based positions in the selection set `S_n(p,d)` from the rank proof. -/
def selectionPositions (p d : ℕ) : List ℕ :=
  List.range (p - d) ++ (List.range d).map (fun k => p - d + 2 * k + 1)

/-- Entries of a word selected by `S_n(p,d)`. Out-of-range positions use zero. -/
def selection (x : List ℕ) (p d : ℕ) : List ℕ :=
  (selectionPositions p d).map (fun i => x.getD i 0)
/-- Number of entries of a word that are at least the threshold `q`. -/
def countGE (q : ℕ) (x : List ℕ) : ℕ :=
  x.countP (fun v => decide (q ≤ v))

/-- The strengthened selection invariant (F). -/
def SelectionInvariant (n : ℕ) (x y : List ℕ) : Prop :=
  ∀ p d q : ℕ, p ≤ n → d ≤ p → d ≤ n - p →
    1 ≤ q → q ≤ n + 1 → countGE q (x.take p) ≤ countGE q (selection y p d)
private def reverseSelectionPositions (n p d : ℕ) : List ℕ :=
  (selectionPositions p d).map (fun i => n - 1 - i)
private lemma reverseSelectionPositions_partition {n p d : ℕ}
    (hp : p ≤ n) (hdp : d ≤ p) (hdn : d ≤ n - p) :
    List.Perm
      (reverseSelectionPositions n p d ++ selectionPositions (n - p) d)
      (List.range n) := by
  have hreverseMem : ∀ {j : ℕ}, j < n →
      (n - 1 - j ∈ selectionPositions p d ↔ j ∉ selectionPositions (n - p) d) := by
    intro j hj
    have hmem : ∀ {p d i : ℕ},
        i ∈ selectionPositions p d ↔
          i < p - d ∨ ∃ k < d, i = p - d + 2 * k + 1 := by
      intro p d i
      simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map]
      constructor
      · rintro (h | ⟨k, hk, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, hk, rfl⟩
      · rintro (h | ⟨k, hk, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, hk, rfl⟩
    rw [hmem]
    simp only [hmem, not_or, not_exists, not_and, not_lt]
    constructor
    · intro h
      constructor
      · rcases h with h | ⟨i, hi, heq⟩ <;> omega
      · intro k hk heqk
        rcases h with h | ⟨i, hi, heqi⟩ <;> omega
    · rintro ⟨hleft, hstep⟩
      by_cases hprefix : n - 1 - j < p - d
      · exact Or.inl hprefix
      · right
        have hspan : n - 1 - j < p + d := by omega
        let off := n - 1 - j - (p - d)
        have hoff : n - 1 - j = p - d + off := by simp only [off]; omega
        have hofflt : off < 2 * d := by simp only [off]; omega
        obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' off
        · have hklt : k < d := by omega
          have hbad := hstep (d - k - 1) (by omega)
          exfalso
          apply hbad
          omega
        · refine ⟨k, ?_, ?_⟩ <;> omega
  have hbound : ∀ {p d i : ℕ}, d ≤ p → i ∈ selectionPositions p d → i < p + d := by
    intro p d i hdp hi
    simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map] at hi
    rcases hi with hi | ⟨k, hk, rfl⟩ <;> omega
  have hselNodup : ∀ p d : ℕ, (selectionPositions p d).Nodup := by
    intro p d
    rw [selectionPositions, List.nodup_append]
    refine ⟨List.nodup_range, List.nodup_range.map ?_, ?_⟩
    · intro a b h
      change p - d + 2 * a + 1 = p - d + 2 * b + 1 at h
      omega
    · intro i hi k hk
      simp only [List.mem_range] at hi
      simp only [List.mem_map, List.mem_range] at hk
      rcases hk with ⟨j, hj, rfl⟩
      omega
  have hleft : (reverseSelectionPositions n p d).Nodup := by
    unfold reverseSelectionPositions
    apply (hselNodup p d).map_on
    intro i hi j hj heq
    have hi' := hbound hdp hi
    have hj' := hbound hdp hj
    have hsum : p + d ≤ n := by omega
    omega
  have hright := hselNodup (n - p) d
  have happ :
      (reverseSelectionPositions n p d ++ selectionPositions (n - p) d).Nodup := by
    rw [List.nodup_append]
    refine ⟨hleft, hright, ?_⟩
    intro j hjleft k hk heq
    subst k
    simp only [reverseSelectionPositions, List.mem_map] at hjleft
    rcases hjleft with ⟨i, hi, rfl⟩
    have hi' := hbound hdp hi
    have hsum : p + d ≤ n := by omega
    have hjlt : n - 1 - i < n := by omega
    have hback : n - 1 - (n - 1 - i) = i := by omega
    have hirev : n - 1 - (n - 1 - i) ∈ selectionPositions p d := by
      simpa only [hback] using hi
    exact (hreverseMem hjlt).mp hirev hk
  apply (List.perm_ext_iff_of_nodup happ List.nodup_range).mpr
  intro j
  simp only [List.mem_append, List.mem_range]
  constructor
  · rintro (hj | hj)
    · simp only [reverseSelectionPositions, List.mem_map] at hj
      rcases hj with ⟨i, hi, rfl⟩
      have hi' := hbound hdp hi
      omega
    · have hj' := hbound hdn hj
      omega
  · intro hj
    by_cases hsel : j ∈ selectionPositions (n - p) d
    · exact Or.inr hsel
    · left
      simp only [reverseSelectionPositions, List.mem_map]
      refine ⟨n - 1 - j, (hreverseMem hj).mpr hsel, ?_⟩
      omega
/-- Reverse-complementation preserves permutations of `[n]`. -/
theorem ru_isPerm {n : ℕ} {x : List ℕ} (hx : IsPerm n x) : IsPerm n (RU n x) := by
  unfold IsPerm at hx ⊢
  unfold RU
  have hrev : x.reverse.Perm (List.range' 1 n).reverse :=
    x.reverse_perm.trans (hx.trans (List.reverse_perm _).symm)
  have h := hrev.map (fun v => n + 1 - v)
  have hr : RU n (List.range' 1 n) = List.range' 1 n := by
    apply List.ext_getElem
    · simp [RU]
    · intro i hi h'i
      simp only [RU, List.length_map, List.length_reverse, List.length_range'] at hi
      simp only [RU, List.getElem_map, List.getElem_reverse]
      rw [List.getElem_range'_1, List.getElem_range'_1]
      simp only [List.length_range']
      omega
  unfold RU at hr
  rw [hr] at h
  exact h
private def valuesAt (x : List ℕ) (is : List ℕ) : List ℕ :=
  is.map (fun i => x.getD i 0)
private def reverseSelectionValues (n : ℕ) (x : List ℕ) (p d : ℕ) : List ℕ :=
  valuesAt x (reverseSelectionPositions n p d)
private lemma countGE_complement_add {n q : ℕ} {z : List ℕ}
    (_hq1 : 1 ≤ q) (hqn : q ≤ n + 1) (hz : ∀ v ∈ z, 1 ≤ v ∧ v ≤ n) :
    countGE q (z.map (fun v => n + 1 - v)) + countGE (n + 2 - q) z = z.length := by
  induction z with
  | nil => rfl
  | cons a z ih =>
      have ha := hz a (by simp)
      have hz' : ∀ v ∈ z, 1 ≤ v ∧ v ≤ n := by
        intro v hv
        exact hz v (by simp [hv])
      have := ih hz'
      simp only [List.map_cons, countGE, List.countP_cons, List.length_cons] at ⊢
      by_cases h : n + 2 - q ≤ a
      · have hn : ¬q ≤ n + 1 - a := by omega
        have h1 : decide (q ≤ n + 1 - a) = false := by simp [hn]
        have h2 : decide (n + 2 - q ≤ a) = true := by simp [h]
        rw [h1, h2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [countGE] at this
        omega
      · have hy : q ≤ n + 1 - a := by omega
        have h1 : decide (q ≤ n + 1 - a) = true := by simp [hy]
        have h2 : decide (n + 2 - q ≤ a) = false := by simp [h]
        rw [h1, h2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [countGE] at this
        omega
/-- Reverse-complementation preserves the full selection invariant (Lemma 2). -/
theorem selectionInvariant_ru {n : ℕ} {x y : List ℕ}
    (hx : IsPerm n x) (hy : IsPerm n y) (hF : SelectionInvariant n x y) :
    SelectionInvariant n (RU n x) (RU n y) := by
  have hbound : ∀ {p d i : ℕ}, d ≤ p → i ∈ selectionPositions p d → i < p + d := by
    intro p d i hdp hi
    simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map] at hi
    rcases hi with hi | ⟨k, hk, rfl⟩ <;> omega
  have hmapRange : ∀ (z : List ℕ) (k : ℕ), k ≤ z.length →
      (List.range k).map (fun i => z.getD i 0) = z.take k := by
    intro z k hk
    apply List.ext_getElem
    · simp [hk]
    · intro i hi h'i
      simp only [List.length_map, List.length_range] at hi
      have hiz : i < z.length := lt_of_lt_of_le hi hk
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem z 0 hiz]
      exact z.getElem_take' hiz hi
  have hselectionZero : ∀ (z : List ℕ) (k : ℕ), k ≤ z.length →
      selection z k 0 = z.take k := by
    intro z k hk
    unfold selection selectionPositions
    simp only [Nat.sub_zero, List.range_zero, List.map_nil, List.append_nil]
    exact hmapRange z k hk
  have hreversePerm : ∀ {p d : ℕ} {z : List ℕ}, z.length = n → p ≤ n → d ≤ p →
      d ≤ n - p →
      List.Perm (reverseSelectionValues n z p d ++ selection z (n - p) d) z := by
    intro p d z hzlen hp hdp hdn
    have hpos := reverseSelectionPositions_partition hp hdp hdn
    have hmap := hpos.map (fun i => z.getD i 0)
    rw [List.map_append] at hmap
    rw [hmapRange z n (by omega)] at hmap
    have htake : z.take n = z := by rw [← hzlen, List.take_length]
    rw [htake] at hmap
    exact hmap
  have hvaluesBounds : ∀ {p d : ℕ} {z : List ℕ}, IsPerm n z → p ≤ n → d ≤ p →
      ∀ v ∈ reverseSelectionValues n z p d, 1 ≤ v ∧ v ≤ n := by
    intro p d z hz hp hdp v hv
    have hzlen : z.length = n := by simpa [IsPerm] using hz.length_eq
    have hvz : v ∈ z := by
      simp only [reverseSelectionValues, valuesAt, List.mem_map] at hv
      rcases hv with ⟨i, hi, rfl⟩
      simp only [reverseSelectionPositions, List.mem_map] at hi
      rcases hi with ⟨j, hj, rfl⟩
      have hj' := hbound hdp hj
      rw [List.getD_eq_getElem z 0 (by omega)]
      exact List.getElem_mem _
    have hv' : v ∈ List.range' 1 n := hz.subset hvz
    simp only [List.mem_range'] at hv'
    rcases hv' with ⟨i, hi, rfl⟩
    omega
  have hselectionRU : ∀ {p d : ℕ} {z : List ℕ}, z.length = n → p ≤ n → d ≤ p →
      d ≤ n - p →
      selection (RU n z) p d =
        (reverseSelectionValues n z p d).map (fun v => n + 1 - v) := by
    intro p d z hzlen hp hdp hdn
    unfold selection reverseSelectionValues valuesAt reverseSelectionPositions RU
    simp only [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' := hbound hdp hi
    have hsum : p + d ≤ n := by omega
    simp only [Function.comp_apply]
    have hiru : i < (z.reverse.map (fun v => n + 1 - v)).length := by simp [hzlen]; omega
    rw [List.getD_eq_getElem _ 0 hiru, List.getElem_map, List.getElem_reverse]
    have hiz : n - 1 - i < z.length := by omega
    rw [List.getD_eq_getElem z 0 hiz]
    have hind : z.length - 1 - i = n - 1 - i := by omega
    simp only [hind]
  intro p d q hp hdp hdn hq1 hqn
  let Q := n + 2 - q
  have hQ1 : 1 ≤ Q := by simp only [Q]; omega
  have hQn : Q ≤ n + 1 := by simp only [Q]; omega
  have hnp : n - p ≤ n := Nat.sub_le _ _
  have hrest : n - (n - p) = p := by omega
  have hold := hF (n - p) d Q hnp hdn (by simpa only [hrest] using hdp) hQ1 hQn
  have hxlen : x.length = n := by simpa [IsPerm] using hx.length_eq
  have hylen : y.length = n := by simpa [IsPerm] using hy.length_eq
  have hruXlen : (RU n x).length = n := by simp [RU, hxlen]
  rw [← hselectionZero (RU n x) p (by omega)]
  rw [hselectionRU hxlen hp (Nat.zero_le _) (Nat.zero_le _)]
  rw [hselectionRU hylen hp hdp hdn]
  have hcompX := countGE_complement_add hq1 hqn
    (hvaluesBounds hx hp (Nat.zero_le _))
  have hcompY := countGE_complement_add hq1 hqn
    (hvaluesBounds hy hp hdp)
  have hrevLen : ∀ {p d : ℕ} {z : List ℕ}, d ≤ p →
      (reverseSelectionValues n z p d).length = p := by
    intro p d z hdp
    simp [reverseSelectionValues, valuesAt, reverseSelectionPositions, selectionPositions]
    omega
  rw [hrevLen (Nat.zero_le p)] at hcompX
  rw [hrevLen hdp] at hcompY
  have hpartX : countGE Q (reverseSelectionValues n x p 0 ++ selection x (n - p) 0) =
      countGE Q x := (hreversePerm hxlen hp (Nat.zero_le _) (Nat.zero_le _)).countP_eq _
  have hpartY : countGE Q (reverseSelectionValues n y p d ++ selection y (n - p) d) =
      countGE Q y := (hreversePerm hylen hp hdp hdn).countP_eq _
  have happend : ∀ (q : ℕ) (u v : List ℕ),
      countGE q (u ++ v) = countGE q u + countGE q v := by
    intro q u v
    simp [countGE]
  rw [happend] at hpartX hpartY
  rw [hselectionZero x (n - p) (by omega)] at hpartX
  have htotal : countGE Q x = countGE Q y := (hx.trans hy.symm).countP_eq _
  simp only [Q] at hold hpartX hpartY htotal
  omega
private def oldPosition (s j : ℕ) : ℕ :=
  if j < s - 1 then j else if (j - (s - 1)) % 2 = 0 then j + 2 else j
private def selectedOldPositions (m s p d : ℕ) : List ℕ :=
  (List.range m).filter (fun j => decide (oldPosition s j ∈ selectionPositions p d))
private def oldPositionInv (s k : ℕ) : ℕ :=
  if k < s - 1 then k else if (k - s) % 2 = 0 then k else k - 2
private lemma selected_position_decomposition {n m s p d : ℕ}
    (hn : n = m + 1) (hs1 : 1 ≤ s) (hsn : s ≤ n) (hns : (n - s) % 2 = 0)
    (hp : p ≤ n) (hdp : d ≤ p) (hdn : d ≤ n - p) :
    List.Perm (selectionPositions p d)
      ((if s - 1 ∈ selectionPositions p d then [s - 1] else []) ++
        (selectedOldPositions m s p d).map (oldPosition s)) := by
  have hinjective : ∀ {i j : ℕ}, oldPosition s i = oldPosition s j → i = j := by
    intro i j hij
    unfold oldPosition at hij
    split_ifs at hij with hi hip hj hjp <;> omega
  have hneMax : ∀ {j : ℕ}, oldPosition s j ≠ s - 1 := by
    intro j
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hinv : ∀ {k : ℕ}, k < n → k ≠ s - 1 →
      oldPositionInv s k < m ∧ oldPosition s (oldPositionInv s k) = k := by
    intro k hk hne
    unfold oldPositionInv oldPosition
    split_ifs with hkpre hkpar hjpre hjpar <;> omega
  have hselMem : ∀ {j : ℕ}, j ∈ selectedOldPositions m s p d ↔
      j < m ∧ oldPosition s j ∈ selectionPositions p d := by
    intro j
    simp [selectedOldPositions]
  have hselNodup : ∀ p d : ℕ, (selectionPositions p d).Nodup := by
    intro p d
    rw [selectionPositions, List.nodup_append]
    refine ⟨List.nodup_range, List.nodup_range.map ?_, ?_⟩
    · intro a b h
      change p - d + 2 * a + 1 = p - d + 2 * b + 1 at h
      omega
    · intro i hi k hk
      simp only [List.mem_range] at hi
      simp only [List.mem_map, List.mem_range] at hk
      rcases hk with ⟨j, hj, rfl⟩
      omega
  have himage : ((selectedOldPositions m s p d).map (oldPosition s)).Nodup := by
    exact (List.Nodup.filter _ List.nodup_range).map (by
      intro i j h
      exact hinjective h)
  have hright :
      (((if s - 1 ∈ selectionPositions p d then [s - 1] else []) ++
        (selectedOldPositions m s p d).map (oldPosition s))).Nodup := by
    split_ifs with hmax
    · rw [List.nodup_append]
      refine ⟨by simp, himage, ?_⟩
      intro i hi j hj heq
      simp only [List.mem_singleton] at hi
      subst i
      subst j
      simp only [List.mem_map] at hj
      rcases hj with ⟨k, hk, hkeq⟩
      exact hneMax hkeq
    · simpa using himage
  apply (List.perm_ext_iff_of_nodup (hselNodup p d) hright).mpr
  intro k
  simp only [List.mem_append, List.mem_map]
  constructor
  · intro hk
    by_cases heq : k = s - 1
    · left
      split_ifs with hmax
      · simp [heq]
      · exact False.elim (hmax (heq ▸ hk))
    · right
      have hkb : k < p + d := by
        simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map] at hk
        rcases hk with hk | ⟨i, hi, rfl⟩ <;> omega
      have hsum : p + d ≤ n := by omega
      obtain ⟨hj, hpos⟩ := hinv (by omega) heq
      refine ⟨oldPositionInv s k, ?_, hpos⟩
      rw [hselMem]
      refine ⟨hj, ?_⟩
      rw [hpos]
      exact hk
  · rintro (hk | ⟨j, hj, rfl⟩)
    · split_ifs at hk with hmax
      · simp only [List.mem_singleton] at hk
        subst k
        exact hmax
      · simp at hk
    · rw [hselMem] at hj
      exact hj.2
private lemma swapPairs_length : ∀ x : List ℕ, (swapPairs x).length = x.length
  | [] => rfl
  | [a] => rfl
  | a :: b :: t => by simp [swapPairs, swapPairs_length t]
private lemma swapPairs_perm : ∀ x : List ℕ, (swapPairs x).Perm x
  | [] => .refl []
  | [a] => .refl [a]
  | a :: b :: t => by
      simpa [swapPairs] using
        (List.Perm.swap a b (swapPairs t)).trans ((swapPairs_perm t).cons b |>.cons a)
private def pairPosition (k : ℕ) : ℕ := if k % 2 = 0 then k + 1 else k - 1
private lemma swapPairs_getD : ∀ (x : List ℕ) (k : ℕ),
    x.length % 2 = 0 → k < x.length →
      (swapPairs x).getD (pairPosition k) 0 = x.getD k 0
  | [], k => by simp
  | [a], k => by simp
  | a :: b :: t, k => by
      intro heven hk
      cases k with
      | zero => simp [swapPairs, pairPosition]
      | succ k =>
          cases k with
          | zero => simp [swapPairs, pairPosition]
          | succ k =>
              have ht : t.length % 2 = 0 := by
                change (t.length + 2) % 2 = 0 at heven
                omega
              have hk' : k < t.length := by simp at hk; omega
              have ih := swapPairs_getD t k ht hk'
              have hpair : pairPosition (k + 2) = pairPosition k + 2 := by
                unfold pairPosition
                split_ifs <;> omega
              simpa [swapPairs, hpair] using ih
/-- Ordinary insertion of a new maximum at the one-based position `r`. -/
def insertMax (n r : ℕ) (a : List ℕ) : List ℕ :=
  a.take (r - 1) ++ n :: a.drop (r - 1)
private lemma countGE_take_le_succ (q p : ℕ) (x : List ℕ) :
    countGE q (x.take p) ≤ countGE q (x.take (p - 1)) + 1 := by
  induction p generalizing x with
  | zero => simp [countGE]
  | succ p ih =>
      cases x with
      | nil => simp [countGE]
      | cons a x =>
          cases p with
          | zero =>
              by_cases h : q ≤ a <;> simp [countGE, h]
          | succ p =>
              have htail : countGE q (x.take (p + 1)) ≤ countGE q (x.take p) + 1 := by
                simpa using ih x
              simpa [countGE, List.countP_cons, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using
                Nat.add_le_add_left htail (if decide (q ≤ a) then 1 else 0)

/-- Matched ordinary and suffix-swapping insertion preserves the full selection invariant
    (Lemma 4). -/
theorem selectionInvariant_insert {n m r s : ℕ} {a b : List ℕ}
    (hn : n = m + 1) (ha : IsPerm m a) (hb : IsPerm m b)
    (hF : SelectionInvariant m a b) (hr1 : 1 ≤ r) (hrn : r ≤ n)
    (hs : s = 2 * r - n) (hs1 : 1 ≤ s) :
    SelectionInvariant n (insertMax n r a) (inss s b) := by
  have halen : a.length = m := by simpa [IsPerm] using ha.length_eq
  have hblen : b.length = m := by simpa [IsPerm] using hb.length_eq
  have hsn : s ≤ n := by omega
  have hsr : s ≤ r := by omega
  have hns : (n - s) % 2 = 0 := by
    have heq : n - s = 2 * (n - r) := by omega
    rw [heq]
    omega
  have hbound : ∀ {p d i : ℕ}, d ≤ p → i ∈ selectionPositions p d → i < p + d := by
    intro p d i hdp hi
    simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map] at hi
    rcases hi with hi | ⟨k, hk, rfl⟩ <;> omega
  have hselNodup : ∀ p d : ℕ, (selectionPositions p d).Nodup := by
    intro p d
    rw [selectionPositions, List.nodup_append]
    refine ⟨List.nodup_range, List.nodup_range.map ?_, ?_⟩
    · intro u v huv
      change p - d + 2 * u + 1 = p - d + 2 * v + 1 at huv
      omega
    · intro i hi k hk
      simp only [List.mem_range] at hi
      simp only [List.mem_map, List.mem_range] at hk
      rcases hk with ⟨j, hj, rfl⟩
      omega
  have hinterval : ∀ {p d i : ℕ}, d ≤ p →
      (i ∈ selectionPositions p d ↔ i < p - d ∨
        (p - d < i ∧ i < p + d ∧ (i - (p - d)) % 2 = 1)) := by
    intro p d i hdp
    simp only [selectionPositions, List.mem_append, List.mem_range, List.mem_map]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact Or.inl h
      · right
        constructor
        · omega
        constructor <;> omega
    · rintro (h | ⟨hlo, hhi, hodd⟩)
      · exact Or.inl h
      · right
        refine ⟨(i - (p - d)) / 2, ?_, ?_⟩ <;> omega
  have hrowF0 : ∀ {p d : ℕ}, d ≤ p → p + d < s →
      List.Perm (selectedOldPositions m s p d) (selectionPositions p d) := by
    intro p d hdp hzs
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup p d)).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hj⟩
      unfold oldPosition at hj
      split_ifs at hj with hpre heven
      · exact hj
      · have := hbound hdp hj
        omega
      · have := hbound hdp hj
        omega
    · intro hj
      have hjb := hbound hdp hj
      refine ⟨by omega, ?_⟩
      unfold oldPosition
      rw [if_pos (by omega)]
      exact hj
  have hrowF1 : ∀ {p : ℕ}, s ≤ p → (p - s) % 2 = 0 → p ≤ m + 1 →
      List.Perm (selectedOldPositions m s p 0) (selectionPositions (p - 1) 0) := by
    intro p hsp hpar hp
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup (p - 1) 0)).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq,
      selectionPositions, List.mem_append, List.mem_map]
    simp only [Nat.sub_zero, not_lt_zero, false_and, exists_const, or_false]
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hrowF2 : ∀ {p d : ℕ}, s ≤ p - d → (p - d - s) % 2 = 0 → 1 ≤ d →
      p ≤ n → d ≤ p → d ≤ n - p →
      List.Perm (selectedOldPositions m s p d) (selectionPositions (p - 1) (d - 1)) := by
    intro p d hsp hpar hd1 hp hdp hdn
    obtain ⟨t, ht⟩ : ∃ t, p - d - s = 2 * t := ⟨(p - d - s) / 2, by omega⟩
    have hdp' : d - 1 ≤ p - 1 := by omega
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup (p - 1) (d - 1))).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    rw [hinterval hdp, hinterval hdp']
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hrowF3 : ∀ {p d : ℕ}, s ≤ p - d → (p - d - s) % 2 = 1 →
      p ≤ n → d ≤ p → d ≤ n - p →
      List.Perm (selectedOldPositions m s p d) (selectionPositions (p - 1) (d + 1)) := by
    intro p d hsp hpar hp hdp hdn
    obtain ⟨t, ht⟩ : ∃ t, p - d - s = 2 * t + 1 := ⟨(p - d - s) / 2, by omega⟩
    obtain ⟨h, hh⟩ : ∃ h, n - s = 2 * h := ⟨(n - s) / 2, by omega⟩
    have hdp' : d + 1 ≤ p - 1 := by omega
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup (p - 1) (d + 1))).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    rw [hinterval hdp, hinterval hdp']
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hrowF4 : ∀ {p d : ℕ}, p - d < s → s ≤ p + d →
      (s - (p - d)) % 2 = 0 → p ≤ n → d ≤ p → d ≤ n - p →
      List.Perm (selectedOldPositions m s p d) (selectionPositions (p - 1) (d - 1)) := by
    intro p d hu hz hpar hp hdp hdn
    obtain ⟨t, ht⟩ : ∃ t, s - (p - d) = 2 * t :=
      ⟨(s - (p - d)) / 2, by omega⟩
    have hdp' : d - 1 ≤ p - 1 := by omega
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup (p - 1) (d - 1))).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    rw [hinterval hdp, hinterval hdp']
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hrowF5 : ∀ {p d : ℕ}, p - d < s → s ≤ p + d →
      (s - (p - d)) % 2 = 1 → p ≤ n → d ≤ p → d ≤ n - p →
      List.Perm (selectedOldPositions m s p d) (selectionPositions p d) := by
    intro p d hu hz hpar hp hdp hdn
    obtain ⟨t, ht⟩ : ∃ t, s - (p - d) = 2 * t + 1 :=
      ⟨(s - (p - d)) / 2, by omega⟩
    obtain ⟨h, hh⟩ : ∃ h, n - s = 2 * h := ⟨(n - s) / 2, by omega⟩
    apply (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
      (hselNodup p d)).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    rw [hinterval hdp, hinterval hdp]
    unfold oldPosition
    split_ifs with hpre heven <;> omega
  have hinsertPerm : (insertMax n r a).Perm (n :: a) := by
    unfold insertMax
    have hsplit : a.take (r - 1) ++ a.drop (r - 1) = a := List.take_append_drop _ _
    have hmid : (a.take (r - 1) ++ n :: a.drop (r - 1)).Perm
        (n :: (a.take (r - 1) ++ a.drop (r - 1))) := List.perm_middle
    simpa only [hsplit] using hmid
  have hinssPerm : (inss s b).Perm ((b.length + 1) :: b) := by
    unfold inss
    have hswap := swapPairs_perm (b.drop (s - 1))
    have hsplit : b.take (s - 1) ++ b.drop (s - 1) = b := List.take_append_drop _ _
    have happ := (hswap.cons (b.length + 1)).append_left (b.take (s - 1))
    exact happ.trans (by
      simpa only [hsplit] using
        (List.perm_middle (l₁ := b.take (s - 1)) (l₂ := b.drop (s - 1))
          (a := b.length + 1)))
  have hcountZero : ∀ {q : ℕ} {z : List ℕ}, (∀ v ∈ z, v < q) → countGE q z = 0 := by
    intro q z hz
    induction z with
    | nil => rfl
    | cons c z ih =>
        have hc := hz c (by simp)
        have hz' : ∀ v ∈ z, v < q := by intro v hv; exact hz v (by simp [hv])
        have hdec : decide (q ≤ c) = false := by simp [Nat.not_le.mpr hc]
        simp only [countGE, List.countP_cons, hdec, Bool.false_eq_true, ↓reduceIte]
        exact ih hz'
  have hgetOld : ∀ {j : ℕ}, j < m →
      (inss s b).getD (oldPosition s j) 0 = b.getD j 0 := by
    intro j hj
    by_cases hpre : j < s - 1
    · have hslen : s - 1 ≤ b.length := by omega
      have hjtake : j < (b.take (s - 1)).length := by simp; omega
      unfold inss oldPosition
      rw [if_pos hpre]
      rw [List.getD_append _ _ 0 j hjtake]
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getD_eq_getElem b 0 (by omega)]
      exact (b.getElem_take' (by omega) hpre).symm
    · have hslen : s - 1 ≤ b.length := by omega
      have hsuflen : (b.drop (s - 1)).length = n - s := by simp [hblen]; omega
      have hseven : (b.drop (s - 1)).length % 2 = 0 := by rw [hsuflen]; exact hns
      have hjge : s - 1 ≤ j := Nat.le_of_not_gt hpre
      have hkj : j = s - 1 + (j - (s - 1)) := by omega
      have hklt : j - (s - 1) < (b.drop (s - 1)).length := by simp [hblen]; omega
      have hsuf : s ≤ oldPosition s j ∧
          oldPosition s j - s = pairPosition (j - (s - 1)) := by
        unfold oldPosition pairPosition
        split_ifs <;> omega
      unfold inss
      rw [List.getD_append_right _ _ 0 _ (by simp; omega)]
      have htakelen : (b.take (s - 1)).length = s - 1 := by simp [hslen]
      rw [htakelen]
      have hrel : oldPosition s j - (s - 1) = pairPosition (j - (s - 1)) + 1 := by
        omega
      rw [hrel]
      simp only [List.getD_cons_succ]
      rw [swapPairs_getD _ _ hseven hklt]
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getD_eq_getElem b 0 (by omega)]
      simp only [List.getElem_drop]
      congr 1
      omega
  have hselectionPerm : ∀ {p d : ℕ}, p ≤ n → d ≤ p → d ≤ n - p →
      List.Perm (selection (inss s b) p d)
        ((if s - 1 ∈ selectionPositions p d then [n] else []) ++
          valuesAt b (selectedOldPositions m s p d)) := by
    intro p d hp hdp hdn
    have hpos := (selected_position_decomposition hn hs1 hsn hns hp hdp hdn).map
      (fun i => (inss s b).getD i 0)
    unfold selection valuesAt at ⊢
    rw [List.map_append, List.map_map] at hpos
    have holdmap :
        List.map ((fun i => (inss s b).getD i 0) ∘ oldPosition s)
            (selectedOldPositions m s p d) =
          List.map (fun i => b.getD i 0) (selectedOldPositions m s p d) := by
      apply List.map_congr_left
      intro j hj
      simp only [selectedOldPositions, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      exact hgetOld hj.1
    rw [holdmap] at hpos
    split_ifs at hpos ⊢ with hmax
    · have hmaxval : (inss s b).getD (s - 1) 0 = n := by
        unfold inss
        have hslen : s - 1 ≤ b.length := by omega
        rw [List.getD_append_right _ _ 0 _ (by simp [hslen])]
        have htakelen : (b.take (s - 1)).length = s - 1 := by simp [hslen]
        rw [htakelen]
        simp [hblen, hn]
      simp only [List.map_cons, List.map_nil] at hpos ⊢
      rw [hmaxval] at hpos
      exact hpos
    · simpa using hpos
  have hcountMem : ∀ {p d p' d' q : ℕ}, p ≤ n → d ≤ p → d ≤ n - p →
      s - 1 ∈ selectionPositions p d → q ≤ n →
      List.Perm (selectedOldPositions m s p d) (selectionPositions p' d') →
      countGE q (selection (inss s b) p d) = 1 + countGE q (selection b p' d') := by
    intro p d p' d' q hp hdp hdn hmax hq hrow
    have hsel : countGE q (selection (inss s b) p d) =
        countGE q ((if s - 1 ∈ selectionPositions p d then [n] else []) ++
          valuesAt b (selectedOldPositions m s p d)) :=
      (hselectionPerm hp hdp hdn).countP_eq _
    have hold : countGE q (valuesAt b (selectedOldPositions m s p d)) =
        countGE q (selection b p' d') := (hrow.map (fun i => b.getD i 0)).countP_eq _
    rw [if_pos hmax] at hsel
    rw [show countGE q ([n] ++ valuesAt b (selectedOldPositions m s p d)) =
        countGE q [n] + countGE q (valuesAt b (selectedOldPositions m s p d)) by
      simp [countGE, hq, Nat.add_comm]] at hsel
    rw [hold] at hsel
    simpa [countGE, hq, Nat.add_comm] using hsel
  have hcountNotMem : ∀ {p d p' d' q : ℕ}, p ≤ n → d ≤ p → d ≤ n - p →
      s - 1 ∉ selectionPositions p d →
      List.Perm (selectedOldPositions m s p d) (selectionPositions p' d') →
      countGE q (selection (inss s b) p d) = countGE q (selection b p' d') := by
    intro p d p' d' q hp hdp hdn hmax hrow
    have hsel : countGE q (selection (inss s b) p d) =
        countGE q ((if s - 1 ∈ selectionPositions p d then [n] else []) ++
          valuesAt b (selectedOldPositions m s p d)) :=
      (hselectionPerm hp hdp hdn).countP_eq _
    have hold : countGE q (valuesAt b (selectedOldPositions m s p d)) =
        countGE q (selection b p' d') := (hrow.map (fun i => b.getD i 0)).countP_eq _
    rw [if_neg hmax] at hsel
    rw [show countGE q ([] ++ valuesAt b (selectedOldPositions m s p d)) =
        countGE q [] + countGE q (valuesAt b (selectedOldPositions m s p d)) by
      simp [countGE]] at hsel
    rw [hold] at hsel
    simpa [countGE] using hsel
  intro p d q hp hdp hdn hq1 hqn
  by_cases hq : q ≤ n
  · have hsourceBefore : p < r →
        countGE q ((insertMax n r a).take p) = countGE q (a.take p) := by
      intro hpr
      have htake : (insertMax n r a).take p = a.take p := by
        unfold insertMax
        rw [List.take_append_of_le_length]
        · rw [List.take_take]
          congr 1
          omega
        · simp
          omega
      rw [htake]
    have hsourceAfter :
        countGE q ((insertMax n r a).take p) ≤ 1 + countGE q (a.take (p - 1)) := by
      by_cases hpr : p < r
      · rw [hsourceBefore hpr]
        have := countGE_take_le_succ q p a
        omega
      · have hperm : ((insertMax n r a).take p).Perm (n :: a.take (p - 1)) := by
          unfold insertMax
          have hpre : (a.take (r - 1)).length = r - 1 := by simp; omega
          rw [List.take_append]
          simp only [hpre]
          have hsub : p - (r - 1) = p - r + 1 := by omega
          rw [hsub]
          simp only [List.take_succ_cons]
          have htakepre : (a.take (r - 1)).take p = a.take (r - 1) :=
            (List.take_eq_self_iff _).mpr (by simp; omega)
          have hmid :
              (a.take (r - 1) ++ n :: (a.drop (r - 1)).take (p - r)).Perm
                (n :: (a.take (r - 1) ++ (a.drop (r - 1)).take (p - r))) :=
            List.perm_middle
          have hjoin : a.take (r - 1) ++ (a.drop (r - 1)).take (p - r) =
              a.take (p - 1) := by
            have hadd : a.take ((r - 1) + (p - r)) =
                a.take (r - 1) ++ (a.drop (r - 1)).take (p - r) := List.take_add
            have hsum : (r - 1) + (p - r) = p - 1 := by omega
            rw [← hsum]
            exact hadd.symm
          rw [htakepre]
          simpa only [hjoin] using hmid
        have hc : countGE q ((insertMax n r a).take p) =
            countGE q (n :: a.take (p - 1)) := hperm.countP_eq _
        rw [hc]
        simp [countGE, hq, Nat.add_comm]
    by_cases hF0 : p + d < s
    · have hrow := hrowF0 hdp hF0
      have hmax : s - 1 ∉ selectionPositions p d := by
        intro hmem
        have := hbound hdp hmem
        omega
      have ht := hcountNotMem (q := q) hp hdp hdn hmax hrow
      have hold := hF p d q (by omega) hdp (by omega) hq1 (by omega)
      rw [hsourceBefore (by omega), ht]
      exact hold
    · have hsz : s ≤ p + d := Nat.le_of_not_gt hF0
      by_cases hsu : s ≤ p - d
      · rcases Nat.mod_two_eq_zero_or_one (p - d - s) with hpar | hpar
        · by_cases hd0 : d = 0
          · subst d
            have hrow := hrowF1 (by simpa using hsu) hpar (by omega)
            have hmax : s - 1 ∈ selectionPositions p 0 := by
              rw [hinterval (Nat.zero_le p)]
              simp
              omega
            have ht := hcountMem hp (Nat.zero_le _) (Nat.zero_le _) hmax hq hrow
            have hold := hF (p - 1) 0 q (by omega) (Nat.zero_le _) (Nat.zero_le _) hq1 (by omega)
            rw [ht]
            simp only [Nat.sub_zero] at hsourceAfter hold ⊢
            omega
          · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
            have hrow := hrowF2 hsu hpar hd1 hp hdp hdn
            have hmax : s - 1 ∈ selectionPositions p d := by
              rw [hinterval hdp]
              omega
            have ht := hcountMem hp hdp hdn hmax hq hrow
            have hold := hF (p - 1) (d - 1) q (by omega) (by omega) (by omega) hq1 (by omega)
            rw [ht]
            omega
        · have hrow := hrowF3 hsu hpar hp hdp hdn
          have hmax : s - 1 ∈ selectionPositions p d := by
            rw [hinterval hdp]
            omega
          have ht := hcountMem hp hdp hdn hmax hq hrow
          have hold := hF (p - 1) (d + 1) q (by omega) (by omega) (by omega) hq1 (by omega)
          rw [ht]
          omega
      · have hus : p - d < s := Nat.lt_of_not_ge hsu
        rcases Nat.mod_two_eq_zero_or_one (s - (p - d)) with hpar | hpar
        · have hrow := hrowF4 hus hsz hpar hp hdp hdn
          have hmax : s - 1 ∈ selectionPositions p d := by
            rw [hinterval hdp]
            omega
          have ht := hcountMem hp hdp hdn hmax hq hrow
          have hold := hF (p - 1) (d - 1) q (by omega) (by omega) (by omega) hq1 (by omega)
          rw [ht]
          omega
        · have hrow := hrowF5 hus hsz hpar hp hdp hdn
          have hmax : s - 1 ∉ selectionPositions p d := by
            rw [hinterval hdp]
            omega
          have ht := hcountNotMem (q := q) hp hdp hdn hmax hrow
          have hold := hF p d q (by omega) hdp (by omega) hq1 (by omega)
          rw [hsourceBefore (by omega), ht]
          exact hold
  · have hqeq : q = n + 1 := by omega
    subst q
    apply Nat.le_of_eq
    have hsourceZero : countGE (n + 1) ((insertMax n r a).take p) = 0 := by
      apply hcountZero
      intro v hv
      have hv' : v ∈ insertMax n r a := (List.take_sublist p _).subset hv
      have hpins := hinsertPerm.subset hv'
      simp only [List.mem_cons] at hpins
      rcases hpins with hvn | hva
      · omega
      · have hva' : v ∈ List.range' 1 m := ha.subset hva
        simp only [List.mem_range'] at hva'
        rcases hva' with ⟨i, hi, rfl⟩
        omega
    have htargetZero : countGE (n + 1) (selection (inss s b) p d) = 0 := by
      apply hcountZero
      intro v hv
      simp only [selection, List.mem_map] at hv
      rcases hv with ⟨i, hi, rfl⟩
      have hib := hbound hdp hi
      have hisum : p + d ≤ n := by omega
      have houtlen : (inss s b).length = n := by
        simp [inss, swapPairs_length, hblen, hn]
        omega
      rw [List.getD_eq_getElem _ 0 (by omega)]
      have hvout : (inss s b)[i] ∈ inss s b := List.getElem_mem _
      have hpout := hinssPerm.subset hvout
      simp only [List.mem_cons] at hpout
      rcases hpout with hvmax | hvb
      · omega
      · have hvb' := hb.subset hvb
        simp only [List.mem_range'] at hvb'
        rcases hvb' with ⟨j, hj, hval⟩
        rw [hval]
        omega
    rw [hsourceZero, htargetZero]

end D5.S3.Combinatorics.PanSkanderaWangBruhat
