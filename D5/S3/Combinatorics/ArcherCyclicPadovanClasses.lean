/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanClasses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanClasses
   mirror-E: none(waiver:counting-classes-for-cyclic-padovan-proof)
   anchors: []
   utility: none
   digest: Rooted avoiders and an auxiliary class organize the Padovan count. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanSuccessor
import D5.S3.Combinatorics.ArcherCyclicTetranacciSuccessor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanClasses

open ArcherCyclicDefs ArcherCyclicTetranacciCycleWords

def circleWords (n : ℕ) : Set (List ℕ) :=
  {w | w.Perm (List.range' 1 n) ∧ w.head? = some 1 ∧
    ∀ r < n, ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)}

def goodWords (n : ℕ) : Set (List ℕ) :=
  {w | w ∈ circleWords n ∧ ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w)}

def tailCondition (w : List ℕ) : Prop :=
  let q := (oneLine w).tail
  ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q ∧
    ¬ ∃ c d, [c, d].Sublist q ∧ d < c ∧ c < w.tail.headD 0

def auxWords (k : ℕ) : Set (List ℕ) :=
  {w | w ∈ circleWords (k + 1) ∧ tailCondition w}

theorem auxiliary_arc_ends_at_two (h : ℕ) (T R : List ℕ)
    (hR : R = List.range' 3 R.length)
    (hsep : ∀ y ∈ R, y < h)
    (hnd : (1 :: ((h :: T) ++ 2 :: R)).Nodup)
    (haux : tailCondition (1 :: ((h :: T) ++ 2 :: R))) :
    R = [] := by
  by_contra hne
  have hpos : 0 < R.length := by
    cases R with
    | nil => contradiction
    | cons a t => simp
  have h3 : 3 ∈ R := by
    rw [hR]
    exact List.mem_range'.mpr ⟨0, hpos, by simp⟩
  have h3h : 3 < h := hsep 3 h3
  have hline := ArcherCyclicPadovanSuccessor.oneLine_split_block h T R hR hnd
  have hq :
      ¬ ∃ c d, [c, d].Sublist
          (List.range' 3 R.length ++ [1] ++
            (List.range' (R.length + 3) (T.length + 1)).map
              (1 :: ((h :: T) ++ 2 :: R)).formPerm) ∧
          d < c ∧ c < h := by
    unfold tailCondition at haux
    rw [hline] at haux
    simpa [List.headD] using haux.2
  have hrange : List.range' 3 R.length =
      3 :: List.range' 4 (R.length - 1) := by
    rw [show R.length = (R.length - 1) + 1 by omega]
    rfl
  have hsub : [3, 1].Sublist
      (List.range' 3 R.length ++ [1] ++
        (List.range' (R.length + 3) (T.length + 1)).map
          (1 :: ((h :: T) ++ 2 :: R)).formPerm) := by
    rw [hrange]
    apply List.Sublist.cons_cons
    have hinner : ([1] : List ℕ).Sublist
        (List.range' 4 (R.length - 1) ++ [1]) :=
      List.sublist_append_of_sublist_right (List.Sublist.refl [1])
    exact List.sublist_append_of_sublist_left hinner
  exact hq ⟨3, 1, hsub, by omega, h3h⟩

theorem auxiliary_word_shape (k : ℕ) (hk : 1 ≤ k) (w : List ℕ)
    (hw : w ∈ auxWords k) :
    (∃ R, w = 1 :: 2 :: R) ∨
      (∃ H, H ≠ [] ∧ w = 1 :: (H ++ [2])) := by
  obtain ⟨⟨hperm, hhead, hcircle⟩, htailcond⟩ := hw
  rcases w with _ | ⟨a, s⟩
  · simp at hhead
  have ha : a = 1 := by simpa using hhead
  subst a
  have h2range : 2 ∈ List.range' 1 (k + 1) :=
    List.mem_range'.mpr ⟨1, by omega, by simp⟩
  have h2w : 2 ∈ 1 :: s := hperm.mem_iff.mpr h2range
  have h2s : 2 ∈ s := by simpa using h2w
  obtain ⟨L, R, hsplit⟩ := List.mem_iff_append.mp h2s
  have hwlen : (1 :: (L ++ 2 :: R)).length = k + 1 := by
    simpa [hsplit] using hperm.length_eq
  have hself : (1 :: (L ++ 2 :: R)).Perm
      (List.range' 1 (1 :: (L ++ 2 :: R)).length) := by
    simpa [hwlen, hsplit] using hperm
  have hav : ∀ r < (1 :: (L ++ 2 :: R)).length,
      ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: (L ++ 2 :: R)).rotate r) := by
    simpa [hwlen, hsplit] using hcircle
  by_cases hL : L = []
  · subst L
    left
    exact ⟨R, by simp [hsplit]⟩
  · obtain ⟨hsep, hR, _⟩ :=
      ArcherCyclicPadovanDecomposition.low_arc_forced L R hL hself hav
    rcases L with _ | ⟨h, T⟩
    · contradiction
    have hnd : (1 :: ((h :: T) ++ 2 :: R)).Nodup :=
      hself.nodup_iff.mpr List.nodup_range'
    have hRnil := auxiliary_arc_ends_at_two h T R hR
      (fun y hy => hsep h (by simp) y hy) hnd
      (by simpa [hsplit] using htailcond)
    subst R
    right
    exact ⟨h :: T, by simp, by simp [hsplit]⟩

theorem auxiliary_last_insert_iff (h : ℕ) (T : List ℕ)
    (hv : (1 :: h :: T).Perm (List.range' 1 (1 :: h :: T).length)) :
    tailCondition (1 :: ((h :: T).map
      (ArcherCyclicPadovanPatterns.raiseHigh 2) ++ [2])) ↔
      tailCondition (1 :: h :: T) := by
  have oneLine_perm (w : List ℕ) (hw : w.Perm (List.range' 1 w.length)) :
      (oneLine w).Perm (List.range' 1 w.length) := by
    have hnd : (oneLine w).Nodup :=
      List.Nodup.map w.formPerm.injective List.nodup_range'
    apply List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range'
    apply Finset.ext
    intro x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hw.mem_iff.mp (List.formPerm_mem_iff_mem.mpr (hw.mem_iff.mpr hy))
    · intro hx
      let y := w.formPerm.symm x
      have hyw : y ∈ w := by
        apply List.formPerm_mem_iff_mem.mp
        simpa [y] using (hw.mem_iff.mpr hx)
      refine List.mem_map.mpr ⟨y, hw.mem_iff.mp hyw, ?_⟩
      simp [y]
  let p := 1 :: h :: T
  let q := (oneLine p).tail
  let f := ArcherCyclicPadovanSuccessor.raiseSuccessor 2
  have hfmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [f, ArcherCyclicPadovanSuccessor.raiseSuccessor,
      ArcherCyclicPadovanPatterns.raiseHigh]
    split_ifs <;> omega
  have hpperm : p.Perm (List.range' 1 p.length) := by simpa [p] using hv
  have hqpositive (z : ℕ) (hz : z ∈ q) : 1 ≤ z := by
    have hline := oneLine_perm p hpperm
    exact List.left_le_of_mem_range'
      (hline.mem_iff.mp (List.mem_of_mem_tail hz))
  have hqmappositive (z : ℕ) (hz : z ∈ q.map f) : 1 < z := by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    have hypos := hqpositive y hy
    by_cases hy1 : y = 1
    · simp [f, ArcherCyclicPadovanSuccessor.raiseSuccessor, hy1]
    · have hnot : ¬ y < 2 := by omega
      simp only [f, ArcherCyclicPadovanSuccessor.raiseSuccessor, hy1,
        ↓reduceIte, ArcherCyclicPadovanPatterns.raiseHigh, hnot]
      omega
  have hpnd : p.Nodup := hpperm.nodup_iff.mpr List.nodup_range'
  have hhmem : h ∈ p := by simp [p]
  have hhr : h ∈ List.range' 1 p.length := hpperm.mem_iff.mp hhmem
  have hge : 1 ≤ h := List.left_le_of_mem_range' hhr
  have hne : h ≠ 1 := by
    intro heq
    exact (List.nodup_cons.mp hpnd).1 (by simp [heq])
  have hfh : f h = ArcherCyclicPadovanPatterns.raiseHigh 2 h := by
    simp [f, ArcherCyclicPadovanSuccessor.raiseSuccessor, hne]
  have hline : oneLine (1 :: ((h :: T).map
      (ArcherCyclicPadovanPatterns.raiseHigh 2) ++ [2])) =
      ArcherCyclicPadovanPatterns.raiseHigh 2 h :: 1 :: q.map f := by
    simpa [p, q, f, List.range', List.append_assoc] using
        ArcherCyclicPadovanSuccessor.oneLine_inserted_block h T 2 (by omega) hv
  have hpat (s : List ℕ) :
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (1 :: s) ↔
        ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 s := by
    constructor
    · rintro ⟨x, hx, hm, hs, ha⟩
      change [x 4, x 1, x 3, x 2].Sublist (1 :: s) at hs
      rcases List.cons_sublist_cons'.mp hs with htail | ⟨hfirst, _⟩
      · refine ⟨x, hx, ?_, htail, by simp⟩
        intro i hi hik
        apply htail.subset
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
          have hik' : i ≤ 4 := by simpa using hik
          omega
        rcases hi' with rfl | rfl | rfl | rfl <;> simp
      · have h12 := hx 1 (by omega) (by simp)
        have h23 := hx 2 (by omega) (by simp)
        have h34 := hx 3 (by omega) (by simp)
        simp only [Nat.reduceAdd] at h12 h23 h34
        omega
    · rintro ⟨x, hx, hm, hs, ha⟩
      refine ⟨x, hx, ?_, List.sublist_cons_of_sublist 1 hs, by simp⟩
      intro i hi hik
      exact List.mem_cons_of_mem _ (hm i hi hik)
  have hdescent :
      (∃ c d, [c, d].Sublist (1 :: q.map f) ∧ d < c ∧
        c < ArcherCyclicPadovanPatterns.raiseHigh 2 h) ↔
      (∃ c d, [c, d].Sublist (q.map f) ∧ d < c ∧
        c < ArcherCyclicPadovanPatterns.raiseHigh 2 h) := by
    constructor
    · rintro ⟨c, d, hcd, hdc, hca⟩
      rcases List.cons_sublist_cons'.mp hcd with htail | ⟨hfirst, hrest⟩
      · exact ⟨c, d, htail, hdc, hca⟩
      · have hd : d ∈ q.map f := hrest.subset (by simp)
        have h2d := hqmappositive d hd
        omega
    · rintro ⟨c, d, hcd, hdc, hca⟩
      exact ⟨c, d, List.sublist_cons_of_sublist 1 hcd, hdc, hca⟩
  unfold tailCondition
  rw [hline]
  simp only [List.tail_cons]
  simp only [List.headD_cons]
  change (¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (1 :: q.map f) ∧
      ¬ ∃ c d, [c, d].Sublist (1 :: q.map f) ∧ d < c ∧
        c < ArcherCyclicPadovanPatterns.raiseHigh 2 h) ↔
    (¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q ∧
      ¬ ∃ c d, [c, d].Sublist q ∧ d < c ∧ c < h)
  have hmap : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (q.map f) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q := by
    simpa using ArcherCyclicPadovanPatterns.contains_map_iff
      [4, 1, 3, 2] q f hfmono
  rw [hpat, hmap, hdescent, ← hfh,
    ArcherCyclicPadovanSuccessor.below_descent_map_iff q h f hfmono]

theorem front_insert_good_iff (s : List ℕ)
    (hv : (1 :: s).Perm (List.range' 1 (1 :: s).length)) :
    ArcherCyclicTetranacciInsertion.insertWord 1 (1 :: s) ∈
      goodWords (s.length + 2) ↔
    1 :: s ∈ goodWords (s.length + 1) := by
  have hraise : StrictMono (ArcherCyclicPadovanPatterns.raiseHigh 2) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [ArcherCyclicPadovanPatterns.raiseHigh]
    split_ifs <;> omega
  let v := 1 :: s
  let R := s.map (fun z => 1 + z)
  let w := ArcherCyclicTetranacciInsertion.insertWord 1 v
  have hvlen : v.length = s.length + 1 := rfl
  have hvTail : s.Perm (List.range' 2 s.length) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [v, List.range', Nat.add_comm] using hv
  have hsge (z : ℕ) (hz : z ∈ s) : 2 ≤ z :=
    List.left_le_of_mem_range' (hvTail.mem_iff.mp hz)
  have hRgt : ∀ z ∈ R, 2 < z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    have := hsge x hx
    omega
  have hw : w = 1 :: 2 :: R := by simp [w, v, R, ArcherCyclicTetranacciInsertion.insertWord]
  have hwlen : w.length = s.length + 2 := by simp [hw, R]
  have hmapRange : (List.range' 1 (1 :: s).length).map (fun z => 1 + z) =
      List.range' 2 (s.length + 1) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range'_1]
      omega
  have hmap : (v.map (fun z => 1 + z)).Perm (List.range' 2 (s.length + 1)) := by
    rw [← hmapRange]
    exact hv.map _
  have hwp : w.Perm (List.range' 1 (s.length + 2)) := by
    have hrange : List.range' 1 (s.length + 2) =
        1 :: List.range' 2 (s.length + 1) := by
      rw [show s.length + 2 = 1 + (s.length + 1) by omega,
        ← List.range'_append_1]
      rfl
    rw [hrange]
    simpa [w, ArcherCyclicTetranacciInsertion.insertWord] using hmap.cons 1
  have hnd : w.Nodup := by
    have hself : w.Perm (List.range' 1 w.length) := by
      have hlen : w.length = s.length + 2 := by simp [hw, R]
      simpa [hlen] using hwp
    exact hself.nodup_iff.mpr List.nodup_range'
  have hRcircle :
      (∀ r < (1 :: R).length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: R).rotate r)) ↔
      (∀ r < v.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (v.rotate r)) := by
    have hmapword : v.map (ArcherCyclicPadovanPatterns.raiseHigh 2) = 1 :: R := by
      have htailmap : s.map (ArcherCyclicPadovanPatterns.raiseHigh 2) = R := by
        apply List.map_congr_left
        intro z hz
        have hnot : ¬ z < 2 := by have := hsge z hz; omega
        simp only [ArcherCyclicPadovanPatterns.raiseHigh, hnot, ↓reduceIte]
        omega
      simp [v, htailmap, ArcherCyclicPadovanPatterns.raiseHigh]
    constructor
    · intro hc r hr hpat
      have hmapPat := (ArcherCyclicPadovanPatterns.contains_map_iff [1, 3, 2, 4]
        (v.rotate r) (ArcherCyclicPadovanPatterns.raiseHigh 2)
        hraise).mpr hpat
      rw [List.map_rotate, hmapword] at hmapPat
      exact hc r (by simp [v, R] at hr ⊢; omega) hmapPat
    · intro hc r hr hpat
      have hrot : (1 :: R).rotate r =
          (v.rotate r).map (ArcherCyclicPadovanPatterns.raiseHigh 2) := by
        rw [← hmapword, List.map_rotate]
      rw [hrot] at hpat
      have hplain := (ArcherCyclicPadovanPatterns.contains_map_iff [1, 3, 2, 4]
        (v.rotate r) (ArcherCyclicPadovanPatterns.raiseHigh 2)
        hraise).mp hpat
      exact hc r (by simp [v, R] at hr ⊢; omega) hplain
  have hcircequiv :
      (∀ r < w.length, ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) ↔
      (∀ r < v.length, ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (v.rotate r)) := by
    rw [hw]
    exact (ArcherCyclicPadovanInsertTwo.circular_avoidance_insert_two R
      (by simpa [hw] using hnd) hRgt).trans hRcircle
  have hmono : StrictMono (ArcherCyclicTetranacciSuccessor.relabel 1) := by
    apply strictMono_nat_of_lt_succ
    intro x
    by_cases hx0 : x = 0
    · subst x
      simp [ArcherCyclicTetranacciSuccessor.relabel]
    by_cases hx1 : x = 1
    · subst x
      simp [ArcherCyclicTetranacciSuccessor.relabel]
    have hx2 : 2 ≤ x := by omega
    have hx0' : x ≠ 0 := by omega
    have hx1' : x ≠ 1 := by omega
    have hnext0 : x + 1 ≠ 0 := by omega
    have hnext1 : x + 1 ≠ 1 := by omega
    simp only [ArcherCyclicTetranacciSuccessor.relabel, hx0', hx1',
      hnext0, hnext1, ↓reduceIte]
    omega
  have hcons (p : List ℕ) :
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (2 :: p) ↔
        ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 p := by
    constructor
    · rintro ⟨x, hx, hm, hs, _⟩
      change [x 4, x 1, x 3, x 2].Sublist (2 :: p) at hs
      rcases List.cons_sublist_cons'.mp hs with hs | ⟨hfirst, _⟩
      · refine ⟨x, hx, ?_, hs, by simp⟩
        intro i hi hik
        apply hs.subset
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases hi' with rfl | rfl | rfl | rfl <;> simp
      · have h12 := hx 1 (by omega) (by omega)
        have h23 := hx 2 (by omega) (by omega)
        have h34 := hx 3 (by omega) (by omega)
        simp only [Nat.reduceAdd] at h12 h23 h34
        omega
    · rintro ⟨x, hx, hm, hs, _⟩
      refine ⟨x, hx, ?_, List.sublist_cons_of_sublist 2 hs, by simp⟩
      intro i hi hik
      exact List.mem_cons_of_mem _ (hm i hi hik)
  have hpat : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine v) := by
    have hline := ArcherCyclicTetranacciSuccessor.oneLine_insert 1 s
      (by omega) (by simpa [v, Nat.add_comm] using hv)
    rw [show w = ArcherCyclicTetranacciInsertion.insertWord 1 (1 :: s) by rfl,
      hline]
    change ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4
      (2 :: (oneLine v).map (ArcherCyclicTetranacciSuccessor.relabel 1)) ↔ _
    rw [hcons]
    have hmap : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4
        ((oneLine v).map (ArcherCyclicTetranacciSuccessor.relabel 1)) ↔
        ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine v) := by
      simpa using ArcherCyclicPadovanPatterns.contains_map_iff
        [4, 1, 3, 2] (oneLine v) _ hmono
    exact hmap
  change (w ∈ goodWords (s.length + 2)) ↔ (v ∈ goodWords (s.length + 1))
  constructor
  · rintro ⟨⟨_, _, hc⟩, ho⟩
    exact ⟨⟨by simpa [v, Nat.add_comm] using hv, by simp [v],
      hcircequiv.mp (by simpa only [hwlen] using hc)⟩,
      fun hh => ho (hpat.mpr hh)⟩
  · rintro ⟨⟨_, _, hc⟩, ho⟩
    exact ⟨⟨hwp, by simp [hw],
      by simpa only [hwlen] using hcircequiv.mpr hc⟩,
      fun hh => ho (hpat.mp hh)⟩

theorem high_insert_good_iff (h : ℕ) (T : List ℕ) (m : ℕ)
    (hm : 2 ≤ m)
    (hv : (1 :: h :: T).Perm (List.range' 1 (1 :: h :: T).length)) :
    (1 :: ((h :: T).map (ArcherCyclicPadovanPatterns.raiseHigh m) ++
      2 :: List.range' 3 (m - 2))) ∈ goodWords (T.length + 1 + m) ↔
    (1 :: h :: T) ∈ auxWords (T.length + 1) := by
  have hraise : StrictMono (ArcherCyclicPadovanPatterns.raiseHigh m) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [ArcherCyclicPadovanPatterns.raiseHigh]
    split_ifs <;> omega
  let v := h :: T
  let old := 1 :: v
  let f := ArcherCyclicPadovanPatterns.raiseHigh m
  let w := 1 :: (v.map f ++ 2 :: List.range' 3 (m - 2))
  have holdlen : old.length = T.length + 2 := by simp [old, v]
  have hwlen : w.length = T.length + 1 + m := by
    simp [w, v]
    omega
  have hwp : w.Perm (List.range' 1 (T.length + 1 + m)) := by
    have hvTail : v.Perm (List.range' 2 v.length) := by
      apply List.Perm.cons_inv (a := 1)
      simpa [v, old, List.range', Nat.add_comm] using hv
    have hmapRange : (List.range' 2 v.length).map (ArcherCyclicPadovanPatterns.raiseHigh m) =
        List.range' (m + 1) v.length := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_range'_1] at hi ⊢
        simp only [ArcherCyclicPadovanPatterns.raiseHigh]
        split_ifs <;> omega
    have hhigh : (v.map f).Perm (List.range' (m + 1) v.length) := by
      rw [← hmapRange]
      exact hvTail.map (ArcherCyclicPadovanPatterns.raiseHigh m)
    have hlow : 2 :: List.range' 3 (m - 2) = List.range' 2 (m - 1) := by
      have hsub : m - 1 = (m - 2) + 1 := by omega
      rw [hsub]
      rfl
    have hjoin : (v.map f ++ 2 :: List.range' 3 (m - 2)).Perm
        (List.range' 2 (m - 1 + v.length)) := by
      have h₁ := hhigh.append_right (2 :: List.range' 3 (m - 2))
      have h₂ : (List.range' (m + 1) v.length ++ 2 :: List.range' 3 (m - 2)).Perm
          ((2 :: List.range' 3 (m - 2)) ++ List.range' (m + 1) v.length) :=
        List.perm_append_comm
      have h₃ : (2 :: List.range' 3 (m - 2)) ++ List.range' (m + 1) v.length =
          List.range' 2 (m - 1 + v.length) := by
        rw [hlow]
        have hstart : 2 + (m - 1) = m + 1 := by omega
        rw [← hstart, List.range'_append_1]
      exact (h₁.trans h₂).trans (h₃ ▸ List.Perm.refl _)
    have hfinal : 1 :: List.range' 2 (m - 1 + v.length) =
        List.range' 1 (T.length + 1 + m) := by
      have hlen : T.length + 1 + m = (m - 1 + v.length) + 1 := by
        simp [v]
        omega
      rw [hlen]
      rfl
    simpa [w, f, ← hfinal] using hjoin.cons 1
  have hsub : (1 :: v.map f).Sublist w := by
    change (1 :: v.map f).Sublist (1 :: (v.map f ++
      2 :: List.range' 3 (m - 2)))
    exact (List.sublist_append_left _ _).cons_cons 1
  have hcircleBack
      (hc : ∀ r < w.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) :
      ∀ r < old.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (old.rotate r) := by
    have hhigh := ArcherCyclicPadovanSubwords.circular_avoidance_sublist
      [1, 3, 2, 4] (1 :: v.map f) w hsub hc
    have hmapword : old.map f = 1 :: v.map f := by
      simp [old, f, ArcherCyclicPadovanPatterns.raiseHigh]
    intro r hr hpat
    have hmapPat := (ArcherCyclicPadovanPatterns.contains_map_iff [1, 3, 2, 4]
      (old.rotate r) f
      hraise).mpr hpat
    rw [List.map_rotate, hmapword] at hmapPat
    exact hhigh r (by simpa [old] using hr) hmapPat
  have hcircleForward
      (hc : ∀ r < old.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (old.rotate r)) :
      ∀ r < w.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r) := by
    have hh := ArcherCyclicPadovanDecomposition.inserted_word_circular_avoid
      v m hm (by simpa [old, v] using hv)
      (by simpa [old] using hc)
    simpa [w, f] using hh
  have hpat :
      (¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w)) ↔
        tailCondition old := by
    have hh := ArcherCyclicPadovanSuccessor.inserted_avoid_iff h T m hm hv
    simpa [w, old, v, f, tailCondition, List.headD] using hh
  change (w ∈ goodWords (T.length + 1 + m)) ↔
    (old ∈ auxWords (T.length + 1))
  constructor
  · rintro ⟨⟨_, _, hc⟩, ho⟩
    refine ⟨⟨?_, by simp [old], ?_⟩, hpat.mp ho⟩
    · simpa [holdlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hv
    · exact hcircleBack (by simpa only [hwlen] using hc)
  · rintro ⟨⟨_, _, hc⟩, ho⟩
    refine ⟨⟨hwp, by simp [w], ?_⟩, hpat.mpr ho⟩
    exact (by simpa only [hwlen] using hcircleForward hc)

theorem front_insert_aux_iff (s : List ℕ)
    (hv : (1 :: s).Perm (List.range' 1 (1 :: s).length)) :
    ArcherCyclicTetranacciInsertion.insertWord 1 (1 :: s) ∈
      auxWords (s.length + 1) ↔
    1 :: s ∈ goodWords (s.length + 1) := by
  have oneLine_perm (w : List ℕ) (hw : w.Perm (List.range' 1 w.length)) :
      (oneLine w).Perm (List.range' 1 w.length) := by
    have hnd : (oneLine w).Nodup :=
      List.Nodup.map w.formPerm.injective List.nodup_range'
    apply List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range'
    apply Finset.ext
    intro x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hw.mem_iff.mp (List.formPerm_mem_iff_mem.mpr (hw.mem_iff.mpr hy))
    · intro hx
      let y := w.formPerm.symm x
      have hyw : y ∈ w := by
        apply List.formPerm_mem_iff_mem.mp
        simpa [y] using (hw.mem_iff.mpr hx)
      refine List.mem_map.mpr ⟨y, hw.mem_iff.mp hyw, ?_⟩
      simp [y]
  let w := ArcherCyclicTetranacciInsertion.insertWord 1 (1 :: s)
  have hwlen : w.length = s.length + 2 := by
    simp [w, ArcherCyclicTetranacciInsertion.insertWord]
  have hthreshold : w.tail.headD 0 = 2 := by
    simp [w, ArcherCyclicTetranacciInsertion.insertWord]
  have hline := ArcherCyclicTetranacciSuccessor.oneLine_insert 1 s
    (by omega) (by simpa [Nat.add_comm] using hv)
  have hline2 : oneLine w =
      2 :: (oneLine (1 :: s)).map (ArcherCyclicTetranacciSuccessor.relabel 1) := by
    simpa [w, ArcherCyclicTetranacciSuccessor.lowPrefix] using hline
  have hcons (p : List ℕ) :
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (2 :: p) ↔
        ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 p := by
    constructor
    · rintro ⟨x, hx, hm, hs, _⟩
      change [x 4, x 1, x 3, x 2].Sublist (2 :: p) at hs
      rcases List.cons_sublist_cons'.mp hs with hs | ⟨hfirst, _⟩
      · refine ⟨x, hx, ?_, hs, by simp⟩
        intro i hi hik
        apply hs.subset
        have hi' : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases hi' with rfl | rfl | rfl | rfl <;> simp
      · have h12 := hx 1 (by omega) (by omega)
        have h23 := hx 2 (by omega) (by omega)
        have h34 := hx 3 (by omega) (by omega)
        simp only [Nat.reduceAdd] at h12 h23 h34
        omega
    · rintro ⟨x, hx, hm, hs, _⟩
      refine ⟨x, hx, ?_, List.sublist_cons_of_sublist 2 hs, by simp⟩
      intro i hi hik
      exact List.mem_cons_of_mem _ (hm i hi hik)
  have hpat : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w).tail := by
    rw [hline2]
    exact hcons _
  have htailiff
      (hp : w.Perm (List.range' 1 (s.length + 2))) :
      tailCondition w ↔ ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w) := by
    have hpself : w.Perm (List.range' 1 w.length) := by
      simpa [hwlen] using hp
    have hlineperm := oneLine_perm w hpself
    have hqpositive (z : ℕ) (hz : z ∈ (oneLine w).tail) : 1 ≤ z :=
      List.left_le_of_mem_range'
        (hlineperm.mem_iff.mp (List.mem_of_mem_tail hz))
    have hno : ¬ ∃ c d, [c, d].Sublist (oneLine w).tail ∧
        d < c ∧ c < 2 := by
      rintro ⟨c, d, hcd, hdc, hc2⟩
      have hd : d ∈ (oneLine w).tail := hcd.subset (by simp)
      have := hqpositive d hd
      omega
    change (¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w).tail ∧
        ¬ ∃ c d, [c, d].Sublist (oneLine w).tail ∧
          d < c ∧ c < w.tail.headD 0) ↔
      ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (oneLine w)
    rw [hthreshold]
    constructor
    · intro hh hocc
      exact hh.1 (hpat.mp hocc)
    · intro hh
      exact ⟨fun hocc => hh (hpat.mpr hocc), hno⟩
  have hgood := front_insert_good_iff s hv
  change (w ∈ auxWords (s.length + 1)) ↔
    ((1 :: s) ∈ goodWords (s.length + 1))
  constructor
  · rintro ⟨hc, ht⟩
    have hgoodNew : w ∈ goodWords (s.length + 2) :=
      ⟨hc, (htailiff hc.1).mp ht⟩
    exact hgood.mp hgoodNew
  · intro hold
    have hgoodNew := hgood.mpr hold
    exact ⟨hgoodNew.1, (htailiff hgoodNew.1.1).mpr hgoodNew.2⟩

theorem last_insert_aux_iff (h : ℕ) (T : List ℕ)
    (hv : (1 :: h :: T).Perm (List.range' 1 (1 :: h :: T).length)) :
    (1 :: ((h :: T).map (ArcherCyclicPadovanPatterns.raiseHigh 2) ++ [2])) ∈
      auxWords (T.length + 2) ↔
    (1 :: h :: T) ∈ auxWords (T.length + 1) := by
  have hraise : StrictMono (ArcherCyclicPadovanPatterns.raiseHigh 2) := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [ArcherCyclicPadovanPatterns.raiseHigh]
    split_ifs <;> omega
  let v := h :: T
  let old := 1 :: v
  let f := ArcherCyclicPadovanPatterns.raiseHigh 2
  let w := 1 :: (v.map f ++ [2])
  have holdlen : old.length = T.length + 2 := by simp [old, v]
  have hwlen : w.length = T.length + 3 := by simp [w, v]
  have hwp : w.Perm (List.range' 1 (T.length + 3)) := by
    have hvTail : v.Perm (List.range' 2 v.length) := by
      apply List.Perm.cons_inv (a := 1)
      simpa [v, old, List.range', Nat.add_comm] using hv
    have hmapRange : (List.range' 2 v.length).map f = List.range' 3 v.length := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_range'_1] at hi ⊢
        simp only [f, ArcherCyclicPadovanPatterns.raiseHigh]
        split_ifs <;> omega
    have hhigh : (v.map f).Perm (List.range' 3 v.length) := by
      rw [← hmapRange]
      exact hvTail.map f
    have hjoin : (v.map f ++ [2]).Perm (List.range' 2 (v.length + 1)) := by
      have h₁ := hhigh.append_right [2]
      have h₂ : (List.range' 3 v.length ++ [2]).Perm ([2] ++ List.range' 3 v.length) :=
        List.perm_append_comm
      have h₃ : [2] ++ List.range' 3 v.length = List.range' 2 (v.length + 1) := by
        rw [show [2] = List.range' 2 1 by rfl, List.range'_append_1]
        simp [Nat.add_comm]
      exact (h₁.trans h₂).trans (h₃ ▸ List.Perm.refl _)
    have hfinal : 1 :: List.range' 2 (v.length + 1) =
        List.range' 1 (T.length + 3) := by
      simp [v, List.range']
    simpa [w, hfinal] using hjoin.cons 1
  have hsub : (1 :: v.map f).Sublist w := by
    change (1 :: v.map f).Sublist (1 :: (v.map f ++ [2]))
    exact (List.sublist_append_left _ _).cons_cons 1
  have hcircleBack
      (hc : ∀ r < w.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) :
      ∀ r < old.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (old.rotate r) := by
    have hhigh := ArcherCyclicPadovanSubwords.circular_avoidance_sublist
      [1, 3, 2, 4] (1 :: v.map f) w hsub hc
    have hmapword : old.map f = 1 :: v.map f := by
      simp [old, f, ArcherCyclicPadovanPatterns.raiseHigh]
    intro r hr hpat
    have hmapPat := (ArcherCyclicPadovanPatterns.contains_map_iff [1, 3, 2, 4]
      (old.rotate r) f
      hraise).mpr hpat
    rw [List.map_rotate, hmapword] at hmapPat
    exact hhigh r (by simpa [old] using hr) hmapPat
  have hcircleForward
      (hc : ∀ r < old.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (old.rotate r)) :
      ∀ r < w.length,
        ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r) := by
    have hh := ArcherCyclicPadovanDecomposition.inserted_word_circular_avoid
      v 2 (by omega) (by simpa [old, v] using hv)
      (by simpa [old] using hc)
    simpa [w, f] using hh
  have hcondition : tailCondition w ↔ tailCondition old := by
    simpa [w, old, v, f] using auxiliary_last_insert_iff h T hv
  change (w ∈ auxWords (T.length + 2)) ↔
    (old ∈ auxWords (T.length + 1))
  constructor
  · rintro ⟨⟨_, _, hc⟩, ht⟩
    refine ⟨⟨?_, by simp [old], ?_⟩, hcondition.mp ht⟩
    · simpa [holdlen, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hv
    · exact hcircleBack (by simpa only [hwlen] using hc)
  · rintro ⟨⟨_, _, hc⟩, ht⟩
    refine ⟨⟨?_, by simp [w], ?_⟩, hcondition.mpr ht⟩
    · simpa [Nat.add_assoc] using hwp
    · exact (by simpa only [hwlen] using hcircleForward hc)

end D5.S3.Combinatorics.ArcherCyclicPadovanClasses
