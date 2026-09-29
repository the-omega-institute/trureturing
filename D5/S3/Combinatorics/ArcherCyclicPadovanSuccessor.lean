/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanSuccessor
   mirror-E: none(waiver:successor-list-block-form-for-padovan-proof)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The successor permutation of a split cycle word has the required one-line block form. -/

import D5.S3.Combinatorics.ArcherCyclicPadovanCycleWords
import D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanSuccessor

open ArcherCyclicTetranacciCycleWords
open ArcherCyclicPadovanPatterns ArcherCyclicPadovanDecomposition

theorem oneLine_split_block (h : ℕ) (T R : List ℕ)
    (hR : R = List.range' 3 R.length)
    (hnd : (1 :: ((h :: T) ++ 2 :: R)).Nodup) :
    oneLine (1 :: ((h :: T) ++ 2 :: R)) =
      h :: (List.range' 3 R.length ++ [1] ++
        (List.range' (R.length + 3) (T.length + 1)).map
          (1 :: ((h :: T) ++ 2 :: R)).formPerm) := by
  let H := h :: T
  let K := 2 :: R
  let w := 1 :: (H ++ K)
  have hK : K = List.range' 2 (R.length + 1) := by
    calc
      K = 2 :: R := rfl
      _ = 2 :: List.range' 3 R.length := congrArg (2 :: ·) hR
      _ = List.range' 2 (R.length + 1) := by
        have he : List.range' 2 (1 + R.length) =
            [2] ++ List.range' 3 R.length := by
          rw [← List.range'_append_1]
          rfl
        simpa [show R.length + 1 = 1 + R.length by omega] using he.symm
  have hwlen : w.length = R.length + 2 + H.length := by
    simp [w, H, K]
    omega
  have hfirst : w.formPerm 1 = h := by
    change (1 :: h :: (T ++ K)).formPerm 1 = h
    exact List.formPerm_apply_head 1 h (T ++ K) (by simpa [K] using hnd)
  have hentry (i : ℕ) (hi : i < R.length) :
      w.formPerm (2 + i) = 3 + i := by
    have hiK : i + 1 < K.length := by simp [K]; omega
    have hiw : H.length + 1 + i + 1 < w.length := by
      simp [w, K]
      omega
    have hget (j : ℕ) (hj : j < K.length) :
        w[H.length + 1 + j]'(by simp [w]; omega) = K[j] := by
      simp [w, show H.length + 1 + j = (H.length + j) + 1 by omega,
        List.getElem_cons_succ, List.getElem_append_right]
    have hki : K[i] = 2 + i := by
      have hki' : (List.range' 2 (R.length + 1))[i]'(by simp; omega) = 2 + i := by simp
      simpa only [← hK] using hki'
    have hki1 : K[i + 1] = 3 + i := by
      have hki' : (List.range' 2 (R.length + 1))[i + 1]'(by simp; omega) = 3 + i := by
        simp
        omega
      simpa only [← hK] using hki'
    have hform := List.formPerm_apply_lt_getElem w hnd
      (H.length + 1 + i) hiw
    rw [hget i (by omega)] at hform
    have hgetnext := hget (i + 1) hiK
    have hgetnext' : w[H.length + 1 + i + 1] = K[i + 1] := by
      simpa only [Nat.add_assoc] using hgetnext
    rw [hgetnext'] at hform
    rw [hki, hki1] at hform
    simpa [Nat.add_assoc] using hform
  have hmiddle : (List.range' 2 R.length).map w.formPerm =
      List.range' 3 R.length := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range'_1] at hi ⊢
      exact hentry i (by simpa using hi)
  have hlastval : K.getLast (by simp [K]) = R.length + 2 := by
    have hval : (List.range' 2 (R.length + 1)).getLast
        (by simp) = R.length + 2 := by
      simp [List.getLast_range']
      omega
    simpa only [← hK] using hval
  have hlast : w.formPerm (R.length + 2) = 1 := by
    have hlastw : w.getLast (by simp [w]) = R.length + 2 := by
      change (1 :: (H ++ K)).getLast (by simp) = R.length + 2
      rw [List.getLast_cons]
      · rw [List.getLast_append_of_right_ne_nil H K (by simp [K])]
        exact hlastval
      · simp [H]
    have hform := List.formPerm_apply_getLast 1 (H ++ K)
    simpa [w, hlastw] using hform
  have hrange : List.range' 1 w.length =
      [1] ++ List.range' 2 R.length ++ [R.length + 2] ++
        List.range' (R.length + 3) H.length := by
    have h₁ : List.range' 1 w.length =
        [1] ++ List.range' 2 (R.length + 1 + H.length) := by
      rw [hwlen, show R.length + 2 + H.length =
        1 + (R.length + 1 + H.length) by omega, ← List.range'_append_1]
      rfl
    have h₂ : List.range' 2 (R.length + 1 + H.length) =
        List.range' 2 R.length ++ [R.length + 2] ++
          List.range' (R.length + 3) H.length := by
      rw [show R.length + 1 + H.length = R.length + (1 + H.length) by omega,
        ← List.range'_append_1]
      rw [show 2 + R.length = R.length + 2 by omega,
        ← List.range'_append_1]
      simp [List.range'_one, Nat.add_assoc, List.append_assoc]
    simpa only [List.append_assoc] using h₁.trans (congrArg ([1] ++ ·) h₂)
  unfold oneLine
  rw [hrange]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [hfirst, hmiddle, hlast]
  rfl

def raiseSuccessor (m x : ℕ) : ℕ :=
  if x = 1 then 2 else raiseHigh m x

theorem below_descent_map_iff (q : List ℕ) (a : ℕ)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    (∃ c d, [c, d].Sublist (q.map f) ∧ d < c ∧ c < f a) ↔
      (∃ c d, [c, d].Sublist q ∧ d < c ∧ c < a) := by
  constructor
  · rintro ⟨c, d, hcd, hdc, hca⟩
    have hc : c ∈ q.map f := hcd.subset (by simp)
    have hd : d ∈ q.map f := hcd.subset (by simp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
    have hleft (z : ℕ) : Function.invFun f (f z) = z :=
      Function.leftInverse_invFun hf.injective z
    have hpre := hcd.map (Function.invFun f)
    have hsub : [x, y].Sublist q := by
      simpa [List.map_map, Function.comp_def, hleft] using hpre
    exact ⟨x, y, hsub, hf.lt_iff_lt.mp hdc, hf.lt_iff_lt.mp hca⟩
  · rintro ⟨c, d, hcd, hdc, hca⟩
    exact ⟨f c, f d, by simpa using hcd.map f, hf hdc, hf hca⟩

theorem oneLine_inserted_block (h : ℕ) (T : List ℕ) (m : ℕ)
    (hm : 2 ≤ m)
    (hv : (1 :: h :: T).Perm (List.range' 1 (1 :: h :: T).length)) :
    oneLine (1 :: (((h :: T).map (raiseHigh m)) ++
      2 :: List.range' 3 (m - 2))) =
    raiseHigh m h :: (List.range' 3 (m - 2) ++ [1] ++
      ((oneLine (1 :: h :: T)).tail.map (raiseSuccessor m))) := by
  let v := h :: T
  let p := 1 :: v
  let K := 2 :: List.range' 3 (m - 2)
  let w := 1 :: (v.map (raiseHigh m) ++ K)
  have hwp : (1 :: (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2))).Perm
      (List.range' 1 (v.length + m)) := by
    have hvTail : v.Perm (List.range' 2 v.length) := by
      apply List.Perm.cons_inv (a := 1)
      simpa [v, p, List.range', Nat.add_comm] using hv
    have hmapRange : (List.range' 2 v.length).map (raiseHigh m) =
        List.range' (m + 1) v.length := by
      apply List.ext_getElem
      · simp
      · intro i hi hi'
        simp only [List.getElem_map, List.getElem_range'_1] at hi ⊢
        simp only [raiseHigh]
        split_ifs <;> omega
    have hhigh : (v.map (raiseHigh m)).Perm (List.range' (m + 1) v.length) := by
      rw [← hmapRange]
      exact hvTail.map (raiseHigh m)
    have hlow : 2 :: List.range' 3 (m - 2) = List.range' 2 (m - 1) := by
      have hsub : m - 1 = (m - 2) + 1 := by omega
      rw [hsub]
      rfl
    have hjoin : (v.map (raiseHigh m) ++ 2 :: List.range' 3 (m - 2)).Perm
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
        List.range' 1 (v.length + m) := by
      have hlen : v.length + m = (m - 1 + v.length) + 1 := by omega
      rw [hlen]
      rfl
    rw [← hfinal]
    exact hjoin.cons 1
  have hwlen : w.length = v.length + m := by
    simp [w, K]
    omega
  have hnd : w.Nodup := by
    have : w.Perm (List.range' 1 w.length) := by
      rw [hwlen]
      exact hwp
    exact this.nodup_iff.mpr List.nodup_range'
  have hpnd : p.Nodup := hv.nodup_iff.mpr List.nodup_range'
  have hvperm : v.Perm (List.range' 2 v.length) := by
    apply List.Perm.cons_inv (a := 1)
    simpa [p, v, List.range', Nat.add_comm] using hv
  have hentry (j : ℕ) (hj : j < v.length) :
      w[j + 1]'(by simp [w, K]; omega) = (raiseHigh m) v[j] := by
    simp only [w, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa using hj), List.getElem_map]
  have hpentry (j : ℕ) (hj : j < v.length) :
      p[j + 1]'(by simp [p]; omega) = v[j] := by
    simp [p]
  have hnext (j : ℕ) (hj : j < v.length) :
      w.formPerm ((raiseHigh m) v[j]) =
        raiseSuccessor m (p.formPerm v[j]) := by
    by_cases hjnext : j + 1 < v.length
    · have hwpnext : j + 1 + 1 < w.length := by simp [w, K]; omega
      have hppnext : j + 1 + 1 < p.length := by simp [p]; omega
      have hnew : w.formPerm ((raiseHigh m) v[j]) =
          (raiseHigh m) v[j + 1] := by
        rw [← hentry j hj, List.formPerm_apply_lt_getElem w hnd (j + 1) hwpnext]
        simpa only [Nat.add_assoc] using hentry (j + 1) hjnext
      have hold : p.formPerm v[j] = v[j + 1] := by
        rw [← hpentry j hj, List.formPerm_apply_lt_getElem p hpnd (j + 1) hppnext]
        simpa only [Nat.add_assoc] using hpentry (j + 1) hjnext
      rw [hnew, hold]
      have hne : v[j + 1] ≠ 1 := by
        intro heq
        have hzero : p[0]'(by simp [p]) = 1 := rfl
        have hsame : p[j + 1 + 1] = p[0] := by
          calc
            p[j + 1 + 1] = v[j + 1] := by
              simpa only [Nat.add_assoc] using hpentry (j + 1) hjnext
            _ = 1 := heq
            _ = p[0] := hzero.symm
        have hidx := hpnd.getElem_inj_iff.mp hsame
        omega
      simp [raiseSuccessor, hne]
    · have hjlast : j + 1 = v.length := by omega
      have hwpnext : j + 1 + 1 < w.length := by simp [w, K]; omega
      have hnew : w.formPerm ((raiseHigh m) v[j]) = 2 := by
        rw [← hentry j hj, List.formPerm_apply_lt_getElem w hnd (j + 1) hwpnext]
        have he : w[j + 1 + 1] = 2 := by
          simp only [w, List.getElem_cons_succ]
          rw [List.getElem_append_right (by simp; omega)]
          simp [K, hjlast]
        exact he
      have hold : p.formPerm v[j] = 1 := by
        rw [← hpentry j hj, List.formPerm_apply_getElem p hpnd (j + 1) (by simp [p]; omega)]
        have he : (j + 1 + 1) % p.length = 0 := by
          simp [p, hjlast]
        simp only [he]
        rfl
      rw [hnew, hold]
      simp [raiseSuccessor]
  have hq : (List.range' (m + 1) v.length).map w.formPerm =
      ((List.range' 2 v.length).map p.formPerm).map (raiseSuccessor m) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hiV : i < v.length := by simpa using hi
      have hx : 2 + i ∈ v := hvperm.mem_iff.mpr
        (List.mem_range'.mpr ⟨i, hiV, by simp⟩)
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hx
      simp only [List.getElem_map, List.getElem_range'_1]
      have hf : (raiseHigh m) (2 + i) = m + 1 + i := by
        have hnot : ¬ 2 + i < 2 := by omega
        simp only [raiseHigh, hnot, ↓reduceIte]
        omega
      calc
        w.formPerm (m + 1 + i) = w.formPerm ((raiseHigh m) v[j]) := by
          rw [hjeq, hf]
        _ = raiseSuccessor m (p.formPerm v[j]) := hnext j hj
        _ = raiseSuccessor m (p.formPerm (2 + i)) := by rw [← hjeq]
  have htail : (oneLine p).tail = (List.range' 2 v.length).map p.formPerm := by
    have he : List.range' 1 p.length = 1 :: List.range' 2 v.length := by
      rw [show p.length = 1 + v.length by simp [p, Nat.add_comm]]
      rw [← List.range'_append_1]
      rfl
    simp only [oneLine, he, List.map_cons, List.tail_cons]
  have hR : List.range' 3 (m - 2) =
      List.range' 3 (List.range' 3 (m - 2)).length := by simp
  have hblock := oneLine_split_block (raiseHigh m h)
    (T.map (raiseHigh m)) (List.range' 3 (m - 2)) hR (by simpa [w, v, K] using hnd)
  have hblock' : oneLine w = raiseHigh m h ::
      (List.range' 3 (m - 2) ++ [1] ++
        (List.range' ((List.range' 3 (m - 2)).length + 3) v.length).map w.formPerm) := by
    simpa only [w, v, K, List.map_cons, List.length_map, List.length_range',
      List.length_cons] using hblock
  have hlen : (List.range' 3 (m - 2)).length + 3 = m + 1 := by simp; omega
  change oneLine w = raiseHigh m h ::
    (List.range' 3 (m - 2) ++ [1] ++ (oneLine p).tail.map (raiseSuccessor m))
  rw [hblock']
  rw [hlen]
  rw [hq, ← htail]

theorem inserted_avoid_iff (h : ℕ) (T : List ℕ) (m : ℕ)
    (hm : 2 ≤ m)
    (hv : (1 :: h :: T).Perm (List.range' 1 (1 :: h :: T).length)) :
    (¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4
      (oneLine (1 :: ((h :: T).map (raiseHigh m) ++
        2 :: List.range' 3 (m - 2))))) ↔
      let q := (oneLine (1 :: h :: T)).tail
      ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q ∧
        ¬ ∃ c d, [c, d].Sublist q ∧ d < c ∧ c < h := by
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
  let g := raiseSuccessor m
  have hgmono : StrictMono g := by
    apply strictMono_nat_of_lt_succ
    intro x
    simp only [g, raiseSuccessor, raiseHigh]
    split_ifs <;> omega
  let mid := List.range' 3 (m - 2)
  have hpnd : p.Nodup := hv.nodup_iff.mpr List.nodup_range'
  have hpperm : p.Perm (List.range' 1 p.length) := by simpa [p] using hv
  have hhmem : h ∈ p := by simp [p]
  have hhr : h ∈ List.range' 1 p.length := by
    exact hpperm.mem_iff.mp hhmem
  have hge : 1 ≤ h := List.left_le_of_mem_range' hhr
  have hne : h ≠ 1 := by
    intro heq
    have hnodup := List.nodup_cons.mp hpnd
    exact hnodup.1 (by simp [heq])
  have hgt : 1 < h := by omega
  have hfg : g h = raiseHigh m h := by simp [g, raiseSuccessor, hne]
  have hfgt : 1 < raiseHigh m h := by
    have hnot : ¬ h < 2 := by omega
    simp only [raiseHigh, hnot, ↓reduceIte]
    omega
  have hqpositive (z : ℕ) (hz : z ∈ q) : 1 ≤ z := by
    have hline := oneLine_perm p hpperm
    have hzline : z ∈ oneLine p := List.mem_of_mem_tail hz
    exact List.left_le_of_mem_range' (hline.mem_iff.mp hzline)
  have hmidpair : mid.Pairwise (· < ·) := by
    exact List.pairwise_lt_range' (s := 3) (n := m - 2)
  have hmidgt : ∀ z ∈ mid, 2 < z := by
    intro z hz
    have := List.left_le_of_mem_range' hz
    omega
  have hqgt : ∀ z ∈ q.map g, 1 < z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    by_cases hy1 : y = 1
    · simp [g, raiseSuccessor, hy1]
    · have hy2 : 2 ≤ y := by have := hqpositive y hy; omega
      have hn : ¬ y < 2 := by omega
      simp only [g, raiseSuccessor, hy1, ↓reduceIte, raiseHigh, hn]
      omega
  have hqmid : ∀ z ∈ q.map g, z = 2 ∨ ∀ y ∈ mid, y < z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    by_cases hx1 : x = 1
    · left
      simp [g, raiseSuccessor, hx1]
    · right
      have hx2 : 2 ≤ x := by have := hqpositive x hx; omega
      have hn : ¬ x < 2 := by omega
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hy
      simp only [g, raiseSuccessor, hx1, ↓reduceIte, raiseHigh, hn]
      omega
  have hblock := oneLine_inserted_block h T m hm hv
  change ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4
    (oneLine (1 :: ((h :: T).map (raiseHigh m) ++ 2 :: mid))) ↔
      ¬ ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q ∧
        ¬ ∃ c d, [c, d].Sublist q ∧ d < c ∧ c < h
  rw [hblock]
  simp only [List.append_assoc, List.singleton_append]
  have hmidtest := ArcherCyclicPadovanBlockPattern.contains_4132_high_middle_iff
    (raiseHigh m h) mid (q.map g) hfgt hmidpair hmidgt hqgt hqmid
  have honetest := ArcherCyclicPadovanOneLine.contains_4132_high_one_iff
    (raiseHigh m h) (q.map g) hfgt hqgt
  rw [hmidtest, honetest, not_or]
  have hmap : ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 (q.map g) ↔
      ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 q := by
    simpa using ArcherCyclicPadovanPatterns.contains_map_iff
      [4, 1, 3, 2] q g hgmono
  rw [hmap]
  rw [← hfg, below_descent_map_iff q h g hgmono]

end D5.S3.Combinatorics.ArcherCyclicPadovanSuccessor
