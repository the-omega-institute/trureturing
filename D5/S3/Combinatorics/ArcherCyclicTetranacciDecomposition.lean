/- GID: D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicTetranacciDecomposition
   mirror-E: none(waiver:exhaustive-insertion-decomposition-of-cycle-words)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Each admissible rooted word has a unique predecessor in four branches. -/

import D5.S3.Combinatorics.ArcherCyclicTetranacciOneLine
import D5.S3.Combinatorics.ArcherCyclicTetranacciStructure
import D5.S3.Combinatorics.ArcherCyclicPadovanDecomposition
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicTetranacciDecomposition

open ArcherCyclicDefs ArcherCyclicTetranacciInsertion
open ArcherCyclicTetranacciCycleWords ArcherCyclicTetranacciStructure
open ArcherCyclicTetranacciOneLine

def words (n : ℕ) : Set (List ℕ) :=
  {w | w.Perm (List.range' 1 n) ∧ w.head? = some 1 ∧
    (∀ r < w.length, ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (w.rotate r)) ∧
    ¬ ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 (oneLine w)}

/-- The entry after one identifies the branch, and deleting the low arc and
subtracting the branch size recovers its unique predecessor. -/
theorem decomposition (n : ℕ) (hn : 1 < n) (w : List ℕ) :
    w ∈ words n ↔ ∃ k v, 1 ≤ k ∧ k ≤ 4 ∧ k < n ∧
      v ∈ words (n - k) ∧ w = insertWord k v := by
  constructor
  · rintro ⟨hwperm, hwhead, hc, ho⟩
    have hlen : w.length = n := by simpa using hwperm.length_eq
    have hnd := hwperm.nodup_iff.mpr List.nodup_range'
    have hrot := hc
    have reduce (k : ℕ) (p : List ℕ) (hk : 1 ≤ k) (hk4 : k ≤ 4)
        (hp : p.Perm (List.range' (k + 1) p.length))
        (hphead : p.head? = some (k + 1))
        (hw : w = 1 :: (p ++ List.range' 2 (k - 1))) :
        ∃ v, k < n ∧ v ∈ words (n - k) ∧ w = insertWord k v := by
      let v := p.map (fun z => z - k)
      have hpmin (z : ℕ) (hz : z ∈ p) : k + 1 ≤ z :=
        List.left_le_of_mem_range' (hp.mem_iff.mp hz)
      have hvperm : v.Perm (List.range' 1 p.length) := by
        have hh := hp.map (fun z => z - k)
        simpa [v, List.map_sub_range'] using hh
      have hvhead : v.head? = some 1 := by
        rcases p with (_ | ⟨a, p⟩)
        · simp at hphead
        · have ha : a = k + 1 := by simpa using hphead
          simp [v, ha]
      have hpne : 0 < p.length := by
        rcases p with (_ | ⟨a, p⟩)
        · simp at hphead
        · simp
      have hsize : p.length + k = n := by
        rw [hw] at hlen
        simp only [List.length_cons, List.length_append, List.length_range'] at hlen
        omega
      have hback : v.map (fun z => k + z) = p := by
        calc
          _ = p.map id := by
            dsimp [v]
            rw [List.map_map]
            apply List.map_congr_left
            intro z hz
            have := hpmin z hz
            dsimp
            omega
          _ = p := List.map_id p
      have hweq : w = insertWord k v := by
        rw [hw]
        simp only [insertWord, hback]
      obtain ⟨s, hvs⟩ : ∃ s, v = 1 :: s := by
        rcases v with (_ | ⟨a, s⟩)
        · simp at hvhead
        · have ha : a = 1 := by simpa using hvhead
          exact ⟨s, by simp [ha]⟩
      have hvself : (1 :: s).Perm (List.range' 1 (s.length + 1)) := by
        have hvlen : (1 :: s).length = p.length := by
          simpa only [hvs, List.length_range'] using hvperm.length_eq
        simpa [hvs, ← hvlen, Nat.add_comm] using hvperm
      have hcold : ∀ r < v.length,
          ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 (v.rotate r) := by
        intro r hr hh
        have hh' : ∃ r < (1 :: s).length,
            ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4 ((1 :: s).rotate r) :=
          ⟨r, by simpa [hvs] using hr, by simpa [hvs] using hh⟩
        have hnew := (circular_1324_insert_iff k s hk hvself).mpr hh'
        rw [hweq, hvs] at hc
        exact hc hnew.choose hnew.choose_spec.1 hnew.choose_spec.2
      have hoold : ¬ ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4 (oneLine v) := by
        intro hh
        apply ho
        rw [hweq, hvs]
        exact (contains_4123_insert_iff k s hk hk4 hvself).mpr
          (by simpa [hvs] using hh)
      refine ⟨v, by omega, ?_, hweq⟩
      exact ⟨by simpa [show p.length = n - k by omega] using hvperm,
        hvhead, hcold, hoold⟩
    rcases w with (_ | ⟨a, s⟩)
    · simp at hwhead
    · have ha : a = 1 := by simpa using hwhead
      subst a
      have h2mem : 2 ∈ s := by
        have hh : 2 ∈ 1 :: s := hwperm.mem_iff.mpr (by
          apply List.mem_range'.mpr
          exact ⟨1, by omega, by omega⟩)
        simpa using hh
      obtain ⟨p, t, hs, _⟩ := List.eq_append_cons_of_mem h2mem
      subst s
      by_cases hpnil : p = []
      · subst p
        have hp : (2 :: t).Perm (List.range' 2 (2 :: t).length) := by
          apply List.Perm.cons_inv (a := 1)
          have hnlen : n = (2 :: t).length + 1 := by simpa using hlen.symm
          simpa [hnlen, List.range'_succ] using hwperm
        obtain ⟨v, hkn, hv, heq⟩ := reduce 1 (2 :: t) (by omega) (by omega)
          hp (by simp) (by simp)
        exact ⟨1, v, by omega, by omega, hkn, hv, heq⟩
      · have hwself : (1 :: (p ++ 2 :: t)).Perm
            (List.range' 1 (1 :: (p ++ 2 :: t)).length) := by
          simpa only [hlen] using hwperm
        obtain ⟨hsep, ht, _⟩ :=
          ArcherCyclicPadovanDecomposition.low_arc_forced p t hpnil hwself hrot
        let m := t.length
        have ht' : t = List.range' 3 m := ht
        have htailperm : (p ++ 2 :: t).Perm
            (List.range' 2 (p.length + t.length + 1)) := by
          have hw' : (1 :: (p ++ 2 :: t)).Perm
              (List.range' 1 ((p.length + t.length + 1) + 1)) := by
            simpa [List.length_append, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hwself
          simpa only [List.range'_succ, Nat.reduceAdd, List.perm_cons] using hw'
        have hpperm : p.Perm (List.range' (m + 3) p.length) := by
          have hlperm : ((2 :: t) ++ p).Perm
              (List.range' 2 (m + 1 + p.length)) :=
            List.perm_append_comm.trans (by
              simpa [m, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htailperm)
          have hrange : (2 :: t) ++ List.range' (m + 3) p.length =
              List.range' 2 (m + 1 + p.length) := by
            rw [ht']
            have hstart : m + 3 = 2 + (m + 1) := by omega
            rw [hstart, show 2 :: List.range' 3 m = List.range' 2 (m + 1) by
              simp [List.range'_succ], List.range'_append_1]
          apply (List.perm_append_left_iff (2 :: t)).mp
          rwa [hrange]
        rcases p with (_ | ⟨a, u⟩)
        · exact False.elim (hpnil rfl)
        · have hdn : (1 :: ((a :: u) ++ 2 :: List.range' 3 m)).Nodup := by
            rw [← ht']
            exact hnd
          have hcn : ¬ ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4
              (1 :: ((a :: u) ++ 2 :: List.range' 3 m)) := by
            rw [← ht']
            simpa using hrot 0 (by simp)
          have hon : ¬ ArrowWilfDefs.Contains [4, 1, 2, 3] [] 4
              (oneLine (1 :: ((a :: u) ++ 2 :: List.range' 3 m))) := by
            rw [← ht']
            exact ho
          have ha := first_high_minimum a m u (by simpa using hpperm) hdn hcn hon
          subst a
          have hm := low_arc_length_le_two m u hdn hon
          let k := m + 2
          have hlow : List.range' 2 (k - 1) = 2 :: t := by
            rw [show k - 1 = m + 1 by rfl, List.range'_succ]
            exact congrArg (List.cons 2) ht'.symm
          obtain ⟨v, hkn, hv, heq⟩ := reduce k ((m + 3) :: u)
            (by dsimp [k]; omega) (by dsimp [k]; omega)
            (by simpa [k] using hpperm) (by simp [k, Nat.add_assoc])
            (by rw [hlow])
          exact ⟨k, v, by dsimp [k]; omega, by dsimp [k]; omega, hkn, hv, heq⟩
  · rintro ⟨k, v, hk, hk4, hkn, hv, rfl⟩
    obtain ⟨hp, hhead, hc, ho⟩ := hv
    rcases v with (_ | ⟨a, s⟩)
    · simp at hhead
    · have ha : a = 1 := by simpa using hhead
      subst a
      have hvlen : s.length + 1 = n - k := by simpa using hp.length_eq
      have hvself : (1 :: s).Perm (List.range' 1 (s.length + 1)) := by
        rwa [hvlen]
      have hmap : ((1 :: s).map (fun z => k + z)).Perm
          (List.range' (k + 1) (n - k)) := by
        simpa [List.map_add_range'] using hp.map (fun z => k + z)
      have hperm : (insertWord k (1 :: s)).Perm (List.range' 1 n) := by
        have hh : (((1 :: s).map (fun z => k + z)) ++ List.range' 2 (k - 1)).Perm
            (List.range' 2 (k - 1) ++ List.range' (k + 1) (n - k)) :=
          (hmap.append (List.Perm.refl _)).trans List.perm_append_comm
        have hcanon : 1 :: (List.range' 2 (k - 1) ++ List.range' (k + 1) (n - k)) =
            List.range' 1 n := by
          rw [show k + 1 = 2 + (k - 1) by omega, List.range'_append_1]
          have hsize : (k - 1) + (n - k) + 1 = n := by omega
          conv_rhs => rw [← hsize, List.range'_succ]
        rw [← hcanon]
        exact hh.cons 1
      refine ⟨hperm, by simp [insertWord], ?_, ?_⟩
      · intro r hr hh
        have hnew : ∃ r < (insertWord k (1 :: s)).length,
            ArrowWilfDefs.Contains [1, 3, 2, 4] [] 4
              ((insertWord k (1 :: s)).rotate r) := ⟨r, hr, hh⟩
        obtain ⟨r', hr', hh'⟩ := (circular_1324_insert_iff k s hk hvself).mp hnew
        exact hc r' hr' hh'
      · intro hh
        exact ho ((contains_4123_insert_iff k s hk hk4 hvself).mp hh)

end D5.S3.Combinatorics.ArcherCyclicTetranacciDecomposition
