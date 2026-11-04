/- GID: D5/S1/Words/Permutations/PrefixNormalGeneratorConnectivity
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/PrefixNormalGeneratorConnectivity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Prefix-normal flip-chain generators are connected by valid adjacent-position swaps. -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! Prefix-normal generator connectivity via the published ascent exchange and valid sorting paths. -/

namespace D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity

/-- Number of occupied positions in the half-open window [s,s+l). -/
def count (S : Finset ℕ) (s l : ℕ) : ℕ :=
  (S ∩ Finset.Ico s (s + l)).card

/-- Every factor within length n has at most as many ones as its equal-length prefix. -/
def PN (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ s l : ℕ, s + l ≤ n → count S s l ≤ count S 0 l

theorem count_erase (S : Finset ℕ) (s l a : ℕ) :
    count (S.erase a) s l =
      if a ∈ S ∧ s ≤ a ∧ a < s + l then count S s l - 1 else count S s l := by
  simp only [count, Finset.erase_inter, Finset.card_erase_eq_ite,
    Finset.mem_inter, Finset.mem_Ico]

theorem erase_later_preserves (n : ℕ) (S : Finset ℕ) (a b : ℕ)
    (hab : a < b) (ha : a ∈ S) (hb : b ∈ S)
    (hS : PN n S) (hA : PN n (S.erase a)) : PN n (S.erase b) := by
  intro s l hsl
  by_cases hbl : b < l
  · have hal : a < l := lt_trans hab hbl
    by_cases hbi : s ≤ b ∧ b < s + l
    · simpa only [count_erase, hb, hbi.1, hbi.2, hbl, Nat.zero_le,
        Nat.zero_add, and_self, if_true] using Nat.sub_le_sub_right (hS s l hsl) 1
    · have hnb : ¬ (s ≤ b ∧ b < s + l) := hbi
      have hna : ¬ (s ≤ a ∧ a < s + l) := by omega
      have h := hA s l hsl
      simpa only [count_erase, ha, hb, hnb, hna, hbl, hal, Nat.zero_le,
        Nat.zero_add, true_and, and_self, if_true, if_false] using h
  · have h := hS s l hsl
    rw [count_erase, count_erase]
    simp only [hb, Nat.zero_le, Nat.zero_add, hbl, and_false, if_false]
    split_ifs <;> omega

def Generator (n : ℕ) (l : List ℕ) : Prop :=
  l.Perm (List.range n) ∧ ∀ t : ℕ, t ≤ n → PN n (l.drop t).toFinset

/-- Published Lemma 17, with the changed state indexed consistently by the chain recurrence. -/
theorem generator_ascent_swap (n : ℕ) (p s : List ℕ) (a b : ℕ)
    (hab : a < b) (h : Generator n (p ++ a :: b :: s)) :
    Generator n (p ++ b :: a :: s) := by
  have hperm : (p ++ b :: a :: s).Perm (p ++ a :: b :: s) :=
    (List.Perm.swap a b s).append_left p
  refine ⟨hperm.trans h.1, ?_⟩
  have hnd : (p ++ a :: b :: s).Nodup := h.1.nodup_iff.mpr List.nodup_range
  have htnd := (List.nodup_append.mp hnd).2.1
  have ha : a ∉ b :: s := (List.nodup_cons.mp htnd).1
  have hb : b ∉ s := (List.nodup_cons.mp (List.nodup_cons.mp htnd).2).1
  have hlen : p.length + 2 + s.length = n := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1.length_eq
  intro t ht
  by_cases htp : t ≤ p.length
  · have eqsets : ((p ++ b :: a :: s).drop t).toFinset =
        ((p ++ a :: b :: s).drop t).toFinset := by
      simp [List.drop_append, Nat.sub_eq_zero_of_le htp, Finset.insert_comm]
    rw [eqsets]
    exact h.2 t ht
  · by_cases hmid : t = p.length + 1
    · subst t
      have hpdrop1 : p.drop (p.length + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      have hpre := h.2 p.length (by omega)
      have hfirst := h.2 (p.length + 1) (by omega)
      have heqa : (a :: b :: s).toFinset.erase a = (b :: s).toFinset := by
        simp_all
      have heqb : (a :: b :: s).toFinset.erase b = (a :: s).toFinset := by
        simp [hab.ne, hb, Finset.erase_insert_of_ne]
      have hpS : PN n (a :: b :: s).toFinset := by
        simpa using hpre
      have hpA : PN n ((a :: b :: s).toFinset.erase a) := by
        rw [heqa]
        simpa [List.drop_append, hpdrop1] using hfirst
      have hlocal := erase_later_preserves n (a :: b :: s).toFinset a b hab
        (by simp) (by simp) hpS hpA
      rw [heqb] at hlocal
      simpa [List.drop_append, hpdrop1] using hlocal
    · have ht2 : 2 ≤ t - p.length := by omega
      have hpdrop : p.drop t = [] := List.drop_eq_nil_iff.mpr (by omega)
      have eqdrops : (p ++ b :: a :: s).drop t = (p ++ a :: b :: s).drop t := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le ht2
        simp [List.drop_append, hpdrop, hk, List.drop_succ_cons, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
      rw [eqdrops]
      exact h.2 t ht

def Edge (P : List ℕ → Prop) (l m : List ℕ) : Prop :=
  P l ∧ P m ∧ ∃ (p s : List ℕ) (a b : ℕ),
    l = p ++ a :: b :: s ∧ m = p ++ b :: a :: s

theorem normalize_by_adjacent_ascents (P : List ℕ → Prop)
    (hclose : ∀ (p s : List ℕ) (a b : ℕ), a < b →
      P (p ++ a :: b :: s) → P (p ++ b :: a :: s)) :
    ∀ (l p : List ℕ), P (p ++ l) →
      Relation.ReflTransGen (Edge P) (p ++ l)
        (p ++ l.insertionSort (fun a b : ℕ => b ≤ a)) := by
  have insert_path : ∀ (l p : List ℕ) (a : ℕ), P (p ++ a :: l) →
      Relation.ReflTransGen (Edge P) (p ++ a :: l)
        (p ++ l.orderedInsert (fun a b : ℕ => b ≤ a) a) := by
    intro l
    induction l with
    | nil => intro p a hp; exact .refl
    | cons b s ih =>
      intro p a hp
      by_cases hab : b ≤ a
      · simpa [List.orderedInsert_cons, hab] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen (Edge P)
            (p ++ a :: b :: s) (p ++ a :: b :: s))
      · have hnext := hclose p s a b (by omega) hp
        have hedge : Edge P (p ++ a :: b :: s) (p ++ b :: a :: s) :=
          ⟨hp, hnext, p, s, a, b, rfl, rfl⟩
        have hr := ih (p ++ [b]) a (by simpa [List.append_assoc] using hnext)
        exact Relation.ReflTransGen.head hedge (by
          simpa [List.orderedInsert_cons, hab, List.append_assoc] using hr)
  intro l
  induction l with
  | nil => intro p hp; exact .refl
  | cons a s ih =>
    intro p hp
    have htail := ih (p ++ [a]) (by simpa [List.append_assoc] using hp)
    have hP : P (p ++ a :: s.insertionSort (fun a b : ℕ => b ≤ a)) := by
      have preserve : ∀ {x y}, Relation.ReflTransGen (Edge P) x y → P x → P y := by
        intro x y hxy hx
        induction hxy with
        | refl => exact hx
        | tail hxy e ih => exact e.2.1
      simpa [List.append_assoc] using preserve htail (by simpa [List.append_assoc] using hp)
    have hins := insert_path (s.insertionSort (fun a b : ℕ => b ≤ a)) p a hP
    have htpath : Relation.ReflTransGen (Edge P) (p ++ a :: s)
        (p ++ a :: s.insertionSort (fun a b : ℕ => b ≤ a)) := by
      simpa [List.append_assoc] using htail
    exact htpath.trans (by simpa [List.insertionSort_cons] using hins)

theorem full_event_list (n : ℕ) (l m : List ℕ)
    (hl : Generator n l) (hm : Generator n m) :
    Relation.ReflTransGen (Edge (Generator n)) l m := by
  let : Std.Symm (Edge (Generator n)) := ⟨by
    intro x y h
    rcases h with ⟨hx, hy, p, s, a, b, hxa, hyb⟩
    exact ⟨hy, hx, p, s, b, a, hyb, hxa⟩⟩
  have hlpath : Relation.ReflTransGen (Edge (Generator n)) l
      (l.insertionSort (fun a b : ℕ => b ≤ a)) := by
    simpa using normalize_by_adjacent_ascents (Generator n) (generator_ascent_swap n) l [] hl
  have hmpath : Relation.ReflTransGen (Edge (Generator n)) m
      (m.insertionSort (fun a b : ℕ => b ≤ a)) := by
    simpa using normalize_by_adjacent_ascents (Generator n) (generator_ascent_swap n) m [] hm
  have hperm : (l.insertionSort (fun a b : ℕ => b ≤ a)).Perm
      (m.insertionSort (fun a b : ℕ => b ≤ a)) :=
    (List.perm_insertionSort _ l).trans
      ((hl.1.trans hm.1.symm).trans (List.perm_insertionSort _ m).symm)
  have heq := List.Perm.eq_of_pairwise'
    (List.pairwise_insertionSort (fun a b : ℕ => b ≤ a) l)
    (List.pairwise_insertionSort (fun a b : ℕ => b ≤ a) m) hperm
  rw [heq] at hlpath
  exact hlpath.trans (symm hmpath)

theorem suffix_eq_undeleted (n : ℕ) (l : List ℕ)
    (hp : l.Perm (List.range n)) (t : ℕ) :
    (l.drop t).toFinset = Finset.range n \ (l.take t).toFinset := by
  have hnd : l.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hsplit : (l.take t ++ l.drop t).Nodup := by simpa using hnd
  have hdis := (List.nodup_append.mp hsplit).2.2
  have hall : l.toFinset = Finset.range n := by
    ext a
    simpa only [List.mem_toFinset, Finset.mem_range, List.mem_range] using
      (hp.mem_iff : a ∈ l ↔ a ∈ List.range n)
  ext a
  simp only [Finset.mem_sdiff, List.mem_toFinset]
  constructor
  · intro had
    refine ⟨?_, ?_⟩
    · rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_of_mem_drop had)
    · intro hat
      exact hdis a hat a had rfl
  · rintro ⟨har, hat⟩
    have hal : a ∈ l := by
      apply List.mem_toFinset.mp
      rw [hall]
      exact har
    have haunion : a ∈ l.take t ++ l.drop t := by simpa using hal
    exact (List.mem_append.mp haunion).resolve_left hat

/-- All n+1 states, including the all-one and all-zero words, in flip-to-zero order. -/
def ExactGenerator (n : ℕ) (l : List ℕ) : Prop :=
  l.Perm (List.range n) ∧
    ∀ t : ℕ, t ≤ n → PN n (Finset.range n \ (l.take t).toFinset)

theorem generator_iff_exact (n : ℕ) (l : List ℕ) :
    Generator n l ↔ ExactGenerator n l := by
  constructor
  · rintro ⟨hp, hv⟩
    refine ⟨hp, ?_⟩
    intro t ht
    rw [← suffix_eq_undeleted n l hp t]
    exact hv t ht
  · rintro ⟨hp, hv⟩
    refine ⟨hp, ?_⟩
    intro t ht
    rw [suffix_eq_undeleted n l hp t]
    exact hv t ht

/-- The exact v1 connectivity question, also valid for the empty permutation. -/
theorem result (n : ℕ) (l m : List ℕ)
    (hl : ExactGenerator n l) (hm : ExactGenerator n m) :
    Relation.ReflTransGen (Edge (ExactGenerator n)) l m := by
  have path := full_event_list n l m
    ((generator_iff_exact n l).mpr hl) ((generator_iff_exact n m).mpr hm)
  apply Relation.ReflTransGen.mono (r := Edge (Generator n)) ?_ l m path
  intro x y he
  exact ⟨(generator_iff_exact n x).mp he.1,
    (generator_iff_exact n y).mp he.2.1, he.2.2⟩

end D5.S1.Words.Permutations.PrefixNormalGeneratorConnectivity
