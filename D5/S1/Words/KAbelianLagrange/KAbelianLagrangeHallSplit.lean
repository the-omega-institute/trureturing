/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeHallSplit
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeHallSplit
   mirror-E: none(waiver:hall-interval-splitting)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Archimedean.Real.Basic]
   utility: none
   digest: Greedy gap splitting realizes every point in the sum of two interval-tree hulls. -/

import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- A binary interval construction, with the newest branch choice at the list head.
The two children retain the parent's outer endpoints. Each child is at least as long
as the removed gap, gaps decrease down the tree, and interval lengths shrink uniformly. -/
structure HallTree where
  lo : List Bool → ℝ
  hi : List Bool → ℝ
  ordered : ∀ p, lo p ≤ hi p
  left : ∀ p, lo (false :: p) = lo p
  right : ∀ p, hi (true :: p) = hi p
  inside : ∀ p b, lo p ≤ lo (b :: p) ∧ hi (b :: p) ≤ hi p
  gap_pos : ∀ p, 0 < lo (true :: p) - hi (false :: p)
  child_size : ∀ p b,
    lo (true :: p) - hi (false :: p) ≤ hi (b :: p) - lo (b :: p)
  gap_mono : ∀ p b,
    lo (true :: b :: p) - hi (false :: b :: p) ≤ lo (true :: p) - hi (false :: p)
  shrink : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p, N ≤ p.length → hi p - lo p < ε

/-- Hall's interval-splitting argument. The limit sets are expressed by survival at every
finite level; no assumption that either tree already has points is required. -/
theorem hall_interval_splitting (U V : HallTree)
    (hUV : U.lo [true] - U.hi [false] ≤ V.hi [] - V.lo [])
    (hVU : V.lo [true] - V.hi [false] ≤ U.hi [] - U.lo [])
    (z : ℝ) (hz : z ∈ Set.Icc (U.lo [] + V.lo []) (U.hi [] + V.hi [])) :
    ∃ x y : ℝ, z = x + y ∧
      (∀ n : ℕ, ∃ p : List Bool, p.length = n ∧ x ∈ Set.Icc (U.lo p) (U.hi p)) ∧
      (∀ n : ℕ, ∃ p : List Bool, p.length = n ∧ y ∈ Set.Icc (V.lo p) (V.hi p)) := by
  classical
  let good (p q : List Bool) : Prop :=
    z ∈ Set.Icc (U.lo p + V.lo q) (U.hi p + V.hi q) ∧
      U.lo (true :: p) - U.hi (false :: p) ≤ V.hi q - V.lo q ∧
      V.lo (true :: q) - V.hi (false :: q) ≤ U.hi p - U.lo p
  have hchoose (T S : HallTree) (p q : List Bool)
      (hsum : z ∈ Set.Icc (T.lo p + S.lo q) (T.hi p + S.hi q))
      (hgap : T.lo (true :: p) - T.hi (false :: p) ≤ S.hi q - S.lo q) :
      ∃ b : Bool, z ∈ Set.Icc (T.lo (b :: p) + S.lo q)
        (T.hi (b :: p) + S.hi q) := by
    by_cases h : z ≤ T.hi (false :: p) + S.hi q
    · refine ⟨false, ?_, h⟩
      simpa only [T.left] using hsum.1
    · refine ⟨true, ?_, ?_⟩
      · have := lt_of_not_ge h
        linarith
      · simpa only [T.right] using hsum.2
  have hnext : ∀ p q, good p q →
      ∃ p' q', good p' q' ∧
        ((∃ b, p' = b :: p ∧ q' = q) ∨ (∃ b, p' = p ∧ q' = b :: q)) := by
    intro p q hg
    by_cases h : V.lo (true :: q) - V.hi (false :: q) ≤
        U.lo (true :: p) - U.hi (false :: p)
    · obtain ⟨b, hb⟩ := hchoose U V p q hg.1 hg.2.1
      refine ⟨b :: p, q, ⟨hb, ?_, ?_⟩, Or.inl ⟨b, rfl, rfl⟩⟩
      · exact (U.gap_mono p b).trans hg.2.1
      · exact h.trans (U.child_size p b)
    · obtain ⟨b, hb⟩ := hchoose V U q p
        (by simpa only [add_comm] using hg.1) hg.2.2
      refine ⟨p, b :: q, ⟨?_, ?_, ?_⟩, Or.inr ⟨b, rfl, rfl⟩⟩
      · simpa only [add_comm] using hb
      · exact (le_of_lt (lt_of_not_ge h)).trans (V.child_size q b)
      · exact (V.gap_mono q b).trans hg.2.2
  let State := {pq : List Bool × List Bool // good pq.1 pq.2}
  let step (s : State) : State :=
    ⟨⟨(hnext s.val.1 s.val.2 s.property).choose,
      (hnext s.val.1 s.val.2 s.property).choose_spec.choose⟩,
      (hnext s.val.1 s.val.2 s.property).choose_spec.choose_spec.1⟩
  let s : ℕ → State := fun n => step^[n] ⟨([], []), hz, hUV, hVU⟩
  let p (n : ℕ) := (s n).val.1
  let q (n : ℕ) := (s n).val.2
  have hg (n : ℕ) : good (p n) (q n) := (s n).property
  have hstep (n : ℕ) :
      ((∃ b, p (n + 1) = b :: p n ∧ q (n + 1) = q n) ∨
        (∃ b, p (n + 1) = p n ∧ q (n + 1) = b :: q n)) := by
    have hs : s (n + 1) = step (s n) := Function.iterate_succ_apply' _ _ _
    simpa only [p, q, hs, step] using
      (hnext (s n).val.1 (s n).val.2 (s n).property).choose_spec.choose_spec.2
  have htotal (n : ℕ) : (p n).length + (q n).length = n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rcases hstep n with ⟨b, hp, hq⟩ | ⟨b, hp, hq⟩ <;>
          simp only [hp, hq, List.length_cons] <;> omega
  have hmono : Monotone (fun n => (p n).length) ∧
      Monotone (fun n => (q n).length) := by
    constructor <;> apply monotone_nat_of_le_succ <;> intro n <;>
      rcases hstep n with ⟨b, hp, hq⟩ | ⟨b, hp, hq⟩ <;>
      simp only [hp, hq, List.length_cons] <;> omega
  have hnested :
      Monotone (fun n => U.lo (p n)) ∧ Antitone (fun n => U.hi (p n)) ∧
      Monotone (fun n => V.lo (q n)) ∧ Antitone (fun n => V.hi (q n)) := by
    refine ⟨monotone_nat_of_le_succ ?_, antitone_nat_of_succ_le ?_,
      monotone_nat_of_le_succ ?_, antitone_nat_of_succ_le ?_⟩ <;> intro n <;>
      rcases hstep n with ⟨b, hp, hq⟩ | ⟨b, hp, hq⟩ <;>
      simp only [hp, hq] <;>
      first
      | exact le_rfl
      | exact (U.inside _ _).1
      | exact (U.inside _ _).2
      | exact (V.inside _ _).1
      | exact (V.inside _ _).2
  have hgrowth (T S : HallTree) (a b : ℕ → List Bool)
      (hmove : ∀ n, (∃ c, a (n + 1) = c :: a n ∧ b (n + 1) = b n) ∨
        (∃ c, a (n + 1) = a n ∧ b (n + 1) = c :: b n))
      (hlen : ∀ n, (a n).length + (b n).length = n)
      (ha : Monotone (fun n => (a n).length))
      (hcross : ∀ n, T.lo (true :: a n) - T.hi (false :: a n) ≤
        S.hi (b n) - S.lo (b n)) :
      ∀ n, ∃ m, n ≤ m ∧ (a n).length < (a m).length := by
    intro n
    by_contra h
    have hbound : ∀ m, n ≤ m → (a m).length ≤ (a n).length := by
      intro m hm
      by_contra hc
      exact h ⟨m, hm, lt_of_not_ge hc⟩
    have hfixed : ∀ d, a (n + d) = a n := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          rcases hmove (n + d) with ⟨c, hc, hd⟩ | ⟨c, hc, hd⟩
          · have := hbound (n + d + 1) (by omega)
            simp only [hc, List.length_cons, ih] at this
            omega
          · simpa only [Nat.add_succ, hc] using ih
    obtain ⟨N, hN⟩ := S.shrink _ (T.gap_pos (a n))
    let m := n + N + (a n).length
    have ham : a m = a n := by
      change a (n + N + (a n).length) = a n
      rw [Nat.add_assoc]
      exact hfixed (N + (a n).length)
    have hbm : N ≤ (b m).length := by
      have := hlen m
      rw [ham] at this
      have hmm : m = n + N + (a n).length := rfl
      omega
    have := hN (b m) hbm
    have := hcross m
    rw [ham] at this
    linarith
  have hpg := hgrowth U V p q hstep htotal hmono.1 (fun n => (hg n).2.1)
  have hqg := hgrowth V U q p (fun n => by
    rcases hstep n with ⟨b, hp, hq⟩ | ⟨b, hp, hq⟩
    · exact Or.inr ⟨b, hq, hp⟩
    · exact Or.inl ⟨b, hq, hp⟩)
    (fun n => (Nat.add_comm _ _).trans (htotal n)) hmono.2 (fun n => (hg n).2.2)
  have hunbounded (a : ℕ → List Bool)
      (ha : ∀ n, ∃ m, n ≤ m ∧ (a n).length < (a m).length) :
      ∀ N, ∃ n, N ≤ (a n).length := by
    intro N
    induction N with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ N ih =>
        obtain ⟨n, hn⟩ := ih
        obtain ⟨m, _, hm⟩ := ha n
        exact ⟨m, by omega⟩
  have hpLarge := hunbounded p hpg
  have hqLarge := hunbounded q hqg
  have hupper (n m : ℕ) : U.lo (p m) ≤ U.hi (p n) := by
    rcases le_total m n with h | h
    · exact (hnested.1 h).trans (U.ordered _)
    · exact (U.ordered _).trans (hnested.2.1 h)
  have hbdd : BddAbove (Set.range (fun n => U.lo (p n))) := by
    exact ⟨U.hi (p 0), fun _ ⟨n, hn⟩ => hn ▸ hupper 0 n⟩
  let x := sSup (Set.range (fun n => U.lo (p n)))
  have hxm (n : ℕ) : x ∈ Set.Icc (U.lo (p n)) (U.hi (p n)) := by
    exact ⟨le_csSup hbdd ⟨n, rfl⟩,
      csSup_le (Set.range_nonempty _) (fun _ ⟨m, hm⟩ => hm ▸ hupper n m)⟩
  have hym (n : ℕ) : z - x ∈ Set.Icc (V.lo (q n)) (V.hi (q n)) := by
    constructor
    · have hxle : x ≤ z - V.lo (q n) := by
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨m, rfl⟩
        rcases le_total m n with h | h
        · have := (hg n).1.1
          have := hnested.1 h
          linarith
        · have := (hg m).1.1
          have := hnested.2.2.1 h
          linarith
      linarith
    · by_contra h
      have he : 0 < z - x - V.hi (q n) := by linarith [lt_of_not_ge h]
      obtain ⟨N, hN⟩ := U.shrink _ he
      obtain ⟨m, hm⟩ := hpLarge N
      let l := max n m
      have hNl : N ≤ (p l).length := hm.trans (hmono.1 (le_max_right _ _))
      have := hN (p l) hNl
      have := (hg l).1.2
      have := hnested.2.2.2 (le_max_left n m)
      have := (hxm l).1
      linarith
  have hancestor (T : HallTree) : ∀ (p : List Bool) (n : ℕ), n ≤ p.length →
      ∃ r : List Bool, r.length = n ∧ T.lo r ≤ T.lo p ∧ T.hi p ≤ T.hi r := by
    intro p
    induction p with
    | nil =>
        intro n hn
        have : n = 0 := by simpa using hn
        subst n
        exact ⟨[], rfl, le_rfl, le_rfl⟩
    | cons b p ih =>
        intro n hn
        simp only [List.length_cons] at hn
        by_cases h : n ≤ p.length
        · obtain ⟨r, hr, hl, hh⟩ := ih n h
          exact ⟨r, hr, hl.trans (T.inside p b).1, (T.inside p b).2.trans hh⟩
        · exact ⟨b :: p, by simpa only [List.length_cons] using (by omega :
            p.length + 1 = n), le_rfl, le_rfl⟩
  refine ⟨x, z - x, by ring, ?_, ?_⟩
  · intro n
    obtain ⟨m, hm⟩ := hpLarge n
    obtain ⟨r, hr, hl, hh⟩ := hancestor U (p m) n hm
    exact ⟨r, hr, hl.trans (hxm m).1, (hxm m).2.trans hh⟩
  · intro n
    obtain ⟨m, hm⟩ := hqLarge n
    obtain ⟨r, hr, hl, hh⟩ := hancestor V (q m) n hm
    exact ⟨r, hr, hl.trans (hym m).1, (hym m).2.trans hh⟩

end D5.S1.Words.KAbelianLagrange
