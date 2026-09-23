/- GID: D5/S1/Digit/Carry/OrderedGame/Completion
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame/Completion
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Ordered priority correspondence and finite completion for every LGS switch choice. -/

import D5.S1.Digit.Carry.OrderedGame.Optimality
import D5.S1.Digit.Carry.OrderedGame.Attainment

namespace D5.S1.Digit.Carry.OrderedGame

open ListInversions

/-- Erasing every permitted switch retains the weight and the exact raw greedy
priority. Positional rightmost splits become highest duplicates, and leftmost
merges become least enabled consecutive indices. -/
theorem lgs_path_raw_erasure {s t : List ℕ} {length weight : ℕ}
    (path : LGSPath s t length weight) :
    RawGreedyPath (rawCounts s) (rawCounts t) weight := by
  classical
  have duplicate (l : List ℕ) (hs : l.Pairwise (· ≤ ·)) (k : ℕ)
      (hc : 2 ≤ l.count k) : ∃ P S, l = P ++ [k, k] ++ S := by
    induction l with
    | nil => simp at hc
    | cons x xs ih =>
      by_cases ht : 2 ≤ xs.count k
      · obtain ⟨P, S, he⟩ := ih (List.pairwise_cons.mp hs).2 ht
        exact ⟨x :: P, S, by simp [he]⟩
      have hx : x = k := by
        by_contra hn
        simp [hn] at hc
        omega
      subst x
      cases xs with
      | nil => simp at hc
      | cons y ys =>
        have kmem : k ∈ y :: ys := List.count_pos_iff.mp (by
          simp only [List.count_cons_self] at hc
          omega)
        have ky := (List.pairwise_cons.mp hs).1 y (by simp)
        have yk : y ≤ k := by
          rcases List.mem_cons.mp kmem with he | hm
          · omega
          · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 k hm
        have he : y = k := by omega
        subst y
        exact ⟨[], ys, rfl⟩
  have consecutive (l : List ℕ) (hs : l.Pairwise (· ≤ ·)) (k : ℕ)
      (hk : k ∈ l) (hk' : k + 1 ∈ l) : ∃ P S, l = P ++ [k, k + 1] ++ S := by
    induction l with
    | nil => simp at hk
    | cons x xs ih =>
      by_cases ht : k ∈ xs
      · have ht' : k + 1 ∈ xs := by
          rcases List.mem_cons.mp hk' with he | hm
          · have := (List.pairwise_cons.mp hs).1 k ht
            omega
          · exact hm
        obtain ⟨P, S, he⟩ := ih (List.pairwise_cons.mp hs).2 ht ht'
        exact ⟨x :: P, S, by simp [he]⟩
      have hx : x = k := by simpa [ht, eq_comm] using hk
      subst x
      cases xs with
      | nil => simp at hk'
      | cons y ys =>
        have kmem : k + 1 ∈ y :: ys := by simpa using hk'
        have ky := (List.pairwise_cons.mp hs).1 y (by simp)
        have yk : y ≤ k + 1 := by
          rcases List.mem_cons.mp kmem with he | hm
          · omega
          · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 _ hm
        have ne : y ≠ k := by intro he; exact ht (by simp [he])
        have he : y = k + 1 := by omega
        subst y
        exact ⟨[], ys, rfl⟩
  have position_order {l P Q S T : List ℕ} {x y : ℕ}
      (hs : l.Pairwise (· ≤ ·)) (hx : l = P ++ x :: S)
      (hy : l = Q ++ y :: T) (hxy : x < y) : P.length < Q.length := by
    have hp : P.length < l.length := by simp [hx]
    have hq : Q.length < l.length := by simp [hy]
    have ex : l[P.length] = x := by simp [hx]
    have ey : l[Q.length] = y := by simp [hy]
    by_contra hn
    by_cases he : P.length = Q.length
    · have : x = y := ex.symm.trans (by simpa only [he] using ey)
      omega
    have h := List.pairwise_iff_getElem.mp hs Q.length P.length hq hp (by omega)
    rw [ex, ey] at h
    omega
  have preferred {p a s t} (step : LGSMove p a s t) (ha : a ≠ .switch) :
      RawPreferred (rawCounts s) a := by
    have hs : s.Pairwise (· ≤ ·) := by
      apply List.isChain_iff_pairwise.mp
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro x y P S he
      by_contra hn
      have hm : Move P.length .switch s (P ++ [y, x] ++ S) := by
        simpa [he] using Move.switch P S x y (by omega)
      apply step.2 _ _ _ hm
      left
      cases a <;> simp_all [priority]
    have dup (k : ℕ) (hc : 2 ≤ rawCounts s k) :
        ∃ P S, s = P ++ [k, k] ++ S :=
      duplicate s hs k (by simpa [rawCounts, Multiset.toFinsupp_apply] using hc)
    have zero (hpa : 1 < priority a) : rawCounts s 0 ≤ 1 := by
      by_contra hn
      obtain ⟨P, S, he⟩ := dup 0 (by omega)
      have hm : Move P.length .ones s (P ++ [1] ++ S) := by
        simpa [he] using Move.ones P S
      exact step.2 _ _ _ hm (Or.inl hpa)
    have high {P S : List ℕ} {i : ℕ} (he : s = P ++ [i, i] ++ S)
        (hp : p = P.length) (hpa : priority a = 2) :
        ∀ k, i < k → rawCounts s k ≤ 1 := by
      intro k hk
      by_contra hn
      obtain ⟨Q, T, he'⟩ := dup k (by omega)
      have pos : P.length < Q.length :=
        position_order hs (by simpa using he) (by simpa using he') hk
      rcases k with _ | _ | k
      · omega
      · have hm : Move Q.length .twos s (Q ++ [0, 2] ++ T) := by
          simpa [he'] using Move.twos Q T
        apply step.2 _ _ _ hm
        exact Or.inr ⟨hpa.symm, Or.inr ⟨rfl, by simpa only [hp] using pos⟩⟩
      · have hm : Move Q.length (.split k) s (Q ++ [k, k + 3] ++ T) := by
          simpa [he'] using Move.split Q T k
        apply step.2 _ _ _ hm
        exact Or.inr ⟨hpa.symm, Or.inr ⟨rfl, by simpa only [hp] using pos⟩⟩
    cases hm : step.1 with
    | switch P S i j hij => exact (ha rfl).elim
    | ones P S => trivial
    | twos P S => exact ⟨zero (by simp [priority]), high (P := P) (S := S) rfl rfl rfl⟩
    | split P S i => exact ⟨zero (by simp [priority]), high (P := P) (S := S) rfl rfl rfl⟩
    | merge P S i =>
      refine ⟨?_, ?_⟩
      · intro k
        by_contra hn
        obtain ⟨Q, T, he⟩ := dup k (by omega)
        rcases k with _ | _ | k
        · have hm : Move Q.length .ones _ (Q ++ [1] ++ T) := Move.ones Q T
          rw [← he] at hm
          exact step.2 _ _ _ hm (Or.inl (by simp [priority]))
        · have hm : Move Q.length .twos _ (Q ++ [0, 2] ++ T) := Move.twos Q T
          rw [← he] at hm
          exact step.2 _ _ _ hm (Or.inl (by simp [priority]))
        · have hm : Move Q.length (.split k) _ (Q ++ [k, k + 3] ++ T) := Move.split Q T k
          rw [← he] at hm
          exact step.2 _ _ _ hm (Or.inl (by simp [priority]))
      · intro b hb ⟨h₀, h₁⟩
        have mem₀ : b ∈ P ++ [i, i + 1] ++ S := List.count_pos_iff.mp (by
          simpa [rawCounts, Multiset.toFinsupp_apply] using h₀)
        have mem₁ : b + 1 ∈ P ++ [i, i + 1] ++ S := List.count_pos_iff.mp (by
          simpa [rawCounts, Multiset.toFinsupp_apply] using h₁)
        obtain ⟨Q, T, he⟩ := consecutive _ hs b mem₀ mem₁
        have pos : Q.length < P.length :=
          position_order (P := Q) (Q := P) (S := (b + 1) :: T) (T := (i + 1) :: S)
            hs (by simpa using he) (by simp) hb
        have hm : Move Q.length (.merge b) _ (Q ++ [b + 2] ++ T) := Move.merge Q T b
        rw [← he] at hm
        apply step.2 _ _ _ hm
        simp [Preferred, priority, pos]
  have context (P M S : List ℕ) :
      rawCounts (P ++ M ++ S) = rawCounts (P ++ S) + rawCounts M := by
    ext k
    simp [rawCounts, Multiset.toFinsupp_apply, List.count_append]
    omega
  have erase_move {p a s t} (step : Move p a s t) :
      (a = .switch ∧ rawCounts s = rawCounts t) ∨ RawMove a (rawCounts s) (rawCounts t) := by
    cases step with
    | switch P S i j h =>
      left
      refine ⟨rfl, ?_⟩
      ext k
      simp [rawCounts, Multiset.toFinsupp_apply, List.count_append, List.count_cons]
      omega
    | ones P S | twos P S | split P S i | merge P S i =>
      right
      rw [context, context]
      have inputs : ∀ (i : ℕ), rawCounts [i, i] = Finsupp.single i 2 := by
        intro i; ext k
        simp only [rawCounts, Multiset.toFinsupp_apply, Multiset.coe_count,
          Finsupp.single_apply, List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      have outputs : ∀ (i : ℕ), rawCounts [i] = Finsupp.single i 1 := by
        intro i; ext k
        simp [rawCounts, Finsupp.single_apply]
      have pair : ∀ (i j : ℕ), rawCounts [i, j] =
          Finsupp.single i 1 + Finsupp.single j 1 := by
        intro i j; ext k
        simp only [rawCounts, Multiset.toFinsupp_apply, Multiset.coe_count,
          Finsupp.add_apply, Finsupp.single_apply, List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
      first
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, outputs, add_assoc] using CarryStep.double_zero (rawCounts (P ++ S))
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, outputs]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, pair, add_assoc] using CarryStep.double_one (rawCounts (P ++ S))
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, pair]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [inputs, pair, add_assoc] using CarryStep.double_succ (rawCounts (P ++ S)) i
        · simp [rawInput, inputs]
        · simp [rawOutput, splitOutput, pair]
      | refine ⟨?_, rawCounts (P ++ S), ?_, ?_, by intro h; cases h⟩
        · simpa [pair, outputs, add_assoc] using CarryStep.adjacent (rawCounts (P ++ S)) i
        · simp [rawInput, pair]
        · simp [rawOutput, outputs]
  induction path with
  | nil => exact .nil _
  | cons step tail ih =>
    rcases erase_move step.1 with ⟨rfl, same⟩ | carry
    · simpa [reward, same] using ih
    · have h := RawGreedyPath.cons carry (preferred step carry.2.choose_spec.2.2) ih
      convert h using 1
      cases step.1 <;> rfl

/-- Every ordered state has a finite complete LGS continuation. The minimizing
rank selects an actual legal move; the descent combines carry measure and
inversions, so it includes arbitrary initial disorder and the singleton start. -/
theorem complete_lgs_exists (s : List ℕ) :
    ∃ t length weight, LGSPath s t length weight ∧ Terminal t := by
  classical
  by_cases terminal : Terminal s
  · exact ⟨s, 0, 0, .nil s, terminal⟩
  have available : ∃ p a t, Move p a s t := by
    simpa only [Terminal, not_forall, not_not] using terminal
  let rank (p : ℕ) (a : Action) := priority a * (s.length + 1) +
    if priority a = 0 then 0 else if priority a = 2 then s.length - p else p
  have ranked : ∃ r, ∃ p a t, Move p a s t ∧ rank p a = r := by
    obtain ⟨p, a, t, hm⟩ := available
    exact ⟨rank p a, p, a, t, hm, rfl⟩
  obtain ⟨p, a, t, move, hrank⟩ := Nat.find_spec ranked
  have position_bound {q b u} (hm : Move q b s u) : q + 1 < s.length := by
    cases hm <;> simp
  have selected : LGSMove p a s t := by
    refine ⟨move, ?_⟩
    intro q b u hm hpref
    have hp := position_bound move
    have hq := position_bound hm
    have lower : rank q b < rank p a := by
      cases a <;> cases b <;> simp only [Preferred, priority] at hpref <;>
        simp [rank, priority] <;> omega
    have impossible := Nat.find_min ranked (show rank q b < Nat.find ranked by omega)
    exact impossible ⟨q, b, u, hm, rfl⟩
  have descent : Prod.Lex (Prod.Lex (· < ·) (· < ·)) (· < ·)
      (carryMeasure (rawCounts t), inv (decode t))
      (carryMeasure (rawCounts s), inv (decode s)) := by
    by_cases ha : a = .switch
    · subst a
      have same : rawCounts s = rawCounts t := by
        cases move with
        | switch P S i j hij =>
          ext k
          simp [rawCounts, Multiset.toFinsupp_apply, List.count_append, List.count_cons]
          omega
      have he := lgs_move_potential selected
      simp only [reward, Nat.add_zero] at he
      rw [same]
      exact Prod.Lex.right _ (by omega)
    · have raw_decrease {c d : RawDigits} {w : ℕ} (h : RawPath c d w) :
          (c = d ∧ w = 0) ∨
            Prod.Lex (· < ·) (· < ·) (carryMeasure d) (carryMeasure c) := by
        induction h with
        | nil => exact Or.inl ⟨rfl, rfl⟩
        | cons hm tail ih =>
          right
          have first := carryStep_measure_decreases hm.1
          rcases ih with ⟨rfl, _⟩ | last
          · exact first
          · simp only [Prod.lex_def, carryMeasure] at first last ⊢
            omega
      have positive : 0 < reward s a := by
        cases move <;> simp_all [reward, rawCounts, Multiset.toFinsupp_apply,
          List.count_append] <;> omega
      have raw := path_raw_erasure (Path.cons move (Path.nil t))
      rcases raw_decrease raw with ⟨_, hz⟩ | hd
      · omega
      · exact Prod.Lex.left _ _ hd
  obtain ⟨u, length, weight, tail, done⟩ := complete_lgs_exists t
  exact ⟨u, length + 1, reward s a + weight, .cons selected tail, done⟩
termination_by (carryMeasure (rawCounts s), inv (decode s))
decreasing_by exact descent

/-- Full Conjecture 1.7: every positive start has a complete LGS run, and every
permitted complete LGS run is at least as long as every legal terminal rival. -/
theorem result : Conjecture17 := by
  have terminal_sorted {s : List ℕ} (h : Terminal s) : s.Pairwise (· ≤ ·) := by
    apply List.isChain_iff_pairwise.mp
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y P S he
    by_contra hn
    apply h P.length .switch (P ++ [y, x] ++ S)
    simpa [he] using Move.switch P S x y (by omega)
  refine ⟨fun n _ => complete_lgs_exists (List.replicate n 0), ?_⟩
  intro n hn g gl gw h hl hw gp gt hp ht
  have initial : inv (decode (List.replicate n 0)) = 0 :=
    (inversions_zero_iff_sorted _).mpr (by simp)
  have endpoint : inv (decode g) = 0 :=
    (inversions_zero_iff_sorted _).mpr (terminal_sorted gt)
  have exact_weight := lgs_path_potential gp
  have upper := path_potential hp
  have greedy := complete_greedy_reward (lgs_path_raw_erasure gp) (terminal_raw_canonical gt)
  have bound := raw_terminal_bound (path_raw_erasure hp) (terminal_raw_canonical ht)
  omega

#print axioms lgs_path_raw_erasure
#print axioms complete_lgs_exists
#print axioms result
#check @lgs_path_raw_erasure
#check @complete_lgs_exists
#check @result

end D5.S1.Digit.Carry.OrderedGame
