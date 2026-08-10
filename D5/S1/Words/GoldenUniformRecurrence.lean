/- GID: D5/S1/Words/GoldenUniformRecurrence
   generality: I
   mirror-B: D5/B/S1/Words/GoldenUniformRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden-word factors recur in an explicit uniformly linear window. -/

import D5.S1.Words.GoldenRecurrence

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

/-- The explicit, deliberately coarse recurrence window used below. -/
def goldenRecurrenceBound (n : Nat) : Nat :=
  3 * Nat.fib (Nat.greatestFib n + 5)

private def supertile : Nat → Bool → List Bool
  | 0, b => [b]
  | k + 1, b => (supertile k b).flatMap subst

private theorem supertile_true (k : Nat) : supertile k true = fibWord k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [supertile, fibWord, ih]

private theorem supertile_false (k : Nat) : supertile (k + 1) false = fibWord k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (supertile (k + 1) false).flatMap subst = (fibWord k).flatMap subst
      rw [ih]

private theorem fibWord_flatMap_supertile (r k : Nat) :
    fibWord (r + k) = (fibWord r).flatMap (supertile k) := by
  induction k with
  | zero => simp [supertile]
  | succ k ih =>
      rw [Nat.add_succ, fibWord, ih, List.flatMap_assoc]
      rfl

private theorem subst_flatMap_chain (letters : List Bool) :
    (letters.flatMap subst).IsChain (fun a b => a = true ∨ b = true) := by
  induction letters with
  | nil => simp
  | cons a letters ih =>
      cases a <;> cases letters with
      | nil => simp [subst]
      | cons b tail =>
          cases b <;> simp_all [subst, List.isChain_cons_cons]

private theorem fibWord_chain (r : Nat) :
    (fibWord r).IsChain (fun a b => a = true ∨ b = true) := by
  cases r with
  | zero => simp [fibWord]
  | succ r => simpa [fibWord] using subst_flatMap_chain (fibWord r)

private theorem pair_infix_fibWord_three {r : Nat} {a b : Bool}
    (hpair : [a, b] <:+: fibWord r) : [a, b] <:+: fibWord 3 := by
  have hab := (fibWord_chain r).infix hpair
  rw [List.isChain_pair] at hab
  cases a <;> cases b
  · simp at hab
  · decide
  · decide
  · decide

private theorem take_drop_isInfix (l : List α) (p n : Nat) :
    (l.drop p).take n <:+: l := by
  refine ⟨l.take p, l.drop (p + n), ?_⟩
  rw [List.append_assoc, List.drop_take_append_drop, List.take_append_drop]

private theorem goldenFactor_eq_take_drop (Q n p : Nat)
    (hQ : p + n ≤ (fibWord Q).length) :
    goldenFactor n p = ((fibWord Q).drop p).take n := by
  apply List.ext_get
  · simp only [goldenFactor, List.length_ofFn, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (by omega)]
  · intro i hi _
    have hin : i < n := by simpa [goldenFactor] using hi
    have hindex : p + i < (fibWord Q).length := by omega
    simpa [goldenFactor] using goldenWord_eq_fibWord_get Q (p + i) hindex

private theorem exists_flatMap_block {f : α → List β} {l : List α} {p : Nat}
    (hp : p < (l.flatMap f).length) :
    ∃ pre a post, l = pre ++ a :: post ∧
      (pre.flatMap f).length ≤ p ∧ p < (pre.flatMap f).length + (f a).length := by
  induction l generalizing p with
  | nil => simp at hp
  | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append] at hp
      by_cases ha : p < (f a).length
      · exact ⟨[], a, l, rfl, by simp, by simpa using ha⟩
      · have hfa : (f a).length ≤ p := by omega
        have hp_eq : p = (f a).length + (p - (f a).length) := by omega
        have hp' : p - (f a).length < (l.flatMap f).length := by omega
        obtain ⟨pre, b, post, hdecomp, hlo, hhi⟩ := ih hp'
        subst l
        refine ⟨a :: pre, b, post, by simp, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.length_append]
          omega
        · simp only [List.flatMap_cons, List.length_append]
          omega

private theorem take_drop_append_eq_left {x y : List α} {p n : Nat}
    (h : p + n ≤ x.length) : ((x ++ y).drop p).take n = (x.drop p).take n := by
  have hp : p ≤ x.length := by omega
  rw [List.drop_append_of_le_length hp, List.take_append_of_le_length]
  simp only [List.length_drop]
  omega

private theorem flatMap_window_infix_one_or_two {f : α → List β} {l : List α}
    {p n : Nat} (hnpos : 0 < n) (hblocks : ∀ a ∈ l, n < (f a).length)
    (hend : p + n ≤ (l.flatMap f).length) :
    (∃ a, [a] <:+: l ∧ ((l.flatMap f).drop p).take n <:+: f a) ∨
      ∃ a b, [a, b] <:+: l ∧ ((l.flatMap f).drop p).take n <:+: f a ++ f b := by
  have hp : p < (l.flatMap f).length := by omega
  obtain ⟨pre, a, post, hdecomp, hlo, hhi⟩ := exists_flatMap_block hp
  subst l
  let blocksBefore := pre.flatMap f
  let offset := p - blocksBefore.length
  have hp_eq : p = blocksBefore.length + offset := by
    dsimp [blocksBefore, offset]
    omega
  have hoff : offset < (f a).length := by
    dsimp [blocksBefore, offset]
    omega
  have hdrop :
      (((pre ++ a :: post).flatMap f).drop p).take n =
        (((a :: post).flatMap f).drop offset).take n := by
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hp_eq, ← List.drop_drop]
    simp [blocksBefore]
  cases post with
  | nil =>
      left
      refine ⟨a, ⟨pre, [], by simp⟩, ?_⟩
      rw [hdrop]
      simpa using take_drop_isInfix (f a) offset n
  | cons b tail =>
      right
      refine ⟨a, b, ⟨pre, tail, by simp⟩, ?_⟩
      have hb : n < (f b).length := hblocks b (by simp)
      have htwo : offset + n ≤ (f a ++ f b).length := by
        simp only [List.length_append]
        omega
      rw [hdrop]
      rw [show (a :: b :: tail).flatMap f = (f a ++ f b) ++ tail.flatMap f by simp]
      rw [take_drop_append_eq_left htwo]
      exact take_drop_isInfix (f a ++ f b) offset n

private theorem greatestFib_le_add_one (n : Nat) : Nat.greatestFib n ≤ n + 1 := by
  unfold Nat.greatestFib
  exact Nat.findGreatest_le _

private theorem supertile_longer_than {n k : Nat} (hk : k = Nat.greatestFib n)
    (hn : 0 < n) (b : Bool) : n < (supertile k b).length := by
  have hk2 : 2 ≤ k := by
    rw [hk, Nat.le_greatestFib]
    norm_num [Nat.fib]
    omega
  have hnext := Nat.lt_fib_greatestFib_add_one n
  rw [← hk] at hnext
  cases b with
  | false =>
      rw [show k = (k - 1) + 1 by omega, supertile_false, fibWord_length]
      rw [show k - 1 + 2 = k + 1 by omega]
      exact hnext
  | true =>
      rw [supertile_true, fibWord_length]
      exact hnext.trans_le (Nat.fib_mono (by omega))

private theorem supertile_infix_control {k : Nat} {a : Bool} :
    supertile k a <:+: fibWord (k + 3) := by
  have ha : [a] <:+: fibWord 3 := by cases a <;> decide
  have hflat := ha.flatMap (supertile k)
  rw [← fibWord_flatMap_supertile 3 k] at hflat
  simpa [Nat.add_comm] using hflat

private theorem supertile_pair_infix_control {r k : Nat} {a b : Bool}
    (hpair : [a, b] <:+: fibWord r) :
    supertile k a ++ supertile k b <:+: fibWord (k + 3) := by
  have hthree := pair_infix_fibWord_three hpair
  have hflat := hthree.flatMap (supertile k)
  rw [← fibWord_flatMap_supertile 3 k] at hflat
  simpa [Nat.add_comm] using hflat

private theorem goldenFactor_infix_control_word {n p : Nat} (hn : 0 < n) :
    goldenFactor n p <:+: fibWord (Nat.greatestFib n + 3) := by
  let k := Nat.greatestFib n
  let Q := p + n + 2
  have hkQ : k ≤ Q := by
    dsimp [k, Q]
    exact (greatestFib_le_add_one n).trans (by omega)
  have hQ : p + n ≤ (fibWord Q).length := by
    have hdiag := index_lt_diagonal_level Q
    dsimp [Q] at hdiag ⊢
    omega
  have hdecomp : fibWord Q = (fibWord (Q - k)).flatMap (supertile k) := by
    simpa [Nat.sub_add_cancel hkQ] using fibWord_flatMap_supertile (Q - k) k
  have hblocks : ∀ a ∈ fibWord (Q - k), n < (supertile k a).length := by
    intro a _
    exact supertile_longer_than rfl hn a
  have hend : p + n ≤ ((fibWord (Q - k)).flatMap (supertile k)).length := by
    rw [← hdecomp]
    exact hQ
  have hfactor := goldenFactor_eq_take_drop Q n p hQ
  rcases flatMap_window_infix_one_or_two hn hblocks hend with hone | htwo
  · obtain ⟨a, _, hwindow⟩ := hone
    rw [hfactor, hdecomp]
    exact hwindow.trans supertile_infix_control
  · obtain ⟨a, b, hpair, hwindow⟩ := htwo
    rw [hfactor, hdecomp]
    exact hwindow.trans (supertile_pair_infix_control hpair)

private theorem supertile_length_le_fibWord {m : Nat} (hm : 0 < m) (b : Bool) :
    (supertile m b).length ≤ (fibWord m).length := by
  cases b with
  | false =>
      rw [show m = (m - 1) + 1 by omega, supertile_false, fibWord_length,
        fibWord_length]
      exact Nat.fib_mono (by omega)
  | true => rw [supertile_true]

private theorem exists_control_word_after (m i : Nat) (hm : 0 < m) :
    ∃ Q left right, fibWord Q = left ++ fibWord m ++ right ∧
      i ≤ left.length ∧ left.length + (fibWord m).length ≤
        i + 3 * (fibWord m).length := by
  let L := (fibWord m).length
  let Q := i + 3 * L + m + 2
  have hL : 0 < L := by
    have hdiag := index_lt_diagonal_level m
    dsimp [L]
    omega
  have hmQ : m ≤ Q := by dsimp [Q]; omega
  have hspaceQ : i + 3 * L ≤ (fibWord Q).length := by
    have hdiag := index_lt_diagonal_level Q
    dsimp [Q] at hdiag ⊢
    omega
  have hdecomp : fibWord Q = (fibWord (Q - m)).flatMap (supertile m) := by
    simpa [Nat.sub_add_cancel hmQ] using fibWord_flatMap_supertile (Q - m) m
  have hi : i < ((fibWord (Q - m)).flatMap (supertile m)).length := by
    rw [← hdecomp]
    omega
  obtain ⟨pre, a, post, hletters, hlo, hhi⟩ := exists_flatMap_block hi
  rw [hletters] at hdecomp
  rw [hdecomp] at hspaceQ
  have haL : (supertile m a).length ≤ L := by
    simpa [L] using supertile_length_le_fibWord hm a
  cases post with
  | nil =>
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append] at hspaceQ
      omega
  | cons b post =>
      have hbL : (supertile m b).length ≤ L := by
        simpa [L] using supertile_length_le_fibWord hm b
      cases post with
      | nil =>
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.length_append] at hspaceQ
          omega
      | cons c tail =>
          have hcL : (supertile m c).length ≤ L := by
            simpa [L] using supertile_length_le_fibWord hm c
          have hpair : [b, c] <:+: fibWord (Q - m) := by
            rw [hletters]
            exact ⟨pre ++ [a], tail, by simp⟩
          have hbc := (fibWord_chain (Q - m)).infix hpair
          rw [List.isChain_pair] at hbc
          rcases hbc with hb | hc
          · subst b
            refine ⟨Q, pre.flatMap (supertile m) ++ supertile m a,
              supertile m c ++ tail.flatMap (supertile m), ?_, ?_, ?_⟩
            · simpa [supertile_true, List.append_assoc] using hdecomp
            · simp only [List.length_append]
              omega
            · simp only [List.length_append]
              omega
          · subst c
            refine ⟨Q,
              pre.flatMap (supertile m) ++ supertile m a ++ supertile m b,
              tail.flatMap (supertile m), ?_, ?_, ?_⟩
            · simpa [supertile_true, List.append_assoc] using hdecomp
            · simp only [List.length_append]
              omega
            · simp only [List.length_append]
              omega

private theorem goldenRecurrenceBound_eq_control_length (n : Nat) :
    goldenRecurrenceBound n = 3 * (fibWord (Nat.greatestFib n + 3)).length := by
  simp only [goldenRecurrenceBound, fibWord_length]

private theorem positive_factor_occurs_in_uniform_window {n : Nat} (hn : 0 < n)
    {w : List Bool} (hw : w ∈ goldenFactorSet n) (i : Nat) :
    ∃ j, i ≤ j ∧ j + n ≤ i + goldenRecurrenceBound n ∧ w = goldenFactor n j := by
  obtain ⟨p, hp⟩ := mem_goldenFactorSet.mp hw
  have hinfix : w <:+: fibWord (Nat.greatestFib n + 3) := by
    rw [hp]
    exact goldenFactor_infix_control_word hn
  obtain ⟨insideLeft, insideRight, hcontrol⟩ := hinfix
  have hm : 0 < Nat.greatestFib n + 3 := by omega
  obtain ⟨Q, left, right, hQ, hi, hend⟩ :=
    exists_control_word_after (Nat.greatestFib n + 3) i hm
  let j := (left ++ insideLeft).length
  have hsplit : fibWord Q = (left ++ insideLeft) ++ w ++ (insideRight ++ right) := by
    calc
      fibWord Q = left ++ fibWord (Nat.greatestFib n + 3) ++ right := hQ
      _ = left ++ (insideLeft ++ w ++ insideRight) ++ right := by rw [hcontrol]
      _ = (left ++ insideLeft) ++ w ++ (insideRight ++ right) := by
        simp [List.append_assoc]
  have hwlen : w.length = n := length_eq_of_mem_goldenFactorSet hw
  have hjQ : j + n ≤ (fibWord Q).length := by
    rw [hsplit]
    dsimp [j]
    simp only [List.length_append]
    omega
  refine ⟨j, ?_, ?_, ?_⟩
  · dsimp [j]
    simp only [List.length_append]
    omega
  · rw [goldenRecurrenceBound_eq_control_length]
    dsimp [j]
    simp only [List.length_append]
    have hinside : insideLeft.length + n ≤ (fibWord (Nat.greatestFib n + 3)).length := by
      have hlen := congrArg List.length hcontrol
      simp only [List.length_append] at hlen
      omega
    omega
  · rw [goldenFactor_eq_take_drop Q n j hjQ, hsplit]
    dsimp [j]
    simp [hwlen]

/-- Every length-`n` golden factor occurs wholly inside every window of the explicit bound. -/
theorem golden_factor_uniformly_recurrent {n : Nat} {w : List Bool}
    (hw : w ∈ goldenFactorSet n) :
    ∀ i, ∃ j, i ≤ j ∧ j + n ≤ i + goldenRecurrenceBound n ∧ w = goldenFactor n j := by
  intro i
  rcases n.eq_zero_or_pos with rfl | hn
  · have hwlen := length_eq_of_mem_goldenFactorSet hw
    have hwempty : w = [] := List.length_eq_zero_iff.mp (by simpa using hwlen)
    subst w
    exact ⟨i, le_rfl, by simp, by simp [goldenFactor]⟩
  · exact positive_factor_occurs_in_uniform_window hn hw i

/-- The explicit Fibonacci recurrence window is at most `39 * n` for positive lengths. -/
theorem golden_recurrenceBound_le (n : Nat) (hn : 0 < n) :
    goldenRecurrenceBound n ≤ 39 * n := by
  let k := Nat.greatestFib n
  have hk2 : 2 ≤ k := by
    dsimp [k]
    rw [Nat.le_greatestFib]
    norm_num [Nat.fib]
    omega
  have hfk : Nat.fib k ≤ n := by
    simpa [k] using Nat.fib_greatestFib_le n
  have hfk1 : Nat.fib (k + 1) ≤ 2 * n := by
    rw [Nat.fib_add_one (by omega : k ≠ 0)]
    have hpred : Nat.fib (k - 1) ≤ n :=
      (Nat.fib_mono (Nat.sub_le k 1)).trans hfk
    omega
  have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := by
    simpa using (@Nat.fib_add_two k)
  have h3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using (@Nat.fib_add_two (k + 1))
  have h4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using (@Nat.fib_add_two (k + 2))
  have h5 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using (@Nat.fib_add_two (k + 3))
  have hadd : Nat.fib (k + 5) = 3 * Nat.fib k + 5 * Nat.fib (k + 1) := by omega
  dsimp [goldenRecurrenceBound]
  change 3 * Nat.fib (k + 5) ≤ 39 * n
  rw [hadd]
  omega

/-- Direct linear-window form of uniform recurrence. -/
theorem golden_factor_uniformly_recurrent_linear {n : Nat} (hn : 0 < n)
    {w : List Bool} (hw : w ∈ goldenFactorSet n) :
    ∀ i, ∃ j, i ≤ j ∧ j + n ≤ i + 39 * n ∧ w = goldenFactor n j := by
  intro i
  obtain ⟨j, hij, hjend, hfactor⟩ := golden_factor_uniformly_recurrent hw i
  exact ⟨j, hij, hjend.trans (Nat.add_le_add_left (golden_recurrenceBound_le n hn) i), hfactor⟩

example : goldenRecurrenceBound 1 = 39 := by decide
example : goldenRecurrenceBound 2 = 63 := by decide

example : ∀ i ∈ Finset.range 13,
    ∀ w ∈ ({[true], [false]} : Finset (List Bool)),
    ∃ j ∈ Finset.Icc i (i + 2), w = goldenFactor 1 j := by
  decide

example : ∀ i ∈ Finset.range 13,
    ∀ w ∈ ({[true, false], [false, true], [true, true]} : Finset (List Bool)),
    ∃ j ∈ Finset.Icc i (i + 4), w = goldenFactor 2 j := by
  decide

end D5.S1.Words
