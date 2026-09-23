/- GID: D5/S1/Digit/Carry/OrderedGame/Optimality
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame/Optimality
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Legal weighted exchanges for complete raw greedy comparison. -/

import D5.S1.Digit.Carry.OrderedGame
import Mathlib.Data.List.Chain

namespace D5.S1.Digit.Carry.OrderedGame

/-- A singleton merge has a finite preferred high cascade and legal replay under arbitrary lower-boundary changes. -/
theorem singleton_merge_cascade {c d : RawDigits} {a : ℕ}
    (move : RawMove (.merge a) c d) (positive : 0 < a) (zero : c 0 ≤ 1)
    (lower : c a = 1) (upper : c (a + 1) = 1)
    (high : ∀ i, a + 1 < i → c i ≤ 1) :
    ∃ u n, RawGreedyPath d u n ∧ (∀ i, a ≤ i → u i ≤ 1) ∧
      (∀ i, i < a → u i = c i) ∧
      ∀ x : RawDigits, 0 < x a → (∀ i, a < i → x i = c i) →
        ∃ v, RawPath x v (1 + n) ∧ v + c = u + x := by
  classical
  obtain ⟨_, r, hc, hd, _⟩ := move
  have coord (i : ℕ) : d i + (if i = a then 1 else 0) +
      (if i = a + 1 then 1 else 0) = c i + (if i = a + 2 then 1 else 0) := by
    simp [hc, hd, rawInput, rawOutput, Finsupp.single_apply, eq_comm]
    omega
  have dz : d 0 ≤ 1 := by have := coord 0; split_ifs at this <;> omega
  have dh₀ : d a = 0 := by have := coord a; split_ifs at this <;> omega
  have dh₁ : d (a + 1) = 0 := by
    have := coord (a + 1); split_ifs at this <;> omega
  have dh₂ : d (a + 2) ≤ 2 := by
    have := coord (a + 2); have := high (a + 2) (by omega)
    split_ifs at * <;> omega
  have dhi : ∀ i, a + 2 < i → d i ≤ 1 := by
    intro i hi; have := coord i; have := high i (by omega)
    split_ifs at * <;> omega
  obtain ⟨u, n, path, binary, low, replay⟩ := high_cascade positive dz dh₀ dh₁ dh₂ dhi
  refine ⟨u, n, path, binary, ?_, ?_⟩
  · intro i hi
    rw [low i hi]
    have := coord i; split_ifs at this <;> omega
  · intro x xa agree
    have xu : x (a + 1) = 1 := (agree _ (by omega)).trans upper
    have le : rawInput (.merge a) ≤ x := by
      intro i
      simp only [rawInput, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> subst_vars <;> omega
    let s := x - rawInput (.merge a)
    have hs : s + rawInput (.merge a) = x := tsub_add_cancel_of_le le
    let y := s + rawOutput (.merge a)
    have first : RawMove (.merge a) x y := by
      refine ⟨?_, s, hs.symm, rfl, by simp⟩
      rw [← hs]
      simpa [y, rawInput, rawOutput, add_assoc] using CarryStep.adjacent s a
    have balance (i : ℕ) : y i + c i = d i + x i := by
      have hx := congrArg (fun q : RawDigits => q i) hs
      have hc' := congrArg (fun q : RawDigits => q i) hc
      dsimp [y]
      simp only [Finsupp.add_apply] at hx hc' ⊢
      rw [hd]; simp only [Finsupp.add_apply]
      omega
    have same : ∀ i, a < i → y i = d i := by
      intro i hi; have := balance i; rw [agree i hi] at this; omega
    obtain ⟨v, rest, eq⟩ := replay y same
    refine ⟨v, ?_, ?_⟩
    · simpa [rawReward, xu] using RawPath.cons first rest
    · ext i
      have he := congrArg (fun q : RawDigits => q i) eq
      have hb := balance i
      simp only [Finsupp.add_apply] at he ⊢
      omega

/-- The finite high cascade permits a lower preferred split to be extracted first, with a common endpoint and exact reward. -/
theorem lower_split_merge_exchange {c c' d : RawDigits} {a j : ℕ}
    (merge : RawMove (.merge a) c d) (first : SplitStep j c c')
    (positive : 0 < j) (order : j < a)
    (preferred : RawPreferred c (splitAction j))
    (lower : c a = 1) (upper : c (a + 1) = 1) :
    ∃ u v n, RawGreedyPath d u n ∧ RawMove (splitAction j) u v ∧
      RawPreferred u (splitAction j) ∧ RawPath c' v (1 + n) ∧
      splitReward u j = splitReward c j := by
  classical
  have zero : c 0 ≤ 1 := by
    rcases j with _ | _ | j <;> simp_all [splitAction, RawPreferred]
  have high : ∀ i, j < i → c i ≤ 1 := by
    rcases j with _ | _ | j <;> simp_all [splitAction, RawPreferred]
  obtain ⟨u, n, path, binary, low, replay⟩ :=
    singleton_merge_cascade merge (by omega) zero lower upper
      (fun i hi => high i (by omega))
  obtain ⟨r, hc, hc'⟩ := first
  have enabled : 2 ≤ u j := by rw [low j order, hc]; simp
  let s := u - Finsupp.single j 2
  have hs : s + Finsupp.single j 2 = u :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr enabled)
  let v := s + splitOutput j
  have move : RawMove (splitAction j) u v := by
    refine ⟨?_, s, ?_, ?_, ?_⟩
    · rw [← hs]
      rcases j with _ | _ | j
      · exact CarryStep.double_zero s
      · simpa [v, splitOutput, add_assoc] using CarryStep.double_one s
      · simpa [v, splitOutput, add_assoc] using CarryStep.double_succ s j
    · rcases j with _ | _ | j <;> exact hs.symm
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> simp [splitAction]
  have up : RawPreferred u (splitAction j) := by
    have uz : u 0 ≤ 1 := by rw [low 0 (by omega)]; exact zero
    have uh : ∀ i, j < i → u i ≤ 1 := by
      intro i hi
      by_cases hai : a ≤ i
      · exact binary i hai
      · rw [low i (by omega)]; exact high i hi
    rcases j with _ | _ | j <;> simp_all [splitAction, RawPreferred]
  have ca : 0 < c' a := by
    have ha := congrArg (fun q : RawDigits => q a) hc
    rw [hc']
    simp only [Finsupp.add_apply, Finsupp.single_apply] at ha ⊢
    have ne : j ≠ a := by omega
    simp only [ne, if_false, Nat.add_zero] at ha
    omega
  have agree : ∀ i, a < i → c' i = c i := by
    intro i hi
    rw [hc, hc']
    rcases j with _ | _ | j <;>
      simp only [splitOutput, Finsupp.add_apply, Finsupp.single_apply] <;>
      split_ifs <;> omega
  obtain ⟨v', rep, balance⟩ := replay c' ca agree
  have same : v' = v := by
    ext i
    have hb := congrArg (fun q : RawDigits => q i) balance
    have hh := congrArg (fun q : RawDigits => q i) hs
    rw [hc, hc'] at hb
    dsimp [v]
    simp only [Finsupp.add_apply] at hb hh ⊢
    omega
  subst v'
  refine ⟨u, v, n, path, move, up, rep, ?_⟩
  rcases j with _ | _ | j
  · omega
  · simp only [splitReward, low 1 order]
  · simp only [splitReward, low (j + 1) (by omega), low (j + 2) order]

/-- The finite high cascade of a separated binary merge commutes with the least merge, including the lower boundary case. -/
theorem binary_separated_merge_exchange {c c' d : RawDigits} {a b : ℕ}
    (first : RawMove (.merge a) c c') (preferred : RawPreferred c (.merge a))
    (competing : RawMove (.merge b) c d) (order : a + 3 ≤ b) :
    ∃ u v n, RawGreedyPath d u n ∧ RawMove (.merge a) u v ∧
      RawPreferred u (.merge a) ∧ RawPath c' v (1 + n) ∧
      rawReward u (.merge a) = 1 := by
  classical
  have enabled {i : ℕ} {x : RawDigits} (m : RawMove (.merge i) c x) :
      c i = 1 ∧ c (i + 1) = 1 := by
    obtain ⟨_, r, hc, _, _⟩ := m
    have lo := preferred.1 i
    have hi := preferred.1 (i + 1)
    simp [hc, rawInput] at lo hi ⊢
    omega
  obtain ⟨ca, ca1⟩ := enabled first
  obtain ⟨cb, cb1⟩ := enabled competing
  obtain ⟨u, n, path, binary, low, replay⟩ :=
    singleton_merge_cascade competing (by omega) (preferred.1 0) cb cb1
      (fun i _ => preferred.1 i)
  have ua : u a = 1 := (low a (by omega)).trans ca
  have ua1 : u (a + 1) = 1 := (low (a + 1) (by omega)).trans ca1
  have le : rawInput (.merge a) ≤ u := by
    intro i
    simp only [rawInput, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> subst_vars <;> omega
  let s := u - rawInput (.merge a)
  have hs : s + rawInput (.merge a) = u := tsub_add_cancel_of_le le
  let v := s + rawOutput (.merge a)
  have move : RawMove (.merge a) u v := by
    refine ⟨?_, s, hs.symm, rfl, by simp⟩
    rw [← hs]
    simpa [v, rawInput, rawOutput, add_assoc] using CarryStep.adjacent s a
  have up : RawPreferred u (.merge a) := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : b ≤ i
      · exact binary i h
      · rw [low i (by omega)]; exact preferred.1 i
    · intro i hi
      rw [low i (by omega), low (i + 1) (by omega)]
      exact preferred.2 i hi
  obtain ⟨_, r, hc, hc', _⟩ := first
  have agree : ∀ i, a + 2 < i → c' i = c i := by
    intro i hi
    simp only [hc, hc', rawInput, rawOutput, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  obtain ⟨v', rep, balance⟩ :=
    replay c' (by rw [agree b (by omega), cb]; omega)
      (fun i hi => agree i (by omega))
  have same : v' = v := by
    ext i
    have hb := congrArg (fun q : RawDigits => q i) balance
    have hh := congrArg (fun q : RawDigits => q i) hs
    rw [hc, hc'] at hb
    dsimp [v]
    simp only [Finsupp.add_apply] at hb hh ⊢
    omega
  subst v'
  exact ⟨u, v, n, path, move, up, rep, ua1⟩

/-- Every legal terminal raw path is bounded by the concrete greedy reward.
The induction uses optimality only at strict carry successors. Split competitors
are settled before shared-input merges; binary merges use an inner descent on
their index. No Bellman inequality is assumed. -/
theorem raw_terminal_bound {c e : RawDigits} {w : ℕ}
    (path : RawPath c e w) (complete : CanonicalRaw e) : w ≤ G c := by
  classical
  have higher_split_merge_exchange {c c' d : RawDigits} {a j : ℕ}
      (merge : RawMove (.merge a) c d) (first : SplitStep (j + 2) c c')
      (preferred : RawPreferred c (.split j)) (order : a ≤ j) :
      ∃ u, RawMove (.split j) d u ∧ RawPreferred d (.split j) ∧
        RawMove (.merge a) c' u ∧
        rawReward c (.merge a) + rawReward d (.split j) =
          splitReward c (j + 2) + rawReward c' (.merge a) := by
    classical
    obtain ⟨_, r, hc, hd, _⟩ := merge
    obtain ⟨q, hq, hc'⟩ := first
    have enabled : 2 ≤ r (j + 2) := by
      have eq := congrArg (fun f : RawDigits => f (j + 2)) (hc.symm.trans hq)
      simp only [rawInput, Finsupp.add_apply, Finsupp.single_apply] at eq
      split_ifs at eq <;> omega
    let t := r - Finsupp.single (j + 2) 2
    have ht : t + Finsupp.single (j + 2) 2 = r :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr enabled)
    have qt : q = t + rawInput (.merge a) := by
      apply add_right_cancel (b := Finsupp.single (j + 2) 2)
      rw [← hq, hc, ← ht]; ac_rfl
    let u := t + rawOutput (.merge a) + splitOutput (j + 2)
    have across : RawMove (.split j) d u := by
      refine ⟨?_, t + rawOutput (.merge a), ?_, rfl, by simp⟩
      · rw [hd, ← ht]
        simpa [u, rawOutput, splitOutput, add_assoc, add_left_comm, add_comm] using
          CarryStep.double_succ (t + rawOutput (.merge a)) j
      · rw [hd, ← ht]; simp only [rawInput]; ac_rfl
    have replay : RawMove (.merge a) c' u := by
      refine ⟨?_, t + splitOutput (j + 2), ?_, ?_, by simp⟩
      · rw [hc', qt]
        simpa [u, rawInput, rawOutput, add_assoc, add_left_comm, add_comm] using
          CarryStep.adjacent (t + splitOutput (j + 2)) a
      · rw [hc', qt]; ac_rfl
      · dsimp [u]; ac_rfl
    have priority : RawPreferred d (.split j) := by
      refine ⟨?_, ?_⟩
      · have hz := preferred.1
        simp only [hc, hd, rawInput, rawOutput, Finsupp.add_apply,
          Finsupp.single_apply] at hz ⊢
        split_ifs at * <;> omega
      · intro i hi
        have old := preferred.2 i hi
        simp only [hc, hd, rawInput, rawOutput, Finsupp.add_apply,
          Finsupp.single_apply] at old ⊢
        split_ifs at * <;> omega
    refine ⟨u, across, priority, replay, ?_⟩
    rw [hc, hd, hc', qt, ← ht]
    simp [rawReward, splitReward, rawInput, rawOutput, splitOutput,
      Finsupp.single_apply]
    split_ifs <;> omega
  have binary_predecessor_detour {c d : RawDigits} {b : ℕ}
      (merge : RawMove (.merge (b + 1)) c d)
      (left : c b = 1) (middle : c (b + 1) = 1) (right : c (b + 2) = 1) :
      ∃ x, RawMove (.merge b) c x ∧ RawMove (.split b) x d ∧
        rawReward c (.merge b) = 1 ∧ rawReward x (.split b) = 1 := by
    classical
    obtain ⟨_, r, hc, hd, _⟩ := merge
    have rb : r b = 1 := by
      simpa [hc, rawInput, Finsupp.single_apply, Nat.add_assoc] using left
    let t := r - Finsupp.single b 1
    have ht : t + Finsupp.single b 1 = r :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))
    let x := t + Finsupp.single (b + 2) 2
    have two : Finsupp.single (b + 2) 2 =
        (Finsupp.single (b + 2) 1 + Finsupp.single (b + 2) 1 : RawDigits) := by
      rw [← Finsupp.single_add]
    have before : RawMove (.merge b) c x := by
      have hin : c = (t + Finsupp.single (b + 2) 1) + rawInput (.merge b) := by
        rw [hc, ← ht]; simp only [rawInput, Nat.add_assoc]; ac_rfl
      have hout : x = (t + Finsupp.single (b + 2) 1) + rawOutput (.merge b) := by
        dsimp [x, rawOutput]; rw [two]; ac_rfl
      refine ⟨?_, t + Finsupp.single (b + 2) 1, hin, hout, by simp⟩
      rw [hin, hout]
      convert CarryStep.adjacent (t + Finsupp.single (b + 2) 1) b using 1 <;>
        simp only [rawInput, rawOutput] <;> ac_rfl
    have after : RawMove (.split b) x d := by
      refine ⟨?_, t, rfl, ?_, by simp⟩
      · rw [hd, ← ht]
        simpa [x, rawOutput, add_assoc] using CarryStep.double_succ t b
      · rw [hd, ← ht]; simp [rawOutput, splitOutput, add_assoc]
    refine ⟨x, before, after, middle, ?_⟩
    have hm := middle
    have hr := right
    rw [hc, ← ht] at hm hr
    simp [rawInput, Finsupp.single_apply, Nat.add_assoc] at hm hr
    simp [x, rawReward, splitReward, Finsupp.single_apply, hm, hr]
  have erase {x y : RawDigits} {v : ℕ} (p : RawGreedyPath x y v) : RawPath x y v := by
    induction p with
    | nil x => exact .nil x
    | cons m _ _ ih => exact .cons m ih
  have append {x y z : RawDigits} {v t : ℕ}
      (p : RawPath x y v) (q : RawPath y z t) : RawPath x z (v + t) := by
    induction p with
    | nil => simpa using q
    | cons m _ ih => simpa [Nat.add_assoc] using RawPath.cons m (ih q)
  have splitRaw {x y : RawDigits} {j : ℕ} (p : SplitStep j x y) :
      RawMove (splitAction j) x y := by
    obtain ⟨r, rfl, rfl⟩ := p
    refine ⟨?_, r, ?_, ?_, ?_⟩
    · rcases j with _ | _ | j
      · exact CarryStep.double_zero r
      · simpa [splitOutput, add_assoc] using CarryStep.double_one r
      · simpa [splitOutput, add_assoc] using CarryStep.double_succ r j
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> simp [splitAction]
  have asSplit {x y : RawDigits} {j : ℕ} (p : RawMove (splitAction j) x y) :
      SplitStep j x y := by
    obtain ⟨_, r, hx, hy, _⟩ := p
    refine ⟨r, ?_, ?_⟩ <;> rcases j with _ | _ | j <;> assumption
  have sr (x : RawDigits) (j : ℕ) : rawReward x (splitAction j) = splitReward x j := by
    rcases j with _ | _ | j <;> rfl
  have enabled {x y : RawDigits} {a : Action} (p : RawMove a x y) :
      match a with
      | .switch => False
      | .ones => 2 ≤ x 0
      | .twos => 2 ≤ x 1
      | .split i => 2 ≤ x (i + 2)
      | .merge i => 0 < x i ∧ 0 < x (i + 1) := by
    obtain ⟨_, r, rfl, _, hn⟩ := p
    cases a <;> try exact hn rfl
    all_goals simp_all [rawInput]
  have recurrence {x y : RawDigits} {a : Action} (m : RawMove a x y)
      (p : RawPreferred x a) : G x = rawReward x a + G y := by
    obtain ⟨z, tail, canonical⟩ := greedy_attainment y
    exact (complete_greedy_reward (.cons m p tail) canonical).symm
  have prefixValue {x y : RawDigits} {v : ℕ} (p : RawGreedyPath x y v) :
      G x = v + G y := by
    induction p with
    | nil => simp
    | cons m pref _ ih => rw [recurrence m pref, ih, Nat.add_assoc]
  have below {a : Action} {d f : RawDigits} {v : ℕ}
      (first : RawMove a c d) (p : RawPath d f v) : v + G f ≤ G d := by
    obtain ⟨z, tail, canonical⟩ := greedy_attainment f
    exact raw_terminal_bound (append p (erase tail)) canonical
  have bellman {a : Action} {d : RawDigits} (move : RawMove a c d) :
      rawReward c a + G d ≤ G c := by
    generalize hd : greedyDecision c = decision
    cases decision with
    | terminal canonical =>
      have hm := enabled move
      cases a with
      | switch => exact hm.elim
      | ones => have := canonical.1 0; omega
      | twos => have := canonical.1 1; omega
      | split i => have := canonical.1 (i + 2); omega
      | merge i =>
        have := canonical.1 i
        have := canonical.2 i (by omega)
        omega
    | step b c' chosen preferred =>
      have eq := recurrence chosen preferred
      have splitCase (j : ℕ) (hb : b = splitAction j) :
          rawReward c a + G d ≤ G c := by
        subst b
        have first := asSplit chosen
        rw [sr] at eq
        by_cases zero : j = 0
        · subst j
          obtain ⟨f, tail, canonical⟩ := greedy_attainment d
          obtain ⟨v, replay, gain⟩ :=
            ones_terminal_promotion (.cons move (erase tail)) canonical first
          have bound := below chosen replay
          omega
        have high : ∀ i, j < i → c i ≤ 1 := by
          rcases j with _ | _ | j
          · exact (zero rfl).elim
          · exact preferred.2
          · exact preferred.2
        have splitBound {i : ℕ} {x : RawDigits} (m : SplitStep i c x) :
            splitReward c i + G x ≤ G c := by
          obtain ⟨f, tail, canonical⟩ := greedy_attainment x
          obtain ⟨v, replay, gain⟩ :=
            split_greedy_terminal_promotion m tail canonical first (Or.inr high)
          have bound := below chosen replay
          omega
        have hm := enabled move
        cases a with
        | switch => exact hm.elim
        | ones => exact splitBound (asSplit (j := 0) move)
        | twos => exact splitBound (asSplit (j := 1) move)
        | split i => exact splitBound (asSplit (j := i + 2) move)
        | merge k =>
          by_cases shared : 2 ≤ c k ∨ 2 ≤ c (k + 1)
          · obtain ⟨x, v, step, repair, gain⟩ := shared_input_merge_repair move shared
            have tailBound := below (splitRaw step) repair
            have headBound := splitBound step
            omega
          have ck : c k = 1 := by omega
          have ck1 : c (k + 1) = 1 := by omega
          have cj : 2 ≤ c j := by obtain ⟨r, rfl, _⟩ := first; simp
          have positions : j < k ∨ k + 2 ≤ j := by
            by_contra hn
            have h : j = k ∨ j = k + 1 := by omega
            rcases h with rfl | rfl <;> omega
          rcases positions with lower | higher
          · obtain ⟨u, v, n, pre, step, pref, replay, sameReward⟩ :=
              lower_split_merge_exchange move first (by omega) lower preferred ck ck1
            have gv := recurrence step pref
            rw [sr, sameReward] at gv
            have gd := prefixValue pre
            have bound := below chosen replay
            change c (k + 1) + G d ≤ G c
            omega
          · rcases j with _ | _ | j
            · omega
            · omega
            · obtain ⟨u, across, pref, replay, gain⟩ :=
                higher_split_merge_exchange move first preferred (by omega)
              have gd := recurrence across pref
              have bound := below chosen (RawPath.cons replay (.nil u))
              simp only [Nat.add_zero] at bound
              change G c = splitReward c (j + 2) + G c' at eq
              omega
      cases b with
      | switch => exact preferred.elim
      | ones => exact splitCase 0 rfl
      | twos => exact splitCase 1 rfl
      | split j => exact splitCase (j + 2) rfl
      | merge k =>
        have binary := preferred.1
        have singles {i : ℕ} {x : RawDigits} (m : RawMove (.merge i) c x) :
            c i = 1 ∧ c (i + 1) = 1 := by
          have hm := enabled m
          have := binary i; have := binary (i + 1)
          omega
        have ck := singles chosen
        have merges : ∀ i, ∀ {x : RawDigits}, RawMove (.merge i) c x →
            c (i + 1) + G x ≤ G c := by
          intro i
          induction i using Nat.strong_induction_on with
          | h i ih =>
            intro x competing
            have ci := singles competing
            have ki : k ≤ i := by
              by_contra hn
              exact preferred.2 i (by omega) (by omega)
            by_cases same : i = k
            · subst i
              obtain ⟨_, r, hr, hx, _⟩ := competing
              obtain ⟨_, s, hs, hc', _⟩ := chosen
              have rs : r = s := add_right_cancel (hr.symm.trans hs)
              have xx : x = c' := by simpa [hx, hc', rs]
              rw [xx]; exact le_of_eq eq.symm
            by_cases predecessor : c (i - 1) = 1
            · cases i with
              | zero => omega
              | succ h =>
                obtain ⟨y, before, after, r₁, r₂⟩ :=
                  binary_predecessor_detour competing (by simpa using predecessor) ci.1 ci.2
                have localBound := below before (RawPath.cons after (.nil x))
                have earlier := ih h (by omega) before
                simp only [Nat.add_zero, r₂] at localBound
                change c (h + 1) = 1 at r₁
                omega
            · have predZero : c (i - 1) = 0 := by have := binary (i - 1); omega
              have ne₁ : i ≠ k + 1 := by
                intro h; subst i; simp only [Nat.add_sub_cancel] at predZero; omega
              have ne₂ : i ≠ k + 2 := by
                intro h; subst i
                have h : k + 2 - 1 = k + 1 := by omega
                rw [h] at predZero; omega
              obtain ⟨u, v, n, pre, step, pref, replay, sameReward⟩ :=
                binary_separated_merge_exchange chosen preferred competing (by omega)
              have gd := prefixValue pre
              have gu := recurrence step pref
              have bound := below chosen replay
              change G c = c (k + 1) + G c' at eq
              rw [sameReward] at gu
              omega
        have hm := enabled move
        cases a with
        | switch => exact hm.elim
        | ones => have := binary 0; omega
        | twos => have := binary 1; omega
        | split i => have := binary (i + 2); omega
        | merge i => exact merges i move
  cases path with
  | nil => exact Nat.zero_le _
  | @cons a c d e w move tail =>
    have bound := below move tail
    have first := bellman move
    omega
termination_by (tokenCount c, indexWeight c)
decreasing_by exact carryStep_measure_decreases first.1

/-- An ordered terminal state has binary, nonconsecutive raw multiplicities.
Absence of each of the five actual adjacent operations forces a gap of at
least two between successive list entries. -/
theorem terminal_raw_canonical {s : List ℕ} (terminal : Terminal s) :
    CanonicalRaw (rawCounts s) := by
  letI : IsTrans ℕ (fun a b => a + 2 ≤ b) := ⟨by omega⟩
  have spaced : s.Pairwise (fun a b => a + 2 ≤ b) := by
    apply List.isChain_iff_pairwise.mp
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y P S heq
    have ordered : x ≤ y := by
      by_contra h
      apply terminal P.length .switch (P ++ [y, x] ++ S)
      subst s
      simpa using Move.switch P S x y (by omega)
    have distinct : x ≠ y := by
      intro h; subst y; subst s
      rcases x with _ | _ | x
      · apply terminal P.length .ones (P ++ [1] ++ S)
        simpa using Move.ones P S
      · apply terminal P.length .twos (P ++ [0, 2] ++ S)
        simpa using Move.twos P S
      · apply terminal P.length (.split x) (P ++ [x, x + 3] ++ S)
        simpa using Move.split P S x
    have apart : x + 1 ≠ y := by
      intro h; subst y; subst s
      apply terminal P.length (.merge x) (P ++ [x + 2] ++ S)
      simpa using Move.merge P S x
    omega
  have separate : ∀ i ∈ s, i + 1 ∉ s := by
    clear terminal
    induction s with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp spaced
      intro i hi hj
      simp only [List.mem_cons] at hi hj
      rcases hi with rfl | hi <;> rcases hj with hj | hj
      · omega
      · have := head _ hj; omega
      · have := head _ hi; omega
      · exact ih tail i hi hj
  have nodup : s.Nodup := by
    exact spaced.imp (fun h => by omega)
  refine ⟨?_, ?_⟩
  · intro i
    simpa [rawCounts, Multiset.toFinsupp_apply] using
      List.nodup_iff_count_le_one.mp nodup i
  · intro i hi
    have mem : i ∈ s := by
      have count : s.count i = 1 := by
        simpa [rawCounts, Multiset.toFinsupp_apply] using hi
      apply List.count_pos_iff.mp
      omega
    simpa [rawCounts, Multiset.toFinsupp_apply] using
      List.count_eq_zero.mpr (separate i mem)

end D5.S1.Digit.Carry.OrderedGame
