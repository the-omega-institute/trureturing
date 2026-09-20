/- GID: D5/S1/Digit/Carry/OrderedGame
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Concrete raw greedy attainment, weighted merge repairs, ones promotion, and ordered reward erasure. -/

import D5.S1.Digit.Raw
import D5.S1.Digit.Carry.ListInversions
import D5.S1.Digit.Carry.SplitStabilization

namespace D5.S1.Digit.Carry.OrderedGame

open ListInversions

/-- Decode raw W indices to the paper's positive indices. -/
def decode (s : List ℕ) : List ℕ := s.map Nat.succ

/-- Multiplicities, not a position-indexed finitely supported list. -/
noncomputable def rawCounts (s : List ℕ) : RawDigits :=
  Multiset.toFinsupp (s : Multiset ℕ)

/-- Labels retain the raw carry index; a switch has no carry reward. -/
inductive Action where
  | switch
  | ones
  | twos
  | split (i : ℕ)
  | merge (a : ℕ)

/-- All five contextual adjacent moves, in zero-based indices. The general
split at raw index i+2 decodes to the paper's split at positive index i+3. -/
inductive Move : ℕ → Action → List ℕ → List ℕ → Prop where
  | switch (P S : List ℕ) (i j : ℕ) (h : j < i) :
      Move P.length .switch (P ++ [i, j] ++ S) (P ++ [j, i] ++ S)
  | ones (P S : List ℕ) : Move P.length .ones (P ++ [0, 0] ++ S) (P ++ [1] ++ S)
  | twos (P S : List ℕ) : Move P.length .twos (P ++ [1, 1] ++ S) (P ++ [0, 2] ++ S)
  | split (P S : List ℕ) (i : ℕ) :
      Move P.length (.split i) (P ++ [i + 2, i + 2] ++ S) (P ++ [i, i + 3] ++ S)
  | merge (P S : List ℕ) (a : ℕ) :
      Move P.length (.merge a) (P ++ [a, a + 1] ++ S) (P ++ [a + 2] ++ S)

/-- Full carry-then-sort reward, including the carry itself. -/
noncomputable def reward (s : List ℕ) : Action → ℕ
  | .switch => 0
  | .ones => rawCounts s 0 - 1
  | .twos => rawCounts s 1 - 1
  | .split i => rawCounts s (i + 1) + rawCounts s (i + 2) - 1
  | .merge a => rawCounts s (a + 1)

/-- Finite legal paths retain both actual move count and summed carry reward. -/
inductive Path : List ℕ → List ℕ → ℕ → ℕ → Prop where
  | nil (s) : Path s s 0 0
  | cons {position a s t u length weight} (move : Move position a s t)
      (tail : Path t u length weight) :
      Path s u (length + 1) (reward s a + weight)

/-- The consumed raw digits of a carry label. Switches are excluded by RawMove. -/
noncomputable def rawInput : Action → RawDigits
  | .switch => 0
  | .ones => Finsupp.single 0 2
  | .twos => Finsupp.single 1 2
  | .split i => Finsupp.single (i + 2) 2
  | .merge a => Finsupp.single a 1 + Finsupp.single (a + 1) 1

/-- The produced raw digits of a carry label. -/
noncomputable def rawOutput : Action → RawDigits
  | .switch => 0
  | .ones => splitOutput 0
  | .twos => splitOutput 1
  | .split i => splitOutput (i + 2)
  | .merge a => Finsupp.single (a + 2) 1

/-- A label together with the actual existing carry relation and its context. -/
def RawMove (a : Action) (c d : RawDigits) : Prop :=
  CarryStep c d ∧ ∃ rest, c = rest + rawInput a ∧
    d = rest + rawOutput a ∧ a ≠ .switch

/-- Full raw carry reward, sharing the split reward used in stabilization. -/
def rawReward (c : RawDigits) : Action → ℕ
  | .switch => 0
  | .ones => splitReward c 0
  | .twos => splitReward c 1
  | .split i => splitReward c (i + 2)
  | .merge a => c (a + 1)

/-- Labelled weighted raw paths. Carry labels are explicit data; no data is
recovered by eliminating a proof of the unlabelled CarryStep proposition. -/
inductive RawPath : RawDigits → RawDigits → ℕ → Prop where
  | nil (c) : RawPath c c 0
  | cons {a c d e w} (move : RawMove a c d) (tail : RawPath d e w) :
      RawPath c e (rawReward c a + w)

/-- The label of a split at a raw index. -/
def splitAction : ℕ → Action
  | 0 => .ones
  | 1 => .twos
  | i + 2 => .split i

/-- The actual raw priority: zero first, otherwise highest duplicate, otherwise
the least consecutive pair in a binary state. Legality is recorded separately. -/
def RawPreferred (c : RawDigits) : Action → Prop
  | .switch => False
  | .ones => True
  | .twos => c 0 ≤ 1 ∧ ∀ k, 1 < k → c k ≤ 1
  | .split i => c 0 ≤ 1 ∧ ∀ k, i + 2 < k → c k ≤ 1
  | .merge a => (∀ k, c k ≤ 1) ∧ ∀ b, b < a → ¬(0 < c b ∧ 0 < c (b + 1))

/-- A concrete decision keeps its action as data, with a proof of legality and
priority; no action is extracted from the unlabelled carry proposition. -/
inductive GreedyDecision (c : RawDigits) : Type where
  | terminal (canonical : CanonicalRaw c)
  | step (a : Action) (d : RawDigits) (legal : RawMove a c d)
      (preferred : RawPreferred c a)

/-- Select the next actual greedy carry, recomputing priority at each state. -/
noncomputable def greedyDecision (c : RawDigits) : GreedyDecision c := by
  classical
  have takeSplit (j : ℕ) (enabled : 2 ≤ c j)
      (preferred : RawPreferred c (splitAction j)) : GreedyDecision c := by
    let r := c - Finsupp.single j 2
    have hr : r + Finsupp.single j 2 = c :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr enabled)
    refine .step (splitAction j) (r + splitOutput j) ?_ preferred
    rw [← hr]
    refine ⟨?_, r, ?_, ?_, ?_⟩
    · rcases j with _ | _ | j
      · exact CarryStep.double_zero r
      · simpa [splitOutput, add_assoc] using CarryStep.double_one r
      · simpa [splitOutput, add_assoc] using CarryStep.double_succ r j
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> simp [splitAction]
  by_cases zero : 2 ≤ c 0
  · exact takeSplit 0 zero trivial
  let duplicates := c.support.filter (fun j => 2 ≤ c j)
  by_cases nonempty : duplicates.Nonempty
  · let j := duplicates.max' nonempty
    have mem : j ∈ duplicates := Finset.max'_mem _ _
    have enabled : 2 ≤ c j := (Finset.mem_filter.mp mem).2
    have high : ∀ k, j < k → c k ≤ 1 := by
      intro k hk
      by_contra hn
      have kmem : k ∈ duplicates := Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr (by omega), by omega⟩
      have := Finset.le_max' duplicates k kmem
      omega
    apply takeSplit j enabled
    rcases j with _ | _ | j
    · trivial
    · exact ⟨by omega, high⟩
    · exact ⟨by omega, high⟩
  have binary : ∀ k, c k ≤ 1 := by
    intro k
    by_contra hn
    exact nonempty ⟨k, Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (by omega), by omega⟩⟩
  by_cases adjacent : ∃ a, 0 < c a ∧ 0 < c (a + 1)
  · let a := Nat.find adjacent
    have enabled := Nat.find_spec adjacent
    let input := Finsupp.single a 1 + Finsupp.single (a + 1) 1
    have le : input ≤ c := by
      intro k
      change (Finsupp.single a 1 + Finsupp.single (a + 1) 1 : RawDigits) k ≤ c k
      by_cases h : k = a
      · subst k
        simpa [a, Nat.succ_le_iff] using enabled.1
      by_cases h' : k = a + 1
      · subst k
        simpa [a, Nat.succ_le_iff] using enabled.2
      simp [Finsupp.single_apply, Ne.symm h, Ne.symm h']
    let r := c - input
    have hr : r + input = c := tsub_add_cancel_of_le le
    refine .step (.merge a) (r + Finsupp.single (a + 2) 1) ?_ ?_
    · refine ⟨?_, r, hr.symm, rfl, by simp⟩
      rw [← hr]
      simpa [input, add_assoc] using CarryStep.adjacent r a
    · exact ⟨binary, fun b hb => Nat.find_min adjacent hb⟩
  · exact .terminal ⟨binary, fun i hi => by
      by_contra hn
      exact adjacent ⟨i, by omega, by omega⟩⟩

/-- Full reward of the concrete greedy continuation, by the strict carry
measure. This is not a maximum over arbitrary continuations. -/
noncomputable def G (c : RawDigits) : ℕ :=
  match greedyDecision c with
  | .terminal _ => 0
  | .step a d legal _ => rawReward c a + G d
termination_by (tokenCount c, indexWeight c)
decreasing_by exact carryStep_measure_decreases legal.1

/-- Every carry in a raw greedy path obeys the priority at its own source. -/
inductive RawGreedyPath : RawDigits → RawDigits → ℕ → Prop where
  | nil (c) : RawGreedyPath c c 0
  | cons {a c d e w} (legal : RawMove a c d) (preferred : RawPreferred c a)
      (tail : RawGreedyPath d e w) : RawGreedyPath c e (rawReward c a + w)

/-- The concrete greedy reward is attained by a finite legal priority path
ending at binary nonadjacent digits, for every raw start, including zero. -/
theorem greedy_attainment (c : RawDigits) :
    ∃ d, RawGreedyPath c d (G c) ∧ CanonicalRaw d := by
  rw [G]
  generalize hd : greedyDecision c = decision
  cases decision with
  | terminal canonical => exact ⟨c, .nil c, canonical⟩
  | step a d legal preferred =>
    obtain ⟨e, path, canonical⟩ := greedy_attainment d
    exact ⟨e, .cons legal preferred path, canonical⟩
termination_by (tokenCount c, indexWeight c)
decreasing_by exact carryStep_measure_decreases legal.1

/-- Every complete path obeying the raw priorities has exactly the concrete
greedy reward. Completeness is essential: a greedy prefix may stop early. -/
theorem complete_greedy_reward {c e : RawDigits} {w : ℕ}
    (path : RawGreedyPath c e w) (complete : CanonicalRaw e) : w = G c := by
  have enabled {a : Action} {x y : RawDigits} (move : RawMove a x y) :
      match a with
      | .switch => False
      | .ones => 2 ≤ x 0
      | .twos => 2 ≤ x 1
      | .split i => 2 ≤ x (i + 2)
      | .merge i => 0 < x i ∧ 0 < x (i + 1) := by
    obtain ⟨_, r, rfl, _, hn⟩ := move
    cases a <;> try exact hn rfl
    all_goals simp_all [rawInput, Finsupp.single_apply]
  have impossible {a : Action} {x y : RawDigits} (canonical : CanonicalRaw x)
      (move : RawMove a x y) : False := by
    have he := enabled move
    obtain ⟨binary, separate⟩ := canonical
    cases a with
    | switch => exact he
    | ones => have := binary 0; omega
    | twos => have := binary 1; omega
    | split i => have := binary (i + 2); omega
    | merge i =>
      have hi := binary i
      have := separate i (by omega)
      omega
  have unique {a b : Action} {x y z : RawDigits}
      (ma : RawMove a x y) (pa : RawPreferred x a)
      (mb : RawMove b x z) (pb : RawPreferred x b) : a = b ∧ y = z := by
    have ha := enabled ma
    have hb := enabled mb
    have same : a = b := by
      cases a <;> cases b <;> simp_all only [RawPreferred]
      all_goals grind
    subst b
    obtain ⟨_, r, hr, hy, _⟩ := ma
    obtain ⟨_, s, hs, hz, _⟩ := mb
    have rs : r = s := add_right_cancel (hr.symm.trans hs)
    exact ⟨rfl, by simpa [rs, hy, hz]⟩
  induction path with
  | nil c =>
    rw [G]
    generalize hd : greedyDecision c = decision
    cases decision with
    | terminal _ => rfl
    | step a d legal _ => exact (impossible complete legal).elim
  | @cons a c d e w legal preferred tail ih =>
    rw [G]
    generalize hd : greedyDecision c = decision
    cases decision with
    | terminal canonical => exact (impossible canonical legal).elim
    | step b d' legal' preferred' =>
      obtain ⟨rfl, rfl⟩ := unique legal preferred legal' preferred'
      rw [ih complete]

/-- Exact additional full reward in the five shared-input merge detours. -/
def sharedMergeGain (c : RawDigits) (a : ℕ) : ℕ :=
  if 2 ≤ c a then
    match a with
    | 0 => c 0 - 1
    | 1 => 2 * c 1 + c 0 - 2
    | i + 2 => 2 * c (i + 1) + 2 * c (i + 2) - 2
  else if a = 0 then 0 else 1

set_option maxHeartbeats 1200000 in
/-- A merge sharing either input with an enabled split has a legal split-first
detour to its exact endpoint, with the full nonnegative reward gain. Spectator
multiplicities are unrestricted. The replacement tail need not be greedy. -/
theorem shared_input_merge_repair {c d : RawDigits} {a : ℕ}
    (merge : RawMove (.merge a) c d) (shared : 2 ≤ c a ∨ 2 ≤ c (a + 1)) :
    ∃ c' w, SplitStep (if 2 ≤ c a then a else a + 1) c c' ∧ RawPath c' d w ∧
      rawReward c (.merge a) + sharedMergeGain c a =
        splitReward c (if 2 ≤ c a then a else a + 1) + w := by
  classical
  let fire (x : RawDigits) (b : Action) := x - rawInput b + rawOutput b
  have legal (x : RawDigits) (b : Action) (notSwitch : b ≠ .switch)
      (enabled : rawInput b ≤ x) : RawMove b x (fire x b) := by
    let r := x - rawInput b
    have hr : r + rawInput b = x := tsub_add_cancel_of_le enabled
    refine ⟨?_, r, hr.symm, rfl, notSwitch⟩
    change CarryStep x (r + rawOutput b)
    rw [← hr]
    change CarryStep (r + rawInput b) (r + rawOutput b)
    cases b with
    | switch => exact (notSwitch rfl).elim
    | ones => exact CarryStep.double_zero r
    | twos => simpa [rawInput, rawOutput, splitOutput, add_assoc] using CarryStep.double_one r
    | split i => simpa [rawInput, rawOutput, splitOutput, add_assoc] using CarryStep.double_succ r i
    | merge i => simpa [rawInput, rawOutput, add_assoc] using CarryStep.adjacent r i
  have first (x : RawDigits) (j : ℕ) (enabled : 2 ≤ x j) :
      SplitStep j x (fire x (splitAction j)) := by
    refine ⟨x - Finsupp.single j 2,
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr enabled)).symm, ?_⟩
    rcases j with _ | _ | j <;> rfl
  obtain ⟨_, r, hc, hd, _⟩ := merge
  have positive : 0 < c a ∧ 0 < c (a + 1) := by simp [hc, rawInput]
  have endpoint : ∀ k, d k =
      c k - (rawInput (.merge a)) k + (rawOutput (.merge a)) k := by
    intro k
    simp [hc, hd]
  by_cases lower : 2 ≤ c a
  · rcases a with _ | _ | i
    · let u := fire c .ones
      have next : RawMove .twos u (fire u .twos) := legal u .twos (by simp) (by
        intro k
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have same : fire u .twos = d := by
        ext k
        rw [endpoint]
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega
      refine ⟨u, rawReward u .twos + 0, ?_, same ▸ .cons next (.nil _), ?_⟩
      · simpa [lower, u, splitAction] using first c 0 lower
      · simp [lower, sharedMergeGain, rawReward, splitReward, u, fire,
          rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        omega
    · let u := fire c .twos
      let v := fire u (.split 0)
      have next : RawMove (.split 0) u v := legal u (.split 0) (by simp) (by
        intro k
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have last : RawMove .ones v (fire v .ones) := legal v .ones (by simp) (by
        intro k
        simp [v, u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have same : fire v .ones = d := by
        ext k
        rw [endpoint]
        simp [v, u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega
      refine ⟨u, rawReward u (.split 0) + (rawReward v .ones + 0), ?_,
        same ▸ .cons next (.cons last (.nil _)), ?_⟩
      · simpa [lower, u, splitAction] using first c 1 lower
      · simp [lower, sharedMergeGain, rawReward, splitReward, v, u, fire,
          rawInput, rawOutput, splitOutput, Finsupp.single_apply, Nat.add_assoc]
        simp only [Nat.add_assoc, Nat.reduceAdd] at lower positive
        omega
    · let u := fire c (.split i)
      let v := fire u (.split (i + 1))
      have next : RawMove (.split (i + 1)) u v := legal u (.split (i + 1)) (by simp) (by
        intro k
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have last : RawMove (.merge i) v (fire v (.merge i)) := legal v (.merge i) (by simp) (by
        intro k
        simp [v, u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have same : fire v (.merge i) = d := by
        ext k
        rw [endpoint]
        simp [v, u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega
      refine ⟨u, rawReward u (.split (i + 1)) + (rawReward v (.merge i) + 0), ?_,
        same ▸ .cons next (.cons last (.nil _)), ?_⟩
      · simpa [lower, u, splitAction] using first c (i + 2) lower
      · simp [lower, sharedMergeGain, rawReward, splitReward, v, u, fire,
          rawInput, rawOutput, splitOutput, Finsupp.single_apply, Nat.add_assoc]
        simp only [Nat.add_assoc, Nat.reduceAdd] at lower positive
        omega
  · have upper : 2 ≤ c (a + 1) := shared.resolve_left lower
    rcases a with _ | i
    · let u := fire c .twos
      have next : RawMove .ones u (fire u .ones) := legal u .ones (by simp) (by
        intro k
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have same : fire u .ones = d := by
        ext k
        rw [endpoint]
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega
      refine ⟨u, rawReward u .ones + 0, ?_, same ▸ .cons next (.nil _), ?_⟩
      · simpa [lower, u, splitAction] using first c 1 upper
      · simp [lower, sharedMergeGain, rawReward, splitReward, u, fire,
          rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        simp only [Nat.add_assoc, Nat.reduceAdd] at lower positive upper
        omega
    · let u := fire c (.split i)
      have next : RawMove (.merge i) u (fire u (.merge i)) := legal u (.merge i) (by simp) (by
        intro k
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega)
      have same : fire u (.merge i) = d := by
        ext k
        rw [endpoint]
        simp [u, fire, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
        split_ifs <;> simp_all <;> omega
      refine ⟨u, rawReward u (.merge i) + 0, ?_, same ▸ .cons next (.nil _), ?_⟩
      · simpa [lower, u, splitAction] using first c (i + 2) upper
      · simp [lower, sharedMergeGain, rawReward, splitReward, u, fire,
          rawInput, rawOutput, splitOutput, Finsupp.single_apply, Nat.add_assoc]
        simp only [Nat.add_assoc, Nat.reduceAdd] at lower positive upper
        omega

/-- Combining ones can be promoted ahead of an arbitrary terminal raw path,
including arbitrary interleaved merges, without decreasing full reward. -/
theorem ones_terminal_promotion {c c' e : RawDigits} {w : ℕ}
    (path : RawPath c e w) (complete : CanonicalRaw e) (first : SplitStep 0 c c') :
    ∃ w', RawPath c' e w' ∧ w ≤ splitReward c 0 + w' := by
  classical
  have unique {x y z : RawDigits} {j : ℕ}
      (p : SplitStep j x y) (q : SplitStep j x z) : y = z := by
    obtain ⟨r, hr, rfl⟩ := p
    obtain ⟨s, hs, rfl⟩ := q
    rw [show r = s from add_right_cancel (hr.symm.trans hs)]
  have splitRaw {x y : RawDigits} {j : ℕ} (step : SplitStep j x y) :
      RawMove (splitAction j) x y := by
    obtain ⟨r, rfl, rfl⟩ := step
    refine ⟨?_, r, ?_, ?_, ?_⟩
    · rcases j with _ | _ | j
      · exact CarryStep.double_zero r
      · simpa [splitOutput, add_assoc] using CarryStep.double_one r
      · simpa [splitOutput, add_assoc] using CarryStep.double_succ r j
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> rfl
    · rcases j with _ | _ | j <;> simp [splitAction]
  have join {x y z : RawDigits} {v u : ℕ} (p : RawPath x y v) (q : RawPath y z u) :
      RawPath x z (v + u) := by
    induction p with
    | nil => simpa using q
    | cons step tail ih => simpa [Nat.add_assoc] using RawPath.cons step (ih q)
  induction path generalizing c' with
  | nil c =>
    obtain ⟨r, eq, _⟩ := first
    have h := complete.1 0
    simp [eq] at h
  | @cons a c d e w move tail ih =>
    have enabled : 2 ≤ c 0 := by obtain ⟨r, rfl, _⟩ := first; simp
    have splitCase (j : ℕ) (nonzero : j ≠ 0) (eq : a = splitAction j) :
        ∃ w', RawPath c' e w' ∧ rawReward c a + w ≤ splitReward c 0 + w' := by
      subst a
      have step : SplitStep j c d := by
        obtain ⟨_, r, hc, hd, _⟩ := move
        refine ⟨r, ?_, ?_⟩ <;> rcases j with _ | _ | j <;> assumption
      obtain ⟨x, y, v, hx, hy, replay, gain⟩ :=
        split_prefix_promotion (WeightedSplitPath.cons step (.nil d)) enabled
          (by intro k hk; simp only [List.mem_singleton] at hk; subst k
              exact ⟨nonzero, Or.inl rfl⟩)
      have same := unique hx first
      subst x
      obtain ⟨u, rest, bound⟩ := ih complete hy
      cases replay with
      | cons across empty =>
        cases empty
        have reward_eq (x : RawDigits) : rawReward x (splitAction j) = splitReward x j := by
          rcases j with _ | _ | j <;> rfl
        refine ⟨_, .cons (splitRaw across) rest, ?_⟩
        rw [reward_eq, reward_eq]
        omega
    cases a with
    | switch => exact (move.2.choose_spec.2.2 rfl).elim
    | ones =>
      have step : SplitStep 0 c d := by
        obtain ⟨_, r, hc, hd, _⟩ := move
        exact ⟨r, hc, hd⟩
      have same := unique step first
      subst d
      exact ⟨w, tail, le_rfl⟩
    | twos => exact splitCase 1 (by omega) rfl
    | split i => exact splitCase (i + 2) (by omega) rfl
    | merge a =>
      cases a with
      | zero =>
        obtain ⟨x, v, hx, repair, gain⟩ := shared_input_merge_repair move (Or.inl enabled)
        simp only [if_pos enabled] at hx gain
        have same := unique hx first
        subst x
        exact ⟨v + w, join repair tail, by omega⟩
      | succ a =>
        obtain ⟨_, r, hc, hd, _⟩ := move
        have hr : 2 ≤ r 0 := by simpa [hc, rawInput, Finsupp.single_apply] using enabled
        let t := r - Finsupp.single 0 2
        have ht : t + Finsupp.single 0 2 = r :=
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hr)
        let y := t + rawOutput (.merge (a + 1)) + splitOutput 0
        have hy : SplitStep 0 d y := by
          refine ⟨t + rawOutput (.merge (a + 1)), ?_, rfl⟩
          rw [hd, ← ht]; ac_rfl
        have cx : c' = t + rawInput (.merge (a + 1)) + splitOutput 0 := by
          apply unique first
          refine ⟨t + rawInput (.merge (a + 1)), ?_, rfl⟩
          rw [hc, ← ht]; ac_rfl
        have across : RawMove (.merge (a + 1)) c' y := by
          rw [cx]
          refine ⟨?_, t + splitOutput 0, by ac_rfl, by dsimp [y]; ac_rfl, by simp⟩
          simpa [y, rawInput, rawOutput, add_assoc, add_left_comm, add_comm] using
            CarryStep.adjacent (t + splitOutput 0) (a + 1)
        obtain ⟨u, rest, bound⟩ := ih complete hy
        have gain : rawReward c (.merge (a + 1)) + splitReward d 0 =
            splitReward c 0 + rawReward c' (.merge (a + 1)) := by
          rw [hc, hd, cx, ← ht]
          simp [rawReward, splitReward, rawInput, rawOutput, splitOutput, Finsupp.single_apply]
          omega
        exact ⟨_, .cons across rest, by omega⟩

/-- Erasing all ordered switches preserves the complete accumulated reward
and maps every remaining move to a labelled instance of the existing carries. -/
theorem path_raw_erasure {s t : List ℕ} {length weight : ℕ}
    (path : Path s t length weight) : RawPath (rawCounts s) (rawCounts t) weight := by
  classical
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
    rcases erase_move step with ⟨rfl, same⟩ | carry
    · simpa [reward, same] using ih
    · have h := RawPath.cons carry ih
      convert h using 1
      cases step <;> rfl

/-- A natural-number telescope bounds every legal ordered path, including
arbitrary switch choices, by its raw carry reward and initial inversions. -/
theorem path_potential {s t : List ℕ} {length weight : ℕ}
    (path : Path s t length weight) :
    length + inv (decode t) ≤ inv (decode s) + weight := by
  have local_bound {position a s t} (step : Move position a s t) :
      1 + inv (decode t) ≤ inv (decode s) + reward s a := by
    have counts (l : List ℕ) (k : ℕ) :
        (l.map Nat.succ).count (k + 1) = l.count k :=
      List.count_map_of_injective l Nat.succ Nat.succ_injective k
    cases step with
    | switch P S i j h =>
      simp only [decode, List.map_append, List.map_cons, List.map_nil, reward]
      rw [inv_window, inv_window]
      simp [inv, show ¬i + 1 < j + 1 by omega, show j + 1 < i + 1 by omega]
      omega
    | ones P S =>
      have h := inv_replace_ones (decode P) (decode S)
      simp only [decode, ← List.map_append] at h
      rw [show 1 = 0 + 1 from rfl, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | twos P S =>
      have h := inv_replace_twos (decode P) (decode S)
      simp only [decode, ← List.map_append] at h
      rw [show 2 = 1 + 1 from rfl, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | split P S i =>
      have h := inv_replace_double (decode P) (decode S) (i + 3) (by omega)
      simp only [decode, ← List.map_append] at h
      rw [show i + 3 - 2 = i + 1 by omega,
        show i + 3 - 1 = (i + 1) + 1 by omega,
        show i + 3 = (i + 2) + 1 by omega, counts, counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
    | merge P S a =>
      have h := inv_replace_adjacent (decode P) (decode S) (a + 1)
      simp only [decode, ← List.map_append] at h
      rw [counts] at h
      simpa [decode, reward, rawCounts, Multiset.toFinsupp_apply,
        List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left h 1
  induction path with
  | nil => simp
  | cons step tail ih => have := local_bound step; omega

/-- Strategy priorities are restarted at each state. -/
def priority : Action → ℕ
  | .switch => 0
  | .ones => 1
  | .twos | .split _ => 2
  | .merge _ => 3

/-- All switches tie; ones and merges choose the leftmost position, splits
choose the rightmost position. No order is imposed on switch choices. -/
def Preferred (p : ℕ) (a : Action) (q : ℕ) (b : Action) : Prop :=
  priority a < priority b ∨
    (priority a = priority b ∧
      (((priority a = 1 ∨ priority a = 3) ∧ p < q) ∨
        (priority a = 2 ∧ q < p)))

/-- Actual legal moves satisfying the complete relational LGS priority. -/
def LGSMove (p : ℕ) (a : Action) (s t : List ℕ) : Prop :=
  Move p a s t ∧ ∀ q b u, Move q b s u → ¬Preferred q b p a

/-- Every permitted switch choice is retained in the complete strategy relation. -/
inductive LGSPath : List ℕ → List ℕ → ℕ → ℕ → Prop where
  | nil (s) : LGSPath s s 0 0
  | cons {p a s t u length weight} (move : LGSMove p a s t)
      (tail : LGSPath t u length weight) :
      LGSPath s u (length + 1) (reward s a + weight)

/-- No legal ordered operation is enabled. -/
def Terminal (s : List ℕ) : Prop := ∀ p a t, ¬Move p a s t

/-- The full source target, including nonvacuous completion. This definition
records an unproved proposition, not a resolution of the conjecture. -/
def Conjecture17 : Prop :=
  (∀ n, 0 < n → ∃ t length weight,
    LGSPath (List.replicate n 0) t length weight ∧ Terminal t) ∧
  (∀ n, 0 < n → ∀ g gl gw h hl hw,
    LGSPath (List.replicate n 0) g gl gw → Terminal g →
    Path (List.replicate n 0) h hl hw → Terminal h → hl ≤ gl)

end D5.S1.Digit.Carry.OrderedGame
