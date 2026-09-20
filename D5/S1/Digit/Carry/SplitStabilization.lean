/- GID: D5/S1/Digit/Carry/SplitStabilization
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/SplitStabilization
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Legal split phases have a least-action bound and unique firing counts and endpoint. -/

import D5.S1.Digit.Normalize

namespace D5.S1.Digit.Carry

/-- Outputs of a split at a zero-based W index, including combining ones. -/
noncomputable def splitOutput : ℕ → RawDigits
  | 0 => Finsupp.single 1 1
  | 1 => Finsupp.single 0 1 + Finsupp.single 2 1
  | i + 2 => Finsupp.single i 1 + Finsupp.single (i + 3) 1

/-- A labelled legal split; the residual digits include all spectators. -/
def SplitStep (i : ℕ) (c d : RawDigits) : Prop :=
  ∃ rest, c = rest + Finsupp.single i 2 ∧ d = rest + splitOutput i

/-- An actual finite legal split phase, retaining its chronological indices. -/
inductive SplitPath : RawDigits → RawDigits → List ℕ → Prop where
  | nil (c) : SplitPath c c []
  | snoc {c d e indices} (path : SplitPath c d indices) {i}
      (step : SplitStep i d e) : SplitPath c e (indices ++ [i])

/-- Tokens received at a site from a firing-count function. -/
def splitIncoming (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 1 + u 2
  | 1 => u 0 + u 3
  | j + 2 => u (j + 1) + u (j + 4)

/-- Exact sitewise accounting for every legal split sequence. -/
theorem split_path_balance {c d : RawDigits} {indices : List ℕ}
    (path : SplitPath c d indices) (j : ℕ) :
    d j + 2 * indices.count j =
      c j + splitIncoming (fun k => indices.count k) j := by
  induction path with
  | nil => cases j with
    | zero => simp [splitIncoming]
    | succ j => cases j <;> simp [splitIncoming]
  | @snoc d e indices path i step ih =>
    obtain ⟨rest, rfl, rfl⟩ := step
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
      simp [splitOutput, splitIncoming, List.count_append,
        List.count_singleton, Finsupp.single_apply, beq_iff_eq] at ih ⊢ <;>
      (try split_ifs at ih ⊢) <;> omega

/-- No legal phase overfires a stabilizing phase. Complete phases therefore
have identical firing counts and identical endpoints, irrespective of order. -/
theorem split_stabilization {c d e : RawDigits} {xs ys : List ℕ}
    (p : SplitPath c d xs) (q : SplitPath c e ys) (stable : ∀ j, e j ≤ 1) :
    (∀ j, xs.count j ≤ ys.count j) ∧
      ((∀ j, d j ≤ 1) → (∀ j, xs.count j = ys.count j) ∧ d = e) := by
  have bound : ∀ {a b z : RawDigits} {us vs : List ℕ},
      SplitPath a b us → SplitPath a z vs → (∀ j, z j ≤ 1) →
      ∀ j, us.count j ≤ vs.count j := by
    intro a b z us vs hp hq hz
    induction hp with
    | nil => simp
    | @snoc b d us hp i hs ih =>
      have strict : us.count i < vs.count i := by
        by_contra hn
        have same : us.count i = vs.count i := by have := ih i; omega
        have incoming : splitIncoming (fun k => us.count k) i ≤
            splitIncoming (fun k => vs.count k) i := by
          rcases i with _ | _ | i
          · exact Nat.add_le_add (ih 1) (ih 2)
          · exact Nat.add_le_add (ih 0) (ih 3)
          · exact Nat.add_le_add (ih (i + 1)) (ih (i + 4))
        have before := split_path_balance hp i
        have after := split_path_balance hq i
        have stable_i := hz i
        obtain ⟨rest, heq, _⟩ := hs
        have enabled : 2 ≤ b i := by simp [heq]
        omega
      intro j
      have hj := ih j
      by_cases hji : j = i
      · subst j; simpa using Nat.succ_le_of_lt strict
      · simp [List.count_append, Ne.symm hji]
        exact hj
  refine ⟨bound p q stable, ?_⟩
  intro hd
  have counts : ∀ j, xs.count j = ys.count j :=
    fun j => Nat.le_antisymm (bound p q stable j) (bound q p hd j)
  refine ⟨counts, ?_⟩
  ext j
  have hp := split_path_balance p j
  have hq := split_path_balance q j
  have hf : (fun k => xs.count k) = (fun k => ys.count k) := funext counts
  rw [hf, counts j] at hp
  omega

/-- Given a legal prefix, a complete split phase exists from the same start,
by recursion at the prefix endpoint using the strict carry measure. -/
theorem exists_split_stabilization (start c : RawDigits) (xs : List ℕ)
    (preceding : SplitPath start c xs) :
    ∃ d ys, SplitPath start d ys ∧ (∀ j, d j ≤ 1) := by
  classical
  by_cases stable : ∀ j, c j ≤ 1
  · exact ⟨c, xs, preceding, stable⟩
  push Not at stable
  obtain ⟨i, hi⟩ := stable
  let rest := c - Finsupp.single i 2
  have hr : rest + Finsupp.single i 2 = c :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (by omega))
  let next := rest + splitOutput i
  have step : SplitStep i c next := ⟨rest, hr.symm, rfl⟩
  have carry : CarryStep c next := by
    rw [← hr]
    rcases i with _ | _ | i
    · exact CarryStep.double_zero rest
    · simpa [next, splitOutput, add_assoc] using CarryStep.double_one rest
    · simpa [next, splitOutput, add_assoc] using CarryStep.double_succ rest i
  exact exists_split_stabilization start next (xs ++ [i]) (.snoc preceding step)
termination_by (tokenCount c, indexWeight c)
decreasing_by exact carryStep_measure_decreases carry

/-- Full carry-then-sort reward of a split at a raw index. -/
def splitReward (c : RawDigits) : ℕ → ℕ
  | 0 => c 0 - 1
  | 1 => c 1 - 1
  | i + 2 => c (i + 1) + c (i + 2) - 1

/-- Weighted legal split paths retain their chronological indices. -/
inductive WeightedSplitPath : RawDigits → RawDigits → List ℕ → ℕ → Prop where
  | nil (c) : WeightedSplitPath c c [] 0
  | cons {c d e xs w i} (step : SplitStep i c d)
      (tail : WeightedSplitPath d e xs w) :
      WeightedSplitPath c e (i :: xs) (splitReward c i + w)

/-- An enabled preferred split can cross an arbitrary finite prefix of lower
splits without losing reward. Combining ones can cross every other split.
The replay is only asserted to be legal, not to obey greedy priorities. -/
theorem split_prefix_promotion {c d : RawDigits} {xs : List ℕ} {w j : ℕ}
    (path : WeightedSplitPath c d xs w) (enabled : 2 ≤ c j)
    (order : ∀ i ∈ xs, i ≠ j ∧ (j = 0 ∨ i < j)) :
    ∃ c' d' w', SplitStep j c c' ∧ SplitStep j d d' ∧
      WeightedSplitPath c' d' xs w' ∧
      w + splitReward d j ≤ splitReward c j + w' := by
  classical
  induction path with
  | nil c =>
    let r := c - Finsupp.single j 2
    have hr : r + Finsupp.single j 2 = c :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr enabled)
    exact ⟨r + splitOutput j, r + splitOutput j, 0,
      ⟨r, hr.symm, rfl⟩, ⟨r, hr.symm, rfl⟩, .nil _, by omega⟩
  | @cons c d e xs w i step tail ih =>
    obtain ⟨hne, hij⟩ := order i (by simp)
    obtain ⟨r, rfl, rfl⟩ := step
    have hrj : 2 ≤ r j := by simpa [Finsupp.single_apply, Ne.symm hne] using enabled
    let t := r - Finsupp.single j 2
    have ht : t + Finsupp.single j 2 = r :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hrj)
    have next_enabled : 2 ≤ (r + splitOutput i) j := by simp only [Finsupp.add_apply]; omega
    obtain ⟨d', e', w', hd', he', replay, gain⟩ :=
      ih next_enabled (fun k hk => order k (by simp [hk]))
    have d'_eq : d' = t + splitOutput i + splitOutput j := by
      obtain ⟨u, hu, rfl⟩ := hd'
      have hu' : u = t + splitOutput i := by
        apply add_right_cancel (b := Finsupp.single j 2)
        rw [← hu, ← ht]
        ac_rfl
      rw [hu']
    let c' := t + Finsupp.single i 2 + splitOutput j
    have first : SplitStep j (r + Finsupp.single i 2) c' := by
      refine ⟨t + Finsupp.single i 2, ?_, rfl⟩
      rw [← ht]; ac_rfl
    have across : SplitStep i c' d' := by
      refine ⟨t + splitOutput j, ?_, ?_⟩
      · dsimp [c']; ac_rfl
      · rw [d'_eq]; ac_rfl
    have local_gain :
        splitReward (r + Finsupp.single i 2) i + splitReward (r + splitOutput i) j ≤
          splitReward (r + Finsupp.single i 2) j + splitReward c' i := by
      rw [← ht]
      dsimp [c']
      clear * - hne hij
      rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
        simp [splitReward, splitOutput, Finsupp.single_apply] <;>
        (try split_ifs) <;> omega
    refine ⟨c', e', splitReward c' i + w', first, he', .cons across replay, ?_⟩
    omega

/-- Every complete split phase admits the currently preferred split first,
with the same endpoint and at least the original full reward. The maximal
index condition is re-evaluated at the state where this theorem is applied. -/
theorem split_phase_promotion {c c' d : RawDigits} {xs : List ℕ} {w j : ℕ}
    (path : WeightedSplitPath c d xs w) (first : SplitStep j c c')
    (highest : j = 0 ∨ ∀ k, j < k → c k ≤ 1) (stable : ∀ k, d k ≤ 1) :
    ∃ ys w', WeightedSplitPath c' d ys w' ∧ w ≤ splitReward c j + w' := by
  classical
  have erase {a b : RawDigits} {zs : List ℕ} {v : ℕ}
      (p : WeightedSplitPath a b zs v) :
      ∀ {s us}, SplitPath s a us → SplitPath s b (us ++ zs) := by
    induction p with
    | nil => intro s us pre; simpa using pre
    | @cons a b e zs v i step tail ih =>
      intro s us pre
      simpa [List.append_assoc] using ih (.snoc pre step)
  have once : SplitPath c c' [j] := by simpa using SplitPath.snoc (.nil c) first
  have bound := (split_stabilization once (by simpa using erase path (.nil c)) stable).1 j
  have occurs : j ∈ xs := by
    have positive : 0 < xs.count j := by simpa using bound
    exact List.count_pos_iff.mp positive
  have extract {a b : RawDigits} {zs : List ℕ} {v : ℕ}
      (p : WeightedSplitPath a b zs v) :
      ∀ {a' j}, SplitStep j a a' →
        (j = 0 ∨ ∀ k, j < k → a k ≤ 1) → j ∈ zs →
        ∃ us v', WeightedSplitPath a' b us v' ∧ v ≤ splitReward a j + v' := by
    induction p with
    | nil => simp
    | @cons a b e zs v i step tail ih =>
      intro a' j hj high mem
      have enabled : 2 ≤ a j := by obtain ⟨r, rfl, _⟩ := hj; simp
      by_cases same : i = j
      · subst i
        have eq : b = a' := by
          obtain ⟨r, hr, rfl⟩ := step
          obtain ⟨s, hs, rfl⟩ := hj
          have : r = s := add_right_cancel (hr.symm.trans hs)
          rw [this]
        subst a'
        exact ⟨zs, v, tail, le_rfl⟩
      have ord : j = 0 ∨ i < j := by
        rcases high with h | h
        · exact Or.inl h
        · right
          have eni : 2 ≤ a i := by obtain ⟨r, rfl, _⟩ := step; simp
          by_contra hn
          have := h i (by omega)
          omega
      have high' : j = 0 ∨ ∀ k, j < k → b k ≤ 1 := by
        rcases high with h | h
        · exact Or.inl h
        · by_cases hj0 : j = 0
          · exact Or.inl hj0
          right
          intro k hk
          have hik : i < j := ord.resolve_left hj0
          have old := h k hk
          obtain ⟨r, rfl, rfl⟩ := step
          rcases i with _ | _ | i <;>
            simp [splitOutput, Finsupp.single_apply] at old ⊢ <;>
            (try split_ifs at old ⊢) <;> omega
      obtain ⟨a₀, b₀, u, ha₀, hb₀, cross, gain⟩ :=
        split_prefix_promotion (.cons step (.nil b)) enabled
          (by intro k hk; simp only [List.mem_singleton] at hk; subst k; exact ⟨same, ord⟩)
      have eq : a₀ = a' := by
        obtain ⟨r, hr, rfl⟩ := ha₀
        obtain ⟨s, hs, rfl⟩ := hj
        have : r = s := add_right_cancel (hr.symm.trans hs)
        rw [this]
      subst a₀
      obtain ⟨us, v', rest, hrest⟩ := ih hb₀ high' (by simpa [Ne.symm same] using mem)
      cases cross with
      | cons si empty =>
        cases empty
        exact ⟨i :: us, _, .cons si rest, by omega⟩
  exact extract path first highest occurs

/-- The split part of LGS, recomputing ones priority and the highest duplicate
after every split. It does not specify a choice of ordered switches. -/
inductive GreedySplitPath : RawDigits → RawDigits → ℕ → Prop where
  | nil (c) : GreedySplitPath c c 0
  | cons {c d e j w} (step : SplitStep j c d)
      (preferred : j = 0 ∨ (c 0 ≤ 1 ∧ ∀ k, j < k → c k ≤ 1))
      (tail : GreedySplitPath d e w) :
      GreedySplitPath c e (splitReward c j + w)

/-- Among all complete split phases from an arbitrary raw state, every
complete greedy phase maximizes full carry-then-sort reward. This statement
allows adjacent occupied digits at the endpoints and does not compare merges. -/
theorem greedy_split_optimality {c e : RawDigits} {g : ℕ}
    (greedy : GreedySplitPath c e g) (complete : ∀ k, e k ≤ 1)
    {d : RawDigits} {xs : List ℕ} {w : ℕ}
    (path : WeightedSplitPath c d xs w) (stable : ∀ k, d k ≤ 1) : w ≤ g := by
  induction greedy generalizing d xs w with
  | nil c =>
    cases path with
    | nil => exact le_refl 0
    | @cons _ b _ xs w i step tail =>
      have h := complete i
      obtain ⟨r, eq, _⟩ := step
      have : 2 ≤ c i := by simp [eq]
      omega
  | cons step preferred tail ih =>
    obtain ⟨ys, w', replay, gain⟩ := split_phase_promotion path step
      (preferred.imp_right And.right) stable
    have := ih complete replay stable
    omega

end D5.S1.Digit.Carry
