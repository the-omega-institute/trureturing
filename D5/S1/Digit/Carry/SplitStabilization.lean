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

/-- Every finite raw state admits a complete split phase. More generally any
legal prefix extends to one, by the existing strict carry measure. -/
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

end D5.S1.Digit.Carry
