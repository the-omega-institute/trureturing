/- GID: D5/S3/Observer/LinearMemory/AcceptedWordEffectPropagation
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/AcceptedWordEffectPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Accepted partial runs generate all-state effect propagation and its rank-gap horizon. -/

import D5.S0.Automata.TypedPartialDFAO
import D5.S3.Observer.LinearMemory.FiniteWordReachability

/-! Accepted partial runs, effect propagation, and simultaneous stabilization. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation

open D5.S0.Automata.TypedPartialDFAO
open scoped BigOperators

universe u v w z
variable {K : Type u} {E : Type v} {Alphabet : Type w} {Q : Type z}
  [DivisionRing K] [AddCommGroup E] [Module K E] [DecidableEq Q]

/-- Acceptance reads only the terminal state of an actual, fully defined run. -/
def Accepts (M : BaseAutomaton Alphabet Q) (F : Finset Q) (q : Q) (word : List Alphabet) : Prop :=
  ∃ f ∈ F, M.runFrom q word = some f

/-- The independently defined span of accepted chronological word effects. -/
def acceptedSpan (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (n : ℕ) (q : Q) : Submodule K E :=
  Submodule.span K {x | ∃ word : List Alphabet, word.length ≤ n ∧ Accepts M F q word ∧
    ∃ t ∈ U, x = (word.map A).prod t}

/-- Every finite accepted word is allowed, with no horizon bound. -/
def fullFuture (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (q : Q) : Submodule K E :=
  Submodule.span K {x | ∃ word : List Alphabet, Accepts M F q word ∧
    ∃ t ∈ U, x = (word.map A).prod t}

/-- Only defined transitions contribute to the sum of image subspaces. -/
def effectStep (M : BaseAutomaton Alphabet Q) (A : Alphabet → Module.End K E)
    (S : Q → Submodule K E) (q : Q) : Submodule K E :=
  S q ⊔ ⨆ (a : Alphabet) (q' : Q) (_ : M.step q a = some q'), (S q').map (A a)

/-- The actual all-state recurrence, initialized at accepting terminals only. -/
def propagation (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) : ℕ → Q → Submodule K E
  | 0 => fun q => if q ∈ F then U else ⊥
  | n + 1 => effectStep M A (propagation M F A U n)

omit [DecidableEq Q] in
private theorem accepts_cons (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (q : Q) (a : Alphabet) (word : List Alphabet) :
    Accepts M F q (a :: word) ↔
      ∃ q', M.step q a = some q' ∧ Accepts M F q' word := by
  cases h : M.step q a with
  | none => simp [Accepts, BaseAutomaton.runFrom, h]
  | some q' => simp [Accepts, BaseAutomaton.runFrom, h]

private theorem accepted_zero (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (q : Q) :
    acceptedSpan M F A U 0 q = if q ∈ F then U else ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨word, hw, ha, t, ht, rfl⟩
    have he : word = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hw)
    subst word
    have hq : q ∈ F := by simpa [Accepts, BaseAutomaton.runFrom] using ha
    simpa [hq] using ht
  · split_ifs with hq
    · intro x hx
      exact Submodule.subset_span ⟨[], by simp,
        ⟨q, hq, rfl⟩, x, hx, by simp⟩
    · exact bot_le

omit [DecidableEq Q] in
private theorem accepted_succ (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (n : ℕ) :
    effectStep M A (acceptedSpan M F A U n) = acceptedSpan M F A U (n + 1) := by
  funext q
  unfold effectStep
  apply le_antisymm
  · refine sup_le (Submodule.span_mono ?_) (iSup_le fun a => iSup_le fun q' =>
        iSup_le fun hδ => ?_)
    · rintro x ⟨word, hw, ha, t, ht, rfl⟩
      exact ⟨word, hw.trans (Nat.le_succ n), ha, t, ht, rfl⟩
    · rw [acceptedSpan, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro x ⟨y, ⟨word, hw, ha, t, ht, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a :: word, by simpa using Nat.succ_le_succ hw,
        (accepts_cons M F q a word).mpr ⟨q', hδ, ha⟩,
        t, ht, by simp [Module.End.mul_apply]⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨word, hw, ha, t, ht, rfl⟩
    cases word with
    | nil =>
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], by simp, ha, t, ht, rfl⟩)
    | cons a word =>
        obtain ⟨q', hδ, ha'⟩ := (accepts_cons M F q a word).mp ha
        apply Submodule.mem_sup_right
        apply Submodule.mem_iSup_of_mem a
        apply Submodule.mem_iSup_of_mem q'
        apply Submodule.mem_iSup_of_mem hδ
        exact ⟨(word.map A).prod t,
          Submodule.subset_span ⟨word, by simpa using hw, ha', t, ht, rfl⟩,
          by simp [Module.End.mul_apply]⟩

/-- The recurrence is exactly the span of actual accepted chronological words
of length at most the horizon; absent transitions never produce an event. -/
theorem propagation_eq_accepted (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (n : ℕ) :
    propagation M F A U n = acceptedSpan M F A U n := by
  induction n with
  | zero => exact (funext (accepted_zero M F A U)).symm
  | succ n ih => rw [propagation, ih, accepted_succ]

private theorem propagation_mono (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) :
    Monotone (propagation M F A U) := by
  apply monotone_nat_of_le_succ
  intro n q
  exact le_sup_left

private theorem propagation_fixed (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) (n : ℕ)
    (h : propagation M F A U (n + 1) = propagation M F A U n) (m : ℕ) :
    propagation M F A U (n + m) = propagation M F A U n := by
  induction m with
  | zero => simp
  | succ m ih =>
      change effectStep M A (propagation M F A U (n + m)) = _
      rw [ih]
      exact h

/-- Simultaneous one-step equality persists. All states reach their full legal
future by `|Q| dim(E) - |F| dim(U)`, including empty and zero cases. -/
theorem simultaneous_stabilization [Fintype Q] [FiniteDimensional K E]
    (M : BaseAutomaton Alphabet Q) (F : Finset Q)
    (A : Alphabet → Module.End K E) (U : Submodule K E) :
    (∀ n, (∀ q, propagation M F A U (n + 1) q = propagation M F A U n q) →
      ∀ m q, propagation M F A U (n + m) q = propagation M F A U n q) ∧
    (let B := Fintype.card Q * Module.finrank K E - F.card * Module.finrank K U
     (∀ n, B ≤ n → propagation M F A U n = propagation M F A U B) ∧
       ∀ q, fullFuture M F A U q = propagation M F A U B q) := by
  classical
  let V := propagation M F A U
  have hmono : Monotone V := propagation_mono M F A U
  have hperm : ∀ n, V (n + 1) = V n → ∀ m, V (n + m) = V n :=
    propagation_fixed M F A U
  refine ⟨fun n h m q => congrFun (hperm n (funext h) m) q, ?_⟩
  let rankAt := fun n => ∑ q : Q, Module.finrank K (V n q)
  have hrmono : Monotone rankAt := by
    intro n m h
    exact Finset.sum_le_sum fun q _ => Submodule.finrank_mono (hmono h q)
  have hrbound : ∀ n, rankAt n ≤ Fintype.card Q * Module.finrank K E := by
    intro n
    calc
      rankAt n ≤ ∑ _q : Q, Module.finrank K E :=
        Finset.sum_le_sum fun q _ => Submodule.finrank_le (V n q)
      _ = _ := by simp
  have hrzero : rankAt 0 = F.card * Module.finrank K U := by
    change (∑ q : Q, Module.finrank K (V 0 q)) = _
    calc
      _ = ∑ q : Q, if q ∈ F then Module.finrank K U else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hq : q ∈ F
        · have hv : V 0 q = U := if_pos hq
          rw [hv, if_pos hq]
        · have hv : V 0 q = ⊥ := if_neg hq
          rw [hv, if_neg hq]
          simp
      _ = _ := by simp
  let B := Fintype.card Q * Module.finrank K E - F.card * Module.finrank K U
  obtain ⟨m, hm, he⟩ :=
    D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate.bounded_monotone_has_equal_step
      rankAt (Fintype.card Q * Module.finrank K E) hrmono hrbound
  have hmB : m ≤ B := by simpa only [hrzero] using hm
  have hcoord : ∀ q, Module.finrank K (V m q) = Module.finrank K (V (m + 1) q) := by
    exact fun q => (Finset.sum_eq_sum_iff_of_le
      (fun q _ => Submodule.finrank_mono (hmono (Nat.le_succ m) q))).mp he q
        (Finset.mem_univ q)
  have hflat : V (m + 1) = V m := by
    funext q
    exact (Submodule.eq_of_le_of_finrank_eq (hmono (Nat.le_succ m) q) (hcoord q)).symm
  have hstable : ∀ n, B ≤ n → V n = V B := by
    intro n hn
    have h1 := hperm m hflat (n - m)
    have h2 := hperm m hflat (B - m)
    rw [Nat.add_sub_of_le (hmB.trans hn)] at h1
    rw [Nat.add_sub_of_le hmB] at h2
    exact h1.trans h2.symm
  refine ⟨hstable, fun q => le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨word, ha, t, ht, rfl⟩
    have hx : (word.map A).prod t ∈ V word.length q := by
      rw [show V word.length = acceptedSpan M F A U word.length from
        propagation_eq_accepted M F A U word.length]
      exact Submodule.subset_span ⟨word, le_rfl, ha, t, ht, rfl⟩
    have hb := hmono (Nat.le_add_right word.length B) q hx
    rw [hstable (word.length + B) (Nat.le_add_left B word.length)] at hb
    exact hb
  · change V B q ≤ fullFuture M F A U q
    rw [show V B = acceptedSpan M F A U B from propagation_eq_accepted M F A U B]
    apply Submodule.span_mono
    rintro x ⟨word, _, ha, t, ht, rfl⟩
    exact ⟨word, ha, t, ht, rfl⟩

/-- A chain has only the successor edge, and no edge out of its terminal. -/
def chain (L : ℕ) : BaseAutomaton Unit (Fin (L + 1)) where
  start := ⟨0, by omega⟩
  step q _ := if h : q.val < L then some ⟨q.val + 1, by omega⟩ else none

/-- The sole accepting state of the chain. -/
def chainFinal (L : ℕ) : Finset (Fin (L + 1)) := {⟨L, by omega⟩}

private theorem chain_step (L : ℕ) (S : Fin (L + 1) → Submodule K E)
    (q : Fin (L + 1)) :
    effectStep (chain L) (fun _ => (1 : Module.End K E)) S q =
      if h : q.val < L then S q ⊔ S ⟨q.val + 1, by omega⟩ else S q := by
  classical
  unfold effectStep chain
  split_ifs with h
  · simp [h, show (1 : Module.End K E) = LinearMap.id by rfl]
  · simp [h]

private theorem chain_spaces (L : ℕ) (U : Submodule K E) (n : ℕ)
    (q : Fin (L + 1)) :
    propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U n q =
      if L ≤ q.val + n then U else ⊥ := by
  induction n generalizing q with
  | zero =>
      by_cases h : q.val = L
      · simp [propagation, chainFinal, Fin.ext_iff, h]
      · have hlt : q.val < L := by omega
        simp [propagation, chainFinal, Fin.ext_iff, h, Nat.not_le.mpr hlt]
  | succ n ih =>
      rw [propagation, chain_step]
      by_cases h : q.val < L
      · rw [dite_eq_left h, ih, ih]
        by_cases h1 : L ≤ q.val + n
        · simp [h1, show L ≤ q.val + 1 + n by omega, show L ≤ q.val + (n + 1) by omega]
        · by_cases h2 : L ≤ q.val + 1 + n
          · simp [h1, h2, show L ≤ q.val + (n + 1) by omega]
          · simp [h1, h2, show ¬ L ≤ q.val + (n + 1) by omega]
      · rw [dite_eq_right h, ih]
        simp [show L ≤ q.val + n by omega, show L ≤ q.val + (n + 1) by omega]

/-- The uniform identity-chain family has an arbitrarily delayed initial
effect: all earlier horizons are zero and the length-`L` horizon is `U`.
For `L ≥ 2` and nonzero `U`, a one-step initial-state plateau is followed by
a later strict change, despite the actual recurrence and acceptance filter. -/
theorem arbitrary_chain_delay (L : ℕ) (U : Submodule K E) :
    (∀ n q, propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U n q =
      if L ≤ q.val + n then U else ⊥) ∧
    (∀ n, n < L → propagation (chain L) (chainFinal L)
      (fun _ => (1 : Module.End K E)) U n (chain L).start = ⊥) ∧
    propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U L
      (chain L).start = U ∧
    (2 ≤ L → U ≠ ⊥ →
      propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 1
          (chain L).start =
        propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 0
          (chain L).start ∧
      propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U L
          (chain L).start ≠
        propagation (chain L) (chainFinal L) (fun _ => (1 : Module.End K E)) U 0
          (chain L).start) := by
  refine ⟨chain_spaces L U, ?_, ?_, ?_⟩
  · intro n hn
    rw [chain_spaces]
    simp [chain, Nat.not_le.mpr hn]
  · rw [chain_spaces]
    simp [chain]
  · intro hL hU
    rw [chain_spaces, chain_spaces, chain_spaces]
    change (if L ≤ 0 + 1 then U else ⊥) = (if L ≤ 0 + 0 then U else ⊥) ∧
      (if L ≤ 0 + L then U else ⊥) ≠ (if L ≤ 0 + 0 then U else ⊥)
    simp [show ¬ L ≤ 1 by omega, show ¬ L ≤ 0 by omega, hU]

#print axioms propagation_eq_accepted
#print axioms simultaneous_stabilization
#print axioms arbitrary_chain_delay

end D5.S3.Observer.LinearMemory.AcceptedWordEffectPropagation
