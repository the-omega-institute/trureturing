/- GID: D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All-odd finite subtraction games have nonconvergent winning probabilities. -/

/-
result: proof_shape: content; escape_witness: d_nonneg (strong induction through changing legal-move cardinalities)
admission_basis: open-problem-resolution (#19195; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19292
winProb_eq: proof_shape: bind-only; escape_witness: none; consumers: winProb_bounds, b_initial, b_recurrence, d_initial.
legal_spec: proof_shape: bind-only; escape_witness: none; consumers: winProb_bounds, b_zero, b_recurrence, legal_succ_of_not_mem, next_not_legal, d_flat, d_threshold, d_initial, d_nonneg, d_seed.
winProb_bounds: proof_shape: content; escape_witness: winProb_bounds (strong-induction probability bound); consumers: b_bounds.
sign_sub: proof_shape: bind-only; escape_witness: none; consumers: b_recurrence.
b_bounds: proof_shape: content; escape_witness: winProb_bounds (strong-induction probability bound); consumers: d_nonneg.
b_initial: proof_shape: bind-only; escape_witness: none; consumers: b_zero, d_initial.
b_zero: proof_shape: bind-only; escape_witness: none; consumers: d_threshold.
b_recurrence: proof_shape: bind-only; escape_witness: none; consumers: d_flat, d_threshold.
legal_succ_of_not_mem: proof_shape: bind-only; escape_witness: none; consumers: d_flat, d_initial.
next_not_legal: proof_shape: bind-only; escape_witness: none; consumers: d_threshold.
legal_succ_of_mem: proof_shape: bind-only; escape_witness: none; consumers: d_threshold, d_initial.
d_flat: proof_shape: bind-only; escape_witness: none; consumers: d_nonneg, d_full.
d_threshold: proof_shape: bind-only; escape_witness: none; consumers: d_nonneg.
d_initial: proof_shape: bind-only; escape_witness: none; consumers: d_nonneg, d_seed.
d_nonneg: proof_shape: content; escape_witness: d_nonneg (strong induction through changing legal-move cardinalities); consumers: invariant_positive.
d_seed: proof_shape: bind-only; escape_witness: none; consumers: invariant_positive.
legal_full: proof_shape: bind-only; escape_witness: none; consumers: d_full.
d_full: proof_shape: bind-only; escape_witness: none; consumers: invariant_step.
window_step: proof_shape: bind-only; escape_witness: none; consumers: invariant_step.
invariant_step: proof_shape: bind-only; escape_witness: none; consumers: invariant_constant.
invariant_constant: proof_shape: bind-only; escape_witness: none; consumers: nonconvergence.
invariant_positive: proof_shape: content; escape_witness: d_nonneg (strong induction through changing legal-move cardinalities); consumers: nonconvergence.
d_difference: proof_shape: bind-only; escape_witness: none; consumers: d_tendsto_zero.
d_tendsto_zero: proof_shape: bind-only; escape_witness: none; consumers: nonconvergence.
invariant_tendsto_zero: proof_shape: bind-only; escape_witness: none; consumers: nonconvergence.
nonconvergence: proof_shape: content; escape_witness: d_nonneg (strong induction through changing legal-move cardinalities); consumers: result.
legalMoves: proof_shape: bind-only; escape_witness: none; consumers: winProb, claim, legal_spec.
winProb: proof_shape: bind-only; escape_witness: none; consumers: claim, winProb_eq, b.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
b: proof_shape: bind-only; escape_witness: none; consumers: d, b_bounds, b_recurrence.
d: proof_shape: bind-only; escape_witness: none; consumers: invariant, d_nonneg, d_difference.
invariant: proof_shape: bind-only; escape_witness: none; consumers: invariant_step, invariant_positive, nonconvergence.
The finite nonempty all-odd argument does not require the gcd hypothesis.
-/

import Mathlib.Topology.Instances.Real.Lemmas

/-! Binding conventions for N. Capitelli and F. Somma, "On sequences arising from randomizing subtraction games",
arXiv:2405.19593v1, Section 1 (the randomized subtraction game and `a_n^S`) and Section 3 (the all-odd nonconvergence
conjecture). -/

namespace D5.S3.Combinatorics.Games.CapitelliSommaAllOddNonconvergence

open Filter Topology

/-- The legal moves `A_n = {s ∈ S : 0 < s ≤ n}` from a pile of `n` chips. -/
def legalMoves (S : Finset ℕ) (n : ℕ) : Finset ℕ := S.filter fun s => 0 < s ∧ s ≤ n

/-- `a_n^S`: the probability that the next player to move wins from a pile of `n` chips when a legal subtraction is
chosen uniformly at random and a player who cannot move loses. Thus `a_n = 0` if there is no legal move, and
otherwise `a_n = 1 − (1/|A_n|) Σ_{s ∈ A_n} a_{n−s}`. -/
noncomputable def winProb (S : Finset ℕ) (n : ℕ) : ℝ :=
  if h : (legalMoves S n).Nonempty then
    1 - (∑ s ∈ (legalMoves S n).attach, winProb S (n - s.1)) / (legalMoves S n).card
  else 0
termination_by n
decreasing_by
  have hs := (Finset.mem_filter.mp s.2).2
  omega

/-- Section 3: for a finite subtraction set `S = {k_1, …, k_t}` of positive integers with `gcd = 1`, "we do not show
that an all-odd subtraction set necesarily do not converge (although we conjeture it)". -/
def claim : Prop :=
  ∀ S : Finset ℕ, S.Nonempty → (∀ s ∈ S, Odd s) → S.gcd id = 1 →
    ¬ ∃ L : ℝ, Tendsto (fun n => winProb S n) atTop (𝓝 L)

end D5.S3.Combinatorics.Games.CapitelliSommaAllOddNonconvergence

namespace D5.S3.Combinatorics.Games.CapitelliSommaAllOddNonconvergence
open Filter Topology
set_option maxHeartbeats 800000

private theorem winProb_eq (S : Finset ℕ) (n : ℕ) :
    winProb S n = if (legalMoves S n).Nonempty then
      1 - (∑ s ∈ legalMoves S n, winProb S (n-s)) / (legalMoves S n).card else 0 := by
  rw [winProb]
  split_ifs with h
  · have he := Finset.sum_attach (legalMoves S n) (fun s : ℕ => winProb S (n-s))
    rw [he]
  · rfl


private theorem legal_spec {S : Finset ℕ} {n s : ℕ} (hs : s ∈ legalMoves S n) :
    s ∈ S ∧ 0 < s ∧ s ≤ n := by
  exact Finset.mem_filter.mp hs

private theorem winProb_bounds (S : Finset ℕ) (n : ℕ) : 0 ≤ winProb S n ∧ winProb S n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [winProb_eq]
    split_ifs with hn
    · have hc : (0 : ℝ) < (legalMoves S n).card := by
        exact_mod_cast Finset.card_pos.mpr hn
      have hb : ∀ s ∈ legalMoves S n, 0 ≤ winProb S (n-s) ∧ winProb S (n-s) ≤ 1 := by
        intro s hs
        exact ih _ (by have := legal_spec hs; omega)
      have h0 : 0 ≤ ∑ s ∈ legalMoves S n, winProb S (n-s) :=
        Finset.sum_nonneg fun s hs => (hb s hs).1
      have h1 : (∑ s ∈ legalMoves S n, winProb S (n-s)) ≤ (legalMoves S n).card := by
        calc
          _ ≤ ∑ s ∈ legalMoves S n, (1 : ℝ) := Finset.sum_le_sum fun s hs => (hb s hs).2
          _ = _ := by simp
      constructor
      · have := (div_le_one hc).mpr h1
        linarith
      · have := div_nonneg h0 hc.le
        linarith
    · norm_num

private noncomputable def b (S : Finset ℕ) (n : ℕ) : ℝ := (-1)^n * (1 - 2 * winProb S n)
private noncomputable def d (S : Finset ℕ) (n : ℕ) : ℝ := b S n + b S (n+1)

private theorem sign_sub {n s : ℕ} (hs : s ≤ n) (ho : Odd s) :
    (-1 : ℝ)^(n-s) = -(-1 : ℝ)^n := by
  have he := congrArg (fun k : ℕ => (-1 : ℝ)^k) (Nat.sub_add_cancel hs)
  rw [pow_add, ho.neg_one_pow] at he
  linarith

private theorem b_bounds (S : Finset ℕ) (n : ℕ) : -1 ≤ b S n ∧ b S n ≤ 1 := by
  have ha := winProb_bounds S n
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [b, h] <;> constructor <;> nlinarith

private theorem b_initial {S : Finset ℕ} {n : ℕ} (hn : legalMoves S n = ∅) :
    b S n = (-1 : ℝ)^n := by
  simp [b, winProb_eq, hn]

private theorem b_zero (S : Finset ℕ) : b S 0 = 1 := by
  apply (b_initial (by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have := legal_spec hs
    omega)).trans
  simp

private theorem b_recurrence {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {n : ℕ}
    (hn : (legalMoves S n).Nonempty) :
    (legalMoves S n).card * b S n = ∑ s ∈ legalMoves S n, b S (n-s) := by
  have hc : (legalMoves S n).card ≠ (0 : ℝ) := by
    exact_mod_cast Finset.card_ne_zero.mpr hn
  have he : (∑ s ∈ legalMoves S n, b S (n-s)) =
      ∑ s ∈ legalMoves S n, -(-1 : ℝ)^n * (1 - 2 * winProb S (n-s)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [b, sign_sub (legal_spec hs).2.2 (ho s (legal_spec hs).1)]
  rw [he, b, winProb_eq, ite_eq_left hn]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  field_simp [hc]
  ring


private theorem legal_succ_of_not_mem (S : Finset ℕ) (n : ℕ) (hn : n+1 ∉ S) :
    legalMoves S (n+1) = legalMoves S n := by
  ext s
  simp only [legalMoves, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hp, hle⟩
    refine ⟨hs, hp, ?_⟩
    by_contra h
    have : s = n+1 := by omega
    exact hn (this ▸ hs)
  · rintro ⟨hs, hp, hle⟩
    exact ⟨hs, hp, by omega⟩

private theorem next_not_legal (S : Finset ℕ) (n : ℕ) : n+1 ∉ legalMoves S n := by
  intro hs
  have := legal_spec hs
  omega

private theorem legal_succ_of_mem (S : Finset ℕ) (n : ℕ) (hn : n+1 ∈ S) :
    legalMoves S (n+1) = insert (n+1) (legalMoves S n) := by
  ext s
  simp only [legalMoves, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hs, hp, hle⟩
    by_cases h : s = n+1
    · exact Or.inl h
    · exact Or.inr ⟨hs, hp, by omega⟩
  · rintro (rfl | ⟨hs, hp, hle⟩)
    · exact ⟨hn, by omega, le_rfl⟩
    · exact ⟨hs, hp, by omega⟩

private theorem d_flat {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {n : ℕ}
    (hn : (legalMoves S n).Nonempty) (ht : n+1 ∉ S) :
    (legalMoves S n).card * d S n = ∑ s ∈ legalMoves S n, d S (n-s) := by
  have he := legal_succ_of_not_mem S n ht
  have h0 := b_recurrence ho hn
  have h1 := b_recurrence ho (n := n+1) (he.symm ▸ hn)
  rw [he] at h1
  have hd : (∑ s ∈ legalMoves S n, d S (n-s)) =
      (∑ s ∈ legalMoves S n, b S (n-s)) + (∑ s ∈ legalMoves S n, b S (n+1-s)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [d, show n-s+1 = n+1-s by have := legal_spec hs; omega]
  rw [hd, d, mul_add, h0, h1]

private theorem d_threshold {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {n : ℕ}
    (hn : (legalMoves S n).Nonempty) (ht : n+1 ∈ S) :
    ((legalMoves S n).card + 1 : ℝ) * d S n =
      (∑ s ∈ legalMoves S n, d S (n-s)) + b S n + 1 := by
  have he := legal_succ_of_mem S n ht
  have h0 := b_recurrence ho hn
  have h1 := b_recurrence ho (n := n+1)
    (show (legalMoves S (n+1)).Nonempty by rw [he]; exact Finset.insert_nonempty ..)
  rw [he, Finset.card_insert_of_notMem (next_not_legal S n),
    Finset.sum_insert (next_not_legal S n), Nat.sub_self, b_zero] at h1
  push_cast at h1
  have hd : (∑ s ∈ legalMoves S n, d S (n-s)) =
      (∑ s ∈ legalMoves S n, b S (n-s)) + (∑ s ∈ legalMoves S n, b S (n+1-s)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [d, show n-s+1 = n+1-s by have := legal_spec hs; omega]
  rw [hd, d]
  nlinarith

private theorem d_initial {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {n : ℕ} (hn : legalMoves S n = ∅) :
    d S n = if n+1 ∈ S then 2 else 0 := by
  by_cases ht : n+1 ∈ S
  · rw [ite_eq_left ht, d, b_initial hn]
    have he := legal_succ_of_mem S n ht
    rw [hn] at he
    have hp : winProb S (n+1) = 1 := by
      rw [winProb_eq, he]
      have hz : legalMoves S 0 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        have := legal_spec hs
        omega
      have ha0 : winProb S 0 = 0 := by rw [winProb_eq, hz]; simp
      simp [ha0]
    have hs := (ho _ ht).neg_one_pow (α := ℝ)
    have hs0 : (-1 : ℝ)^n = 1 := by
      rw [pow_succ] at hs
      linarith
    rw [b, hp, hs, hs0]
    norm_num
  · rw [ite_eq_right ht, d, b_initial hn,
      b_initial (by rw [legal_succ_of_not_mem S n ht, hn])]
    simp [pow_succ]


private theorem d_nonneg {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) (n : ℕ) : 0 ≤ d S n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : (legalMoves S n).Nonempty
    · have hs : 0 ≤ ∑ s ∈ legalMoves S n, d S (n-s) := by
        apply Finset.sum_nonneg
        intro s hs
        exact ih _ (by have := legal_spec hs; omega)
      by_cases ht : n+1 ∈ S
      · have he := d_threshold ho hn ht
        have hb := (b_bounds S n).1
        have hc : (0 : ℝ) < (legalMoves S n).card + 1 := Nat.cast_add_one_pos _
        nlinarith
      · have he := d_flat ho hn ht
        have hc : (0 : ℝ) < (legalMoves S n).card := by
          exact_mod_cast Finset.card_pos.mpr hn
        nlinarith
    · rw [d_initial ho (Finset.not_nonempty_iff_eq_empty.mp hn)]
      split_ifs <;> norm_num

private theorem d_seed {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {m : ℕ}
    (hm : m ∈ S) (hmin : ∀ s ∈ S, m ≤ s) : d S (m-1) = 2 := by
  have hp : 0 < m := (ho m hm).pos
  have he : legalMoves S (m-1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hh := legal_spec hs
    have := hmin s hh.1
    omega
  rw [d_initial ho he, show m-1+1 = m by omega, ite_eq_left hm]

private theorem legal_full {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) {N : ℕ}
    (hN : ∀ s ∈ S, s ≤ N) : legalMoves S N = S := by
  apply Finset.filter_eq_self.mpr
  intro s hs
  exact ⟨(ho s hs).pos, hN s hs⟩

private theorem d_full {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) (hne : S.Nonempty) {N : ℕ}
    (hN : ∀ s ∈ S, s ≤ N) :
    (S.card : ℝ) * d S N = ∑ s ∈ S, d S (N-s) := by
  have he := legal_full ho hN
  have ht : N+1 ∉ S := by intro hs; have := hN _ hs; omega
  simpa only [he] using d_flat ho (he.symm ▸ hne) ht

private noncomputable def invariant (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ s ∈ S, ∑ r ∈ Finset.range s, d S (N-s+r)

private theorem window_step (f : ℕ → ℝ) {N s : ℕ} (hs : s ≤ N) :
    (∑ r ∈ Finset.range s, f (N+1-s+r)) -
      (∑ r ∈ Finset.range s, f (N-s+r)) = f N - f (N-s) := by
  rw [← Finset.sum_sub_distrib]
  have he : ∀ r, N+1-s+r = N-s+(r+1) := by intro r; omega
  simp_rw [he]
  have hh := Finset.sum_range_sub (fun r => f (N-s+r)) s
  simpa only [Nat.sub_add_cancel hs, Nat.add_zero] using hh

private theorem invariant_step {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) (hne : S.Nonempty) {N : ℕ}
    (hN : ∀ s ∈ S, s ≤ N) : invariant S (N+1) = invariant S N := by
  have hdiff : invariant S (N+1) - invariant S N =
      (S.card : ℝ) * d S N - ∑ s ∈ S, d S (N-s) := by
    unfold invariant
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ s ∈ S, (d S N - d S (N-s)) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact window_step (d S) (hN s hs)
      _ = _ := by simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  have := d_full ho hne hN
  linarith

private theorem invariant_constant {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) (hne : S.Nonempty) {M : ℕ}
    (hM : ∀ s ∈ S, s ≤ M) (n : ℕ) : invariant S (M+n) = invariant S M := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show M+(n+1) = (M+n)+1 by omega,
      invariant_step ho hne (fun s hs => (hM s hs).trans (by omega)), ih]

private theorem invariant_positive {S : Finset ℕ} (ho : ∀ s ∈ S, Odd s) (hne : S.Nonempty) :
    2 ≤ invariant S (S.max' hne) := by
  let m := S.min' hne
  let M := S.max' hne
  have hm : m ∈ S := S.min'_mem hne
  have hM : M ∈ S := S.max'_mem hne
  have hp : 0 < m := (ho m hm).pos
  have hle : m ≤ M := S.min'_le M hM
  have hseed : d S (m-1) = 2 := d_seed ho hm (fun s hs => S.min'_le s hs)
  have houter : (∑ r ∈ Finset.range M, d S (M-M+r)) ≤ invariant S M := by
    unfold invariant
    exact Finset.single_le_sum
      (f := fun s => ∑ r ∈ Finset.range s, d S (M-s+r))
      (fun s hs => Finset.sum_nonneg fun r hr => d_nonneg ho _) hM
  have hinner : d S (m-1) ≤ ∑ r ∈ Finset.range M, d S r := by
    apply Finset.single_le_sum
    · intro r hr
      exact d_nonneg ho _
    · exact Finset.mem_range.mpr (by omega)
  simp only [Nat.sub_self, Nat.zero_add] at houter
  exact hseed ▸ hinner.trans houter

private theorem d_difference (S : Finset ℕ) (n : ℕ) :
    d S n = (-1 : ℝ)^n * (2 * (winProb S (n+1) - winProb S n)) := by
  simp only [d, b, pow_succ]
  ring

private theorem d_tendsto_zero {S : Finset ℕ} {L : ℝ}
    (hL : Tendsto (winProb S) atTop (𝓝 L)) : Tendsto (d S) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 2 * (winProb S (n+1) - winProb S n)) atTop (𝓝 0) := by
    simpa using ((hL.comp (tendsto_add_atTop_nat 1)).sub hL).const_mul 2
  have hb : ∀ᶠ n in atTop, |(-1 : ℝ)^n| ≤ 1 := by
    exact Filter.Eventually.of_forall fun n => (abs_neg_one_pow n).le
  simpa only [← d_difference] using bdd_le_mul_tendsto_zero' 1 hb hh

private theorem invariant_tendsto_zero {S : Finset ℕ}
    (hd : Tendsto (d S) atTop (𝓝 0)) : Tendsto (invariant S) atTop (𝓝 0) := by
  have hh : Tendsto (invariant S) atTop
      (𝓝 (∑ s ∈ S, ∑ r ∈ Finset.range s, (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro s hs
    apply tendsto_finsetSum
    intro r hr
    exact hd.comp ((tendsto_add_atTop_nat r).comp (tendsto_sub_atTop_nat s))
  simpa using hh

private theorem nonconvergence {S : Finset ℕ} (hne : S.Nonempty) (ho : ∀ s ∈ S, Odd s) :
    ¬ ∃ L : ℝ, Tendsto (winProb S) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hh := invariant_tendsto_zero (d_tendsto_zero hL)
  have hp := invariant_positive ho hne
  let M := S.max' hne
  have hc : ∀ n, invariant S (M+n) = invariant S M :=
    invariant_constant ho hne (fun s hs => S.le_max' s hs)
  have hz : Tendsto (fun _ : ℕ => invariant S M) atTop (𝓝 0) := by
    have hx := hh.comp (tendsto_add_atTop_nat M)
    have heq : (fun n => invariant S (n+M)) = (fun _ : ℕ => invariant S M) := by
      funext n
      rw [Nat.add_comm n M, hc]
    simpa only [Function.comp_def, heq] using hx
  have he : invariant S M = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  linarith

theorem result : claim := by
  intro S hne ho _
  exact nonconvergence hne ho


end D5.S3.Combinatorics.Games.CapitelliSommaAllOddNonconvergence
