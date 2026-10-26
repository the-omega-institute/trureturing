/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-history consecutive-bit execution is the stopped gap prefix with exact paid time. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalTable

/-! Exact finite and infinite execution of one counted renewal table on one bit history. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical Finset
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths
open CriticalRenewalTable

/-- A finite block of fresh zero outcomes and its one closing-tick outcome.
    These are proof coordinates, not retained observer data. -/
structure Block where
  zeros : List Bool
  tick : Bool
  deriving Countable

def phaseAt (J : ℕ) (b : Block) : ℕ → Phase.T J
  | 0 => Phase.first J
  | k + 1 => Phase.step (phaseAt J b k) (b.zeros[k]?.getD false)

def increment {J : ℕ} (t : Tick J) (b : Block) : ℤ :=
  t.increment (phaseAt J b b.zeros.length) b.tick

def evidence {J : ℕ} (t : Tick J) (blocks : ℕ → Block) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, increment t (blocks k)

/-- The ordinary real partial sum of the marks on grid spacing delta. -/
def score {J : ℕ} (δ : ℝ) (t : Tick J) (blocks : ℕ → Block) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (increment t (blocks k) : ℝ) * δ

def inside (H : ℕ) (u : ℤ) : Prop := -(H : ℤ) < u ∧ u < H

def clock (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) : ℕ :=
  τ + 1 + ∑ k ∈ range n, ((blocks k).zeros.length + 1)

private lemma clock_succ (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) :
    clock τ blocks (n+1) = clock τ blocks n + (blocks n).zeros.length + 1 := by
  simp only [clock, sum_range_succ]
  omega

private lemma clock_strict (τ : ℕ) (blocks : ℕ → Block) : StrictMono (clock τ blocks) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [clock_succ]
  omega

private lemma clock_ge (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) : n ≤ clock τ blocks n := by
  induction n with
  | zero => omega
  | succ n ih => rw [clock_succ]; omega

private lemma clock_unbounded (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) :
    ∃ n, m < clock τ blocks (n+1) := ⟨m, by have := clock_ge τ blocks (m+1); omega⟩

/-- Locate proof coordinates in one uninterrupted bit history. -/
def blockIndex (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) : ℕ :=
  Nat.find (clock_unbounded τ blocks m)

/-- An actual bit and the fresh outcome used for its single row transition. -/
def event (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) : Bool × Bool :=
  if m < τ then (false,false)
  else if m = τ then (true,false)
  else
    let n := blockIndex τ blocks m
    let k := m - clock τ blocks n
    if k < (blocks n).zeros.length then (false, (blocks n).zeros[k]?.getD false)
    else (true, (blocks n).tick)

private lemma blockIndex_local (τ : ℕ) (blocks : ℕ → Block) (n k : ℕ)
    (hk : k ≤ (blocks n).zeros.length) :
    blockIndex τ blocks (clock τ blocks n + k) = n := by
  apply (Nat.find_eq_iff (clock_unbounded τ blocks (clock τ blocks n + k))).mpr
  constructor
  · rw [clock_succ]; omega
  · intro m hm
    have := (clock_strict τ blocks).monotone (show m+1 ≤ n by omega)
    omega

theorem consecutive_block_event (τ : ℕ) (blocks : ℕ → Block) (n k : ℕ)
    (hk : k ≤ (blocks n).zeros.length) :
    event τ blocks (clock τ blocks n + k) =
      if k < (blocks n).zeros.length then (false, (blocks n).zeros[k]?.getD false)
      else (true, (blocks n).tick) := by
  have ht : τ < clock τ blocks n + k := by dsimp [clock]; omega
  simp [event, not_lt.mpr ht.le, ne_of_gt ht, blockIndex_local τ blocks n k hk]

/-- Only the current counted state, next actual bit and fresh coin enter next. -/
def run {H J : ℕ} (hH : 0 < H) (t : Tick J) (τ : ℕ) (blocks : ℕ → Block) : ℕ → State H J
  | 0 => wait
  | m+1 => next hH t (run hH t τ blocks m) (event τ blocks m).1 (event τ blocks m).2

private lemma wait_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (m : ℕ) (hm : m ≤ τ) :
    run hH t τ blocks m = wait := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hh : m < τ := by omega
    simp [run, ih (by omega), event, hh, next, wait]

private lemma first_tick {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) :
    run hH t τ blocks (clock τ blocks 0) = active (initialEvidence hH) (Phase.first J) := by
  simp only [clock, range_zero, sum_empty, add_zero]
  simp [run, wait_prefix hH t τ blocks τ le_rfl, event, next, wait]

private lemma gap_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) (e : Evidence H)
    (hstart : run hH t τ blocks (clock τ blocks n) = active e (Phase.first J))
    (k : ℕ) (hk : k ≤ (blocks n).zeros.length) :
    run hH t τ blocks (clock τ blocks n + k) = active e (phaseAt J (blocks n) k) := by
  induction k with
  | zero => simpa [phaseAt] using hstart
  | succ k ih =>
    have hlt : k < (blocks n).zeros.length := by omega
    rw [Nat.add_succ, run, consecutive_block_event τ blocks n k hlt.le, if_pos hlt]
    simp only [Prod.fst, Prod.snd, ih (by omega), next, active, phaseAt]

private lemma gap_tick {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ) (e : Evidence H)
    (hstart : run hH t τ blocks (clock τ blocks n) = active e (Phase.first J)) :
    run hH t τ blocks (clock τ blocks (n+1)) = target H J (e.val + increment t (blocks n)) := by
  rw [clock_succ, run, consecutive_block_event τ blocks n _ le_rfl, if_neg (lt_irrefl _)]
  rw [gap_prefix hH t τ blocks n e hstart _ le_rfl]
  rfl

private lemma target_inside {H J : ℕ} (u : ℤ) (hu : inside H u) :
    target H J u = active ⟨u, Finset.mem_Ioo.mpr hu⟩ (Phase.first J) := by
  simp [target, not_le.mpr hu.2, not_le.mpr hu.1]

private lemma run_endpoint {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (n : ℕ)
    (hprev : ∀ m < n, inside H (evidence t blocks m)) :
    run hH t τ blocks (clock τ blocks n) = target H J (evidence t blocks n) := by
  induction n with
  | zero =>
    rw [first_tick]
    rw [show evidence t blocks 0 = 0 by simp [evidence], target,
      dif_neg (by omega : ¬ (H : ℤ) ≤ 0), dif_neg (by omega : ¬ (0 : ℤ) ≤ -(H : ℤ))]
    rfl
  | succ n ih =>
    have hnow := hprev n (by omega)
    have he := (ih (fun m hm => hprev m (by omega))).trans (target_inside _ hnow)
    rw [gap_tick hH t τ blocks n _ he]
    simp [evidence, sum_range_succ]

/-- Labels have no further reads in the paid run. The total trace only keeps
    their value fixed on the unused suffix. -/
def isLabel {H J : ℕ} : State H J → Prop
  | some (.inl _) => True
  | _ => False

private lemma target_label {H J : ℕ} (u : ℤ) :
    isLabel (target H J u) ↔ ¬ inside H u := by
  unfold target inside
  split <;> rename_i h
  · simp only [label, isLabel, true_iff]; omega
  · split <;> simp_all [label, active, isLabel] <;> omega

private lemma no_label_before {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (g : ℕ)
    (hprev : ∀ n < g, inside H (evidence t blocks n))
    (m : ℕ) (hm : m < clock τ blocks g) : ¬ isLabel (run hH t τ blocks m) := by
  by_cases ht : m ≤ τ
  · rw [wait_prefix hH t τ blocks m ht]; simp [wait, isLabel]
  · let n := blockIndex τ blocks m
    have hu : m < clock τ blocks (n+1) := Nat.find_spec (clock_unbounded τ blocks m)
    have hl : clock τ blocks n ≤ m := by
      by_cases hn : n = 0
      · rw [hn]; simp only [clock, range_zero, sum_empty, add_zero]; omega
      · have hp := Nat.find_min (clock_unbounded τ blocks m) (show n-1 < n by omega)
        have hn' : n-1+1=n := by omega
        rw [hn'] at hp
        omega
    have hng : n < g := by
      by_contra hh
      have := (clock_strict τ blocks).monotone (show g ≤ n by omega)
      omega
    have he : run hH t τ blocks (clock τ blocks n) =
        active ⟨evidence t blocks n, Finset.mem_Ioo.mpr (hprev n hng)⟩ (Phase.first J) :=
      (run_endpoint hH t τ blocks n (fun a ha => hprev a (by omega))).trans
        (target_inside _ (hprev n hng))
    have hk : m - clock τ blocks n ≤ (blocks n).zeros.length := by
      rw [clock_succ] at hu; omega
    have hr := gap_prefix hH t τ blocks n _ he _ hk
    have eqm : clock τ blocks n + (m - clock τ blocks n) = m := by omega
    rw [eqm] at hr
    rw [hr]; simp [active, isLabel]

/-- The first threshold crossing in completed gaps, including the infinite case. -/
def gapStop {J : ℕ} (H : ℕ) (t : Tick J) (blocks : ℕ → Block) : ℕ∞ :=
  if h : ∃ n, ¬ inside H (evidence t blocks n) then (Nat.find h : ℕ∞) else ⊤

/-- First entry into either internally emitted label, measured in paid reads. -/
def paidStop {H J : ℕ} (hH : 0 < H) (t : Tick J) (τ : ℕ) (blocks : ℕ → Block) : ℕ∞ :=
  if h : ∃ m, isLabel (run hH t τ blocks m) then (Nat.find h : ℕ∞) else ⊤

/-- Finite threshold exit is the very same run's first label, with exact payment.
    Every suffix after phase death and the terminal closing tick remain charged. -/
theorem stopped_prefix_payment {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block) (g : ℕ)
    (hexit : ¬ inside H (evidence t blocks g))
    (hprev : ∀ n < g, inside H (evidence t blocks n)) :
    gapStop H t blocks = (g : ℕ∞) ∧
    paidStop hH t τ blocks =
      ((1 + τ + ∑ n ∈ range g, ((blocks n).zeros.length + 1) : ℕ) : ℕ∞) ∧
    run hH t τ blocks (clock τ blocks g) = target H J (evidence t blocks g) ∧
    (∀ m < clock τ blocks g, ¬ isLabel (run hH t τ blocks m)) ∧
    (∀ n (hn : n < g) k, k ≤ (blocks n).zeros.length →
      run hH t τ blocks (clock τ blocks n + k) =
        active ⟨evidence t blocks n, Finset.mem_Ioo.mpr (hprev n hn)⟩ (phaseAt J (blocks n) k)) ∧
    (∀ (δ : ℝ), δ ≠ 0 → ∀ n, (evidence t blocks n : ℝ) = score δ t blocks n / δ) ∧
    (run hH t τ blocks (clock τ blocks g) = label true ↔ (H : ℤ) ≤ evidence t blocks g) ∧
    (run hH t τ blocks (clock τ blocks g) = label false ↔ evidence t blocks g ≤ -(H : ℤ)) ∧
    Fintype.card (State H J) = 3 + (2 * H - 1) * (J + 1) := by
  have hE : ∃ n, ¬ inside H (evidence t blocks n) := ⟨g,hexit⟩
  have hg : Nat.find hE = g := (Nat.find_eq_iff hE).mpr ⟨hexit, by simpa using hprev⟩
  have hend := run_endpoint hH t τ blocks g hprev
  have hlab : isLabel (run hH t τ blocks (clock τ blocks g)) := by
    rw [hend]; exact target_label _ |>.mpr hexit
  have hP : ∃ m, isLabel (run hH t τ blocks m) := ⟨_,hlab⟩
  have hp : Nat.find hP = clock τ blocks g := (Nat.find_eq_iff hP).mpr
    ⟨hlab, no_label_before hH t τ blocks g hprev⟩
  refine ⟨by simp [gapStop, hE, hg], ?_, hend, no_label_before hH t τ blocks g hprev,
    ?_, ?_, ?_, ?_, full_state_count H J hH⟩
  · simp [paidStop, hP, hp, clock, Nat.add_comm 1 τ]
  · intro n hn k hk
    exact gap_prefix hH t τ blocks n _
      ((run_endpoint hH t τ blocks n (fun m hm => hprev m (by omega))).trans
        (target_inside _ (hprev n hn))) k hk
  · intro δ hδ n
    simp only [score, ← sum_mul, evidence, Int.cast_sum]
    exact (mul_div_cancel_right₀ _ hδ).symm
  · rw [hend]
    unfold target
    split
    · simp_all [label]
    · split <;> simp_all [label, active]
  · rw [hend]
    unfold target
    split
    · have hn : ¬ evidence t blocks g ≤ -(H : ℤ) := by omega
      simp_all [label]
    · split <;> simp_all [label, active]

/-- If no completed-gap threshold is reached, no finite actual bit prefix emits
    a label. Infinite stopping is preserved, rather than assigned a default label. -/
theorem infinite_prefix {H J : ℕ} (hH : 0 < H) (t : Tick J)
    (τ : ℕ) (blocks : ℕ → Block)
    (h : ∀ n, inside H (evidence t blocks n)) :
    gapStop H t blocks = ⊤ ∧ paidStop hH t τ blocks = ⊤ := by
  have hp : ¬ ∃ m, isLabel (run hH t τ blocks m) := by
    rintro ⟨m,hm⟩
    exact no_label_before hH t τ blocks (m+1) (fun n _ => h n) m
      (by have := clock_ge τ blocks (m+1); omega) hm
  simp [gapStop, paidStop, h, hp]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution.CriticalRenewalPaths
