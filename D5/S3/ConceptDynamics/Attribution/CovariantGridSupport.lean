/- GID: D5/S3/ConceptDynamics/Attribution/CovariantGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/CovariantGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite seed budgets for covariant binary calibration on odd and even grids. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.CovariantGridSupport

open Finset

private def capacity (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (d + 1) * capacity d n + 1

private theorem capacity_mul (d n : ℕ) : d * capacity d n + 1 = (d + 1)^n := by
  induction n with
  | zero => simp [capacity]
  | succ n ih =>
    rw [pow_succ', ← ih, capacity]
    ring

/-- Adding a weight no larger than one plus the old representable range introduces no gaps. -/
private theorem split_digit {d old new k : ℕ} (hnew : new ≤ d * old + 1)
    (hk : k ≤ d * (old + new)) :
    ∃ x ≤ d, ∃ r ≤ d * old, r + x * new = k := by
  by_cases new_zero : new = 0
  · exact ⟨0, Nat.zero_le _, k, by simpa [new_zero] using hk, by simp⟩
  have new_pos := Nat.pos_of_ne_zero new_zero
  by_cases hd : k / new ≤ d
  · refine ⟨k / new, hd, k % new, ?_, ?_⟩
    · exact Nat.le_of_lt_succ ((Nat.mod_lt k new_pos).trans_le hnew)
    · simpa only [Nat.mul_comm (k / new) new] using Nat.mod_add_div k new
  · have hd' : d ≤ k / new := Nat.le_of_lt (Nat.lt_of_not_ge hd)
    have hmul : d * new ≤ k := (Nat.mul_le_mul_right new hd').trans (Nat.div_mul_le_self _ _)
    refine ⟨d, le_rfl, k - d * new, ?_, Nat.sub_add_cancel hmul⟩
    rw [Nat.mul_add] at hk
    omega

private theorem cover_capacity {d : ℕ} (n : ℕ) {q : ℕ} (hq : q ≤ capacity d n) :
    ∃ w : Fin n → ℕ, ∑ i, w i = q ∧
      ∀ k ≤ d * q, ∃ x : Fin n → Fin (d + 1), (∑ i, (x i).val * w i) = k := by
  induction n generalizing q with
  | zero =>
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    subst q
    refine ⟨fun i => i.elim0, by simp, ?_⟩
    intro k hk
    exact ⟨fun i => i.elim0, by simp at hk; simp [hk]⟩
  | succ n ih =>
    let old := min q (capacity d n)
    let new := q - old
    have old_le : old ≤ capacity d n := min_le_right _ _
    have old_add_new : old + new = q := Nat.add_sub_of_le (min_le_left _ _)
    have new_le : new ≤ d * old + 1 := by
      by_cases h : q ≤ capacity d n
      · simp [new, old, min_eq_left h]
      · change q - min q (capacity d n) ≤ d * min q (capacity d n) + 1
        rw [min_eq_right (le_of_not_ge h)]
        simp only [capacity, Nat.add_mul, Nat.one_mul] at hq
        omega
    obtain ⟨w, hw, cover⟩ := ih old_le
    refine ⟨Fin.snoc w new, ?_, ?_⟩
    · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hw] using old_add_new
    · intro k hk
      obtain ⟨x, hx, r, hr, eq⟩ := split_digit (k := k) new_le (by simpa only [old_add_new] using hk)
      obtain ⟨xs, hxs⟩ := cover r hr
      exact ⟨Fin.snoc xs ⟨x, Nat.lt_succ_of_le hx⟩,
        by simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hxs] using eq⟩

private theorem exists_digit_cover {d n q : ℕ} (hd : 0 < d) (hcapacity : d * q + 1 ≤ (d + 1)^n) :
    ∃ w : Fin n → ℕ, ∑ i, w i = q ∧
      ∀ k ≤ d * q, ∃ x : Fin n → Fin (d + 1), (∑ i, (x i).val * w i) = k := by
  rw [← capacity_mul] at hcapacity
  exact cover_capacity n (Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hcapacity) hd)

private theorem complete_grid {S : Type*} [Fintype S] [DecidableEq S] {m : ℕ}
    (a : S → ℕ) (total : ∑ s, a s = m) (σ : Equiv.Perm S)
    (inv : Function.Involutive σ) (invariant : ∀ s, a (σ s) = a s)
    (small : ∀ k : Fin (m + 1), k < k.rev → ∃ A : Finset S, ∑ s ∈ A, a s = k.val)
    (midpoint : ∀ k : Fin (m + 1), k = k.rev →
      ∃ A : Finset S, (∑ s ∈ A, a s = k.val) ∧ (∀ s, s ∈ A ↔ σ s ∉ A)) :
    ∃ E : Fin (m + 1) → Finset S,
      (∀ k, ∑ s ∈ E k, a s = k.val) ∧
      (∀ k s, s ∈ E k ↔ σ s ∉ E k.rev) := by
  classical
  let lower (k : Fin (m + 1)) := if h : k < k.rev then (small k h).choose else ∅
  let middle (k : Fin (m + 1)) := if h : k = k.rev then (midpoint k h).choose else ∅
  let opposite (A : Finset S) : Finset S := (A.map σ.toEmbedding)ᶜ
  have opposite_mem (A : Finset S) (s : S) : s ∈ opposite A ↔ σ s ∉ A := by
    have hinv : σ.symm s = σ s := by
      apply σ.injective
      rw [σ.apply_symm_apply, inv s]
    simp [opposite, Finset.mem_map_equiv, hinv]
  have opposite_mass (A : Finset S) :
      (∑ s ∈ opposite A, a s) + (∑ s ∈ A, a s) = m := by
    have hmapped : (∑ s ∈ A.map σ.toEmbedding, a s) = ∑ s ∈ A, a s := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun s _ => invariant s
    simpa only [opposite, hmapped, total] using
      (A.map σ.toEmbedding).sum_compl_add_sum a
  let E (k : Fin (m + 1)) : Finset S :=
    if k < k.rev then lower k else if k = k.rev then middle k else opposite (lower k.rev)
  have hrevl (k : Fin (m + 1)) : k.rev.val = m - k.val := by
    have hk := k.isLt
    change m + 1 - (k.val + 1) = m - k.val
    omega
  have Elo (k : Fin (m + 1)) (hl : k < k.rev) : E k = (small k hl).choose := by
    dsimp only [E, lower]
    rw [ite_eq_left hl, dite_eq_left hl]
  have Emid (k : Fin (m + 1)) (he : k = k.rev) : E k = (midpoint k he).choose := by
    have hn : ¬ k < k.rev := not_lt_of_ge he.ge
    dsimp only [E, middle]
    rw [ite_eq_right hn, ite_eq_left he, dite_eq_left he]
  have Ehi (k : Fin (m + 1)) (hr : k.rev < k) : E k = opposite (lower k.rev) := by
    dsimp only [E]
    rw [ite_eq_right (not_lt_of_gt hr), ite_eq_right (ne_of_gt hr)]
  refine ⟨E, ?_, ?_⟩
  · intro k
    rcases lt_trichotomy k k.rev with hl | he | hr
    · rw [Elo k hl]
      exact (small k hl).choose_spec
    · rw [Emid k he]
      exact (midpoint k he).choose_spec.1
    · have h' : k.rev < k.rev.rev := by simpa only [Fin.rev_rev] using hr
      have hh := opposite_mass (lower k.rev)
      have hlo : lower k.rev = (small k.rev h').choose := dite_eq_left h'
      rw [hlo, (small k.rev h').choose_spec] at hh
      have hrev := hrevl k
      have hnv := k.isLt
      rw [Ehi k hr, hlo]
      omega
  · intro k s
    rcases lt_trichotomy k k.rev with hl | he | hr
    · have hr' : k.rev.rev < k.rev := by simpa only [Fin.rev_rev] using hl
      have hlo : lower k = (small k hl).choose := dite_eq_left hl
      rw [Elo k hl, Ehi k.rev hr', Fin.rev_rev, hlo, opposite_mem, inv, not_not]
    · rw [← he, Emid k he]
      exact (midpoint k he).choose_spec.2 s
    · have hl' : k.rev < k.rev.rev := by simpa only [Fin.rev_rev] using hr
      have hlo : lower k.rev = (small k.rev hl').choose := dite_eq_left hl'
      rw [Ehi k hr, Elo k.rev hl', hlo, opposite_mem]

private theorem odd_grid_achievable {m n : ℕ} (odd : Odd m) (capacity : m + 1 ≤ 2^n) :
    ∃ a : Fin n → ℕ, (∑ s, a s = m) ∧
      ∃ E : Fin (m + 1) → Finset (Fin n),
        (∀ k, ∑ s ∈ E k, a s = k.val) ∧ (∀ k s, s ∈ E k ↔ s ∉ E k.rev) := by
  obtain ⟨a, total, cover⟩ :=
    exists_digit_cover (d := 1) (n := n) (q := m) (by decide) (by simpa using capacity)
  refine ⟨a, total, complete_grid a total (Equiv.refl _) (fun _ => rfl)
    (fun _ => rfl) ?_ ?_⟩
  · intro k _
    obtain ⟨digits, eq⟩ := cover k.val (by have hk := k.isLt; omega)
    refine ⟨univ.filter (fun s => (digits s).val = 1), ?_⟩
    rw [Finset.sum_filter, ← eq]
    apply Finset.sum_congr rfl
    intro i _
    generalize digits i = t
    fin_cases t <;> simp
  · intro k he
    exfalso
    have hv := congrArg Fin.val he
    change k.val = m + 1 - (k.val + 1) at hv
    obtain ⟨j, hj⟩ := odd
    have hk := k.isLt
    omega

private def pairEvent {r : ℕ} (digits : Fin r → Fin 3) : Finset (Fin r × Bool) :=
  univ.filter fun p => (if p.2 then 1 else 0) < (digits p.1).val

private theorem pairEvent_mass {r : ℕ} (a : Fin r → ℕ) (digits : Fin r → Fin 3) :
    (∑ s ∈ pairEvent digits, a s.1) = ∑ i, (digits i).val * a i := by
  rw [pairEvent, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  generalize digits i = t
  fin_cases t <;> simp [Nat.succ_mul]

private theorem even_grid_achievable {q r : ℕ} (capacity : 2 * q + 1 ≤ 3^r) :
    ∃ a : Fin r → ℕ, (∑ i, a i = q) ∧
      ∃ E : Fin (2 * q + 1) → Finset (Fin r × Bool),
        (∀ k, ∑ s ∈ E k, a s.1 = k.val) ∧
        (∀ k s, s ∈ E k ↔ (s.1, !s.2) ∉ E k.rev) := by
  obtain ⟨a, total, cover⟩ :=
    exists_digit_cover (d := 2) (n := r) (q := q) (by decide) capacity
  let σ : Equiv.Perm (Fin r × Bool) :=
    ⟨fun s => (s.1, !s.2), fun s => (s.1, !s.2), fun s => by simp, fun s => by simp⟩
  have inv : Function.Involutive σ := by intro s; simp [σ]
  have sumPair : ∑ s : Fin r × Bool, a s.1 = 2 * q := by
    simp [Fintype.sum_prod_type, ← two_mul, ← Finset.mul_sum, total]
  refine ⟨a, total,
    complete_grid (fun s => a s.1) sumPair σ inv (fun _ => rfl) ?_ ?_⟩
  · intro k _
    obtain ⟨digits, eq⟩ := cover k.val (by omega)
    exact ⟨pairEvent digits, (pairEvent_mass _ _).trans eq⟩
  · intro k he
    have hv := congrArg Fin.val he
    change k.val = 2 * q + 1 - (k.val + 1) at hv
    have hk := k.isLt
    have middle : k.val = q := by omega
    let digits : Fin r → Fin 3 := fun _ => 1
    refine ⟨pairEvent digits, ?_, ?_⟩
    · rw [pairEvent_mass, middle]
      simpa [digits] using total
    · rintro ⟨i, _ | _⟩ <;> simp [pairEvent, σ, digits]

private theorem event_grid_injective {S : Type*} {m : ℕ}
    (E : Fin (m + 1) → Finset S) (w : S → ℝ) (hm : 0 < m)
    (calibration : ∀ k, ∑ s ∈ E k, w s = (k.val : ℝ) / m) :
    Function.Injective E := by
  intro k l same
  have eq := (calibration k).symm.trans ((congrArg (fun t : Finset S => ∑ s ∈ t, w s) same).trans
    (calibration l))
  have nz : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  exact Fin.ext (by exact_mod_cast (div_left_inj' nz).mp eq)

private theorem subset_count_bound {S : Type*} [Fintype S] {m : ℕ}
    (E : Fin (m + 1) → Finset S) (w : S → ℝ) (hm : 0 < m)
    (calibration : ∀ k, ∑ s ∈ E k, w s = (k.val : ℝ) / m) :
    m + 1 ≤ 2 ^ Fintype.card S := by
  classical
  simpa using Fintype.card_le_of_injective E (event_grid_injective E w hm calibration)

private def midpointPairs {S : Type*} [DecidableEq S]
    (A : Finset S) (σ : S → S) (inv : Function.Involutive σ)
    (flip : ∀ s, s ∈ A ↔ σ s ∉ A) : ({s // s ∈ A} × Bool) ≃ S where
  toFun p := if p.2 then p.1.val else σ p.1.val
  invFun s := if h : s ∈ A then (⟨s, h⟩, true) else (⟨σ s, (flip (σ s)).mpr (by simpa [inv s] using h)⟩, false)
  left_inv := by
    rintro ⟨a, _ | _⟩
    · have hn := (flip a.val).mp a.property
      simp [hn, inv a.val]
    · simp [a.property]
  right_inv := by
    intro s
    by_cases h : s ∈ A <;> simp [h, inv s]

private def pairCount {J : Type*} [DecidableEq J] (A : Finset (J × Bool))
    (j : J) : Fin 3 := ⟨(if (j, false) ∈ A then 1 else 0) + (if (j, true) ∈ A then 1 else 0), by
  split_ifs <;> decide⟩

private theorem pairMass {J : Type*} [Fintype J] [DecidableEq J]
    (A : Finset (J × Bool)) (w : J → ℝ) :
    (∑ u ∈ A, w u.1) = ∑ j, ((pairCount A j).val : ℝ) * w j := by
  have filterA : univ.filter (fun u => u ∈ A) = A := by simp
  calc
    (∑ u ∈ A, w u.1) = ∑ u : J × Bool, if u ∈ A then w u.1 else 0 := by
      rw [← Finset.sum_filter, filterA]
    _ = _ := ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  by_cases hf : (j, false) ∈ A <;> by_cases ht : (j, true) ∈ A
  all_goals simp [pairCount, hf, ht, two_mul, add_comm]

private theorem pair_count_bound {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (E : Fin (m + 1) → Finset (J × Bool)) (w : J → ℝ) (hm : 0 < m)
    (calibration : ∀ k, ∑ s ∈ E k, w s.1 = (k.val : ℝ) / m) :
    m + 1 ≤ 3 ^ Fintype.card J := by
  let digits (k : Fin (m + 1)) := pairCount (E k)
  have inj : Function.Injective digits := by
    intro k l same
    have eq : ∑ s ∈ E k, w s.1 = ∑ s ∈ E l, w s.1 := by
      rw [pairMass, pairMass]
      change (∑ j, ((digits k j).val : ℝ) * w j) = ∑ j, ((digits l j).val : ℝ) * w j
      rw [same]
    rw [calibration, calibration] at eq
    have nz : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    exact Fin.ext (by exact_mod_cast (div_left_inj' nz).mp eq)
  simpa using Fintype.card_le_of_injective digits inj

private theorem even_grid_pair_bound {S : Type*} [Fintype S] [DecidableEq S] {q : ℕ}
    (E : Fin (2 * q + 1) → Finset S) (w : S → ℝ) (hq : 0 < q)
    (calibration : ∀ k, ∑ s ∈ E k, w s = (k.val : ℝ) / (2 * q : ℕ))
    (σ : S → S) (inv : Function.Involutive σ) (law : ∀ s, w (σ s) = w s)
    (midFlip : ∀ s, s ∈ E ⟨q, by omega⟩ ↔ σ s ∉ E ⟨q, by omega⟩) :
    ∃ r, Fintype.card S = 2 * r ∧ 2 * q + 1 ≤ 3 ^ r := by
  let A := E ⟨q, by omega⟩
  let e := midpointPairs A σ inv midFlip
  let J := {s // s ∈ A}
  let E' (k : Fin (2 * q + 1)) := (E k).map e.symm.toEmbedding
  have transport (s : S) : w (e.symm s).1.val = w s := by
    change w (((if h : s ∈ A then (⟨s, h⟩, true)
      else (⟨σ s, (midFlip (σ s)).mpr (by simpa [inv s] using h)⟩, false)) : J × Bool).1.val) = w s
    split_ifs <;> simp [law]
  have hcal (k : Fin (2 * q + 1)) :
      ∑ u ∈ E' k, w u.1.val = (k.val : ℝ) / (2 * q : ℕ) := by
    change (∑ u ∈ (E k).map e.symm.toEmbedding, w u.1.val) = _
    rw [Finset.sum_map, ← calibration k]
    exact Finset.sum_congr rfl fun s _ => transport s
  refine ⟨Fintype.card J, ?_, pair_count_bound E' (fun a => w a.val) (by omega) hcal⟩
  rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

/-- One seed law and a single label-swap action for the whole binary probability grid. -/
structure CovariantGrid (m : ℕ) (S : Type*) [Fintype S] where
  weight : S → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  normalized : ∑ s, weight s = 1
  exchange : Equiv.Perm S
  exchange_twice : Function.Involutive exchange
  weight_exchange : ∀ s, weight (exchange s) = weight s
  event : Fin (m + 1) → Finset S
  calibrated : ∀ k, ∑ s ∈ event k, weight s = (k.val : ℝ) / m
  covariant : ∀ k s, s ∈ event k ↔ exchange s ∉ event k.rev

private noncomputable def ofIntegerWeights {m : ℕ} {S : Type*} [Fintype S] (hm : 0 < m)
    (a : S → ℕ) (total : ∑ s, a s = m) (σ : Equiv.Perm S) (inv : Function.Involutive σ)
    (law : ∀ s, a (σ s) = a s) (E : Fin (m + 1) → Finset S)
    (counts : ∀ k, ∑ s ∈ E k, a s = k.val)
    (flip : ∀ k s, s ∈ E k ↔ σ s ∉ E k.rev) : CovariantGrid m S where
  weight s := (a s : ℝ) / m
  nonnegative s := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  normalized := by
    rw [← Finset.sum_div, ← Nat.cast_sum, total, div_self (by exact_mod_cast hm.ne')]
  exchange := σ
  exchange_twice := inv
  weight_exchange s := by rw [law]
  event := E
  calibrated k := by rw [← Finset.sum_div, ← Nat.cast_sum, counts]
  covariant := flip

/-- A grid with odd denominator admits a covariant law on at most n seeds exactly when
its m + 1 distinct levels fit into the 2^n subsets of an n-element seed type. -/
theorem odd_support_budget_iff {m : ℕ} (odd : Odd m) (n : ℕ) :
    (∃ (S : Type) (finite : Fintype S), Fintype.card S ≤ n ∧
      Nonempty (@CovariantGrid m S finite)) ↔ m + 1 ≤ 2^n := by
  have hm : 0 < m := by obtain ⟨k, hk⟩ := odd; omega
  constructor
  · rintro ⟨S, finite, hcard, ⟨grid⟩⟩
    exact (subset_count_bound grid.event grid.weight hm grid.calibrated).trans
      (Nat.pow_le_pow_right (by decide) hcard)
  · intro h
    obtain ⟨a, total, E, counts, flip⟩ := odd_grid_achievable odd h
    exact ⟨Fin n, inferInstance, by simp,
      ⟨ofIntegerWeights hm a total (Equiv.refl _) (fun _ => rfl) (fun _ => rfl) E counts flip⟩⟩

/-- A grid with positive even denominator admits a covariant law on at most 2r seeds
exactly when its 2q + 1 levels fit into the 3^r pair occupancy vectors. -/
theorem even_support_budget_iff {q : ℕ} (positive : 0 < q) (r : ℕ) :
    (∃ (S : Type) (finite : Fintype S), Fintype.card S ≤ 2 * r ∧
      Nonempty (@CovariantGrid (2 * q) S finite)) ↔ 2 * q + 1 ≤ 3^r := by
  classical
  constructor
  · rintro ⟨S, finite, hcard, ⟨grid⟩⟩
    let mid : Fin (2 * q + 1) := ⟨q, by omega⟩
    have fixed : mid.rev = mid := by
      apply Fin.ext
      change 2 * q + 1 - (q + 1) = q
      omega
    have flip (s : S) : s ∈ grid.event mid ↔ grid.exchange s ∉ grid.event mid := by
      simpa only [fixed] using grid.covariant mid s
    obtain ⟨p, hp, lower⟩ := even_grid_pair_bound grid.event grid.weight positive
      grid.calibrated grid.exchange grid.exchange_twice grid.weight_exchange flip
    exact lower.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · intro h
    obtain ⟨a, total, E, counts, flip⟩ := even_grid_achievable h
    let σ : Equiv.Perm (Fin r × Bool) :=
      ⟨fun s => (s.1, !s.2), fun s => (s.1, !s.2), fun s => by simp, fun s => by simp⟩
    have inv : Function.Involutive σ := by intro s; simp [σ]
    have sumPair : ∑ s : Fin r × Bool, a s.1 = 2 * q := by
      simp [Fintype.sum_prod_type, ← two_mul, ← Finset.mul_sum, total]
    exact ⟨Fin r × Bool, inferInstance, by simp [Fintype.card_prod, Nat.mul_comm],
      ⟨ofIntegerWeights (by omega) (fun s => a s.1) sumPair σ inv (fun _ => rfl) E counts flip⟩⟩

#print axioms odd_support_budget_iff
#print axioms even_support_budget_iff

end D5.S3.ConceptDynamics.Attribution.CovariantGridSupport
