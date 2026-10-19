/- GID: D5/S1/Words/TwoCenteredAbelianPeriods
   generality: G
   mirror-B: D5/B/S1/Words/TwoCenteredAbelianPeriods
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two centered abelian period lengths force ordinary periodicity. -/

/-
Public theorem result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#17818; Proved)
  Direct frozen dependencies: D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.letterCount
    declaration statement_id: sha256:757677e4170f6f89e0ca360e898ad7c4d1081d9c5a08649a9fa36bc0333c57bd

The centered blocks retain the literal List.ofFn expression of issue #17818,
with no duplicate block definition. Proofs use Mathlib.fwdDiff, Pi.single and birkhoffSum along Order.pred
directly, and the frozen letterCount for abelian equivalence. The alphabet is
finite, positions are cuts after w i, and zero block lengths are excluded.
For positive lengths the proof supplies Nat.lcm as a period.
Literature completeness: ASSUMED-UNVERIFIED.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19073 (result).

Declaration classification (all theorem proofs bind-only; no escape witness):
  CentralAbelianPower: definition; consumers: claim, result.
  Periodic: definition; consumers: claim.
  claim: definition; consumers: result.
  central_square: bind-only; consumers: result.
  H2: definition; consumers: energy_identity, flux, flux_step, flux_bounded, flux_coboundary.
  H3: definition; consumers: energy_identity, flux, flux_step, flux_bounded, flux_coboundary.
  H4: definition; consumers: energy_identity, flux, flux_step, flux_bounded, flux_coboundary.
  mixed_comm: bind-only; consumers: energy_identity, flux_coboundary.
  energy_identity: bind-only; consumers: flux_step.
  cumulative: definition; consumers: cumulative_neg, cumulative_step, squares_lcm_period.
  cumulative_neg: bind-only; consumers: cumulative_step.
  cumulative_step: bind-only; consumers: cumulative_window, squares_lcm_period.
  cumulative_window: bind-only; consumers: count_cumulative.
  block_succ: bind-only; consumers: count_block.
  count_block: bind-only; consumers: count_cumulative.
  count_cumulative: bind-only; consumers: count_bound, square_count_difference.
  count_bound: bind-only; consumers: squares_lcm_period.
  backSum_step: bind-only; consumers: flux_step.
  backSum_add: bind-only; consumers: flux_coboundary.
  backSum_bound: bind-only; consumers: flux_bounded, no_defects.
  flux: definition; consumers: flux_step, flux_bounded, finite_defects, flux_coboundary, no_defects.
  flux_step: bind-only; consumers: flux_antitone, finite_defects, no_defects.
  flux_antitone: bind-only; consumers: finite_defects, no_defects.
  bounded_extrema: bind-only; consumers: finite_defects, no_defects.
  flux_bounded: bind-only; consumers: finite_defects, no_defects.
  finite_defects: bind-only; consumers: no_defects.
  bounded_drift_zero: bind-only; consumers: no_defects.
  H: definition; consumers: flux_coboundary, no_defects.
  flux_coboundary: bind-only; consumers: no_defects.
  no_defects: bind-only; consumers: squares_lcm_period.
  F_add: bind-only; consumers: periodic_multiple_window.
  periodic_multiple_window: bind-only; consumers: periodic_increment.
  periodic_increment: bind-only; consumers: squares_lcm_period.
  square_count_difference: bind-only; consumers: squares_lcm_period.
  squares_lcm_period: bind-only; consumers: result.
  result: bind-only; consumers: none (settling result).
-/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Dynamics.BirkhoffSum.Basic

set_option autoImplicit false

namespace D5.S1.Words.TwoCenteredAbelianPeriods

open D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs (letterCount)


/-- `w` has at position `i` (the cut between `w_i` and `w_{i+1}`) a central abelian `2k`-power with
period of length `l` (RAIRO-ITA 46 (2012), Section 2.2): the factor `w_{i-lk+1} … w_{i+lk}` is the
concatenation of `2k` nonempty blocks of length `l` with the same letter counts. -/
def CentralAbelianPower {r : ℕ} (w : ℤ → Fin r) (k l : ℕ) (i : ℤ) : Prop :=
  0 < l ∧ ∀ j : ℕ, j < 2 * k → ∀ a : Fin r,
    letterCount ((List.ofFn fun t : Fin l => w ((i - l * k + 1 + j * l) + t))) a = letterCount ((List.ofFn fun t : Fin l => w ((i - l * k + 1) + t))) a

/-- Ordinary periodicity of a bi-infinite word. -/
def Periodic {r : ℕ} (w : ℤ → Fin r) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ n : ℤ, w (n + p) = w n

/-- Avgustinovich–Karhumäki–Puzynina, RAIRO-ITA 46 (2012), Open problem 6.2: "Let k be an integer.
Does there exist a non-periodic word w and integers l1, l2, such that w contains a central abelian
2k-power of length l1 or l2 at every position?" The settlement answers no: for every `k ≥ 1`, every
finite alphabet `Fin r` and all `l₁, l₂`, a bi-infinite word with such a power at every position is
periodic. -/
def claim : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (r : ℕ) (w : ℤ → Fin r) (l₁ l₂ : ℕ),
    (∀ i : ℤ, CentralAbelianPower w k l₁ i ∨ CentralAbelianPower w k l₂ i) → Periodic w

open Finset

private theorem central_square {r k l : ℕ} {w : ℤ → Fin r} {i : ℤ}
    (hk : 1 ≤ k) (h : CentralAbelianPower w k l i) :
    CentralAbelianPower w 1 l i := by
  refine ⟨h.1, ?_⟩
  intro j hj a
  have hleft := h.2 (k - 1) (by omega) a
  have hright := h.2 k (lt_two_mul_self hk) a
  have hl : i - (l : ℤ) * k + 1 + (↑(k - 1) : ℤ) * l = i - l + 1 := by
    rw [Nat.cast_sub hk]; ring
  have hr : i - (l : ℤ) * k + 1 + (k : ℤ) * l = i + 1 := by ring
  norm_num only [Nat.cast_one, mul_one] at *
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp
  · simpa [hl, hr, show i - (l : ℤ) + 1 + l = i + 1 by ring] using hright.trans hleft.symm

private def H2 (C : ℤ → ℤ) (p q n : ℤ) := fwdDiff (p : ℤ) C n * fwdDiff (q : ℤ) C (n + p)
private def H3 (C : ℤ → ℤ) (p q n : ℤ) := fwdDiff (p : ℤ) C (n + q) * fwdDiff (q : ℤ) C n
private def H4 (C : ℤ → ℤ) (p q n : ℤ) := fwdDiff (p : ℤ) C (n + q) * fwdDiff (q : ℤ) C (n + p)

private theorem mixed_comm (C : ℤ → ℤ) (p q n : ℤ) :
    fwdDiff (p : ℤ) C (n + q) - fwdDiff (p : ℤ) C n = fwdDiff (q : ℤ) C (n + p) - fwdDiff (q : ℤ) C n := by
  simp only [fwdDiff, add_comm q p, add_assoc]
  ring

private theorem energy_identity (C : ℤ → ℤ) (p q n : ℤ) :
    (fwdDiff (p : ℤ) C n - fwdDiff (p : ℤ) C (n - p)) * (fwdDiff (q : ℤ) C n - fwdDiff (q : ℤ) C (n - q)) -
      (fwdDiff (p : ℤ) C (n + q) - fwdDiff (p : ℤ) C n)^2 =
    (H2 C p q n - H2 C p q (n - p)) +
    (H3 C p q n - H3 C p q (n - q)) -
    (H4 C p q n - H4 C p q (n - (p + q))) := by
  have h := mixed_comm C p q n
  unfold H2 H3 H4
  simp only [sub_add_cancel, sub_add_eq_add_sub,
    show n - (p + q) + q = n - p by ring,
    show n - (p + q) + p = n - q by ring]
  have hh : (fwdDiff (p : ℤ) C (n + q) - fwdDiff (p : ℤ) C n)^2 =
      (fwdDiff (p : ℤ) C (n + q) - fwdDiff (p : ℤ) C n) * (fwdDiff (q : ℤ) C (n + p) - fwdDiff (q : ℤ) C n) := by
    rw [← h]; ring
  rw [hh]
  ring


private def cumulative (a : ℤ → ℤ) : ℤ → ℤ
  | .ofNat n => ∑ j ∈ range n, a (j+1)
  | .negSucc n => -∑ j ∈ range (n+1), a (-j)

private theorem cumulative_neg (a : ℤ → ℤ) (n : ℕ) :
    cumulative a (-n) = -∑ j ∈ range n, a (-j) := by
  cases n with
  | zero => simp [cumulative]
  | succ n => rfl

private theorem cumulative_step (a : ℤ → ℤ) (n : ℤ) :
    cumulative a (n+1) - cumulative a n = a (n+1) := by
  cases n with
  | ofNat n =>
    rw [show (Int.ofNat n : ℤ)+1 = Int.ofNat (n+1) by rfl]
    simp [cumulative, sum_range_succ]
  | negSucc n =>
    rw [show Int.negSucc n + 1 = -(n:ℤ) from Int.negSucc_add_one_eq_neg_ofNat_iff.mpr rfl]
    change cumulative a (-(n:ℤ)) - (-∑ j ∈ range (n+1), a (-j)) = a (-(n:ℤ))
    rw [cumulative_neg, sum_range_succ]
    ring

private theorem cumulative_window (a : ℤ → ℤ) (l : ℕ) (n : ℤ) :
    fwdDiff (l : ℤ) (cumulative a) n = ∑ j ∈ range l, a (n+j+1) := by
  change cumulative a (n + l) - cumulative a n = _
  calc
    cumulative a (n + l) - cumulative a n =
        ∑ j ∈ range l, (cumulative a (n + (j + 1 : ℕ)) - cumulative a (n + j)) := by
      simpa only [Nat.cast_zero, add_zero] using
        (sum_range_sub (fun j : ℕ => cumulative a (n + j)) l).symm
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using cumulative_step a (n + j)

private theorem block_succ {r : ℕ} (w : ℤ → Fin r) (s : ℤ) (l : ℕ) :
    (List.ofFn fun t : Fin (l+1) => w (s + t)) = w s :: (List.ofFn fun t : Fin l => w ((s+1) + t)) := by
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Nat.cast_zero, add_zero]
  congr 1
  apply congrArg List.ofFn
  funext j
  congr 1
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

private theorem count_block {r : ℕ} (w : ℤ → Fin r) (a : Fin r) (s : ℤ) (l : ℕ) :
    (letterCount ((List.ofFn fun t : Fin l => w (s + t))) a : ℤ) = ∑ j ∈ range l, (fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)) (s+j) := by
  induction l generalizing s with
  | zero => simp [letterCount]
  | succ l ih =>
    rw [block_succ]
    unfold letterCount
    rw [List.count_cons]
    push_cast
    rw [show (((List.ofFn fun t : Fin l => w ((s+1) + t))).count a : ℤ) =
        ∑ j ∈ range l, (fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)) (s+1+j) from ih (s+1)]
    rw [sum_range_succ']
    simp only [Nat.cast_zero, add_zero]
    have hs : (∑ j ∈ range l, (fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)) (s+1+j)) =
        ∑ j ∈ range l, (fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)) (s+(j+1:ℕ)) := by
      apply sum_congr rfl
      intro j hj
      congr 1
      push_cast
      ring
    rw [hs]
    simp [Pi.single_apply, beq_iff_eq, add_comm]

private theorem count_cumulative {r : ℕ} (w : ℤ → Fin r) (a : Fin r) (n : ℤ) (l : ℕ) :
    fwdDiff (l : ℤ) (cumulative ((fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)))) n = (letterCount ((List.ofFn fun t : Fin l => w ((n+1) + t))) a : ℤ) := by
  rw [cumulative_window, count_block]
  apply sum_congr rfl
  intro j hj
  congr 1
  ring

private theorem count_bound {r : ℕ} (w : ℤ → Fin r) (a : Fin r) (n : ℤ) (l : ℕ) :
    |fwdDiff (l : ℤ) (cumulative ((fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)))) n| ≤ l := by
  rw [count_cumulative, abs_of_nonneg (Int.natCast_nonneg _)]
  have h := List.count_le_length (a := a) (l := (List.ofFn fun t : Fin l => w ((n+1) + t)))
  simp only [List.length_ofFn] at h
  exact_mod_cast h


private theorem backSum_step (f : ℤ → ℤ) (r : ℕ) (n : ℤ) :
    birkhoffSum (Order.pred : ℤ → ℤ) f r n - birkhoffSum (Order.pred : ℤ → ℤ) f r (n - 1) = f n - f (n - r) := by
  simpa only [Order.pred_eq_sub_one, Order.pred_iterate, neg_sub] using
    congrArg Neg.neg (birkhoffSum_apply_sub_birkhoffSum (Order.pred : ℤ → ℤ) f r n)

private theorem backSum_add (f : ℤ → ℤ) (p q : ℕ) (n : ℤ) :
    birkhoffSum (Order.pred : ℤ → ℤ) f (p + q) n =
      birkhoffSum (Order.pred : ℤ → ℤ) f p n + birkhoffSum (Order.pred : ℤ → ℤ) f q (n - p) := by
  simpa only [Order.pred_iterate] using
    birkhoffSum_add_right_apply (Order.pred : ℤ → ℤ) f p q n

private theorem backSum_bound (f : ℤ → ℤ) (r : ℕ) (n B : ℤ)
    (hb : ∀ n, |f n| ≤ B) : |birkhoffSum (Order.pred : ℤ → ℤ) f r n| ≤ r * B := by
  calc
    |birkhoffSum (Order.pred : ℤ → ℤ) f r n| ≤ ∑ j ∈ range r, |f (n - j)| := by
      simpa only [birkhoffSum, Order.pred_iterate] using
        (abs_sum_le_sum_abs (fun j : ℕ => f (n - j)) (range r))
    _ ≤ ∑ j ∈ range r, B := sum_le_sum fun j hj => hb _
    _ = r * B := by simp

private def flux (C : ℤ → ℤ) (p q : ℕ) (n : ℤ) : ℤ :=
  birkhoffSum (Order.pred : ℤ → ℤ) (H2 C p q) p n + birkhoffSum (Order.pred : ℤ → ℤ) (H3 C p q) q n - birkhoffSum (Order.pred : ℤ → ℤ) (H4 C p q) (p+q) n

private theorem flux_step (C : ℤ → ℤ) (p q : ℕ)
    (ha : ∀ n, (fwdDiff (p : ℤ) C n - fwdDiff (p : ℤ) C (n - p)) * (fwdDiff (q : ℤ) C n - fwdDiff (q : ℤ) C (n - q)) = 0)
    (n : ℤ) :
    flux C p q n - flux C p q (n-1) = -(fwdDiff (p : ℤ) C (n+q) - fwdDiff (p : ℤ) C n)^2 := by
  have he := energy_identity C p q n
  rw [ha n] at he
  have h2 := backSum_step (H2 C p q) p n
  have h3 := backSum_step (H3 C p q) q n
  have h4 := backSum_step (H4 C p q) (p+q) n
  unfold flux
  push_cast at h4
  linarith

private theorem flux_antitone (C : ℤ → ℤ) (p q : ℕ)
    (ha : ∀ n, (fwdDiff (p : ℤ) C n - fwdDiff (p : ℤ) C (n - p)) * (fwdDiff (q : ℤ) C n - fwdDiff (q : ℤ) C (n - q)) = 0) :
    Antitone (flux C p q) := by
  apply antitone_int_of_succ_le
  intro n
  have h := flux_step C p q ha (n+1)
  simp only [add_sub_cancel_right] at h
  nlinarith [sq_nonneg (fwdDiff (p : ℤ) C (n + 1 + q) - fwdDiff (p : ℤ) C (n+1))]

private theorem bounded_extrema (f : ℤ → ℤ) (B : ℤ) (hb : ∀ n, |f n| ≤ B) :
    (∃ lo : ℤ, ∀ n, f lo ≤ f n) ∧ (∃ hi : ℤ, ∀ n, f n ≤ f hi) := by
  classical
  have hf : (Set.range f).Finite :=
    (Set.finite_Icc (-B) B).subset (by rintro _ ⟨n, rfl⟩; exact abs_le.mp (hb n))
  have hn : (Set.range f).Nonempty := Set.range_nonempty f
  obtain ⟨x, ⟨lo, rfl⟩, hx⟩ := Set.exists_min_image (Set.range f) id hf hn
  obtain ⟨y, ⟨hi, rfl⟩, hy⟩ := Set.exists_max_image (Set.range f) id hf hn
  exact ⟨⟨lo, fun n => hx _ ⟨n,rfl⟩⟩, ⟨hi, fun n => hy _ ⟨n,rfl⟩⟩⟩


private theorem flux_bounded (C : ℤ → ℤ) (p q : ℕ)
    (hf : ∀ n, |fwdDiff (p : ℤ) C n| ≤ p) (hg : ∀ n, |fwdDiff (q : ℤ) C n| ≤ q) :
    ∀ n, |flux C p q n| ≤ 2 * (p+q) * (p*q : ℕ) := by
  have prod_bound (x y : ℤ) : |fwdDiff (p : ℤ) C x * fwdDiff (q : ℤ) C y| ≤ (p : ℤ) * q := by
    rw [abs_mul]
    exact mul_le_mul (hf x) (hg y) (abs_nonneg _) (Int.natCast_nonneg p)
  intro n
  have h2 := backSum_bound (H2 C p q) p n (p*q) (fun n => prod_bound n (n+p))
  have h3 := backSum_bound (H3 C p q) q n (p*q) (fun n => prod_bound (n+q) n)
  have h4 := backSum_bound (H4 C p q) (p+q) n (p*q) (fun n => prod_bound (n+q) (n+p))
  have hle : |flux C p q n| ≤ |birkhoffSum (Order.pred : ℤ → ℤ) (H2 C p q) p n| +
      |birkhoffSum (Order.pred : ℤ → ℤ) (H3 C p q) q n| + |birkhoffSum (Order.pred : ℤ → ℤ) (H4 C p q) (p+q) n| := by
    unfold flux
    have h1 := abs_add_le (birkhoffSum (Order.pred : ℤ → ℤ) (H2 C p q) p n + birkhoffSum (Order.pred : ℤ → ℤ) (H3 C p q) q n)
      (-birkhoffSum (Order.pred : ℤ → ℤ) (H4 C p q) (p+q) n)
    have h2 := abs_add_le (birkhoffSum (Order.pred : ℤ → ℤ) (H2 C p q) p n) (birkhoffSum (Order.pred : ℤ → ℤ) (H3 C p q) q n)
    rw [abs_neg] at h1
    simp only [sub_eq_add_neg]
    linarith
  push_cast at *
  nlinarith

private theorem finite_defects (C : ℤ → ℤ) (p q : ℕ)
    (ha : ∀ n, (fwdDiff (p : ℤ) C n - fwdDiff (p : ℤ) C (n - p)) * (fwdDiff (q : ℤ) C n - fwdDiff (q : ℤ) C (n - q)) = 0)
    (hf : ∀ n, |fwdDiff (p : ℤ) C n| ≤ p) (hg : ∀ n, |fwdDiff (q : ℤ) C n| ≤ q) :
    ∃ L R : ℤ, (∀ n, n ≤ L → fwdDiff (p : ℤ) C (n+q) = fwdDiff (p : ℤ) C n) ∧
      (∀ n, R ≤ n → fwdDiff (p : ℤ) C (n+q) = fwdDiff (p : ℤ) C n) := by
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := bounded_extrema _ _ (flux_bounded C p q hf hg)
  have anti := flux_antitone C p q ha
  refine ⟨hi, lo+1, ?_, ?_⟩
  · intro n hn
    have h1 : flux C p q n = flux C p q hi := le_antisymm (hhi _) (anti hn)
    have h2 : flux C p q (n-1) = flux C p q hi :=
      le_antisymm (hhi _) (anti (by omega))
    have he := flux_step C p q ha n
    rw [h1, h2] at he
    nlinarith [sq_nonneg (fwdDiff (p : ℤ) C (n+q) - fwdDiff (p : ℤ) C n)]
  · intro n hn
    have h1 : flux C p q n = flux C p q lo := le_antisymm (anti (Int.le_of_lt hn)) (hlo _)
    have h2 : flux C p q (n-1) = flux C p q lo :=
      le_antisymm (anti (Int.le_sub_one_of_lt hn)) (hlo _)
    have he := flux_step C p q ha n
    rw [h1, h2] at he
    nlinarith [sq_nonneg (fwdDiff (p : ℤ) C (n+q) - fwdDiff (p : ℤ) C n)]

private theorem bounded_drift_zero (f : ℕ → ℤ) (c B : ℤ)
    (hb : ∀ n, |f n| ≤ B) (hd : ∀ n, f (n+1) - f n = c) : c = 0 := by
  have he (n : ℕ) : f n = f 0 + n*c := by
    induction n with
    | zero => simp
    | succ n ih => have h := hd n; push_cast; rw [ih] at h; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2*B)
  have h0 := abs_le.mp (hb 0)
  have h1 := abs_le.mp (hb n)
  rw [he n] at h1
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hc' : c ≤ -1 := by exact Int.add_le_zero_iff_le_neg.mp hc
    nlinarith
  · exact hc
  · have hc' : 1 ≤ c := by exact Int.le_of_sub_one_lt hc
    nlinarith

private def H (C : ℤ → ℤ) (p q n : ℤ) := fwdDiff (p : ℤ) C n * fwdDiff (q : ℤ) C n

private theorem flux_coboundary (C : ℤ → ℤ) (p q : ℕ) (n : ℤ)
    (hz : ∀ j : ℕ, j < p+q → fwdDiff (p : ℤ) C (n-j+q) = fwdDiff (p : ℤ) C (n-j)) :
    flux C p q n = birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q n - birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q (n-p) := by
  have h2 : birkhoffSum (Order.pred : ℤ → ℤ) (H2 C p q) p n = birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) p n := by
    simp only [birkhoffSum, Order.pred_iterate]
    apply sum_congr rfl
    intro j hj
    have he := mixed_comm C p q (n-j)
    rw [hz j (by have := mem_range.mp hj; omega)] at he
    unfold H2 H
    have hg : fwdDiff (q : ℤ) C (n-j+p) = fwdDiff (q : ℤ) C (n-j) := by omega
    rw [hg]
  have h3 : birkhoffSum (Order.pred : ℤ → ℤ) (H3 C p q) q n = birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q n := by
    simp only [birkhoffSum, Order.pred_iterate]
    apply sum_congr rfl
    intro j hj
    unfold H3 H
    rw [hz j (by have := mem_range.mp hj; omega)]
  have h4 : birkhoffSum (Order.pred : ℤ → ℤ) (H4 C p q) (p+q) n = birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) (p+q) n := by
    simp only [birkhoffSum, Order.pred_iterate]
    apply sum_congr rfl
    intro j hj
    have he := mixed_comm C p q (n-j)
    rw [hz j (mem_range.mp hj)] at he
    unfold H4 H
    have hg : fwdDiff (q : ℤ) C (n-j+p) = fwdDiff (q : ℤ) C (n-j) := by omega
    rw [hz j (mem_range.mp hj), hg]
  unfold flux
  rw [h2, h3, h4, backSum_add]
  ring

/-- No finite defects: the monotone integer flux has zero values on both tails. -/
private theorem no_defects (C : ℤ → ℤ) (p q : ℕ)
    (ha : ∀ n, (fwdDiff (p : ℤ) C n - fwdDiff (p : ℤ) C (n - p)) * (fwdDiff (q : ℤ) C n - fwdDiff (q : ℤ) C (n - q)) = 0)
    (hf : ∀ n, |fwdDiff (p : ℤ) C n| ≤ p) (hg : ∀ n, |fwdDiff (q : ℤ) C n| ≤ q) :
    ∀ n, fwdDiff (p : ℤ) C (n+q) = fwdDiff (p : ℤ) C n := by
  obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := bounded_extrema _ _ (flux_bounded C p q hf hg)
  have anti := flux_antitone C p q ha
  have right_const (n : ℤ) (hn : lo ≤ n) : flux C p q n = flux C p q lo :=
    le_antisymm (anti hn) (hlo _)
  have left_const (n : ℤ) (hn : n ≤ hi) : flux C p q n = flux C p q hi :=
    le_antisymm (hhi _) (anti hn)
  obtain ⟨L, R, left_zero, right_zero⟩ := finite_defects C p q ha hf hg
  have hb (n : ℤ) : |birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q n| ≤ (q : ℤ) * (p*q) := by
    apply backSum_bound
    intro x
    unfold H
    rw [abs_mul]
    exact mul_le_mul (hf _) (hg _) (abs_nonneg _) (Int.natCast_nonneg p)
  have hr : flux C p q lo = 0 := by
    let N : ℤ := max lo R + p + q + 1
    apply bounded_drift_zero (fun t => birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q (N + t*p)) _ _ (fun t => hb _)
    intro t
    have hN : lo ≤ N + (t+1 : ℕ)*p := by
      dsimp [N]
      have hp : (0 : ℤ) ≤ (t+1 : ℕ)*p := by exact Int.zero_le_ofNat ((t + 1) * p)
      have hm := le_max_left lo R
      push_cast at hp ⊢
      omega
    have hc := flux_coboundary C p q (N + (t+1 : ℕ)*p) (by
      intro j hj
      apply right_zero
      dsimp [N]
      have hm := le_max_right lo R
      push_cast at *
      have hp : (0 : ℤ) ≤ (t+1 : ℕ)*p := by exact Int.zero_le_ofNat ((t + 1) * p)
      push_cast at hp
      omega)
    rw [right_const _ hN] at hc
    convert hc.symm using 1; congr 2; push_cast; ring
  have hl : flux C p q hi = 0 := by
    have hz : -flux C p q hi = 0 := by
      apply bounded_drift_zero (fun t => birkhoffSum (Order.pred : ℤ → ℤ) (H C p q) q (min hi L - t*p)) _ _ (fun t => hb _)
      intro t
      have hN : min hi L - (t : ℤ)*p ≤ hi := by
        have hp : (0 : ℤ) ≤ t*p := by exact Int.zero_le_ofNat (t * p)
        have hm := min_le_left hi L
        omega
      have hc := flux_coboundary C p q (min hi L - t*p) (by
        intro j hj
        apply left_zero
        have hp : (0 : ℤ) ≤ t*p := by exact Int.zero_le_ofNat (t * p)
        have hj' : (0 : ℤ) ≤ j := by exact Int.natCast_nonneg j
        have hm := min_le_right hi L
        omega)
      rw [left_const _ hN] at hc
      have he : min hi L - (t : ℤ)*p - p = min hi L - (t+1 : ℕ)*p := by push_cast; ring
      rw [he] at hc
      linarith
    omega
  intro n
  have he := flux_step C p q ha n
  have hzero (x : ℤ) : flux C p q x = 0 := by have := hlo x; have := hhi x; omega
  rw [hzero n, hzero (n-1)] at he
  nlinarith [sq_nonneg (fwdDiff (p : ℤ) C (n+q) - fwdDiff (p : ℤ) C n)]

private theorem F_add (C : ℤ → ℤ) (u v n : ℤ) :
    fwdDiff ((u+v) : ℤ) C n = fwdDiff (u : ℤ) C n + fwdDiff (v : ℤ) C (n+u) := by
  unfold fwdDiff
  rw [add_assoc]
  ring

private theorem periodic_multiple_window (C : ℤ → ℤ) (p q : ℕ)
    (hp : Function.Periodic (fwdDiff (p : ℤ) C) q) (t : ℕ) :
    Function.Periodic (fwdDiff ((p*t) : ℤ) C) q := by
  induction t with
  | zero => intro n; simp [fwdDiff]
  | succ t ih =>
    intro n
    have he : (p:ℤ)*(t+1:ℕ) = (p:ℤ)*t + p := by push_cast; ring
    rw [he, F_add, F_add, ih n]
    rw [show n+(q:ℤ)+(p:ℤ)*t = (n+(p:ℤ)*t)+q from Int.add_right_comm n (q:ℤ) ((p:ℤ)*t), hp]

private theorem periodic_increment (C : ℤ → ℤ) (p q m : ℕ)
    (hpm : p ∣ m) (hqm : q ∣ m)
    (hp : Function.Periodic (fwdDiff (p : ℤ) C) q)
    (ha : ∀ n, 0 ≤ C (n+1)-C n ∧ C (n+1)-C n ≤ 1) :
    Function.Periodic (fun n => C (n+1)-C n) m := by
  have hm : Function.Periodic (fwdDiff (m : ℤ) C) q := by
    obtain ⟨t,rfl⟩ := hpm
    exact periodic_multiple_window C p q hp t
  have hJ : Function.Periodic (fwdDiff (m : ℤ) C) m := by
    obtain ⟨t,ht⟩ := hqm
    have h := hm.nat_mul t
    simpa [ht, Nat.cast_mul, mul_comm] using h
  have hdouble (n : ℤ) : C (n+2*m)-C n = 2*fwdDiff (m : ℤ) C n := by
    have h := hJ n
    unfold fwdDiff at *
    rw [show n+(m:ℤ)+m = n+2*m by ring] at h
    linarith
  have hconst (n : ℤ) : fwdDiff (m : ℤ) C (n+1) = fwdDiff (m : ℤ) C n := by
    have h0 := hdouble n
    have h1 := hdouble (n+1)
    rw [show n+1+2*(m:ℤ) = n+2*m+1 from Int.add_right_comm n 1 (2*(m:ℤ))] at h1
    have h2 := ha n
    have h3 := ha (n+2*m)
    have hd : (C (n+2*m+1)-C (n+2*m)) - (C (n+1)-C n) =
        2*(fwdDiff (m : ℤ) C (n+1)-fwdDiff (m : ℤ) C n) := by linarith
    omega
  intro n
  have hc := hconst n
  unfold fwdDiff at hc
  rw [show n+1+(m:ℤ) = n+m+1 from Int.add_right_comm n 1 (m:ℤ)] at hc
  linarith

private theorem square_count_difference {r l : ℕ} {w : ℤ → Fin r} {n : ℤ}
    (h : CentralAbelianPower w 1 l n) (a : Fin r) :
    fwdDiff (l : ℤ) (cumulative ((fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)))) n - fwdDiff (l : ℤ) (cumulative ((fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)))) (n-l) = 0 := by
  have he := h.2 1 (Nat.one_lt_succ_succ 0) a
  simp only [Nat.cast_one, mul_one, one_mul] at he
  rw [show n-(l:ℤ)+1+l = n+1 by ring] at he
  rw [count_cumulative, count_cumulative]
  exact sub_eq_zero.mpr (by exact_mod_cast he)

private theorem squares_lcm_period {r : ℕ} (w : ℤ → Fin r) (p q : ℕ)
    (hs : ∀ n : ℤ, CentralAbelianPower w 1 p n ∨ CentralAbelianPower w 1 q n) :
    Function.Periodic w (Nat.lcm p q : ℕ) := by
  intro n
  let a := w n
  let C := cumulative ((fun n => (Pi.single a (1 : ℤ) : Fin r → ℤ) (w n)))
  have hprod (i : ℤ) :
      (fwdDiff (p : ℤ) C i - fwdDiff (p : ℤ) C (i-p)) * (fwdDiff (q : ℤ) C i - fwdDiff (q : ℤ) C (i-q)) = 0 := by
    rcases hs i with h | h
    · rw [square_count_difference h a, zero_mul]
    · rw [square_count_difference h a, mul_zero]
  have hp : Function.Periodic (fwdDiff (p : ℤ) C) q :=
    no_defects C p q hprod (count_bound w a · p) (count_bound w a · q)
  have hbound (i : ℤ) : 0 ≤ C (i+1)-C i ∧ C (i+1)-C i ≤ 1 := by
    rw [cumulative_step]
    simp only [Pi.single_apply]
    split <;> omega
  have hi := periodic_increment C p q (Nat.lcm p q)
    (Nat.dvd_lcm_left p q) (Nat.dvd_lcm_right p q) hp hbound (n-1)
  change C (n-1+↑(Nat.lcm p q)+1)-C (n-1+↑(Nat.lcm p q)) = C (n-1+1)-C (n-1) at hi
  rw [cumulative_step, cumulative_step] at hi
  have h1 : n-1+(Nat.lcm p q:ℕ)+1 = n+(Nat.lcm p q:ℕ) := by
    simpa only [sub_add_eq_add_sub] using Int.sub_add_cancel (n + (Nat.lcm p q : ℕ)) 1
  have h2 : n-1+1 = n := by exact Int.sub_add_cancel n 1
  rw [h1, h2] at hi
  by_contra hne
  simp [a, hne] at hi

theorem result : claim := by
  intro k hk r w p q h
  have hs (i : ℤ) : CentralAbelianPower w 1 p i ∨ CentralAbelianPower w 1 q i :=
    (h i).imp (central_square hk) (central_square hk)
  by_cases hp : 0 < p
  · by_cases hq : 0 < q
    · exact ⟨Nat.lcm p q, Nat.lcm_pos hp hq, squares_lcm_period w p q hs⟩
    · have hh (i : ℤ) : CentralAbelianPower w 1 p i := by
        rcases hs i with h | h
        · exact h
        · exact False.elim (hq h.1)
      refine ⟨p, hp, ?_⟩
      simpa using squares_lcm_period w p p (fun i => Or.inl (hh i))
  · have hh (i : ℤ) : CentralAbelianPower w 1 q i := by
      rcases hs i with h | h
      · exact False.elim (hp h.1)
      · exact h
    refine ⟨q, (hh 0).1, ?_⟩
    simpa using squares_lcm_period w q q (fun i => Or.inl (hh i))

end D5.S1.Words.TwoCenteredAbelianPeriods
