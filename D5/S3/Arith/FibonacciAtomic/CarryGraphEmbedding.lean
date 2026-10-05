/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphEmbedding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Canonical minimum-anchor embedding of positive real laws in the original carry graph. -/

import D5.S3.Arith.FibonacciAtomic.DyadicSupportLines
import Mathlib.Analysis.Real.OfDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding

open scoped BigOperators

/-- The integer residual width and the size of the minimum-anchor equality group. -/
structure State where
  r : ℤ
  e : ℤ

/-- Parameters of one column: anchor bit, departing equal labels, larger one-labels. -/
structure Action where
  b : ℤ
  h : ℤ
  c : ℤ

/-- All states of the original carry graph, including unreachable states. -/
def IsState (m : ℕ) (s : State) : Prop :=
  0 ≤ s.r ∧ s.r ≤ (m : ℤ) - 1 ∧ 1 ≤ s.e ∧ s.e ≤ m

/-- A single continuing root cylinder and all labels in the equality group. -/
def root (m : ℕ) : State := ⟨1, m⟩

/-- The number of labels with a one in the next column. -/
def ones (s : State) (a : Action) : ℤ :=
  if a.b = 1 then s.e + a.c else a.h + a.c

/-- The residual recurrence and the removal of departing equality-group labels. -/
def successor (s : State) (a : Action) : State :=
  ⟨2 * s.r - ones s a, s.e - a.h⟩

/-- Exactly the two action rows, together with the successor's state bounds. -/
def Legal (m : ℕ) (s : State) (a : Action) : Prop :=
  IsState m s ∧
    ((a.b = 1 ∧ a.h = 0 ∧ 0 ≤ a.c ∧ a.c ≤ (m : ℤ) - s.e) ∨
      (a.b = 0 ∧ 0 ≤ a.h ∧ a.h ≤ s.e - 1 ∧
        0 ≤ a.c ∧ a.c ≤ (m : ℤ) - s.e)) ∧
    IsState m (successor s a)

/-- An infinite sequence of states and column actions; column zero produces bit one. -/
structure Path where
  state : ℕ → State
  action : ℕ → Action

/-- A path begins at the root and takes a legal action at every depth. -/
def IsRootPath (m : ℕ) (γ : Path) : Prop :=
  γ.state 0 = root m ∧ ∀ d,
    Legal m (γ.state d) (γ.action d) ∧
      γ.state (d + 1) = successor (γ.state d) (γ.action d)

/-- The anchor value, with the first column bit weighted by one half. -/
noncomputable def anchorValue (γ : Path) : ℝ :=
  ∑' d : ℕ, (γ.action d).b / (2 : ℝ) ^ (d + 1)

/-- The whole-column residual tail cost, including the root term. -/
noncomputable def pathCost (γ : Path) : ℝ :=
  ∑' d : ℕ, (γ.state d).r / (2 : ℝ) ^ d

/-- Every state has an action, zero residual is absorbing, and every positive real
law has its canonical root path for each choice of minimum anchor. -/
theorem result (m : ℕ) (hm : 2 ≤ m) :
    (∀ s : State, IsState m s → ∃ a : Action, Legal m s a) ∧
    (∀ (s : State) (a : Action), s.r = 0 → Legal m s a →
      a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s) ∧
    (∀ (s : State) (a : Action), s.e = 1 → Legal m s a → a.h = 0) ∧
    (∀ (p : Fin m → ℝ), (∀ i, 0 < p i) → (∑ i, p i = 1) →
      ∀ k : Fin m, (∀ i, p k ≤ p i) → ∃ γ : Path,
        IsRootPath m γ ∧
        (∀ d, ((γ.state d).r : ℝ) = DyadicSupportLines.residual p d) ∧
        (∀ d, (γ.state d).e =
          ((Finset.univ.filter (fun i => ⌊(2 : ℝ) ^ d * p i⌋ =
            ⌊(2 : ℝ) ^ d * p k⌋)).card : ℤ)) ∧
        (∀ d, (γ.action d).b =
          ⌊(2 : ℝ) ^ (d + 1) * p k⌋ - 2 * ⌊(2 : ℝ) ^ d * p k⌋) ∧
        anchorValue γ = p k ∧ pathCost γ = DyadicSupportLines.cost p) := by
  classical
  have available (s : State) (hs : IsState m s) : ∃ a : Action, Legal m s a := by
    let q := max 0 (2 * s.r - ((m : ℤ) - 1))
    let h := min q (s.e - 1)
    refine ⟨⟨0, h, q - h⟩, hs, Or.inr ?_, ?_⟩
    · dsimp only
      dsimp [q, h]
      rcases hs with ⟨hr0, hr1, he0, he1⟩
      omega
    · dsimp [IsState, successor, ones, q, h]
      rcases hs with ⟨hr0, hr1, he0, he1⟩
      omega
  have absorbing (s : State) (a : Action) (hr : s.r = 0) (ha : Legal m s a) :
      a.b = 0 ∧ a.h = 0 ∧ a.c = 0 ∧ successor s a = s := by
    rcases ha with ⟨hs, ha, hs'⟩
    rcases hs with ⟨hr0, hr1, he0, he1⟩
    have hr' := hs'.1
    dsimp [successor, ones] at hr'
    rcases ha with ha | ha
    · rcases ha with ⟨hb, hh, hc0, hc1⟩
      rw [hb, if_pos rfl, hr] at hr'
      omega
    · rcases ha with ⟨hb, hh0, hh1, hc0, hc1⟩
      rw [hb, if_neg (by norm_num), hr] at hr'
      have hh : a.h = 0 := by omega
      have hc : a.c = 0 := by omega
      refine ⟨hb, hh, hc, ?_⟩
      cases s
      simp_all [successor, ones]
  refine ⟨available, absorbing, ?_, ?_⟩
  · intro s a he ha
    rcases ha.2.1 with ha | ha
    · exact ha.2.1
    · have H := ha.2.1
      have H' := ha.2.2.1
      omega
  intro p hp hs k hk
  letI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let n : ℕ → Fin m → ℤ := fun d i => ⌊(2 : ℝ) ^ d * p i⌋
  let bit : ℕ → Fin m → ℤ := fun d i => n (d + 1) i - 2 * n d i
  let eqg : ℕ → Fin m → Prop := fun d i => n d i = n d k
  let E : ℕ → ℤ := fun d => ∑ i, if eqg d i then 1 else 0
  let H : ℕ → ℤ := fun d =>
    ∑ i, if eqg d i ∧ bit d i = 1 ∧ bit d k = 0 then 1 else 0
  let C : ℕ → ℤ := fun d => ∑ i, if ¬ eqg d i ∧ bit d i = 1 then 1 else 0
  let R : ℕ → ℤ := fun d => (2 : ℤ) ^ d - ∑ i, n d i
  have atom_lt_one (i : Fin m) : p i < 1 := by
    obtain ⟨j, hj⟩ := exists_ne i
    have Hsum := Finset.single_lt_sum (s := Finset.univ) (f := p)
      hj (Finset.mem_univ i) (Finset.mem_univ j) (hp j) (fun l _ _ => (hp l).le)
    rwa [hs] at Hsum
  have floor_zero (i : Fin m) : n 0 i = 0 := by
    dsimp [n]
    simp only [pow_zero, one_mul]
    exact Int.floor_eq_zero_iff.mpr ⟨(hp i).le, atom_lt_one i⟩
  have bit_bounds (d : ℕ) (i : Fin m) : 0 ≤ bit d i ∧ bit d i ≤ 1 := by
    have div : n (d + 1) i / 2 = n d i := by
      dsimp only [n]
      rw [pow_succ', mul_assoc]
      exact Int.natCast_mul_floor_div_cancel (n := 2) (by norm_num) _
    dsimp only [bit]
    omega
  have min_prefix (d : ℕ) (i : Fin m) : n d k ≤ n d i :=
    Int.floor_mono (mul_le_mul_of_nonneg_left (hk i) (by positivity))
  have group_step (d : ℕ) (i : Fin m) :
      eqg (d + 1) i ↔ eqg d i ∧ bit d i = bit d k := by
    have Hi := bit_bounds d i
    have Hk := bit_bounds d k
    have Hmin := min_prefix d i
    dsimp only [eqg, bit] at *
    omega
  have equal_one (d : ℕ) (i : Fin m) (he : eqg d i) (hb : bit d k = 1) :
      bit d i = 1 := by
    have Hmin := min_prefix (d + 1) i
    have Hi := bit_bounds d i
    dsimp only [eqg, bit] at *
    omega
  have residual_bounds (d : ℕ) : 0 ≤ R d ∧ R d ≤ (m : ℤ) - 1 := by
    have sumscale : ∑ i, (2 : ℝ) ^ d * p i = (2 : ℝ) ^ d := by
      rw [← Finset.mul_sum, hs, mul_one]
    have lower := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => Int.floor_le ((2 : ℝ) ^ d * p i))
    have upper := Finset.sum_lt_sum_of_nonempty
      (s := Finset.univ) ⟨k, Finset.mem_univ k⟩
      (fun i _ => Int.lt_floor_add_one ((2 : ℝ) ^ d * p i))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, sumscale] at lower upper
    have lo : (0 : ℝ) ≤ (R d : ℝ) := by
      dsimp only [R, n]
      push_cast
      linarith only [lower]
    have hi : (R d : ℝ) < m := by
      dsimp only [R, n]
      push_cast
      linarith only [upper]
    have lo' : 0 ≤ R d := by exact_mod_cast lo
    have hi' : R d < m := by exact_mod_cast hi
    exact ⟨lo', by omega⟩
  have group_bounds (d : ℕ) : 1 ≤ E d ∧ E d ≤ m := by
    have nonneg (i : Fin m) : (0 : ℤ) ≤ if eqg d i then 1 else 0 := by
      split_ifs <;> omega
    have lower := Finset.single_le_sum (s := Finset.univ) (f := fun i =>
      if eqg d i then (1 : ℤ) else 0) (fun i _ => nonneg i) (Finset.mem_univ k)
    have upper := Finset.sum_le_sum (s := Finset.univ) (f := fun i =>
      if eqg d i then (1 : ℤ) else 0) (g := fun _ => 1)
      (fun i _ => by split_ifs <;> omega)
    simp only [eqg, if_pos rfl] at lower
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at upper
    exact ⟨lower, upper⟩
  have column (d : ℕ) :
      0 ≤ H d ∧ H d ≤ E d - 1 ∧ 0 ≤ C d ∧ C d ≤ (m : ℤ) - E d ∧
      (bit d k = 1 → H d = 0) ∧
      E (d + 1) = E d - H d ∧
      (∑ i, bit d i) = if bit d k = 1 then E d + C d else H d + C d := by
    have hb := bit_bounds d k
    have nonneg (i : Fin m) :
        (0 : ℤ) ≤ (if eqg d i ∧ bit d i = 1 ∧ bit d k = 0 then 1 else 0) ∧
        (0 : ℤ) ≤ (if ¬ eqg d i ∧ bit d i = 1 then 1 else 0) := by
      constructor <;> split_ifs <;> omega
    have strict : H d < E d := by
      apply Finset.sum_lt_sum
      · intro i hi
        split_ifs <;> simp_all <;> omega
      · refine ⟨k, Finset.mem_univ k, ?_⟩
        simp [eqg]
        omega
    have capacity : C d + E d ≤ m := by
      dsimp only [C, E]
      rw [← Finset.sum_add_distrib]
      calc
        _ ≤ ∑ _ : Fin m, (1 : ℤ) := Finset.sum_le_sum fun i _ => by
          split_ifs <;> simp_all <;> omega
        _ = m := by simp
    have zero (hbit : bit d k = 1) : H d = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hbit]
    have step : E (d + 1) = E d - H d := by
      dsimp only [E, H]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hg := group_step d i
      have hone := equal_one d i
      have hbi := bit_bounds d i
      rcases (show bit d i = 0 ∨ bit d i = 1 by omega) with hbi | hbi <;>
        rcases (show bit d k = 0 ∨ bit d k = 1 by omega) with hbk | hbk <;>
        by_cases he : eqg d i <;>
        simp_all only [hg, he, hbi, hbk, and_true, and_false,
          true_and, false_and, not_true_eq_false, not_false_eq_true,
          Int.reduceEq, ite_true, ite_false] <;> omega
    have total : (∑ i, bit d i) =
        if bit d k = 1 then E d + C d else H d + C d := by
      by_cases hbit : bit d k = 1
      · rw [if_pos hbit]
        dsimp only [E, C]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hone := equal_one d i
        have hbi := bit_bounds d i
        by_cases he : eqg d i
        · rw [if_pos he, if_neg (by tauto)]
          have := hone he hbit
          omega
        · rw [if_neg he]
          by_cases hi1 : bit d i = 1
          · rw [if_pos ⟨he, hi1⟩, hi1]
            norm_num
          · rw [if_neg (by tauto)]
            omega
      · rw [if_neg hbit]
        have hbit0 : bit d k = 0 := by omega
        dsimp only [H, C]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        have hbi := bit_bounds d i
        by_cases he : eqg d i <;> by_cases hi1 : bit d i = 1 <;>
          simp only [he, hi1, hbit0, and_true, and_false, true_and,
            false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> omega
    exact ⟨Finset.sum_nonneg (fun i _ => (nonneg i).1), by omega,
      Finset.sum_nonneg (fun i _ => (nonneg i).2), by omega, zero, step, total⟩
  let γ : Path := ⟨fun d => ⟨R d, E d⟩, fun d => ⟨bit d k, H d, C d⟩⟩
  have root_eq : γ.state 0 = root m := by
    dsimp [γ, root, R, E, eqg]
    simp [floor_zero]
  have state_bounds (d : ℕ) : IsState m (γ.state d) :=
    ⟨(residual_bounds d).1, (residual_bounds d).2,
      (group_bounds d).1, (group_bounds d).2⟩
  have next (d : ℕ) : γ.state (d + 1) = successor (γ.state d) (γ.action d) := by
    have hc := column d
    have recurrence : R (d + 1) = 2 * R d - ∑ i, bit d i := by
      dsimp only [R, bit]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, pow_succ]
      ring
    dsimp only [γ, successor, ones]
    rw [← hc.2.2.2.2.2.1, ← hc.2.2.2.2.2.2, recurrence]
  have path : IsRootPath m γ := by
    refine ⟨root_eq, fun d => ⟨?_, next d⟩⟩
    refine ⟨state_bounds d, ?_, ?_⟩
    · change (bit d k = 1 ∧ H d = 0 ∧ 0 ≤ C d ∧ C d ≤ (m : ℤ) - E d) ∨
        (bit d k = 0 ∧ 0 ≤ H d ∧ H d ≤ E d - 1 ∧
          0 ≤ C d ∧ C d ≤ (m : ℤ) - E d)
      have hb := bit_bounds d k
      have hc := column d
      by_cases hbit : bit d k = 1
      · exact Or.inl ⟨hbit, hc.2.2.2.2.1 hbit, hc.2.2.1, hc.2.2.2.1⟩
      · exact Or.inr ⟨by omega, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
    · rw [← next d]
      exact state_bounds (d + 1)
  have real_residual (d : ℕ) : ((γ.state d).r : ℝ) =
      DyadicSupportLines.residual p d := by
    simp [γ, R, n, DyadicSupportLines.residual]
  have real_bit (d : ℕ) : ((γ.action d).b : ℝ) = (Real.digits (p k) 2 d : ℝ) := by
    have div : n (d + 1) k / 2 = n d k := by
      dsimp only [n]
      rw [pow_succ', mul_assoc]
      exact Int.natCast_mul_floor_div_cancel (n := 2) (by norm_num) _
    have rem : bit d k = n (d + 1) k % 2 := by dsimp only [bit]; omega
    have hn : 0 ≤ p k * (2 : ℝ) ^ (d + 1) :=
      mul_nonneg (hp k).le (by positivity)
    have eq : ((Real.digits (p k) 2 d).val : ℤ) = bit d k := by
      simp only [Real.digits, Fin.val_ofNat, Int.natCast_mod, Nat.cast_ofNat]
      rw [Int.natCast_floor_eq_floor hn, mul_comm]
      exact rem.symm
    exact_mod_cast eq.symm
  have anchor_eq : anchorValue γ = p k := by
    unfold anchorValue
    simp_rw [real_bit, div_eq_mul_inv]
    exact Real.ofDigits_digits (b := 2) (by norm_num) ⟨(hp k).le, atom_lt_one k⟩
  refine ⟨γ, path, real_residual, ?_, fun _ => rfl, anchor_eq, ?_⟩
  · intro d
    dsimp only [γ, E, eqg, n]
    rw [Finset.card_filter]
    simp
  · unfold pathCost DyadicSupportLines.cost
    simp_rw [real_residual]

end D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
