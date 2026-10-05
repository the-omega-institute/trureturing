/- GID: D5/S3/Arith/FibonacciAtomic/TriangularSharedImplementation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TriangularSharedImplementation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Immediate-output sharing for every legal stationary triangular table. -/

import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation

open scoped BigOperators
open TriangularPathNormalization

/-- A fixed action at every aggregate state, including zero residual states. -/
structure Table (m : ℕ) where
  action : State → Action
  legal : ∀ s, 0 < s.e → s.r < s.e → s.e ≤ m → Legal m s (action s)

/-- The original slot coordinates e, r, k; empty Fin r removes zero residual slots. -/
def Slot (m : ℕ) := Σ e : Fin (m + 1), Σ r : Fin e.val, Fin r.val

/-- The aggregate state of an original slot. -/
def aggregate {m : ℕ} (s : Slot m) : State := ⟨s.2.1.val, s.1.val⟩

/-- Slots with the same one-bit ordered terminal pair can share a vertex. -/
def Immediate {m : ℕ} (s : Slot m) : Prop :=
  s.1.val ≤ 2 * s.2.1.val ∧ s.2.2.val < s.1.val / 2

/-- Shared one-bit vertices and all remaining singleton slots. -/
def SharedActive (m : ℕ) := Fin (m / 2) ⊕ {s : Slot m // ¬Immediate s}

local notation "Original" m:arg => (Slot m ⊕ Fin m)
local notation "Shared" m:arg => (SharedActive m ⊕ Fin m)

/-- Activities have no terminal label; distinct terminals retain their own labels. -/
def color {m : ℕ} {A : Type} : A ⊕ Fin m → Option (Fin m)
  | .inl _ => none
  | .inr i => some i

/-- The source root has coordinates (r,e,k)=(1,m,0). -/
def root (m : ℕ) (hm : 2 ≤ m) : Original m :=
  .inl ⟨⟨m, by omega⟩, ⟨⟨1, by change 1 < m; omega⟩, ⟨0, by change 0 < 1; omega⟩⟩⟩

/-- Ordered output count and the successor prescribed by the original column. -/
def outputCount (a : Action) (e : ℕ) : ℕ :=
  match a with
  | .one => e
  | .zero h => h

/-- Label at position z in the ordered output list, represented with zero-based labels. -/
def outputLabel (a : Action) (e z : ℕ) : ℕ :=
  match a with
  | .one => z
  | .zero h => e - h + z

/-- Every active edge consumes one bit; terminal loops are absorbing extensions. -/
def originalStep {m : ℕ} (f : Table m) : Original m → Fin 2 → Original m
  | .inr i, _ => .inr i
  | .inl s, u => by
    let a := f.action (aggregate s)
    let z := 2 * s.2.2.val + u.val
    let q := outputCount a s.1.val
    have hl := f.legal (aggregate s) (by change 0 < s.1.val; have H := s.2.1.isLt; omega)
      s.2.1.isLt (by change s.1.val ≤ m; have H := s.1.isLt; omega)
    have action_legal : (match a with
        | .one => s.1.val ≤ 2 * s.2.1.val
        | .zero h => 2 * s.2.1.val < s.1.val ∧ h ≤ 2 * s.2.1.val) := by
      simpa only [aggregate] using hl.2.2.2
    have hz : z < 2 * s.2.1.val := by
      have H := s.2.2.isLt
      have H' := u.isLt
      dsimp [z]
      omega
    if h : z < q then
      exact .inr ⟨outputLabel a s.1.val z, by
        cases ha : a with
        | one =>
          simp only [outputLabel, ha]
          have Hq : q = s.1.val := by simp [q, ha, outputCount]
          have He : s.1.val ≤ m := hl.2.2.1
          omega
        | zero h' =>
          have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
            simpa only [ha] using action_legal
          simp only [outputLabel, ha]
          dsimp [q] at h
          simp only [outputCount, ha] at h
          have He := hl.2.2.1
          dsimp [aggregate] at He
          omega⟩
    else
      exact .inl ⟨⟨(successor (aggregate s) a).e, by
        cases ha : a <;> simp [successor, ha, aggregate] <;> omega⟩,
        ⟨⟨(successor (aggregate s) a).r, by
          cases ha : a with
          | one =>
            have H : s.1.val ≤ 2 * s.2.1.val := by
              simpa only [ha] using action_legal
            simp [successor, ha, aggregate]
            have Hr := s.2.1.isLt
            omega
          | zero h' =>
            have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
              simpa only [ha] using action_legal
            simp [successor, ha, aggregate]
            omega⟩,
          ⟨z - q, by
            cases ha : a with
            | one =>
              have H : s.1.val ≤ 2 * s.2.1.val := by
                simpa only [ha] using action_legal
              simp [successor, ha, aggregate]
              dsimp [q] at h ⊢
              simp only [outputCount, ha] at h ⊢
              omega
            | zero h' =>
              have H : 2 * s.2.1.val < s.1.val ∧ h' ≤ 2 * s.2.1.val := by
                simpa only [ha] using action_legal
              simp [successor, ha, aggregate]
              dsimp [q] at h ⊢
              simp only [outputCount, ha] at h ⊢
              omega⟩⟩⟩

/-- The projection merges precisely the immediate slots of a fixed k. -/
def projection {m : ℕ} : Original m → Shared m
  | .inr i => .inr i
  | .inl s => by
    letI : Decidable (Immediate s) := inferInstanceAs
      (Decidable (s.1.val ≤ 2 * s.2.1.val ∧ s.2.2.val < s.1.val / 2))
    exact if h : Immediate s then .inl (.inl ⟨s.2.2.val, by
      have He := s.1.isLt
      have Hk := h.2
      omega⟩) else .inl (.inr ⟨s, h⟩)

/-- Shared immediate vertices output their ordered pair; singletons use the projected successor. -/
def sharedStep {m : ℕ} (f : Table m) : Shared m → Fin 2 → Shared m
  | .inr i, _ => .inr i
  | .inl (.inl k), u => .inr ⟨2 * k.val + u.val, by
      have H := k.isLt
      have H' := u.isLt
      omega⟩
  | .inl (.inr s), u => projection (originalStep f (.inl s.val) u)

/-- The state after a finite prefix of an infinite bit stream. -/
def trace {A : Type} (δ : A → Fin 2 → A) (s : A) (ω : ℕ → Fin 2) (n : ℕ) : A :=
  (List.ofFn (fun j : Fin n => ω j.val)).foldl δ s

/-- First terminal label and consumed length, including a terminal initial state at length zero. -/
def FirstStop {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) (i : Fin m) (n : ℕ) : Prop :=
  c (trace δ s ω n) = some i ∧ ∀ j < n, c (trace δ s ω j) = none

/-- Paid bits among a prefix: precisely the edges whose source is still active. -/
def charged {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => c (trace δ s ω j) = none)).card

/-- Nontermination means every prefix is still active. -/
def Nonstop {m : ℕ} {A : Type} (δ : A → Fin 2 → A) (c : A → Option (Fin m))
    (s : A) (ω : ℕ → Fin 2) : Prop := ∀ n, c (trace δ s ω n) = none

/-- Activity states obtainable from the root by a finite input word. -/
def ReachableActive {m : ℕ} (δ : Shared m → Fin 2 → Shared m) (s : Shared m) :=
  {a : SharedActive m // ∃ w : List (Fin 2), w.foldl δ s = .inl a}

/-- The general sufficient activity bound; subtraction removes all immediate slots. -/
def bound (m : ℕ) : ℕ :=
  m * (m - 1) * (m + 1) / 6 - (∑ e ∈ Finset.range (m + 1), (e / 2) ^ 2) + m / 2

/-- Every stationary legal table has an explicit color-preserving shared implementation,
with identical first-stop responses and bills on every stream and the stated general bound. -/
theorem result (m : ℕ) (hm : 2 ≤ m) (f : Table m) :
    ∃ (π : Original m → Shared m) (δ : Shared m → Fin 2 → Shared m),
      Function.Surjective π ∧
      (∀ s, color (π s) = color s) ∧
      (∀ s u, π (originalStep f s u) = δ (π s) u) ∧
      (∀ ω i n, FirstStop (originalStep f) color (root m hm) ω i n ↔
        FirstStop δ color (π (root m hm)) ω i n) ∧
      (∀ ω n, charged (originalStep f) color (root m hm) ω n =
        charged δ color (π (root m hm)) ω n) ∧
      (∀ ω i n, FirstStop (originalStep f) color (root m hm) ω i n →
        charged (originalStep f) color (root m hm) ω n = n) ∧
      (∀ ω, Nonstop (originalStep f) color (root m hm) ω ↔
        Nonstop δ color (π (root m hm)) ω) ∧
      Nat.card (SharedActive m) = bound m ∧
      Nat.card (ReachableActive δ (π (root m hm))) ≤ bound m ∧
      Nat.card (Fin m) = m ∧
      (∀ q : ℕ, 1 ≤ q → bound (2 * q) = (2 * q ^ 3 + q) / 3 ∧
        bound (2 * q + 1) = (2 * q ^ 3 + 3 * q ^ 2 + 4 * q) / 3) := by
  classical
  letI : Fintype (Slot m) := inferInstanceAs (Fintype
    (Σ e : Fin (m + 1), Σ r : Fin e.val, Fin r.val))
  letI : Fintype (SharedActive m) := inferInstanceAs
    (Fintype (Fin (m / 2) ⊕ {s : Slot m // ¬Immediate s}))
  have immediate_action (s : Slot m) (hi : Immediate s) :
      f.action (aggregate s) = .one := by
    have hl := f.legal (aggregate s) (by change 0 < s.1.val; have H := s.2.1.isLt; omega)
      s.2.1.isLt (by change s.1.val ≤ m; have H := s.1.isLt; omega)
    cases ha : f.action (aggregate s) with
    | one => rfl
    | zero h =>
      have H : 2 * s.2.1.val < s.1.val ∧ h ≤ 2 * s.2.1.val := by
        have H := hl.2.2.2
        rw [ha] at H
        simpa only [aggregate] using H
      have H' := hi.1
      omega
  have immediate_step (s : Slot m) (hi : Immediate s) (u : Fin 2) :
      originalStep f (.inl s) u = .inr ⟨2 * s.2.2.val + u.val, by
        have H := hi.2
        have He := s.1.isLt
        have Hu := u.isLt
        omega⟩ := by
    have hz : 2 * s.2.2.val + u.val < s.1.val := by
      have H := hi.2
      have Hu := u.isLt
      omega
    simp [originalStep, immediate_action s hi, outputCount, outputLabel, hz]
  have colors (s : Original m) : color (projection s) = color s := by
    cases s with
    | inr i => rfl
    | inl s => simp only [projection]; split_ifs <;> rfl
  have commutes (s : Original m) (u : Fin 2) :
      projection (originalStep f s u) = sharedStep f (projection s) u := by
    cases s with
    | inr i => rfl
    | inl s =>
      by_cases hi : Immediate s
      · rw [immediate_step s hi u]
        simp [projection, hi, sharedStep]
      · simp [projection, hi, sharedStep]
  have onto : Function.Surjective (projection (m := m)) := by
    intro t
    rcases t with (k | s) | i
    · let s : Slot m := ⟨⟨2 * (k.val + 1), by have H := k.isLt; omega⟩,
        ⟨⟨k.val + 1, by change k.val + 1 < 2 * (k.val + 1); omega⟩,
          ⟨k.val, by change k.val < k.val + 1; omega⟩⟩⟩
      have hi : Immediate s := by dsimp [Immediate, s]; omega
      refine ⟨.inl s, ?_⟩
      simp [projection, hi, s]
    · exact ⟨.inl s.val, by simp [projection, s.property]⟩
    · exact ⟨.inr i, rfl⟩
  have history (ω : ℕ → Fin 2) (n : ℕ) :
      color (trace (originalStep f) (root m hm) ω n) =
      color (trace (sharedStep f) (projection (root m hm)) ω n) := by
    have H := List.foldl_hom projection (g₁ := originalStep f) (g₂ := sharedStep f)
      (l := List.ofFn (fun j : Fin n => ω j.val)) (a₁ := root m hm)
      (fun s u => (commutes s u).symm)
    exact (colors _).symm.trans (congrArg color H.symm)
  have stop (ω : ℕ → Fin 2) (i : Fin m) (n : ℕ) :
      FirstStop (originalStep f) color (root m hm) ω i n ↔
      FirstStop (sharedStep f) color (projection (root m hm)) ω i n := by
    simp only [FirstStop, history]
  have bills (ω : ℕ → Fin 2) (n : ℕ) :
      charged (originalStep f) color (root m hm) ω n =
      charged (sharedStep f) color (projection (root m hm)) ω n := by
    simp only [charged, history]
  have paid (ω : ℕ → Fin 2) (i : Fin m) (n : ℕ)
      (h : FirstStop (originalStep f) color (root m hm) ω i n) :
      charged (originalStep f) color (root m hm) ω n = n := by
    unfold charged
    rw [Finset.filter_eq_self.mpr (fun j hj => h.2 j (Finset.mem_range.mp hj)),
      Finset.card_range]
  have no_stop (ω : ℕ → Fin 2) :
      Nonstop (originalStep f) color (root m hm) ω ↔
      Nonstop (sharedStep f) color (projection (root m hm)) ω := by
    simp only [Nonstop, history]
  let removedEquiv : {s : Slot m // Immediate s} ≃
      Σ e : Fin (m + 1), Fin (e.val / 2) × Fin (e.val / 2) :=
    { toFun := fun s => ⟨s.val.1,
        ⟨⟨s.val.2.1.val - (s.val.1.val - s.val.1.val / 2), by
          have Hr := s.val.2.1.isLt
          have H := s.property.1
          omega⟩, ⟨s.val.2.2.val, s.property.2⟩⟩⟩
      invFun := fun t => ⟨⟨t.1,
        ⟨⟨t.1.val - t.1.val / 2 + t.2.1.val, by
          have H := t.2.1.isLt
          omega⟩, ⟨t.2.2.val, by
          change t.2.2.val < t.1.val - t.1.val / 2 + t.2.1.val
          have H := t.2.1.isLt
          have H' := t.2.2.isLt
          omega⟩⟩⟩, by
            constructor
            · have H := t.2.1.isLt; omega
            · exact t.2.2.isLt⟩
      left_inv := by
        intro s
        apply Subtype.ext
        dsimp
        have H := s.property.1
        have Hr := s.val.2.1.isLt
        have heq : s.val.1.val - s.val.1.val / 2 +
            (s.val.2.1.val - (s.val.1.val - s.val.1.val / 2)) = s.val.2.1.val := by omega
        simp only [heq, Fin.eta]
      right_inv := by
        intro t
        dsimp
        have H := t.2.1.isLt
        have heq : (t.1.val - t.1.val / 2 + t.2.1.val) -
            (t.1.val - t.1.val / 2) = t.2.1.val := by omega
        simp only [heq, Fin.eta, Prod.eta, Sigma.eta] }
  have removed : Fintype.card {s : Slot m // Immediate s} =
      ∑ e ∈ Finset.range (m + 1), (e / 2) ^ 2 := by
    rw [Fintype.card_congr removedEquiv]
    simp [Fintype.card_sigma, Fintype.card_prod, sq, Fin.sum_univ_eq_sum_range]
  have total : Fintype.card (Slot m) = m * (m - 1) * (m + 1) / 6 := by
    have hs : (∑ e ∈ Finset.range (m + 1), e.choose 2) = (m + 1).choose 3 := by
      rw [← Nat.sum_Icc_choose m 2]
      apply Finset.sum_subset
      · intro e he
        simp only [Finset.mem_Icc, Finset.mem_range] at he ⊢
        omega
      · intro e he hn
        apply Nat.choose_eq_zero_of_lt
        simp only [Finset.mem_range, Finset.mem_Icc, not_and] at he hn
        omega
    calc
      Fintype.card (Slot m) = ∑ e ∈ Finset.range (m + 1), e.choose 2 := by
        simp [Slot, Fintype.card_sigma, Fin.sum_univ_eq_sum_range,
          Finset.sum_range_id, Nat.choose_two_right]
      _ = (m + 1).choose 3 := hs
      _ = _ := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
          Nat.factorial_zero]
        congr 1
        have H : m + 1 - 2 = m - 1 := by omega
        simp only [H, Nat.add_sub_cancel, Nat.sub_zero, mul_one]
        ring
  have activity : Nat.card (SharedActive m) = bound m := by
    simp only [SharedActive, Nat.card_eq_fintype_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_subtype_compl, total, removed, bound]
    omega
  have reachable : Nat.card (ReachableActive (sharedStep f) (projection (root m hm))) ≤ bound m := by
    rw [← activity]
    letI : Fintype (ReachableActive (sharedStep f) (projection (root m hm))) :=
      inferInstanceAs (Fintype {a : SharedActive m // ∃ w : List (Fin 2),
        w.foldl (sharedStep f) (projection (root m hm)) = .inl a})
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have closed : ∀ q : ℕ, 1 ≤ q → bound (2 * q) = (2 * q ^ 3 + q) / 3 ∧
      bound (2 * q + 1) = (2 * q ^ 3 + 3 * q ^ 2 + 4 * q) / 3 := by
    intro q hq
    have square_sum (n : ℕ) :
        6 * (∑ j ∈ Finset.range n, j ^ 2) + 3 * n ^ 2 = 2 * n ^ 3 + n := by
      have H := sum_range_pow n 2
      norm_num [Finset.sum_range_succ] at H
      have H' : ((∑ j ∈ Finset.range n, j ^ 2 : ℕ) : ℚ) =
          ∑ j ∈ Finset.range n, (j : ℚ) ^ 2 := by push_cast; rfl
      rw [← H'] at H
      exact_mod_cast (show (6 : ℚ) * (∑ j ∈ Finset.range n, j ^ 2 : ℕ) +
        3 * (n : ℚ) ^ 2 = 2 * (n : ℚ) ^ 3 + n by nlinarith only [H])
    have pairs (n : ℕ) : (∑ e ∈ Finset.range (2 * n), (e / 2) ^ 2) =
        2 * ∑ j ∈ Finset.range n, j ^ 2 := by
      have H := (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)).sum_comp
        (fun e : Fin (n * 2) => (e.val / 2) ^ 2)
      have per (t : Fin n × Fin 2) :
          ((finProdFinEquiv t).val / 2) ^ 2 = t.1.val ^ 2 := by
        change ((t.2.val + 2 * t.1.val) / 2) ^ 2 = t.1.val ^ 2
        have H := t.2.isLt
        congr 1
        omega
      simp_rw [per] at H
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at H
      rw [Fin.sum_univ_eq_sum_range (fun e : ℕ => (e / 2) ^ 2),
        Fin.sum_univ_eq_sum_range (fun j : ℕ => j ^ 2)] at H
      simpa only [Nat.mul_comm n 2] using H.symm
    have even_removed : (∑ e ∈ Finset.range (2 * q + 1), (e / 2) ^ 2) =
        2 * (∑ j ∈ Finset.range q, j ^ 2) + q ^ 2 := by
      rw [Finset.sum_range_succ, pairs]
      simp
    have odd_removed : (∑ e ∈ Finset.range (2 * q + 1 + 1), (e / 2) ^ 2) =
        2 * (∑ j ∈ Finset.range q, j ^ 2) + 2 * q ^ 2 := by
      rw [Finset.sum_range_succ, even_removed]
      have H : (2 * q + 1) / 2 = q := by omega
      rw [H]
      ring
    have N_exact (n : ℕ) : 6 * (n * (n - 1) * (n + 1) / 6) =
        n * (n - 1) * (n + 1) := by
      have H := Nat.descFactorial_eq_factorial_mul_choose (n + 1) 3
      simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
        Nat.factorial_zero] at H
      have hn : n + 1 - 2 = n - 1 := by omega
      simp only [hn, Nat.add_sub_cancel, Nat.sub_zero, mul_one] at H
      have H' : n * (n - 1) * (n + 1) = 6 * (n + 1).choose 3 := by
        nlinarith only [H]
      rw [H', Nat.mul_div_cancel_left _ (by decide : 0 < 6)]
    have S := square_sum q
    have Ne := N_exact (2 * q)
    have No := N_exact (2 * q + 1)
    have he : 2 * q - 1 + 1 = 2 * q := by omega
    have e_poly : (2 * q) * (2 * q - 1) * (2 * q + 1) + 2 * q = 8 * q ^ 3 := by
      calc
        _ = (2 * q) * (2 * q - 1) * (2 * q + 1) +
            (2 * q) * ((2 * q + 1) - (2 * q - 1)) / 2 := by
              have H : (2 * q + 1) - (2 * q - 1) = 2 := by omega
              rw [H]
              simp
        _ = _ := by nlinarith only [he]
    have o_poly : (2 * q + 1) * (2 * q + 1 - 1) * (2 * q + 1 + 1) =
        8 * q ^ 3 + 12 * q ^ 2 + 4 * q := by
      simp only [Nat.add_sub_cancel]
      ring
    have he_div : (2 * q) / 2 = q := by omega
    have ho_div : (2 * q + 1) / 2 = q := by omega
    have le_even : 2 * (∑ j ∈ Finset.range q, j ^ 2) + q ^ 2 ≤
        (2 * q) * (2 * q - 1) * (2 * q + 1) / 6 := by
      nlinarith only [S, Ne, e_poly, hq]
    have le_odd : 2 * (∑ j ∈ Finset.range q, j ^ 2) + 2 * q ^ 2 ≤
        (2 * q + 1) * (2 * q + 1 - 1) * (2 * q + 1 + 1) / 6 := by
      nlinarith only [S, No, o_poly, hq]
    have be : 3 * bound (2 * q) = 2 * q ^ 3 + q := by
      unfold bound
      rw [even_removed, he_div]
      have H := Nat.sub_add_cancel le_even
      nlinarith only [H, S, Ne, e_poly]
    have bo : 3 * bound (2 * q + 1) = 2 * q ^ 3 + 3 * q ^ 2 + 4 * q := by
      unfold bound
      rw [odd_removed, ho_div]
      have H := Nat.sub_add_cancel le_odd
      nlinarith only [H, S, No, o_poly]
    constructor <;> omega
  exact ⟨projection, sharedStep f, onto, colors, commutes, stop, bills, paid,
    no_stop, activity, reachable, Nat.card_fin m, closed⟩

end D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation
