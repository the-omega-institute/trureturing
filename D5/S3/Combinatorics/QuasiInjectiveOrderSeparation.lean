/- GID: D5/S3/Combinatorics/QuasiInjectiveOrderSeparation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QuasiInjectiveOrderSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Function.Iterate]
   utility: none
   digest: For every order m at least two some function separates quasi-injectivity of order m-1 from order m. -/

import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QuasiInjectiveOrderSeparation

/-
proof_shape: result: content
escape_witness: the closed form `iterate_even` for the iterates of `g m` on even inputs, and
  the collapse `iterate_eq_one`; neither is an instantiation, projection or normalisation of a
  pinned upstream statement, and together they are the sole source of the opposing conclusions.
admission_basis: open-problem-resolution (issue #9295)
Direct frozen dependencies: none (pinned Mathlib only)
-/

/-! ### Quasi-injectivity of a given order -/

/-- `f` is quasi-injective of order `l`: for every `k` between one and `l`, if the `k`-fold
composite of `f` agrees on the multiples of `a` and on the multiples of `b`, then `a = b`. -/
def QuasiInjectiveOfOrder (f : ℕ → ℕ) (l : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ l → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    (∀ n : ℕ, 1 ≤ n → f^[k] (a * n) = f^[k] (b * n)) → a = b

/-! ### The separating family -/

/-- The separating function of order `m`. An odd number `2 * t + 1` carries the level
`t % (m - 1)`; the function raises the level by one, sends the top level to `1`, fixes `1`,
and sends an even number into the first level. -/
def g (m : ℕ) (n : ℕ) : ℕ :=
  if n = 1 then 1
  else if n % 2 = 0 then 2 * (m - 1) * (n / 2) + 1
  else if (n - 1) / 2 % (m - 1) = (m - 2) % (m - 1) then 1
  else n + 2

/-! ### Elementary values -/

private lemma g_one (m : ℕ) : g m 1 = 1 := by simp [g]

private lemma g_zero (m : ℕ) : g m 0 = 1 := by norm_num [g]

private lemma g_even (m t : ℕ) : g m (2 * t) = 2 * (m - 1) * t + 1 := by
  have h1 : 2 * t ≠ 1 := by omega
  have h2 : 2 * t % 2 = 0 := by omega
  have h3 : 2 * t / 2 = t := by omega
  simp [g, h1, h2, h3]

private lemma g_odd_step (m t : ℕ) (ht : 1 ≤ t)
    (h : t % (m - 1) ≠ (m - 2) % (m - 1)) : g m (2 * t + 1) = 2 * (t + 1) + 1 := by
  have h1 : 2 * t + 1 ≠ 1 := by omega
  have h2 : (2 * t + 1) % 2 = 1 := by omega
  have h3 : (2 * t + 1 - 1) / 2 = t := by omega
  simp only [g, if_neg h1, h2, h3, if_neg h, Nat.one_ne_zero, if_false]
  omega

private lemma g_odd_collapse (m t : ℕ) (ht : 1 ≤ t)
    (h : t % (m - 1) = (m - 2) % (m - 1)) : g m (2 * t + 1) = 1 := by
  have h1 : 2 * t + 1 ≠ 1 := by omega
  have h2 : (2 * t + 1) % 2 = 1 := by omega
  have h3 : (2 * t + 1 - 1) / 2 = t := by omega
  simp only [g, if_neg h1, h2, h3, if_pos h, Nat.one_ne_zero, if_false]

private lemma iterate_one (m k : ℕ) : (g m)^[k] 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, g_one]

/-! ### The closed form on even inputs -/

private lemma iterate_even (m : ℕ) (hm : 2 ≤ m) :
    ∀ k t : ℕ, 1 ≤ k → k ≤ m - 1 → 1 ≤ t →
      (g m)^[k] (2 * t) = 2 * ((m - 1) * t + (k - 1)) + 1 := by
  intro k
  induction k with
  | zero => intro t hk; omega
  | succ k ih =>
      intro t hk hkm ht
      have hmt : 0 < (m - 1) * t := Nat.mul_pos (by omega) (by omega)
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp only [Nat.zero_add, Function.iterate_one]
        rw [g_even m t]
        have hassoc : 2 * (m - 1) * t = 2 * ((m - 1) * t) := by ring
        omega
      · have hkm' : k ≤ m - 1 := by omega
        have hstep := ih t hk0 hkm' ht
        rw [Function.iterate_succ_apply', hstep]
        have hmod : ((m - 1) * t + (k - 1)) % (m - 1) ≠ (m - 2) % (m - 1) := by
          have h1 : ((m - 1) * t + (k - 1)) % (m - 1) = (k - 1) % (m - 1) := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_left]
          have h2 : (k - 1) % (m - 1) = k - 1 := Nat.mod_eq_of_lt (by omega)
          have h3 : (m - 2) % (m - 1) = m - 2 := Nat.mod_eq_of_lt (by omega)
          omega
        rw [g_odd_step m _ (by omega) hmod]
        omega

/-! ### The collapse -/

private lemma collapse_odd (m : ℕ) (hm : 2 ≤ m) :
    ∀ d t : ℕ, 1 ≤ t → m - 2 - t % (m - 1) = d → (g m)^[d + 1] (2 * t + 1) = 1 := by
  intro d
  induction d with
  | zero =>
      intro t ht hd
      have hlt : t % (m - 1) < m - 1 := Nat.mod_lt _ (by omega)
      have h3 : (m - 2) % (m - 1) = m - 2 := Nat.mod_eq_of_lt (by omega)
      have heq : t % (m - 1) = (m - 2) % (m - 1) := by omega
      simp only [Nat.zero_add, Function.iterate_one]
      exact g_odd_collapse m t ht heq
  | succ d ih =>
      intro t ht hd
      have hlt : t % (m - 1) < m - 1 := Nat.mod_lt _ (by omega)
      have h3 : (m - 2) % (m - 1) = m - 2 := Nat.mod_eq_of_lt (by omega)
      have hne : t % (m - 1) ≠ (m - 2) % (m - 1) := by omega
      have hone : 1 % (m - 1) = 1 := Nat.mod_eq_of_lt (by omega)
      have hsucc : (t + 1) % (m - 1) = t % (m - 1) + 1 := by
        rw [Nat.add_mod, hone]
        exact Nat.mod_eq_of_lt (by omega)
      have hd' : m - 2 - (t + 1) % (m - 1) = d := by omega
      have hrec := ih (t + 1) (by omega) hd'
      rw [Function.iterate_succ_apply, g_odd_step m t ht hne]
      exact hrec

private lemma iterate_eq_one (m : ℕ) (hm : 2 ≤ m) : ∀ n : ℕ, (g m)^[m] n = 1 := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have hsplit := Function.iterate_succ_apply (g m) (m - 1) 0
    rw [show Nat.succ (m - 1) = m from by omega] at hsplit
    rw [hsplit, g_zero, iterate_one]
  · rcases Nat.even_or_odd n with he | ho
    · obtain ⟨t, ht⟩ := he
      have htpos : 1 ≤ t := by omega
      have hn : n = 2 * t := by omega
      subst hn
      have hmt : 0 < (m - 1) * t := Nat.mul_pos (by omega) (by omega)
      have hk := iterate_even m hm (m - 1) t (by omega) le_rfl htpos
      have hsplit := Function.iterate_succ_apply' (g m) (m - 1) (2 * t)
      rw [show Nat.succ (m - 1) = m from by omega] at hsplit
      rw [hsplit, hk]
      have h3 : (m - 2) % (m - 1) = m - 2 := Nat.mod_eq_of_lt (by omega)
      have hmod : ((m - 1) * t + (m - 1 - 1)) % (m - 1) = (m - 2) % (m - 1) := by
        have hrw : m - 1 - 1 = m - 2 := by omega
        rw [hrw, Nat.add_comm, Nat.add_mul_mod_self_left]
      exact g_odd_collapse m _ (by omega) hmod
    · obtain ⟨t, ht⟩ := ho
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · subst ht0
        have hn : n = 1 := by omega
        subst hn
        exact iterate_one m m
      · have hn : n = 2 * t + 1 := by omega
        subst hn
        have hlt : t % (m - 1) < m - 1 := Nat.mod_lt _ (by omega)
        have hcol := collapse_odd m hm (m - 2 - t % (m - 1)) t ht0 rfl
        have hsplit := Function.iterate_add_apply (g m)
          (m - (m - 2 - t % (m - 1) + 1)) (m - 2 - t % (m - 1) + 1) (2 * t + 1)
        rw [show m - (m - 2 - t % (m - 1) + 1) + (m - 2 - t % (m - 1) + 1) = m from by omega]
          at hsplit
        rw [hsplit, hcol, iterate_one]

/-! ### The two halves of the separation -/

private lemma g_pos (m : ℕ) (n : ℕ) (hn : 1 ≤ n) : 1 ≤ g m n := by
  unfold g
  split_ifs <;> omega

private lemma quasi_lower (m : ℕ) (hm : 2 ≤ m) : QuasiInjectiveOfOrder (g m) (m - 1) := by
  intro k hk hkm a b ha hb h
  have h2 := h 2 (by omega)
  rw [show a * 2 = 2 * a from by ring, show b * 2 = 2 * b from by ring] at h2
  rw [iterate_even m hm k a hk hkm ha, iterate_even m hm k b hk hkm hb] at h2
  have hprod : (m - 1) * a = (m - 1) * b := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) hprod

private lemma not_quasi_upper (m : ℕ) (hm : 2 ≤ m) : ¬ QuasiInjectiveOfOrder (g m) m := by
  intro h
  have hcontra := h m (by omega) le_rfl 1 2 (by omega) (by omega)
    (fun n _ => by simp [iterate_eq_one m hm])
  omega

/-! ### Question 17 -/

/-- Question 17 of Pongsriiam: for every order `m` at least two there is a function
`f : ℕ → ℕ` that is quasi-injective of order `m - 1` but not of order `m`. -/
def claim : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ f : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → 1 ≤ f n) ∧
    QuasiInjectiveOfOrder f (m - 1) ∧ ¬ QuasiInjectiveOfOrder f m

theorem result : claim := by
  intro m hm
  exact ⟨g m, g_pos m, quasi_lower m hm, not_quasi_upper m hm⟩

end D5.S3.Combinatorics.QuasiInjectiveOrderSeparation
