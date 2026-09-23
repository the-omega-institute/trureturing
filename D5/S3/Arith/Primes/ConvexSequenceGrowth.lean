/- GID: D5/S3/Arith/Primes/ConvexSequenceGrowth
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/ConvexSequenceGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Filter.AtTopBot.Basic, mathlib/module/Mathlib.Order.Filter.AtTopBot.Field, mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Order, mathlib/module/Mathlib.Tactic.Ring, mathlib/module/Mathlib.Tactic.FieldSimp]
   utility: none
   digest: A convex integer sequence grows faster than every multiple of n squared exactly when its gaps outgrow every multiple of n. -/

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace D5.S3.Arith.Primes.ConvexSequenceGrowth

open Filter

/-- The consecutive gap of a natural-valued sequence. -/
def gap (q : ℕ → ℕ) (n : ℕ) : ℕ := q (n + 1) - q n

/-- Strict increase together with nondecreasing consecutive gaps. -/
def ConvexSequence (q : ℕ → ℕ) : Prop :=
  StrictMono q ∧ ∀ n, gap q n ≤ gap q (n + 1)

/-- For a convex integer sequence, quotient growth by `n^2` is equivalent to gap
growth by `n`. -/
theorem quotient_tendsto_atTop_iff_gap_tendsto_atTop (q : ℕ → ℕ)
    (hq : ConvexSequence q) :
    Tendsto (fun n => (q n : ℝ) / (n : ℝ) ^ 2) atTop atTop ↔
      Tendsto (fun n => (gap q n : ℝ) / (n : ℝ)) atTop atTop := by
  rcases hq with ⟨hqmono, hgapmono⟩
  have hgap_pos : ∀ n, 0 < gap q n := by
    intro n
    exact Nat.sub_pos_of_lt (hqmono (Nat.lt_succ_self n))
  have hgap_mono : Monotone (gap q) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (hgapmono n)
  have htail : ∀ m t, q m + t * gap q m ≤ q (m + t) := by
    intro m t
    induction t with
    | zero => simp
    | succ t ih =>
        have hgm : gap q m ≤ gap q (m + t) := hgap_mono (Nat.le_add_right m t)
        have hstep : q (m + t) + gap q (m + t) = q (m + t + 1) := by
          have hle : q (m + t) ≤ q (m + t + 1) :=
            (Nat.sub_pos_iff_lt.mp (hgap_pos (m + t))).le
          exact Nat.add_sub_of_le hle
        calc
          q m + (t + 1) * gap q m = (q m + t * gap q m) + gap q m := by ring
          _ ≤ q (m + t) + gap q m := Nat.add_le_add_right ih _
          _ ≤ q (m + t) + gap q (m + t) := Nat.add_le_add_left hgm _
          _ = q (m + t + 1) := hstep
  have hupp : ∀ n, q n ≤ q 0 + n * gap q n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep : q n + gap q n = q (n + 1) := by
          have hle : q n ≤ q (n + 1) := (Nat.sub_pos_iff_lt.mp (hgap_pos n)).le
          exact Nat.add_sub_of_le hle
        have hgm := hgap_mono (Nat.le_succ n)
        rw [← hstep]
        calc
          q n + gap q n ≤ (q 0 + n * gap q n) + gap q n := Nat.add_le_add_right ih _
          _ = q 0 + (n + 1) * gap q n := by ring
          _ ≤ q 0 + (n + 1) * gap q (n + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left (n + 1) hgm) _
  have hhalf_tendsto : Tendsto (fun n : ℕ => n / 2) Filter.atTop Filter.atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨2 * b, ?_⟩
    intro n hn
    omega
  have hforward : Tendsto (fun n : ℕ => (gap q n : ℝ) / (n : ℝ)) atTop atTop →
      Tendsto (fun n : ℕ => (q n : ℝ) / (n : ℝ) ^ 2) atTop atTop := by
    intro hgaplim
    have hcomp : Tendsto (fun n : ℕ => (gap q (n / 2) : ℝ) / ((n / 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      simpa [Function.comp_def] using hgaplim.comp hhalf_tendsto
    have hlow : ∀ᶠ n : ℕ in Filter.atTop,
        (1 / 16 : ℝ) * ((gap q (n / 2) : ℝ) / ((n / 2 : ℕ) : ℝ)) ≤
          (q n : ℝ) / (n : ℝ) ^ 2 := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
      let m := n / 2
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hnm : m + m ≤ n + 1 := by dsimp [m]; omega
      have htail' := htail m (n - m)
      have hmn : m ≤ n := by dsimp [m]; omega
      have hq0 : 0 ≤ q m := Nat.zero_le _
      have hnm' : m ≤ n - m := by dsimp [m]; omega
      have hmul : (m : ℝ) * (gap q m : ℝ) ≤ (q n : ℝ) := by
        have hnat : m * gap q m ≤ q n := by
          calc
            m * gap q m ≤ q m + (n - m) * gap q m := by
              exact (Nat.mul_le_mul_right _ hnm').trans
                (Nat.le_add_left ((n - m) * gap q m) (q m))
            _ ≤ q n := by simpa [Nat.add_sub_of_le hmn] using htail'
        exact_mod_cast hnat
      have hncast : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
      have hmcast : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
      have hnle : (n : ℝ) ≤ 4 * m := by
        have hnleNat : n ≤ 4 * m := by dsimp [m]; omega
        exact_mod_cast hnleNat
      have hratio : (1 / 16 : ℝ) * ((gap q m : ℝ) / (m : ℝ)) ≤
          (m : ℝ) * (gap q m : ℝ) / (n : ℝ) ^ 2 := by
        have hg : 0 ≤ (gap q m : ℝ) := by positivity
        have hsq : (n : ℝ) ^ 2 ≤ (4 * (m : ℝ)) ^ 2 := by nlinarith
        have hmul' := mul_le_mul_of_nonneg_left hsq hg
        rw [show (1 / 16 : ℝ) * ((gap q m : ℝ) / (m : ℝ)) =
          (gap q m : ℝ) / (16 * (m : ℝ)) by field_simp]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith
      have hqdiv : (m : ℝ) * (gap q m : ℝ) / (n : ℝ) ^ 2 ≤
          (q n : ℝ) / (n : ℝ) ^ 2 := by
        exact (div_le_div_iff_of_pos_right (by positivity)).2 hmul
      exact hratio.trans hqdiv
    rw [tendsto_atTop_atTop]
    intro c
    have hev : ∀ᶠ n : ℕ in atTop, (16 : ℝ) * c ≤
        (gap q (n / 2) : ℝ) / ((n / 2 : ℕ) : ℝ) :=
      hcomp (eventually_ge_atTop (16 * c))
    exact eventually_atTop.mp ((hev.and hlow).mono fun n hn => by
      rcases hn with ⟨hn₁, hn₂⟩
      nlinarith)
  have hreverse : Tendsto (fun n : ℕ => (q n : ℝ) / (n : ℝ) ^ 2) atTop atTop →
      Tendsto (fun n : ℕ => (gap q n : ℝ) / (n : ℝ)) atTop atTop := by
    intro hqlim
    rw [tendsto_atTop_atTop]
    intro c
    have hq0small : ∀ᶠ n : ℕ in Filter.atTop, (q 0 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
      filter_upwards [Filter.eventually_ge_atTop (q 0 + 1)] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < n))
      have hq0n : (q 0 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hnq : q 0 ≤ n := by omega
        have hnat : q 0 ≤ n * n := le_trans hnq (Nat.le_mul_of_pos_left n (by omega))
        have hreal : (q 0 : ℝ) ≤ (n : ℝ) * (n : ℝ) := by exact_mod_cast hnat
        simpa [pow_two] using hreal
      exact (div_le_iff₀ (by positivity)).2 (by simpa [pow_two] using hq0n)
    have hevq : ∀ᶠ n : ℕ in atTop, c + 1 ≤ (q n : ℝ) / (n : ℝ) ^ 2 :=
      hqlim (eventually_ge_atTop (c + 1))
    exact eventually_atTop.mp ((hevq.and hq0small).mono fun n hn => by
      rcases hn with ⟨hn, hsmall⟩
      by_cases hn0 : n = 0
      · subst n
        norm_num at hn ⊢
        linarith
      · have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hn0)
        have hbound := hupp n
        have hupper : (q n : ℝ) / (n : ℝ) ^ 2 ≤
            (q 0 : ℝ) / (n : ℝ) ^ 2 + (gap q n : ℝ) / (n : ℝ) := by
          have hnat : q n ≤ q 0 + n * gap q n := hbound
          have hcast : (q n : ℝ) ≤ (q 0 : ℝ) + (n : ℝ) * (gap q n : ℝ) := by exact_mod_cast hnat
          have hEq : (q 0 : ℝ) / (n : ℝ) ^ 2 + (gap q n : ℝ) / (n : ℝ) =
              ((q 0 : ℝ) + (n : ℝ) * (gap q n : ℝ)) / (n : ℝ) ^ 2 := by
            field_simp
          rw [hEq]
          exact (div_le_div_iff_of_pos_right (by positivity)).2 hcast
        linarith
      )
  exact ⟨hreverse, hforward⟩

end D5.S3.Arith.Primes.ConvexSequenceGrowth
