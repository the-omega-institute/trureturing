/- GID: D5/S0/Asymptotics/DensePhaseEscapeIdentity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/DensePhaseEscapeIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dense scaling gives decay only at finitely many realizable exponents. -/

import D5.S0.Asymptotics.DensePhaseUnrealizable
import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import Mathlib.Tactic

namespace D5.S0.Asymptotics.DensePhaseEscapeIdentity

open Filter
open D5.S0.Asymptotics.DensePhaseUnrealizable
open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Diagonal.EscapeCount

/-- At every realizable positive exponent, fixed-point density `c` gives the
exact escape probability `(1 - c) ^ A`. The abstract exponential profile tends
to zero, but the same fixed transformation cannot realize the density equation
at or beyond a finite cutoff. -/
theorem dense_phase_escape_identity_on_realizable_exponents
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y → Y)
    (A n k : Nat) (hn : 2 ≤ n) (hcard : Nat.card Y = n)
    (c : Real) (hc : c ∈ Set.Ioo 0 1)
    (hfix : Nat.card {y : Y // f y = y} = k)
    (hdense : (k : Real) = c * (n : Real) ^ A) :
    escapeProbability (A := Fin A) f = (1 - c) ^ A ∧
      Tendsto (fun B : Nat ↦ (1 - c) ^ B) atTop (nhds 0) ∧
      ∃ A₀ : Nat, A < A₀ ∧ ∀ B : Nat, A₀ ≤ B →
        (Nat.card {y : Y // f y = y} : Real) ≠ c * (n : Real) ^ B := by
  classical
  have hcardF : Fintype.card Y = n := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hA : 1 ≤ A := by
    by_contra hnot
    have hAzero : A = 0 := by omega
    subst A
    simp only [pow_zero, mul_one] at hdense
    have hk_pos : 0 < (k : Real) := by rw [hdense]; exact hc.1
    have hk_one : 1 ≤ k := by exact_mod_cast hk_pos
    have hk_one_real : (1 : Real) ≤ k := by exact_mod_cast hk_one
    linarith [hc.2]
  have hk_le_n : k ≤ n := by
    rw [← hfix, ← hcard]
    exact Finite.card_subtype_le (fun y : Y ↦ f y = y)
  have hk : k ≤ n ^ A :=
    hk_le_n.trans (Nat.le_pow (a := n) (b := A) (by omega))
  have hden : (Fintype.card (Fin A → Fin A → Y) : Real) =
      (n : Real) ^ (A * A) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, hcardF]
    norm_num [Nat.cast_pow, pow_mul]
  have hn_pow_ne : (n : Real) ^ A ≠ 0 := by positivity
  have hprob : escapeProbability (A := Fin A) f = (1 - c) ^ A := by
    rw [escapeProbability, escaped_listing_card, hfix]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, hcardF]
    rw [Nat.cast_pow, Nat.cast_sub hk, Nat.cast_pow, hden]
    calc
      ((n : Real) ^ A - k) ^ A / (n : Real) ^ (A * A) =
          (((n : Real) ^ A - k) / (n : Real) ^ A) ^ A := by
            rw [div_pow, pow_mul]
      _ = (1 - c) ^ A := by
        congr 1
        rw [hdense]
        field_simp [hn_pow_ne]
  have hdecay : Tendsto (fun B : Nat ↦ (1 - c) ^ B) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [hc.2]) (by linarith [hc.1])
  obtain ⟨_, A₀, hlarge⟩ :=
    fixed_point_dense_phase_eventually_unrealizable f n hn hcard c hc
  refine ⟨hprob, hdecay, A₀, ?_, hlarge⟩
  by_contra hnot
  have hA₀ : A₀ ≤ A := Nat.le_of_not_gt hnot
  apply hlarge A hA₀
  rw [hfix]
  exact hdense

/-- The complete hypothesis bundle is jointly satisfiable at exponent one. -/
example : ∃ (f : Fin 2 → Fin 2) (A n k : Nat) (c : Real),
    2 ≤ n ∧ Nat.card (Fin 2) = n ∧ c ∈ Set.Ioo 0 1 ∧
      Nat.card {y : Fin 2 // f y = y} = k ∧
      (k : Real) = c * (n : Real) ^ A := by
  refine ⟨fun _ ↦ 0, 1, 2, 1, 1 / 2, by norm_num,
    by norm_num, by norm_num, ?_, by norm_num⟩
  norm_num [Nat.card_eq_fintype_card]

/-- The finite output domain used by the satisfiability witness is inhabited. -/
example : Nonempty (Fin 2) := inferInstance

#print axioms dense_phase_escape_identity_on_realizable_exponents

end D5.S0.Asymptotics.DensePhaseEscapeIdentity
