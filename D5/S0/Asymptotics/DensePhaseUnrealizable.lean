/- GID: D5/S0/Asymptotics/DensePhaseUnrealizable
   generality: G
   mirror-B: D5/B/S0/Asymptotics/DensePhaseUnrealizable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed points cannot have positive exponential density for all large listing sizes. -/

import D5.S0.Diagonal.EscapeCount
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.SetTheory.Cardinal.NatCard

namespace D5.S0.Asymptotics.DensePhaseUnrealizable

open Filter

universe u

/-- For a finite output type of fixed cardinality `n >= 2`, fixed points form a
subtype of the output type and hence have cardinality at most `n`. Consequently,
for every real density `0 < c < 1`, the equation `|Fix f| = c * n^A` is
impossible for every sufficiently large natural `A`. -/
theorem fixed_point_dense_phase_eventually_unrealizable
    {Y : Type u} [Finite Y] (f : Y → Y) (n : Nat) (hn : 2 ≤ n)
    (hcard : Nat.card Y = n) (c : Real) (hc : c ∈ Set.Ioo 0 1) :
    Nat.card {y : Y // f y = y} ≤ n ∧
      ∃ A₀ : Nat, ∀ A : Nat, A₀ ≤ A →
        (Nat.card {y : Y // f y = y} : Real) ≠ c * (n : Real) ^ A := by
  have hfix : Nat.card {y : Y // f y = y} ≤ n := by
    rw [← hcard]
    exact Finite.card_subtype_le (fun y : Y ↦ f y = y)
  have hn_one : (1 : Real) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hpow : Tendsto (fun A : Nat ↦ (n : Real) ^ A) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hn_one
  obtain ⟨A₀, hA₀⟩ :=
    (hpow.eventually_gt_atTop ((n : Real) / c + (1 - c))).exists_forall_of_atTop
  refine ⟨hfix, A₀, fun A hA hEq ↦ ?_⟩
  have hlarge_buffer :
      (n : Real) / c + (1 - c) < (n : Real) ^ A := hA₀ A hA
  have hc_pos : 0 < c := hc.1
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hlarge : (n : Real) / c < (n : Real) ^ A := by
    linarith [hc.2]
  have hscaled : (n : Real) < c * (n : Real) ^ A := by
    calc
      (n : Real) = c * ((n : Real) / c) := by field_simp
      _ < c * (n : Real) ^ A := mul_lt_mul_of_pos_left hlarge hc_pos
  have hfix_real : (Nat.card {y : Y // f y = y} : Real) ≤ (n : Real) := by
    exact_mod_cast hfix
  rw [hEq] at hfix_real
  exact (not_lt_of_ge hfix_real) hscaled

/-- The finite domain used by the hypothesis-satisfiability witness is inhabited. -/
example : Fin 2 := 0

/-- All source hypotheses, including a concrete transformation, are simultaneously satisfiable. -/
example : ∃ (f : Fin 2 → Fin 2) (n : Nat) (c : Real),
    f = id ∧ 2 ≤ n ∧ Nat.card (Fin 2) = n ∧ c ∈ Set.Ioo 0 1 := by
  exact ⟨id, 2, 1 / 2, rfl, by norm_num⟩

#print axioms fixed_point_dense_phase_eventually_unrealizable

end D5.S0.Asymptotics.DensePhaseUnrealizable
