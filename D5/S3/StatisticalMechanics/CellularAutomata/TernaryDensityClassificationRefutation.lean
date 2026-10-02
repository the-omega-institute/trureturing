/- GID: D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.claim; result=D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.result; claim=D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.claim
   digest: The ternary rule pair of Fukś–Procyk misclassifies 210 (2002.08924). -/

/-
proof_shape: result: bind-only (evaluation of the two rules on the configuration (2, 1, 0) of
  length 3 by `decide`, and of its density by `norm_num`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11845; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation

/-- The ternary nearest-neighbour local rule with Wolfram number `N`: the coefficient of
`3 ^ (9 a + 3 b + c)` in the base-3 expansion of `N` is `f(a, b, c)`. -/
def wolfram (N : ℕ) (a b c : Fin 3) : Fin 3 :=
  ⟨N / 3 ^ (9 * a.val + 3 * b.val + c.val) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The rule `F` of Conjecture 1, Wolfram number 6478767664173. -/
def ruleF : Fin 3 → Fin 3 → Fin 3 → Fin 3 := wolfram 6478767664173

/-- The rule `G` of Conjecture 1, Wolfram number 7580606234490. -/
def ruleG : Fin 3 → Fin 3 → Fin 3 → Fin 3 := wolfram 7580606234490

/-- The global map of a local rule on periodic configurations of length `L`:
`(F x)_i = f(x_{i-1}, x_i, x_{i+1})` with indices in `ℤ/L`. -/
def step {L : ℕ} (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) (x : ZMod L → Fin 3) : ZMod L → Fin 3 :=
  fun i => f (x (i - 1)) (x i) (x (i + 1))

/-- The density `ρ(x) = (1/2L) Σ_i x_i`. -/
def rho {L : ℕ} [NeZero L] (x : ZMod L → Fin 3) : ℚ :=
  (∑ i, ((x i : ℕ) : ℚ)) / (2 * L)

/-- Conjecture 1 of Fukś and Procyk (arXiv:2002.08924): for every length `L` and every
configuration containing a zero, `G^L F^L` sends densities in `[0, 2/3)`, `(2/3, 3/4)` and
`(3/4, 1)` to `0^L`, `1^L` and `2^L`. `result` shows that it is false. -/
def claim : Prop :=
  ∀ (L : ℕ) [NeZero L] (x : ZMod L → Fin 3), (∃ i, x i = 0) →
    (rho x ∈ Set.Ico (0 : ℚ) (2 / 3) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 0) ∧
    (rho x ∈ Set.Ioo (2 / 3 : ℚ) (3 / 4) → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 1) ∧
    (rho x ∈ Set.Ioo (3 / 4 : ℚ) 1 → (step ruleG)^[L] ((step ruleF)^[L] x) = fun _ => 2)

theorem result : ¬ claim := by
  intro h
  -- the configuration `x = (2, 1, 0)` of length 3 has density `1/2`
  let x : ZMod 3 → Fin 3 := ![2, 1, 0]
  have hzero : ∃ i, x i = 0 := ⟨2, rfl⟩
  have hsum : (∑ i, (x i : ℕ)) = 3 := by decide
  have hrho : rho x ∈ Set.Ico (0 : ℚ) (2 / 3) := by
    simp only [rho, Set.mem_Ico, ← Nat.cast_sum, hsum]
    norm_num
  have hcls := (h 3 x hzero).1 hrho
  -- `F` sends `x` to `111`, which both rules fix
  have hrun : (step ruleG)^[3] ((step ruleF)^[3] x) ≠ fun _ => 0 := by decide
  exact hrun hcls

end D5.S3.StatisticalMechanics.CellularAutomata.TernaryDensityClassificationRefutation
