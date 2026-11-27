/- GID: D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.claim; result=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result; claim=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.claim
   digest: The realized finite least periods of RESOCA 115 are not closed under squaring. -/

import D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115

/-!
# Rule 115 and Formenti–Kamilya Question 2

Formenti–Kamilya, arXiv:2606.13159v1, §3, Question 2, printed p. 97:
“If p is a period for RESOCA 115, is p² also a period?”
-/

namespace D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115SquareClosure

open FormentiKamilyaRule115 (Config step zeroConfig zero_period_three returns_three_of_returns_nine)

/-- A positive least period attained by two finitely supported initial layers. -/
def RealizesLeastPeriod (p : ℕ) : Prop :=
  0 < p ∧ ∃ s : Config, Set.Finite {i : ℤ | s.1 i = true ∨ s.2 i = true} ∧
    step^[p] s = s ∧ ∀ q : ℕ, 0 < q → q < p → step^[q] s ≠ s

/-- The set of realized least periods is closed under squaring. -/
def claim : Prop :=
  ∀ p : ℕ, RealizesLeastPeriod p → RealizesLeastPeriod (p ^ 2)

private theorem zero_finite :
    Set.Finite {i : ℤ | zeroConfig.1 i = true ∨ zeroConfig.2 i = true} := by
  simp [zeroConfig]

private theorem three_realized : RealizesLeastPeriod 3 :=
  ⟨by decide, zeroConfig, zero_finite, zero_period_three⟩

private theorem nine_unrealized : ¬ RealizesLeastPeriod 9 := by
  rintro ⟨_, s, hfinite, h9, hleast⟩
  exact hleast 3 (by decide) (by decide) (returns_three_of_returns_nine s hfinite h9)

/-- Three is a realized least period and its square is impossible. -/
theorem result : ¬ claim := by
  intro hclosure
  have hnine : RealizesLeastPeriod 9 := hclosure 3 three_realized
  exact nine_unrealized hnine

end D5.S3.StatisticalMechanics.CellularAutomata.FormentiKamilyaRule115SquareClosure
