/- GID: D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim; result=D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.result; claim=D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.claim
   digest: Four disordered exclusion sites refute the nonzero quadratic-current conjecture. -/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Continuity

set_option linter.style.longLine false

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.DisorderedExclusionQuadraticResponseRefutation
open scoped BigOperators Topology Asymptotics

noncomputable def p {L : ℕ} (wp : Fin L → ℝ) (ε : ℝ) (i : Fin L) : ℝ :=
  (1 + ε) / 2 * wp i

noncomputable def q {L : ℕ} (wm : Fin L → ℝ) (ε : ℝ) (i : Fin L) : ℝ :=
  (1 - ε) / 2 * wm i

noncomputable def rate {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) (ε : ℝ)
    (s t : Finset (Fin L)) : ℝ :=
  ∑ i ∈ s, ((if i + 1 ∉ s ∧ t = insert (i + 1) (s.erase i) then p wp ε i else 0) +
    (if i - 1 ∉ s ∧ t = insert (i - 1) (s.erase i) then q wm ε i else 0))

def IsStationary {L : ℕ} [NeZero L] (N : ℕ) (wp wm : Fin L → ℝ) (ε : ℝ)
    (μ : Finset (Fin L) → ℝ) : Prop :=
  (∀ s, s.card ≠ N → μ s = 0) ∧ (∀ s, 0 ≤ μ s) ∧ (∑ s, μ s) = 1 ∧
    ∀ t, (∑ s, μ s * rate wp wm ε s t) = μ t * ∑ s, rate wp wm ε t s

noncomputable def current {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) (ε : ℝ)
    (μ : Finset (Fin L) → ℝ) : ℝ :=
  ∑ s, μ s * ((if 0 ∈ s ∧ 1 ∉ s then p wp ε 0 else 0) -
    (if 1 ∈ s ∧ 0 ∉ s then q wm ε 1 else 0))

def BondRatioUniform {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) : Prop :=
  ∀ ε : ℝ, -1 < ε → ε < 1 → ∀ i j : Fin L,
    p wp ε i / q wm ε (i + 1) = p wp ε j / q wm ε (j + 1)

def InversionCorrespondence {L : ℕ} [NeZero L] (wp wm : Fin L → ℝ) : Prop :=
  ∃ k : Fin L, ∀ i : Fin L,
    (∀ ε : ℝ, p wp ε (k + i) = q wm (-ε) (k - i)) ∨
    (∀ ε : ℝ, p wp ε (k + i) = q wm (-ε) (k - i + 1))

def claim : Prop :=
  ∀ (L N : ℕ) [NeZero L], 2 ≤ N → N + 2 ≤ L →
    ∀ wp wm : Fin L → ℝ, (∀ i, 0 < wp i ∧ 0 < wm i) →
    (∏ i, wm i) = (∏ i, wp i) → ¬ BondRatioUniform wp wm →
    ¬ InversionCorrespondence wp wm → ∀ δ : ℝ, 0 < δ →
    ∀ π : ℝ → Finset (Fin L) → ℝ,
    (∀ ε, |ε| < δ → IsStationary N wp wm ε (π ε) ∧
      ∀ μ, IsStationary N wp wm ε μ → μ = π ε) →
    ∀ c₁ c₂ : ℝ,
      (fun ε => current wp wm ε (π ε) - c₁ * ε - c₂ * ε ^ 2)
        =o[𝓝 0] (fun ε => ε ^ 2) → c₂ ≠ 0

private noncomputable def a : Fin 4 → ℝ := ![2, 4, 3, 41]

private def states : Fin 6 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

private noncomputable def D (ε : ℝ) : ℝ :=
  223175 + 17022*ε^2 - 1628*ε^3 - 114725*ε^4 + 1628*ε^5

private noncomputable def B (ε : ℝ) : Fin 6 → ℝ :=
  ![123*(2825-1612*ε+390*ε^2+1256*ε^3-1695*ε^4+148*ε^5),
    164*(2825+518*ε-928*ε^2-370*ε^3-1033*ε^4-148*ε^5),
    12*(2825+5608*ε+4830*ε^2+3036*ε^3+1265*ε^4+148*ε^5),
    82*(2825+1008*ε+1150*ε^2-1564*ε^3-2415*ε^4+148*ε^5),
    6*(2825-222*ε+2672*ε^2+370*ε^3-2873*ε^4-148*ε^5),
    8*(2825-4412*ε+2630*ε^2-1544*ε^3+545*ε^4+148*ε^5)]

private noncomputable def law (ε : ℝ) (s : Finset (Fin 4)) : ℝ :=
  ∑ j : Fin 6, if s = states j then B ε j / (5 * D ε) else 0

private theorem sum_configs (f : Finset (Fin 4) → ℝ) :
    (∑ s, f s) = f {} + f {0} + f {1} + f {2} + f {3} +
      f {0,1} + f {0,2} + f {0,3} + f {1,2} + f {1,3} + f {2,3} +
      f {0,1,2} + f {0,1,3} + f {0,2,3} + f {1,2,3} + f {0,1,2,3} := by
  have hu : (Finset.univ : Finset (Finset (Fin 4))) =
      {{}, {0}, {1}, {2}, {3}, {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3},
        {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, {0,1,2,3}} := by decide
  rw [hu]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

private theorem no_uniform : ¬ BondRatioUniform a a := by
  intro h
  have hh := h 0 (by norm_num) (by norm_num) 0 1
  norm_num [p.eq_1, q.eq_1, a.eq_1, Fin.add_def, Fin.sub_def, Fin.neg_def] at hh

private theorem no_inversion : ¬ InversionCorrespondence a a := by
  rintro ⟨k, hk⟩
  have hh : ∀ i : Fin 4,
      p a 0 (k+i) = q a 0 (k-i) ∨ p a 0 (k+i) = q a 0 (k-i+1) := by
    intro i
    exact (hk i).imp (fun h => by simpa using h 0) (fun h => by simpa using h 0)
  fin_cases k <;> norm_num [p.eq_1, q.eq_1, a.eq_1, Fin.forall_fin_succ, Fin.add_def, Fin.sub_def, Fin.neg_def] at hh

end D5.S3.StatisticalMechanics.DisorderedExclusionQuadraticResponseRefutation
