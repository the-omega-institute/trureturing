/- GID: D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SetImaginarity/PrintedConjecture
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.claim; result=D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.result; claim=D5/S3/Quantum/Information/SetImaginarity/PrintedConjecture.claim
   digest: Three diagonal qubit states refute the printed set-imaginarity biconditional. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

compile_only_with_mathlib

namespace D5.S3.Quantum.Information.SetImaginarity.PrintedConjecture

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

/-- One unitary conjugation makes every state entrywise real. -/
def CommonRealBasis {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (ρ : Fin n → Matrix ι ι ℂ) : Prop :=
  ∃ U : unitaryGroup ι ℂ, ∀ j i l,
    (((U : Matrix ι ι ℂ) * ρ j * (U : Matrix ι ι ℂ)ᴴ) i l).im = 0

/-- Trace of the product of the selected states in increasing word position. -/
def traceWord {ι : Type} [Fintype ι] [DecidableEq ι] {n k : ℕ}
    (ρ : Fin n → Matrix ι ι ℂ) (w : Fin k → Fin n) : ℂ :=
  ((List.ofFn fun t => ρ (w t)).prod).trace

/-- Conjecture 1 of Guo–Pan–Wang–Du, arXiv:2608.28985v1, with its printed polarity. -/
def claim : Prop :=
  ∀ (d n : ℕ) (ρ : Fin n → Matrix (Fin d) (Fin d) ℂ),
    2 ≤ d → 3 ≤ n → Function.Injective ρ →
    (∀ j, (ρ j).PosSemidef ∧ (ρ j).trace = 1) →
    (CommonRealBasis ρ ↔ ∃ k : ℕ, 3 ≤ k ∧ k ≤ d * (d + 1) / 2 ∧
      ∃ w : Fin k → Fin n, (traceWord ρ w).im ≠ 0)

private def weights : Fin 3 → Fin 2 → ℝ :=
  ![![3 / 4, 1 / 4], ![1 / 4, 3 / 4], ![1 / 2, 1 / 2]]

private def realStates (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal (weights j)

private def states (j : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (realStates j).map Complex.ofReal

private theorem states_injective : Function.Injective states := by
  intro i j hij
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).re) hij
  fin_cases i <;> fin_cases j <;> norm_num [states, realStates, weights] at h ⊢

private theorem states_density (j : Fin 3) : (states j).PosSemidef ∧ (states j).trace = 1 := by
  have hdiag : states j = diagonal (fun i => (weights j i : ℂ)) := by
    simp [states, realStates, diagonal_map]
  rw [hdiag]
  constructor
  · apply PosDef.posSemidef
    apply posDef_diagonal_iff.mpr
    intro i
    rw [Complex.zero_lt_real]
    fin_cases j <;> fin_cases i <;> norm_num [weights]
  · fin_cases j <;> norm_num [trace, diag, weights, Fin.sum_univ_two]

private theorem states_real_words {k : ℕ} (w : Fin k → Fin 3) :
    (traceWord states w).im = 0 := by
  let f := RingHom.mapMatrix (m := Fin 2) Complex.ofRealHom
  let word := List.ofFn fun t => realStates (w t)
  have hw : List.ofFn (fun t => states (w t)) = word.map f := by
    simp [word, states, f, List.map_ofFn]
  change (trace (List.ofFn (fun t => states (w t))).prod).im = 0
  rw [hw, ← map_list_prod]
  change (trace (word.prod.map Complex.ofReal)).im = 0
  rw [← AddMonoidHom.map_trace Complex.ofRealHom.toAddMonoidHom]
  exact Complex.ofReal_im _

/-- The printed biconditional fails already for three distinct diagonal qubit states. -/
theorem result : ¬ claim := by
  intro h
  have hreal : CommonRealBasis states := by
    refine ⟨1, fun j i l => ?_⟩
    simp [states]
  obtain ⟨k, _, _, w, hw⟩ :=
    (h 2 3 states (by decide) (by decide) states_injective states_density).mp hreal
  exact hw (states_real_words w)

end

end D5.S3.Quantum.Information.SetImaginarity.PrintedConjecture
