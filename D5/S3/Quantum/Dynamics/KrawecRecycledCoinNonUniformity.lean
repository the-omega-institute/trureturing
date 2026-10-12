/- GID: D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim; result=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.result; claim=D5/S3/Quantum/Dynamics/KrawecRecycledCoinNonUniformity.claim
   digest: Nonuniformity of the recycled-coin walk at a nonexceptional memory parameter. -/

import D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section
open scoped BigOperators Topology
namespace D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity


def angle (φ : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then Real.pi / 4 else Real.pi * (1 + φ) / 4

def coinFlip {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ∑ b : Fin 2, (D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness.X3
    (angle φ c.1) c.2 b : ℂ) * ψ n (c.1, b)

def shift {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ (n + (if c.2 = 0 then 1 else -1)) c

def swap {d : ℕ} (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => ψ n (c.2, c.1)

def U {d : ℕ} (φ : ℝ) (ψ : ZMod d → Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  swap (shift (coinFlip φ ψ))

def initial {d : ℕ} (α : Fin 2 × Fin 2 → ℂ) : ZMod d → Fin 2 × Fin 2 → ℂ :=
  fun n c => if n = 0 then α c else 0

def p {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (t : ℕ) : ℝ :=
  ∑ c : Fin 2 × Fin 2, Complex.normSq
    (((U φ)^[t]) (initial (d := d) α) n c)

def avg {d : ℕ} (φ : ℝ) (α : Fin 2 × Fin 2 → ℂ)
    (n : ZMod d) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, p φ α n (t + 1)) / (T : ℝ)

def exceptional (d : ℕ) : Set ℝ :=
  if 12 ∣ d then {0, 1, 2, 4, 5, 6} else {0, 2, 4, 6}

def unitCoin (α : Fin 2 × Fin 2 → ℂ) : Prop :=
  (∑ c : Fin 2 × Fin 2, Complex.normSq (α c)) = 1

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∀ φ : ℝ, φ ∈ Set.Ico 0 8 → φ ∉ exceptional d →
      ∀ α : Fin 2 × Fin 2 → ℂ, unitCoin α →
        ∀ n : ZMod d,
          Filter.Tendsto (avg φ α n) Filter.atTop
            (nhds (1 / (d : ℝ)))

end D5.S3.Quantum.Dynamics.KrawecRecycledCoinNonUniformity
