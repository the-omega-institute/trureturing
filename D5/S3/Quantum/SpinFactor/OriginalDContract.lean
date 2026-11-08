/- GID: D5/S3/Quantum/SpinFactor/OriginalDContract
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinFactor/OriginalDContract
   mirror-E: none(waiver:source-only-contract)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.CrossProduct]
   utility: none
   digest: The complete H2 original carrier, directed two-label positivity, and phase-balance contract.

This module records the exact original-domain contract used by the H2 classification.
The arbitrary original map is kept as a total function.  No regularity, unit row,
translation, bilinearity, or source-realisation premise is hidden in the definitions.
The classification and the finite two-axis rotation argument are downstream consumers.
-/

import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.Quantum.SpinFactor.OriginalDContract

abbrev Vec := Fin 3 → ℝ
abbrev E := ℝ × Vec

def unit : E := (1, 0)

def dot (x y : Vec) : ℝ := x ⬝ᵥ y

def vnorm (x : Vec) : ℝ := Real.sqrt (dot x x)

def jordan (a b : E) : E :=
  (a.1 * b.1 + dot a.2 b.2, a.1 • b.2 + b.1 • a.2)

def cone (a : E) : Prop := vnorm a.2 ≤ a.1

def originalNorm (a : E) : ℝ := |a.1| + vnorm a.2

structure Evaluation where
  mass : ℝ
  vector : Vec
  positive : vnorm vector ≤ mass

def evaluate (α : Evaluation) (a : E) : ℝ :=
  α.mass * a.1 + dot α.vector a.2

def allEvaluations : Set Evaluation := Set.univ

def cross (x y : Vec) : Vec :=
  ![x 1 * y 2 - x 2 * y 1,
    x 2 * y 0 - x 0 * y 2,
    x 0 * y 1 - x 1 * y 0]

inductive Orientation where
  | plus
  | minus

def crossD (ε : Orientation) (a b : E) : E :=
  (0, match ε with | .plus => cross a.2 b.2 | .minus => -(cross a.2 b.2))

def scalarPart (a : E) : ℝ := a.1
def vectorPart (a : E) : Vec := a.2

def readout (D : E → E → E) (α : Evaluation) (a b : E) : ℂ :=
  (evaluate α (jordan a b) : ℂ) - Complex.I * (evaluate α (D a b) : ℂ)

def gram2 (D : E → E → E) (α : Evaluation) (a b : E) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![readout D α a a, readout D α a b;
     readout D α b a, readout D α b b]

/-- Actual directed complex two-label positivity, with both off-diagonal entries
    computed from the same original D. -/
def P2 (D : E → E → E) : Prop :=
  ∀ (α : Evaluation) (a b : E), (gram2 D α a b).PosSemidef

def squareReadout (D : E → E → E) (α : Evaluation) (b c : E) : ℝ :=
  evaluate α (jordan b b) + evaluate α (jordan c c) +
    2 * evaluate α (D b c)

def phaseR (D : E → E → E) (a b c : E) : E :=
  b + D a b - jordan a c

def phaseS (D : E → E → E) (a b c : E) : E :=
  c + jordan a b + D a c

/-- The original ±1 phase-square balance, retaining the same D in every slot. -/
def PB (D : E → E → E) : Prop :=
  ∀ (α : Evaluation) (a b c : E),
    squareReadout D α (phaseR D a b c) (phaseS D a b c) =
      squareReadout D α (b - D a b + jordan a c) (c - jordan a b - D a c)

def skew (D : E → E → E) : Prop := ∀ a b, D b a = -D a b

def zeroRows (D : E → E → E) : Prop :=
  (∀ b, D (0, 0) b = 0) ∧ (∀ a, D a (0, 0) = 0)

def proportionalZero (D : E → E → E) : Prop :=
  ∀ (r : ℝ) (a : E), D (r • a) a = 0 ∧ D a (r • a) = 0

def basicOriginalD (D : E → E → E) : Prop :=
  skew D ∧ zeroRows D ∧ proportionalZero D

def finiteDifference (D : E → E → E) (a b c : E) : E :=
  D (b + D a b - jordan a c) (c + jordan a b + D a c) -
    D (b - D a b + jordan a c) (c - jordan a b - D a c) +
    2 • jordan b (D a b - jordan a c) +
    2 • jordan c (jordan a b + D a c)

def classificationStatement : Prop :=
  ∀ D : E → E → E, P2 D ∧ PB D ↔
    ∃ ε : Orientation, ∀ a b, D a b = crossD ε a b

theorem jordan_comm (a b : E) : jordan a b = jordan b a := by
  apply Prod.ext
  · simp [jordan, dot, add_comm, mul_comm]
  · funext i
    simp [jordan, dot, add_comm, mul_comm]

theorem jordan_unit_left (a : E) : jordan unit a = a := by
  apply Prod.ext
  · simp [unit, jordan, dot]
  · funext i
    simp [unit, jordan, dot]

theorem jordan_unit_right (a : E) : jordan a unit = a := by
  rw [jordan_comm, jordan_unit_left]

theorem cross_swap (x y : Vec) : cross y x = -(cross x y) := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_zero_left (y : Vec) : cross 0 y = 0 := by
  funext i
  fin_cases i <;> simp [cross]

theorem cross_zero_right (x : Vec) : cross x 0 = 0 := by
  rw [cross_swap, cross_zero_left, neg_zero]

theorem cross_self (x : Vec) : cross x x = 0 := by
  funext i
  fin_cases i <;> simp [cross]

theorem cross_add_left (x y z : Vec) : cross (x + y) z = cross x z + cross y z := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_add_right (x y z : Vec) : cross x (y + z) = cross x y + cross x z := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem cross_smul_left (r : ℝ) (x y : Vec) : cross (r • x) y = r • cross x y := by
  funext i
  fin_cases i <;> simp [cross, smul_eq_mul] <;> ring

theorem cross_smul_right (r : ℝ) (x y : Vec) : cross x (r • y) = r • cross x y := by
  funext i
  fin_cases i <;> simp [cross, smul_eq_mul] <;> ring

theorem crossD_skew (ε : Orientation) : skew (crossD ε) := by
  intro a b
  simp only [crossD]
  rw [cross_swap]
  cases ε <;> simp

theorem crossD_zero (ε : Orientation) : zeroRows (crossD ε) := by
  constructor
  · intro b
    simp [crossD, cross_zero_left]
  · intro a
    simp [crossD, cross_zero_right]

theorem crossD_proportional (ε : Orientation) : proportionalZero (crossD ε) := by
  intro r a
  constructor
  · simp [crossD, cross_smul_left, cross_self]
  · simp [crossD, cross_smul_right, cross_self]

theorem crossD_basic (ε : Orientation) : basicOriginalD (crossD ε) := by
  exact ⟨crossD_skew ε, crossD_zero ε, crossD_proportional ε⟩

def phaseBalanceDifference (D : E → E → E) (α : Evaluation) (a b c : E) : ℝ :=
  squareReadout D α (phaseR D a b c) (phaseS D a b c) -
    squareReadout D α (b - D a b + jordan a c) (c - jordan a b - D a c)

theorem phaseBalanceDifference_zero
    (D : E → E → E) (hPB : PB D) (α : Evaluation) (a b c : E) :
    phaseBalanceDifference D α a b c = 0 := by
  dsimp [phaseBalanceDifference]
  exact sub_eq_zero.mpr (hPB α a b c)

end D5.S3.Quantum.SpinFactor.OriginalDContract
