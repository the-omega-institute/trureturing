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

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-! Directed positivity and finite phase balance on the original spin factor. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

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

private def evaluationLinear (α : Evaluation) : E →ₗ[ℝ] ℝ where
  toFun := evaluate α
  map_add' a b := by
    simp [evaluate, dot, dotProduct, Fin.sum_univ_three]
    ring
  map_smul' r a := by
    simp [evaluate, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
    ring

private theorem evaluations_separate (a b : E)
    (h : ∀ α : Evaluation, evaluate α a = evaluate α b) : a = b := by
  have hs := h ⟨1, 0, by norm_num [vnorm, dot, dotProduct]⟩
  simp only [evaluate, one_mul, dot, zero_dotProduct, add_zero] at hs
  apply Prod.ext hs
  funext i
  have hv := h ⟨1, Pi.single i 1, by simp [vnorm, dot, single_dotProduct]⟩
  simp [evaluate, dot, single_dotProduct] at hv
  linarith

/-- The two directed entries force antisymmetry of the same total map. -/
theorem p2_skew (D : E → E → E) (hP : P2 D) : skew D := by
  intro a b
  apply evaluations_separate
  intro α
  have h := congrArg Complex.im ((hP α a b).1.apply 0 1)
  simp [gram2, readout, Complex.star_def] at h
  change evaluate α (D b a) = evaluationLinear α (-D a b)
  rw [map_neg]
  exact h

private theorem p2_self (D : E → E → E) (hP : P2 D) (a : E) : D a a = 0 := by
  have h := p2_skew D hP a a
  apply Prod.ext
  · change (D a a).1 = 0
    have h' := congrArg Prod.fst h
    simp only [Prod.fst_neg] at h'
    linarith
  · funext i
    change (D a a).2 i = 0
    have h' := congrArg (fun e : E => e.2 i) h
    change (D a a).2 i = -(D a a).2 i at h'
    linarith

/-- The exact real determinant bound retains the real off-diagonal entry. -/
theorem p2_determinant_bound (D : E → E → E) (hP : P2 D)
    (α : Evaluation) (a b : E) :
    (evaluate α (D a b)) ^ 2 ≤
      evaluate α (jordan a a) * evaluate α (jordan b b) -
        (evaluate α (jordan a b)) ^ 2 := by
  have hd := (hP α a b).det_nonneg
  have hj : jordan b a = jordan a b := by
    apply Prod.ext
    · simp [jordan, dot, dotProduct_comm, mul_comm, add_comm]
    · simp [jordan, add_comm]
  have hsk := p2_skew D hP a b
  have he : evaluate α (D b a) = -evaluate α (D a b) := by
    change evaluationLinear α (D b a) = -evaluationLinear α (D a b)
    rw [hsk, map_neg]
  have ez : evaluate α 0 = 0 := by simp [evaluate, dot]
  have hd' := (Complex.nonneg_iff.mp hd).1
  simp [Matrix.det_fin_two, gram2, readout, p2_self D hP, hj, he,
    ez, Complex.mul_re, Complex.mul_im] at hd'
  nlinarith

/-- Proportional original inputs vanish, including zero and negative scaling. -/
theorem p2_proportional (D : E → E → E) (hP : P2 D) : proportionalZero D := by
  intro r a
  have hz : D (r • a) a = 0 := by
    apply evaluations_separate
    intro α
    have hb := p2_determinant_bound D hP α (r • a) a
    have h1 : evaluate α (jordan (r • a) (r • a)) =
        r ^ 2 * evaluate α (jordan a a) := by
      simp [evaluate, jordan, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      ring
    have h2 : evaluate α (jordan (r • a) a) =
        r * evaluate α (jordan a a) := by
      simp [evaluate, jordan, dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
      ring
    rw [h1, h2] at hb
    have he : evaluate α (D (r • a) a) = 0 := by nlinarith [sq_nonneg (evaluate α (D (r • a) a))]
    simpa [evaluate, dot] using he
  refine ⟨hz, ?_⟩
  rw [p2_skew D hP (r • a) a, hz, neg_zero]

/-- Both original zero rows follow without any assumed regularity. -/
theorem p2_zero_rows (D : E → E → E) (hP : P2 D) : zeroRows D := by
  constructor
  · intro b
    change D 0 b = 0
    simpa using (p2_proportional D hP 0 b).1
  · intro a
    change D a 0 = 0
    simpa using (p2_proportional D hP 0 a).2

/-- Phase balance is equivalent to the element-valued finite-difference law. -/
theorem pb_iff_finite_difference (D : E → E → E) :
    PB D ↔ ∀ a b c, finiteDifference D a b c = 0 := by
  have expansion (α : Evaluation) (a b c : E) :
      squareReadout D α (phaseR D a b c) (phaseS D a b c) -
        squareReadout D α (b - D a b + jordan a c) (c - jordan a b - D a c) =
          2 * evaluate α (finiteDifference D a b c) := by
    simp [squareReadout, phaseR, phaseS, finiteDifference, evaluate, jordan,
      dot, dotProduct, Fin.sum_univ_three, smul_eq_mul]
    ring
  constructor
  · intro h a b c
    apply evaluations_separate
    intro α
    have he := expansion α a b c
    rw [h α a b c] at he
    simp only [sub_self] at he
    have hz : evaluate α (finiteDifference D a b c) = 0 := by linarith
    simpa [evaluate, dot] using hz
  · intro h α a b c
    have he := expansion α a b c
    rw [h a b c] at he
    simp [evaluate, dot] at he
    exact sub_eq_zero.mp he

end D5.S3.Quantum.SpinFactor.OriginalDContract
