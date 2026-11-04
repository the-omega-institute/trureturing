/- GID: D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim; result=D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result; claim=D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim
   digest: An inverse spread gives a non-group projective toric 2-design in dimension 27. -/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
The formal reading is the representative slice with first phase zero in
Iosue–Mooney–Ehrenberg–Gorshkov, arXiv:2311.13479v3, equations
`eq:repr-proj-toric` and `eq:toric-angle`. The identity-containing reading
of Conjecture 4.9 is fixed by preregistration #26419.
Mathlib calls the angle exponential `Real.Angle.toCircle`.
Admission basis: open-problem-resolution (refutation).
-/

open scoped BigOperators
open Matrix
noncomputable section
namespace D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup

/-- The second moment condition in representatives, multiplied by the cardinality. -/
def design2 {d : ℕ} (X : Finset (Fin d → Real.Angle)) : Prop :=
  ∀ a₁ a₂ b₁ b₂ : Fin d,
    (((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)) →
      ∑ φ ∈ X, (Real.Angle.toCircle (φ a₁ + φ a₂ - φ b₁ - φ b₂) : ℂ) = X.card) ∧
    ((¬ ((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))) →
      ∑ φ ∈ X, (Real.Angle.toCircle (φ a₁ + φ a₂ - φ b₁ - φ b₂) : ℂ) = 0)

/-- The unnormalized MUB overlap condition. -/
def mubOverlap {d : ℕ} (X : Finset (Fin d → Real.Angle)) : Prop :=
  ∀ φ ∈ X, ∀ θ ∈ X, φ ≠ θ →
    ‖∑ j, (Real.Angle.toCircle (φ j - θ j) : ℂ)‖ ^ 2 = 0 ∨
    ‖∑ j, (Real.Angle.toCircle (φ j - θ j) : ℂ)‖ ^ 2 = (d : ℝ)

def claim : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (X : Finset (Fin d → Real.Angle)),
    (∀ φ ∈ X, φ ⟨0, hd⟩ = 0) → X.card = d ^ 2 → design2 X → mubOverlap X → 0 ∈ X →
      ∃ H : AddSubgroup (Fin d → Real.Angle), (H : Set (Fin d → Real.Angle)) = ↑X

private def coord : Fin 27 ≃ (Fin 3 → ZMod 3) :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => (ZMod.finEquiv 3).toEquiv)

private def phase (k : ZMod 3) : Real.Angle := ((2 * Real.pi / 3) * k.val : ℝ)

private def matrices : Fin 27 → Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  ![!![0, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 1, 2; 1, 1, 2; 2, 2, 0],
    !![0, 2, 1; 2, 2, 1; 1, 1, 0],
    !![0, 0, 2; 0, 2, 1; 2, 1, 2],
    !![1, 1, 1; 1, 0, 2; 1, 2, 2],
    !![1, 2, 2; 2, 0, 2; 2, 2, 1],
    !![0, 0, 1; 0, 1, 2; 1, 2, 1],
    !![2, 1, 1; 1, 0, 1; 1, 1, 2],
    !![2, 2, 2; 2, 0, 1; 2, 1, 1],
    !![2, 0, 2; 0, 2, 0; 2, 0, 0],
    !![1, 2, 0; 2, 1, 2; 0, 2, 2],
    !![1, 2, 1; 2, 2, 0; 1, 0, 1],
    !![1, 1, 2; 1, 2, 2; 2, 2, 2],
    !![2, 2, 0; 2, 2, 2; 0, 2, 0],
    !![0, 2, 2; 2, 1, 0; 2, 0, 1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![2, 0, 1; 0, 0, 2; 1, 2, 0],
    !![1, 0, 0; 0, 2, 2; 0, 2, 1],
    !![1, 0, 1; 0, 1, 0; 1, 0, 0],
    !![2, 1, 2; 1, 1, 0; 2, 0, 2],
    !![2, 1, 0; 1, 2, 1; 0, 1, 1],
    !![0, 2, 0; 2, 0, 0; 0, 0, 2],
    !![2, 0, 0; 0, 1, 1; 0, 1, 2],
    !![1, 0, 2; 0, 0, 1; 2, 1, 0],
    !![2, 2, 1; 2, 1, 1; 1, 1, 1],
    !![0, 1, 1; 1, 2, 0; 1, 0, 2],
    !![1, 1, 0; 1, 1, 1; 0, 1, 0]]

private def polynomial (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (b x : Fin 3 → ZMod 3) : ZMod 3 := x ⬝ᵥ M.mulVec x + b ⬝ᵥ x

private def point (p : Fin 27 × (Fin 3 → ZMod 3)) (j : Fin 27) : Real.Angle :=
  phase (polynomial (matrices p.1) p.2 (coord j))

private def counterexample : Finset (Fin 27 → Real.Angle) := by
  classical
  exact Finset.univ.image point

private theorem phase_character (k : ZMod 3) :
    (Real.Angle.toCircle (phase k) : ℂ) = ZMod.stdAddChar k := by
  sorry

private theorem phase_add (a b : ZMod 3) : phase (a + b) = phase a + phase b := by
  sorry

private theorem phase_injective : Function.Injective phase := by
  sorry

private theorem coord_zero : coord 0 = 0 := by
  sorry

private theorem matrices_symmetric (i : Fin 27) : (matrices i).IsSymm := by
  sorry

private theorem spread (i j : Fin 27) (h : i ≠ j) : (matrices i - matrices j).det ≠ 0 := by
  sorry

private theorem matrices_not_add :
    ∀ i : Fin 27, matrices i ≠ matrices 1 + matrices 3 := by
  sorry

private theorem character_orthogonality (w : Fin 3 → ZMod 3) :
    ∑ x : Fin 3 → ZMod 3, ZMod.stdAddChar (w ⬝ᵥ x) =
      if w = 0 then (27 : ℂ) else 0 := by
  sorry

private theorem quadratic_energy (M : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hM : M.IsSymm) (hD : M.det ≠ 0) (b : Fin 3 → ZMod 3) :
    ‖∑ x : Fin 3 → ZMod 3, ZMod.stdAddChar (polynomial M b x)‖ ^ 2 = 27 := by
  sorry

private theorem spread_evaluation (g : Fin 3 → ZMod 3) (hg : g ≠ 0) :
    Function.Bijective (fun i : Fin 27 => (matrices i).mulVec g) := by
  sorry

private theorem polynomial_unique (A B : Matrix (Fin 3) (Fin 3) (ZMod 3))
    (hA : A.IsSymm) (hB : B.IsSymm) (b c : Fin 3 → ZMod 3)
    (h : ∀ x, polynomial A b x = polynomial B c x) : A = B ∧ b = c := by
  sorry

private theorem exponent_overlap (i k : Fin 27) (b c : Fin 3 → ZMod 3)
    (h : (i, b) ≠ (k, c)) :
    ‖∑ x : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) b x - polynomial (matrices k) c x)‖ ^ 2 = 0 ∨
    ‖∑ x : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) b x - polynomial (matrices k) c x)‖ ^ 2 = 27 := by
  sorry

private theorem exponent_moment (a₁ a₂ b₁ b₂ : Fin 3 → ZMod 3) :
    (let S := ∑ i : Fin 27, ∑ c : Fin 3 → ZMod 3,
      ZMod.stdAddChar (polynomial (matrices i) c a₁ + polynomial (matrices i) c a₂ -
        polynomial (matrices i) c b₁ - polynomial (matrices i) c b₂)
    (((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁)) → S = 729) ∧
    ((¬ ((a₁ = b₁ ∧ a₂ = b₂) ∨ (a₁ = b₂ ∧ a₂ = b₁))) → S = 0)) := by
  sorry

private theorem point_injective : Function.Injective point := by
  sorry

private theorem counterexample_anchored :
    ∀ φ ∈ counterexample, φ ⟨0, by decide⟩ = 0 := by
  sorry

private theorem counterexample_card : counterexample.card = 27 ^ 2 := by
  sorry

private theorem counterexample_design : design2 counterexample := by
  sorry

private theorem counterexample_overlap : mubOverlap counterexample := by
  sorry

private theorem counterexample_zero : 0 ∈ counterexample := by
  sorry

private theorem counterexample_not_group :
    ¬ ∃ H : AddSubgroup (Fin 27 → Real.Angle),
      (H : Set (Fin 27 → Real.Angle)) = ↑counterexample := by
  sorry

theorem result : ¬ claim := by
  intro h
  exact counterexample_not_group
    (h 27 (by decide) counterexample counterexample_anchored counterexample_card
      counterexample_design counterexample_overlap counterexample_zero)

end D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup
