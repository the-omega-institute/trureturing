/- GID: D5/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Solitons/NambuKahanCremonaDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Graffeo--Gubbiotti's generic quadratic Nambu KHK map factors through cremona -/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Graffeo--Gubbiotti's generic quadratic Nambu KHK map factors through the
standard four-dimensional Cremona lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition

open Matrix
open scoped Matrix

noncomputable section

private def complexMatrix (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  A.map (algebraMap ℝ ℂ)

private def nambuLinearPart (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j =>
    crossProduct (complexMatrix A *ᵥ x)
        (complexMatrix B *ᵥ (Pi.single j 1)) i +
      crossProduct (complexMatrix A *ᵥ (Pi.single j 1))
        (complexMatrix B *ᵥ x) i

/-- The source KHK matrix, with its linear part written by cross-product columns. -/
def kahanMatrix (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) (X : Fin 4 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (X 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
    (2 * (h : ℂ)) • nambuLinearPart A B (fun i : Fin 3 => X i.castSucc)

/-- The homogeneous KHK lift of the quadratic Nambu system. -/
def kahan (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ) (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Fin.snoc ((kahanMatrix A B h X).adjugate *ᵥ (fun i : Fin 3 => X i.castSucc))
    (kahanMatrix A B h X).det

/-- The standard cubic Cremona lift in four homogeneous coordinates. -/
def cremona (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![X 1 * X 2 * X 3, X 0 * X 2 * X 3, X 0 * X 1 * X 3, X 0 * X 1 * X 2]

def claim : Prop :=
  ∀ A B : Matrix (Fin 3) (Fin 3) ℝ, A.PosDef → B.PosDef →
    (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
      ∀ h : ℝ, 0 < h →
        ∃ l₁ l₂ : Matrix (Fin 4) (Fin 4) ℂ,
          IsUnit l₁.det ∧ IsUnit l₂.det ∧
            ∀ X : Fin 4 → ℂ, kahan A B h X = l₂ *ᵥ cremona (l₁ *ᵥ X)

private def eulerVector (a₁ a₂ a₃ : ℂ) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![a₁ * y 1 * y 2, a₂ * y 0 * y 2, a₃ * y 0 * y 1]

private def eulerJacobian (a₁ a₂ a₃ : ℂ) (y : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, a₁ * y 2, a₁ * y 1;
     a₂ * y 2, 0, a₂ * y 0;
     a₃ * y 1, a₃ * y 0, 0]

private def eulerMatrix (a₁ a₂ a₃ h : ℂ) (X : Fin 4 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (X 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
    (h / 2) • eulerJacobian a₁ a₂ a₃ (fun i : Fin 3 => X i.castSucc)

private def eulerPhi (a₁ a₂ a₃ h : ℂ) (X : Fin 4 → ℂ) : Fin 4 → ℂ :=
  Fin.snoc ((eulerMatrix a₁ a₂ a₃ h X).adjugate *ᵥ (fun i : Fin 3 => X i.castSucc))
    (eulerMatrix a₁ a₂ a₃ h X).det

private def allOnes (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun _ _ => 1

private def g₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) - allOnes 4

private def T (a₁ a₂ a₃ h : ℂ) (α β γ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-β * γ * h, -α * γ * h, α * β * h, -2;
      β * γ * h, -α * γ * h, -α * β * h, -2;
      -β * γ * h, α * γ * h, -α * β * h, -2;
      β * γ * h, α * γ * h, α * β * h, -2]

private theorem euler_top_identity (a₁ a₂ a₃ h α β γ : ℂ)
    (hα : α ^ 2 = a₁) (hβ : β ^ 2 = a₂) (hγ : γ ^ 2 = a₃) :
    ∀ X : Fin 4 → ℂ,
      T a₁ a₂ a₃ h α β γ *ᵥ eulerPhi a₁ a₂ a₃ h X =
        (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (T a₁ a₂ a₃ h α β γ *ᵥ X)) := by
  sorry

private theorem det_T (a₁ a₂ a₃ h α β γ : ℂ) :
    (T a₁ a₂ a₃ h α β γ).det = 32 * α ^ 2 * β ^ 2 * γ ^ 2 * h ^ 3 := by
  sorry

private theorem g₀_unit : IsUnit g₀.det := by
  sorry

private theorem whitening
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hrank : ∀ t : ℝ, 2 ≤ (B - t • A).rank) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℝ, IsUnit P.det ∧
      ∃ mu : Fin 3 → ℝ,
        Pᵀ * A * P = 1 ∧ Pᵀ * B * P = diagonal mu ∧
          ∀ i j : Fin 3, i ≠ j → mu i ≠ mu j := by
  sorry

private theorem covariance
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
    (P : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ)
    (hP : IsUnit P.det)
    (hA : Pᵀ * A * P = 1) (hB : Pᵀ * B * P = diagonal mu)
    (ha : ∀ i j : Fin 3, i ≠ j → mu i ≠ mu j) :
    ∃ a₁ a₂ a₃ α β γ : ℂ,
      α ^ 2 = a₁ ∧ β ^ 2 = a₂ ∧ γ ^ 2 = a₃ ∧
        ∀ X : Fin 4 → ℂ,
          kahan A B h X =
            (fun i => X i) := by
  sorry

private theorem assembly
    (he : ∀ (a₁ a₂ a₃ h α β γ : ℂ), α ^ 2 = a₁ → β ^ 2 = a₂ → γ ^ 2 = a₃ →
      ∀ X : Fin 4 → ℂ,
        T a₁ a₂ a₃ h α β γ *ᵥ eulerPhi a₁ a₂ a₃ h X =
          (-1 / 8 : ℂ) • (g₀ *ᵥ cremona (T a₁ a₂ a₃ h α β γ *ᵥ X)))
    (hd : ∀ (a₁ a₂ a₃ h α β γ : ℂ),
      (T a₁ a₂ a₃ h α β γ).det = 32 * α ^ 2 * β ^ 2 * γ ^ 2 * h ^ 3)
    (hg : IsUnit g₀.det)
    (hw : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ), A.PosDef → B.PosDef →
      (∀ t : ℝ, 2 ≤ (B - t • A).rank) →
      ∃ P : Matrix (Fin 3) (Fin 3) ℝ, IsUnit P.det ∧
        ∃ mu : Fin 3 → ℝ,
          Pᵀ * A * P = 1 ∧ Pᵀ * B * P = diagonal mu ∧
            ∀ i j : Fin 3, i ≠ j → mu i ≠ mu j)
    (hc : ∀ (A B : Matrix (Fin 3) (Fin 3) ℝ) (h : ℝ)
      (P : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ), IsUnit P.det →
      Pᵀ * A * P = 1 → Pᵀ * B * P = diagonal mu →
      (∀ i j : Fin 3, i ≠ j → mu i ≠ mu j) →
      ∃ a₁ a₂ a₃ α β γ : ℂ,
        α ^ 2 = a₁ ∧ β ^ 2 = a₂ ∧ γ ^ 2 = a₃ ∧
          ∀ X : Fin 4 → ℂ, kahan A B h X = X) :
    claim := by
  sorry

theorem result : claim := by
  apply assembly
  · intro a₁ a₂ a₃ h α β γ hα hβ hγ
    exact euler_top_identity a₁ a₂ a₃ h α β γ hα hβ hγ
  · intro a₁ a₂ a₃ h α β γ
    exact det_T a₁ a₂ a₃ h α β γ
  · exact g₀_unit
  · intro A B hA hB hrank
    exact whitening A B hA hB hrank
  · intro A B h P mu hP hA hB ha
    exact covariance A B h P mu hP hA hB ha

end

end D5.S3.FluidDynamics.Solitons.NambuKahanCremonaDecomposition
