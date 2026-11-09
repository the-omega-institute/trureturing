/- GID: D5/S3/Quantum/MatrixVarianceTreeReal
   generality: G
   mirror-B: D5/B/S3/Quantum/MatrixVarianceTreeReal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/MatrixVarianceTreeReal.family_defect_posSemidef; instance=D5/S3/Quantum/MatrixVarianceTreeReal.commonResponse
   digest: Real positive-definite matrix weights yield a square-remainder identity and a positive-semidefinite variance certificate. -/

/-
  Real-scalar companion of MatrixVarianceTree.lean.
  This file is kernel-checked with the pinned Mathlib toolchain; the complex
  quantum contract remains in the companion source and is intentionally not
  claimed as compiled because Matrix.PosDef requires PartialOrder ℂ.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix MatrixOrder

namespace D5.S3.Quantum.MatrixVarianceTreeReal

noncomputable section

variable {ι n m : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]

abbrev Weight (n : Type*) := Matrix n n ℝ
abbrev Response (n m : Type*) := Matrix n m ℝ

def aggregateWeight (A : ι → Weight n) : Weight n := ∑ i, A i

def aggregateResponse (B : ι → Response n m) : Response n m := ∑ i, B i

def commonResponse (A : ι → Weight n) (B : ι → Response n m) : Response n m :=
  (aggregateWeight A)⁻¹ * aggregateResponse B

def familyDefect (A : ι → Weight n) (B : ι → Response n m) : Matrix m m ℝ :=
  (∑ i, (B i)ᴴ * (A i)⁻¹ * B i) -
    (aggregateResponse B)ᴴ * (aggregateWeight A)⁻¹ * aggregateResponse B

def familySquareRemainder (A : ι → Weight n) (B : ι → Response n m) : Matrix m m ℝ :=
  ∑ i, ((B i - A i * commonResponse A B)ᴴ * (A i)⁻¹ *
    (B i - A i * commonResponse A B))

def MatrixVarianceIdentity : Prop :=
  ∀ (A : ι → Weight n) (B : ι → Response n m),
    Nonempty ι → (∀ i, (A i).PosDef) →
      familyDefect A B = familySquareRemainder A B

def MatrixVariancePositive : Prop :=
  ∀ (A : ι → Weight n) (B : ι → Response n m),
    Nonempty ι → (∀ i, (A i).PosDef) → (familyDefect A B).PosSemidef

def MatrixVarianceEquality : Prop :=
  ∀ (A : ι → Weight n) (B : ι → Response n m),
    Nonempty ι → (∀ i, (A i).PosDef) →
      familyDefect A B = 0 ↔
        ∀ i, (A i)⁻¹ * B i = commonResponse A B

def inverseChiSquare (ρ σ : Weight n) : ℝ :=
  (Matrix.trace ((ρ - σ) * σ⁻¹ * (ρ - σ)))

def QuantumRecordDiscardingContract : Prop :=
  ∀ (ρ σ : ι → Weight n),
    Nonempty ι →
    (∀ i, (ρ i).IsHermitian ∧ (σ i).PosDef) →
      inverseChiSquare (∑ i, ρ i) (∑ i, σ i) ≤
        ∑ i, inverseChiSquare (ρ i) (σ i)

theorem aggregateWeight_posDef (hι : Nonempty ι)
    (A : ι → Weight n) (hA : ∀ i, (A i).PosDef) :
    (aggregateWeight A).PosDef := by
  classical
  exact Matrix.posDef_sum (s := Finset.univ) Finset.univ_nonempty (by
    intro i hi
    exact hA i)

theorem aggregateWeight_isUnit (hι : Nonempty ι)
    (A : ι → Weight n) (hA : ∀ i, (A i).PosDef) :
    IsUnit (aggregateWeight A) :=
  (aggregateWeight_posDef hι A hA).isUnit

theorem square_term_expansion (A : Weight n) (B C : Response n m)
    (hA : A.PosDef) :
    ((B - A * C)ᴴ * A⁻¹ * (B - A * C)) =
      Bᴴ * A⁻¹ * B - Bᴴ * C - Cᴴ * B + Cᴴ * A * C := by
  classical
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hleft : A⁻¹ * A = (1 : Weight n) := Matrix.nonsing_inv_mul A hdet
  have hright : A * A⁻¹ = (1 : Weight n) := Matrix.mul_nonsing_inv A hdet
  have hself : Aᴴ = A := hA.isHermitian.eq
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hself]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.add_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hcancel : A⁻¹ * (A * C) = C := by
    rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]
  have hcancel' : Cᴴ * (A * C) = Cᴴ * A * C := by
    rw [← Matrix.mul_assoc]
  have h1 : Cᴴ * A * A⁻¹ * B = Cᴴ * B := by
    rw [Matrix.mul_assoc Cᴴ A A⁻¹, hright, Matrix.mul_one]
  have h2 : Cᴴ * A * A⁻¹ * (A * C) = Cᴴ * (A * C) := by
    rw [Matrix.mul_assoc Cᴴ A A⁻¹, hright, Matrix.mul_one]
  have h3 : Bᴴ * A⁻¹ * (A * C) = Bᴴ * C := by
    rw [Matrix.mul_assoc Bᴴ A⁻¹ (A * C), hcancel]
  rw [h1, h2, h3, hcancel']
  noncomm_ring

theorem family_defect_eq_square
    (A : ι → Weight n) (B : ι → Response n m)
    (hι : Nonempty ι) (hA : ∀ i, (A i).PosDef) :
    familyDefect A B = familySquareRemainder A B := by
  classical
  let S : Weight n := aggregateWeight A
  let T : Response n m := aggregateResponse B
  have hS : S.PosDef := by
    simpa [S] using aggregateWeight_posDef hι A hA
  have hdetS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hSleft : S⁻¹ * S = (1 : Weight n) := Matrix.nonsing_inv_mul S hdetS
  have hSright : S * S⁻¹ = (1 : Weight n) := Matrix.mul_nonsing_inv S hdetS
  have hterm : ∀ i,
      ((B i - A i * (S⁻¹ * T))ᴴ * (A i)⁻¹ *
        (B i - A i * (S⁻¹ * T))) =
        (B i)ᴴ * (A i)⁻¹ * B i - (B i)ᴴ * (S⁻¹ * T) -
          (S⁻¹ * T)ᴴ * B i + (S⁻¹ * T)ᴴ * A i * (S⁻¹ * T) := by
    intro i
    exact square_term_expansion (A i) (B i) (S⁻¹ * T) (hA i)
  have hsum :
      (∑ i, ((B i - A i * (S⁻¹ * T))ᴴ * (A i)⁻¹ *
        (B i - A i * (S⁻¹ * T)))) =
      (∑ i, (B i)ᴴ * (A i)⁻¹ * B i) -
        (∑ i, (B i)ᴴ) * (S⁻¹ * T) -
        (S⁻¹ * T)ᴴ * (∑ i, B i) +
        (S⁻¹ * T)ᴴ * S * (S⁻¹ * T) := by
    simp_rw [hterm]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Matrix.sum_mul Finset.univ (fun i => (B i)ᴴ) (S⁻¹ * T),
      ← Matrix.mul_sum Finset.univ (fun i => B i) (S⁻¹ * T)ᴴ,
      ← Matrix.sum_mul Finset.univ (fun i => (S⁻¹ * T)ᴴ * A i) (S⁻¹ * T),
      ← Matrix.mul_sum Finset.univ (fun i => A i) (S⁻¹ * T)ᴴ]
    rw [show S = aggregateWeight A by rfl]
    simp only [aggregateWeight]
  have hcenter :
      (S⁻¹ * T)ᴴ * S * (S⁻¹ * T) = Tᴴ * S⁻¹ * T := by
    have hSinv : (S⁻¹)ᴴ = S⁻¹ := (hS.inv).isHermitian.eq
    calc
      (S⁻¹ * T)ᴴ * S * (S⁻¹ * T) =
          (Tᴴ * (S⁻¹)ᴴ) * S * (S⁻¹ * T) := by
            rw [Matrix.conjTranspose_mul (S⁻¹) T]
      _ = (Tᴴ * S⁻¹) * S * (S⁻¹ * T) := by rw [hSinv]
      _ = Tᴴ * (S⁻¹ * S) * (S⁻¹ * T) := by
        rw [Matrix.mul_assoc Tᴴ S⁻¹ S]
      _ = Tᴴ * (S⁻¹ * T) := by rw [hSleft, Matrix.mul_one]
      _ = Tᴴ * S⁻¹ * T := by rw [Matrix.mul_assoc]
  change (∑ i, (B i)ᴴ * (A i)⁻¹ * B i) - Tᴴ * S⁻¹ * T = _
  rw [show familySquareRemainder A B =
      ∑ i, ((B i - A i * (S⁻¹ * T))ᴴ * (A i)⁻¹ *
        (B i - A i * (S⁻¹ * T))) by rfl]
  rw [hsum, hcenter]
  rw [← Matrix.conjTranspose_sum]
  change (∑ i, (B i)ᴴ * (A i)⁻¹ * B i) - Tᴴ * S⁻¹ * T =
    (∑ i, (B i)ᴴ * (A i)⁻¹ * B i) - Tᴴ * (S⁻¹ * T) -
      (S⁻¹ * T)ᴴ * T + Tᴴ * S⁻¹ * T
  have hSinv : (S⁻¹)ᴴ = S⁻¹ := (hS.inv).isHermitian.eq
  have hcross : (S⁻¹ * T)ᴴ * T = Tᴴ * S⁻¹ * T := by
    calc
      (S⁻¹ * T)ᴴ * T = (Tᴴ * (S⁻¹)ᴴ) * T := by
        rw [Matrix.conjTranspose_mul (S⁻¹) T]
      _ = (Tᴴ * S⁻¹) * T := by rw [hSinv]
      _ = Tᴴ * S⁻¹ * T := by rfl
  rw [hcross, Matrix.mul_assoc]
  noncomm_ring

theorem family_defect_eq_zero_of_common_response
    (A : ι → Weight n) (B : ι → Response n m)
    (hι : Nonempty ι) (hA : ∀ i, (A i).PosDef)
    (hcommon : ∀ i, (A i)⁻¹ * B i = commonResponse A B) :
    familyDefect A B = 0 := by
  rw [family_defect_eq_square A B hι hA]
  simp only [familySquareRemainder]
  apply Finset.sum_eq_zero
  intro i hi
  have hdet : IsUnit (A i).det :=
    (Matrix.isUnit_iff_isUnit_det (A i)).mp (hA i).isUnit
  have hright : A i * (A i)⁻¹ = (1 : Weight n) :=
    Matrix.mul_nonsing_inv (A i) hdet
  have hres : B i - A i * commonResponse A B = 0 := by
    calc
      B i - A i * commonResponse A B =
          A i * ((A i)⁻¹ * B i) - A i * commonResponse A B := by
            rw [← Matrix.mul_assoc, hright, Matrix.one_mul]
      _ = 0 := by rw [hcommon i]; noncomm_ring
  rw [hres]
  simp

theorem family_defect_posSemidef
    (A : ι → Weight n) (B : ι → Response n m)
    (hι : Nonempty ι) (hA : ∀ i, (A i).PosDef) :
    (familyDefect A B).PosSemidef := by
  rw [family_defect_eq_square A B hι hA]
  simp only [familySquareRemainder]
  apply Matrix.posSemidef_sum Finset.univ
  intro i hi
  exact (hA i).inv.posSemidef.conjTranspose_mul_mul_same
    (B i - A i * commonResponse A B)

/- The reverse implication (zero defect -> common response) requires the
   strict-positive quadratic-form API for complex Hermitian matrices; it is
   intentionally left as a later scoped target rather than asserted here. -/

/- A finite rooted tree is represented inductively. A branch has k+1 children,
   so leaves and positive branching are separated by construction. -/
inductive MatrixTree (n m : Type*) [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] where
  | leaf : Weight n → Response n m → MatrixTree n m
  | branch {k : Nat} : (Fin (k + 1) → MatrixTree n m) → MatrixTree n m

def treeWeight : MatrixTree n m → Weight n
  | .leaf A _ => A
  | .branch children => ∑ j, treeWeight (children j)

def treeResponse : MatrixTree n m → Response n m
  | .leaf _ B => B
  | .branch children => ∑ j, treeResponse (children j)

def treeCenter (T : MatrixTree n m) : Response n m :=
  (treeWeight T)⁻¹ * treeResponse T

def treeLeafEnergy : MatrixTree n m → Matrix m m ℝ
  | .leaf A B => Bᴴ * A⁻¹ * B
  | .branch children => ∑ j, treeLeafEnergy (children j)

def treeAggregateEnergy (T : MatrixTree n m) : Matrix m m ℝ :=
  (treeResponse T)ᴴ * (treeWeight T)⁻¹ * treeResponse T

def treeEdgeEnergy : MatrixTree n m → Matrix m m ℝ
  | .leaf _ _ => 0
  | .branch children =>
      ∑ j, ((treeCenter (children j) - treeCenter (.branch children))ᴴ *
        treeWeight (children j) *
        (treeCenter (children j) - treeCenter (.branch children)) +
        treeEdgeEnergy (children j))

def allWeightsPositive : MatrixTree n m → Prop
  | .leaf A _ => A.PosDef
  | .branch children => ∀ j, allWeightsPositive (children j)

def TreeVarianceIdentity : Prop :=
  ∀ (T : MatrixTree n m), allWeightsPositive T →
    treeLeafEnergy T - treeAggregateEnergy T = treeEdgeEnergy T

def TreeVariancePositive : Prop :=
  ∀ (T : MatrixTree n m), allWeightsPositive T →
    (treeLeafEnergy T - treeAggregateEnergy T).PosSemidef

def treeUniform : MatrixTree n m → Prop
  | .leaf _ _ => True
  | .branch children =>
      (∀ j, treeUniform (children j)) ∧
      (∀ j, treeCenter (children j) = treeCenter (.branch children))

def TreeVarianceEquality : Prop :=
  ∀ (T : MatrixTree n m), allWeightsPositive T →
    treeLeafEnergy T - treeAggregateEnergy T = 0 ↔
      treeUniform T

end
end D5.S3.Quantum.MatrixVarianceTreeReal
