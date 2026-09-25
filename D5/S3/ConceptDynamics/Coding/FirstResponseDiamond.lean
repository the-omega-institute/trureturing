/- GID: D5/S3/ConceptDynamics/Coding/FirstResponseDiamond
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FirstResponseDiamond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal first-level row and column classes construct an explicit quotient diamond.
-/

import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FirstResponseDiamond

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

def columnMembership {q r : ℕ} (class : Fin q → Fin r) : CountMat r q :=
  fun f v => if class v = f then 1 else 0

def rowMembership {q s : ℕ} (class : Fin q → Fin s) : CountMat q s :=
  fun u h => if class u = h then 1 else 0

def columnSelector {q r : ℕ} (representative : Fin r → Fin q) : CountMat q r :=
  fun v f => if representative f = v then 1 else 0

def rowSelector {q s : ℕ} (representative : Fin s → Fin q) : CountMat s q :=
  fun h u => if representative h = u then 1 else 0

/- The two response partitions calculate the common rectangular matrix and
   both exchanged products directly from the entries of C. -/
theorem first_response_diamond {q r s : ℕ} (C : CountMat q q)
    (leftClass : Fin q → Fin r) (rightClass : Fin q → Fin s)
    (leftRep : Fin r → Fin q) (rightRep : Fin s → Fin q)
    (hleftRep : ∀ f, leftClass (leftRep f) = f)
    (hrightRep : ∀ h, rightClass (rightRep h) = h)
    (hcolumns : ∀ u v, leftClass u = leftClass v → ∀ i, C i u = C i v)
    (hrows : ∀ u v, rightClass u = rightClass v → ∀ k, C u k = C v k) :
    ∃ D : CountMat s r,
      columnMembership leftClass * C * columnSelector leftRep =
        (columnMembership leftClass * rowMembership rightClass) * D ∧
      rowSelector rightRep * C * rowMembership rightClass =
        D * (columnMembership leftClass * rowMembership rightClass) ∧
      Nonempty (ExchangeChain ℕ
        (columnMembership leftClass * C * columnSelector leftRep)
        (rowSelector rightRep * C * rowMembership rightClass) 1) := by
  let IL := columnMembership leftClass
  let IJ := rowMembership rightClass
  let SL := columnSelector leftRep
  let SJ := rowSelector rightRep
  let D : CountMat s r := fun h f => C (rightRep h) (leftRep f)
  have hentry (u v : Fin q) : C u v = D (rightClass u) (leftClass v) := by
    calc
      C u v = C (rightRep (rightClass u)) v :=
        hrows u _ (hrightRep _).symm v
      _ = C (rightRep (rightClass u)) (leftRep (leftClass v)) :=
        hcolumns v _ (hleftRep _).symm _
      _ = D (rightClass u) (leftClass v) := rfl
  have hfactor : C = IJ * D * IL := by
    ext u v
    calc
      C u v = D (rightClass u) (leftClass v) := hentry u v
      _ = (IJ * D * IL) u v := by
        simp [Matrix.mul_apply, IJ, IL, rowMembership, columnMembership]
  have hleft : IL * SL = 1 := by
    ext f g
    by_cases h : f = g <;>
      simp [Matrix.mul_apply, IL, SL, columnMembership, columnSelector,
        hleftRep, h, eq_comm]
  have hright : SJ * IJ = 1 := by
    ext h k
    by_cases heq : h = k <;>
      simp [Matrix.mul_apply, SJ, IJ, rowMembership, rowSelector,
        hrightRep, heq, eq_comm]
  have hcol : IL * C * SL = (IL * IJ) * D := by
    calc
      IL * C * SL = IL * (IJ * D * IL) * SL := by rw [hfactor]
      _ = (IL * IJ) * D * (IL * SL) := by simp only [Matrix.mul_assoc]
      _ = (IL * IJ) * D := by rw [hleft, Matrix.mul_one]
  have hrow : SJ * C * IJ = D * (IL * IJ) := by
    calc
      SJ * C * IJ = (SJ * IJ) * D * (IL * IJ) := by
        rw [hfactor]
        simp only [Matrix.mul_assoc]
      _ = D * (IL * IJ) := by rw [hright, Matrix.one_mul]
  refine ⟨D, hcol, hrow, ?_⟩
  rw [hcol, hrow]
  exact ⟨ExchangeChain.cons (IL * IJ) D (ExchangeChain.nil _)⟩

#print axioms first_response_diamond

end D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
