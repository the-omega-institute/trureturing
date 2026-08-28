/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionAction
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Explicit matrices, permutations, and word tables encode the A5 action over F5. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

/-- The order-three matrix `A` displayed in the source. -/
def matrixA : Matrix (Fin 3) (Fin 3) F5 :=
  ![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]]

/-- The order-five matrix `B` displayed in the source. -/
def matrixB : Matrix (Fin 3) (Fin 3) F5 :=
  ![![4, 4, 3], ![1, 0, 4], ![0, 1, 4]]

private def matrixAInv : Matrix (Fin 3) (Fin 3) F5 :=
  ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

private def matrixBInv : Matrix (Fin 3) (Fin 3) F5 :=
  ![![1, 2, 1], ![1, 1, 2], ![1, 1, 1]]

/-- The projective permutation induced by the source matrix `A`. -/
private def projectiveA : Equiv.Perm AxisChart :=
  { toFun := ![6, 0, 7, 9, 8, 10, 1, 11, 21, 16, 26, 2, 12, 24, 18,
      30, 3, 13, 22, 20, 29, 4, 14, 25, 17, 28, 5, 15, 23, 19, 27]
    invFun := ![1, 6, 11, 16, 21, 26, 0, 2, 4, 3, 5, 7, 12, 17, 22,
      27, 9, 24, 14, 29, 19, 8, 18, 28, 13, 23, 10, 30, 25, 20, 15]
    left_inv := by decide
    right_inv := by decide }

/-- The projective permutation induced by the source matrix `B`. -/
private def projectiveB : Equiv.Perm AxisChart :=
  { toFun := ![24, 10, 16, 4, 27, 13, 26, 8, 3, 15, 17, 18, 6, 12, 30,
      2, 22, 0, 21, 25, 23, 14, 9, 19, 1, 29, 5, 7, 28, 20, 11]
    invFun := ![17, 24, 15, 8, 3, 26, 12, 27, 7, 22, 1, 30, 13, 5, 21,
      9, 2, 10, 11, 23, 29, 18, 16, 20, 0, 19, 6, 4, 28, 25, 14]
    left_inv := by decide
    right_inv := by decide }

/-- The chart permutations agree pointwise with projectivizing the source matrices. -/
theorem source_matrix_actions :
    (∀ p, (normalize (matrixA.mulVec (axisVector p))).1 =
      axisVector (projectiveA p)) ∧
    (∀ p, (normalize (matrixB.mulVec (axisVector p))).1 =
      axisVector (projectiveB p)) := by
  decide

def icosahedralWords : List (List (Fin 4)) :=
  [[], [0], [1], [2], [3], [0, 2], [0, 3], [1, 2], [1, 3], [2, 0],
   [2, 1], [2, 2], [3, 0], [3, 1], [3, 3], [0, 2, 0], [0, 2, 1],
   [0, 2, 2], [0, 3, 0], [0, 3, 1], [0, 3, 3], [1, 2, 0], [1, 2, 1],
   [1, 2, 2], [1, 3, 0], [1, 3, 1], [1, 3, 3], [2, 0, 2], [2, 0, 3],
   [2, 1, 3], [2, 2, 1], [3, 0, 2], [3, 1, 2], [3, 3, 0],
   [0, 2, 0, 2], [0, 2, 0, 3], [0, 2, 1, 3], [0, 3, 0, 2],
   [0, 3, 1, 2], [0, 3, 3, 0], [1, 2, 0, 2], [1, 2, 0, 3],
   [1, 2, 1, 3], [1, 3, 0, 2], [1, 3, 1, 2], [2, 0, 2, 0],
   [2, 0, 2, 1], [2, 0, 3, 1], [2, 1, 3, 0], [3, 0, 2, 1],
   [3, 1, 2, 0], [0, 2, 0, 2, 0], [0, 2, 0, 2, 1],
   [0, 2, 1, 3, 0], [0, 3, 1, 2, 0], [1, 2, 0, 2, 0],
   [1, 2, 0, 2, 1], [2, 0, 3, 1, 2], [2, 1, 3, 0, 2],
   [0, 2, 1, 3, 0, 2]]

def evaluateLetter : Fin 4 → Equiv.Perm AxisChart :=
  ![projectiveA, projectiveA⁻¹, projectiveB, projectiveB⁻¹]

def evaluateWord (word : List (Fin 4)) : Equiv.Perm AxisChart :=
  word.foldl (fun g letter => g * evaluateLetter letter) 1

/-- The source identifies its order-60 matrix group with `A₅`. -/
abbrev IcosahedralGroup := alternatingGroup (Fin 5)

private def alternatingPermA : Equiv.Perm (Fin 5) :=
  { toFun := ![1, 2, 0, 3, 4]
    invFun := ![2, 0, 1, 3, 4]
    left_inv := by decide
    right_inv := by decide }

private def alternatingPermB : Equiv.Perm (Fin 5) :=
  { toFun := ![1, 2, 3, 4, 0]
    invFun := ![4, 0, 1, 2, 3]
    left_inv := by decide
    right_inv := by decide }

private def alternatingA : IcosahedralGroup :=
  ⟨alternatingPermA, by
    change Equiv.Perm.sign alternatingPermA = 1
    decide⟩

private def alternatingB : IcosahedralGroup :=
  ⟨alternatingPermB, by
    change Equiv.Perm.sign alternatingPermB = 1
    decide⟩

def evaluateAlternatingLetter : Fin 4 → IcosahedralGroup :=
  ![alternatingA, alternatingA⁻¹, alternatingB, alternatingB⁻¹]

def evaluateAlternatingWord (word : List (Fin 4)) : IcosahedralGroup :=
  word.foldl (fun g letter => g * evaluateAlternatingLetter letter) 1

def representativeWord (g : IcosahedralGroup) : List (Fin 4) :=
  (icosahedralWords.find? fun word => evaluateAlternatingWord word = g).getD []

def actionPermutation (g : IcosahedralGroup) : Equiv.Perm AxisChart :=
  evaluateWord (representativeWord g)

/-- The standard generators induce the two displayed chart permutations. -/
theorem source_generator_chart_actions :
    actionPermutation alternatingA = projectiveA ∧
      actionPermutation alternatingB = projectiveB := by
  decide

def evaluateMatrixLetter : Fin 4 → Matrix (Fin 3) (Fin 3) F5 :=
  ![matrixA, matrixAInv, matrixB, matrixBInv]

private def evaluateMatrixWord (word : List (Fin 4)) : Matrix (Fin 3) (Fin 3) F5 :=
  word.foldl (fun matrix letter => matrix * evaluateMatrixLetter letter) 1

def actionMatrix (g : IcosahedralGroup) : Matrix (Fin 3) (Fin 3) F5 :=
  evaluateMatrixWord (representativeWord g)

set_option maxRecDepth 100000 in
/-- The standard `A₅` generators act linearly by the two displayed source matrices. -/
theorem source_generator_actions :
    actionMatrix alternatingA = matrixA ∧ actionMatrix alternatingB = matrixB := by
  decide

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
