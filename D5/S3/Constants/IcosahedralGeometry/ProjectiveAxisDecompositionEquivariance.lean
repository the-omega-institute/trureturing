/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionEquivariance
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionEquivariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The projective coordinate equivalence intertwines the explicit A5 action. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionChart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

private theorem source_letter_actions (letter : Fin 4) :
    actionMatrix (evaluateAlternatingLetter letter) = evaluateMatrixLetter letter := by
  fin_cases letter <;> decide

set_option maxRecDepth 100000 in
private theorem source_matrix_letter_actions :
    ∀ letter : Fin 4, ∀ p : AxisChart,
      (normalize ((evaluateMatrixLetter letter).mulVec (axisVector p))).1 =
        axisVector (evaluateLetter letter p) := by
  intro letter p
  fin_cases letter <;> fin_cases p <;> decide

private theorem alternatingLetter_chartPoint (letter : Fin 4) (p : AxisChart) :
    evaluateAlternatingLetter letter • chartPoint p =
      chartPoint (evaluateLetter letter p) := by
  rw [chartPoint, Projectivization.smul_mk]
  change Projectivization.mk F5
      ((actionMatrix (evaluateAlternatingLetter letter)).mulVec (axisVector p)) _ =
    Projectivization.mk F5 (axisVector (evaluateLetter letter p)) _
  symm
  apply (Projectivization.mk_eq_mk_iff' F5 _ _ _ _).mpr
  obtain ⟨a, ha⟩ := normalize_scalar
    ((actionMatrix (evaluateAlternatingLetter letter)).mulVec (axisVector p))
    ((smul_ne_zero_iff_ne (evaluateAlternatingLetter letter)).mpr (axisVector_ne_zero p))
  refine ⟨a, ha.trans ?_⟩
  rw [source_letter_actions, source_matrix_letter_actions]

private theorem foldl_chartPoint :
    ∀ word : List (Fin 4), ∀ g : IcosahedralGroup, ∀ e : Equiv.Perm AxisChart,
      (∀ p, g • chartPoint p = chartPoint (e p)) →
        ∀ p,
          (word.foldl (fun h letter => h * evaluateAlternatingLetter letter) g) •
              chartPoint p =
            chartPoint
              ((word.foldl (fun f letter => f * evaluateLetter letter) e) p) := by
  intro word
  induction word with
  | nil =>
      intro g e h p
      exact h p
  | cons letter word ih =>
      intro g e h p
      apply ih (g * evaluateAlternatingLetter letter)
        (e * evaluateLetter letter)
      intro q
      rw [mul_smul, alternatingLetter_chartPoint, h]
      rfl

private theorem evaluateAlternatingWord_chartPoint
    (word : List (Fin 4)) (p : AxisChart) :
    evaluateAlternatingWord word • chartPoint p = chartPoint (evaluateWord word p) := by
  apply foldl_chartPoint word 1 1
  intro q
  simp

set_option maxHeartbeats 4000000 in
-- The finite certificate normalizes all 60 explicit representatives of `A₅`.
set_option maxRecDepth 100000 in
private theorem representativeWord_complete (g : IcosahedralGroup) :
    evaluateAlternatingWord (representativeWord g) = g := by
  fin_cases g <;> decide

private theorem chartPoint_smul (g : IcosahedralGroup) (p : AxisChart) :
    g • chartPoint p = chartPoint (g • p) := by
  calc
    g • chartPoint p =
        evaluateAlternatingWord (representativeWord g) • chartPoint p := by
      rw [representativeWord_complete]
    _ = chartPoint (evaluateWord (representativeWord g) p) :=
      evaluateAlternatingWord_chartPoint (representativeWord g) p
    _ = chartPoint (g • p) := rfl

/-- The coordinate equivalence intertwines the finite chart action with
Mathlib's induced projective action. -/
theorem projectiveChart_smul (g : IcosahedralGroup) (p : ProjectiveAxis) :
    projectiveChart (g • p) = g • projectiveChart p := by
  have hp : chartPoint (projectiveChart p) = p := by
    simpa only [projectiveChart_symm_apply] using projectiveChart.symm_apply_apply p
  calc
    projectiveChart (g • p) =
        projectiveChart (g • chartPoint (projectiveChart p)) := by rw [hp]
    _ = projectiveChart (chartPoint (g • projectiveChart p)) := by
      rw [chartPoint_smul]
    _ = g • projectiveChart p := projectiveChart_chartPoint _

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
