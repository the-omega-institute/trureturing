/- GID: D5/S3/Analytic/SeriesInequalities/GoldenShellMomentDiscretization
   generality: I
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/GoldenShellMomentDiscretization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden geometric shells recover positive defect moments within a fixed factor. -/

/- Library-search audit trail (2026-09-01):
   * Repository searches for golden shell moments, defect-moment discretization,
     weighted sandwiches, and multiplicative-error bounds found no equivalent
     declaration. `BodeWidthCriterion` identifies its finite area with a squared
     defect sum, but does not discretize that sum into golden shells.
   * The atom's two same-section chain neighbors remain residual-open and have no
     formalization receipts. The unrelated `GoldenShellRecurrence` concerns the
     Hofstadter G sequence rather than geometric defect shells.
   * Pinned Mathlib provides `Real.rpow_le_rpow`, `Real.rpow_lt_rpow`,
     `Real.mul_rpow`, `Real.rpow_mul`, `Finset.sum_le_sum`,
     `Real.goldenRatio_pos`, and `Real.one_lt_goldenRatio`. These are reused below;
     no exact golden-shell moment theorem was found.
   * No admissible third-party package with this theorem's finite weighted
     interface was found. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Analytic.SeriesInequalities.GoldenShellMomentDiscretization

noncomputable section

/-- The contraction ratio between consecutive golden defect shells. -/
def goldenShellRatio : Real := Real.goldenRatio ^ (-2 : Real)

/-- The upper radius of shell `n`, namely `(1 / 2) * phi ^ (-2n)`. -/
def goldenShellRadius (n : Nat) : Real :=
  (1 / 2 : Real) * goldenShellRatio ^ n

/-- The finite golden-shell transcript evaluated at moment exponent `s`. -/
def goldenShellTranscript {ι : Type*} [Fintype ι]
    (weight : ι -> Real) (shell : ι -> Nat) (s : Real) : Real :=
  Finset.univ.sum fun i => weight i * goldenShellRadius (shell i) ^ s

/-- The finite weighted transverse-defect moment evaluated at exponent `s`. -/
def transverseDefectMoment {ι : Type*} [Fintype ι]
    (weight defect : ι -> Real) (s : Real) : Real :=
  Finset.univ.sum fun i => weight i * defect i ^ s

private theorem goldenShellRatio_pos : 0 < goldenShellRatio := by
  exact Real.rpow_pos_of_pos Real.goldenRatio_pos _

private theorem goldenShellRadius_pos (n : Nat) : 0 < goldenShellRadius n := by
  exact mul_pos (by norm_num) (pow_pos goldenShellRatio_pos n)

private theorem goldenShellRadius_succ (n : Nat) :
    goldenShellRadius (n + 1) = goldenShellRatio * goldenShellRadius n := by
  simp only [goldenShellRadius, pow_succ]
  ring

private theorem goldenShellRatio_rpow (s : Real) :
    goldenShellRatio ^ s = Real.goldenRatio ^ (-2 * s) := by
  rw [goldenShellRatio, <- Real.rpow_mul Real.goldenRatio_pos.le]

/-- Assign each positive defect to a golden shell. For every positive real moment,
the shell transcript bounds the exact weighted defect moment, with lower factor
`phi ^ (-2s)`. Finite indexing is the finite-support form of the source sums. -/
theorem golden_shell_moment_sandwich {ι : Type*} [Fintype ι]
    (weight defect : ι -> Real) (shell : ι -> Nat) (s : Real)
    (hs : 0 < s) (hweight : forall i, 0 <= weight i)
    (hshell : forall i,
      goldenShellRadius (shell i + 1) < defect i /\
        defect i <= goldenShellRadius (shell i)) :
    Real.goldenRatio ^ (-2 * s) * goldenShellTranscript weight shell s <=
        transverseDefectMoment weight defect s /\
      transverseDefectMoment weight defect s <= goldenShellTranscript weight shell s := by
  have hlower :
      goldenShellRatio ^ s * goldenShellTranscript weight shell s <=
        transverseDefectMoment weight defect s := by
    rw [goldenShellTranscript, transverseDefectMoment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hradiusNonneg : 0 <= goldenShellRadius (shell i) :=
      (goldenShellRadius_pos (shell i)).le
    have hnextNonneg : 0 <= goldenShellRadius (shell i + 1) :=
      (goldenShellRadius_pos (shell i + 1)).le
    have hpower : goldenShellRadius (shell i + 1) ^ s <= defect i ^ s :=
      Real.rpow_le_rpow hnextNonneg (hshell i).1.le hs.le
    have hscaled :
        weight i * goldenShellRadius (shell i + 1) ^ s <=
          weight i * defect i ^ s :=
      mul_le_mul_of_nonneg_left hpower (hweight i)
    rw [goldenShellRadius_succ,
      Real.mul_rpow goldenShellRatio_pos.le hradiusNonneg] at hscaled
    nlinarith
  have hupper :
      transverseDefectMoment weight defect s <= goldenShellTranscript weight shell s := by
    rw [goldenShellTranscript, transverseDefectMoment]
    apply Finset.sum_le_sum
    intro i hi
    have hradiusNonneg : 0 <= goldenShellRadius (shell i) :=
      (goldenShellRadius_pos (shell i)).le
    have hpower : defect i ^ s <= goldenShellRadius (shell i) ^ s :=
      Real.rpow_le_rpow
        (le_trans (goldenShellRadius_pos (shell i + 1)).le (hshell i).1.le)
        (hshell i).2 hs.le
    exact mul_le_mul_of_nonneg_left hpower (hweight i)
  rw [goldenShellRatio_rpow] at hlower
  exact ⟨hlower, hupper⟩

/-- At exponent two, the multiplicative lower factor is exactly `phi ^ (-4)`. -/
theorem golden_shell_second_moment_sandwich {ι : Type*} [Fintype ι]
    (weight defect : ι -> Real) (shell : ι -> Nat)
    (hweight : forall i, 0 <= weight i)
    (hshell : forall i,
      goldenShellRadius (shell i + 1) < defect i /\
        defect i <= goldenShellRadius (shell i)) :
    Real.goldenRatio ^ (-4 : Real) * goldenShellTranscript weight shell 2 <=
        transverseDefectMoment weight defect 2 /\
      transverseDefectMoment weight defect 2 <= goldenShellTranscript weight shell 2 := by
  rw [show (-4 : Real) = (-2 : Real) * 2 by norm_num]
  exact golden_shell_moment_sandwich weight defect shell 2 (by norm_num) hweight hshell

/-- A nonempty numerical witness: one unit-weight defect at the upper edge of shell zero
has transcript and exact second moment both equal to `1 / 4`. -/
theorem valid_singleton_shell_witness :
    let weight : Fin 1 -> Real := fun _ => 1
    let defect : Fin 1 -> Real := fun _ => 1 / 2
    let shell : Fin 1 -> Nat := fun _ => 0
    (forall i,
      goldenShellRadius (shell i + 1) < defect i /\
        defect i <= goldenShellRadius (shell i)) /\
      goldenShellTranscript weight shell 2 = 1 / 4 /\
      transverseDefectMoment weight defect 2 = 1 / 4 /\
      (Real.goldenRatio ^ (-4 : Real) * goldenShellTranscript weight shell 2 <=
          transverseDefectMoment weight defect 2 /\
        transverseDefectMoment weight defect 2 <=
          goldenShellTranscript weight shell 2) := by
  dsimp only
  have hratioLtOne : goldenShellRatio < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg Real.one_lt_goldenRatio (by norm_num)
  have hshell : forall i : Fin 1,
      goldenShellRadius ((fun _ : Fin 1 => 0) i + 1) < (fun _ : Fin 1 => 1 / 2) i /\
        (fun _ : Fin 1 => 1 / 2) i <= goldenShellRadius ((fun _ : Fin 1 => 0) i) := by
    intro i
    constructor
    · simp only [goldenShellRadius]
      nlinarith [goldenShellRatio_pos]
    · simp [goldenShellRadius]
  refine ⟨hshell, ?_, ?_, ?_⟩
  · norm_num [goldenShellTranscript, goldenShellRadius, Real.rpow_two]
  · norm_num [transverseDefectMoment, Real.rpow_two]
  · exact golden_shell_second_moment_sandwich _ _ _ (by simp) hshell

/-- A numerical counter-witness after removing the shell premise: moving the same defect
to one makes the exact second moment `1`, while the declared shell transcript remains `1 / 4`. -/
theorem invalid_singleton_shell_witness :
    let weight : Fin 1 -> Real := fun _ => 1
    let defect : Fin 1 -> Real := fun _ => 1
    let shell : Fin 1 -> Nat := fun _ => 0
    goldenShellTranscript weight shell 2 = 1 / 4 /\
      transverseDefectMoment weight defect 2 = 1 /\
      (¬ (forall i,
        goldenShellRadius (shell i + 1) < defect i /\
          defect i <= goldenShellRadius (shell i))) /\
      ¬ (Real.goldenRatio ^ (-4 : Real) * goldenShellTranscript weight shell 2 <=
          transverseDefectMoment weight defect 2 /\
        transverseDefectMoment weight defect 2 <=
          goldenShellTranscript weight shell 2) := by
  dsimp only
  refine ⟨by norm_num [goldenShellTranscript, goldenShellRadius, Real.rpow_two],
    by norm_num [transverseDefectMoment, Real.rpow_two], ?_, ?_⟩
  · intro hshell
    have hupper := (hshell (0 : Fin 1)).2
    norm_num [goldenShellRadius] at hupper
  · intro hsandwich
    have hupper := hsandwich.2
    norm_num [goldenShellTranscript, transverseDefectMoment, goldenShellRadius,
      Real.rpow_two] at hupper

#print axioms golden_shell_moment_sandwich
#print axioms golden_shell_second_moment_sandwich
#print axioms valid_singleton_shell_witness
#print axioms invalid_singleton_shell_witness

end

end D5.S3.Analytic.SeriesInequalities.GoldenShellMomentDiscretization
