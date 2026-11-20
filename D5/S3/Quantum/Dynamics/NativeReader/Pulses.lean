/- GID: D5/S3/Quantum/Dynamics/NativeReader/Pulses
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Pulses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original fifteen pulses on the complete legal auxiliary fibers. -/

import D5.S3.Quantum.Dynamics.NativeReader.Carrier
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Literal full-pulse dynamics on each complete legal auxiliary fiber. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

open Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Measurement.OneSidedGoldenHistory (x x_properties)

def alpha : ℝ := 3 * Real.pi / 5

/-- All five addresses are the original physical centers ten through fourteen. -/
def projection (i : Bool) (j : Fin 5) : Matrix (Tail i) (Tail i) ℂ :=
  pathProjection adjacent weight Real.goldenRatio 6 i true (j.val + 1) ⟨by omega, by omega⟩

theorem projection_laws (i : Bool) (j : Fin 5) :
    (projection i j).conjTranspose = projection i j ∧
      projection i j * projection i j = projection i j :=
  (weighted_legal_path_temperley_lieb adjacent adjacent_symm weight weight_positive
    Real.goldenRatio Real.goldenRatio_pos weight_perron 6 i true).1 _ _

def unitPhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem unitPhase_star (t : ℝ) : star (unitPhase t) * unitPhase t = 1 := by
  have hn : ‖unitPhase t‖ = 1 := by simp [unitPhase, Complex.norm_exp]
  simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using
    (show (Complex.normSq (unitPhase t) : ℂ) = 1 by
      rw [Complex.normSq_eq_norm_sq, hn]
      norm_num)

/-- A full or internal part of one native forward pulse, with its global phase retained. -/
def pulse (i : Bool) (j : Fin 5) (t : ℝ) : Matrix (Tail i) (Tail i) ℂ :=
  unitPhase t • (1 + (unitPhase t - 1) • projection i j)

/-- Only addresses eleven and thirteen change, with one common comparison parameter. -/
def angle (lam : ℝ) (j : Fin 5) : ℝ := if j = 1 ∨ j = 3 then lam else alpha

/-- Physical order is the source's order; indices are the physical addresses minus ten. -/
def address : ℕ → Fin 5
  | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 1
  | 5 => 0 | 6 => 3 | 7 => 2 | 8 => 1 | 9 => 0
  | 10 => 4 | 11 => 3 | 12 => 2 | 13 => 1 | _ => 0

def readyVector (i : Bool) : Tail i → ℂ := Pi.single (readyTail i) 1

/-- Every previous letter is executed for its entire forward unit time. -/
def entrance (i : Bool) (lam : ℝ) : ℕ → (Tail i → ℂ)
  | 0 => readyVector i
  | k + 1 => pulse i (address k) (angle lam (address k)) *ᵥ entrance i lam k

/-- The internal time s describes a history inside the next actual full call. -/
def during (i : Bool) (lam : ℝ) (k : Fin 15) (s : ℝ) : Tail i → ℂ :=
  pulse i (address k) (angle lam (address k) * s) *ᵥ entrance i lam k

theorem pulse_zero (i : Bool) (j : Fin 5) : pulse i j 0 = 1 := by
  simp [pulse, unitPhase]

theorem during_right (i : Bool) (lam : ℝ) (k : Fin 15) :
    during i lam k 1 = entrance i lam (k.val + 1) := by
  simp [during, entrance]

theorem ready_report (i : Bool) : report (readyTail i) = false := by
  simp [report, readyTail]

/-- The unchanged physical addresses have singleton blocks at the candidate tail. -/
theorem unchanged_row (i : Bool) (j : Fin 5) (hj : j ≠ 1 ∧ j ≠ 3) (z : Tail i) :
    projection i j (readyTail i) z =
      (if j = 0 ∧ i = true then (1 : ℂ) else 0) *
        (if readyTail i = z then 1 else 0) := by
  have hs (z : Tail true)
      (h : ∀ k : Fin 7, k.val ≠ 1 → (readyTail true).1 k = z.1 k) :
      z = readyTail true := by
    have he := z.2.2.2 0
    have hz : z.1 1 = false := by
      cases hb : z.1 1
      · rfl
      · have h0 : z.1 0 = true := z.2.1
        simp [adjacent, h0, hb] at he
    apply Subtype.ext
    funext k
    by_cases hk : k.val = 1
    · have hk' : k = 1 := Fin.ext hk
      simp [hk', hz, readyTail]
    · exact (h k hk).symm
  have hjs : j = 0 ∨ j = 2 ∨ j = 4 := by
    fin_cases j <;> simp_all
  rcases hjs with rfl | rfl | rfl
  · cases i
    · simp [projection, pathProjection, readyTail]
    · by_cases hz : z = readyTail true
      · subst z
        have hm : Real.goldenRatio * x = 1 := mul_inv_cancel₀ Real.goldenRatio_ne_zero
        simp [projection, pathProjection, readyTail, weight, hm]

      · have ha : ¬ ∀ k : Fin 7, k.val ≠ 1 → (readyTail true).1 k = z.1 k :=
          fun h => hz (hs z h)
        change (if (∀ k : Fin 7, k.val ≠ 1 → (readyTail true).1 k = z.1 k) ∧ _
          then _ else _) = _
        rw [if_neg (fun h => ha h.1)]
        simp only [Fin.reduceEq, and_self, ite_true, one_mul]
        rw [if_neg (Ne.symm hz)]
  · cases i <;> simp [projection, pathProjection, readyTail]
  · cases i <;> simp [projection, pathProjection, readyTail]

/-- This row identity concerns arbitrary global vectors; other coordinates are retained. -/
theorem unchanged_current (i : Bool) (j : Fin 5) (hj : j ≠ 1 ∧ j ≠ 3)
    (t : ℝ) (v : Tail i → ℂ) :
    (pulse i j t *ᵥ v) (readyTail i) =
      (if j = 0 ∧ i = true then unitPhase t ^ 2 else unitPhase t) * v (readyTail i) := by
  simp only [pulse, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  have hr : (projection i j *ᵥ v) (readyTail i) =
      (if j = 0 ∧ i = true then (1 : ℂ) else 0) * v (readyTail i) := by
    simp only [Matrix.mulVec, dotProduct, unchanged_row i j hj]
    by_cases h : j = 0 ∧ i = true <;> simp [h]
  rw [hr]
  split_ifs <;> ring

/-- All unchanged calls act on the ready column by one nonzero phase. -/
theorem unchanged_column (i : Bool) (j : Fin 5) (hj : j ≠ 1 ∧ j ≠ 3) (t : ℝ) :
    ∃ c : ℂ, c ≠ 0 ∧ pulse i j t *ᵥ readyVector i = c • readyVector i := by
  have hcol : projection i j *ᵥ readyVector i =
      (if j = 0 ∧ i = true then (1 : ℂ) else 0) • readyVector i := by
    ext z
    simp only [readyVector, Matrix.mulVec_single_one, Matrix.col_apply]
    have h := congrFun (congrFun (projection_laws i j).1 z) (readyTail i)
    simp only [Matrix.conjTranspose_apply, unchanged_row i j hj] at h
    by_cases hj0 : j = 0 ∧ i = true <;> by_cases hz : readyTail i = z
    all_goals
      simp [hj0, hz, Ne.symm, Pi.smul_apply, Pi.single_apply] at h ⊢
      exact h.symm

  refine ⟨if j = 0 ∧ i = true then unitPhase t ^ 2 else unitPhase t, ?_, ?_⟩
  · split_ifs <;> simp [unitPhase, Complex.exp_ne_zero]
  · rw [pulse, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, hcol]
    split_ifs <;> module

/-- The mathematical reference parameter zero never executes an additional control. -/
theorem reference_entrance (i : Bool) (k : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ entrance i 0 k = c • readyVector i := by
  induction k with
  | zero => exact ⟨1, one_ne_zero, by simp [entrance]⟩
  | succ k ih =>
    obtain ⟨c, hc, he⟩ := ih
    by_cases hj : address k = 1 ∨ address k = 3
    · exact ⟨c, hc, by simp [entrance, angle, hj, pulse_zero, he]⟩
    · obtain ⟨b, hb, hbe⟩ := unchanged_column i (address k) (not_or.mp hj) alpha
      refine ⟨b * c, mul_ne_zero hb hc, ?_⟩
      simp only [entrance, angle, if_neg hj, he, Matrix.mulVec_smul, hbe, smul_smul]
      rw [mul_comm]

/-- Entry analyticity is proved from the literal finite pulse recursion. -/
theorem entrance_analytic (i : Bool) (k : ℕ) (z : Tail i) (t : ℝ) :
    AnalyticAt ℝ (fun lam : ℝ => entrance i lam k z) t := by
  have hphase : AnalyticAt ℝ unitPhase t := by
    have he : AnalyticAt ℝ Complex.exp ((t : ℂ) * Complex.I) :=
      AnalyticAt.restrictScalars (𝕜 := ℝ) analyticAt_cexp
    have ha : AnalyticAt ℝ (fun r : ℝ => (r : ℂ) * Complex.I) t :=
      (Complex.ofRealCLM.analyticAt t).mul analyticAt_const
    exact AnalyticAt.comp (f := fun r : ℝ => (r : ℂ) * Complex.I) (x := t) he ha

  have hp (j : Fin 5) (r z : Tail i) :
      AnalyticAt ℝ (fun lam : ℝ => pulse i j (angle lam j) r z) t := by
    by_cases hj : j = 1 ∨ j = 3
    · simpa [pulse, angle, hj, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] using
        (show AnalyticAt ℝ (fun lam => unitPhase lam *
          ((1 : Matrix (Tail i) (Tail i) ℂ) r z +
          (unitPhase lam - 1) * projection i j r z)) t from
          hphase.mul (analyticAt_const.add ((hphase.sub analyticAt_const).mul analyticAt_const)))
    · simp only [angle, if_neg hj]
      exact analyticAt_const
  induction k generalizing z with
  | zero => exact analyticAt_const
  | succ k ih =>
    simp only [entrance, Matrix.mulVec, dotProduct]
    convert (Finset.analyticAt_sum Finset.univ
      (fun r _ => (hp (address k) z r).mul (ih r))) using 1
    funext lam
    simp only [Finset.sum_apply, Pi.mul_apply]

end D5.S3.Quantum.Dynamics.NativeReader
