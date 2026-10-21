/- GID: D5/S3/Quantum/Information/SkewInformationLambdaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SkewInformationLambdaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim; result=D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result; claim=D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim
   digest: A regular symmetric operator monotone counterexample to the endpoint formula. -/

import D5.S3.Fourier.PositiveFourierApproximationRefutation
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-! A rational counterexample to the conjectured skew-information constant. -/

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.SkewInformationLambdaRefutation

/-- The scalar expression whose least value defines the skew-information constant. -/
def lambdaIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + x - f 0 * (1 - x) ^ 2 / (2 * f x)) / (2 * f x)

/-- Nonnegative, operator monotone, symmetric, normalized and regular functions. -/
def Admissible (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → 0 ≤ f x) ∧
    D5.S3.Fourier.PositiveFourierApproximationRefutation.OperatorMonotoneOn f ∧
    (∀ x, 0 < x → x * f (1 / x) = f x) ∧ f 1 = 1 ∧ 0 < f 0

/-- The conjectured endpoint formula for the least value. -/
def claim : Prop :=
  ∀ f : ℝ → ℝ, Admissible f →
    IsLeast (lambdaIntegrand f '' Set.Ici 0) (min 1 (1 / (4 * f 0)))

private def counterexampleFunction (x : ℝ) : ℝ :=
  (2 / 9) * (1 + x) + (10 / 3) * (x / (11 * x + 1)) +
    (10 / 3) * (x / (x + 11))

private theorem counterexample_cfc {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.PosSemidef) :
    cfc counterexampleFunction M = (2 / 9 : ℝ) • (1 + M) +
      (10 / 3 : ℝ) • cfc (fun x : ℝ => x / (11 * x + 1)) M +
      (10 / 3 : ℝ) • cfc (fun x : ℝ => x / (1 * x + 11)) M := by
  have hcont (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      ContinuousOn (fun x : ℝ => x / (a * x + b)) (spectrum ℝ M) := by
    refine continuousOn_id.div
      ((continuousOn_const.mul continuousOn_id).add continuousOn_const) ?_
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ha.le (spectrum_nonneg_of_nonneg hM.nonneg hx)) hb)
  have hc₁ := hcont 11 1 (by norm_num) (by norm_num)
  have hc₂ := hcont 1 11 (by norm_num) (by norm_num)
  unfold counterexampleFunction
  conv_lhs => arg 1; ext x; rw [show x + 11 = 1 * x + 11 by ring]
  rw [cfc_add M
      (fun x : ℝ => (2 / 9) * (1 + x) + (10 / 3) * (x / (11 * x + 1)))
      (fun x : ℝ => (10 / 3) * (x / (1 * x + 11)))
      (((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).add
        (continuousOn_const.mul hc₁))) (continuousOn_const.mul hc₂),
    cfc_add M (fun x : ℝ => (2 / 9) * (1 + x))
      (fun x : ℝ => (10 / 3) * (x / (11 * x + 1)))
      (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
      (continuousOn_const.mul hc₁),
    cfc_const_mul (2 / 9 : ℝ) (fun x : ℝ => 1 + x) M
      (continuousOn_const.add continuousOn_id),
    cfc_const_mul (10 / 3 : ℝ) (fun x : ℝ => x / (11 * x + 1)) M hc₁,
    cfc_const_mul (10 / 3 : ℝ) (fun x : ℝ => x / (1 * x + 11)) M hc₂,
    cfc_const_add (p := IsSelfAdjoint) 1 (fun x : ℝ => x) M continuousOn_id
      hM.isHermitian.isSelfAdjoint,
    cfc_id' (p := IsSelfAdjoint) ℝ M hM.isHermitian.isSelfAdjoint, map_one]

private theorem counterexample_monotone :
    D5.S3.Fourier.PositiveFourierApproximationRefutation.OperatorMonotoneOn
      counterexampleFunction := by
  intro n A B hA hB hAB
  cases n with
  | zero => exact le_of_eq (Subsingleton.elim _ _)
  | succ n =>
      have hq : ContinuousOn (fun x : ℝ => 1 - (1 + x)⁻¹) (Set.Ici 0) := by
        refine continuousOn_const.sub ((continuousOn_const.add continuousOn_id).inv₀ ?_)
        intro x hx
        change 1 + x ≠ 0
        exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hx)
      have hmono (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
          cfc (fun x : ℝ => x / (a * x + b)) A ≤
            cfc (fun x : ℝ => x / (a * x + b)) B := by
        have hc : 0 ≤ a / b := (div_pos ha hb).le
        have hscale (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
            (hM : M.PosSemidef) :
            cfc (fun x : ℝ => x / (a * x + b)) M =
              (1 / a) • cfc (fun x : ℝ => 1 - (1 + x)⁻¹) ((a / b) • M) := by
          have hspec : (fun x : ℝ => a / b * x) '' spectrum ℝ M ⊆ Set.Ici 0 := by
            rintro _ ⟨x, hx, rfl⟩
            exact mul_nonneg hc (spectrum_nonneg_of_nonneg hM.nonneg hx)
          have hcomp : ContinuousOn (fun x : ℝ => 1 - (1 + a / b * x)⁻¹)
              (spectrum ℝ M) :=
            hq.comp (continuousOn_const.mul continuousOn_id)
              (fun x hx => hspec ⟨x, hx, rfl⟩)
          calc
            _ = cfc (fun x : ℝ => (1 / a) * (1 - (1 + a / b * x)⁻¹)) M := by
              apply cfc_congr
              intro x hx
              have hx0 := spectrum_nonneg_of_nonneg hM.nonneg hx
              have hd : a * x + b ≠ 0 := by positivity
              have hd' : 1 + a / b * x ≠ 0 := by positivity
              field_simp [ha.ne', hb.ne', hd, hd']
              <;> ring
            _ = _ := by
              rw [cfc_const_mul (1 / a) _ M
                  hcomp,
                cfc_comp_const_mul (a / b) _ M (hq.mono hspec)
                  hM.isHermitian.isSelfAdjoint]
        rw [hscale A hA, hscale B hB]
        apply smul_le_smul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 1 / a)
        have hAs := (hA.smul hc).nonneg
        have hBs := (hB.smul hc).nonneg
        have h := CFC.monotoneOn_one_sub_one_add_inv_real hAs hBs
          (smul_le_smul_of_nonneg_left hAB hc)
        rw [cfcₙ_eq_cfc (hq.mono (fun x hx =>
            quasispectrum_nonneg_of_nonneg _ hAs x hx)) (by simp),
          cfcₙ_eq_cfc (hq.mono (fun x hx =>
            quasispectrum_nonneg_of_nonneg _ hBs x hx)) (by simp)] at h
        exact h
      rw [counterexample_cfc A hA, counterexample_cfc B hB]
      exact add_le_add
        (add_le_add
          (smul_le_smul_of_nonneg_left (add_le_add le_rfl hAB) (by norm_num))
          (smul_le_smul_of_nonneg_left (hmono 11 1 (by norm_num) (by norm_num))
            (by norm_num)))
        (smul_le_smul_of_nonneg_left (hmono 1 11 (by norm_num) (by norm_num))
          (by norm_num))

private theorem counterexample_admissible : Admissible counterexampleFunction := by
  refine ⟨?_, counterexample_monotone, ?_, ?_, ?_⟩
  · intro x hx
    unfold counterexampleFunction
    positivity
  · intro x hx
    unfold counterexampleFunction
    have h₁ : 11 * x + 1 ≠ 0 := by positivity
    have h₂ : x + 11 ≠ 0 := by positivity
    have h₃ : 11 * (1 / x) + 1 ≠ 0 := by positivity
    have h₄ : 1 / x + 11 ≠ 0 := by positivity
    field_simp [hx.ne', h₁, h₂, h₃, h₄]
    ring
  · norm_num [counterexampleFunction]
  · norm_num [counterexampleFunction]

private theorem counterexample_value :
    lambdaIntegrand counterexampleFunction (1 / 4) = 7641 / 7688 := by
  norm_num [lambdaIntegrand, counterexampleFunction]

theorem result : ¬ claim := by
  intro h
  have hleast := h counterexampleFunction counterexample_admissible
  have hbound := hleast.2 (show lambdaIntegrand counterexampleFunction (1 / 4) ∈
      lambdaIntegrand counterexampleFunction '' Set.Ici 0 from
    ⟨1 / 4, by norm_num, rfl⟩)
  rw [counterexample_value] at hbound
  norm_num [counterexampleFunction] at hbound

end D5.S3.Quantum.Information.SkewInformationLambdaRefutation
