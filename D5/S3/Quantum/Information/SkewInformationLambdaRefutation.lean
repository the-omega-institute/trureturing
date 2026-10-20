/- GID: D5/S3/Quantum/Information/SkewInformationLambdaRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SkewInformationLambdaRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim; result=D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result; claim=D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim
   digest: A regular symmetric operator monotone counterexample to the endpoint formula. -/

import D5.S3.Quantum.Lieb.LownerHeinzCore
import D5.S3.Quantum.Matrix.CayleyResolvent

/-! A rational counterexample to the conjectured skew-information constant. -/

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.SkewInformationLambdaRefutation

/-- The scalar expression whose least value defines the skew-information constant. -/
def lambdaIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 + x - f 0 * (1 - x) ^ 2 / (2 * f x)) / (2 * f x)

/-- Operator monotonicity on the positive semidefinite cone in every finite size. -/
def MatrixOperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → (B - A).PosSemidef →
    (cfc f B - cfc f A).PosSemidef

/-- Nonnegative, operator monotone, symmetric, normalized and regular functions. -/
def Admissible (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → 0 ≤ f x) ∧ MatrixOperatorMonotone f ∧
    (∀ x, 0 < x → x * f (1 / x) = f x) ∧ f 1 = 1 ∧ 0 < f 0

/-- The conjectured endpoint formula for the least value. -/
def claim : Prop :=
  ∀ f : ℝ → ℝ, Admissible f →
    IsLeast (lambdaIntegrand f '' Set.Ici 0) (min 1 (1 / (4 * f 0)))

private def counterexampleFunction (x : ℝ) : ℝ :=
  (2 / 9) * (1 + x) + (10 / 3) * (x / (11 * x + 1)) +
    (10 / 3) * (x / (x + 11))

private theorem rational_cfc {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.PosSemidef) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    cfc (fun x : ℝ => x / (a * x + b)) M =
      (1 / a) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        (b / a) • (a • M + b • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ := by
  have hne : ∀ x ∈ spectrum ℝ M, a * x + b ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ha.le (spectrum_nonneg_of_nonneg hM.nonneg hx)) hb)
  have hden : ContinuousOn (fun x : ℝ => a * x + b) (spectrum ℝ M) :=
    (continuousOn_const.mul continuousOn_id).add continuousOn_const
  have hinv := hden.inv₀ hne
  have heq : (spectrum ℝ M).EqOn (fun x : ℝ => x / (a * x + b))
      (fun x : ℝ => 1 / a - (b / a) * (a * x + b)⁻¹) := by
    intro x hx
    change x / (a * x + b) = 1 / a - (b / a) * (a * x + b)⁻¹
    apply (div_eq_iff (hne x hx)).2
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ (hne x hx), mul_one]
    field_simp [ha.ne']
    ring
  rw [cfc_congr heq,
    cfc_sub (fun _ : ℝ => 1 / a)
      (fun x : ℝ => (b / a) * (a * x + b)⁻¹) M
      continuousOn_const (continuousOn_const.mul hinv),
    cfc_const (p := IsSelfAdjoint) (1 / a) M hM.isHermitian.isSelfAdjoint,
    cfc_const_mul (p := IsSelfAdjoint) (b / a)
      (fun x : ℝ => (a * x + b)⁻¹) M hinv,
    cfc_inv (p := IsSelfAdjoint) (fun x : ℝ => a * x + b) M hne hden
      hM.isHermitian.isSelfAdjoint,
    cfc_add_const (p := IsSelfAdjoint) b (fun x : ℝ => a * x) M
      (continuousOn_const.mul continuousOn_id) hM.isHermitian.isSelfAdjoint,
    cfc_const_mul_id (p := IsSelfAdjoint) a M hM.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    ← Matrix.nonsing_inv_eq_ringInverse]

private theorem rational_monotone (n : ℕ) [Nonempty (Fin n)] (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    LownerHeinzCore.OperatorMonotoneOn (𝓐 := Matrix (Fin n) (Fin n) ℂ)
      (Set.Ici 0) (fun x : ℝ => x / (a * x + b)) := by
  intro A B hA hB hBA _ _
  change cfc (fun x : ℝ => x / (a * x + b)) B ≤
    cfc (fun x : ℝ => x / (a * x + b)) A
  have hAp := Matrix.nonneg_iff_posSemidef.mp hA
  have hBp := Matrix.nonneg_iff_posSemidef.mp hB
  rw [rational_cfc B hBp a b ha hb, rational_cfc A hAp a b ha hb]
  have hP := Matrix.PosDef.posSemidef_add (hBp.smul ha.le) (Matrix.PosDef.one.smul hb)
  have hQ := Matrix.PosDef.posSemidef_add (hAp.smul ha.le) (Matrix.PosDef.one.smul hb)
  have hi := D5.S3.Quantum.Matrix.CayleyResolvent.inverse_antitone hP hQ
    (add_le_add (smul_le_smul_of_nonneg_left hBA ha.le) le_rfl)
  exact sub_le_sub_left (smul_le_smul_of_nonneg_left hi (div_nonneg hb.le ha.le)) _

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

private theorem counterexample_monotone : MatrixOperatorMonotone counterexampleFunction := by
  intro n A B hA hBA
  have hAB : A ≤ B := hBA
  have hB := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans hAB)
  cases n with
  | zero =>
      have hz : cfc counterexampleFunction B - cfc counterexampleFunction A = 0 :=
        Subsingleton.elim _ _
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n =>
      have hsA : spectrum ℝ A ⊆ Set.Ici 0 :=
        fun _ hx => spectrum_nonneg_of_nonneg hA.nonneg hx
      have hsB : spectrum ℝ B ⊆ Set.Ici 0 :=
        fun _ hx => spectrum_nonneg_of_nonneg hB.nonneg hx
      have h₁ := rational_monotone (n + 1) 11 1 (by norm_num) (by norm_num)
        hB.nonneg hA.nonneg hAB hsB hsA
      have h₂ := rational_monotone (n + 1) 1 11 (by norm_num) (by norm_num)
        hB.nonneg hA.nonneg hAB hsB hsA
      apply Matrix.le_iff.mp
      rw [counterexample_cfc A hA, counterexample_cfc B hB]
      exact add_le_add
        (add_le_add
          (smul_le_smul_of_nonneg_left (add_le_add le_rfl hAB) (by norm_num))
          (smul_le_smul_of_nonneg_left h₁ (by norm_num)))
        (smul_le_smul_of_nonneg_left h₂ (by norm_num))

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
