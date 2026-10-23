/- GID: D5/S3/Quantum/Lieb/LiebConcavity
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/LiebConcavity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attributed Lieb joint trace concavity for positive-definite inputs and interior exponents. -/

/-
Attributed Physlib source transplant, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Source: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean
Copyright and Apache-2.0 header follow; full license retained at
`docs/reports/inoutbalance/physlib-LICENSE.txt`; supplier root has no NOTICE.
Retire this transplant when the repository-pinned Mathlib provides an equivalent
consumed declaration, replacing this proof with its direct application.
This is upstream reuse; no mathematical originality is claimed.
-/

/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import D5.S3.Quantum.Lieb.LiebBridge

@[expose] public section

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance : NonnegSpectrumClass ℝ ((L ℋ)ᵐᵒᵖ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance :
    IsometricContinuousFunctionalCalculus ℂ ((L ℋ)ᵐᵒᵖ) IsStarNormal := inferInstance

omit [FiniteDimensional ℂ ℋ] in
/-- Convex combinations preserve `pdSet` (strict positivity). -/
lemma pdSet_convexCombo {A B : L ℋ} {t : ℝ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA_sa |>.add ((IsSelfAdjoint.all t).smul hB_sa)
  have hApos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 ?_
    intro x hx
    exact hA_spec hx
  have hBpos : ∃ r > 0, algebraMap ℝ (L ℋ) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB_sa)).2 ?_
    intro x hx
    exact hB_spec hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by linarith
      subst ht'
      simpa [rC] using hrB
    · have h1t_pos : 0 < 1 - t := lt_of_le_of_ne (sub_nonneg.mpr ht1) (Ne.symm h1t)
      simpa [rC] using
        add_pos_of_pos_of_nonneg (mul_pos h1t_pos hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hsum :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB ≤ C := by
      simpa [C] using
        add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
          (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  refine ⟨hC, ?_⟩
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

private lemma phiK_weightedSum_operatorPowerMean_eq
    {s θ : ℝ} (K A₁ A₂ B₁ B₂ : L ℋ)
    (hA₁ : A₁ ∈ pdSet (ℋ := ℋ)) (hA₂ : A₂ ∈ pdSet (ℋ := ℋ))
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) • liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ • liebTraceMap (ℋ := ℋ) s K A₂ B₂ := by
  rw [phiK_add, phiK_smul, phiK_smul]
  simpa [smul_eq_mul] using
    show (1 - θ) * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁)) +
      θ * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) * liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ * liebTraceMap (ℋ := ℋ) s K A₂ B₂ by
      simp only [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₂ B₂ hA₂ hB₂]

-- The `HSOp`-valued `operatorPowerMean` terms are large enough that the skeleton itself is expensive.
theorem liebTrace_jointlyConcaveOn_pdSet
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconc_hs :=
    operatorPowerMean_jointlyConcaveOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconc :
      (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
        θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) ≤
        operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) := by
    simpa [hleft_combo, hright_combo] using hconc_hs
  have hphi_mono :
      phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) ≤
        phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) := by
    exact phiK_mono (ℋ := ℋ) K hconc
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono


#print axioms liebTrace_jointlyConcaveOn_pdSet

theorem liebTrace_jointlyConvexOn_pdSet
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo :
      ((1 - θ) • A₁ + θ • A₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo :
      ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) := by
    exact pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconv_hs :=
    operatorPowerMean_jointlyConvexOn_pdSet
      (ℋ := HSOp ℋ) (α := s) (β := 1)
      ⟨hs1, hs2⟩ ⟨by norm_num, by norm_num⟩
      (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
      (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂)
      (θ := θ)
      (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
      (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂)
      hθ0 hθ1
  have hconv :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) ≤
        (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) := by
    simpa [hleft_combo, hright_combo] using hconv_hs
  have hphi_mono :
      phiK (ℋ := ℋ) K
          (operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
            (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂))) ≤
        phiK (ℋ := ℋ) K
          ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
            θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
              (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) := by
    exact phiK_mono (ℋ := ℋ) K hconv
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

end LiebAndoTrace
