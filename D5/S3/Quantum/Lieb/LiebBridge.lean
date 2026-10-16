/- GID: D5/S3/Quantum/Lieb/LiebBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/LiebBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Hilbert-Schmidt perspective-to-Lieb trace bridge. -/

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

public import D5.S3.Quantum.Lieb.OperatorGeometricMean
public import D5.S3.Quantum.Lieb.HilbertSchmidtOperatorSpace
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

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

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance instCFCRealSelfAdjointMop :
    ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint := inferInstance

/-- The real part of the finite-dimensional trace on bounded operators. -/
noncomputable def traceRe (T : L ℋ) : ℝ :=
  Complex.re (LinearMap.trace ℂ ℋ T.toLinearMap)

/-- Trace functional appearing in Lieb's concavity theorem. -/
noncomputable def liebTraceMap (s : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K)

omit [Nontrivial ℋ] [CompleteSpace ℋ] in
private lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp (toOp T * ((algebraMap ℝ (L ℋ)) r)) =
    r • ofOp (toOp T * (1 : L ℋ))
  calc
    ofOp (toOp T * ((algebraMap ℝ (L ℋ)) r))
        = ofOp (((algebraMap ℝ (L ℋ)) r * toOp T) * (1 : L ℋ)) := by
            have hcomm := Algebra.commutes (R := ℝ) (A := L ℋ) r (toOp T)
            exact congrArg (fun X => X * (1 : L ℋ)) hcomm.symm
    _ = r • ofOp (toOp T) := by
          delta HSOp
          rfl
    _ = r • ofOp (toOp T * (1 : L ℋ)) := by simp

omit [Nontrivial ℋ] in
private lemma rightMulHS_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    0 ≤ rightMulHS (ℋ := ℋ) A := by
  let sqrtA : L ℋ := A ^ ((1 : ℝ) / 2)
  have hsqrt_sq_pow : sqrtA ^ (2 : ℕ) = A := by
    calc
      sqrtA ^ (2 : ℕ) = sqrtA ^ (2 : ℝ) := by
            simpa using (CFC.rpow_natCast sqrtA 2).symm
      _ = A ^ (((1 : ℝ) / 2) * 2) := by
            simpa [sqrtA] using
              (CFC.rpow_rpow_of_exponent_nonneg A ((1 : ℝ) / 2) 2
                (by positivity) (by positivity) (ha := hA0))
      _ = A ^ (1 : ℝ) := by ring_nf
      _ = A := by simpa using CFC.rpow_one A
  have hsqrt_sq : sqrtA * sqrtA = A := by
    simpa [pow_two] using hsqrt_sq_pow
  have hsqrt_sa : IsSelfAdjoint sqrtA := IsSelfAdjoint.of_nonneg (by
    simp [sqrtA])
  let S : L (HSOp ℋ) := rightMulHS (ℋ := ℋ) sqrtA
  have hSstar : star S = S := by
    change star (rightMulHS (ℋ := ℋ) sqrtA) = rightMulHS (ℋ := ℋ) sqrtA
    simp [hsqrt_sa.star_eq]
  have hSq : rightMulHS (ℋ := ℋ) A = star S * S := by
    calc
      rightMulHS (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (sqrtA * sqrtA) := by simp [hsqrt_sq]
      _ = S * S := by simp [S]
      _ = star S * S := by simp [hSstar]
  simp [hSq]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma rightMulHS_le_rightMulHS {A B : L ℋ} (hAB : A ≤ B) :
    rightMulHS (ℋ := ℋ) A ≤ rightMulHS (ℋ := ℋ) B := by
  have hnonneg : 0 ≤ rightMulHS (ℋ := ℋ) (B - A) :=
    rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB)
  have hsub :
      rightMulHS (ℋ := ℋ) B - rightMulHS (ℋ := ℋ) A =
        rightMulHS (ℋ := ℋ) (B - A) := by
    ext T
    have h1 := (mul_add (toOp T) B (-A)).symm
    simp_all only [sub_eq_add_neg, mul_neg, add_apply, rightMulHS_apply, neg_apply]
    exact h1
  exact sub_nonneg.mp (by simpa [hsub] using hnonneg)

lemma rightMulHS_pdSet {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    rightMulHS (ℋ := ℋ) A ∈ pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) A) := by
    change star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq]
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  refine ⟨hright_sa, ?_⟩
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec
    with ⟨r, hr, hrA⟩
  refine (CFC.exists_pos_algebraMap_le_iff
    (A := L (HSOp ℋ)) (a := rightMulHS (ℋ := ℋ) A) (ha := hright_sa)).1 ?_
  refine ⟨r, hr, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, rightMulHS_real_smul_one (ℋ := ℋ) (r := r)] using
    rightMulHS_le_rightMulHS (ℋ := ℋ) hrA

noncomputable def phiK (K : L ℋ) (T : L (HSOp ℋ)) : ℝ :=
  Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))

omit [Nontrivial ℋ] in
private lemma phiK_nonneg (K : L ℋ) {T : L (HSOp ℋ)} (hT : 0 ≤ T) :
    0 ≤ phiK (ℋ := ℋ) K T := by
  dsimp [phiK]
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive (f := T)).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    exact ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos (ofOp (star K))).2
  have hre :
      Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K)))) =
        Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    simpa using
      (inner_re_symm (𝕜 := ℂ) (x := ofOp (star K)) (y := T (ofOp (star K))))
  rw [hre]
  exact hnonneg

omit [Nontrivial ℋ] in
lemma phiK_add (K : L ℋ) (T S : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (T + S) = phiK (ℋ := ℋ) K T + phiK (ℋ := ℋ) K S := by
  simp [phiK, inner_add_right, Complex.add_re]

omit [Nontrivial ℋ] in
lemma phiK_smul (K : L ℋ) (r : ℝ) (T : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (r • T) = r * phiK (ℋ := ℋ) K T := by
  rw [phiK]
  change Complex.re (inner ℂ (ofOp (star K)) (r • T (ofOp (star K)))) =
    r * Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))
  rw [show inner ℂ (ofOp (star K)) (r • T (ofOp (star K))) =
      (r : ℂ) * inner ℂ (ofOp (star K)) (T (ofOp (star K))) by
        simpa using inner_smul_right (ofOp (star K)) (T (ofOp (star K))) (r : ℂ)]
  simp

omit [Nontrivial ℋ] in
lemma phiK_mono (K : L ℋ) {T S : L (HSOp ℋ)} (hTS : T ≤ S) :
    phiK (ℋ := ℋ) K T ≤ phiK (ℋ := ℋ) K S := by
  have hnonneg :
      0 ≤ S + (-1 : ℝ) • T := by
    simpa [sub_eq_add_neg] using (sub_nonneg.mpr hTS)
  have hphi_nonneg := phiK_nonneg (ℋ := ℋ) K hnonneg
  have hrewrite :
      phiK (ℋ := ℋ) K (S + (-1 : ℝ) • T) =
        phiK (ℋ := ℋ) K S - phiK (ℋ := ℋ) K T := by
    rw [phiK_add, phiK_smul]
    ring
  linarith [hrewrite ▸ hphi_nonneg]

private lemma re_inner_nonneg_of_nonneg
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} (hT : 0 ≤ T) :
    ∀ x : 𝓚, 0 ≤ Complex.re (inner ℂ x (T x)) := by
  intro x
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive (f := T)).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T x) x) :=
    ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos x).2
  have hre :
      Complex.re (inner ℂ x (T x)) = Complex.re (inner ℂ (T x) x) := by
    simpa using (inner_re_symm (𝕜 := ℂ) (x := x) (y := T x))
  rw [hre]
  exact hnonneg

private lemma aeval_apply_of_mem_eigenspace_realpoly
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) (p : ℝ[X]) :
    Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
      ((p.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
        Polynomial.aeval T.toLinearMap (p.map (algebraMap ℝ ℂ)) x := by
    simpa using
      congrArg (fun F : 𝓚 →ₗ[ℂ] 𝓚 => F x)
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℂ) (S := 𝓚 →L[ℂ] 𝓚) (T := ℂ) (U := 𝓚 →ₗ[ℂ] 𝓚)
          (φ := RingHom.id ℂ) (ψ := ContinuousLinearMap.toLinearMapRingHom)
          (h := by ext z; rfl) (p := p.map (algebraMap ℝ ℂ)) (a := T))
  rw [hmap]
  simpa using
    (Module.End.aeval_apply_of_hasEigenvector
      (f := T.toLinearMap) (p := p.map (algebraMap ℝ ℂ)) (μ := (r : ℂ)) (x := x) ⟨hx, hx0⟩)

-- The interpolation-based `cfcR`-on-eigenspace lemma is elaboration-heavy.
set_option maxHeartbeats 400000 in
private lemma cfcR_apply_of_mem_eigenspace_real
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (L 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : L 𝓚} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) :
    cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  have : IsScalarTower ℝ ℂ (L 𝓚) := RestrictScalars.isScalarTower ℝ ℂ (L 𝓚)
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite (spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := 𝓚) T.toLinearMap
  have hspecRfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  let s : Finset ℝ := hspecRfin.toFinset
  let q : ℝ[X] := Lagrange.interpolate s id fun y ↦ f y
  have hq_spec : (spectrum ℝ T).EqOn f q.eval := by
    intro y hy
    have hy' : y ∈ s := by
      simpa [s] using hy
    symm
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun z ↦ f z) (i := y)
        (hvs := fun _ _ _ _ h => h) hy')
  have hcfc : cfcR (ℋ := 𝓚) f T = cfcR (ℋ := 𝓚) q.eval T := by
    simpa [cfcR] using (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)
  have hpoly : cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q := by
    simpa [cfcR] using (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
  have hxv : Module.End.HasEigenvector T.toLinearMap (r : ℂ) x := ⟨hx, hx0⟩
  have hr_specC : (r : ℂ) ∈ spectrum ℂ T :=
    by
      change (r : ℂ) ∈ spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap)
      simpa using (Module.End.hasEigenvalue_of_hasEigenvector hxv).mem_spectrum
  have hr_spec : r ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hr_specC
  calc
    cfcR (ℋ := 𝓚) f T x = cfcR (ℋ := 𝓚) q.eval T x := by rw [hcfc]
    _ = Polynomial.aeval T q x := by rw [hpoly]
    _ = Polynomial.aeval T (q.map (algebraMap ℝ ℂ)) x := by
      symm
      simp
    _ = ((q.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
      simpa using aeval_apply_of_mem_eigenspace_realpoly hx q
    _ = (f r : ℂ) • x := by
      congr 1
      rw [Polynomial.eval_map_algebraMap]
      calc
        Polynomial.aeval (algebraMap ℝ ℂ r) q = ((Polynomial.eval r q : ℝ) : ℂ) := by
          simpa using
            (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := r) (p := q))
        _ = (f r : ℂ) := by
          simpa using congrArg (fun t : ℝ => (t : ℂ)) (hq_spec hr_spec).symm

-- This proof is isolated because the joint eigenspace decomposition is heartbeat-heavy.
set_option maxHeartbeats 800000 in
private lemma hmiddle_leftMul_rightMul
    {s : ℝ} {A B : L ℋ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
        (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
      leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    calc
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2)
          = B ^ (((-1 : ℝ) / 2) + ((-1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (-1 : ℝ) := by ring_nf
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf]
    calc
      rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
          leftMulHS (ℋ := ℋ) A *
          rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        leftMulHS (ℋ := ℋ) A *
          (rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))) := by
            rw [← mul_assoc,
              (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
              mul_assoc]
      _ = leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
            rw [← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)), hBnegOne]
  rw [hmid_prod]
  let T0 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (leftMulHS (ℋ := ℋ) A).toLinearMap
  let T1 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap
  let lhs : L (HSOp ℋ) :=
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
      (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)))
  let rhs : L (HSOp ℋ) :=
    leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))
  let D : L (HSOp ℋ) := lhs - rhs
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) :=
    IsSelfAdjoint.of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0)
  have hT0_symm : T0.IsSymmetric := by
    simpa [T0] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hleft_sa)
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hBinv_unit : IsUnit (B ^ (-1 : ℝ)) := by
    rcases hBunit with ⟨u, rfl⟩
    simp [CFC.rpow_neg_one_eq_inv u (by simpa using hB0)]
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hT1_symm : T1.IsSymmetric := by
    simpa [T1] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hright_sa)
  have hcomm : Commute T0 T1 := by
    show T0 * T1 = T1 * T0
    ext x
    simpa [T0, T1] using congrArg (fun F : L (HSOp ℋ) => F x)
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).eq
  have hleft_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s) (leftMulHS (ℋ := ℋ) A) =
        leftMulHS (ℋ := ℋ) (A ^ s) := by
    rw [show leftMulHS (ℋ := ℋ) (A ^ s) =
        leftMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := A) (y := s) (ha := hA0))]
    exact (leftMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A hA_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (Or.inl (ne_of_gt (hA_spec hx)))).continuousWithinAt)).symm
  have hright_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) =
        rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ (-s)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ))) by
      congr
      calc
        B ^ (-s) = (B ^ (-1 : ℝ)) ^ s := by
          symm
          simpa using (CFC.rpow_rpow B (-1 : ℝ) s (by norm_num) (hBunit.isStrictlyPositive hB0))
        _ = cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) := by
          simpa [cfcR] using
            (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B ^ (-1 : ℝ)) (y := s) (ha := hBinv0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) hBinv_sa
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          intro hx0
          exact spectrum.zero_notMem (R := ℝ) hBinv_unit (by simpa [hx0] using hx)
        exact (Real.continuousAt_rpow_const x s (Or.inl hx0)).continuousWithinAt)).symm
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hA0)
      (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hprod_sa :
      IsSelfAdjoint
        (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg hprod0
  have htop :
      (⨆ α, ⨆ β, eigenspace T0 α ⊓ eigenspace T1 β) = ⊤ := by
    exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      hT0_symm hT1_symm hcomm
  have hjoint_ker :
      ∀ α β,
        eigenspace T0 α ⊓ eigenspace T1 β ≤ LinearMap.ker D.toLinearMap := by
    intro α β x hx
    rcases hx with ⟨hx0, hx1⟩
    rw [LinearMap.mem_ker]
    by_cases hxzero : x = 0
    · simp [D, hxzero]
    have hxv0 : Module.End.HasEigenvector T0 α x := ⟨hx0, hxzero⟩
    have hxv1 : Module.End.HasEigenvector T1 β x := ⟨hx1, hxzero⟩
    have hαeq : α = (α.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT0_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv0))
        ).symm
    have hβeq : β = (β.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT1_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv1))
        ).symm
    have hx0r : x ∈ eigenspace T0 (α.re : ℂ) := by
      rwa [hαeq] at hx0
    have hx1r : x ∈ eigenspace T1 (β.re : ℂ) := by
      rwa [hβeq] at hx1
    have hT0_nonneg_re :
        ∀ y : HSOp ℋ, 0 ≤ Complex.re (inner ℂ y (T0 y)) := by
      intro y
      simpa [T0] using
        re_inner_nonneg_of_nonneg
          (T := leftMulHS (ℋ := ℋ) A)
          (leftMulHS_nonneg (ℋ := ℋ) hA0) y
    have hT1_nonneg_re :
        ∀ y : HSOp ℋ, 0 ≤ Complex.re (inner ℂ y (T1 y)) := by
      intro y
      simpa [T1] using
        re_inner_nonneg_of_nonneg
          (T := rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)))
          (rightMulHS_nonneg (ℋ := ℋ) hBinv0) y
    have hαnonneg : 0 ≤ α.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0r, hxzero⟩)
        hT0_nonneg_re
    have hβnonneg : 0 ≤ β.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1r, hxzero⟩)
        hT1_nonneg_re
    have hxprod :
        x ∈ eigenspace
          ((leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap)
          (((α.re * β.re : ℝ) : ℂ)) := by
      rw [Module.End.mem_eigenspace_iff]
      have hx0apply : T0 x = (α.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx0r
      have hx1apply : T1 x = (β.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx1r
      have hx0apply' :
          leftMulHS (ℋ := ℋ) A x = (α.re : ℂ) • x := by
        simpa [T0] using hx0apply
      have hx1apply' :
          rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x = (β.re : ℂ) • x := by
        simpa [T1] using hx1apply
      show leftMulHS (ℋ := ℋ) A (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x) =
        (((α.re * β.re : ℝ) : ℂ)) • x
      rw [hx1apply', ContinuousLinearMap.map_smul, hx0apply']
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hlhsx :
        lhs x = ((((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) • x) := by
      simpa [lhs] using
        cfcR_apply_of_mem_eigenspace_real
          (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hprod_sa hxprod
    have hrhsx :
        rhs x = ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x) := by
      change (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) x =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      have hleftx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) x =
            (((α.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hleft_sa hx0r
      have hrightx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s)
              (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) x =
            (((β.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := HSOp ℋ) (f := fun t : ℝ ↦ t ^ s) hright_sa hx1r
      rw [← hleft_pow, ← hright_pow, ContinuousLinearMap.mul_def]
      show cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A)
          (cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s)
            (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) x) =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      rw [hrightx, ContinuousLinearMap.map_smul, hleftx]
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hscal :
        (((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) =
          ((((α.re ^ s) * (β.re ^ s) : ℝ)) : ℂ) := by
      exact congrArg (fun t : ℝ => (t : ℂ)) (Real.mul_rpow hαnonneg hβnonneg)
    simpa [D] using
      sub_eq_zero.mpr (hlhsx.trans (hscal ▸ hrhsx.symm))
  have hker_top : LinearMap.ker D.toLinearMap = ⊤ := by
    apply top_unique
    rw [← htop]
    refine iSup_le ?_
    intro α
    refine iSup_le ?_
    intro β
    exact hjoint_ker α β
  have hDzero : D = 0 := by
    ext x
    have hx : x ∈ LinearMap.ker D.toLinearMap := by simp [hker_top]
    exact LinearMap.mem_ker.mp hx
  have hlhs_eq_rhs : lhs = rhs := sub_eq_zero.mp hDzero
  simpa [lhs, rhs] using hlhs_eq_rhs

-- The bridge lemma expands a large `HSOp`-valued generalized perspective term.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma phiK_operatorPowerMean_eq_liebTraceMap
    {s : ℝ} (K A B : L ℋ) (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B)) =
      liebTraceMap (ℋ := ℋ) s K A B := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      (by intro x hx; exact (hA_spec hx).le)
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_half :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((1 : ℝ) / 2)
          (Or.inr (by positivity))).continuousWithinAt)).symm
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBpow :
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2) = B ^ (1 - s) := by
    calc
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)
          = B ^ (((1 : ℝ) / 2) + (-s)) * B ^ ((1 : ℝ) / 2) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ ((((1 : ℝ) / 2) + (-s)) + ((1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (1 - s) := by ring_nf
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    calc
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2)
          = B ^ (((-1 : ℝ) / 2) + ((-1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (-1 : ℝ) := by ring_nf
  have hBinvHalf0 : 0 ≤ B ^ ((-1 : ℝ) / 2) := by
    simp
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hright_invHalf0 :
      0 ≤ rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    exact rightMulHS_nonneg (ℋ := ℋ) hBinvHalf0
  have hmid_nonneg :
      0 ≤ cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) := by
    rw [hright_negHalf]
    simpa [mul_assoc] using
      conjugate_nonneg_of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0) hright_invHalf0
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf]
    calc
      rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
          leftMulHS (ℋ := ℋ) A *
          rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))
          =
        leftMulHS (ℋ := ℋ) A *
          (rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2))) := by
            rw [← mul_assoc,
              (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
              mul_assoc]
      _ = leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
            rw [← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)), hBnegOne]
  have hmiddle :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
            leftMulHS (ℋ := ℋ) A *
            cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    exact hmiddle_leftMul_rightMul (ℋ := ℋ) (s := s) ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩
  have happly :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K)) =
        ofOp (A ^ s * star K * B ^ (1 - s)) := by
    have hcomm_half :
        Commute (leftMulHS (ℋ := ℋ) (A ^ s)) (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) :=
      leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B ^ ((1 : ℝ) / 2))
    have hright_pow :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)) := by
            simp [mul_assoc]
        _ = rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by rw [hBpow]
    have hreorder :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          ((rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              leftMulHS (ℋ := ℋ) (A ^ s)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                simp [mul_assoc]
        _ =
          ((leftMulHS (ℋ := ℋ) (A ^ s) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                rw [hcomm_half.eq]
        _ =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
                simp [mul_assoc]
    calc
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K))
        =
          (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) (ofOp (star K)) := by
            rw [OperatorGeometricMean.operatorPowerMean, GeneralizedPerspective,
              GeneralizedPerspectiveFunction.hSqrt, GeneralizedPerspectiveFunction.hInvSqrt]
            simp only [Real.rpow_one]
            rw [hmiddle]
            rw [hright_half]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) *
              (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
                rightMulHS (ℋ := ℋ) (B ^ (-s)) *
                rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)))) (ofOp (star K)) := by
            rw [hreorder]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (1 - s))) (ofOp (star K)) := by
            rw [hright_pow]
      _ = ofOp (A ^ s * star K * B ^ (1 - s)) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
  calc
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [phiK, happly]
    _ = traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K) := by
          rw [traceRe]
          set X : L ℋ := A ^ s * star K * B ^ (1 - s)
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ
                  ((K * X).toLinearMap)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) =
                Complex.re (LinearMap.trace ℂ ℋ ((X * K).toLinearMap)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap X.toLinearMap)
          simpa [X, mul_assoc] using htrace'.trans hcycle
    _ = liebTraceMap (ℋ := ℋ) s K A B := by
          rfl


end LiebAndoTrace
