import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Lieb.LiebConcavity
import D5.S3.Quantum.Lieb.MatrixTracePerspective
import D5.S3.Quantum.Recovery.PetzActualLikelihoodEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Superadditivity of the geometric PGM risk

Diagonal Lieb concavity controls the quadratic term of the variational risk.
Continuity extends this comparison to singular reference matrices, where the
supported inverse still attains the minimum. Applying superadditivity to the
tilted likelihood ensemble yields the coefficient-one entropy-loss bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open QuadraticBayesRiskGeometricPetz
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open LiebAndoTrace (liebTraceMap liebTrace_jointlyConcaveOn_pdSet)

open private transport transport_pd transport_lieb from
  D5.S3.Quantum.Lieb.MatrixTracePerspective

open private scoreSecondMoment scoreMoment_isHermitian ensemble_posSemidef ensemble_support
  tracePair_comm tracePair_smul_left tracePair_smul_right from
  D5.S3.Quantum.Recovery.QuadraticBayesRiskGeometricPetz

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace

namespace PetzGeometricRiskSuperadditivity

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

private def rootQuadratic (Q X : Matrix n n ℂ) : ℝ :=
  tracePair X (CFC.sqrt Q * X * CFC.sqrt Q)

private theorem rootQuadratic_smul (Q X : Matrix n n ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hQ : Q.PosSemidef) :
    rootQuadratic (r • Q) X = r * rootQuadratic Q X := by
  have hs : CFC.sqrt (r • Q) = Real.sqrt r • CFC.sqrt Q := by
    apply CFC.sqrt_unique _ (smul_nonneg (Real.sqrt_nonneg r) (CFC.sqrt_nonneg Q))
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hr,
      CFC.sqrt_mul_sqrt_self Q hQ.nonneg]
  simp only [rootQuadratic, hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hr, tracePair_smul_right]

private theorem liebTrace_half_eq (Q X : Matrix n n ℂ)
    (hQ : Q.PosDef) (hX : X.IsHermitian) :
    liebTraceMap (1 / 2 : ℝ) (star (transport X)) (transport Q) (transport Q) =
      rootQuadratic Q X := by
  rw [transport_lieb X Q Q hQ hQ, hX.eq,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  change (trace (X * CFC.rpow Q (1 / 2) * X * CFC.rpow Q (1 / 2))).re =
    tracePair X (CFC.sqrt Q * X * CFC.sqrt Q)
  simp only [CFC.rpow_eq_pow, ← CFC.sqrt_eq_rpow, tracePair, Matrix.mul_assoc]

private theorem rootQuadratic_add_le_of_posDef (Q S X : Matrix n n ℂ)
    (hQ : Q.PosDef) (hS : S.PosDef) (hX : X.IsHermitian) :
    rootQuadratic Q X + rootQuadratic S X ≤ rootQuadratic (Q + S) X := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let _ := hn
    simp [rootQuadratic, tracePair, Matrix.trace]
  | inr hn =>
    let _ := hn
    have h2Q := hQ.smul (show (0 : ℝ) < 2 by norm_num)
    have h2S := hS.smul (show (0 : ℝ) < 2 by norm_num)
    have h := liebTrace_jointlyConcaveOn_pdSet (s := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (star (transport X)) (θ := (1 / 2 : ℝ))
      (transport_pd h2Q) (transport_pd h2S) (transport_pd h2Q) (transport_pd h2S)
      (by norm_num) (by norm_num)
    have hmap (r : ℝ) (M : Matrix n n ℂ) : transport (r • M) = r • transport M := by
      simp only [← Complex.coe_smul, map_smul]
    have hMid :
        (1 - 1 / 2 : ℝ) • transport ((2 : ℝ) • Q) +
          (1 / 2 : ℝ) • transport ((2 : ℝ) • S) = transport (Q + S) := by
      simp only [hmap, smul_smul, map_add]
      norm_num
    rw [hMid, liebTrace_half_eq _ X (hQ.add hS) hX,
      liebTrace_half_eq _ X h2Q hX, liebTrace_half_eq _ X h2S hX,
      rootQuadratic_smul Q X 2 (by norm_num) hQ.posSemidef,
      rootQuadratic_smul S X 2 (by norm_num) hS.posSemidef] at h
    simp only [smul_eq_mul] at h
    linarith only [h]

private theorem continuousOn_rootQuadratic (X : Matrix n n ℂ) :
    ContinuousOn (fun Q => rootQuadratic Q X) {Q : Matrix n n ℂ | 0 ≤ Q} := by
  let T : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have hR : ContinuousOn CFC.sqrt {Q : Matrix n n ℂ | 0 ≤ Q} :=
    CFC.continuousOn_sqrt
  change ContinuousOn (fun Q => T (X * (CFC.sqrt Q * X * CFC.sqrt Q))) _
  exact T.continuous.comp_continuousOn
    (continuousOn_const.mul ((hR.mul continuousOn_const).mul hR))

/-- The diagonal Lieb quadratic form is superadditive on the full PSD cone. -/
private theorem rootQuadratic_add_le (Q S X : Matrix n n ℂ)
    (hQ : Q.PosSemidef) (hS : S.PosSemidef) (hX : X.IsHermitian) :
    rootQuadratic Q X + rootQuadratic S X ≤ rootQuadratic (Q + S) X := by
  let shift (M : Matrix n n ℂ) (ε : ℝ) := M + ε • (1 : Matrix n n ℂ)
  have hcont (M : Matrix n n ℂ) : Continuous (shift M) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hPSD (M : Matrix n n ℂ) (hM : M.PosSemidef) (ε : ℝ) (hε : 0 ≤ ε) :
      (shift M ε).PosSemidef :=
    hM.add ((Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef).smul hε)
  have hPD (M : Matrix n n ℂ) (hM : M.PosSemidef) (ε : ℝ) (hε : 0 < ε) :
      (shift M ε).PosDef :=
    Matrix.PosDef.posSemidef_add hM ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hε)
  have hsingle (M : Matrix n n ℂ) (hM : M.PosSemidef) :
      ContinuousOn (fun ε => rootQuadratic (shift M ε) X) (Ici (0 : ℝ)) :=
    (continuousOn_rootQuadratic X).comp (hcont M).continuousOn
      (fun ε hε => (hPSD M hM ε hε).nonneg)
  have hLeft : ContinuousOn
      (fun ε => rootQuadratic (shift Q ε) X + rootQuadratic (shift S ε) X) (Ici (0 : ℝ)) :=
    (hsingle Q hQ).add (hsingle S hS)
  have hRight : ContinuousOn (fun ε => rootQuadratic (shift Q ε + shift S ε) X)
      (Ici (0 : ℝ)) :=
    (continuousOn_rootQuadratic X).comp ((hcont Q).add (hcont S)).continuousOn
      (fun ε hε => ((hPSD Q hQ ε hε).add (hPSD S hS ε hε)).nonneg)
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hsub : 𝓝[Ioi (0 : ℝ)] 0 ≤ 𝓝[Ici (0 : ℝ)] 0 :=
    nhdsWithin_mono _ Ioi_subset_Ici_self
  have _ : (𝓝[Ioi (0 : ℝ)] 0).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have h := le_of_tendsto_of_tendsto
    ((hLeft 0 h0).tendsto.mono_left hsub) ((hRight 0 h0).tendsto.mono_left hsub) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact rootQuadratic_add_le_of_posDef _ _ X (hPD Q hQ ε hε) (hPD S hS ε hε) hX)
  simpa only [shift, zero_smul, add_zero] using h

private theorem rootQuadratic_nonneg (Q X : Matrix n n ℂ) (hX : X.IsHermitian) :
    0 ≤ rootQuadratic Q X := by
  let R := CFC.sqrt Q
  have hR : R.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hXR : (X * R * X).PosSemidef := by
    simpa only [hX.eq] using hR.conjTranspose_mul_mul_same X
  have h := (Complex.nonneg_iff.mp (hXR.trace_mul_nonneg hR)).1
  simpa only [rootQuadratic, tracePair, R, Matrix.mul_assoc] using h

private def geometricTrial (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix n n ℂ) : ℝ :=
  scoreSecondMoment A c - 2 * tracePair (scoreMoment A c) X +
    rootQuadratic (∑ i, A i) X

/-- The supported inverse supplies an attained minimum of the geometric trial. -/
private theorem geometricTrial_minimum (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) :
    ∃ Y : Matrix n n ℂ, Y.IsHermitian ∧ geometricTrial A c Y = geometricRisk A c ∧
      ∀ X : Matrix n n ℂ, X.IsHermitian → geometricRisk A c ≤ geometricTrial A c X := by
  let Q := ∑ i, A i
  let P := spectralSupport Q
  let R := CFC.sqrt Q
  let W := spectralInverseSqrt Q
  let B := scoreMoment A c
  let Y := W * B * W
  have hQ : Q.PosSemidef := ensemble_posSemidef A hA
  have hB : B.IsHermitian := scoreMoment_isHermitian A c hA
  have hleft (i : ι) : P * A i = A i := (ensemble_support A hA i).1
  have hright (i : ι) : A i * P = A i := (ensemble_support A hA i).2
  have hPB : P * B = B := by
    simp only [B, scoreMoment, Matrix.mul_sum, Matrix.mul_smul, hleft]
  have hBP : B * P = B := by
    simp only [B, scoreMoment, Matrix.sum_mul, Matrix.smul_mul, hright]
  obtain ⟨-, hW, -, -, -, -, -, -⟩ := spectral_sqrt_normalization Q hQ
  change Wᴴ = W at hW
  obtain ⟨hRW, hWR, -, -⟩ := spectral_sqrt_inverse_products Q hQ
  have hY : Y.IsHermitian := by
    change Yᴴ = Y
    simp only [Y, Matrix.conjTranspose_mul, hW, hB.eq, Matrix.mul_assoc]
  have hSolve : R * Y * R = B := by
    calc
      _ = (R * W) * B * (W * R) := by simp only [Y, Matrix.mul_assoc]
      _ = B := by rw [hRW, hWR, hPB, hBP]
  have hCross (U : Matrix n n ℂ) : tracePair U (R * Y * R) = tracePair B U := by
    rw [hSolve, tracePair_comm U B]
  have hCross' (U : Matrix n n ℂ) : tracePair Y (R * U * R) = tracePair B U := by
    rw [← hCross U]
    simpa only [tracePair, Matrix.mul_assoc] using
      congrArg Complex.re (Matrix.trace_mul_comm (Y * R) (U * R))
  have hSquare (X : Matrix n n ℂ) :
      rootQuadratic Q (X - Y) =
        rootQuadratic Q X - 2 * tracePair B X + tracePair B Y := by
    have hExpand :
        tracePair (X - Y) (R * (X - Y) * R) =
          tracePair X (R * X * R) - tracePair X (R * Y * R) -
            (tracePair Y (R * X * R) - tracePair Y (R * Y * R)) := by
      simp only [tracePair, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
      ring
    change tracePair (X - Y) (R * (X - Y) * R) =
      tracePair X (R * X * R) - 2 * tracePair B X + tracePair B Y
    rw [hExpand, hCross X, hCross' X, hCross Y]
    ring
  refine ⟨Y, hY, ?_, ?_⟩
  · change scoreSecondMoment A c - 2 * tracePair B Y + rootQuadratic Q Y =
      scoreSecondMoment A c - tracePair B Y
    rw [show rootQuadratic Q Y = tracePair B Y from hCross Y]
    ring
  · intro X hX
    change scoreSecondMoment A c - tracePair B Y ≤
      scoreSecondMoment A c - 2 * tracePair B X + rootQuadratic Q X
    linarith only [hSquare X, rootQuadratic_nonneg Q (X - Y) (hX.sub hY)]

/-- Superadditivity for arbitrary finite PSD ensembles with the same labels and scores. -/
theorem geometricRisk_add_ge (A A' : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hA' : ∀ i, (A' i).PosSemidef) :
    geometricRisk A c + geometricRisk A' c ≤ geometricRisk (fun i => A i + A' i) c := by
  obtain ⟨Y, hY, hAttain, -⟩ :=
    geometricTrial_minimum (fun i => A i + A' i) c (fun i => (hA i).add (hA' i))
  obtain ⟨-, -, -, hMin⟩ := geometricTrial_minimum A c hA
  obtain ⟨-, -, -, hMin'⟩ := geometricTrial_minimum A' c hA'
  have hM : scoreMoment (fun i => A i + A' i) c = scoreMoment A c + scoreMoment A' c := by
    simp only [scoreMoment, smul_add, Finset.sum_add_distrib]
  have hV : scoreSecondMoment (fun i => A i + A' i) c =
      scoreSecondMoment A c + scoreSecondMoment A' c := by
    simp only [scoreSecondMoment, Matrix.trace_add, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
  have hPair (B C : Matrix n n ℂ) : tracePair (B + C) Y = tracePair B Y + tracePair C Y := by
    simp only [tracePair, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  calc
    _ ≤ geometricTrial A c Y + geometricTrial A' c Y :=
      add_le_add (hMin Y hY) (hMin' Y hY)
    _ ≤ geometricTrial (fun i => A i + A' i) c Y := by
      simp only [geometricTrial, hM, hV, hPair, Finset.sum_add_distrib]
      linarith only [rootQuadratic_add_le _ _ Y (ensemble_posSemidef A hA)
        (ensemble_posSemidef A' hA') hY]
    _ = _ := hAttain

private theorem geometricTrial_smul (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (X : Matrix n n ℂ) (r : ℝ) (hr : 0 ≤ r) (hA : ∀ i, (A i).PosSemidef) :
    geometricTrial (fun i => r • A i) c X = r * geometricTrial A c X := by
  have hM : scoreMoment (fun i => r • A i) c = r • scoreMoment A c := by
    simp only [scoreMoment, Finset.smul_sum, smul_smul, mul_comm]
  have hV : scoreSecondMoment (fun i => r • A i) c = r * scoreSecondMoment A c := by
    simp only [scoreSecondMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp only [geometricTrial, hM, hV, tracePair_smul_left, ← Finset.smul_sum,
    rootQuadratic_smul _ _ _ hr (ensemble_posSemidef A hA)]
  ring

/-- Nonnegative scaling, including zero, for the same supported risk. -/
theorem geometricRisk_smul (A : ι → Matrix n n ℂ) (c : ι → ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hA : ∀ i, (A i).PosSemidef) :
    geometricRisk (fun i => r • A i) c = r * geometricRisk A c := by
  obtain ⟨Y, hY, hAttain, hMin⟩ := geometricTrial_minimum A c hA
  obtain ⟨Z, hZ, hAttain', hMin'⟩ :=
    geometricTrial_minimum (fun i => r • A i) c (fun i => (hA i).smul hr)
  have hScale (X : Matrix n n ℂ) := geometricTrial_smul A c X r hr hA
  apply le_antisymm
  · simpa only [hScale Y, hAttain] using hMin' Y hY
  · rw [← hAttain', hScale Z]
    exact mul_le_mul_of_nonneg_left (hMin Z hZ) hr

private theorem geometricRisk_nonneg (A : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) : 0 ≤ geometricRisk A c := by
  rw [geometricRisk_eq_half_pairwise A c hA]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (sq_nonneg _)
      (Complex.nonneg_iff.mp ((hA i).trace_mul_nonneg ((pgmEffects_isPOVM A hA).1 (some j)))).1)

/-- Pointwise Loewner domination of the scaled ensemble transfers geometric risk. -/
theorem smul_geometricRisk_le (A A' : ι → Matrix n n ℂ) (c : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (r : ℝ) (hr : 0 ≤ r)
    (hDom : ∀ i, r • A i ≤ A' i) :
    r * geometricRisk A c ≤ geometricRisk A' c := by
  let D : ι → Matrix n n ℂ := fun i => A' i - r • A i
  have hD (i : ι) : (D i).PosSemidef := Matrix.le_iff.mp (hDom i)
  have hDecomp : (fun i => r • A i + D i) = A' := by
    funext i
    dsimp only [D]
    abel
  have h := geometricRisk_add_ge (fun i => r • A i) D c (fun i => (hA i).smul hr) hD
  rw [hDecomp, geometricRisk_smul A c r hr hA] at h
  linarith only [h, geometricRisk_nonneg D c hD]

open PetzLikelihoodHessianIntegration (bkmDeficit geometricRisk_sqrt_le_of_hessian)
open LikelihoodRationalTailSeparation (mixtureScore)

/-- The sampled Hessian bound with the original score and its exact tilted mass. -/
theorem tilted_bkmDeficit_geometricRisk
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (hQ : (∑ i, A i).PosDef) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    (1 - t) * geometricRisk A (fun i => mixtureScore (lam i) t) ≤
      bkmDeficit (fun i => (1 - t + t * lam i) • A i) (fun i => mixtureScore (lam i) t) := by
  let A' : ι → Matrix n n ℂ := fun i => (1 - t + t * lam i) • A i
  let d : ι → ℝ := fun i => mixtureScore (lam i) t
  have hr : 0 < 1 - t := sub_pos.mpr ht.2
  have hDom (i : ι) : (1 - t) • A i ≤ A' i := by
    rw [show A' i = (1 - t) • A i + (t * lam i) • A i by simp only [A', add_smul]]
    exact le_add_of_nonneg_right (smul_nonneg (mul_nonneg ht.1 (hlam i)) (hA i).nonneg)
  have hA' (i : ι) : (A' i).PosSemidef :=
    ((smul_nonneg hr.le (hA i).nonneg).trans (hDom i)).posSemidef
  have hExtra : (∑ i, (t * lam i) • A i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => (hA i).smul (mul_nonneg ht.1 (hlam i))
  have hQ' : (∑ i, A' i).PosDef := by
    simpa only [A', add_smul, Finset.sum_add_distrib, Finset.smul_sum] using
      (hQ.smul hr).add_posSemidef hExtra
  change (1 - t) * geometricRisk A d ≤ bkmDeficit A' d
  exact (smul_geometricRisk_le A A' d hA (1 - t) hr.le hDom).trans
    (geometricRisk_le_bkm_deficit A' d hA' hQ')

/-- Apply the existing endpoint integration theorem to the scaled path. -/
private theorem geometricRisk_sqrt_le_of_hessian_unit
    (A : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (δ velocity hessian : ℝ → ℝ) (hδ₁ : ContinuousAt δ 1)
    (hδ₀ : δ 0 = 0) (hv₀ : velocity 0 = 0)
    (hδ : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt δ (velocity t) (Ico 0 1) t)
    (hv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt velocity (hessian t) (Ico 0 1) t)
    (hh : ∀ u ∈ Ico (0 : ℝ) 1, ContinuousOn hessian (Icc 0 u))
    (hSample : ∀ t ∈ Ico (0 : ℝ) 1,
      (1 - t) * geometricRisk A (fun i => mixtureScore (lam i) t) ≤ hessian t) :
    geometricRisk A (fun i => Real.sqrt (lam i)) ≤ δ 1 := by
  have h := geometricRisk_sqrt_le_of_hessian A hA lam hlam
    (fun t => (2 / 3 : ℝ) * δ t) (fun t => (2 / 3 : ℝ) * velocity t)
    (fun t => (2 / 3 : ℝ) * hessian t)
    (continuousAt_const.mul hδ₁) (by simp only [hδ₀, mul_zero]) (by simp only [hv₀, mul_zero])
    (fun t ht => (hδ t ht).const_mul (2 / 3))
    (fun t ht => (hv t ht).const_mul (2 / 3))
    (fun u hu => continuousOn_const.mul (hh u hu))
    (fun t ht => mul_le_mul_of_nonneg_left (hSample t ht) (by norm_num))
  exact le_of_mul_le_mul_left h (by norm_num)

open PetzActualLikelihoodEntropy (actualEntropyLoss actualEntropyLoss_dummy geometricRisk_dummy)

open private lossPath velocity hessian lossPath_one continuous_lossPath lossPath_zero velocity_zero
  lossPath_hasDerivAt velocity_hasDerivAt continuousOn_hessian hessian_eq_tilted_bkmDeficit
  dummyEnsemble dummyLikelihood dummyEnsemble_posSemidef dummyEnsemble_sum_posDef from
  D5.S3.Quantum.Recovery.PetzActualLikelihoodEntropy

/-- Coefficient one for the actual likelihood path with faithful reference mass. -/
theorem geometricRisk_sqrt_le_actualEntropyLoss_of_posDef
    (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hlam : ∀ i, 0 ≤ lam i)
    (hQ : (∑ i, A i).PosDef) :
    geometricRisk A (fun i => Real.sqrt (lam i)) ≤ actualEntropyLoss A lam := by
  rw [← lossPath_one]
  refine geometricRisk_sqrt_le_of_hessian_unit A hA lam hlam
    (lossPath A lam) (velocity A lam) (hessian A lam)
    (continuous_lossPath A lam hA).continuousAt (lossPath_zero A lam) (velocity_zero A lam)
    (fun _ ht => (lossPath_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
    (fun _ ht => (velocity_hasDerivAt A lam hA hQ hlam ht).hasDerivWithinAt)
    (fun _ hu => continuousOn_hessian A lam hA hQ hlam hu) ?_
  intro t ht
  exact (tilted_bkmDeficit_geometricRisk A hA hQ lam hlam t ht).trans_eq
    (hessian_eq_tilted_bkmDeficit A lam hlam ht).symm

/-- Coefficient one for arbitrary PSD ensembles, including singular endpoint mass. -/
theorem geometricRisk_sqrt_le_actualEntropyLoss
    (A : ι → Matrix n n ℂ) (lam : ι → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hlam : ∀ i, 0 ≤ lam i) :
    geometricRisk A (fun i => Real.sqrt (lam i)) ≤ actualEntropyLoss A lam := by
  have hlam' (i : Option ι) : 0 ≤ dummyLikelihood lam i := by
    cases i with
    | none => exact zero_le_one
    | some i => exact hlam i
  have h := geometricRisk_sqrt_le_actualEntropyLoss_of_posDef
    (dummyEnsemble A) (dummyLikelihood lam) (dummyEnsemble_posSemidef A hA) hlam'
    (dummyEnsemble_sum_posDef A hA)
  have hScores : (fun i => Real.sqrt (dummyLikelihood lam i)) =
      fun i : Option ι => i.elim (Real.sqrt 1) (fun j => Real.sqrt (lam j)) := by
    funext i
    cases i <;> rfl
  rw [hScores, geometricRisk_dummy _ _ _ hA, actualEntropyLoss_dummy A lam hA hlam] at h
  exact h

end PetzGeometricRiskSuperadditivity
