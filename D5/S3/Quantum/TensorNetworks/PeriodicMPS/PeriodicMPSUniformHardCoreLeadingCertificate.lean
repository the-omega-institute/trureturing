/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreLeadingCertificate
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLeadingRows, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetMatching]
   utility: none
   digest: The reduced fold equation has a simple opposite root that yields an actual analytic partner path at every length at least seven. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLeadingRows
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetMatching

/-! The opposite-slope certificate and its analytic realization in the hard-core chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticPartner

open PeriodicMPSAnalyticPartnerPolynomial
open PeriodicMPSUniformHardCoreLeadingRows
open PeriodicMPSUniformHardCoreFirstJet (witness regularReadout component)
open PeriodicMPSUniformHardCoreFoldCurvature (nullSlope)
open PeriodicMPSUniformHardCoreQuarticSign (F G Z G_pos)
open PeriodicMPSUniformHardCoreJetElimination (foldA foldB)
open PeriodicMPSUniformHardCoreNormalizedJet (ratio oppositeSlope oppositeSlope_ne_one)
open Filter Asymptotics
open scoped Matrix Topology

open private realJet imagJet realJet_shift_two imagJet_two_zero regular_of_blocks from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreJetMatching
open private quadratic_readouts foldA_ratio_ne_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreNormalizedJet

noncomputable section


private abbrev leadingSystem (s : ℕ) (w : Parameters) : Parameters :=
  scaled (difference s (nullSlope (s + 4))) (0, w)

private def blockMap {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  M.mulVecLin.toContinuousLinearMap

private theorem blockMap_apply {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    blockMap M v = M *ᵥ v := rfl

private theorem block_unit {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (h : M.det ≠ 0) :
    IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)

private theorem scaledBlock_injective {n k : ℕ} (hn : 7 ≤ n)
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : M.det ≠ 0) :
    Function.Injective (Z n ^ 2 • blockMap M) := by
  intro u v h
  apply Matrix.mulVec_injective_iff_isUnit.mpr (block_unit hM)
  exact (smul_right_injective _ (pow_ne_zero 2 (witnessMass_ne_zero hn))) h

private theorem real_shift (n : ℕ) (hn : 7 ≤ n) (t : ℝ) (v : RealRegular) :
    realJet n (leadingPath t v) 2 =
      realJet n (leadingPath t 0) 2 + PeriodicMPSUniformHardCoreFirstJet.realBlock n *ᵥ v := by
  have h : leadingPath t v = PeriodicMPSUniformHardCoreJetMatching.addReal₂ (leadingPath t 0) v := by
    simp [leadingPath, PeriodicMPSUniformHardCoreJetMatching.addReal₂]
  rw [h, realJet_shift_two n hn]

private theorem leadingSystem_imag (s : ℕ) (hs : 3 ≤ s) (w : Parameters) :
    (leadingSystem s w).1 = (Z (s + 4) ^ 2) •
      (imagLeading (s + 4) w - imagLeading (s + 4) (original (nullSlope (s + 4)))) := by
  rw [leadingSystem, scaled_zero]
  exact funext (imag_leading_row s hs w)

private theorem leadingSystem_real (s : ℕ) (hs : 3 ≤ s) (t : ℝ) (v : RealRegular) :
    (leadingSystem s (leadingParameters (s + 4) t v)).2.1 = (Z (s + 4) ^ 2) •
      (realJet (s + 4) (leadingPath t v) 2 - realJet (s + 4) PeriodicMPSUniformHardCoreJetElimination.original 2) := by
  rw [leadingSystem, scaled_zero]
  funext i
  have h := real_leading_row s hs t v (.inl i)
  fin_cases i <;> exact h

private theorem imagLeading_on_path (n : ℕ) (hn : 7 ≤ n) (t : ℝ) (v : RealRegular) :
    imagLeading n (leadingParameters n t v) = imagLeading n (original (nullSlope n)) := by
  have hg := (G_pos hn).ne'
  have hz := witnessMass_ne_zero hn
  funext i
  fin_cases i <;>
    simp [imagLeading, leadingParameters, original, PeriodicMPSUniformHardCoreFirstJet.imagBlock, PeriodicMPSUniformHardCoreFirstJet.imagA, nullSlope];
    field_simp; ring

private def realEquiv (n : ℕ) (hn : 7 ≤ n) : RealRegular ≃L[ℝ] RealRegular :=
  (LinearEquiv.ofBijective (PeriodicMPSUniformHardCoreFirstJet.realBlock n).mulVecLin ⟨
    Matrix.mulVec_injective_iff_isUnit.mpr (block_unit (PeriodicMPSUniformHardCoreFirstJet.realBlock_det_ne_zero n hn)),
    Matrix.mulVec_surjective_iff_isUnit.mpr (block_unit (PeriodicMPSUniformHardCoreFirstJet.realBlock_det_ne_zero n hn))⟩).toContinuousLinearEquiv

/-- The closed real quadratic correction, obtained by applying the real block inverse
to the four differences at zero correction. -/
def realCorrection (n : ℕ) (hn : 7 ≤ n) (t : ℝ) : RealRegular :=
  (realEquiv n hn).symm (realJet n PeriodicMPSUniformHardCoreJetElimination.original 2 - realJet n (leadingPath t 0) 2)

private theorem realCorrection_matches (n : ℕ) (hn : 7 ≤ n) (t : ℝ) :
    realJet n (leadingPath t (realCorrection n hn t)) 2 = realJet n PeriodicMPSUniformHardCoreJetElimination.original 2 := by
  rw [real_shift n hn]
  change _ + realEquiv n hn ((realEquiv n hn).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]

private theorem regular_matches (n : ℕ) (hn : 7 ≤ n) (t : ℝ) :
    PeriodicMPSUniformHardCoreNormalizedJet.regularCoeff n (leadingPath t (realCorrection n hn t)) 2 = PeriodicMPSUniformHardCoreNormalizedJet.regularCoeff n PeriodicMPSUniformHardCoreJetElimination.original 2 :=
  regular_of_blocks n _ _ 2 (realCorrection_matches n hn t)
    ((imagJet_two_zero n hn _).trans (imagJet_two_zero n hn _).symm)

private theorem differentiableAt_real_base (n : ℕ) (hn : 7 ≤ n) (t : ℝ) :
    DifferentiableAt ℝ (fun z => realJet n (leadingPath z 0) 2) t := by
  have hp (u : ℝ) := (quadratic_readouts n hn (leadingPath u 0)).1
  have hq (u : ℝ) := (quadratic_readouts n hn (leadingPath u 0)).2.1
  have hw (u : ℝ) := (quadratic_readouts n hn (leadingPath u 0)).2.2.2.1
  have hv (u : ℝ) := (quadratic_readouts n hn (leadingPath u 0)).2.2.2.2.1
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · change DifferentiableAt ℝ (fun z => PeriodicMPSUniformHardCoreNormalizedJet.normalizedCoeff false n (leadingPath z 0) 1 2) t
    rw [funext hp]
    simp only [PeriodicMPSUniformHardCoreJetElimination.p₂, PeriodicMPSUniformHardCoreJetElimination.mass₂, leadingPath]
    fun_prop
  · change DifferentiableAt ℝ (fun z => PeriodicMPSUniformHardCoreNormalizedJet.normalizedCoeff false n (leadingPath z 0) 2 2) t
    rw [funext hq]
    simp only [PeriodicMPSUniformHardCoreJetElimination.q₂, PeriodicMPSUniformHardCoreJetElimination.mass₂, leadingPath]
    fun_prop
  · change DifferentiableAt ℝ (fun z => PeriodicMPSUniformHardCoreNormalizedJet.normalizedCoeff false n (leadingPath z 0) 4 2) t
    rw [funext hw]
    simp only [PeriodicMPSUniformHardCoreJetElimination.w₂, leadingPath]
    fun_prop
  · change DifferentiableAt ℝ (fun z => PeriodicMPSUniformHardCoreNormalizedJet.normalizedCoeff false n (leadingPath z 0) 5 2) t
    rw [funext hv]
    simp only [PeriodicMPSUniformHardCoreJetElimination.v₂, leadingPath]
    fun_prop

private def eliminate (n : ℕ) (hn : 7 ≤ n) (t : ℝ) : Imaginary × RealRegular :=
  ((leadingParameters n t 0).1, realCorrection n hn t)

private theorem differentiableAt_eliminate (n : ℕ) (hn : 7 ≤ n) (t : ℝ) :
    DifferentiableAt ℝ (eliminate n hn) t := by
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;>
      simp [leadingParameters]; fun_prop
  · exact (realEquiv n hn).symm.differentiableAt.comp t
      ((differentiableAt_real_base n hn t).const_sub _)

/-- Opposite-slope leading coefficients of the chart parameters. -/
def oppositeParameters (n : ℕ) (hn : 7 ≤ n) : Parameters :=
  leadingParameters n (oppositeSlope n) (realCorrection n hn (oppositeSlope n))

private def reducedScale (n : ℕ) : ℝ := Z n ^ 2 / (2 * (ratio n + 2))

private theorem reducedScale_ne (n : ℕ) (hn : 7 ≤ n) : reducedScale n ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (witnessMass_ne_zero hn))
    (mul_ne_zero (by norm_num) (PeriodicMPSUniformHardCoreNormalizedJet.ratio_add_two_ne_zero n hn))

private theorem reduced_eq (s : ℕ) (hs : 3 ≤ s) (t : ℝ) :
    let n := s + 4
    let hn : 7 ≤ n := by omega
    leadingSystem s (leadingParameters n t (realCorrection n hn t)) =
      (0, 0, reducedScale n * ((t - 1) * (foldA (ratio n) * t + foldB (ratio n)))) := by
  dsimp only
  have hn : 7 ≤ s + 4 := by omega
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [leadingSystem_imag s hs, imagLeading_on_path _ hn, sub_self, smul_zero]
  · rw [leadingSystem_real s hs, realCorrection_matches _ hn, sub_self, smul_zero]
  · rw [leadingSystem, scaled_zero]
    have h := real_leading_row s hs t (realCorrection (s + 4) hn t) (.inr ())
    rw [show (rowData (.inr (.inr ()))).2 = 3 by rfl] at h
    simp only [h]
    rw [PeriodicMPSUniformHardCoreNormalizedJet.normalized_fold_difference _ hn _ (regular_matches _ hn t)]
    change _ = _
    unfold reducedScale leadingPath
    dsimp only
    ring

private theorem realDeriv (s : ℕ) (hs : 3 ≤ s) (t : ℝ) (v : RealRegular) :
    HasFDerivAt (fun v' : RealRegular =>
      (leadingSystem s (leadingParameters (s + 4) t v')).2.1)
      (Z (s + 4) ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.realBlock (s + 4))) v := by
  have hn : 7 ≤ s + 4 := by omega
  let c := Z (s + 4) ^ 2 • (realJet (s + 4) (leadingPath t 0) 2 -
    realJet (s + 4) PeriodicMPSUniformHardCoreJetElimination.original 2)
  refine ((Z (s + 4) ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.realBlock (s + 4))).hasFDerivAt.const_add c).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [leadingSystem_real s hs, real_shift _ hn]
    change _ = c + Z (s + 4) ^ 2 • (PeriodicMPSUniformHardCoreFirstJet.realBlock (s + 4) *ᵥ u)
    rw [add_comm (realJet _ _ 2), add_sub_assoc, smul_add, add_comm]

private theorem imagDeriv (s : ℕ) (hs : 3 ≤ s) (w : Parameters) :
    HasFDerivAt (fun u : Imaginary × RealRegular => (leadingSystem s (u.1, u.2, w.2.2)).1)
      ((Z (s + 4) ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.imagBlock (s + 4))).comp
        (ContinuousLinearMap.fst ℝ Imaginary RealRegular)) (w.1, w.2.1) := by
  let L := (Z (s + 4) ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.imagBlock (s + 4))).comp
    (ContinuousLinearMap.fst ℝ Imaginary RealRegular)
  let c := Z (s + 4) ^ 2 • (w.2.2 • PeriodicMPSUniformHardCoreFirstJet.imagA (s + 4) -
    imagLeading (s + 4) (original (nullSlope (s + 4))))
  refine (L.hasFDerivAt.add_const c).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun u => by
    dsimp only
    rw [leadingSystem_imag s hs]
    simp only [L, ContinuousLinearMap.comp_apply, smul_apply, blockMap_apply, imagLeading, c,
      add_sub_assoc, smul_add]
    rfl

/-- The derivative of the literal reduced coherence at the opposite root. -/
theorem reduced_fold_hasDerivAt (s : ℕ) (hs : 3 ≤ s) :
    let n := s + 4
    let hn : 7 ≤ n := by omega
    let t₀ := oppositeSlope n
    let d := reducedScale n * ((t₀ - 1) * foldA (ratio n))
    d ≠ 0 ∧
      HasDerivAt (fun t => (leadingSystem s (leadingParameters n t (realCorrection n hn t))).2.2)
        d t₀ := by
  dsimp only
  let n := s + 4
  let t₀ := oppositeSlope n
  have hn : 7 ≤ n := by omega
  have ha := foldA_ratio_ne_zero n hn
  have hroot : foldA (ratio n) * t₀ + foldB (ratio n) = 0 := by
    dsimp only [t₀, oppositeSlope]
    field_simp
    ring
  refine ⟨mul_ne_zero (reducedScale_ne n hn)
    (mul_ne_zero (sub_ne_zero.mpr (oppositeSlope_ne_one n hn)) ha), ?_⟩
  have h := (((hasDerivAt_id t₀).sub_const 1).mul
    (((hasDerivAt_id t₀).const_mul (foldA (ratio n))).add_const (foldB (ratio n)))).const_mul
      (reducedScale n)
  have hd : HasDerivAt (fun t => reducedScale n *
      ((t - 1) * (foldA (ratio n) * t + foldB (ratio n))))
      (reducedScale n * ((t₀ - 1) * foldA (ratio n))) t₀ := by
    simpa only [id_eq, Pi.mul_apply, mul_one, one_mul, hroot, add_zero, zero_add] using h
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    congrArg (fun z : Parameters => z.2.2) (reduced_eq s hs t))

/-- The actual cross-multiplied system has the required simple opposite root. -/
def oppositeLeadingCertificate (s : ℕ) (hs : 3 ≤ s) :
    LeadingCertificate (fun w => scaled (difference s (nullSlope (s + 4))) (0, w))
      (oppositeParameters (s + 4) (by omega)) := by
  let n := s + 4
  have hn : 7 ≤ n := by omega
  let t := oppositeSlope n
  refine {
    imagBlock := Z n ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.imagBlock n)
    realBlock := Z n ^ 2 • blockMap (PeriodicMPSUniformHardCoreFirstJet.realBlock n)
    imag_inj := scaledBlock_injective hn _ (PeriodicMPSUniformHardCoreFirstJet.imagBlock_det_ne_zero n hn)
    real_inj := scaledBlock_injective hn _ (PeriodicMPSUniformHardCoreFirstJet.realBlock_det_ne_zero n hn)
    imag_deriv := imagDeriv s hs _
    real_deriv := realDeriv s hs t (realCorrection n hn t)
    eliminate := eliminate n hn
    tangent := deriv (eliminate n hn) t
    eliminate_deriv := (differentiableAt_eliminate n hn t).hasDerivAt
    eliminate_at := rfl
    scale := reducedScale n
    A := foldA (ratio n)
    B := foldB (ratio n)
    scale_ne := reducedScale_ne n hn
    A_ne := foldA_ratio_ne_zero n hn
    root := rfl
    other_root := oppositeSlope_ne_one n hn
    reduced := Filter.Eventually.of_forall (reduced_eq s hs) }

/-- The opposite branch exists for every physical chain length at least seven.
The same witness gives exact matching, distinct chart points and the even Taylor data. -/
theorem exists_opposite_curve (n : ℕ) (hn : 7 ≤ n) :
    let s := n - 4
    let w₀ := oppositeParameters n hn
    ∃ w : ℝ → Parameters, ∃ w₂ : Parameters,
      w 0 = w₀ ∧ AnalyticAt ℝ w 0 ∧
      ((fun ε => w (-ε)) =ᶠ[𝓝 0] w) ∧
      AnalyticAt ℝ (fun ε => chart ε (w ε)) 0 ∧
      AnalyticAt ℝ (fun ε => chart ε (original (nullSlope n))) 0 ∧
      HasDerivAt (fun ε => (chart ε (w ε) 0).im) (oppositeSlope n) 0 ∧
      HasDerivAt (fun ε => (chart ε (original (nullSlope n)) 0).im) 1 0 ∧
      (∀ᶠ ε in 𝓝 0, regularReadout s (chart ε (w ε)) =
        regularReadout s (chart ε (original (nullSlope n))) ∧
        component false s 3 (chart ε (w ε)) =
        component false s 3 (chart ε (original (nullSlope n)))) ∧
      (∀ᶠ ε in 𝓝[≠] (0 : ℝ), chart ε (w ε) ≠ chart ε (original (nullSlope n))) ∧
      ∀ i : Fin 4,
        (fun ε : ℝ => (chart ε (w ε) i).im -
          (imagDirection w₀ i * ε + imagDirection w₂ i * ε ^ 3)) =O[𝓝 0] (fun ε => ε ^ 5) ∧
        (fun ε : ℝ => (chart ε (w ε) i).re -
          ((witness i).re + w₀.2.1 i * ε ^ 2 + w₂.2.1 i * ε ^ 4)) =O[𝓝 0] (fun ε => ε ^ 6) := by
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, n = s + 4 := ⟨n - 4, by omega⟩
  have hs : 3 ≤ s := by omega
  have h := exists_second_curve s hs (nullSlope (s + 4)) _ (oppositeLeadingCertificate s hs)
  simp only [Nat.add_sub_cancel]
  obtain ⟨w, hw₀, hw, he, hz, hx, hd, hd', hEq⟩ := h
  obtain ⟨w₂, ht⟩ := chart_taylor_four hw he
  have hne := eventually_second_curve_ne hd hd' (oppositeSlope_ne_one (s + 4) hn)
  refine ⟨w, w₂, hw₀, hw, he, hz, hx, hd, hd', hEq, hne, ?_⟩
  simpa only [hw₀] using ht

#print axioms reduced_fold_hasDerivAt
#print axioms oppositeLeadingCertificate
#print axioms exists_opposite_curve

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticPartner
