/- GID: D5/S3/Weil/ZetaBridge/PhysicalCosineTailProjection
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PhysicalCosineTailProjection
   mirror-E: none(waiver:analytic-hilbert-fourier-identification-without-executable-mirror)
   anchors: []
   utility: none
   digest: Complex Lebesgue L2 cosine-tail projections satisfy actual compressed-shift and finite-prime bounds for natural N < M and a > 0. -/

import D5.S3.Weil.ZetaBridge.PhysicalPrimeTwoCutoff
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace PhysicalCosineTailProjection

open MeasureTheory Set Filter
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix PhysicalPrimeTwoCutoff
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition

abbrev windowMeasure (a : ℝ) : Measure ℝ := volume.restrict (window a)
abbrev WindowL2 (a : ℝ) := Lp ℂ 2 (windowMeasure a)

private lemma mode_continuous (a : ℝ) (n : ℕ) :
    Continuous (fun x => (mode a n x : ℂ)) := by unfold mode; fun_prop

private lemma mode_norm_bound (a : ℝ) (n : ℕ) (x : ℝ) :
    ‖(mode a n x : ℂ)‖ ≤ |amplitude a n| := by
  rw [Complex.norm_real, Real.norm_eq_abs, mode, abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)

lemma mode_memLp (a : ℝ) (n : ℕ) :
    MemLp (fun x => (mode a n x : ℂ)) 2 (windowMeasure a) := by
  change MemLp (fun x => (mode a n x : ℂ)) 2 (volume.restrict (Ioc (-a) a))
  exact MemLp.of_bound (mode_continuous a n).aestronglyMeasurable
    |amplitude a n| (Eventually.of_forall (mode_norm_bound a n))

def modeL2 (a : ℝ) (n : ℕ) : WindowL2 a :=
  (mode_memLp a n).toLp (fun x => (mode a n x : ℂ))

private lemma pairing_zero_eq_window (a : ℝ) (f g : ℝ → ℂ) :
    pairing a 0 f g = ∫ x in window a, f x * g x := by
  rw [pairing_overlap]
  simp [overlap, window]

private lemma matrixEntry_zero_diagonal (a : ℝ) (ha : 0 < a) (n : ℕ) :
    matrixEntry a n n 0 = 1 := by
  have ha0 : 0 ≤ a := ha.le
  rw [matrixEntry_eq_matrix a ha, PhysicalCompressedCosineMatrix.matrix,
    if_pos (show |(0 : ℝ)| ≤ 2 * a by
      simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)]
  simp only [abs_zero, mul_zero, zero_div, Real.cos_zero, one_mul, sub_zero]
  rw [show (2 * a) / 2 = a by ring, sub_self, S_zero]
  by_cases hn : n = 0
  · subst n
    have hd : (Real.sqrt (2 * a)) ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
    have hdne : Real.sqrt (2 * a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    simp only [omega, Nat.cast_zero, mul_zero, zero_div, zero_add, S_zero,
      amplitude, ite_true]
    field_simp [hdne]
    nlinarith
  · have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hf : omega a n * a = (n : ℝ) * Real.pi := by
      unfold omega
      field_simp [ha.ne']
      <;> ring
    have hfpos : 0 < omega a n := by unfold omega; positivity
    have harg : (omega a n + omega a n) * a = ((2 * n : ℕ) : ℝ) * Real.pi := by
      push_cast
      nlinarith [hf]
    rw [S_of_ne a _ (ne_of_gt (add_pos hfpos hfpos)), harg, Real.sin_nat_mul_pi]
    simp only [zero_div, add_zero, amplitude, if_neg hn]
    rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 / (2 * a))]
    field_simp [ha.ne']
    <;> ring

private lemma matrixEntry_zero_gram (a : ℝ) (ha : 0 < a) (n m : ℕ) :
    matrixEntry a n m 0 = if n = m then 1 else 0 := by
  classical
  have hcap : |(0 : ℝ)| ≤ 2 * a := by
    simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le
  by_cases h : n = m
  · subst m
    simp only [if_pos rfl]
    exact matrixEntry_zero_diagonal a ha n
  · rw [if_neg h]
    rcases lt_or_gt_of_ne h with hnm | hmn
    · rw [matrixEntry_offdiagonal a ha n m hnm 0 hcap]
      simp
    · rw [matrixEntry_symmetric a ha n m 0,
        matrixEntry_offdiagonal a ha m n hmn 0 hcap]
      simp

private lemma modeL2_inner (a : ℝ) (n m : ℕ) :
    inner ℂ (modeL2 a n) (modeL2 a m) = (matrixEntry a n m 0 : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in window a, (mode a n x : ℂ) * (mode a m x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [(mode_memLp a n).coeFn_toLp, (mode_memLp a m).coeFn_toLp]
        with x hn hm
      change modeL2 a n x = (mode a n x : ℂ) at hn
      change modeL2 a m x = (mode a m x : ℂ) at hm
      rw [hn, hm]
      simp [RCLike.inner_apply', mul_comm]
    _ = _ := by
      rw [← pairing_zero_eq_window, pairing_ofReal]
      rfl

lemma modes_orthonormal (a : ℝ) (ha : 0 < a) :
    Orthonormal ℂ (modeL2 a) := by
  classical
  rw [orthonormal_iff_ite]
  intro n m
  rw [modeL2_inner, matrixEntry_zero_gram a ha]
  split_ifs <;> rfl

/-- The actual finite head on the original Ioc Lebesgue L2 carrier. -/
def headL2 (a : ℝ) (N : ℕ) (v : ℕ → ℂ) : WindowL2 a :=
  ∑ n ∈ Finset.range (N + 1), v n • modeL2 a n

private lemma headL2_mass (a : ℝ) (ha : 0 < a) (N : ℕ) (v : ℕ → ℂ) :
    ‖headL2 a N v‖ ^ 2 = headMass N v := by
  simpa only [headL2, headMass, LinearIsometry.toSpanSingleton_apply] using
    (modes_orthonormal a ha).orthogonalFamily.norm_sum v (Finset.range (N + 1))

private def profileBound (a : ℝ) (N : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ‖v n‖ * |amplitude a n|

private lemma profile_norm_bound (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (x : ℝ) :
    ‖profile a (Finset.range (N + 1)) v x‖ ≤ profileBound a N v := by
  unfold profile profileBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (mode_norm_bound a n x) (norm_nonneg _)

private lemma compressed_head_memLp (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (s : ℝ) :
    MemLp (compression a s (profile a (Finset.range (N + 1)) v)) 2
      (windowMeasure a) := by
  change MemLp (compression a s (profile a (Finset.range (N + 1)) v)) 2
    (volume.restrict (Ioc (-a) a))
  have hB : 0 ≤ profileBound a N v :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hm : Measurable (compression a s (profile a (Finset.range (N + 1)) v)) := by
    unfold compression zeroExtension
    exact (((profile_continuous a (Finset.range (N + 1)) v).measurable.indicator
      measurableSet_Ioc).comp (measurable_id.add_const s)).indicator measurableSet_Ioc
  apply MemLp.of_bound hm.aestronglyMeasurable (profileBound a N v)
  filter_upwards [] with x
  by_cases hx : x ∈ window a
  · by_cases hxs : x + s ∈ window a
    · simpa [compression, zeroExtension, hx, hxs] using profile_norm_bound a N v (x + s)
    · simpa [compression, zeroExtension, hx, hxs] using hB
  · simpa [compression, zeroExtension, hx] using hB

/-- L2 class of the original zero-extension compressed whole-line translation. -/
def shiftHeadL2 (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (s : ℝ) : WindowL2 a :=
  (compressed_head_memLp a N v s).toLp
    (compression a s (profile a (Finset.range (N + 1)) v))

private lemma compressed_pairing_eq_window (a s : ℝ) (f g : ℝ → ℂ) :
    pairing a s f g = ∫ x in window a, f x * compression a s g x := by
  have he : (fun x => f x * compression a s g x) =
      (window a).indicator (fun x => f x * compression a s g x) := by
    funext x
    by_cases hx : x ∈ window a
    · simp [hx]
    · simp [compression, zeroExtension, hx]
  unfold pairing
  calc
    _ = ∫ x : ℝ, (window a).indicator
        (fun x => f x * compression a s g x) x := congrArg (integral volume) he
    _ = _ := MeasureTheory.integral_indicator
      (s := window a) (μ := volume) (show MeasurableSet (window a) from measurableSet_Ioc)

private lemma shiftHeadL2_coefficient (a : ℝ) (N : ℕ) (v : ℕ → ℂ)
    (s : ℝ) (m : ℕ) :
    inner ℂ (modeL2 a m) (shiftHeadL2 a N v s) = shiftCoefficient a N v s m := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in window a, (mode a m x : ℂ) *
        compression a s (profile a (Finset.range (N + 1)) v) x := by
      apply integral_congr_ae
      filter_upwards [(mode_memLp a m).coeFn_toLp,
        (compressed_head_memLp a N v s).coeFn_toLp] with x hm hs
      change modeL2 a m x = (mode a m x : ℂ) at hm
      change shiftHeadL2 a N v s x =
        compression a s (profile a (Finset.range (N + 1)) v) x at hs
      rw [hm, hs]
      simp [RCLike.inner_apply', mul_comm]
    _ = _ := (compressed_pairing_eq_window a s _ _).symm

/-- Both physical shifts are retained in the actual L2 finite prime action. -/
def primeHeadL2 (a : ℝ) (N : ℕ) (v : ℕ → ℂ) : WindowL2 a :=
  ∑ r ∈ Finset.Icc 1 (primeCutoff a), (primeWeight r : ℂ) •
    (shiftHeadL2 a N v (Real.log (r : ℝ)) +
      shiftHeadL2 a N v (-Real.log (r : ℝ)))

lemma primeHeadL2_ae_action (a : ℝ) (N : ℕ) (v : ℕ → ℂ) :
    (fun x => primeHeadL2 a N v x) =ᵐ[windowMeasure a]
      primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) := by
  have hsum := Lp.coeFn_fun_finsetSum (Finset.Icc 1 (primeCutoff a))
    (fun r => (primeWeight r : ℂ) •
      (shiftHeadL2 a N v (Real.log (r : ℝ)) +
        shiftHeadL2 a N v (-Real.log (r : ℝ))))
  have hterm (r : ℕ) :
      (fun x => ((primeWeight r : ℂ) •
        (shiftHeadL2 a N v (Real.log (r : ℝ)) +
          shiftHeadL2 a N v (-Real.log (r : ℝ)))) x) =ᵐ[windowMeasure a]
      (fun x => (primeWeight r : ℂ) *
        (compression a (Real.log (r : ℝ)) (profile a (Finset.range (N + 1)) v) x +
          compression a (-Real.log (r : ℝ)) (profile a (Finset.range (N + 1)) v) x)) := by
    filter_upwards [Lp.coeFn_smul (primeWeight r : ℂ)
        (shiftHeadL2 a N v (Real.log (r : ℝ)) + shiftHeadL2 a N v (-Real.log (r : ℝ))),
      Lp.coeFn_add (shiftHeadL2 a N v (Real.log (r : ℝ)))
        (shiftHeadL2 a N v (-Real.log (r : ℝ))),
      (compressed_head_memLp a N v (Real.log (r : ℝ))).coeFn_toLp,
      (compressed_head_memLp a N v (-Real.log (r : ℝ))).coeFn_toLp]
      with x hsm ha hp hm
    change shiftHeadL2 a N v (Real.log (r : ℝ)) x =
      compression a (Real.log (r : ℝ)) (profile a (Finset.range (N + 1)) v) x at hp
    change shiftHeadL2 a N v (-Real.log (r : ℝ)) x =
      compression a (-Real.log (r : ℝ)) (profile a (Finset.range (N + 1)) v) x at hm
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hsm ha
    rw [ha, hp, hm] at hsm
    exact hsm
  filter_upwards [hsum, ae_all_iff.mpr hterm] with x hx hterms
  change ((∑ r ∈ Finset.Icc 1 (primeCutoff a), (primeWeight r : ℂ) •
    (shiftHeadL2 a N v (Real.log (r : ℝ)) +
      shiftHeadL2 a N v (-Real.log (r : ℝ)))) : WindowL2 a) x = _
  rw [hx]
  apply Finset.sum_congr rfl
  intro r _
  exact hterms r

private lemma primeHeadL2_coefficient (a : ℝ) (N : ℕ) (v : ℕ → ℂ) (m : ℕ) :
    inner ℂ (modeL2 a m) (primeHeadL2 a N v) = primeCoefficient a N v m := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in window a, (mode a m x : ℂ) *
        primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x := by
      apply integral_congr_ae
      filter_upwards [(mode_memLp a m).coeFn_toLp, primeHeadL2_ae_action a N v]
        with x hm hp
      change modeL2 a m x = (mode a m x : ℂ) at hm
      rw [hm, hp]
      simp [RCLike.inner_apply', mul_comm]
    _ = _ := by
      have he : (fun x => (mode a m x : ℂ) *
          primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x) =
          (window a).indicator (fun x => (mode a m x : ℂ) *
            primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x) := by
        funext x
        by_cases hx : x ∈ window a
        · simp [hx]
        · simp [primeAction, compression, zeroExtension, hx]
      unfold primeCoefficient
      calc
        _ = ∫ x : ℝ, (window a).indicator (fun x => (mode a m x : ℂ) *
            primeAction a (primeCutoff a) (profile a (Finset.range (N + 1)) v) x) x :=
          (MeasureTheory.integral_indicator (s := window a) (μ := volume)
            (show MeasurableSet (window a) from measurableSet_Ioc)).symm
        _ = _ := congrArg (integral volume) he.symm


/-! A concrete infinite-dimensional exterior projection, with no completeness
assumption about all AE-even functions. Its basis is constructed in its closed
span, rather than passed into the estimate as an input supplier. -/
def exteriorSpace (a : ℝ) (M : ℕ) : Submodule ℂ (WindowL2 a) :=
  (Submodule.span ℂ (Set.range (fun j : ℕ => modeL2 a (M + j + 1)))).topologicalClosure

private instance exteriorSpace_complete (a : ℝ) (M : ℕ) :
    CompleteSpace (exteriorSpace a M) := by
  exact (Submodule.isClosed_topologicalClosure
    (Submodule.span ℂ (Set.range (fun j : ℕ => modeL2 a (M + j + 1))))).isComplete.completeSpace_coe

private def exteriorMode (a : ℝ) (M j : ℕ) : exteriorSpace a M :=
  ⟨modeL2 a (M + j + 1), Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self j))⟩

private lemma exteriorMode_orthonormal (a : ℝ) (ha : 0 < a) (M : ℕ) :
    Orthonormal ℂ (exteriorMode a M) := by
  exact ((modes_orthonormal a ha).comp (fun j : ℕ => M + j + 1) (by
    intro i j hij
    change M + i + 1 = M + j + 1 at hij
    omega)).codRestrict (exteriorSpace a M)
      (fun j => (exteriorMode a M j).property)

private lemma exteriorMode_orthogonal_eq_bot (a : ℝ) (M : ℕ) :
    (Submodule.span ℂ (Set.range (exteriorMode a M)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  apply (Submodule.mem_bot ℂ).mpr
  have hi (j : ℕ) : inner ℂ (exteriorMode a M j) y = 0 :=
    (Submodule.mem_orthogonal _ _).mp hy _
      (Submodule.subset_span (Set.mem_range_self j))
  have hinc : exteriorSpace a M ≤ (ℂ ∙ (y : WindowL2 a))ᗮ := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨j, rfl⟩
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_eq_zero_symm]
      exact hi j
    · exact Submodule.isClosed_orthogonal _
  have hz : inner ℂ (y : WindowL2 a) (y : WindowL2 a) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hinc y.property)
  apply Subtype.ext
  exact inner_self_eq_zero.mp hz

private def exteriorBasis (a : ℝ) (ha : 0 < a) (M : ℕ) :
    HilbertBasis ℕ ℂ (exteriorSpace a M) :=
  HilbertBasis.mkOfOrthogonalEqBot (exteriorMode_orthonormal a ha M)
    (exteriorMode_orthogonal_eq_bot a M)

private lemma exteriorBasis_apply (a : ℝ) (ha : 0 < a) (M j : ℕ) :
    exteriorBasis a ha M j = exteriorMode a M j := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (exteriorMode_orthonormal a ha M) (exteriorMode_orthogonal_eq_bot a M)) j

/-- Actual orthogonal projection on original dx-L2, with infinitely many
exterior modes. This definition does not use a terminal upper mode cutoff. -/
def exteriorProjection (a : ℝ) (M : ℕ) : WindowL2 a →L[ℂ] exteriorSpace a M :=
  (exteriorSpace a M).orthogonalProjectionOnto

private lemma exteriorProjection_parseval (a : ℝ) (ha : 0 < a)
    (M : ℕ) (F : WindowL2 a) :
    ‖exteriorProjection a M F‖ ^ 2 =
      ∑' j : ℕ, ‖inner ℂ (modeL2 a (M + j + 1)) F‖ ^ 2 := by
  let b := exteriorBasis a ha M
  let y := exteriorProjection a M F
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
    (by norm_num : 0 < (2 : ENNReal).toReal) (b.repr y)
  have hnorm : ‖y‖ ^ 2 = ∑' j : ℕ, ‖b.repr y j‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h
  rw [hnorm]
  apply tsum_congr
  intro j
  rw [b.repr_apply_apply]
  change ‖inner ℂ (exteriorBasis a ha M j) (exteriorProjection a M F)‖ ^ 2 = _
  rw [exteriorBasis_apply]
  change ‖inner ℂ (exteriorMode a M j)
    ((exteriorSpace a M).orthogonalProjectionOnto F)‖ ^ 2 = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rfl

/-- An actual L2 exterior projection estimate. It remains a closed-cosine-span
projection until the separate AE-even completeness obligation is established. -/
theorem shift_projection_bound (a : ℝ) (ha : 0 < a)
    (N M : ℕ) (hNM : N < M) (v : ℕ → ℂ) (s : ℝ) :
    ‖exteriorProjection a M (shiftHeadL2 a N v s)‖ ^ 2 ≤
      ((N : ℝ) + 1) / (Real.pi ^ 2 * ((M : ℝ) - (N : ℝ))) *
        ‖headL2 a N v‖ ^ 2 := by
  rw [exteriorProjection_parseval a ha, headL2_mass a ha]
  simp_rw [shiftHeadL2_coefficient]
  exact (shift_complete_tail a ha N M hNM v s).2

/-- The exact prime two-cutoff allowance for the concrete physical cosine-tail
projection. This is not a theorem that the full signed Weil form is positive. -/
theorem prime_projection_bound (a : ℝ) (ha : 0 < a)
    (N M : ℕ) (hNM : N < M) (v : ℕ → ℂ) :
    ‖exteriorProjection a M (primeHeadL2 a N v)‖ ^ 2 ≤
      4 * primeMass a ^ 2 * ((N : ℝ) + 1) /
        (Real.pi ^ 2 * ((M : ℝ) - (N : ℝ))) * ‖headL2 a N v‖ ^ 2 := by
  rw [exteriorProjection_parseval a ha, headL2_mass a ha]
  simp_rw [primeHeadL2_coefficient]
  exact (prime_complete_tail a ha N M hNM v).2

end PhysicalCosineTailProjection
