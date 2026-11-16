/- GID: D5/S3/Quantum/Analysis/ContinuousCutoffCentralizer
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ContinuousCutoffCentralizer
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.VonNeumannAlgebra.Basic]
   utility: none
   digest: Range supports and continuous cutoffs for vector-functional overlap optimization. -/
import Mathlib.Analysis.VonNeumannAlgebra.Basic import Mathlib.Analysis.InnerProductSpace.Projection.Submodule import Mathlib.Analysis.InnerProductSpace.Positive import Mathlib.Analysis.InnerProductSpace.StarOrder import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range import Mathlib.Analysis.Calculus.LocalExtr.Basic import Mathlib.Tactic
/- admission_basis: escape-witness escape_witness: optimal_implies_compressed_centralization Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/29713 compressed_centralization_implies_optimal: proof_shape: content; consumer: all_overlap_optimal_iff_compressed_centralizes. optimal_cutoff_annihilation: proof_shape: content; consumer: optimal_threshold_cross. optimal_implies_compressed_centralization: proof_shape: content; consumer: all_overlap_optimal_iff_compressed_centralizes. all_overlap_optimal_iff_compressed_centralizes: proof_shape: content. Private support, cutoff, coefficient and approximation helpers are consumed by these proofs. -/
/-! Closed-range supports and continuous functional calculus on arbitrary complex Hilbert spaces. -/
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
open ContinuousLinearMap Filter
namespace D5.S3.Quantum.Analysis.ContinuousCutoffCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H
/-- The support is the orthogonal projection onto the closed operator range. -/
def rangeSupport (T : Op) : Op := T.range.topologicalClosure.starProjection
private theorem rangeSupport_isProjection (T : Op) : IsStarProjection (rangeSupport T) := isStarProjection_starProjection
private theorem rangeSupport_range (T : Op) : (rangeSupport T).range = T.range.topologicalClosure :=
  Submodule.range_starProjection _
private theorem rangeSupport_mem (N : VonNeumannAlgebra H) {T : Op} (hT : T ∈ N) : rangeSupport T ∈ N := by
  rw [VonNeumannAlgebra.IsStarProjection.mem_iff (rangeSupport_isProjection T), rangeSupport_range]
  intro Y hY
  change ∀ x ∈ T.range.topologicalClosure, Y x ∈ T.range.topologicalClosure
  intro x hx
  have hclosed : IsClosed {x : H | Y x ∈ T.range.topologicalClosure} := T.range.isClosed_topologicalClosure.preimage Y.continuous
  apply hclosed.closure_subset_iff.mpr ?_ hx
  rintro x ⟨z, rfl⟩
  apply T.range.le_topologicalClosure
  refine ⟨Y z, ?_⟩
  exact congrArg (fun A : Op => A z) ((N.mem_commutant_iff.mp hY) T hT)
private theorem rangeSupport_mul (T : Op) : rangeSupport T * T = T := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (T.range.le_topologicalClosure ⟨x, rfl⟩)
private theorem rangeSupport_ker {T : Op} (hT : IsSelfAdjoint T) : (rangeSupport T).ker = T.ker := by
  rw [rangeSupport, Submodule.ker_starProjection, Submodule.orthogonal_closure, ContinuousLinearMap.orthogonal_range]
  simp only [← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
private theorem mul_rangeSupport {T : Op} (hT : IsSelfAdjoint T) : T * rangeSupport T = T := by
  have he := congrArg star (rangeSupport_mul T)
  simpa only [star_mul, hT.star_eq, (rangeSupport_isProjection T).isSelfAdjoint.star_eq] using he
private theorem rangeSupport_commute {T Y : Op} (hT : IsSelfAdjoint T) (h : Commute T Y) : Commute (rangeSupport T) Y := by
  rw [commute_iff_eq]
  apply ContinuousLinearMap.coe_injective
  change Commute (rangeSupport T).toLinearMap Y.toLinearMap
  rw [LinearMap.IsIdempotentElem.commute_iff (rangeSupport_isProjection T).isIdempotentElem.toLinearMap, rangeSupport_range, rangeSupport_ker hT]
  constructor
  · change ∀ x ∈ T.range.topologicalClosure, Y x ∈ T.range.topologicalClosure
    intro x hx
    apply (T.range.isClosed_topologicalClosure.preimage Y.continuous).closure_subset_iff.mpr ?_ hx
    rintro x ⟨z, rfl⟩
    apply T.range.le_topologicalClosure
    exact ⟨Y z, congrArg (fun A : Op => A z) h.eq⟩
  · change ∀ x, T x = 0 → T (Y x) = 0
    intro x hx
    calc
      T (Y x) = Y (T x) := congrArg (fun A : Op => A x) h.eq
      _ = 0 := by rw [hx, map_zero]
private theorem support_convergence {T : Op} (hT : IsSelfAdjoint T) (A : ℕ → Op) (hbound : ∀ n, ‖A n‖ ≤ 1) (hker : ∀ n x, T x = 0 → A n x = 0) (herror : Tendsto (fun n => ‖(A n - 1) * T‖) atTop (𝓝 0)) (x : H) : Tendsto (fun n => A n x) atTop (𝓝 (rangeSupport T x)) := by
  have hb : ∃ c : ℝ, ∀ n, ‖A n‖ ≤ c := ⟨1, hbound⟩
  have hequi : Equicontinuous (fun n x => A n x) := ((NormedSpace.equicontinuous_TFAE A).out 6 2).mp hb
  have hclosed : IsClosed {x : H | Tendsto (fun n => A n x) atTop (𝓝 x)} := hequi.isClosed_setOfPred_tendsto continuous_id
  have hrange : ∀ x ∈ T.range, Tendsto (fun n => A n x) atTop (𝓝 x) := by
    rintro _ ⟨y, rfl⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using herror.mul_const ‖y‖)
    exact ((A n - 1) * T).le_opNorm y
  have hmem : rangeSupport T x ∈ closure (T.range : Set H) := by
    rw [← Submodule.topologicalClosure_coe]
    exact Submodule.starProjection_apply_mem T.range.topologicalClosure x
  have hlim : Tendsto (fun n => A n (rangeSupport T x)) atTop (𝓝 (rangeSupport T x)) := hclosed.closure_subset_iff.mpr hrange hmem
  have hk : T (x - rangeSupport T x) = 0 := by
    rw [map_sub]
    change T x - (T * rangeSupport T) x = 0
    rw [mul_rangeSupport hT, sub_self]
  have heq (n : ℕ) : A n x = A n (rangeSupport T x) := by
    have hz := hker n (x - rangeSupport T x) hk
    simpa only [map_sub, sub_eq_zero] using hz
  simpa only [heq] using hlim
private def supportRamp (n : ℕ) (x : ℝ) : ℝ := ((n : ℝ) + 1) * x / max 1 (((n : ℝ) + 1) * x)
private theorem supportRamp_continuous (n : ℕ) : Continuous (supportRamp n) := by
  unfold supportRamp
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
private theorem supportRamp_bounds (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ supportRamp n x ∧ supportRamp n x ≤ 1 ∧ 0 ≤ x * (1 - supportRamp n x) ∧ x * (1 - supportRamp n x) ≤ 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd : 0 < max 1 (((n : ℝ) + 1) * x) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h₀ : 0 ≤ supportRamp n x := div_nonneg (mul_nonneg hn.le hx) hd.le
  have h₁ : supportRamp n x ≤ 1 := (div_le_one hd).mpr (le_max_right _ _)
  refine ⟨h₀, h₁, mul_nonneg hx (sub_nonneg.mpr h₁), ?_⟩
  by_cases h : ((n : ℝ) + 1) * x ≤ 1
  · have hxbound : x ≤ 1 / ((n : ℝ) + 1) := (le_div_iff₀ hn).mpr (by nlinarith)
    exact (mul_le_of_le_one_right hx (by linarith)).trans hxbound
  · have heq : supportRamp n x = 1 := by
      unfold supportRamp
      rw [max_eq_right (le_of_not_ge h), div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_of_not_ge h)))]
    rw [heq, sub_self, mul_zero]
    positivity
private def supportApprox (T : Op) (n : ℕ) : Op := cfc (supportRamp n) T
private theorem supportApprox_factor {T : Op} (hT : IsSelfAdjoint T) (n : ℕ) : supportApprox T n = cfc (fun x : ℝ => ((n : ℝ) + 1) / max 1 (((n : ℝ) + 1) * x)) T * T := by
  have hq : Continuous (fun x : ℝ => ((n : ℝ) + 1) / max 1 (((n : ℝ) + 1) * x)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  calc
    _ = cfc (fun x : ℝ => (((n : ℝ) + 1) / max 1 (((n : ℝ) + 1) * x)) * x) T := by
      apply cfc_congr
      intro x hx
      dsimp [supportRamp]
      ring
    _ = _ := by simpa only [cfc_id' ℝ T hT] using (cfc_mul (fun x : ℝ => ((n : ℝ) + 1) / max 1 (((n : ℝ) + 1) * x)) (fun x : ℝ => x) T hq.continuousOn continuousOn_id)
private theorem supportApprox_tendsto {T : Op} (hT : 0 ≤ T) (x : H) : Tendsto (fun n => supportApprox T n x) atTop (𝓝 (rangeSupport T x)) := by
  have hs := IsSelfAdjoint.of_nonneg hT
  apply support_convergence hs (supportApprox T)
  · intro n
    apply norm_cfc_le zero_le_one
    intro u hu
    have hb := supportRamp_bounds n (spectrum_nonneg_of_nonneg hT hu)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1
  · intro n y hy
    rw [supportApprox_factor hs n]
    change cfc (fun x : ℝ => ((n : ℝ) + 1) / max 1 (((n : ℝ) + 1) * x)) T (T y) = 0
    rw [hy, map_zero]
  · have herr (n : ℕ) : ‖(supportApprox T n - 1) * T‖ ≤ 1 / ((n : ℝ) + 1) := by
      have heq : (supportApprox T n - 1) * T = cfc (fun u : ℝ => (supportRamp n u - 1) * u) T := by
        have he := cfc_mul (fun u : ℝ => supportRamp n u - 1) (fun u : ℝ => u) T ((supportRamp_continuous n).sub continuous_const).continuousOn continuousOn_id
        rw [cfc_sub (supportRamp n) (fun _ : ℝ => 1) T (supportRamp_continuous n).continuousOn continuousOn_const, cfc_const_one ℝ T hs, cfc_id' ℝ T hs] at he
        exact he.symm
      rw [heq]
      apply norm_cfc_le (by positivity)
      intro u hu
      have hb := supportRamp_bounds n (spectrum_nonneg_of_nonneg hT hu)
      rw [Real.norm_eq_abs]
      have heq : (supportRamp n u - 1) * u = -(u * (1 - supportRamp n u)) := by ring
      rw [heq, abs_neg, abs_of_nonneg hb.2.2.1]
      exact hb.2.2.2
    exact squeeze_zero (fun _ => norm_nonneg _) herr (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
private theorem positive_apply_eq_zero {X : Op} (hX : 0 ≤ X) {x : H} (hx : inner ℂ x (X x) = 0) : X x = 0 := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  change inner ℂ x (B.adjoint (B x)) = 0 at hx
  have hB : B x = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [ContinuousLinearMap.adjoint_inner_right] using hx
  change B.adjoint (B x) = 0
  rw [hB, map_zero]
private theorem kernel_antitone {X A : Op} (hX : 0 ≤ X) (hXA : X ≤ A) {x : H} (hx : A x = 0) : X x = 0 := by
  apply positive_apply_eq_zero hX
  apply le_antisymm
  · have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hXA)).inner_nonneg_right x
    simpa only [sub_apply, hx, zero_sub, inner_neg_right, neg_nonneg] using h
  · exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hX).inner_nonneg_right x
private theorem interior_product_selfAdjoint {C : Op} (hC : IsSelfAdjoint C) : IsSelfAdjoint (C * (1 - C)) := by
  change star (C * (1 - C)) = C * (1 - C)
  rw [star_mul, star_sub, star_one, hC.star_eq]
  noncomm_ring
private theorem endpoint_kernel_decomposition {C : Op} {x : H} (hx : (C * (1 - C)) x = 0) : (1 - C) (C x) = 0 ∧ C ((1 - C) x) = 0 ∧ C x + (1 - C) x = x := by
  have hc : Commute C (1 - C) := (Commute.one_right C).sub_right (Commute.refl C)
  refine ⟨?_, hx, ?_⟩
  · exact (congrArg (fun A : Op => A x) hc.eq).symm.trans hx
  · simp only [sub_apply, one_apply_eq_self, add_sub_cancel]
private theorem feasible_annihilates_endpoints {C X : Op} {t : ℝ} (hX : 0 ≤ X) (hXC : X ≤ C) (hXt : X ≤ t • (1 - C)) {x : H} (hx : (C * (1 - C)) x = 0) : X x = 0 := by
  obtain ⟨h₁, h₂, hsum⟩ := endpoint_kernel_decomposition hx
  have hleft : X (C x) = 0 := kernel_antitone hX hXt (by simp only [smul_apply, h₁, smul_zero])
  have hright : X ((1 - C) x) = 0 := kernel_antitone hX hXC h₂
  rw [← hsum, map_add, hleft, hright, add_zero]
/-- The interior support retains all accumulation at both endpoints. -/
def interiorSupport (C : Op) : Op := rangeSupport (C * (1 - C))
private theorem feasible_compression {C X : Op} {t : ℝ} (hC : IsSelfAdjoint C) (hX : 0 ≤ X) (hXC : X ≤ C) (hXt : X ≤ t • (1 - C)) : X = interiorSupport C * X * interiorSupport C := by
  let P := interiorSupport C
  have hP : IsStarProjection P := rangeSupport_isProjection (C * (1 - C))
  have hright : X * P = X := by
    ext x
    change X (P x) = X x
    have hz : (C * (1 - C)) (x - P x) = 0 := by
      have hk : x - P x ∈ (rangeSupport (C * (1 - C))).ker := by
        change P (x - P x) = 0
        simp only [map_sub, show P (P x) = P x from congrArg (fun A : Op => A x) hP.isIdempotentElem.eq, sub_self]
      rwa [rangeSupport_ker (interior_product_selfAdjoint hC)] at hk
    have hh := feasible_annihilates_endpoints hX hXC hXt hz
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hh)).symm
  have hleft : P * X = X := by
    have hh := congrArg star hright
    simpa only [star_mul, (IsSelfAdjoint.of_nonneg hX).star_eq, hP.isSelfAdjoint.star_eq] using hh
  rw [hleft, hright]
/-- The continuous spectral overlap, with no measurable functional calculus. -/
def overlap (C : Op) (t : ℝ) : Op := cfc (fun x : ℝ => min x (t * (1 - x))) C
/-- Every feasible operator is quantified in the ambient concrete algebra. -/
def Feasible (N : VonNeumannAlgebra H) (C X : Op) (t : ℝ) : Prop := X ∈ N ∧ 0 ≤ X ∧ X ≤ C ∧ X ≤ t • (1 - C)
/-- The fixed vector coefficient, including the zero vector. -/
def vectorValue (Ω : H) (T : Op) : ℝ := (inner ℂ Ω (T Ω)).re
/-- Simultaneous optimality for every strictly positive threshold. -/
def AllOverlapOptimal (N : VonNeumannAlgebra H) (C : Op) (Ω : H) : Prop := ∀ t : ℝ, 0 < t → Feasible N C (overlap C t) t ∧ ∀ X : Op, Feasible N C X t → vectorValue Ω X ≤ vectorValue Ω (overlap C t)
/-- Centralization is imposed only on the actual interior corner. -/
def CompressedCentralizes (N : VonNeumannAlgebra H) (C : Op) (Ω : H) : Prop :=
  let P := interiorSupport C
  ∀ Y : Op, Y ∈ N → inner ℂ Ω ((P * C * P * (P * Y * P)) Ω) = inner ℂ Ω (((P * Y * P) * (P * C * P)) Ω)
private theorem cfc_mem_algebra (N : VonNeumannAlgebra H) {C : Op} (hC : C ∈ N) (f : ℝ → ℝ) : cfc f C ∈ N := by
  rw [← N.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro Y hY
  have hc : Commute C Y := (VonNeumannAlgebra.mem_commutant_iff.mp hY) C hC
  exact (hc.cfc_real f).symm.eq
private theorem spectrum_unit_interval {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) {x : ℝ} (hx : x ∈ spectrum ℝ C) : 0 ≤ x ∧ x ≤ 1 := by
  refine ⟨spectrum_nonneg_of_nonneg hC₀ hx, ?_⟩
  apply (le_algebraMap_iff_spectrum_le (R := ℝ) (IsSelfAdjoint.of_nonneg hC₀)).mp (by simpa using hC₁) x hx
private theorem complement_cfc {C : Op} (hC : IsSelfAdjoint C) (t : ℝ) : cfc (fun x : ℝ => t * (1 - x)) C = t • (1 - C) := by rw [cfc_const_mul t (fun x : ℝ => 1 - x) C (by fun_prop), cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) C continuousOn_const continuousOn_id, cfc_const_one ℝ C hC, cfc_id' ℝ C hC]
private theorem overlap_feasible (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) {t : ℝ} (ht : 0 ≤ t) : Feasible N C (overlap C t) t := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  refine ⟨cfc_mem_algebra N hCN _, ?_, ?_, ?_⟩
  · apply cfc_nonneg
    intro x hx
    have hi := spectrum_unit_interval hC₀ hC₁ hx
    exact le_min hi.1 (mul_nonneg ht (sub_nonneg.mpr hi.2))
  · change cfc _ C ≤ C
    conv_rhs => rw [← cfc_id' ℝ C hs]
    apply (cfc_le_iff _ _ C (by fun_prop) continuousOn_id hs).mpr
    intro x hx
    exact min_le_left _ _
  · rw [← complement_cfc hs t]
    apply (cfc_le_iff _ _ C (by fun_prop) (by fun_prop) hs).mpr
    intro x hx
    exact min_le_right _ _
private theorem interiorSupport_properties (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC : IsSelfAdjoint C) : IsStarProjection (interiorSupport C) ∧ interiorSupport C ∈ N ∧ Commute (interiorSupport C) C := by
  refine ⟨rangeSupport_isProjection _, rangeSupport_mem N (N.mul_mem hCN (N.sub_mem N.one_mem hCN)), ?_⟩
  apply rangeSupport_commute (interior_product_selfAdjoint hC)
  exact (Commute.refl C).mul_left ((Commute.one_left C).sub_left (Commute.refl C))
private theorem interior_product_nonneg {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) : 0 ≤ C * (1 - C) := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have heq : cfc (fun x : ℝ => x * (1 - x)) C = C * (1 - C) := by rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => 1 - x) C continuousOn_id (by fun_prop), cfc_id' ℝ C hs, cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) C continuousOn_const continuousOn_id, cfc_const_one ℝ C hs, cfc_id' ℝ C hs]
  rw [← heq]
  apply cfc_nonneg
  intro x hx
  have hi := spectrum_unit_interval hC₀ hC₁ hx
  exact mul_nonneg hi.1 (sub_nonneg.mpr hi.2)
private def thresholdPart (C : Op) (s : ℝ) : Op := cfc (fun x : ℝ => max 0 (x - s)) C
private def thresholdSupport (C : Op) (s : ℝ) : Op := rangeSupport (thresholdPart C s)
private theorem thresholdPart_nonneg (C : Op) (s : ℝ) : 0 ≤ thresholdPart C s := cfc_nonneg (fun _ _ => le_max_left _ _)
private theorem thresholdSupport_properties (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (s : ℝ) : IsStarProjection (thresholdSupport C s) ∧ thresholdSupport C s ∈ N ∧ Commute (thresholdSupport C s) C := by
  refine ⟨rangeSupport_isProjection _, rangeSupport_mem N (cfc_mem_algebra N hCN _), ?_⟩
  apply rangeSupport_commute (IsSelfAdjoint.of_nonneg (thresholdPart_nonneg C s))
  exact (Commute.refl C).cfc_real _
private def coeff (Ω : H) (A : Op) : ℂ := inner ℂ Ω (A Ω)
private theorem coeff_star (Ω : H) (A : Op) : coeff Ω (star A) = star (coeff Ω A) := by
  change inner ℂ Ω (A.adjoint Ω) = star (inner ℂ Ω (A Ω))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (A Ω) Ω).symm
private def centralizer (N : VonNeumannAlgebra H) (Ω : H) : StarSubalgebra ℂ Op where
  carrier := {A | A ∈ N ∧ ∀ Y ∈ N, coeff Ω (A * Y) = coeff Ω (Y * A)}
  zero_mem' := ⟨N.zero_mem, by simp⟩
  one_mem' := ⟨N.one_mem, by simp⟩
  add_mem' := by
    intro A B hA hB
    refine ⟨N.add_mem hA.1 hB.1, ?_⟩
    intro Y hY
    simp only [add_mul, mul_add, coeff, add_apply, inner_add_right]
    exact congrArg₂ (· + ·) (hA.2 Y hY) (hB.2 Y hY)
  mul_mem' := by
    intro A B hA hB
    refine ⟨N.mul_mem hA.1 hB.1, ?_⟩
    intro Y hY
    calc
      coeff Ω (A * B * Y) = coeff Ω ((B * Y) * A) := by rw [mul_assoc, hA.2 _ (N.mul_mem hB.1 hY)]
      _ = coeff Ω ((Y * A) * B) := by rw [mul_assoc, hB.2 _ (N.mul_mem hY hA.1)]
      _ = coeff Ω (Y * (A * B)) := by rw [mul_assoc]
  algebraMap_mem' := by
    intro z
    refine ⟨N.toStarSubalgebra.algebraMap_mem z, ?_⟩
    intro Y hY
    rw [Algebra.commutes z Y]
  star_mem' := by
    intro A hA
    refine ⟨star_mem hA.1, ?_⟩
    intro Y hY
    have he := congrArg star (hA.2 (star Y) (star_mem hY))
    simpa only [← coeff_star, star_mul, star_star] using he.symm
private instance centralizer_closed (N : VonNeumannAlgebra H) (Ω : H) : IsClosed ((centralizer N Ω : StarSubalgebra ℂ Op) : Set Op) := by
  have hN : IsClosed (N : Set Op) := by
    rw [← N.centralizer_centralizer]
    exact Set.isClosed_centralizer _
  have hc : IsClosed {A : Op | ∀ Y ∈ N, coeff Ω (A * Y) = coeff Ω (Y * A)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro Y
    apply isClosed_iInter
    intro hY
    exact isClosed_eq (by unfold coeff; fun_prop) (by unfold coeff; fun_prop)
  exact hN.inter hc
private theorem centralizer_strong_closed (N : VonNeumannAlgebra H) (Ω : H) (A : ℕ → Op) (B : Op) (hB : B ∈ N) (hA : ∀ n, A n ∈ centralizer N Ω) (hlim : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (B x))) : B ∈ centralizer N Ω := by
  refine ⟨hB, ?_⟩
  intro Y hY
  have hleft : Tendsto (fun n => coeff Ω (A n * Y)) atTop (𝓝 (coeff Ω (B * Y))) := tendsto_const_nhds.inner (hlim (Y Ω))
  have hright : Tendsto (fun n => coeff Ω (Y * A n)) atTop (𝓝 (coeff Ω (Y * B))) := by exact tendsto_const_nhds.inner (Y.continuous.tendsto (B Ω) |>.comp (hlim Ω))
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => ((hA n).2 Y hY).symm)))
private theorem compressed_coefficients (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC : IsSelfAdjoint C) (Ω : H) : CompressedCentralizes N C Ω ↔ C ∈ centralizer N (interiorSupport C Ω) := by
  let P := interiorSupport C
  obtain ⟨hP, hPN, hPC⟩ := interiorSupport_properties N hCN hC
  have hP' : IsStarProjection P := hP
  have hPC' : Commute P C := hPC
  have hPm : P * P = P := hP'.isIdempotentElem.eq
  have hPCP : P * C * P = P * C := by
    calc
      _ = C * (P * P) := by rw [hPC'.eq, mul_assoc]
      _ = C * P := by rw [hPm]
      _ = P * C := hPC'.eq.symm
  have hcoeff_left (Y : Op) : inner ℂ Ω ((P * C * P * (P * Y * P)) Ω) = coeff (P Ω) (C * Y) := by
    have heq : P * C * P * (P * Y * P) = P * C * Y * P := by
      calc
        _ = (P * C) * (P * Y * P) := by rw [hPCP]
        _ = (P * C * P) * Y * P := by noncomm_ring
        _ = _ := by rw [hPCP]
    rw [heq]
    change inner ℂ Ω (P (C (Y (P Ω)))) = inner ℂ (P Ω) (C (Y (P Ω)))
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP'.isSelfAdjoint) _ _).symm
  have hcoeff_right (Y : Op) : inner ℂ Ω (((P * Y * P) * (P * C * P)) Ω) = coeff (P Ω) (Y * C) := by
    have heq : (P * Y * P) * (P * C * P) = P * Y * C * P := by
      calc
        _ = P * Y * (P * P) * C * P := by noncomm_ring
        _ = P * Y * P * C * P := by rw [hPm]
        _ = P * Y * (P * C * P) := by noncomm_ring
        _ = P * Y * (C * P) := by rw [hPCP, hPC'.eq]
        _ = _ := by noncomm_ring
    rw [heq]
    change inner ℂ Ω (P (Y (C (P Ω)))) = inner ℂ (P Ω) (Y (C (P Ω)))
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP'.isSelfAdjoint) _ _).symm
  constructor
  · intro h
    refine ⟨hCN, ?_⟩
    intro Y hY
    rw [← hcoeff_left Y, ← hcoeff_right Y]
    exact h Y hY
  · intro h Y hY
    change inner ℂ Ω ((P * C * P * (P * Y * P)) Ω) = inner ℂ Ω (((P * Y * P) * (P * C * P)) Ω)
    rw [hcoeff_left Y, hcoeff_right Y]
    exact h.2 Y hY
private theorem mul_support_zero {A T : Op} (h : A * T = 0) : A * rangeSupport T = 0 := by
  have hle : T.range.topologicalClosure ≤ A.ker := by
    apply T.range.topologicalClosure_minimal _ A.isClosed_ker
    rintro _ ⟨x, rfl⟩
    exact congrArg (fun B : Op => B x) h
  ext x
  exact hle (Submodule.starProjection_apply_mem T.range.topologicalClosure x)
private def thresholdNegative (C : Op) (s : ℝ) : Op := cfc (fun x : ℝ => max 0 (s - x)) C
private theorem threshold_parts_orthogonal (C : Op) (s : ℝ) : thresholdPart C s * thresholdNegative C s = 0 := by
  rw [thresholdPart, thresholdNegative, ← cfc_mul _ _ C (by fun_prop) (by fun_prop)]
  have heq : cfc (fun x : ℝ => max 0 (x - s) * max 0 (s - x)) C = cfc (fun _ : ℝ => 0) C := by
    apply cfc_congr
    intro x hx
    dsimp only
    by_cases hxs : x ≤ s
    · rw [max_eq_left (sub_nonpos.mpr hxs), zero_mul]
    · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge hxs)), mul_zero]
  rw [heq, cfc_const_zero]
private theorem threshold_negative_support_zero (C : Op) (s : ℝ) : thresholdNegative C s * thresholdSupport C s = 0 := by
  apply mul_support_zero
  have hc : Commute (thresholdNegative C s) (thresholdPart C s) := cfc_commute_cfc (fun x : ℝ => max 0 (s - x)) (fun x : ℝ => max 0 (x - s)) C
  rw [hc.eq]
  exact threshold_parts_orthogonal C s
private theorem threshold_centralizes (N : VonNeumannAlgebra H) {C : Op} (Ω : H) (hC : C ∈ centralizer N Ω) (s : ℝ) : thresholdSupport C s ∈ centralizer N Ω := by
  have hp : thresholdPart C s ∈ centralizer N Ω := cfc_mem (fun x : ℝ => max 0 (x - s)) hC
  apply centralizer_strong_closed N Ω (supportApprox (thresholdPart C s)) _ (thresholdSupport_properties N hC.1 s).2.1
  · intro n
    exact cfc_mem (supportRamp n) hp
  · intro x
    exact supportApprox_tendsto (thresholdPart_nonneg C s) x
private theorem overlap_slacks {C : Op} (hC : IsSelfAdjoint C) {t : ℝ} (ht : 0 < t) : C - overlap C t = (1 + t) • thresholdPart C (t / (1 + t)) ∧ t • (1 - C) - overlap C t = (1 + t) • thresholdNegative C (t / (1 + t)) := by
  have hd : 0 < 1 + t := by linarith
  have hr : (1 + t) * (t / (1 + t)) = t := mul_div_cancel₀ t (ne_of_gt hd)
  have hscalar (x : ℝ) : x - min x (t * (1 - x)) = (1 + t) * max 0 (x - t / (1 + t)) ∧ t * (1 - x) - min x (t * (1 - x)) = (1 + t) * max 0 (t / (1 + t) - x) := by
    by_cases h : x ≤ t / (1 + t)
    · have hm : x ≤ t * (1 - x) := by nlinarith
      rw [min_eq_left hm, max_eq_left (sub_nonpos.mpr h), max_eq_right (sub_nonneg.mpr h)]
      constructor <;> nlinarith
    · have hx : t / (1 + t) ≤ x := le_of_not_ge h
      have hm : t * (1 - x) ≤ x := by nlinarith
      rw [min_eq_right hm, max_eq_right (sub_nonneg.mpr hx), max_eq_left (sub_nonpos.mpr hx)]
      constructor <;> nlinarith
  constructor
  · have he := cfc_congr (a := C) (f := fun x : ℝ => x - min x (t * (1 - x))) (g := fun x : ℝ => (1 + t) * max 0 (x - t / (1 + t))) (fun x _ => (hscalar x).1)
    rw [cfc_sub (fun x : ℝ => x) (fun x : ℝ => min x (t * (1 - x))) C continuousOn_id (by fun_prop), cfc_id' ℝ C hC, cfc_const_mul (1 + t) (fun x : ℝ => max 0 (x - t / (1 + t))) C (by fun_prop)] at he
    exact he
  · have he := cfc_congr (a := C) (f := fun x : ℝ => t * (1 - x) - min x (t * (1 - x))) (g := fun x : ℝ => (1 + t) * max 0 (t / (1 + t) - x)) (fun x _ => (hscalar x).2)
    rw [cfc_sub _ _ C (by fun_prop) (by fun_prop), complement_cfc hC t, cfc_const_mul (1 + t) _ C (by fun_prop)] at he
    exact he
private theorem overlap_threshold_corners {C : Op} (hC : IsSelfAdjoint C) {t : ℝ} (ht : 0 < t) : let S := thresholdSupport C (t / (1 + t))
    (1 - S) * overlap C t * (1 - S) = (1 - S) * C * (1 - S) ∧ S * overlap C t * S = S * (t • (1 - C)) * S := by
  let s := t / (1 + t)
  let S := thresholdSupport C s
  have hplus : thresholdPart C s * S = thresholdPart C s := mul_rangeSupport (IsSelfAdjoint.of_nonneg (thresholdPart_nonneg C s))
  have hp : thresholdPart C s * (1 - S) = 0 := by rw [mul_sub, mul_one, hplus, sub_self]
  have hn : thresholdNegative C s * S = 0 := threshold_negative_support_zero C s
  obtain ⟨hslackE, hslackF⟩ := overlap_slacks hC ht
  change C - overlap C t = (1 + t) • thresholdPart C s at hslackE
  change t • (1 - C) - overlap C t = (1 + t) • thresholdNegative C s at hslackF
  have he := congrArg (fun A : Op => A * (1 - S)) hslackE
  have hf := congrArg (fun A : Op => A * S) hslackF
  have he' : C * (1 - S) = overlap C t * (1 - S) := sub_eq_zero.mp (by simpa only [sub_mul, smul_mul_assoc, hp, smul_zero] using he)
  have hf' : (t • (1 - C)) * S = overlap C t * S := sub_eq_zero.mp (by simpa only [sub_mul, smul_mul_assoc, hn, smul_zero] using hf)
  constructor
  · simpa only [mul_assoc] using congrArg (fun A : Op => (1 - S) * A) he'.symm
  · simpa only [mul_assoc] using congrArg (fun A : Op => S * A) hf'.symm
private theorem coeff_compression {P : Op} (hP : IsStarProjection P) (Ω : H) (X : Op) : coeff (P Ω) X = coeff Ω (P * X * P) := by
  change inner ℂ (P Ω) (X (P Ω)) = inner ℂ Ω (P (X (P Ω)))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint) _ _
private theorem coeff_real_mono (Ω : H) {A B : Op} (h : A ≤ B) : (coeff Ω A).re ≤ (coeff Ω B).re := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr h)).re_inner_nonneg_right Ω
  change 0 ≤ (inner ℂ Ω ((B - A) Ω)).re at hp
  rw [sub_apply, inner_sub_right, Complex.sub_re] at hp
  exact sub_nonneg.mp hp
private theorem centralizer_split (N : VonNeumannAlgebra H) (Ω : H) {S X : Op} (hS : IsStarProjection S) (hSN : S ∈ centralizer N Ω) (hX : X ∈ N) : coeff Ω X = coeff Ω ((1 - S) * X * (1 - S)) + coeff Ω (S * X * S) := by
  have hSX : coeff Ω (S * X) = coeff Ω (S * X * S) := by
    have he := hSN.2 (S * X) (N.mul_mem hSN.1 hX)
    simpa only [← mul_assoc, hS.isIdempotentElem.eq] using he
  have hXS : coeff Ω (X * S) = coeff Ω (S * X * S) := by
    have he := hSN.2 (X * S) (N.mul_mem hX hSN.1)
    simpa only [← mul_assoc, mul_assoc X S S, hS.isIdempotentElem.eq] using he.symm
  have heq : (1 - S) * X * (1 - S) = X - S * X - X * S + S * X * S := by noncomm_ring
  rw [heq]
  change coeff Ω X = _
  simp only [coeff, add_apply, sub_apply, inner_add_right, inner_sub_right] at hSX hXS ⊢
  linear_combination hSX + hXS

/-- Centralization on the interior corner makes the actual continuous overlap optimal against every feasible, possibly noncommuting, operator in the algebra. -/
theorem compressed_centralization_implies_optimal (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (Ω : H) (hc : CompressedCentralizes N C Ω) : AllOverlapOptimal N C Ω := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  let P := interiorSupport C
  let w := P Ω
  obtain ⟨hP, hPN, hPC⟩ := interiorSupport_properties N hCN hs
  have hc' : C ∈ centralizer N w := (compressed_coefficients N hCN hs Ω).mp hc
  intro t ht
  have hG := overlap_feasible N hCN hC₀ hC₁ ht.le
  refine ⟨hG, ?_⟩
  intro X hX
  let S := thresholdSupport C (t / (1 + t))
  have hS : IsStarProjection S := (thresholdSupport_properties N hCN _).1
  have hSc : S ∈ centralizer N w := threshold_centralizes N w hc' _
  have hXsplit := centralizer_split N w hS hSc hX.1
  have hGsplit := centralizer_split N w hS hSc hG.1
  have hcorner := overlap_threshold_corners hs ht
  have hupperE : (1 - S) * X * (1 - S) ≤ (1 - S) * overlap C t * (1 - S) := by
    rw [hcorner.1]
    simpa only [hS.one_sub.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate hX.2.2.1 (1 - S)
  have hupperF : S * X * S ≤ S * overlap C t * S := by
    rw [hcorner.2]
    simpa only [hS.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate hX.2.2.2 S
  have hbound := add_le_add (coeff_real_mono w hupperE) (coeff_real_mono w hupperF)
  rw [← Complex.add_re, ← hXsplit, ← Complex.add_re, ← hGsplit] at hbound
  have hXcomp : coeff w X = coeff Ω X := by rw [coeff_compression hP Ω X, ← feasible_compression hs hX.2.1 hX.2.2.1 hX.2.2.2]
  have hGcomp : coeff w (overlap C t) = coeff Ω (overlap C t) := by rw [coeff_compression hP Ω (overlap C t), ← feasible_compression hs hG.2.1 hG.2.2.1 hG.2.2.2]
  change (coeff Ω X).re ≤ (coeff Ω (overlap C t)).re
  rw [← hXcomp, ← hGcomp]
  exact hbound
private theorem star_cross_le (U V : Op) : star U * V + star V * U ≤ star U * U + star V * V := by
  have hp := star_mul_self_nonneg (U - V)
  have he : star (U - V) * (U - V) = (star U * U + star V * V) - (star U * V + star V * U) := by
    rw [star_sub]
    noncomm_ring
  exact sub_nonneg.mp (he ▸ hp)
private theorem cutoff_young {E F : Op} (hE : IsSelfAdjoint E) (hF : IsSelfAdjoint F) (Y : Op) {k : ℝ} (hk : 0 < k) (ε : ℝ) : ε • (E * Y * F + star (E * Y * F)) ≤ (k * ε ^ 2) • (E * E) + (‖Y‖ ^ 2 / k) • (F * F) := by
  have hnorm : star (Y * F) * (Y * F) ≤ ‖Y‖ ^ 2 • (F * F) := by simpa only [star_mul, hF.star_eq, mul_assoc, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] using star_left_conjugate_le_conjugate (CStarAlgebra.star_mul_le_algebraMap_norm_sq Y) F
  have hcross := star_cross_le ((k * ε) • E) (Y * F)
  have he : star ((k * ε) • E) * (Y * F) + star (Y * F) * ((k * ε) • E) = (k * ε) • (E * Y * F + star (E * Y * F)) := by simp only [star_smul, star_trivial, hE.star_eq, star_mul, smul_mul_assoc, mul_smul_comm, smul_add, mul_assoc]
  have he' : star ((k * ε) • E) * ((k * ε) • E) = ((k * ε) * (k * ε)) • (E * E) := by simp only [star_smul, star_trivial, hE.star_eq, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [he, he'] at hcross
  have htotal := hcross.trans (add_le_add le_rfl hnorm)
  apply (smul_le_smul_iff_of_pos_left hk).mp
  have hsq : (k * ε) * (k * ε) = k * (k * ε ^ 2) := by ring
  have hcancel : k * (‖Y‖ ^ 2 / k) = ‖Y‖ ^ 2 := mul_div_cancel₀ _ (ne_of_gt hk)
  simpa only [smul_add, smul_smul, hsq, hcancel] using htotal
private theorem cutoff_young_swapped {E F : Op} (hE : IsSelfAdjoint E) (hF : IsSelfAdjoint F) (Y : Op) {k : ℝ} (hk : 0 < k) (ε : ℝ) : ε • (E * Y * F + star (E * Y * F)) ≤ (‖Y‖ ^ 2 / k) • (E * E) + (k * ε ^ 2) • (F * F) := by
  have h := cutoff_young hF hE (star Y) hk ε
  have he : F * star Y * E + star (F * star Y * E) = E * Y * F + star (E * Y * F) := by
    simp only [star_mul, star_star, hE.star_eq, hF.star_eq]
    noncomm_ring
  simpa only [he, norm_star, add_comm] using h
private theorem quadratic_local_max_derivative {d w k : ℝ} (h : ∀ᶠ ε : ℝ in 𝓝 0, ε * d - k * ε ^ 2 * w ≤ 0) : d = 0 := by
  have hm : IsLocalMax (fun ε : ℝ => ε * d - k * ε ^ 2 * w) 0 := by simpa [IsLocalMax, IsMaxFilter] using h
  apply hm.hasDerivAt_eq_zero
  convert ((hasDerivAt_id (0 : ℝ)).mul_const d).sub ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul k).mul_const w) using 1 <;> try norm_num <;> rfl
private theorem cutoff_variation_feasible {C G E F Y : Op} {t u γE γF : ℝ} (hE : IsSelfAdjoint E) (hF : IsSelfAdjoint F) (hu : 0 < u) (hγE : 0 < γE) (hγF : 0 < γF) (hG : u • (E * E + F * F) ≤ G) (hgapE : γE • (E * E) ≤ t • (1 - C) - G) (hgapF : γF • (F * F) ≤ C - G) : ∃ k : ℝ, 0 < k ∧ ∀ᶠ ε : ℝ in 𝓝 0, let X := G + ε • (E * Y * F + star (E * Y * F)) - (k * ε ^ 2) • (E * E + F * F)
      0 ≤ X ∧ X ≤ C ∧ X ≤ t • (1 - C) := by
  let W := E * E + F * F
  let D := E * Y * F + star (E * Y * F)
  let q := ‖Y‖ ^ 2
  let γ := min γE γF
  let k := 1 + q / γ
  let L := 1 + q
  have hγ : 0 < γ := lt_min hγE hγF
  have hq : 0 ≤ q := sq_nonneg _
  have hk : 0 < k := by dsimp [k]; positivity
  have hkg : q / k ≤ γ := by
    apply (div_le_iff₀ hk).mpr
    dsimp [k]
    have he : γ * (1 + q / γ) = γ + q := by field_simp [ne_of_gt hγ]
    rw [he]
    linarith
  have hke : q / k ≤ γE := hkg.trans (min_le_left _ _)
  have hkf : q / k ≤ γF := hkg.trans (min_le_right _ _)
  have hEE : 0 ≤ E * E := hE.mul_self_nonneg
  have hFF : 0 ≤ F * F := hF.mul_self_nonneg
  have hW : 0 ≤ W := add_nonneg hEE hFF
  have hbasic : ∀ ε : ℝ, ε • D ≤ (ε ^ 2) • (E * E) + q • (F * F) := by
    intro ε
    simpa only [one_mul, div_one] using cutoff_young hE hF Y zero_lt_one ε
  have hL1 : (1 : ℝ) ≤ L := by dsimp [L]; linarith
  have hLq : q ≤ L := by dsimp [L]; linarith
  have hcap : E * E + q • (F * F) ≤ L • W := by
    calc
      _ ≤ L • (E * E) + L • (F * F) := by
        apply add_le_add
        · simpa only [one_smul] using smul_le_smul_of_nonneg_right hL1 hEE
        · exact smul_le_smul_of_nonneg_right hLq hFF
      _ = _ := (smul_add L (E * E) (F * F)).symm
  have hbound : ∀ ε : ℝ, ε • D ≤ (|ε| * L) • W := by
    have h₁ : D ≤ L • W := by
      have hh := hbasic 1
      simp only [one_smul, one_pow] at hh
      exact hh.trans hcap
    have h₂ : -D ≤ L • W := by
      have hh := hbasic (-1)
      simp only [neg_one_smul, neg_sq, one_pow, one_smul] at hh
      exact hh.trans hcap
    intro ε
    by_cases hε : 0 ≤ ε
    · simpa only [smul_smul, abs_of_nonneg hε] using smul_le_smul_of_nonneg_left h₁ hε
    · have hh := smul_le_smul_of_nonneg_left h₂ (neg_nonneg.mpr (le_of_not_ge hε))
      simpa only [smul_neg, neg_smul, neg_neg, smul_smul, abs_of_neg (lt_of_not_ge hε)] using hh
  have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < u - |ε| * L - k * ε ^ 2 := by
    have hc : Continuous (fun ε : ℝ => u - |ε| * L - k * ε ^ 2) := by fun_prop
    exact hc.continuousAt.tendsto.eventually (lt_mem_nhds (by simpa using hu))
  refine ⟨k, hk, ?_⟩
  filter_upwards [hpos] with ε hε
  have heps : 0 ≤ k * ε ^ 2 := mul_nonneg hk.le (sq_nonneg ε)
  have hnonneg : 0 ≤ G + ε • D - (k * ε ^ 2) • W := by
    change u • W ≤ G at hG
    have hn := neg_le_neg (hbound (-ε))
    have hn' : -((|ε| * L) • W) ≤ ε • D := by simpa only [abs_neg, neg_smul, neg_neg] using hn
    have hh := sub_le_sub_right (add_le_add hG hn') ((k * ε ^ 2) • W)
    have hz : 0 ≤ (u - |ε| * L - k * ε ^ 2) • W := smul_nonneg hε.le hW
    apply hz.trans
    simpa only [sub_eq_add_neg, add_smul, neg_smul] using hh
  have hupperF : ε • D ≤ (k * ε ^ 2) • W + γF • (F * F) := by
    apply (cutoff_young hE hF Y hk ε).trans
    calc
      (k * ε ^ 2) • (E * E) + (q / k) • (F * F) ≤ (k * ε ^ 2) • (E * E) + (k * ε ^ 2 + γF) • (F * F) := by exact add_le_add le_rfl (smul_le_smul_of_nonneg_right (hkf.trans (le_add_of_nonneg_left heps)) hFF)
      _ = _ := by dsimp [W]; rw [smul_add, add_smul]; abel
  have hupperE : ε • D ≤ (k * ε ^ 2) • W + γE • (E * E) := by
    apply (cutoff_young_swapped hE hF Y hk ε).trans
    calc
      (q / k) • (E * E) + (k * ε ^ 2) • (F * F) ≤ (k * ε ^ 2 + γE) • (E * E) + (k * ε ^ 2) • (F * F) := by exact add_le_add (smul_le_smul_of_nonneg_right (hke.trans (le_add_of_nonneg_left heps)) hEE) le_rfl
      _ = _ := by dsimp [W]; rw [smul_add, add_smul]; abel
  refine ⟨hnonneg, ?_, ?_⟩
  · calc
      _ ≤ G + ((k * ε ^ 2) • W + γF • (F * F)) - (k * ε ^ 2) • W := sub_le_sub_right (add_le_add le_rfl hupperF) _
      _ = G + γF • (F * F) := by abel
      _ ≤ G + (C - G) := add_le_add le_rfl hgapF
      _ = C := by abel
  · calc
      _ ≤ G + ((k * ε ^ 2) • W + γE • (E * E)) - (k * ε ^ 2) • W := sub_le_sub_right (add_le_add le_rfl hupperE) _
      _ = G + γE • (E * E) := by abel
      _ ≤ G + (t • (1 - C) - G) := add_le_add le_rfl hgapE
      _ = t • (1 - C) := by abel
private theorem coeff_add (Ω : H) (A B : Op) : coeff Ω (A + B) = coeff Ω A + coeff Ω B := by simp only [coeff, add_apply, inner_add_right]
private theorem coeff_sub (Ω : H) (A B : Op) : coeff Ω (A - B) = coeff Ω A - coeff Ω B := by simp only [coeff, sub_apply, inner_sub_right]
private theorem coeff_smul (Ω : H) (z : ℂ) (A : Op) : coeff Ω (z • A) = z * coeff Ω A := by simp only [coeff, smul_apply, inner_smul_right]
private theorem coeff_real_smul (Ω : H) (r : ℝ) (A : Op) : coeff Ω (r • A) = (r : ℂ) * coeff Ω A := by rw [← Complex.coe_smul, coeff_smul]
private theorem real_smul_mem (N : VonNeumannAlgebra H) {A : Op} (hA : A ∈ N) (r : ℝ) : r • A ∈ N := by
  have h := N.toStarSubalgebra.smul_mem hA (r : ℂ)
  change r • A ∈ N.toStarSubalgebra
  simpa only [Complex.coe_smul] using h
private theorem optimal_real_cutoff_derivative (N : VonNeumannAlgebra H) {C E F Y : Op} (Ω : H) {t u γE γF : ℝ} (hE : IsSelfAdjoint E) (hF : IsSelfAdjoint F) (hEN : E ∈ N) (hFN : F ∈ N) (hYN : Y ∈ N) (hGN : overlap C t ∈ N) (hu : 0 < u) (hγE : 0 < γE) (hγF : 0 < γF) (hG : u • (E * E + F * F) ≤ overlap C t) (hgapE : γE • (E * E) ≤ t • (1 - C) - overlap C t) (hgapF : γF • (F * F) ≤ C - overlap C t) (hopt : ∀ X, Feasible N C X t → vectorValue Ω X ≤ vectorValue Ω (overlap C t)) : vectorValue Ω (E * Y * F + star (E * Y * F)) = 0 := by
  let W := E * E + F * F
  let D := E * Y * F + star (E * Y * F)
  have hWN : W ∈ N := N.add_mem (N.mul_mem hEN hEN) (N.mul_mem hFN hFN)
  have hDN : D ∈ N := N.add_mem (N.mul_mem (N.mul_mem hEN hYN) hFN) (N.toStarSubalgebra.star_mem' (N.mul_mem (N.mul_mem hEN hYN) hFN))
  obtain ⟨k, hk, hvariation⟩ := cutoff_variation_feasible (Y := Y) hE hF hu hγE hγF hG hgapE hgapF
  apply quadratic_local_max_derivative (w := vectorValue Ω W) (k := k)
  filter_upwards [hvariation] with ε hε
  have hm : overlap C t + ε • D - (k * ε ^ 2) • W ∈ N := N.sub_mem (N.add_mem hGN (real_smul_mem N hDN ε)) (real_smul_mem N hWN _)
  have hineq := hopt _ ⟨hm, hε⟩
  have hformula : vectorValue Ω (overlap C t + ε • D - (k * ε ^ 2) • W) = vectorValue Ω (overlap C t) + ε * vectorValue Ω D - k * ε ^ 2 * vectorValue Ω W := by
    change (coeff Ω (overlap C t + ε • D - (k * ε ^ 2) • W)).re = _
    rw [coeff_sub, coeff_add, coeff_real_smul, coeff_real_smul]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, vectorValue, coeff]
  rw [hformula] at hineq
  linarith
/-- Actual optimality forces every cutoff cross coefficient to vanish whenever the three strict operator margins admit a quadratic feasible perturbation. -/
theorem optimal_cutoff_annihilation (N : VonNeumannAlgebra H) {C E F Y : Op} (Ω : H) {t u γE γF : ℝ} (hE : IsSelfAdjoint E) (hF : IsSelfAdjoint F) (hEN : E ∈ N) (hFN : F ∈ N) (hYN : Y ∈ N) (hGN : overlap C t ∈ N) (hu : 0 < u) (hγE : 0 < γE) (hγF : 0 < γF) (hG : u • (E * E + F * F) ≤ overlap C t) (hgapE : γE • (E * E) ≤ t • (1 - C) - overlap C t) (hgapF : γF • (F * F) ≤ C - overlap C t) (hopt : ∀ X, Feasible N C X t → vectorValue Ω X ≤ vectorValue Ω (overlap C t)) : inner ℂ Ω ((E * Y * F) Ω) = 0 := by
  have hreal := optimal_real_cutoff_derivative N Ω hE hF hEN hFN hYN hGN hu hγE hγF hG hgapE hgapF hopt
  have hI := optimal_real_cutoff_derivative N Ω hE hF hEN hFN (N.toStarSubalgebra.smul_mem hYN Complex.I) hGN hu hγE hγF hG hgapE hgapF hopt
  change (coeff Ω (E * Y * F + star (E * Y * F))).re = 0 at hreal
  change (coeff Ω (E * (Complex.I • Y) * F + star (E * (Complex.I • Y) * F))).re = 0 at hI
  rw [coeff_add, coeff_star] at hreal hI
  have he : E * (Complex.I • Y) * F = Complex.I • (E * Y * F) := by rw [mul_smul_comm, smul_mul_assoc]
  rw [he, coeff_smul] at hI
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hreal hI
  change coeff Ω (E * Y * F) = 0
  apply Complex.ext <;> change _ = 0 <;> linarith
private def flatRamp (n : ℕ) (b x : ℝ) : ℝ := min 1 (max 0 (((n : ℝ) + 1) * x - b))
private theorem flatRamp_continuous (n : ℕ) (b : ℝ) : Continuous (flatRamp n b) := by
  unfold flatRamp
  fun_prop
private theorem flatRamp_bounds (n : ℕ) {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) : 0 ≤ flatRamp n b x ∧ flatRamp n b x ≤ 1 ∧ flatRamp n b x ≤ ((n : ℝ) + 1) * x ∧ x * (1 - flatRamp n b x) ≤ (b + 1) / ((n : ℝ) + 1) := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have h0 : 0 ≤ flatRamp n b x := le_min zero_le_one (le_max_left _ _)
  have h1 : flatRamp n b x ≤ 1 := min_le_left _ _
  refine ⟨h0, h1, ?_, ?_⟩
  · exact (min_le_right _ _).trans (max_le (mul_nonneg hm.le hx) (by linarith))
  · by_cases h : ((n : ℝ) + 1) * x ≤ b + 1
    · have he : x ≤ (b + 1) / ((n : ℝ) + 1) := (le_div_iff₀ hm).mpr (by nlinarith)
      exact (mul_le_of_le_one_right hx (by linarith)).trans he
    · have he : flatRamp n b x = 1 := min_eq_left ((le_max_right _ _).trans' (by linarith))
      rw [he, sub_self, mul_zero]
      positivity
private theorem flatRamp_zero (n : ℕ) {b x : ℝ} (h : ((n : ℝ) + 1) * x ≤ b) : flatRamp n b x = 0 := by simp only [flatRamp, max_eq_left (sub_nonpos.mpr h), min_eq_right zero_le_one]
private theorem flatRamp_one (n : ℕ) {b x : ℝ} (h : b + 1 ≤ ((n : ℝ) + 1) * x) : flatRamp n b x = 1 := by exact min_eq_left ((le_max_right _ _).trans' (by linarith))
private theorem flatApprox_tendsto {T : Op} (hT : 0 ≤ T) {b : ℝ} (hb : 0 ≤ b) (x : H) : Tendsto (fun n => cfc (flatRamp n b) T x) atTop (𝓝 (rangeSupport T x)) := by
  have hs := IsSelfAdjoint.of_nonneg hT
  apply support_convergence hs (fun n => cfc (flatRamp n b) T)
  · intro n
    apply norm_cfc_le zero_le_one
    intro u hu
    have hh := flatRamp_bounds n hb (spectrum_nonneg_of_nonneg hT hu)
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2.1
  · intro n y hy
    apply kernel_antitone (cfc_nonneg (fun u hu =>
      (flatRamp_bounds n hb (spectrum_nonneg_of_nonneg hT hu)).1))
      (A := ((n : ℝ) + 1) • T) ?_ (by simp only [smul_apply, hy, smul_zero])
    conv_rhs => rw [← cfc_id' ℝ T hs]
    rw [← cfc_const_mul ((n : ℝ) + 1) (fun u : ℝ => u) T continuousOn_id]
    apply (cfc_le_iff _ _ T (flatRamp_continuous n b).continuousOn (by fun_prop) hs).mpr
    intro u hu
    exact (flatRamp_bounds n hb (spectrum_nonneg_of_nonneg hT hu)).2.2.1
  · have herr (n : ℕ) : ‖(cfc (flatRamp n b) T - 1) * T‖ ≤ (b + 1) / ((n : ℝ) + 1) := by
      have he : (cfc (flatRamp n b) T - 1) * T = cfc (fun u : ℝ => (flatRamp n b u - 1) * u) T := by rw [cfc_mul (fun u : ℝ => flatRamp n b u - 1) (fun u : ℝ => u) T (by fun_prop [flatRamp]) continuousOn_id, cfc_sub _ _ T (flatRamp_continuous n b).continuousOn continuousOn_const, cfc_const_one ℝ T hs, cfc_id' ℝ T hs]
      rw [he]
      apply norm_cfc_le (by positivity)
      intro u hu
      have hhu := spectrum_nonneg_of_nonneg hT hu
      have hh := flatRamp_bounds n hb hhu
      rw [Real.norm_eq_abs]
      have heq : (flatRamp n b u - 1) * u = -(u * (1 - flatRamp n b u)) := by ring
      rw [heq, abs_neg, abs_of_nonneg (mul_nonneg hhu (sub_nonneg.mpr hh.2.1))]
      exact hh.2.2.2
    apply squeeze_zero (fun _ => norm_nonneg _) herr
    simpa only [div_eq_mul_inv, mul_zero, one_mul] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b + 1)
private def interiorCutoff (n : ℕ) (x : ℝ) : ℝ := flatRamp n 1 (x * (1 - x))
private def lowerCutoff (n : ℕ) (s x : ℝ) : ℝ := interiorCutoff n x * (1 - flatRamp n 0 (max 0 (x - s)))
private def upperCutoff (n : ℕ) (s x : ℝ) : ℝ := interiorCutoff n x * flatRamp n 3 (max 0 (x - s))
private theorem cutoff_continuous (n : ℕ) (s : ℝ) : Continuous (interiorCutoff n) ∧ Continuous (lowerCutoff n s) ∧ Continuous (upperCutoff n s) := by exact ⟨by fun_prop [interiorCutoff, flatRamp], by fun_prop [lowerCutoff, interiorCutoff, flatRamp], by fun_prop [upperCutoff, interiorCutoff, flatRamp]⟩
private theorem interiorCutoff_tendsto {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (x : H) : Tendsto (fun n => cfc (interiorCutoff n) C x) atTop (𝓝 (interiorSupport C x)) := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have he (n : ℕ) : cfc (interiorCutoff n) C = cfc (flatRamp n 1) (C * (1 - C)) := by
    change cfc ((flatRamp n 1) ∘ (fun u : ℝ => u * (1 - u))) C = _
    rw [cfc_comp (flatRamp n 1) (fun u : ℝ => u * (1 - u)) C hs (flatRamp_continuous n 1).continuousOn (by fun_prop)]
    congr 1
    rw [cfc_mul (fun u : ℝ => u) (fun u : ℝ => 1 - u) C continuousOn_id (by fun_prop), cfc_id' ℝ C hs, cfc_sub (fun _ : ℝ => 1) (fun u : ℝ => u) C continuousOn_const continuousOn_id, cfc_const_one ℝ C hs, cfc_id' ℝ C hs]
  simpa only [he, interiorSupport] using flatApprox_tendsto (interior_product_nonneg hC₀ hC₁) zero_le_one x
private theorem strong_mul {A B : ℕ → Op} {a b : Op} (hA : ∀ n, ‖A n‖ ≤ 1) (ha : ∀ x, Tendsto (fun n => A n x) atTop (𝓝 (a x))) (hb : ∀ x, Tendsto (fun n => B n x) atTop (𝓝 (b x))) (x : H) : Tendsto (fun n => (A n * B n) x) atTop (𝓝 ((a * b) x)) := by
  have hdiff : Tendsto (fun n => A n (B n x - b x)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => (A n).le_of_opNorm_le (hA n) _) ?_
    simpa only [one_mul, sub_self, norm_zero] using (hb x).sub_const (b x) |>.norm
  have hh := hdiff.add (ha (b x))
  change Tendsto (fun n => A n (B n x)) atTop (𝓝 (a (b x)))
  simpa only [map_sub, sub_add_cancel, zero_add] using hh
private theorem cutoff_limits {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (s : ℝ) (x : H) : Tendsto (fun n => cfc (lowerCutoff n s) C x) atTop (𝓝 ((interiorSupport C * (1 - thresholdSupport C s)) x)) ∧ Tendsto (fun n => cfc (upperCutoff n s) C x) atTop (𝓝 ((interiorSupport C * thresholdSupport C s) x)) := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have ha := interiorCutoff_tendsto hC₀ hC₁
  have hnorm (n : ℕ) : ‖cfc (interiorCutoff n) C‖ ≤ 1 := by
    apply norm_cfc_le zero_le_one
    intro u hu
    have hi := spectrum_unit_interval hC₀ hC₁ hu
    have hh := flatRamp_bounds n zero_le_one (mul_nonneg hi.1 (sub_nonneg.mpr hi.2))
    change |flatRamp n 1 (u * (1 - u))| ≤ 1
    rw [abs_of_nonneg hh.1]
    exact hh.2.1
  have hcomp (n : ℕ) (b : ℝ) : cfc (fun u : ℝ => flatRamp n b (max 0 (u - s))) C = cfc (flatRamp n b) (thresholdPart C s) := cfc_comp (flatRamp n b) (fun u : ℝ => max 0 (u - s)) C hs (flatRamp_continuous n b).continuousOn (by fun_prop)
  constructor
  · have hb (y : H) : Tendsto (fun n =>
        cfc (fun u : ℝ => 1 - flatRamp n 0 (max 0 (u - s))) C y) atTop
        (𝓝 ((1 - thresholdSupport C s) y)) := by
      have hh := (tendsto_const_nhds (x := y) (f := atTop)).sub (flatApprox_tendsto (thresholdPart_nonneg C s) (le_refl 0) y)
      have heq (n : ℕ) : cfc (fun u : ℝ => 1 - flatRamp n 0 (max 0 (u - s))) C = 1 - cfc (flatRamp n 0) (thresholdPart C s) := by rw [cfc_sub (fun _ : ℝ => 1) (fun u : ℝ => flatRamp n 0 (max 0 (u - s))) C continuousOn_const (by fun_prop [flatRamp]), cfc_const_one ℝ C hs, hcomp]
      simpa only [heq, sub_apply, one_apply_eq_self, thresholdSupport] using hh
    have hh := strong_mul hnorm ha hb x
    have heq (n : ℕ) : cfc (lowerCutoff n s) C = cfc (interiorCutoff n) C * cfc (fun u : ℝ => 1 - flatRamp n 0 (max 0 (u - s))) C := cfc_mul (interiorCutoff n) (fun u : ℝ => 1 - flatRamp n 0 (max 0 (u - s))) C (cutoff_continuous n s).1.continuousOn (by fun_prop [flatRamp])
    simpa only [heq] using hh
  · have hb (y : H) : Tendsto (fun n =>
        cfc (fun u : ℝ => flatRamp n 3 (max 0 (u - s))) C y) atTop
        (𝓝 (thresholdSupport C s y)) := by
      simpa only [hcomp, thresholdSupport] using flatApprox_tendsto (thresholdPart_nonneg C s) (by norm_num : (0 : ℝ) ≤ 3) y
    have hh := strong_mul hnorm ha hb x
    have heq (n : ℕ) : cfc (upperCutoff n s) C = cfc (interiorCutoff n) C * cfc (fun u : ℝ => flatRamp n 3 (max 0 (u - s))) C := cfc_mul (interiorCutoff n) (fun u : ℝ => flatRamp n 3 (max 0 (u - s))) C (cutoff_continuous n s).1.continuousOn (by fun_prop [flatRamp])
    simpa only [heq] using hh
private theorem cutoff_scalar_margins (n : ℕ) (s t : ℝ) (ht : 0 < t) (htr : t * (1 - (s + 2 / ((n : ℝ) + 1))) = s + 2 / ((n : ℝ) + 1)) {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : let δ := 1 / ((n : ℝ) + 1)
    let u := δ * min 1 t / 2
    let e := lowerCutoff n s x
    let f := upperCutoff n s x
    u * (e * e + f * f) ≤ min x (t * (1 - x)) ∧ δ * (e * e) ≤ t * (1 - x) - min x (t * (1 - x)) ∧ δ * (f * f) ≤ x - min x (t * (1 - x)) := by
  let m : ℝ := (n : ℝ) + 1
  let δ := 1 / m
  let a := interiorCutoff n x
  let b := flatRamp n 0 (max 0 (x - s))
  let c := flatRamp n 3 (max 0 (x - s))
  have hm : 0 < m := by dsimp [m]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδm : m * δ = 1 := mul_one_div_cancel (ne_of_gt hm)
  have htr' : t * (1 - (s + 2 * δ)) = s + 2 * δ := by simpa only [δ, m, div_eq_mul_inv, one_mul] using htr
  have hh : 0 ≤ x * (1 - x) := mul_nonneg hx₀ (sub_nonneg.mpr hx₁)
  have ha := flatRamp_bounds n zero_le_one hh
  have hb := flatRamp_bounds n (le_refl (0 : ℝ)) (le_max_left 0 (x - s))
  have hc := flatRamp_bounds n (by norm_num : (0 : ℝ) ≤ 3) (le_max_left 0 (x - s))
  change 0 ≤ a ∧ a ≤ 1 ∧ _ at ha
  change 0 ≤ b ∧ b ≤ 1 ∧ _ at hb
  change 0 ≤ c ∧ c ≤ 1 ∧ _ at hc
  have he₀ : 0 ≤ a * (1 - b) := mul_nonneg ha.1 (sub_nonneg.mpr hb.2.1)
  have he₁ : a * (1 - b) ≤ 1 := (mul_le_of_le_one_right ha.1 (by linarith)).trans ha.2.1
  have hf₀ : 0 ≤ a * c := mul_nonneg ha.1 hc.1
  have hf₁ : a * c ≤ 1 := (mul_le_of_le_one_right ha.1 hc.2.1).trans ha.2.1
  have he2 : (a * (1 - b)) * (a * (1 - b)) ≤ 1 := mul_le_one₀ he₁ he₀ he₁
  have hf2 : (a * c) * (a * c) ≤ 1 := mul_le_one₀ hf₁ hf₀ hf₁
  have hg₀ : 0 ≤ min x (t * (1 - x)) := le_min hx₀ (mul_nonneg ht.le (by linarith))
  have hmin : 0 < min 1 t := lt_min zero_lt_one ht
  have hmin₁ : min 1 t ≤ 1 := min_le_left _ _
  have hminT : min 1 t ≤ t := min_le_right _ _
  have haInterior : a ≠ 0 → δ < x ∧ δ < 1 - x := by
    intro hne
    have hma : 1 < m * (x * (1 - x)) := by
      by_contra h
      exact hne (flatRamp_zero n (le_of_not_gt h))
    have hsmall : δ < x * (1 - x) := by nlinarith only [hma, hδm, hm]
    constructor
    · nlinarith only [hsmall, sq_nonneg x]
    · nlinarith only [hsmall, sq_nonneg (1 - x)]
  have hlower : a * (1 - b) ≠ 0 → x < s + δ := by
    intro hne
    by_contra h
    have hxs : δ ≤ x - s := by linarith [le_of_not_gt h]
    have hmul : 1 ≤ m * max 0 (x - s) := by nlinarith only [hδm, hm, hxs, le_max_right 0 (x - s)]
    have hb1 : b = 1 := flatRamp_one n (by simpa using hmul)
    exact hne (by rw [hb1, sub_self, mul_zero])
  have hupper : a * c ≠ 0 → s + 3 * δ < x := by
    intro hne
    have hmc : 3 < m * max 0 (x - s) := by
      by_contra h
      have hc0 : c = 0 := flatRamp_zero n (le_of_not_gt h)
      exact hne (by rw [hc0, mul_zero])
    have hxs : s < x := by
      by_contra h
      rw [max_eq_left (sub_nonpos.mpr (le_of_not_gt h))] at hmc
      linarith
    rw [max_eq_right (sub_nonneg.mpr hxs.le)] at hmc
    nlinarith only [hmc, hδm, hm]
  change δ * min 1 t / 2 * (_ + _) ≤ _ ∧ δ * _ ≤ _ ∧ δ * _ ≤ _
  change δ * min 1 t / 2 * ((a * (1 - b)) * (a * (1 - b)) + (a * c) * (a * c)) ≤ _ ∧ δ * ((a * (1 - b)) * (a * (1 - b))) ≤ _ ∧ δ * ((a * c) * (a * c)) ≤ _
  refine ⟨?_, ?_, ?_⟩
  · by_cases hz : a = 0
    · simpa only [hz, zero_mul, mul_zero, zero_add] using hg₀
    · obtain ⟨hxi, hxi'⟩ := haInterior hz
      have hδmin : δ * min 1 t ≤ min x (t * (1 - x)) := by
        apply le_min
        · exact (mul_le_of_le_one_right hδ.le hmin₁).trans hxi.le
        · calc
            δ * min 1 t ≤ δ * t := mul_le_mul_of_nonneg_left hminT hδ.le
            _ = t * δ := mul_comm _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left hxi'.le ht.le
      have hu : 0 ≤ δ * min 1 t / 2 := by positivity
      calc
        _ ≤ δ * min 1 t / 2 * 2 := mul_le_mul_of_nonneg_left (by simpa only [one_add_one_eq_two] using add_le_add he2 hf2) hu
        _ = δ * min 1 t := by ring
        _ ≤ _ := hδmin
  · by_cases hz : a * (1 - b) = 0
    · rw [hz, zero_mul, mul_zero]
      exact sub_nonneg.mpr (min_le_right _ _)
    · have hxl := hlower hz
      have hgap : δ ≤ t * (1 - x) - x := by nlinarith only [htr', hxl, hδ, ht]
      rw [min_eq_left (by linarith : x ≤ t * (1 - x))]
      exact (mul_le_of_le_one_right hδ.le he2).trans hgap
  · by_cases hz : a * c = 0
    · rw [hz, zero_mul, mul_zero]
      exact sub_nonneg.mpr (min_le_left _ _)
    · have hxu := hupper hz
      have hgap : δ ≤ x - t * (1 - x) := by nlinarith only [htr', hxu, hδ, ht]
      rw [min_eq_right (by linarith : t * (1 - x) ≤ x)]
      exact (mul_le_of_le_one_right hδ.le hf2).trans hgap
private theorem cutoff_margins {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (n : ℕ) (s t : ℝ) (ht : 0 < t) (htr : t * (1 - (s + 2 / ((n : ℝ) + 1))) = s + 2 / ((n : ℝ) + 1)) : let E := cfc (lowerCutoff n s) C
    let F := cfc (upperCutoff n s) C
    let δ := 1 / ((n : ℝ) + 1)
    (δ * min 1 t / 2) • (E * E + F * F) ≤ overlap C t ∧ δ • (E * E) ≤ t • (1 - C) - overlap C t ∧ δ • (F * F) ≤ C - overlap C t := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have he : ContinuousOn (lowerCutoff n s) (spectrum ℝ C) := (cutoff_continuous n s).2.1.continuousOn
  have hf : ContinuousOn (upperCutoff n s) (spectrum ℝ C) := (cutoff_continuous n s).2.2.continuousOn
  let e := lowerCutoff n s
  let f := upperCutoff n s
  let δ := 1 / ((n : ℝ) + 1)
  let u := δ * min 1 t / 2
  have hEE : cfc e C * cfc e C = cfc (fun x => e x * e x) C := (cfc_mul e e C he he).symm
  have hFF : cfc f C * cfc f C = cfc (fun x => f x * f x) C := (cfc_mul f f C hf hf).symm
  have hsc (x : ℝ) (hx : x ∈ spectrum ℝ C) := cutoff_scalar_margins n s t ht htr (spectrum_unit_interval hC₀ hC₁ hx).1 (spectrum_unit_interval hC₀ hC₁ hx).2
  change u • (cfc e C * cfc e C + cfc f C * cfc f C) ≤ overlap C t ∧ δ • (cfc e C * cfc e C) ≤ t • (1 - C) - overlap C t ∧ δ • (cfc f C * cfc f C) ≤ C - overlap C t
  rw [hEE, hFF]
  constructor
  · rw [← cfc_add C (fun x : ℝ => e x * e x) (fun x : ℝ => f x * f x) (he.mul he) (hf.mul hf), ← cfc_const_mul u (fun x : ℝ => e x * e x + f x * f x) C ((he.mul he).add (hf.mul hf))]
    exact (cfc_le_iff _ _ C (((he.mul he).add (hf.mul hf)).const_mul u) (by fun_prop) hs).mpr (fun x hx => (hsc x hx).1)
  constructor
  · have hrhs : t • (1 - C) - overlap C t = cfc (fun x : ℝ => t * (1 - x) - min x (t * (1 - x))) C := by
      rw [cfc_sub _ _ C (by fun_prop) (by fun_prop), complement_cfc hs t]
      rfl
    rw [hrhs, ← cfc_const_mul δ (fun x : ℝ => e x * e x) C (he.mul he)]
    exact (cfc_le_iff _ _ C ((he.mul he).const_mul δ) (by fun_prop) hs).mpr (fun x hx => (hsc x hx).2.1)
  · have hrhs : C - overlap C t = cfc (fun x : ℝ => x - min x (t * (1 - x))) C := by
      rw [cfc_sub (fun x : ℝ => x) _ C continuousOn_id (by fun_prop), cfc_id' ℝ C hs]
      rfl
    rw [hrhs, ← cfc_const_mul δ (fun x : ℝ => f x * f x) C (hf.mul hf)]
    exact (cfc_le_iff _ _ C ((hf.mul hf).const_mul δ) (by fun_prop) hs).mpr (fun x hx => (hsc x hx).2.2)
private theorem optimal_threshold_cross (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (Ω : H) (hopt : AllOverlapOptimal N C Ω) {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) {Y : Op} (hYN : Y ∈ N) : coeff (interiorSupport C Ω) ((1 - thresholdSupport C s) * Y * thresholdSupport C s) = 0 := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : ∀ᶠ n : ℕ in atTop, s + 2 / ((n : ℝ) + 1) < 1 := by
    have hh := (tendsto_const_nhds (x := s) (f := atTop)).add (hδ.const_mul 2)
    have hh' : Tendsto (fun n : ℕ => s + 2 / ((n : ℝ) + 1)) atTop (𝓝 s) := by simpa only [mul_zero, add_zero, ← mul_div_assoc, mul_one] using hh
    exact hh'.eventually (gt_mem_nhds hs₁)
  have hz : ∀ᶠ n : ℕ in atTop, coeff Ω (cfc (lowerCutoff n s) C * Y * cfc (upperCutoff n s) C) = 0 := by
    filter_upwards [hr] with n hn
    let r := s + 2 / ((n : ℝ) + 1)
    let t := r / (1 - r)
    have hr₀ : 0 < r := by dsimp [r]; positivity
    have hr₁ : r < 1 := hn
    have ht : 0 < t := div_pos hr₀ (sub_pos.mpr hr₁)
    have htr : t * (1 - (s + 2 / ((n : ℝ) + 1))) = s + 2 / ((n : ℝ) + 1) := by
      change r / (1 - r) * (1 - r) = r
      exact div_mul_cancel₀ r (ne_of_gt (sub_pos.mpr hr₁))
    have hm := cutoff_margins hC₀ hC₁ n s t ht htr
    exact optimal_cutoff_annihilation N Ω (cfc_predicate _ C) (cfc_predicate _ C) (cfc_mem_algebra N hCN _) (cfc_mem_algebra N hCN _) hYN (hopt t ht).1.1 (by positivity) (by positivity) (by positivity) hm.1 hm.2.1 hm.2.2 (hopt t ht).2
  have hl := (cutoff_limits hC₀ hC₁ s Ω).1
  have hf := (cutoff_limits hC₀ hC₁ s Ω).2
  have hlim : Tendsto (fun n => inner ℂ (cfc (lowerCutoff n s) C Ω) (Y (cfc (upperCutoff n s) C Ω))) atTop (𝓝 (inner ℂ ((interiorSupport C * (1 - thresholdSupport C s)) Ω) (Y ((interiorSupport C * thresholdSupport C s) Ω)))) := hl.inner (Y.continuous.tendsto _ |>.comp hf)
  have hcoeff (n : ℕ) : inner ℂ (cfc (lowerCutoff n s) C Ω) (Y (cfc (upperCutoff n s) C Ω)) = coeff Ω (cfc (lowerCutoff n s) C * Y * cfc (upperCutoff n s) C) := by exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (cfc_predicate _ C)) _ _
  have hzero : inner ℂ ((interiorSupport C * (1 - thresholdSupport C s)) Ω) (Y ((interiorSupport C * thresholdSupport C s) Ω)) = 0 := by
    apply tendsto_nhds_unique hlim
    exact tendsto_const_nhds.congr' (hz.mono (fun n hn => (hcoeff n).trans hn |>.symm))
  obtain ⟨hP, hPN, hPC⟩ := interiorSupport_properties N hCN hs
  have hSP : Commute (thresholdSupport C s) (interiorSupport C) := rangeSupport_commute (IsSelfAdjoint.of_nonneg (thresholdPart_nonneg C s)) (hPC.symm.cfc_real _)
  have hE : IsSelfAdjoint (1 - thresholdSupport C s) := (thresholdSupport_properties N hCN s).1.one_sub.isSelfAdjoint
  have hleft : (interiorSupport C * (1 - thresholdSupport C s)) Ω = (1 - thresholdSupport C s) (interiorSupport C Ω) := by
    have he : interiorSupport C * (1 - thresholdSupport C s) = (1 - thresholdSupport C s) * interiorSupport C := by rw [mul_sub, sub_mul, mul_one, one_mul, hSP.eq]
    exact congrArg (fun A : Op => A Ω) he
  have hright : (interiorSupport C * thresholdSupport C s) Ω = thresholdSupport C s (interiorSupport C Ω) := congrArg (fun A : Op => A Ω) hSP.eq.symm
  rw [hleft, hright] at hzero
  change inner ℂ (interiorSupport C Ω) ((1 - thresholdSupport C s) (Y (thresholdSupport C s (interiorSupport C Ω)))) = 0
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hE) (interiorSupport C Ω) (Y (thresholdSupport C s (interiorSupport C Ω)))).symm.trans hzero
private theorem optimal_threshold_centralizes (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (Ω : H) (hopt : AllOverlapOptimal N C Ω) {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) : thresholdSupport C s ∈ centralizer N (interiorSupport C Ω) := by
  let S := thresholdSupport C s
  let w := interiorSupport C Ω
  have hS : IsStarProjection S := (thresholdSupport_properties N hCN s).1
  have hoff (Y : Op) (hY : Y ∈ N) : coeff w ((1 - S) * Y * S) = 0 := optimal_threshold_cross N hCN hC₀ hC₁ Ω hopt hs₀ hs₁ hY
  have hoff' (Y : Op) (hY : Y ∈ N) : coeff w (S * Y * (1 - S)) = 0 := by
    have hh := congrArg star (hoff (star Y) (N.toStarSubalgebra.star_mem' hY))
    rw [← coeff_star] at hh
    simpa only [star_mul, star_star, star_sub, star_one, hS.isSelfAdjoint.star_eq, mul_assoc, star_zero] using hh
  refine ⟨(thresholdSupport_properties N hCN s).2.1, ?_⟩
  intro Y hY
  have hl : S * Y = S * Y * S + S * Y * (1 - S) := by noncomm_ring
  have hr : Y * S = S * Y * S + (1 - S) * Y * S := by noncomm_ring
  rw [hl, hr, coeff_add, coeff_add, hoff Y hY, hoff' Y hY]
private theorem mul_support_of_kernel {A T : Op} (hT : IsSelfAdjoint T) (hker : ∀ x, T x = 0 → A x = 0) : A * rangeSupport T = A := by
  ext x
  change A (rangeSupport T x) = A x
  have hk : T (x - rangeSupport T x) = 0 := by
    rw [map_sub]
    change T x - (T * rangeSupport T) x = 0
    rw [mul_rangeSupport hT, sub_self]
  have hh := hker (x - rangeSupport T x) hk
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hh)).symm
private theorem threshold_increment {C : Op} (hC : IsSelfAdjoint C) {s t : ℝ} (hst : s ≤ t) : (t - s) • thresholdSupport C t ≤ thresholdPart C s - thresholdPart C t ∧ thresholdPart C s - thresholdPart C t ≤ (t - s) • thresholdSupport C s := by
  let D := thresholdPart C s - thresholdPart C t
  let f : ℝ → ℝ := fun x => max 0 (x - s) - max 0 (x - t)
  have hSs : IsStarProjection (thresholdSupport C s) := rangeSupport_isProjection _
  have hSt : IsStarProjection (thresholdSupport C t) := rangeSupport_isProjection _
  have hscalar (x : ℝ) : 0 ≤ f x ∧ f x ≤ t - s ∧ (f x - (t - s)) * max 0 (x - t) = 0 := by
    dsimp [f]
    by_cases hxt : x ≤ t
    · rw [max_eq_left (sub_nonpos.mpr hxt), sub_zero]
      refine ⟨le_max_left _ _, ?_, by ring⟩
      exact max_le (sub_nonneg.mpr hst) (by linarith)
    · have htx := le_of_not_ge hxt
      rw [max_eq_right (sub_nonneg.mpr htx), max_eq_right (sub_nonneg.mpr (hst.trans htx))]
      constructor
      · linarith
      constructor <;> ring_nf <;> first | exact le_rfl | rfl
  have hD_eq : D = cfc f C := by exact (cfc_sub _ _ C (by fun_prop) (by fun_prop)).symm
  have hD : 0 ≤ D := by rw [hD_eq]; exact cfc_nonneg (fun x _ => (hscalar x).1)
  have hDsa : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hD
  have hDle : D ≤ (t - s) • (1 : Op) := by
    rw [hD_eq, ← Algebra.algebraMap_eq_smul_one, ← cfc_const (t - s) C hC]
    exact (cfc_le_iff _ _ C (by dsimp only [f]; fun_prop) continuousOn_const hC).mpr (fun x _ => (hscalar x).2.1)
  have hker : D * thresholdSupport C s = D := by
    apply mul_support_of_kernel (IsSelfAdjoint.of_nonneg (thresholdPart_nonneg C s))
    intro x hx
    apply kernel_antitone hD (A := thresholdPart C s) (sub_le_self _ (thresholdPart_nonneg C t)) hx
  have hleft : thresholdSupport C s * D = D := by
    have he := congrArg star hker
    simpa only [star_mul, hDsa.star_eq, hSs.isSelfAdjoint.star_eq] using he
  have hzero : (D - (t - s) • (1 : Op)) * thresholdPart C t = 0 := by
    rw [hD_eq, ← Algebra.algebraMap_eq_smul_one, ← cfc_const (t - s) C hC, ← cfc_sub f (fun _ : ℝ => t - s) C (by dsimp only [f]; fun_prop) continuousOn_const]
    rw [thresholdPart, ← cfc_mul (fun x : ℝ => f x - (t - s)) (fun x : ℝ => max 0 (x - t)) C (by dsimp only [f]; fun_prop) (by fun_prop)]
    have heq := cfc_congr (a := C) (f := fun x : ℝ => (f x - (t - s)) * max 0 (x - t)) (g := fun _ : ℝ => 0) (fun x _ => (hscalar x).2.2)
    rw [heq, cfc_const_zero]
  have hright : D * thresholdSupport C t = (t - s) • thresholdSupport C t := by
    have hh := mul_support_zero hzero
    simpa only [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero, thresholdSupport] using hh
  have hleft' : thresholdSupport C t * D = (t - s) • thresholdSupport C t := by
    have hh := congrArg star hright
    simpa only [star_mul, hDsa.star_eq, star_smul, star_trivial, hSt.isSelfAdjoint.star_eq] using hh
  constructor
  · apply sub_nonneg.mp
    have hp := star_left_conjugate_nonneg hD (1 - thresholdSupport C t)
    rw [hSt.one_sub.isSelfAdjoint.star_eq] at hp
    have he : (1 - thresholdSupport C t) * D * (1 - thresholdSupport C t) = D - (t - s) • thresholdSupport C t := by
      rw [sub_mul, one_mul, hleft', mul_sub, mul_one, sub_mul, hright, smul_mul_assoc, hSt.isIdempotentElem.eq]
      abel
    rwa [he] at hp
  · have hh := star_left_conjugate_le_conjugate hDle (thresholdSupport C s)
    simpa only [hSs.isSelfAdjoint.star_eq, hleft, hker, mul_smul_comm, mul_one, smul_mul_assoc, hSs.isIdempotentElem.eq] using hh
private theorem threshold_endpoint_parts {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) : thresholdPart C 0 = C ∧ thresholdPart C 1 = 0 := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  constructor
  · change cfc (fun x : ℝ => max 0 (x - 0)) C = C
    calc
      _ = cfc (fun x : ℝ => x) C := cfc_congr (fun x hx => by rw [sub_zero, max_eq_right (spectrum_nonneg_of_nonneg hC₀ hx)])
      _ = C := cfc_id' ℝ C hs
  · rw [thresholdPart]
    have heq := cfc_congr (a := C) (f := fun x : ℝ => max 0 (x - 1)) (g := fun _ : ℝ => 0) (fun x hx => max_eq_left (sub_nonpos.mpr (spectrum_unit_interval hC₀ hC₁ hx).2))
    rw [heq, cfc_const_zero]
private theorem threshold_endpoint_one {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) : thresholdSupport C 1 = 0 := by
  rw [thresholdSupport, (threshold_endpoint_parts hC₀ hC₁).2]
  apply ContinuousLinearMap.ext
  intro x
  simp [rangeSupport]
private theorem threshold_step_bound {C : Op} (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (m : ℕ) (hm : 0 < m) : let D := (1 / (m : ℝ)) • ∑ i ∈ Finset.range m, thresholdSupport C (((i : ℝ) + 1) / m)
    0 ≤ C - D ∧ ‖C - D‖ ≤ 1 / (m : ℝ) := by
  have hs := IsSelfAdjoint.of_nonneg hC₀
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let a : ℕ → ℝ := fun i => (i : ℝ) / m
  let S : ℕ → Op := fun i => thresholdSupport C (a i)
  let T : ℕ → Op := fun i => thresholdPart C (a i)
  have hstep (i : ℕ) : a (i + 1) - a i = 1 / (m : ℝ) := by dsimp [a]; push_cast; ring
  have hinc (i : ℕ) := threshold_increment hs (s := a i) (t := a (i + 1)) (by dsimp [a]; gcongr; exact_mod_cast Nat.le_succ i)
  have hlo : (1 / (m : ℝ)) • (∑ i ∈ Finset.range m, S (i + 1)) ≤ C := by
    have hh := Finset.sum_le_sum (s := Finset.range m) (fun i _ => (hinc i).1)
    simp only [hstep, ← Finset.smul_sum, Finset.sum_range_sub', T] at hh
    simpa only [a, Nat.cast_zero, zero_div, Nat.cast_ofNat, div_self (ne_of_gt hmR), (threshold_endpoint_parts hC₀ hC₁).1, (threshold_endpoint_parts hC₀ hC₁).2, sub_zero] using hh
  have hhi : C ≤ (1 / (m : ℝ)) • (∑ i ∈ Finset.range m, S i) := by
    have hh := Finset.sum_le_sum (s := Finset.range m) (fun i _ => (hinc i).2)
    simp only [hstep, ← Finset.smul_sum, Finset.sum_range_sub', T] at hh
    simpa only [a, Nat.cast_zero, zero_div, div_self (ne_of_gt hmR), (threshold_endpoint_parts hC₀ hC₁).1, (threshold_endpoint_parts hC₀ hC₁).2, sub_zero] using hh
  have hsum : (∑ i ∈ Finset.range m, S i) - (∑ i ∈ Finset.range m, S (i + 1)) = S 0 - S m := by rw [← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hSlast : S m = 0 := by
    dsimp [S, a]
    rw [div_self (ne_of_gt hmR), threshold_endpoint_one hC₀ hC₁]
  have herr : C - (1 / (m : ℝ)) • (∑ i ∈ Finset.range m, S (i + 1)) ≤ (1 / (m : ℝ)) • (1 : Op) := by
    calc
      _ ≤ (1 / (m : ℝ)) • (∑ i ∈ Finset.range m, S i) - (1 / (m : ℝ)) • (∑ i ∈ Finset.range m, S (i + 1)) := sub_le_sub_right hhi _
      _ = (1 / (m : ℝ)) • S 0 := by rw [← smul_sub, hsum, hSlast, sub_zero]
      _ ≤ _ := smul_le_smul_of_nonneg_left ((rangeSupport_isProjection (thresholdPart C (a 0))).le_one) (by positivity)
  have hnonneg := sub_nonneg.mpr hlo
  have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap _ (le_of_lt (one_div_pos.mpr hmR)) hnonneg).mpr (by simpa only [Algebra.algebraMap_eq_smul_one] using herr)
  simpa only [S, a, Nat.cast_add, Nat.cast_one] using And.intro hnonneg hnorm

/-- Simultaneous optimality forces compressed centralization of the original vector coefficient on the whole interior corner. -/
theorem optimal_implies_compressed_centralization (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (Ω : H) (hopt : AllOverlapOptimal N C Ω) : CompressedCentralizes N C Ω := by
  apply (compressed_coefficients N hCN (IsSelfAdjoint.of_nonneg hC₀) Ω).mpr
  let D : ℕ → Op := fun n => (1 / ((n : ℝ) + 1)) • ∑ i ∈ Finset.range (n + 1), thresholdSupport C (((i : ℝ) + 1) / ((n : ℝ) + 1))
  have hD (n : ℕ) : D n ∈ centralizer N (interiorSupport C Ω) := by
    change (1 / ((n : ℝ) + 1)) • _ ∈ centralizer N (interiorSupport C Ω)
    rw [← Complex.coe_smul]
    apply (centralizer N (interiorSupport C Ω)).smul_mem
    apply sum_mem
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    by_cases he : i = n
    · subst i
      rw [div_self (by positivity : (n : ℝ) + 1 ≠ 0), threshold_endpoint_one hC₀ hC₁]
      exact (centralizer N (interiorSupport C Ω)).zero_mem
    · apply optimal_threshold_centralizes N hCN hC₀ hC₁ Ω hopt
      · positivity
      · apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
        exact_mod_cast (show i + 1 < n + 1 by omega)
  have hlim : Tendsto D atTop (𝓝 C) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have hh := (threshold_step_bound hC₀ hC₁ (n + 1) (by omega)).2
    simpa only [Nat.cast_add, Nat.cast_one, norm_sub_rev, D] using hh
  exact (centralizer_closed N (interiorSupport C Ω)).mem_of_tendsto hlim (Eventually.of_forall hD)
/-- Endpoint-correct vector-functional optimality criterion for an arbitrary concrete von Neumann algebra, without Borel calculus or representation normality. -/
theorem all_overlap_optimal_iff_compressed_centralizes (N : VonNeumannAlgebra H) {C : Op} (hCN : C ∈ N) (hC₀ : 0 ≤ C) (hC₁ : C ≤ 1) (Ω : H) : AllOverlapOptimal N C Ω ↔ CompressedCentralizes N C Ω :=
  ⟨optimal_implies_compressed_centralization N hCN hC₀ hC₁ Ω, compressed_centralization_implies_optimal N hCN hC₀ hC₁ Ω⟩
end D5.S3.Quantum.Analysis.ContinuousCutoffCentralizer
