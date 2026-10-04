/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/DisplacementCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: DisplacementCovariance on the full bosonic Hilbert space. -/
/-
partialTrace_pairDisplacement:
  proof_shape: content
  escape_witness: Conclusion witness: the contraction-vector representation of every reduced matrix element and its transformation under both mode displacements; the discarded-mode action cancels on arbitrary completed vectors.
beam_displacement:
  proof_shape: content
  escape_witness: Conclusion witness: commutation of the two constructed global Hilbert-space unitaries, extending the two-mode exponential action to every vector in the completion.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Chain prerequisite (first freeze in Stage B): BeamSplitter.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/
import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
open D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
def mixture (v : ι → (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact ∑' i, InnerProductSpace.rankOne ℂ (v i) (v i)
def purePartialTrace (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
  exact mixture (fun n => v n)
def pairWeyl (a z : ℂ × ℂ) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  exact tensor (weylVector a.1 z.1) (weylVector a.2 z.2)
def pairDisplacement (a : ℂ × ℂ) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  have exponential_vectors_total (v : (lp (fun _ : ℕ => ℂ) 2))
      (hv : ∀ α : ℂ, inner ℂ v (exponentialVector α) = 0) : v = 0 := by
    let h_FockAttCoherentBridge_scalarSeries (v : (lp (fun _ : ℕ => ℂ) 2)) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttCoherentBridge_scalarSeries_expansion (v : (lp (fun _ : ℕ => ℂ) 2)) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) (h_FockAttCoherentBridge_scalarSeries v) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
      intro n
      simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialVector, exponentialCoeff, RCLike.inner_apply]
      ring
    have hfun : (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 := funext hv
    have hs := h_FockAttCoherentBridge_scalarSeries_expansion v
    rw [hfun] at hs
    have hzero := hs.eq_zero
    apply lp.ext
    funext n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hzero
    simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn
  have exponentialPair_total (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))
      (hv : ∀ z : ℂ × ℂ, inner ℂ v (exponentialPair z) = 0) : v = 0 := by
    let h_FockAttTwoMode_pairScalarSeries (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
    have h_FockAttTwoMode_pairScalarSeries_expansion (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialPair (α,z)))
          (h_FockAttTwoMode_pairScalarSeries v α) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialPair (α,z)))
      intro n
      simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialPair, h_FockAttTwoMode_tensor_apply, exponentialVector, exponentialCoeff, inner_smul_right]
      ring
    apply lp.ext
    funext n
    apply exponential_vectors_total
    intro α
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 := funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  have h_FockAttTwoMode_tensor_norm (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ = ‖v‖ * ‖w‖ := by
    have hs := h_FockAttTwoMode_tensor_norm_sq v w
    nlinarith [norm_nonneg (tensor v w), norm_nonneg v, norm_nonneg w,
      mul_nonneg (norm_nonneg v) (norm_nonneg w)]
  let h_FockAttTwoMode_tensorLeft (w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun v => tensor v w
        map_add' := by intro v v'; apply lp.ext; funext n; exact smul_add (w n) v v'
        map_smul' := by
          intro c v; apply lp.ext; funext n
          exact smul_comm (w n) c v }
      ‖w‖ (fun v => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm, mul_comm])
  have h_FockAttTwoMode_tensor_smul_left (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor (c • v) w = c • tensor v w := (h_FockAttTwoMode_tensorLeft w).map_smul c v
  let h_FockAttTwoMode_tensorRight (v : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun w => tensor v w
        map_add' := by intro w w'; apply lp.ext; funext n; exact add_smul (w n) (w' n) v
        map_smul' := by
          intro c w; apply lp.ext; funext n
          exact mul_smul c (w n) v }
      ‖v‖ (fun w => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm])
  have h_FockAttTwoMode_tensor_smul_right (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor v (c • w) = c • tensor v w := (h_FockAttTwoMode_tensorRight v).map_smul c w
  have h_FockAttCovariance_pairWeyl_dense (a : ℂ × ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (pairWeyl a)) := by
    have hspan : (Submodule.span ℂ (Set.range (pairWeyl a))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun z => by
          have hmem : pairWeyl a (z.1-a.1,z.2-a.2) ∈ Submodule.span ℂ (Set.range (pairWeyl a)) := Submodule.subset_span ⟨(z.1-a.1,z.2-a.2), rfl⟩
          have hi := Submodule.inner_left_of_mem_orthogonal hmem hv
          have h1 : a.1 + (z.1-a.1) = z.1 := by ring
          have h2 : a.2 + (z.2-a.2) = z.2 := by ring
          simp only [pairWeyl, weylVector, h_FockAttTwoMode_tensor_smul_left, h_FockAttTwoMode_tensor_smul_right,
            inner_smul_right, h1, h2] at hi
          exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (Complex.exp_ne_zero _))).resolve_left
            (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (pairWeyl a)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  let h_FockAttFrameExtension_gramUnitary {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) : H ≃ₗᵢ[ℂ] H := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)])
  have h_FockAttTwoMode_tensor_inner (v w v' w' : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ (tensor v w) (tensor v' w') = inner ℂ v v' * inner ℂ w w' := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum w w']
    simp only [h_FockAttTwoMode_tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
    rw [mul_pow]
    field_simp
    rw [hsq]
    ring
  have h_FockAttCoherentBridge_exponential_inner (α β : ℂ) :
      inner ℂ (exponentialVector α) (exponentialVector β) =
        Complex.exp ((starRingEnd ℂ) α * β) := by
    rw [lp.inner_eq_tsum]
    simp only [exponentialVector, h_FockAttCoherentBridge_exponentialCoeff_inner]
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq
  have h_FockAttCoherentBridge_weyl_gram (α β γ : ℂ) :
      inner ℂ (weylVector α β) (weylVector α γ) =
        inner ℂ (exponentialVector β) (exponentialVector γ) := by
    have haa : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    simp only [weylVector, inner_smul_left, inner_smul_right, h_FockAttCoherentBridge_exponential_inner,
      ← Complex.exp_conj, map_sub, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    push_cast at haa
    linear_combination haa
  have h_FockAttCoherentBridge_weyl_dense (α : ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (weylVector α)) := by
    have hspan : (Submodule.span ℂ (Set.range (weylVector α))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun β => by
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) := Submodule.subset_span ⟨β - α, rfl⟩
          have hinner := Submodule.inner_left_of_mem_orthogonal hmem hv
          have heq : α + (β - α) = β := by ring
          simp only [weylVector, inner_smul_right, heq] at hinner
          exact (mul_eq_zero.mp hinner).resolve_left (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (weylVector α)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_exponential_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialVector) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun α => by
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttFrameExtension_gramUnitary_apply {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) (i : ι) :
      h_FockAttFrameExtension_gramUnitary v w hgram hv hw (v i) = w i := by
    have hh := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
      (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)]) (Finsupp.single i (1 : ℂ))
    simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul, h_FockAttFrameExtension_gramUnitary] using hh
  have h_FockAttCoherentBridge_displacement_exponential (α β : ℂ) :
      displacement α (exponentialVector β) = weylVector α β := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α) β
  have h_FockAttCovariance_pairWeyl_gram (a z w : ℂ × ℂ) :
      inner ℂ (pairWeyl a z) (pairWeyl a w) =
        inner ℂ (exponentialPair z) (exponentialPair w) := by
    rw [pairWeyl, pairWeyl, h_FockAttTwoMode_tensor_inner]
    have h1 := (displacement a.1).inner_map_map (exponentialVector z.1) (exponentialVector w.1)
    have h2 := (displacement a.2).inner_map_map (exponentialVector z.2) (exponentialVector w.2)
    simp only [h_FockAttCoherentBridge_displacement_exponential] at h1 h2
    rw [h1, h2, exponentialPair, exponentialPair, h_FockAttTwoMode_tensor_inner]
  exact h_FockAttFrameExtension_gramUnitary exponentialPair (pairWeyl a)
      (h_FockAttCovariance_pairWeyl_gram a) h_FockAttTwoMode_exponentialPair_dense (h_FockAttCovariance_pairWeyl_dense a)

theorem partialTrace_pairDisplacement (a : ℂ × ℂ) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) :
    purePartialTrace (pairDisplacement a w) = LinearIsometryEquiv.conjStarAlgEquiv (displacement a.1) (purePartialTrace w) := by
  have exponential_vectors_total (v : (lp (fun _ : ℕ => ℂ) 2))
      (hv : ∀ α : ℂ, inner ℂ v (exponentialVector α) = 0) : v = 0 := by
    let h_FockAttCoherentBridge_scalarSeries (v : (lp (fun _ : ℕ => ℂ) 2)) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttCoherentBridge_scalarSeries_expansion (v : (lp (fun _ : ℕ => ℂ) 2)) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) (h_FockAttCoherentBridge_scalarSeries v) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
      intro n
      simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialVector, exponentialCoeff, RCLike.inner_apply]
      ring
    have hfun : (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 := funext hv
    have hs := h_FockAttCoherentBridge_scalarSeries_expansion v
    rw [hfun] at hs
    have hzero := hs.eq_zero
    apply lp.ext
    funext n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hzero
    simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn
  have exponentialPair_total (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))
      (hv : ∀ z : ℂ × ℂ, inner ℂ v (exponentialPair z) = 0) : v = 0 := by
    let h_FockAttTwoMode_pairScalarSeries (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
    have h_FockAttTwoMode_pairScalarSeries_expansion (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialPair (α,z)))
          (h_FockAttTwoMode_pairScalarSeries v α) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialPair (α,z)))
      intro n
      simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialPair, h_FockAttTwoMode_tensor_apply, exponentialVector, exponentialCoeff, inner_smul_right]
      ring
    apply lp.ext
    funext n
    apply exponential_vectors_total
    intro α
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 := funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  have h_FockAttTwoMode_tensor_norm (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ = ‖v‖ * ‖w‖ := by
    have hs := h_FockAttTwoMode_tensor_norm_sq v w
    nlinarith [norm_nonneg (tensor v w), norm_nonneg v, norm_nonneg w,
      mul_nonneg (norm_nonneg v) (norm_nonneg w)]
  let h_FockAttTwoMode_tensorLeft (w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun v => tensor v w
        map_add' := by intro v v'; apply lp.ext; funext n; exact smul_add (w n) v v'
        map_smul' := by
          intro c v; apply lp.ext; funext n
          exact smul_comm (w n) c v }
      ‖w‖ (fun v => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm, mul_comm])
  have h_FockAttTwoMode_tensor_smul_left (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor (c • v) w = c • tensor v w := (h_FockAttTwoMode_tensorLeft w).map_smul c v
  let h_FockAttTwoMode_tensorRight (v : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun w => tensor v w
        map_add' := by intro w w'; apply lp.ext; funext n; exact add_smul (w n) (w' n) v
        map_smul' := by
          intro c w; apply lp.ext; funext n
          exact mul_smul c (w n) v }
      ‖v‖ (fun w => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm])
  have h_FockAttTwoMode_tensor_smul_right (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor v (c • w) = c • tensor v w := (h_FockAttTwoMode_tensorRight v).map_smul c w
  have h_FockAttCovariance_pairWeyl_dense (a : ℂ × ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (pairWeyl a)) := by
    have hspan : (Submodule.span ℂ (Set.range (pairWeyl a))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun z => by
          have hmem : pairWeyl a (z.1-a.1,z.2-a.2) ∈ Submodule.span ℂ (Set.range (pairWeyl a)) := Submodule.subset_span ⟨(z.1-a.1,z.2-a.2), rfl⟩
          have hi := Submodule.inner_left_of_mem_orthogonal hmem hv
          have h1 : a.1 + (z.1-a.1) = z.1 := by ring
          have h2 : a.2 + (z.2-a.2) = z.2 := by ring
          simp only [pairWeyl, weylVector, h_FockAttTwoMode_tensor_smul_left, h_FockAttTwoMode_tensor_smul_right,
            inner_smul_right, h1, h2] at hi
          exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (Complex.exp_ne_zero _))).resolve_left
            (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (pairWeyl a)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  let h_FockAttFrameExtension_gramUnitary {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) : H ≃ₗᵢ[ℂ] H := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)])
  have h_FockAttFrameExtension_gramUnitary_apply {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) (i : ι) :
      h_FockAttFrameExtension_gramUnitary v w hgram hv hw (v i) = w i := by
    have hh := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
      (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)]) (Finsupp.single i (1 : ℂ))
    simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul, h_FockAttFrameExtension_gramUnitary] using hh
  have h_FockAttTwoMode_tensor_inner (v w v' w' : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ (tensor v w) (tensor v' w') = inner ℂ v v' * inner ℂ w w' := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum w w']
    simp only [h_FockAttTwoMode_tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
    rw [mul_pow]
    field_simp
    rw [hsq]
    ring
  have h_FockAttCoherentBridge_exponential_inner (α β : ℂ) :
      inner ℂ (exponentialVector α) (exponentialVector β) =
        Complex.exp ((starRingEnd ℂ) α * β) := by
    rw [lp.inner_eq_tsum]
    simp only [exponentialVector, h_FockAttCoherentBridge_exponentialCoeff_inner]
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq
  have h_FockAttCoherentBridge_weyl_gram (α β γ : ℂ) :
      inner ℂ (weylVector α β) (weylVector α γ) =
        inner ℂ (exponentialVector β) (exponentialVector γ) := by
    have haa : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    simp only [weylVector, inner_smul_left, inner_smul_right, h_FockAttCoherentBridge_exponential_inner,
      ← Complex.exp_conj, map_sub, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    push_cast at haa
    linear_combination haa
  have h_FockAttCoherentBridge_weyl_dense (α : ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (weylVector α)) := by
    have hspan : (Submodule.span ℂ (Set.range (weylVector α))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun β => by
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) := Submodule.subset_span ⟨β - α, rfl⟩
          have hinner := Submodule.inner_left_of_mem_orthogonal hmem hv
          have heq : α + (β - α) = β := by ring
          simp only [weylVector, inner_smul_right, heq] at hinner
          exact (mul_eq_zero.mp hinner).resolve_left (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (weylVector α)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_exponential_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialVector) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun α => by
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_displacement_exponential (α β : ℂ) :
      displacement α (exponentialVector β) = weylVector α β := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α) β
  have h_FockAttCovariance_pairWeyl_gram (a z w : ℂ × ℂ) :
      inner ℂ (pairWeyl a z) (pairWeyl a w) =
        inner ℂ (exponentialPair z) (exponentialPair w) := by
    rw [pairWeyl, pairWeyl, h_FockAttTwoMode_tensor_inner]
    have h1 := (displacement a.1).inner_map_map (exponentialVector z.1) (exponentialVector w.1)
    have h2 := (displacement a.2).inner_map_map (exponentialVector z.2) (exponentialVector w.2)
    simp only [h_FockAttCoherentBridge_displacement_exponential] at h1 h2
    rw [h1, h2, exponentialPair, exponentialPair, h_FockAttTwoMode_tensor_inner]
  have h_FockAttCovariance_pairDisplacement_exponential (a z : ℂ × ℂ) :
      pairDisplacement a (exponentialPair z) = pairWeyl a z := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCovariance_pairWeyl_gram a) h_FockAttTwoMode_exponentialPair_dense (h_FockAttCovariance_pairWeyl_dense a) z
  have h_FockAttFamilyExt_totalFamily_ext {ι H K : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K] (v : ι → H) (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (f g : H →L[ℂ] K) (h : ∀ i, f (v i) = g (v i)) : f = g := by
    apply ContinuousLinearMap.ext
    intro x
    refine hv.induction (P := fun y => f y = g y) ?_ ?_ x
    · rintro y ⟨c, rfl⟩
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, h]
    · exact isClosed_eq f.continuous g.continuous
  let h_FockAttPartialTrace_sliceVector (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) : (lp (fun _ : ℕ => ℂ) 2) := ⟨fun n => inner ℂ x (w n), by
      apply memℓp_gen
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
      apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (hw.summable.mul_left (‖x‖ ^ 2))
      intro n
      have h := norm_inner_le_norm (𝕜 := ℂ) x (w n)
      nlinarith [norm_nonneg (inner ℂ x (w n)), norm_nonneg x, norm_nonneg (w n)]⟩
  have h_FockAttPartialTrace_sliceVector_apply (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (n : ℕ) :
      h_FockAttPartialTrace_sliceVector x w n = inner ℂ x (w n) := rfl
  have h_FockAttPartialTrace_sliceVector_norm (x : (lp (fun _ : ℕ => ℂ) 2)) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) :
      ‖h_FockAttPartialTrace_sliceVector x w‖ ≤ ‖x‖ * ‖w‖ := by
    have hs := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (h_FockAttPartialTrace_sliceVector x w)
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs hw
    have hle : ‖h_FockAttPartialTrace_sliceVector x w‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖w‖ ^ 2 := by
      rw [hs, ← hw.tsum_eq, ← hw.summable.tsum_mul_left]
      apply Summable.tsum_le_tsum _
        (by simpa only [h_FockAttPartialTrace_sliceVector_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (h_FockAttPartialTrace_sliceVector x w)).summable)
        (hw.summable.mul_left (‖x‖ ^ 2))
      intro n
      simp only [h_FockAttPartialTrace_sliceVector_apply]
      have h := norm_inner_le_norm (𝕜 := ℂ) x (w n)
      nlinarith [norm_nonneg (inner ℂ x (w n)), norm_nonneg x, norm_nonneg (w n)]
    nlinarith [norm_nonneg (h_FockAttPartialTrace_sliceVector x w), norm_nonneg x, norm_nonneg w,
      mul_nonneg (norm_nonneg x) (norm_nonneg w)]
  let h_FockAttPartialTrace_sliceMap (x : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) := LinearMap.mkContinuous
      { toFun := h_FockAttPartialTrace_sliceVector x
        map_add' := by intro w v; apply lp.ext; funext n; exact inner_add_right _ _ _
        map_smul' := by intro c w; apply lp.ext; funext n; exact inner_smul_right _ _ _ }
      ‖x‖ (fun w => by change ‖h_FockAttPartialTrace_sliceVector x w‖ ≤ _; exact h_FockAttPartialTrace_sliceVector_norm x w)
  have h_FockAttPartialTrace_sliceMap_tensor (x v w : (lp (fun _ : ℕ => ℂ) 2)) :
      h_FockAttPartialTrace_sliceMap x (tensor v w) = inner ℂ x v • w := by
    apply lp.ext
    funext n
    change inner ℂ x (w n • v) = inner ℂ x v * w n
    rw [inner_smul_right]
    ring
  have h_FockAttCovariance_slice_pairDisplacement (a : ℂ × ℂ) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (x : (lp (fun _ : ℕ => ℂ) 2)) :
      h_FockAttPartialTrace_sliceMap x (pairDisplacement a w) =
        displacement a.2 (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x) w) := by
    let f := (h_FockAttPartialTrace_sliceMap x).comp
      (pairDisplacement a).toContinuousLinearEquiv.toContinuousLinearMap
    let g := (displacement a.2).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x))
    have heq : f = g := h_FockAttFamilyExt_totalFamily_ext exponentialPair h_FockAttTwoMode_exponentialPair_dense f g
      (fun z => by
        change h_FockAttPartialTrace_sliceMap x (pairDisplacement a (exponentialPair z)) = _
        rw [h_FockAttCovariance_pairDisplacement_exponential, pairWeyl, h_FockAttPartialTrace_sliceMap_tensor]
        change _ = displacement a.2
          (h_FockAttPartialTrace_sliceMap ((displacement a.1).symm x) (exponentialPair z))
        rw [exponentialPair, h_FockAttPartialTrace_sliceMap_tensor, map_smul, h_FockAttCoherentBridge_displacement_exponential]
        congr 1
        rw [← h_FockAttCoherentBridge_displacement_exponential]
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (displacement a.1).inner_map_map ((displacement a.1).symm x) (exponentialVector z.1))
    exact congrArg (fun T : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2) => T w) heq
  have h_FockAttMixture_rankOne_summable {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
      Summable (fun i => InnerProductSpace.rankOne ℂ (v i) (v i)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  have h_FockAttMixture_mixture_inner {ι : Type} (v : ι → (lp (fun _ : ℕ => ℂ) 2)) (hv : Summable (fun i => ‖v i‖ ^ 2))
      (x y : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ x (mixture v y) = ∑' i, inner ℂ x (v i) * inner ℂ (v i) y := by
    let φ := (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ => ℂ) 2) y)
    have hs := (h_FockAttMixture_rankOne_summable v hv).hasSum.mapL φ
    have heq : ∀ T : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2), φ T = inner ℂ x (T y) := fun T => rfl
    calc
      inner ℂ x (mixture v y) = ∑' i, inner ℂ x
          (InnerProductSpace.rankOne ℂ (v i) (v i) y) := by
        simpa only [heq, mixture] using hs.tsum_eq.symm
      _ = _ := by
        apply tsum_congr
        intro i
        simp only [InnerProductSpace.rankOne_apply, inner_smul_right]
        ring
  have h_FockAttPartialTrace_purePartialTrace_inner (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (x y : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ x (purePartialTrace w y) = inner ℂ (h_FockAttPartialTrace_sliceMap y w) (h_FockAttPartialTrace_sliceMap x w) := by
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [purePartialTrace, h_FockAttMixture_mixture_inner _ hw.summable, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    rw [RCLike.inner_apply]
    change inner ℂ x (w n) * inner ℂ (w n) y =
      inner ℂ x (w n) * (starRingEnd ℂ) (inner ℂ y (w n))
    rw [inner_conj_symm]
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [h_FockAttPartialTrace_purePartialTrace_inner, h_FockAttCovariance_slice_pairDisplacement,
    h_FockAttCovariance_slice_pairDisplacement, LinearIsometryEquiv.inner_map_map]
  rw [← h_FockAttPartialTrace_purePartialTrace_inner]
  change inner ℂ ((displacement a.1).symm x)
    (purePartialTrace w ((displacement a.1).symm y)) =
      inner ℂ x (displacement a.1 (purePartialTrace w ((displacement a.1).symm y)))
  symm
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (displacement a.1).inner_map_map ((displacement a.1).symm x)
      (purePartialTrace w ((displacement a.1).symm y))

theorem beam_displacement (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1)
    (a : ℂ × ℂ) (w : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) :
    beamUnitary t r h (pairDisplacement a w) =
      pairDisplacement (rotate t r a) (beamUnitary t r h w) := by
  have exponential_vectors_total (v : (lp (fun _ : ℕ => ℂ) 2))
      (hv : ∀ α : ℂ, inner ℂ v (exponentialVector α) = 0) : v = 0 := by
    let h_FockAttCoherentBridge_scalarSeries (v : (lp (fun _ : ℕ => ℂ) 2)) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttCoherentBridge_scalarSeries_expansion (v : (lp (fun _ : ℕ => ℂ) 2)) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialVector z)) (h_FockAttCoherentBridge_scalarSeries v) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialVector z))
      intro n
      simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialVector, exponentialCoeff, RCLike.inner_apply]
      ring
    have hfun : (fun z : ℂ => inner ℂ v (exponentialVector z)) = 0 := funext hv
    have hs := h_FockAttCoherentBridge_scalarSeries_expansion v
    rw [hfun] at hs
    have hzero := hs.eq_zero
    apply lp.ext
    funext n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hzero
    simp only [h_FockAttCoherentBridge_scalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change (starRingEnd ℂ) (v n) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn
  have exponentialPair_total (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))
      (hv : ∀ z : ℂ × ℂ, inner ℂ v (exponentialPair z) = 0) : v = 0 := by
    let h_FockAttTwoMode_pairScalarSeries (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n =>
        inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
    have h_FockAttTwoMode_pairScalarSeries_expansion (v : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)) (α : ℂ) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponentialPair (α,z)))
          (h_FockAttTwoMode_pairScalarSeries v α) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponentialPair (α,z)))
      intro n
      simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponentialPair, h_FockAttTwoMode_tensor_apply, exponentialVector, exponentialCoeff, inner_smul_right]
      ring
    apply lp.ext
    funext n
    apply exponential_vectors_total
    intro α
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 := funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by norm_cast; exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  have h_FockAttCovariance_rotate_add (t r : ℝ) (z w : ℂ × ℂ) :
      rotate t r (z+w) = rotate t r z + rotate t r w := by
    apply Prod.ext <;> simp only [rotate, Prod.fst_add, Prod.snd_add] <;> ring
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_norm_sq (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ ^ 2 = ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    have ht := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (tensor v w)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at ht
    have hw := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hw
    rw [ht]
    simp only [h_FockAttTwoMode_tensor_apply, norm_smul, mul_pow]
    rw [hw.summable.tsum_mul_right, hw.tsum_eq, mul_comm]
  have h_FockAttTwoMode_tensor_norm (v w : (lp (fun _ : ℕ => ℂ) 2)) : ‖tensor v w‖ = ‖v‖ * ‖w‖ := by
    have hs := h_FockAttTwoMode_tensor_norm_sq v w
    nlinarith [norm_nonneg (tensor v w), norm_nonneg v, norm_nonneg w,
      mul_nonneg (norm_nonneg v) (norm_nonneg w)]
  let h_FockAttTwoMode_tensorLeft (w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun v => tensor v w
        map_add' := by intro v v'; apply lp.ext; funext n; exact smul_add (w n) v v'
        map_smul' := by
          intro c v; apply lp.ext; funext n
          exact smul_comm (w n) c v }
      ‖w‖ (fun v => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm, mul_comm])
  have h_FockAttTwoMode_tensor_smul_left (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor (c • v) w = c • tensor v w := (h_FockAttTwoMode_tensorLeft w).map_smul c v
  let h_FockAttCovariance_pairWeylScalar (a z : ℂ × ℂ) : ℂ := Complex.exp (-((‖a.1‖ ^ 2 / 2 : ℝ) : ℂ) - (starRingEnd ℂ) a.1 * z.1) *
    Complex.exp (-((‖a.2‖ ^ 2 / 2 : ℝ) : ℂ) - (starRingEnd ℂ) a.2 * z.2)
  let h_FockAttTwoMode_tensorRight (v : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := LinearMap.mkContinuous
      { toFun := fun w => tensor v w
        map_add' := by intro w w'; apply lp.ext; funext n; exact add_smul (w n) (w' n) v
        map_smul' := by
          intro c w; apply lp.ext; funext n
          exact mul_smul c (w n) v }
      ‖v‖ (fun w => by change ‖tensor v w‖ ≤ _; rw [h_FockAttTwoMode_tensor_norm])
  have h_FockAttTwoMode_tensor_smul_right (c : ℂ) (v w : (lp (fun _ : ℕ => ℂ) 2)) : tensor v (c • w) = c • tensor v w := (h_FockAttTwoMode_tensorRight v).map_smul c w
  have h_FockAttCovariance_pairWeyl_scalar (a z : ℂ × ℂ) :
      pairWeyl a z = h_FockAttCovariance_pairWeylScalar a z • exponentialPair (a+z) := by
    simp only [pairWeyl, weylVector, h_FockAttTwoMode_tensor_smul_left, h_FockAttTwoMode_tensor_smul_right,
      smul_smul, h_FockAttCovariance_pairWeylScalar, exponentialPair, Prod.fst_add, Prod.snd_add]
  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttCovariance_pairWeyl_dense (a : ℂ × ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (pairWeyl a)) := by
    have hspan : (Submodule.span ℂ (Set.range (pairWeyl a))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun z => by
          have hmem : pairWeyl a (z.1-a.1,z.2-a.2) ∈ Submodule.span ℂ (Set.range (pairWeyl a)) := Submodule.subset_span ⟨(z.1-a.1,z.2-a.2), rfl⟩
          have hi := Submodule.inner_left_of_mem_orthogonal hmem hv
          have h1 : a.1 + (z.1-a.1) = z.1 := by ring
          have h2 : a.2 + (z.2-a.2) = z.2 := by ring
          simp only [pairWeyl, weylVector, h_FockAttTwoMode_tensor_smul_left, h_FockAttTwoMode_tensor_smul_right,
            inner_smul_right, h1, h2] at hi
          exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (Complex.exp_ne_zero _))).resolve_left
            (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (pairWeyl a)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  let h_FockAttFrameExtension_gramUnitary {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) : H ≃ₗᵢ[ℂ] H := (LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)])
  have h_FockAttFrameExtension_gramUnitary_apply {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (v w : ι → H)
      (hgram : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j))
      (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (hw : DenseRange (Finsupp.linearCombination ℂ w)) (i : ι) :
      h_FockAttFrameExtension_gramUnitary v w hgram hv hw (v i) = w i := by
    have hh := LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ι →₀ ℂ))
      (Finsupp.linearCombination ℂ v) (Finsupp.linearCombination ℂ w) hv hw
      (by
        intro c
        change ‖Finsupp.linearCombination ℂ w c‖ = ‖Finsupp.linearCombination ℂ v c‖
        have hs : inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w c) =
            inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v c) := by
          classical
          simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
            inner_smul_left, inner_smul_right, hgram]
        rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
        have hsq : ‖Finsupp.linearCombination ℂ w c‖ ^ 2 =
            ‖Finsupp.linearCombination ℂ v c‖ ^ 2 := by exact_mod_cast hs
        nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w c),
          norm_nonneg (Finsupp.linearCombination ℂ v c)]) (Finsupp.single i (1 : ℂ))
    simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul, h_FockAttFrameExtension_gramUnitary] using hh
  have h_FockAttTwoMode_tensor_inner (v w v' w' : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ (tensor v w) (tensor v' w') = inner ℂ v v' * inner ℂ w w' := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum w w']
    simp only [h_FockAttTwoMode_tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
    rw [mul_pow]
    field_simp
    rw [hsq]
    ring
  have h_FockAttCoherentBridge_exponential_inner (α β : ℂ) :
      inner ℂ (exponentialVector α) (exponentialVector β) =
        Complex.exp ((starRingEnd ℂ) α * β) := by
    rw [lp.inner_eq_tsum]
    simp only [exponentialVector, h_FockAttCoherentBridge_exponentialCoeff_inner]
    simpa only [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq
  have h_FockAttCoherentBridge_weyl_gram (α β γ : ℂ) :
      inner ℂ (weylVector α β) (weylVector α γ) =
        inner ℂ (exponentialVector β) (exponentialVector γ) := by
    have haa : (starRingEnd ℂ) α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul]; norm_cast
    simp only [weylVector, inner_smul_left, inner_smul_right, h_FockAttCoherentBridge_exponential_inner,
      ← Complex.exp_conj, map_sub, map_neg, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add]
    push_cast
    push_cast at haa
    linear_combination haa
  have h_FockAttCoherentBridge_weyl_dense (α : ℂ) :
      DenseRange (Finsupp.linearCombination ℂ (weylVector α)) := by
    have hspan : (Submodule.span ℂ (Set.range (weylVector α))).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun β => by
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) := Submodule.subset_span ⟨β - α, rfl⟩
          have hinner := Submodule.inner_left_of_mem_orthogonal hmem hv
          have heq : α + (β - α) = β := by ring
          simp only [weylVector, inner_smul_right, heq] at hinner
          exact (mul_eq_zero.mp hinner).resolve_left (Complex.exp_ne_zero _))
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ (weylVector α)))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_exponential_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialVector) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponential_vectors_total v (fun α => by
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) := Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
  have h_FockAttCoherentBridge_displacement_exponential (α β : ℂ) :
      displacement α (exponentialVector β) = weylVector α β := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α) β
  have h_FockAttCovariance_pairWeyl_gram (a z w : ℂ × ℂ) :
      inner ℂ (pairWeyl a z) (pairWeyl a w) =
        inner ℂ (exponentialPair z) (exponentialPair w) := by
    rw [pairWeyl, pairWeyl, h_FockAttTwoMode_tensor_inner]
    have h1 := (displacement a.1).inner_map_map (exponentialVector z.1) (exponentialVector w.1)
    have h2 := (displacement a.2).inner_map_map (exponentialVector z.2) (exponentialVector w.2)
    simp only [h_FockAttCoherentBridge_displacement_exponential] at h1 h2
    rw [h1, h2, exponentialPair, exponentialPair, h_FockAttTwoMode_tensor_inner]
  have h_FockAttCovariance_pairDisplacement_exponential (a z : ℂ × ℂ) :
      pairDisplacement a (exponentialPair z) = pairWeyl a z := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttCovariance_pairWeyl_gram a) h_FockAttTwoMode_exponentialPair_dense (h_FockAttCovariance_pairWeyl_dense a) z
  have h_FockAttFamilyExt_totalFamily_ext {ι H K : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup K] [NormedSpace ℂ K] (v : ι → H) (hv : DenseRange (Finsupp.linearCombination ℂ v))
      (f g : H →L[ℂ] K) (h : ∀ i, f (v i) = g (v i)) : f = g := by
    apply ContinuousLinearMap.ext
    intro x
    refine hv.induction (P := fun y => f y = g y) ?_ ?_ x
    · rintro y ⟨c, rfl⟩
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, h]
    · exact isClosed_eq f.continuous g.continuous
  have h_FockAttCovariance_rotate_inner_polynomial (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z w : ℂ × ℂ) :
      (starRingEnd ℂ) (rotate t r z).1 * (rotate t r w).1 +
        (starRingEnd ℂ) (rotate t r z).2 * (rotate t r w).2 =
      (starRingEnd ℂ) z.1 * w.1 + (starRingEnd ℂ) z.2 * w.2 := by
    have hc : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast h
    simp only [rotate, map_sub, map_add, map_mul, Complex.conj_ofReal]
    linear_combination hc * ((starRingEnd ℂ) z.1 * w.1 + (starRingEnd ℂ) z.2 * w.2)
  have h_FockAttCovariance_rotate_norm_sq (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (a : ℂ × ℂ) :
      ‖(rotate t r a).1‖ ^ 2 + ‖(rotate t r a).2‖ ^ 2 = ‖a.1‖ ^ 2 + ‖a.2‖ ^ 2 := by
    have hs := h_FockAttCovariance_rotate_inner_polynomial t r h a a
    simp only [RCLike.conj_mul] at hs
    norm_cast at hs
  have h_FockAttCovariance_pairWeylScalar_rotate (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (a z : ℂ × ℂ) :
      h_FockAttCovariance_pairWeylScalar (rotate t r a) (rotate t r z) = h_FockAttCovariance_pairWeylScalar a z := by
    simp only [h_FockAttCovariance_pairWeylScalar, ← Complex.exp_add]
    congr 1
    have hn : (((‖(rotate t r a).1‖ ^ 2 + ‖(rotate t r a).2‖ ^ 2 : ℝ)) : ℂ) =
        ((‖a.1‖ ^ 2 + ‖a.2‖ ^ 2 : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) (h_FockAttCovariance_rotate_norm_sq t r h a)
    have hi := h_FockAttCovariance_rotate_inner_polynomial t r h a z
    push_cast at hn ⊢
    linear_combination -hn / 2 - hi
  have h_FockAttTwoMode_exponentialPair_inner (z w : ℂ × ℂ) :
      inner ℂ (exponentialPair z) (exponentialPair w) =
        Complex.exp ((starRingEnd ℂ) z.1 * w.1 + (starRingEnd ℂ) z.2 * w.2) := by
    rw [exponentialPair, exponentialPair, h_FockAttTwoMode_tensor_inner, h_FockAttCoherentBridge_exponential_inner, h_FockAttCoherentBridge_exponential_inner,
      Complex.exp_add]
  have h_FockAttTwoMode_rotate_gram (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z w : ℂ × ℂ) :
      inner ℂ (exponentialPair (rotate t r z)) (exponentialPair (rotate t r w)) =
        inner ℂ (exponentialPair z) (exponentialPair w) := by
    rw [h_FockAttTwoMode_exponentialPair_inner, h_FockAttTwoMode_exponentialPair_inner]
    congr 1
    have hc : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast h
    simp only [rotate, map_sub, map_add, map_mul, Complex.conj_ofReal]
    linear_combination hc * ((starRingEnd ℂ) z.1 * w.1 + (starRingEnd ℂ) z.2 * w.2)
  have h_FockAttTwoMode_rotate_inverse (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
      rotate t (-r) (rotate t r z) = z := by
    have hc : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast h
    apply Prod.ext
    · simp only [rotate, Complex.ofReal_neg]
      linear_combination hc * z.1
    · simp only [rotate, Complex.ofReal_neg]
      linear_combination hc * z.2
  have h_FockAttTwoMode_rotate_surjective (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) :
      Function.Surjective (rotate t r) := by
    intro z
    refine ⟨rotate t (-r) z, ?_⟩
    simpa using h_FockAttTwoMode_rotate_inverse t (-r) (by simpa using h) z
  have h_FockAttTwoMode_rotated_dense (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) :
      DenseRange (Finsupp.linearCombination ℂ (exponentialPair ∘ rotate t r)) := by
    have heq : Set.range (exponentialPair ∘ rotate t r) = Set.range exponentialPair := by
        apply Set.ext
        intro v
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨rotate t r z, rfl⟩
        · rintro ⟨z, rfl⟩
          obtain ⟨w, hw⟩ := h_FockAttTwoMode_rotate_surjective t r h z
          exact ⟨w, by simp [Function.comp_def, hw]⟩
    have hrange := Finsupp.range_linearCombination (R := ℂ)
        (v := exponentialPair ∘ rotate t r)
    have hbase := Finsupp.range_linearCombination (R := ℂ) (v := exponentialPair)
    change Dense (Set.range (Finsupp.linearCombination ℂ (exponentialPair ∘ rotate t r)))
    have heq' : Set.range (Finsupp.linearCombination ℂ (exponentialPair ∘ rotate t r)) =
        Set.range (Finsupp.linearCombination ℂ exponentialPair) := by
      exact congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2)))
        (hrange.trans ((congrArg (Submodule.span ℂ) heq).trans hbase.symm))
    rw [heq']
    exact h_FockAttTwoMode_exponentialPair_dense
  have h_FockAttTwoMode_beamUnitary_exponential (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
      beamUnitary t r h (exponentialPair z) = exponentialPair (rotate t r z) := by
    exact h_FockAttFrameExtension_gramUnitary_apply _ _ (h_FockAttTwoMode_rotate_gram t r h) h_FockAttTwoMode_exponentialPair_dense (h_FockAttTwoMode_rotated_dense t r h) z
  let f := (beamUnitary t r h).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (pairDisplacement a).toContinuousLinearEquiv.toContinuousLinearMap
  let g := (pairDisplacement (rotate t r a)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (beamUnitary t r h).toContinuousLinearEquiv.toContinuousLinearMap
  have heq : f = g := h_FockAttFamilyExt_totalFamily_ext exponentialPair h_FockAttTwoMode_exponentialPair_dense f g
    (fun z => by
      change beamUnitary t r h (pairDisplacement a (exponentialPair z)) =
        pairDisplacement (rotate t r a) (beamUnitary t r h (exponentialPair z))
      rw [h_FockAttCovariance_pairDisplacement_exponential, h_FockAttCovariance_pairWeyl_scalar, map_smul, h_FockAttTwoMode_beamUnitary_exponential,
        h_FockAttTwoMode_beamUnitary_exponential, h_FockAttCovariance_pairDisplacement_exponential, h_FockAttCovariance_pairWeyl_scalar,
        h_FockAttCovariance_pairWeylScalar_rotate t r h a z, h_FockAttCovariance_rotate_add])
  exact congrArg (fun T : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) →L[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => T w) heq

end D5.S3.Quantum.QuantumChannels.FockAttenuator.DisplacementCovariance
