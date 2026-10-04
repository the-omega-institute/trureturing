/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: BeamSplitter on the full bosonic Hilbert space. -/
/-
beamUnitary_fock:
  proof_shape: content
  escape_witness: Conclusion witness: identification of the completed-space unitary action with the normalized two-variable creation polynomial at every occupation, using totalness and the constructed rotation.
admission_basis: escape-witness
Direct frozen dependencies: none on the immutable origin/dev baseline.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter


def exponentialCoeff (α : ℂ) (n : ℕ) : ℂ := by
  exact α ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)

def exponentialVector (α : ℂ) : (lp (fun _ : ℕ => ℂ) 2) := by
  have h_FockAttCoherentBridge_exponentialCoeff_norm_sq (α : ℂ) (n : ℕ) :
      ‖exponentialCoeff α n‖ ^ 2 = (‖α‖ ^ 2) ^ n / (n.factorial : ℝ) := by
    simp only [exponentialCoeff, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg n.factorial), pow_right_comm ‖α‖ n 2]
  exact ⟨exponentialCoeff α, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs := NormedSpace.expSeries_div_hasSum_exp (‖α‖ ^ 2)
    apply hs.summable.congr
    intro n
    exact (h_FockAttCoherentBridge_exponentialCoeff_norm_sq α n).symm⟩

def weylVector (α β : ℂ) : (lp (fun _ : ℕ => ℂ) 2) := by
  exact Complex.exp (-((‖α‖ ^ 2 / 2 : ℝ) : ℂ) - (starRingEnd ℂ) α * β) •
      exponentialVector (α + β)

def displacement (α : ℂ) : (lp (fun _ : ℕ => ℂ) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => ℂ) 2) := by
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
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hvn : (starRingEnd ℂ) (v n) = 0 := (div_eq_zero_iff.mp hc).resolve_right hsqrt
    simpa using hvn

  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
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
          have hmem : weylVector α (β - α) ∈ Submodule.span ℂ (Set.range (weylVector α)) :=
            Submodule.subset_span ⟨β - α, rfl⟩
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
          have hmem : exponentialVector α ∈ Submodule.span ℂ (Set.range exponentialVector) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialVector))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => ℂ) 2) => (K : Set (lp (fun _ : ℕ => ℂ) 2))) hspan
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
  exact h_FockAttFrameExtension_gramUnitary exponentialVector (weylVector α)
      (h_FockAttCoherentBridge_weyl_gram α) h_FockAttCoherentBridge_exponential_dense (h_FockAttCoherentBridge_weyl_dense α)

def coherentCoeff (α : ℂ) (n : ℕ) : ℂ := by
  exact (Real.exp (-‖α‖ ^ 2 / 2) : ℂ) * α ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)

def coherent (α : ℂ) : (lp (fun _ : ℕ => ℂ) 2) := by
  have h_FockAttProbe_coherent_norm_sq (α : ℂ) (n : ℕ) :
      ‖coherentCoeff α n‖ ^ 2 =
        Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * (‖α‖ ^ 2) ^ n / (n.factorial : ℝ) := by
    rw [coherentCoeff, norm_div, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n.factorial), pow_right_comm ‖α‖ n 2]
  have h_FockAttProbe_coherent_hasSum (α : ℂ) :
      HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2) 1 := by
    have hseries : HasSum (fun n : ℕ => (‖α‖ ^ 2) ^ n / (n.factorial : ℝ))
        (Real.exp (‖α‖ ^ 2)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (‖α‖ ^ 2))
    have hs := hseries.mul_left
      (Real.exp (-‖α‖ ^ 2 / 2) ^ 2)
    have he : Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2) = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have hs' : HasSum (fun n : ℕ => ‖coherentCoeff α n‖ ^ 2)
        (Real.exp (-‖α‖ ^ 2 / 2) ^ 2 * Real.exp (‖α‖ ^ 2)) :=
      HasSum.congr_fun hs (fun n => by rw [h_FockAttProbe_coherent_norm_sq]; ring)
    rwa [he] at hs'
  exact ⟨coherentCoeff α, memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (h_FockAttProbe_coherent_hasSum α).summable)⟩


def tensor (v w : (lp (fun _ : ℕ => ℂ) 2)) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  exact ⟨fun n => w n • v, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) w
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    exact (hs.summable.mul_right (‖v‖ ^ 2)).congr (fun n => by rw [norm_smul, mul_pow])⟩

def exponentialPair (z : ℂ × ℂ) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  exact tensor (exponentialVector z.1) (exponentialVector z.2)

def rotate (t r : ℝ) (z : ℂ × ℂ) : ℂ × ℂ := by
  exact ((t : ℂ) * z.1 - (r : ℂ) * z.2, (r : ℂ) * z.1 + (t : ℂ) * z.2)

def beamUnitary (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
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
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
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
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 :=
      funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
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
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
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
    have heq : Set.range (exponentialPair ∘ rotate t r) = Set.range exponentialPair :=
      by
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
  exact h_FockAttFrameExtension_gramUnitary exponentialPair (exponentialPair ∘ rotate t r)
      (h_FockAttTwoMode_rotate_gram t r h) h_FockAttTwoMode_exponentialPair_dense (h_FockAttTwoMode_rotated_dense t r h)

def beamSplitter (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) ≃ₗᵢ[ℂ] (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  exact beamUnitary (Real.sqrt η) (Real.sqrt (1 - η)) (by
      rw [Real.sq_sqrt hη.1, Real.sq_sqrt (by linarith [hη.2])]
      ring)

def fockPair (m n : ℕ) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  exact tensor (h_FockAttTwoMode_fock m) (h_FockAttTwoMode_fock n)

def fockExpansion (t r : ℝ) (m n : ℕ) : (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) := by
  exact ∑ i : Fin (m+1), ∑ j : Fin (n+1),
      (((m.choose i : ℝ) * (n.choose j : ℝ) * t ^ (i : ℕ) * r ^ (m-i) *
          (-r) ^ (j : ℕ) * t ^ (n-j) *
          Real.sqrt ((i+j : ℕ).factorial : ℝ) *
          Real.sqrt ((m-i+(n-j) : ℕ).factorial : ℝ) /
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) •
        fockPair (i+j) (m-i+(n-j))

theorem beamUnitary_fock (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (m n : ℕ) :
    beamUnitary t r h (fockPair m n) = fockExpansion t r m n := by
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
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
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
    have hfun : (fun z : ℂ => inner ℂ v (exponentialPair (α,z))) = 0 :=
      funext (fun z => hv (α,z))
    have hs := h_FockAttTwoMode_pairScalarSeries_expansion v α
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [h_FockAttTwoMode_pairScalarSeries, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponentialVector α) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hsqrt : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hsqrt

  have h_FockAttTwoMode_tensor_apply (v w : (lp (fun _ : ℕ => ℂ) 2)) (n : ℕ) : tensor v w n = w n • v := rfl
  have h_FockAttTwoMode_tensor_inner (v w v' w' : (lp (fun _ : ℕ => ℂ) 2)) :
      inner ℂ (tensor v w) (tensor v' w') = inner ℂ v v' * inner ℂ w w' := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum w w']
    simp only [h_FockAttTwoMode_tensor_apply, inner_smul_left, inner_smul_right, RCLike.inner_apply]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  let h_FockAttTwoMode_fock (n : ℕ) : (lp (fun _ : ℕ => ℂ) 2) := lp.single 2 n 1
  have h_FockAttTwoMode_exponential_fock_inner (α : ℂ) (m : ℕ) :
      inner ℂ (exponentialVector α) (h_FockAttTwoMode_fock m) =
        (starRingEnd ℂ) α ^ m / (Real.sqrt (m.factorial : ℝ) : ℂ) := by
    simp only [h_FockAttTwoMode_fock, lp.inner_single_right, RCLike.inner_apply, one_mul,
      exponentialVector, exponentialCoeff, map_div₀, map_pow, Complex.conj_ofReal]
  have h_FockAttTwoMode_exponentialPair_fock_inner (z : ℂ × ℂ) (m n : ℕ) :
      inner ℂ (exponentialPair z) (fockPair m n) =
        ((starRingEnd ℂ) z.1 ^ m * (starRingEnd ℂ) z.2 ^ n) /
          ((Real.sqrt (m.factorial : ℝ) : ℂ) * (Real.sqrt (n.factorial : ℝ) : ℂ)) := by
    rw [exponentialPair, fockPair, h_FockAttTwoMode_tensor_inner, h_FockAttTwoMode_exponential_fock_inner, h_FockAttTwoMode_exponential_fock_inner]
    ring
  have h_FockAttTwoMode_rotate_inverse (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
      rotate t (-r) (rotate t r z) = z := by
    have hc : (t : ℂ) ^ 2 + (r : ℂ) ^ 2 = 1 := by exact_mod_cast h
    apply Prod.ext
    · simp only [rotate, Complex.ofReal_neg]
      linear_combination hc * z.1
    · simp only [rotate, Complex.ofReal_neg]
      linear_combination hc * z.2
  have h_FockAttTwoMode_exponentialPair_dense :
      DenseRange (Finsupp.linearCombination ℂ exponentialPair) := by
    have hspan : (Submodule.span ℂ (Set.range exponentialPair)).topologicalClosure = ⊤ := by
      apply Submodule.topologicalClosure_eq_top_iff.mpr
      apply le_antisymm
      · intro v hv
        have hzero : v = 0 := exponentialPair_total v (fun α => by
          have hmem : exponentialPair α ∈ Submodule.span ℂ (Set.range exponentialPair) :=
            Submodule.subset_span ⟨α, rfl⟩
          exact Submodule.inner_left_of_mem_orthogonal hmem hv)
        simp [hzero]
      · exact bot_le
    rw [← Finsupp.range_linearCombination] at hspan
    change Dense (Set.range (Finsupp.linearCombination ℂ exponentialPair))
    rw [dense_iff_closure_eq]
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
      congrArg (fun K : Submodule ℂ (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2) => (K : Set (lp (fun _ : ℕ => (lp (fun _ : ℕ => ℂ) 2)) 2))) hspan
  have h_FockAttCoherentBridge_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
      inner ℂ (exponentialCoeff α n) (exponentialCoeff β n) =
        ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (Nat.cast_nonneg _)
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
  have h_FockAttTwoMode_rotate_surjective (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) :
      Function.Surjective (rotate t r) := by
    intro z
    refine ⟨rotate t (-r) z, ?_⟩
    simpa using h_FockAttTwoMode_rotate_inverse t (-r) (by simpa using h) z
  have h_FockAttTwoMode_rotated_dense (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) :
      DenseRange (Finsupp.linearCombination ℂ (exponentialPair ∘ rotate t r)) := by
    have heq : Set.range (exponentialPair ∘ rotate t r) = Set.range exponentialPair :=
      by
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
  have h_FockAttTwoMode_beamUnitary_symm_exponential (t r : ℝ) (h : t ^ 2 + r ^ 2 = 1) (z : ℂ × ℂ) :
      (beamUnitary t r h).symm (exponentialPair z) = exponentialPair (rotate t (-r) z) := by
    apply (beamUnitary t r h).injective
    rw [LinearIsometryEquiv.apply_symm_apply, h_FockAttTwoMode_beamUnitary_exponential]
    congr 1
    simpa using (h_FockAttTwoMode_rotate_inverse t (-r) (by simpa using h) z).symm
  have h_FockAttTwoMode_sqrt_factorial_ne_zero (m : ℕ) :
      (Real.sqrt (m.factorial : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    exact (Real.sqrt_pos.mpr (by positivity : 0 < (m.factorial : ℝ))).ne'
  have h_FockAttTwoMode_fockExpansion_inner (t r : ℝ) (m n : ℕ) (z : ℂ × ℂ) :
      inner ℂ (exponentialPair z) (fockExpansion t r m n) =
        (((t : ℂ) * (starRingEnd ℂ) z.1 + (r : ℂ) * (starRingEnd ℂ) z.2) ^ m *
          ((-r : ℂ) * (starRingEnd ℂ) z.1 + (t : ℂ) * (starRingEnd ℂ) z.2) ^ n) /
          ((Real.sqrt (m.factorial : ℝ) : ℂ) * (Real.sqrt (n.factorial : ℝ) : ℂ)) := by
    simp only [fockExpansion, inner_sum, inner_smul_right, h_FockAttTwoMode_exponentialPair_fock_inner]
    have hterm (i : Fin (m+1)) (j : Fin (n+1)) :
        ((((m.choose i : ℝ) * (n.choose j : ℝ) * t ^ (i : ℕ) * r ^ (m-i) *
          (-r) ^ (j : ℕ) * t ^ (n-j) * Real.sqrt ((i+j : ℕ).factorial : ℝ) *
          Real.sqrt ((m-i+(n-j) : ℕ).factorial : ℝ) /
          (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) : ℝ) : ℂ) *
         (((starRingEnd ℂ) z.1 ^ (i+j : ℕ) * (starRingEnd ℂ) z.2 ^ (m-i+(n-j))) /
          ((Real.sqrt ((i+j : ℕ).factorial : ℝ) : ℂ) *
            (Real.sqrt ((m-i+(n-j) : ℕ).factorial : ℝ) : ℂ)))) =
        ((((t : ℂ) * (starRingEnd ℂ) z.1) ^ (i : ℕ) *
          ((r : ℂ) * (starRingEnd ℂ) z.2) ^ (m-i) * (m.choose i : ℂ)) *
         (((-r : ℂ) * (starRingEnd ℂ) z.1) ^ (j : ℕ) *
          ((t : ℂ) * (starRingEnd ℂ) z.2) ^ (n-j) * (n.choose j : ℂ))) /
          ((Real.sqrt (m.factorial : ℝ) : ℂ) * (Real.sqrt (n.factorial : ℝ) : ℂ)) := by
      push_cast
      have hm := h_FockAttTwoMode_sqrt_factorial_ne_zero m
      have hn := h_FockAttTwoMode_sqrt_factorial_ne_zero n
      have hk := h_FockAttTwoMode_sqrt_factorial_ne_zero (i+j)
      have hl := h_FockAttTwoMode_sqrt_factorial_ne_zero (m-i+(n-j))
      field_simp [hm, hn, hk, hl]
      simp only [mul_pow, pow_add]
      ring
    simp_rw [hterm]
    simp_rw [← Finset.sum_div]
    have hi : ∑ i : Fin (m+1),
        ((t : ℂ) * (starRingEnd ℂ) z.1) ^ (i : ℕ) *
        ((r : ℂ) * (starRingEnd ℂ) z.2) ^ (m-i) * (m.choose i : ℂ) =
        ((t : ℂ) * (starRingEnd ℂ) z.1 + (r : ℂ) * (starRingEnd ℂ) z.2) ^ m := by
      exact (Fin.sum_univ_eq_sum_range (fun i : ℕ =>
        ((t : ℂ) * (starRingEnd ℂ) z.1) ^ i *
        ((r : ℂ) * (starRingEnd ℂ) z.2) ^ (m-i) * (m.choose i : ℂ)) (m+1)).trans
        (add_pow _ _ m).symm
    have hj : ∑ j : Fin (n+1),
        ((-r : ℂ) * (starRingEnd ℂ) z.1) ^ (j : ℕ) *
        ((t : ℂ) * (starRingEnd ℂ) z.2) ^ (n-j) * (n.choose j : ℂ) =
        ((-r : ℂ) * (starRingEnd ℂ) z.1 + (t : ℂ) * (starRingEnd ℂ) z.2) ^ n := by
      exact (Fin.sum_univ_eq_sum_range (fun j : ℕ =>
        ((-r : ℂ) * (starRingEnd ℂ) z.1) ^ j *
        ((t : ℂ) * (starRingEnd ℂ) z.2) ^ (n-j) * (n.choose j : ℂ)) (n+1)).trans
        (add_pow _ _ n).symm
    rw [← hi, ← hj, Finset.sum_mul_sum]
  apply sub_eq_zero.mp
  apply exponentialPair_total
  intro z
  suffices hx : inner ℂ (exponentialPair z)
      (beamUnitary t r h (fockPair m n) - fockExpansion t r m n) = 0 by
    have hc := congrArg (starRingEnd ℂ) hx
    simpa only [inner_conj_symm, map_zero] using hc
  have hinner : inner ℂ (exponentialPair z) (beamUnitary t r h (fockPair m n)) =
      inner ℂ ((beamUnitary t r h).symm (exponentialPair z)) (fockPair m n) := by
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (beamUnitary t r h).inner_map_map
        ((beamUnitary t r h).symm (exponentialPair z)) (fockPair m n)
  rw [inner_sub_right, hinner]
  rw [h_FockAttTwoMode_beamUnitary_symm_exponential, h_FockAttTwoMode_exponentialPair_fock_inner, h_FockAttTwoMode_fockExpansion_inner]
  simp only [rotate, map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.ofReal_neg, map_neg]
  ring

end D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
