/- GID: D5/S3/Quantum/PassiveFockModel
   generality: I
   mirror-B: D5/B/S3/Quantum/PassiveFockModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-mode bosonic Fock space and passive evolution. -/
/-
admission_basis: escape-witness
Direct frozen dependencies use declaration identities from the merged baseline report.
headTensor_inner: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: PassiveFockModel.exponential_inner, ResolvedCountWeakValue.created_inner.
single_exponentialCoeff_inner: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d.
  Consumers: PassiveFockModel.single_exponential_inner, ResolvedCountWeakValue.numberExponential_inner.
single_exponential_inner: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.exponential_inner, ResolvedCountWeakValue.created_inner.
exponential_inner: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.passive_span_norm, PassiveFockModel.vacuum_exponential_inner, ResolvedCountWeakValue.created_inner, ResolvedCountWeakValue.exponential_created_resolved, ResolvedCountWeakValue.exponential_ne_zero.
exponential_total: proof_shape: content; escape_witness: exponential_total.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.exponential_dense, PassiveFockModel.gamma_onePhoton, ResolvedCountWeakValue.gamma_created.
exponential_dense: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.gamma, PassiveFockModel.gamma_exponential, PassiveFockModel.passive_exponential_dense.
passive_exponential_dense: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.gamma, PassiveFockModel.gamma_exponential.
passive_span_norm: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.gamma, PassiveFockModel.gamma_exponential.
gamma_exponential: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.gamma_coherent, PassiveFockModel.gamma_onePhoton, ResolvedCountWeakValue.gamma_created.
gamma_coherent: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.coherentProbeDomain, ResolvedCountWeakValue.M2, ResolvedCountWeakValue.coherentFinal_eq, ResolvedCountWeakValue.coherent_number_numerator.
single_number_exponential_mem: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.numberExponential.
coherent_number_domain: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.coherentProbeDomain.
vacuum_exponential_inner: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.onePhoton_exponential_inner, ResolvedCountWeakValue.M3.
onePhoton_exponential_inner: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.gamma_onePhoton.
gamma_onePhoton: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.singleProbeDomain, ResolvedCountWeakValue.M3, ResolvedCountWeakValue.singleFinal_eq.
onePhoton_apply: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.onePhoton_number_domain.
onePhoton_number_domain: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.singleProbeDomain.
projector_weight: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: none.
  Consumers: PassiveFockModel.coherentWeakValue, PassiveFockModel.singleWeakValue, ResolvedCountWeakValue.M2, ResolvedCountWeakValue.M3.
coherentProbeDomain: proof_shape: bind-only; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.coherentWeakValue, ResolvedCountWeakValue.M2.
singleProbeDomain: proof_shape: content; escape_witness: none.
  Direct frozen dependencies: D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialCoeff sha256:cb182c9ed363d82cfb0d430c863be611cfb70e76a948f78891550d474d0afa6d; D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter.exponentialVector sha256:418ab9c15b2602b221e2546f26ebe3b3556b537c07e53e72f2e1dc326149453f.
  Consumers: PassiveFockModel.singleWeakValue, ResolvedCountWeakValue.M3.
The occupation-space definitions retain the literal representation fixed in #17772.
The theorem exponential_total uses mode induction and analytic coefficient uniqueness.
The imported BeamSplitter module has generality I; this module has the same tag.
The four-slot escape audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/18878.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace D5.S3.Quantum.PassiveFockModel

structure Hilbert where
  Carrier : Type
  normed : NormedAddCommGroup Carrier
  inner : InnerProductSpace ℂ Carrier
  complete : CompleteSpace Carrier
attribute [instance] Hilbert.normed Hilbert.inner Hilbert.complete

abbrev hilbertStep (H : Hilbert) : Hilbert where
  Carrier := lp (fun _ : ℕ => H.Carrier) 2
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance

@[reducible] def fockHilbert : ℕ → Hilbert
  | 0 => ⟨ℂ, inferInstance, inferInstance, inferInstance⟩
  | k+1 => hilbertStep (fockHilbert k)

abbrev Fock (k : ℕ) := (fockHilbert k).Carrier

abbrev Modes (k : ℕ) := EuclideanSpace ℂ (Fin k)

abbrev Passive (k : ℕ) := Modes k ≃ₗᵢ[ℂ] Modes k

def tail {k : ℕ} (β : Modes (k+1)) : Modes k := WithLp.toLp 2 (fun i => β i.succ)

private def cons {k : ℕ} (a : ℂ) (β : Modes k) : Modes (k+1) :=
  WithLp.toLp 2 (Fin.cons a β)

def headTensor {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u : lp (fun _ : ℕ => ℂ) 2) (v : H) : lp (fun _ : ℕ => H) 2 :=
  ⟨fun n => u n • v, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) u
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    exact (hs.summable.mul_right (‖v‖ ^ 2)).congr
      (fun n => by rw [norm_smul, mul_pow])⟩

lemma headTensor_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u u' : lp (fun _ : ℕ => ℂ) 2) (v v' : H) :
    inner ℂ (headTensor u v) (headTensor u' v') = inner ℂ u u' * inner ℂ v v' := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum u u']
  simp only [headTensor, inner_smul_left, inner_smul_right, RCLike.inner_apply]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  ring

def exponential : (k : ℕ) → Modes k → Fock k
  | 0, _ => (1 : ℂ)
  | k+1, β => headTensor (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector (β 0)) (exponential k (tail β))

def coherent (k : ℕ) (β : Modes k) : Fock k :=
  (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) • exponential k β


lemma single_exponentialCoeff_inner (α β : ℂ) (n : ℕ) :
    inner ℂ (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff α n) (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff β n) =
      ((starRingEnd ℂ) α * β) ^ n / (n.factorial : ℂ) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
  have hsq : (Real.sqrt (n.factorial : ℝ) : ℂ) ^ 2 = (n.factorial : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  simp only [D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff, RCLike.inner_apply, map_div₀, map_pow, Complex.conj_ofReal]
  rw [mul_pow]
  field_simp
  rw [hsq]
  ring

lemma single_exponential_inner (α β : ℂ) :
    inner ℂ (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector α) (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector β) =
      Complex.exp ((starRingEnd ℂ) α * β) := by
  rw [lp.inner_eq_tsum]
  simp only [D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector, single_exponentialCoeff_inner]
  simpa only [Complex.exp_eq_exp_ℂ] using
    (NormedSpace.expSeries_div_hasSum_exp ((starRingEnd ℂ) α * β)).tsum_eq

lemma exponential_inner (k : ℕ) (β γ : Modes k) :
    inner ℂ (exponential k β) (exponential k γ) = Complex.exp (inner ℂ β γ) := by
  induction k with
  | zero => simp [exponential, PiLp.inner_apply, RCLike.inner_apply]
  | succ k ih =>
    rw [exponential, exponential, headTensor_inner, single_exponential_inner, ih,
      ← Complex.exp_add]
    congr 1
    simp [PiLp.inner_apply, Fin.sum_univ_succ, tail, RCLike.inner_apply, mul_comm]

lemma exponential_total : ∀ k, ∀ v : Fock k,
    (∀ β, inner ℂ v (exponential k β) = 0) → v = 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have h := hv 0
    simpa [exponential, RCLike.inner_apply] using h
  | succ k ih =>
    intro v hv
    let series (β : Modes k) : FormalMultilinearSeries ℂ ℂ ℂ :=
      FormalMultilinearSeries.ofScalars ℂ
        (fun n => inner ℂ (v n) (exponential k β) / (Real.sqrt (n.factorial : ℝ) : ℂ))
    have expansion (β : Modes k) :
        HasFPowerSeriesAt (fun z : ℂ => inner ℂ v (exponential (k+1) (cons z β)))
          (series β) 0 := by
      apply hasFPowerSeriesAt_iff.mpr
      filter_upwards [] with z
      simp only [zero_add]
      apply HasSum.congr_fun (lp.hasSum_inner v (exponential (k+1) (cons z β)))
      intro n
      simp only [series, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
        exponential, headTensor, cons, tail, Fin.cons_zero, Fin.cons_succ,
        WithLp.ofLp_toLp, inner_smul_right,
        D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector,
        D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff]
      ring
    apply lp.ext
    funext n
    apply ih
    intro β
    have hfun : (fun z : ℂ => inner ℂ v (exponential (k+1) (cons z β))) = 0 :=
      funext (fun z => hv _)
    have hs := expansion β
    rw [hfun] at hs
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs.eq_zero
    simp only [series, FormalMultilinearSeries.coeff_ofScalars] at hc
    change inner ℂ (v n) (exponential k β) / (Real.sqrt (n.factorial : ℝ) : ℂ) = 0 at hc
    have hn : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 := by
      norm_cast
      exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne'
    exact (div_eq_zero_iff.mp hc).resolve_right hn

private lemma exponential_dense (k : ℕ) :
    DenseRange (Finsupp.linearCombination ℂ (exponential k)) := by
  have hspan : (Submodule.span ℂ (Set.range (exponential k))).topologicalClosure = ⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    apply le_antisymm
    · intro v hv
      have hz : v = 0 := exponential_total k v (fun β => by
        have hm : exponential k β ∈ Submodule.span ℂ (Set.range (exponential k)) :=
          Submodule.subset_span ⟨β, rfl⟩
        exact Submodule.inner_left_of_mem_orthogonal hm hv)
      simp [hz]
    · exact bot_le
  rw [← Finsupp.range_linearCombination] at hspan
  change Dense (Set.range (Finsupp.linearCombination ℂ (exponential k)))
  rw [dense_iff_closure_eq]
  simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe, LinearMap.coe_range] using
    congrArg (fun K : Submodule ℂ (Fock k) => (K : Set (Fock k))) hspan

private lemma passive_exponential_dense {k : ℕ} (V : Passive k) :
    DenseRange (Finsupp.linearCombination ℂ (exponential k ∘ V)) := by
  have heq : Set.range (exponential k ∘ V) = Set.range (exponential k) := by
    exact EquivLike.range_comp (exponential k) V
  have hr := Finsupp.range_linearCombination (R := ℂ) (v := exponential k ∘ V)
  have hb := Finsupp.range_linearCombination (R := ℂ) (v := exponential k)
  have heq' : Set.range (Finsupp.linearCombination ℂ (exponential k ∘ V)) =
      Set.range (Finsupp.linearCombination ℂ (exponential k)) :=
    congrArg (fun K : Submodule ℂ (Fock k) => (K : Set (Fock k)))
      (hr.trans ((congrArg (Submodule.span ℂ) heq).trans hb.symm))
  change Dense (Set.range (Finsupp.linearCombination ℂ (exponential k ∘ V)))
  rw [heq']
  exact exponential_dense k

private lemma passive_span_norm {k : ℕ} (V : Passive k) (c : Modes k →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ (exponential k ∘ V) c‖ =
      ‖Finsupp.linearCombination ℂ (exponential k) c‖ := by
  classical
  have hg (β γ : Modes k) :
      inner ℂ (exponential k (V β)) (exponential k (V γ)) =
        inner ℂ (exponential k β) (exponential k γ) := by
    simp only [exponential_inner, V.inner_map_map]
  have hs : inner ℂ (Finsupp.linearCombination ℂ (exponential k ∘ V) c)
      (Finsupp.linearCombination ℂ (exponential k ∘ V) c) =
      inner ℂ (Finsupp.linearCombination ℂ (exponential k) c)
        (Finsupp.linearCombination ℂ (exponential k) c) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, Function.comp_def, hg]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hs
  have hsq : ‖Finsupp.linearCombination ℂ (exponential k ∘ V) c‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ (exponential k) c‖ ^ 2 := by exact_mod_cast hs
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ (exponential k ∘ V) c),
    norm_nonneg (Finsupp.linearCombination ℂ (exponential k) c)]

def gamma {k : ℕ} (V : Passive k) : Fock k ≃ₗᵢ[ℂ] Fock k :=
  (LinearEquiv.refl ℂ (Modes k →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ (exponential k))
    (Finsupp.linearCombination ℂ (exponential k ∘ V))
    (exponential_dense k) (passive_exponential_dense V) (passive_span_norm V)

lemma gamma_exponential {k : ℕ} (V : Passive k) (β : Modes k) :
    gamma V (exponential k β) = exponential k (V β) := by
  have h := LinearEquiv.extendOfIsometry_eq
    (LinearEquiv.refl ℂ (Modes k →₀ ℂ))
    (Finsupp.linearCombination ℂ (exponential k))
    (Finsupp.linearCombination ℂ (exponential k ∘ V))
    (exponential_dense k) (passive_exponential_dense V) (passive_span_norm V)
    (Finsupp.single β 1)
  simpa [gamma] using h

lemma gamma_coherent {k : ℕ} (V : Passive k) (β : Modes k) :
    gamma V (coherent k β) = coherent k (V β) := by
  simp only [coherent, map_smul, gamma_exponential, V.norm_map]




def NumberDomain {k : ℕ} (ψ : Fock (k+1)) : Prop :=
  Memℓp (fun n : ℕ => (n : ℂ) • ψ n) 2

def number {k : ℕ} (ψ : Fock (k+1)) (h : NumberDomain ψ) : Fock (k+1) :=
  ⟨fun n : ℕ => (n : ℂ) • ψ n, h⟩

private lemma single_number_exponential_mem (α : ℂ) :
    Memℓp (fun n : ℕ => (n : ℂ) *
      D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff α n) 2 := by
  apply (lp.memℓp
    (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector (2*α))).mono'
  intro n
  change ‖(n : ℂ) *
    D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff α n‖ ≤
    ‖D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff (2*α) n‖
  simp only [D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff,
    norm_mul, norm_div, norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat, mul_pow]
  rw [← mul_div_assoc]
  gcongr
  exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)

def numberExponential (α : ℂ) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨_, single_number_exponential_mem α⟩

private lemma coherent_number_domain {k : ℕ} (β : Modes (k+1)) : NumberDomain (coherent (k+1) β) := by
  let ψ : Fock (k+1) := (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
    headTensor (numberExponential (β 0)) (exponential k (tail β))
  have he : (fun n : ℕ => (n : ℂ) • coherent (k+1) β n) = ψ := by
    funext n
    change (n : ℂ) • ((Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
      (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff (β 0) n •
        exponential k (tail β))) =
      (Real.exp (-‖β‖ ^ 2 / 2) : ℂ) •
        (((n : ℂ) * D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff
          (β 0) n) • exponential k (tail β))
    simp only [smul_smul]
    congr 1
    ring
  unfold NumberDomain
  rw [he]
  exact lp.memℓp ψ

def numberProjector {k : ℕ} (m : ℕ) : Fock (k+1) →L[ℂ] Fock (k+1) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => Fock k) 2 m).comp
    (lp.evalCLM ℂ (fun _ : ℕ => Fock k) 2 m)

def vacuum (k : ℕ) : Fock k := exponential k 0

def onePhoton : (k : ℕ) → Modes k → Fock k
  | 0, _ => (0 : ℂ)
  | k+1, β => lp.single 2 1 ((β 0) • vacuum k) +
      lp.single 2 0 (onePhoton k (tail β))

lemma vacuum_exponential_inner (k : ℕ) (β : Modes k) :
    inner ℂ (vacuum k) (exponential k β) = 1 := by
  simp [vacuum, exponential_inner]

lemma onePhoton_exponential_inner (k : ℕ) (β γ : Modes k) :
    inner ℂ (onePhoton k β) (exponential k γ) = inner ℂ β γ := by
  induction k with
  | zero => simp [onePhoton, PiLp.inner_apply]
  | succ k ih =>
    change inner ℂ (lp.single 2 1 ((β 0) • vacuum k) +
      lp.single 2 0 (onePhoton k (tail β)))
      (headTensor (D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector (γ 0))
        (exponential k (tail γ))) = _
    rw [inner_add_left, lp.inner_single_left, lp.inner_single_left]
    simp only [headTensor, inner_smul_left, inner_smul_right,
      D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialVector,
      D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter.exponentialCoeff,
      pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero, Nat.cast_one,
      Real.sqrt_one, Complex.ofReal_one, div_one, one_mul,
      vacuum_exponential_inner, mul_one, ih]
    simp [PiLp.inner_apply, Fin.sum_univ_succ, tail, RCLike.inner_apply, mul_comm]

lemma gamma_onePhoton {k : ℕ} (V : Passive k) (β : Modes k) :
    gamma V (onePhoton k β) = onePhoton k (V β) := by
  apply sub_eq_zero.mp
  apply exponential_total k
  intro γ
  rw [inner_sub_left]
  have ht : exponential k γ = gamma V (exponential k (V.symm γ)) := by
    simp [gamma_exponential]
  rw [ht, (gamma V).inner_map_map, gamma_exponential,
    onePhoton_exponential_inner, onePhoton_exponential_inner]
  have hv := V.inner_map_map β (V.symm γ)
  exact sub_eq_zero.mpr (by simpa using hv.symm)

private lemma onePhoton_apply {k : ℕ} (β : Modes (k+1)) (n : ℕ) :
    onePhoton (k+1) β n = (if n = 1 then (β 0) • vacuum k else 0) +
      (if n = 0 then onePhoton k (tail β) else 0) := by
  change (lp.single 2 1 ((β 0) • vacuum k) : lp (fun _ : ℕ => Fock k) 2) n +
    (lp.single 2 0 (onePhoton k (tail β)) : lp (fun _ : ℕ => Fock k) 2) n = _
  by_cases h1 : n = 1 <;> by_cases h0 : n = 0 <;>
    simp [lp.single_apply, Pi.single_apply, h1, h0]

private lemma onePhoton_number_domain {k : ℕ} (β : Modes (k+1)) :
    NumberDomain (onePhoton (k+1) β) := by
  have he : (fun n : ℕ => (n : ℂ) • onePhoton (k+1) β n) =
      (lp.single 2 1 ((β 0) • vacuum k) : lp (fun _ : ℕ => Fock k) 2) := by
    funext n
    by_cases h1 : n = 1
    · subst n; simp [onePhoton_apply, lp.single_apply, Pi.single_apply]
    · by_cases h0 : n = 0
      · subst n; simp [onePhoton_apply, lp.single_apply, Pi.single_apply]
      · simp [onePhoton_apply, lp.single_apply, Pi.single_apply, h1, h0]
  unfold NumberDomain
  rw [he]
  exact lp.memℓp _

def resolvedProbability {k : ℕ} (m : ℕ) (ψ : Fock (k+1)) : ℝ := ‖ψ m‖ ^ 2

lemma projector_weight {k : ℕ} (m : ℕ) (ψ : Fock (k+1)) :
    inner ℂ ψ (numberProjector m ψ) = (resolvedProbability m ψ : ℂ) := by
  change inner ℂ ψ (lp.single 2 m (ψ m)) = _
  rw [lp.inner_single_right, inner_self_eq_norm_sq_to_K]
  simp [resolvedProbability]

section WeakValue
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


def effectWeight (A B : H ≃ₗᵢ[ℂ] H) (E : H →L[ℂ] H) (ψ : H) : ℂ :=
  inner ℂ (B (A ψ)) (E (B (A ψ)))

def generalizedWeakValue (A B : H ≃ₗᵢ[ℂ] H) (E : H →L[ℂ] H) (ψ inserted : H)
    (_h : effectWeight A B E ψ ≠ 0) : ℂ :=
  inner ℂ (B (A ψ)) (E (B inserted)) / effectWeight A B E ψ
end WeakValue

def inputAmplitude (k : ℕ) (α : ℂ) : Modes (k+1) := EuclideanSpace.single 0 α

def coherentInput (k : ℕ) (α : ℂ) : Fock (k+1) := coherent (k+1) (inputAmplitude k α)

def singleInput (k : ℕ) : Fock (k+1) := onePhoton (k+1) (inputAmplitude k 1)

def coherentFinal {k : ℕ} (A B : Passive (k+1)) (α : ℂ) : Fock (k+1) :=
  gamma B (gamma A (coherentInput k α))

def singleFinal {k : ℕ} (A B : Passive (k+1)) : Fock (k+1) :=
  gamma B (gamma A (singleInput k))

lemma coherentProbeDomain {k : ℕ} (A : Passive (k+1)) (α : ℂ) :
    NumberDomain (gamma A (coherentInput k α)) := by
  change NumberDomain (gamma A (coherent (k+1) (inputAmplitude k α)))
  rw [gamma_coherent A (inputAmplitude k α)]
  exact coherent_number_domain _

lemma singleProbeDomain {k : ℕ} (A : Passive (k+1)) :
    NumberDomain (gamma A (singleInput k)) := by
  change NumberDomain (gamma A (onePhoton (k+1) (inputAmplitude k 1)))
  rw [gamma_onePhoton A (inputAmplitude k 1)]
  exact onePhoton_number_domain _

def coherentProbability {k : ℕ} (A B : Passive (k+1)) (α : ℂ) (m : ℕ) : ℝ :=
  resolvedProbability m (coherentFinal A B α)

def singleProbability {k : ℕ} (A B : Passive (k+1)) (m : Fin 2) : ℝ :=
  resolvedProbability m (singleFinal A B)

def coherentWeakValue {k : ℕ} (A B : Passive (k+1)) (α : ℂ) (m : ℕ)
    (h : coherentProbability A B α m ≠ 0) : ℂ :=
  generalizedWeakValue (gamma A) (gamma B) (numberProjector m) (coherentInput k α)
    (number _ (coherentProbeDomain A α)) (by
      rw [effectWeight, projector_weight]
      exact_mod_cast h)

def singleWeakValue {k : ℕ} (A B : Passive (k+1)) (m : Fin 2)
    (h : singleProbability A B m ≠ 0) : ℂ :=
  generalizedWeakValue (gamma A) (gamma B) (numberProjector m) (singleInput k)
    (number _ (singleProbeDomain A)) (by
      rw [effectWeight, projector_weight]
      exact_mod_cast h)





end D5.S3.Quantum.PassiveFockModel
