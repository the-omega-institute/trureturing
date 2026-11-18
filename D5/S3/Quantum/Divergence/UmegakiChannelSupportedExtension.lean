/- GID: D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiChannelSupportedExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Depolarized endpoint bounds control the supported conditional Umegaki deficit. -/

import D5.S3.Quantum.Divergence.UmegakiConditionalBKM
import D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
import D5.S3.Quantum.Divergence.UmegakiSupportedNoise
import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Divergence.FannesRootFidelityHolevo
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Recovery.QubitCenteredTransport

/-! The input noise makes a supported pair faithful at fixed output depolarization.
A second limit removes the output depolarization, with each state's own marginal
determining its noise. Both limits use data processing for actual CPTP maps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension

open Filter _root_.Matrix
open scoped Topology BigOperators CStarAlgebra ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FinitePreparationChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
open D5.S3.Quantum.Divergence.UmegakiKernelContraction
open D5.S3.Quantum.Divergence.UmegakiConditionalBKM
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (amp_posDef)
open D5.S3.Quantum.Divergence.UmegakiSupportedNoise
open D5.S3.Quantum.Recovery.QubitResidualRounding (referenceState_comp)
open D5.S3.Quantum.Divergence.FannesRootFidelityHolevo (exists_eraseChannel)

universe u
variable {n R a b : Type u}
  [Fintype n] [DecidableEq n] [Fintype R] [DecidableEq R]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private abbrev Weight := Set.Ioo (0 : ℝ) 1

private abbrev raw (X : DensityState n) : Matrix n n ℂ := CStarMatrix.ofMatrix.symm X.1

private lemma density_nonempty (X : DensityState n) : Nonempty n :=
  state_nonempty ⟨density_posSemidef X, X.2.2⟩

private def uniformState (n : Type u) [Fintype n] [DecidableEq n] [Nonempty n] :
    DensityState n := by
  let d : ℝ := Fintype.card n
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨CStarMatrix.ofMatrix (d⁻¹ • (1 : Matrix n n ℂ)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (Matrix.PosSemidef.one.smul (inv_nonneg.mpr hd.le)).nonneg
  · change (d⁻¹ • (1 : Matrix n n ℂ)).trace = 1
    rw [Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]
    exact_mod_cast (inv_mul_cancel₀ hd.ne')

private lemma uniformState_posDef [Nonempty n] : (raw (uniformState n)).PosDef := by
  have hCard : 0 < (Fintype.card n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact Matrix.PosDef.one.smul (inv_pos.mpr hCard)

private def identityChannel (n : Type u) [Fintype n] [DecidableEq n] : QuantumChannel n n where
  toCompletelyPositiveMap :=
    { toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := fun _ X hX => by simpa using hX }
  trace_preserving _ := rfl

private def mixIdentity (t : Weight) (C : QuantumChannel n n) : QuantumChannel n n where
  toCompletelyPositiveMap :=
    { toLinearMap := (1 - (t : ℝ)) • LinearMap.id + (t : ℝ) • C.toCompletelyPositiveMap.toLinearMap
      map_cstarMatrix_nonneg' := by
        intro k X hX
        change 0 ≤ (1 - (t : ℝ)) • X + (t : ℝ) • X.map C.toCompletelyPositiveMap
        exact add_nonneg (smul_nonneg (sub_nonneg.mpr t.2.2.le) hX)
          (smul_nonneg t.2.1.le (C.toCompletelyPositiveMap.map_cstarMatrix_nonneg X hX)) }
  trace_preserving X := by
    change ((1 - (t : ℝ)) • X + (t : ℝ) • C.toCompletelyPositiveMap X).trace = X.trace
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, C.trace_preserving,
      ← add_smul, sub_add_cancel, one_smul]

private lemma act_mixIdentity (t : Weight) (C : QuantumChannel n n) (X : Matrix n n ℂ) :
    act (mixIdentity t C) X = (1 - (t : ℝ)) • X + (t : ℝ) • act C X := rfl

private def replacementChannel (K : DensityState n) : QuantumChannel n n :=
  Classical.choose (finite_preparation_quantum_channel (fun _ : n => K))

private lemma act_replacementChannel (K : DensityState n) (X : Matrix n n ℂ) :
    act (replacementChannel K) X = X.trace • raw K := by
  exact (Classical.choose_spec (finite_preparation_quantum_channel (fun _ : n => K)) X).trans
    (by simp [Matrix.trace, Finset.sum_smul])

private def noiseChannel (K : DensityState n) (t : Weight) : QuantumChannel n n :=
  mixIdentity t (replacementChannel K)

private lemma noiseChannel_state (K X : DensityState n) (t : Weight) :
    raw ((noiseChannel K t).mapState X) = (1 - (t : ℝ)) • raw X + (t : ℝ) • raw K := by
  change act (mixIdentity t (replacementChannel K)) (raw X) = _
  rw [act_mixIdentity, act_replacementChannel, show (raw X).trace = 1 from X.2.2, one_smul]

/-- The genuine trace-replacement mixture with the normalized identity. -/
def depolarizingChannel (b : Type u) [Fintype b] [DecidableEq b]
    (δ : Set.Ioo (0 : ℝ) 1) : QuantumChannel b b := by
  classical
  exact if h : Nonempty b then
    letI := h
    noiseChannel (uniformState b) δ
  else identityChannel b

private lemma depolarizingChannel_eq [Nonempty b] (δ : Weight) :
    depolarizingChannel b δ = noiseChannel (uniformState b) δ := by
  rw [depolarizingChannel, dif_pos (inferInstance : Nonempty b)]

/-- Its action on the full complex matrix algebra is affine trace replacement. -/
theorem act_depolarizingChannel (δ : Set.Ioo (0 : ℝ) 1) (X : Matrix b b ℂ) :
    act (depolarizingChannel b δ) X =
      (1 - (δ : ℝ)) • X + (δ : ℝ) • (X.trace • ((Fintype.card b : ℝ)⁻¹ • (1 : Matrix b b ℂ))) := by
  by_cases hb : Nonempty b
  · have : Nonempty b := hb
    rw [depolarizingChannel_eq, noiseChannel, act_mixIdentity, act_replacementChannel]
    rfl
  · ext i
    exact (hb ⟨i⟩).elim

private lemma act_comp (M : QuantumChannel b b) (N : QuantumChannel a b)
    (X : Matrix a a ℂ) : act (M.comp N) X = act M (act N X) := rfl

private lemma depolarized_posDef [Nonempty a] [Nonempty b] (N : QuantumChannel a b)
    (δ : Weight) : (act ((depolarizingChannel b δ).comp N) 1).PosDef := by
  rw [act_comp, act_depolarizingChannel]
  have hTrace : (act N (1 : Matrix a a ℂ)).trace = (Fintype.card a : ℂ) :=
    (N.trace_preserving (CStarMatrix.ofMatrix 1)).trans Matrix.trace_one
  rw [hTrace]
  change ((1 - (δ : ℝ)) • act N 1 +
    (δ : ℝ) • ((Fintype.card a : ℝ) • raw (uniformState b))).PosDef
  have hOne : 0 ≤ CStarMatrix.ofMatrix (1 : Matrix a a ℂ) :=
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv Matrix.PosSemidef.one.nonneg
  have hPos : (act N (1 : Matrix a a ℂ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (map_nonneg N.toCompletelyPositiveMap hOne))
  have hCard : 0 < (Fintype.card a : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  exact Matrix.PosDef.posSemidef_add (hPos.smul (sub_nonneg.mpr δ.2.2.le))
    (((uniformState_posDef (n := b)).smul hCard).smul δ.2.1)

private theorem exists_amplifiedChannel (N : QuantumChannel a b) :
    ∃ C : QuantumChannel (R × a) (R × b),
      ∀ X : Matrix (R × a) (R × a) ℂ, act C X = amp N X := by
  let K := actual_kraus_representation N
  obtain ⟨C, hC⟩ := finite_local_kraus_quantum_channel (s := R) K.kraus K.hkraus
  refine ⟨C, fun X => ?_⟩
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  exact (hC X (r,i) (s,j)).trans
    (congrArg (fun Z : Matrix b b ℂ => Z i j) (K.haction _)).symm

private lemma amplifiedChannel_state (N : QuantumChannel a b)
    (C : QuantumChannel (R × a) (R × b))
    (hC : ∀ X : Matrix (R × a) (R × a) ℂ, act C X = amp N X) (X : DensityState (R × a)) :
    C.mapState X = referenceState N X := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact hC (raw X)

private lemma marginal_referenceState (N : QuantumChannel a b) (X : DensityState (R × a)) :
    marginalRight (referenceState N X) = marginalRight X := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  exact ptr_amp N (raw X)

private lemma erasure_state
    (C : QuantumChannel (R × a) R)
    (hC : ∀ X : Matrix (R × a) (R × a) ℂ,
      act C X = ∑ i : a, X.submatrix (fun r => (r,i)) (fun r => (r,i)))
    (X : DensityState (R × a)) : C.mapState X = marginalRight X := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change act C (raw X) = partialTraceRight (raw X)
  rw [hC]
  ext r s
  simp [Matrix.sum_apply, partialTraceRight]

private lemma supported_channel_dpi (C : QuantumChannel a b) (X Y : DensityState a)
    (hXY : SupportContained X Y) :
    SupportContained (C.mapState X) (C.mapState Y) ∧
      finiteTraceLogRelativeEntropy (C.mapState X) (C.mapState Y) ≤
        finiteTraceLogRelativeEntropy X Y := by
  have : Nonempty a := density_nonempty X
  have : Nonempty b := density_nonempty (C.mapState X)
  have hDPI := extended_quantum_relative_entropy_channel_dpi C X Y
  have hOut := (extendedQuantumRelativeEntropy_ne_top_iff _ _).mp
    (ne_top_of_le_ne_top ((extendedQuantumRelativeEntropy_ne_top_iff X Y).mpr hXY) hDPI)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hXY,
    extendedQuantumRelativeEntropy_eq_coe_of_support hOut] at hDPI
  exact ⟨hOut, WithTop.coe_le_coe.mp hDPI⟩

private def onUnitInterval (X : DensityState n) (f : Weight → DensityState n) (t : ℝ) :
    DensityState n :=
  if h : t ∈ Set.Ioo (0 : ℝ) 1 then f ⟨t,h⟩ else X

private lemma onUnitInterval_apply (X : DensityState n) (f : Weight → DensityState n)
    (t : Weight) : onUnitInterval X f t = f t := by
  simp [onUnitInterval, t.2]

private lemma tendsto_of_channel_noise
    (X Y K L : DensityState n) (Xt Yt : Weight → DensityState n)
    (hXY : SupportContained X Y)
    (hX : ∀ t : Weight, raw (Xt t) = (1 - (t : ℝ)) • raw X + (t : ℝ) • raw K)
    (hY : ∀ t : Weight, raw (Yt t) = (1 - (t : ℝ)) • raw Y + (t : ℝ) • raw L)
    (hChannel : ∀ t : Weight, ∃ C : QuantumChannel n n,
      Xt t = C.mapState X ∧ Yt t = C.mapState Y) :
    Tendsto (fun t : ℝ =>
      finiteTraceLogRelativeEntropy (onUnitInterval X Xt t) (onUnitInterval Y Yt t))
      (𝓝[>] 0) (𝓝 (finiteTraceLogRelativeEntropy X Y)) := by
  have hNear : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hDPI (t : Weight) : SupportContained (Xt t) (Yt t) ∧
      finiteTraceLogRelativeEntropy (Xt t) (Yt t) ≤ finiteTraceLogRelativeEntropy X Y := by
    obtain ⟨C, hx, hy⟩ := hChannel t
    rw [hx, hy]
    exact supported_channel_dpi C X Y hXY
  apply tendsto_finiteTraceLogRelativeEntropy_of_noise X Y K L _ _ hXY
  · filter_upwards [hNear] with t ht
    rw [onUnitInterval_apply X Xt (⟨t,ht⟩ : Weight)]
    exact hX ⟨t,ht⟩
  · filter_upwards [hNear] with t ht
    rw [onUnitInterval_apply Y Yt (⟨t,ht⟩ : Weight)]
    exact hY ⟨t,ht⟩
  · filter_upwards [hNear] with t ht
    rw [onUnitInterval_apply X Xt (⟨t,ht⟩ : Weight), onUnitInterval_apply Y Yt (⟨t,ht⟩ : Weight)]
    exact (hDPI ⟨t,ht⟩).1
  · filter_upwards [hNear] with t ht
    rw [onUnitInterval_apply X Xt (⟨t,ht⟩ : Weight), onUnitInterval_apply Y Yt (⟨t,ht⟩ : Weight)]
    exact (hDPI ⟨t,ht⟩).2

private lemma referenceState_noise (N : QuantumChannel a b) (K X : DensityState (R × a))
    (t : Weight) :
    referenceState N ((noiseChannel K t).mapState X) =
      (noiseChannel (referenceState N K) t).mapState (referenceState N X) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change amp N (raw ((noiseChannel K t).mapState X)) =
    raw ((noiseChannel (referenceState N K) t).mapState (referenceState N X))
  rw [noiseChannel_state, noiseChannel_state]
  let A : Matrix (R × a) (R × a) ℂ →ₗ[ℝ] Matrix (R × b) (R × b) ℂ :=
    (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)).restrictScalars ℝ
  change A ((1 - (t : ℝ)) • raw X + (t : ℝ) • raw K) =
    (1 - (t : ℝ)) • A (raw X) + (t : ℝ) • A (raw K)
  rw [map_add, map_smul, map_smul]

private lemma marginalRight_noise (K X : DensityState (R × a)) (t : Weight) :
    marginalRight ((noiseChannel K t).mapState X) =
      (noiseChannel (marginalRight K) t).mapState (marginalRight X) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceRight (raw ((noiseChannel K t).mapState X)) =
    raw ((noiseChannel (marginalRight K) t).mapState (marginalRight X))
  rw [noiseChannel_state, noiseChannel_state, partialTraceRight_add,
    partialTraceRight_smul, partialTraceRight_smul]
  rfl

private lemma tendsto_common_noise (X Y K : DensityState n) (hXY : SupportContained X Y) :
    Tendsto (fun t : ℝ =>
      finiteTraceLogRelativeEntropy
        (onUnitInterval X (fun s => (noiseChannel K s).mapState X) t)
        (onUnitInterval Y (fun s => (noiseChannel K s).mapState Y) t))
      (𝓝[>] 0) (𝓝 (finiteTraceLogRelativeEntropy X Y)) :=
  tendsto_of_channel_noise X Y K K _ _ hXY (noiseChannel_state K X)
    (noiseChannel_state K Y) (fun t => ⟨noiseChannel K t, rfl, rfl⟩)

/-- The faithful-output endpoint bound extends to supported inputs with arbitrary actual
reference marginals. -/
theorem supported_conditional_relativeEntropy_contraction_of_faithful_output
    (M : QuantumChannel a b) (c : ℝ) (hM : (act M 1).PosDef)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound M c)
    (ρ σ : DensityState (R × a)) (hSupport : SupportContained ρ σ) :
    finiteTraceLogRelativeEntropy (referenceState M ρ) (referenceState M σ) -
      finiteTraceLogRelativeEntropy (marginalRight (referenceState M ρ))
        (marginalRight (referenceState M σ)) ≤
    c * (finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)) := by
  have : Nonempty (R × a) := density_nonempty ρ
  obtain ⟨C, hC⟩ := exists_amplifiedChannel (R := R) M
  obtain ⟨E, hE⟩ := exists_eraseChannel (n := R) (ι := a)
  have hOutput : SupportContained (referenceState M ρ) (referenceState M σ) := by
    simpa only [amplifiedChannel_state M C hC] using (supported_channel_dpi C ρ σ hSupport).1
  have hMarginal : SupportContained (marginalRight ρ) (marginalRight σ) := by
    simpa only [erasure_state E hE] using (supported_channel_dpi E ρ σ hSupport).1
  let ω := uniformState (R × a)
  rw [marginal_referenceState, marginal_referenceState]
  refine le_of_tendsto_of_tendsto
    ((tendsto_common_noise _ _ (referenceState M ω) hOutput).sub
      (tendsto_common_noise _ _ (marginalRight ω) hMarginal))
    (tendsto_const_nhds.mul ((tendsto_common_noise _ _ ω hSupport).sub
      (tendsto_common_noise _ _ (marginalRight ω) hMarginal))) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  let s : Weight := ⟨t, ht⟩
  have hFaithful (X : DensityState (R × a)) : (raw ((noiseChannel ω s).mapState X)).PosDef := by
    rw [noiseChannel_state]
    exact Matrix.PosDef.posSemidef_add ((density_posSemidef X).smul (sub_nonneg.mpr ht.2.le))
      (uniformState_posDef.smul ht.1)
  simp only [show t = (s : ℝ) from rfl, onUnitInterval_apply]
  rw [← referenceState_noise, ← referenceState_noise, ← marginalRight_noise, ← marginalRight_noise]
  simpa only [marginal_referenceState] using
    faithful_conditional_relativeEntropy_contraction M c hM hc hEnd
      ((noiseChannel ω s).mapState ρ) ((noiseChannel ω s).mapState σ) (hFaithful ρ) (hFaithful σ)

private lemma referenceState_depolarizing [Nonempty b] (X : DensityState (R × b)) (δ : Weight) :
    raw (referenceState (depolarizingChannel b δ) X) =
      (1 - (δ : ℝ)) • raw X + (δ : ℝ) • raw (productState (marginalRight X) (uniformState b)) := by
  obtain ⟨P, hP⟩ := finite_local_preparation_quantum_channel
    (s := R) (fun _ : b => uniformState b)
  have hReplace (Z : Matrix (R × b) (R × b) ℂ) :
      act P Z = amp (replacementChannel (uniformState b)) Z := by
    ext ⟨r,i⟩ ⟨s,j⟩
    rw [amp_entry, act_replacementChannel]
    exact (hP Z (r,i) (s,j)).trans (by simp [Matrix.trace, Finset.sum_mul, smul_eq_mul])
  change amp (depolarizingChannel b δ) (raw X) = _
  rw [depolarizingChannel_eq]
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry, noiseChannel, act_mixIdentity]
  have hBlock := congrArg (fun Z : Matrix (R × b) (R × b) ℂ => Z (r,i) (s,j))
    (hReplace (raw X)).symm
  rw [amp_entry] at hBlock
  change (1 - (δ : ℝ)) • raw X (r,i) (s,j) +
      (δ : ℝ) • act (replacementChannel (uniformState b))
        (fun x y => raw X (r,x) (s,y)) i j =
    (1 - (δ : ℝ)) • raw X (r,i) (s,j) +
      (δ : ℝ) • ((∑ x, raw X (r,x) (s,x)) * raw (uniformState b) i j)
  rw [hBlock]
  change _ + (δ : ℝ) • CStarMatrix.ofMatrix.symm
      (P.toCompletelyPositiveMap (CStarMatrix.ofMatrix (raw X))) (r,i) (s,j) = _
  rw [hP]
  rw [Finset.sum_mul]

/-- A uniform endpoint bound on the genuine depolarizations of a finite channel
controls its conditional relative entropy deficit for every supported joint pair. -/
theorem supported_conditional_relativeEntropy_contraction
    (N : QuantumChannel a b) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hEnd : ∀ δ : Set.Ioo (0 : ℝ) 1, EndpointBound ((depolarizingChannel b δ).comp N) c)
    (ρ σ : DensityState (R × a)) (hSupport : SupportContained ρ σ) :
    finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) -
      finiteTraceLogRelativeEntropy (marginalRight (referenceState N ρ))
        (marginalRight (referenceState N σ)) ≤
    c * (finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)) := by
  have : Nonempty a := Nonempty.map Prod.snd (density_nonempty ρ)
  let X := referenceState N ρ
  let Y := referenceState N σ
  have : Nonempty b := Nonempty.map Prod.snd (density_nonempty X)
  obtain ⟨C, hC⟩ := exists_amplifiedChannel (R := R) N
  have hXY : SupportContained X Y := by
    simpa only [X, Y, amplifiedChannel_state N C hC] using (supported_channel_dpi C ρ σ hSupport).1
  have hLimit := tendsto_of_channel_noise X Y
    (productState (marginalRight X) (uniformState b))
    (productState (marginalRight Y) (uniformState b))
    (fun δ => referenceState (depolarizingChannel b δ) X)
    (fun δ => referenceState (depolarizingChannel b δ) Y) hXY
    (referenceState_depolarizing X) (referenceState_depolarizing Y) (by
      intro δ
      obtain ⟨Cδ, hCδ⟩ := exists_amplifiedChannel (R := R) (depolarizingChannel b δ)
      exact ⟨Cδ, (amplifiedChannel_state _ Cδ hCδ X).symm,
        (amplifiedChannel_state _ Cδ hCδ Y).symm⟩)
  rw [marginal_referenceState, marginal_referenceState]
  refine le_of_tendsto (hLimit.sub tendsto_const_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with t ht
  let δ : Weight := ⟨t, ht⟩
  simp only [show t = (δ : ℝ) from rfl, onUnitInterval_apply]
  simpa only [marginal_referenceState, referenceState_comp, X, Y] using
    supported_conditional_relativeEntropy_contraction_of_faithful_output
      ((depolarizingChannel b δ).comp N) c (depolarized_posDef N δ) hc (hEnd δ) ρ σ hSupport

/-- Complete Umegaki ratios with equal reference marginals and positive finite
input divergence, over every finite reference in the channel's universe. -/
def completeRatios (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (R : Type u) (fR : Fintype R) (eR : DecidableEq R),
    letI := fR
    letI := eR
    ∃ ρ σ : DensityState (R × a), SupportContained ρ σ ∧
      marginalRight ρ = marginalRight σ ∧ 0 < finiteTraceLogRelativeEntropy ρ σ ∧
      x = finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) /
        finiteTraceLogRelativeEntropy ρ σ}

private def conditionalDeficit (ρ σ : DensityState (R × a)) : ℝ :=
  finiteTraceLogRelativeEntropy ρ σ -
    finiteTraceLogRelativeEntropy (marginalRight ρ) (marginalRight σ)

/-- Conditional Umegaki ratios with exact marginal subtraction and a positive
finite input deficit, over every finite reference in the channel's universe. -/
def conditionalRatios (N : QuantumChannel a b) : Set ℝ :=
  {x | ∃ (R : Type u) (fR : Fintype R) (eR : DecidableEq R),
    letI := fR
    letI := eR
    ∃ ρ σ : DensityState (R × a), SupportContained ρ σ ∧
      0 < conditionalDeficit ρ σ ∧
      x = conditionalDeficit (referenceState N ρ) (referenceState N σ) /
        conditionalDeficit ρ σ}

/-- The supported complete Umegaki contraction coefficient, including the
zero convention when the feasible set is empty. -/
def completeCoefficient (N : QuantumChannel a b) : ℝ := sSup (insert 0 (completeRatios N))

/-- The supported conditional Umegaki contraction coefficient, including the
zero convention when the feasible set is empty. -/
def conditionalCoefficient (N : QuantumChannel a b) : ℝ := sSup (insert 0 (conditionalRatios N))

private lemma amplified_dpi (N : QuantumChannel a b) (ρ σ : DensityState (R × a))
    (h : SupportContained ρ σ) :
    SupportContained (referenceState N ρ) (referenceState N σ) ∧
      finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) ≤
        finiteTraceLogRelativeEntropy ρ σ := by
  obtain ⟨C, hC⟩ := exists_amplifiedChannel (R := R) N
  simpa only [amplifiedChannel_state N C hC] using supported_channel_dpi C ρ σ h

private lemma conditionalDeficit_bounds (N : QuantumChannel a b)
    (ρ σ : DensityState (R × a)) (h : SupportContained ρ σ) :
    conditionalDeficit (referenceState N ρ) (referenceState N σ) ∈
      Set.Icc 0 (conditionalDeficit ρ σ) := by
  have hOut := amplified_dpi N ρ σ h
  obtain ⟨E, hE⟩ := exists_eraseChannel (n := R) (ι := b)
  have hErase := supported_channel_dpi E (referenceState N ρ) (referenceState N σ) hOut.1
  rw [erasure_state E hE, erasure_state E hE] at hErase
  constructor
  · exact sub_nonneg.mpr hErase.2
  · unfold conditionalDeficit
    rw [marginal_referenceState, marginal_referenceState]
    exact sub_le_sub_right hOut.2 _

private lemma conditionalDeficit_of_marginal_eq (ρ σ : DensityState (R × a))
    (h : marginalRight ρ = marginalRight σ) :
    conditionalDeficit ρ σ = finiteTraceLogRelativeEntropy ρ σ := by
  rw [conditionalDeficit, h, finiteTraceLogRelativeEntropy_self, sub_zero]

private lemma completeRatios_subset_conditionalRatios (N : QuantumChannel a b) :
    completeRatios N ⊆ conditionalRatios N := by
  rintro x ⟨R, fR, eR, ρ, σ, h, hm, hpos, hx⟩
  let _ := fR
  let _ := eR
  have hmOut : marginalRight (referenceState N ρ) = marginalRight (referenceState N σ) := by
    simpa only [marginal_referenceState] using hm
  refine ⟨R, fR, eR, ρ, σ, h, ?_, ?_⟩
  · rwa [conditionalDeficit_of_marginal_eq ρ σ hm]
  · rwa [conditionalDeficit_of_marginal_eq ρ σ hm, conditionalDeficit_of_marginal_eq _ _ hmOut]

private lemma conditionalRatios_bounds (N : QuantumChannel a b) :
    insert 0 (conditionalRatios N) ⊆ Set.Icc 0 1 := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨R, fR, eR, ρ, σ, h, hpos, rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · let _ := fR
    let _ := eR
    have hBounds := conditionalDeficit_bounds N ρ σ h
    exact ⟨div_nonneg hBounds.1 hpos.le, (div_le_one hpos).mpr hBounds.2⟩

private lemma completeRatios_bounds (N : QuantumChannel a b) :
    insert 0 (completeRatios N) ⊆ Set.Icc 0 1 :=
  (Set.insert_subset_insert (completeRatios_subset_conditionalRatios N)).trans
    (conditionalRatios_bounds N)

private lemma completeCoefficient_bounds (N : QuantumChannel a b) :
    completeCoefficient N ∈ Set.Icc 0 1 :=
  ⟨le_csSup ⟨1, fun _ hx => (completeRatios_bounds N hx).2⟩ (Set.mem_insert _ _),
    csSup_le ⟨0, Set.mem_insert _ _⟩ fun _ hx => (completeRatios_bounds N hx).2⟩

set_option maxHeartbeats 800000 in
private lemma postprocessed_ratio_le_completeCoefficient (N : QuantumChannel a b)
    (C : QuantumChannel b b) (ρ σ : DensityState (R × a)) (h : SupportContained ρ σ)
    (hm : marginalRight ρ = marginalRight σ) (hpos : 0 < finiteTraceLogRelativeEntropy ρ σ) :
    finiteTraceLogRelativeEntropy (referenceState (C.comp N) ρ) (referenceState (C.comp N) σ) /
      finiteTraceLogRelativeEntropy ρ σ ≤ completeCoefficient N := by
  have hOut := amplified_dpi N ρ σ h
  have hPost := amplified_dpi C (referenceState N ρ) (referenceState N σ) hOut.1
  rw [referenceState_comp, referenceState_comp]
  have hMem :
      finiteTraceLogRelativeEntropy (referenceState N ρ) (referenceState N σ) /
        finiteTraceLogRelativeEntropy ρ σ ∈ completeRatios N := by
    rw [completeRatios, Set.mem_setOf_eq]
    refine ⟨R, ‹Fintype R›, ‹DecidableEq R›, ?_⟩
    exact ⟨ρ, σ, h, hm, hpos, rfl⟩
  have hBdd : BddAbove (insert 0 (completeRatios N)) :=
    ⟨1, fun _ hx => (completeRatios_bounds N hx).2⟩
  exact (div_le_div_of_nonneg_right hPost.2 hpos.le).trans
    (le_csSup hBdd (Set.mem_insert_of_mem 0 hMem))

private lemma direction_eq_zero_of_q_eq_zero (Z V : Matrix n n ℂ) (t : ℝ)
    (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q Z V t = 0) : V = 0 := by
  have hGram := weighted_cauchy Z V V t hZ ht
  rw [hq, mul_zero] at hGram
  have hre : (Vᴴ * V).trace.re = 0 := by nlinarith only [hGram]
  have hTrace := congrArg Complex.im (Matrix.trace_conjTranspose (Vᴴ * V))
  rw [(Matrix.isHermitian_conjTranspose_mul_self V).eq] at hTrace
  simp only [Complex.star_def, Complex.conj_im] at hTrace
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  exact Complex.ext hre (by
    change (Vᴴ * V).trace.im = 0
    linarith only [hTrace])

/-- The complete supported entropy coefficient bounds every complex left
endpoint of every genuine output depolarization, uniformly in the reference. -/
theorem depolarized_endpointBound_completeCoefficient (N : QuantumChannel a b) (δ : Weight) :
    EndpointBound ((depolarizingChannel b δ).comp N) (completeCoefficient N) := by
  classical
  intro R fR eR Z V hZ hV
  let M := (depolarizingChannel b δ).comp N
  have hZero (hv : V = 0) : q (amp M Z) (amp M V) 0 ≤ completeCoefficient N * q Z V 0 := by
    subst V
    have hAmp : amp M (0 : Matrix (R × a) (R × a) ℂ) = 0 := by
      simpa only [zero_smul] using amp_smul M (0 : ℝ) Z
    simp only [hAmp, q_eq_trace, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re, mul_zero, le_rfl]
  by_cases hj : Nonempty (R × a)
  · have : Nonempty a := Nonempty.map Prod.snd hj
    have : Nonempty b := density_nonempty (N.mapState (uniformState a))
    have hM := depolarized_posDef N δ
    have hOut := amp_posDef M hM Z hZ
    have hq := q_nonneg Z V 0 hZ (by simp)
    rcases hq.eq_or_lt with hq | hq
    · exact hZero (direction_eq_zero_of_q_eq_zero Z V 0 hZ (by simp) hq.symm)
    · apply (div_le_iff₀ hq).mp
      by_contra! h
      let ε := q (amp M Z) (amp M V) 0 / q Z V 0 - completeCoefficient N
      have hε : 0 < ε := sub_pos.mpr h
      have hqin : 0 < (Vᴴ * Z⁻¹ * V).trace.re := by
        rwa [q_zero_parameter Z V hZ] at hq
      obtain ⟨ρ, σ, _, _, _, _, hm, _, hSupp, _, hpos, hApprox, _⟩ :=
        faithful_density_pair_ratio_approx M hM Z V hZ hV hqin ε hε
      have hUpper := postprocessed_ratio_le_completeCoefficient N (depolarizingChannel b δ)
        ρ σ hSupp hm hpos
      have hLower := (abs_lt.mp hApprox).1
      rw [← q_zero_parameter Z V hZ, ← q_zero_parameter (amp M Z) (amp M V) hOut] at hLower
      change finiteTraceLogRelativeEntropy (referenceState M ρ) (referenceState M σ) /
        finiteTraceLogRelativeEntropy ρ σ ≤ completeCoefficient N at hUpper
      dsimp only [ε] at hLower
      linarith only [hUpper, hLower]
  · exact hZero (by ext i; exact (hj ⟨i⟩).elim)

/-- The supported finite-real Umegaki formulation of the equality asked in
arXiv:2608.27171v1, Definition 2, Remark 2 and Section 9. -/
theorem conditionalCoefficient_eq_completeCoefficient (N : QuantumChannel a b) :
    conditionalCoefficient N = completeCoefficient N := by
  have hComplete := completeCoefficient_bounds N
  apply le_antisymm
  · apply csSup_le ⟨0, Set.mem_insert _ _⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨R, fR, eR, ρ, σ, h, hpos, rfl⟩
    · exact hComplete.1
    · let _ := fR
      let _ := eR
      exact (div_le_iff₀ hpos).mpr (supported_conditional_relativeEntropy_contraction N
        (completeCoefficient N) hComplete (depolarized_endpointBound_completeCoefficient N)
        ρ σ h)
  · exact csSup_le_csSup ⟨1, fun _ hx => (conditionalRatios_bounds N hx).2⟩
      ⟨0, Set.mem_insert _ _⟩
      (Set.insert_subset_insert (completeRatios_subset_conditionalRatios N))

/-- Uniform arithmetic inverse contraction on all genuine output depolarizations. -/
def DepolarizedArithmeticBound (N : QuantumChannel a b) (c : ℝ) : Prop :=
  ∀ (δ : Set.Ioo (0 : ℝ) 1) {R : Type u} [Fintype R] [DecidableEq R]
    (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ), Z.PosDef →
    partialTraceRight V = 0 → t ∈ Set.Icc 0 1 →
      q (amp ((depolarizingChannel b δ).comp N) Z)
        (amp ((depolarizingChannel b δ).comp N) V) t ≤ c * q Z V t

private lemma arithmetic_bound_of_endpoints (N : QuantumChannel a b) (c : ℝ)
    (hc : c ∈ Set.Icc 0 1)
    (hEnd : ∀ δ : Weight, EndpointBound ((depolarizingChannel b δ).comp N) c) :
    DepolarizedArithmeticBound N c := by
  intro δ R _ _ Z V t hZ hV ht
  by_cases hj : Nonempty (R × a)
  · have : Nonempty a := Nonempty.map Prod.snd hj
    have : Nonempty b := density_nonempty (N.mapState (uniformState a))
    exact kernel_contraction _ c (depolarized_posDef N δ) hc (hEnd δ) Z V t hZ hV ht
  · have hZero : V = 0 := by ext i; exact (hj ⟨i⟩).elim
    subst V
    rw [show amp ((depolarizingChannel b δ).comp N) (0 : Matrix (R × a) (R × a) ℂ) = 0 by
      simpa only [zero_smul] using amp_smul ((depolarizingChannel b δ).comp N) (0 : ℝ) Z]
    simp only [q_eq_trace, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re, mul_zero, le_rfl]

/-- The complete entropy coefficient is the least uniform arithmetic inverse
bound in `[0,1]` for all output depolarizations, parameters and references. -/
theorem isLeast_depolarizedArithmeticBound (N : QuantumChannel a b) :
    IsLeast {c : ℝ | c ∈ Set.Icc 0 1 ∧ DepolarizedArithmeticBound N c}
      (completeCoefficient N) := by
  have hc := completeCoefficient_bounds N
  refine ⟨⟨hc, arithmetic_bound_of_endpoints N _ hc
    (depolarized_endpointBound_completeCoefficient N)⟩, ?_⟩
  intro c h
  have hEnd (δ : Weight) : EndpointBound ((depolarizingChannel b δ).comp N) c := by
    intro R _ _ Z V hZ hV
    exact h.2 δ Z V 0 hZ hV (by simp)
  rw [← conditionalCoefficient_eq_completeCoefficient N]
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨R, fR, eR, ρ, σ, hSupp, hpos, rfl⟩
  · exact h.1.1
  · let _ := fR
    let _ := eR
    exact (div_le_iff₀ hpos).mpr
      (supported_conditional_relativeEntropy_contraction N c h.1 hEnd ρ σ hSupp)

def inverseTest (Z V X : Matrix n n ℂ) (t : ℝ) : ℝ :=
  2 * (Xᴴ * V).trace.re - energy Z X t

/-- Variational domain of the inverse quadratic form. Boundedness is automatic
for positive definite bases and can also hold on a singular base. -/
def inverseTestValues (Z V : Matrix n n ℂ) (t : ℝ) : Set ℝ :=
  insert 0 (Set.range (fun X => inverseTest Z V X t))

/-- The real variational inverse quadratic form on its bounded domain. -/
def variationalInverse (Z V : Matrix n n ℂ) (t : ℝ) : ℝ :=
  sSup (inverseTestValues Z V t)

private lemma inverseTest_le_q (Z V X : Matrix n n ℂ) (t : ℝ)
    (hZ : Z.PosDef) (ht : t ∈ Set.Icc 0 1) : inverseTest Z V X t ≤ q Z V t := by
  have h := q_nonneg Z (V - arithmetic Z X t) t hZ ht
  rw [q_sub_arithmetic Z V X t hZ ht] at h
  unfold inverseTest
  linarith

private lemma inverseTest_inverseMatrix (Z V : Matrix n n ℂ) (t : ℝ)
    (hZ : Z.PosDef) (ht : t ∈ Set.Icc 0 1) :
    inverseTest Z V (inverseMatrix Z V t) t = q Z V t := by
  have h := q_sub_arithmetic Z V (inverseMatrix Z V t) t hZ ht
  rw [arithmetic_inverseMatrix Z V t hZ ht, sub_self] at h
  have hz : q Z 0 t = 0 := by
    simp only [q_eq_trace, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re]
  rw [hz] at h
  unfold inverseTest
  linarith

/-- The variational formula agrees with the native Hilbert–Schmidt inverse at
every faithful base. -/
theorem variationalInverse_eq_q (Z V : Matrix n n ℂ) (t : ℝ)
    (hZ : Z.PosDef) (ht : t ∈ Set.Icc 0 1) :
    BddAbove (inverseTestValues Z V t) ∧ variationalInverse Z V t = q Z V t := by
  have hUpper : ∀ x ∈ inverseTestValues Z V t, x ≤ q Z V t := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨X, rfl⟩
    · exact q_nonneg Z V t hZ ht
    · exact inverseTest_le_q Z V X t hZ ht
  have hBdd : BddAbove (inverseTestValues Z V t) := ⟨_, hUpper⟩
  refine ⟨hBdd, le_antisymm (csSup_le ⟨0, Set.mem_insert _ _⟩ hUpper) ?_⟩
  rw [← inverseTest_inverseMatrix Z V t hZ ht]
  exact le_csSup hBdd (Set.mem_insert_of_mem _ (Set.mem_range_self (inverseMatrix Z V t)))

omit [DecidableEq n] in
private lemma energy_linear_base (Z W X : Matrix n n ℂ) (r s t : ℝ) :
    energy (r • Z + s • W) X t = r * energy Z X t + s * energy W X t := by
  simp only [energy, arithmetic, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.smul_re]
  ring

private lemma amp_add_smul (N : QuantumChannel a b) (Z W : Matrix (R × a) (R × a) ℂ)
    (s : ℝ) : amp N (Z + s • W) = amp N Z + s • amp N W := by
  simpa only [neg_smul, sub_neg_eq_add] using amp_sub_smul N (-s) Z W

private def replacementMatrix (X : Matrix (R × b) (R × b) ℂ) :
    Matrix (R × b) (R × b) ℂ :=
  partialTraceRight X ⊗ₖ ((Fintype.card b : ℝ)⁻¹ • (1 : Matrix b b ℂ))

private lemma amp_depolarized (N : QuantumChannel a b)
    (δ : Weight) (X : Matrix (R × a) (R × a) ℂ) :
    amp ((depolarizingChannel b δ).comp N) X =
      (1 - (δ : ℝ)) • amp N X + (δ : ℝ) • replacementMatrix (amp N X) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry, act_comp, act_depolarizingChannel]
  simp only [replacementMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    partialTraceRight, Matrix.trace, Matrix.diag_apply, amp_entry, smul_eq_mul]

omit [DecidableEq n] in
private lemma continuous_inverseTest {Z V : ℝ → Matrix n n ℂ}
    (hZ : Continuous Z) (hV : Continuous V) (X : Matrix n n ℂ) (t : ℝ) :
    Continuous (fun s => inverseTest (Z s) (V s) X t) := by
  unfold inverseTest energy arithmetic
  have h₁ : Continuous (fun s => Xᴴ * V s) := continuous_const.mul hV
  have hL : Continuous (fun s => Z s * X) := hZ.mul continuous_const
  have hR : Continuous (fun s => X * Z s) := continuous_const.mul hZ
  have h₂ : Continuous (fun s => Xᴴ * ((1 - t) • (Z s * X) + t • (X * Z s))) :=
    continuous_const.mul ((hL.const_smul (1 - t)).add (hR.const_smul t))
  exact (continuous_const.mul (Complex.continuous_re.comp h₁.matrix_trace)).sub
    (Complex.continuous_re.comp h₂.matrix_trace)

/-- On its finite input domain, the actual channel contracts the variational
arithmetic inverse form by the complete Umegaki coefficient, even when either
base is singular. The estimate also proves finiteness at the amplified output. -/
theorem variationalInverse_channel_contraction (N : QuantumChannel a b)
    (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ)
    (hZ : Z.PosSemidef) (hV : partialTraceRight V = 0) (ht : t ∈ Set.Icc 0 1)
    (hFin : BddAbove (inverseTestValues Z V t)) :
    BddAbove (inverseTestValues (amp N Z) (amp N V) t) ∧
      variationalInverse (amp N Z) (amp N V) t ≤
        completeCoefficient N * variationalInverse Z V t := by
  let c := completeCoefficient N
  let d := c * variationalInverse Z V t
  have hc : 0 ≤ c := (completeCoefficient_bounds N).1
  have hd : 0 ≤ d := mul_nonneg hc (le_csSup hFin (Set.mem_insert _ _))
  have hMetric := (isLeast_depolarizedArithmeticBound N).1.2
  have hTest (X : Matrix (R × b) (R × b) ℂ) :
      inverseTest (amp N Z) (amp N V) X t ≤ d := by
    have hInput (s : ℝ) (hs : 0 < s) :
        q (Z + s • (1 : Matrix (R × a) (R × a) ℂ)) V t ≤ variationalInverse Z V t := by
      let W := Z + s • (1 : Matrix (R × a) (R × a) ℂ)
      let Y := inverseMatrix W V t
      have hW : W.PosDef := Matrix.PosDef.posSemidef_add hZ (Matrix.PosDef.one.smul hs)
      rw [← inverseTest_inverseMatrix W V t hW ht]
      have hComparison : inverseTest W V Y t ≤ inverseTest Z V Y t := by
        unfold inverseTest
        rw [show W = (1 : ℝ) • Z + s • 1 by simp [W], energy_linear_base, one_mul]
        have he := energy_nonneg (1 : Matrix (R × a) (R × a) ℂ) Y t
          Matrix.PosSemidef.one ht
        linarith only [mul_nonneg hs.le he]
      exact hComparison.trans (le_csSup hFin (Set.mem_insert_of_mem _ (Set.mem_range_self Y)))
    have hOutput (s : ℝ) (hs : 0 < s) :
        inverseTest (amp N (Z + s • 1)) (amp N V) X t ≤ d := by
      let W := Z + s • (1 : Matrix (R × a) (R × a) ℂ)
      have hW : W.PosDef := Matrix.PosDef.posSemidef_add hZ (Matrix.PosDef.one.smul hs)
      let T := amp N W
      let U := amp N V
      let F := fun e : ℝ => inverseTest ((1-e) • T + e • replacementMatrix T)
        ((1-e) • U + e • replacementMatrix U) X t
      have hF : Continuous F := continuous_inverseTest (by fun_prop) (by fun_prop) X t
      have hLim : Tendsto F (𝓝[>] 0) (𝓝 (inverseTest T U X t)) := by
        simpa only [F, sub_zero, one_smul, zero_smul, add_zero] using
          (hF.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      apply le_of_tendsto hLim
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with e he
      let δ : Weight := ⟨e, he⟩
      let M := (depolarizingChannel b δ).comp N
      have hFδ : F e = inverseTest (amp M W) (amp M V) X t := by
        simp only [F, M, amp_depolarized, T, U, show (δ : ℝ) = e from rfl]
      rw [hFδ]
      by_cases hj : Nonempty (R × a)
      · have : Nonempty a := Nonempty.map Prod.snd hj
        have : Nonempty b := density_nonempty (N.mapState (uniformState a))
        have hMO := amp_posDef M (depolarized_posDef N δ) W hW
        exact (inverseTest_le_q _ _ X _ hMO ht).trans
          ((hMetric δ W V t hW hV ht).trans (mul_le_mul_of_nonneg_left (hInput s hs) hc))
      · have hZero : amp M V = 0 := by
          rw [show V = 0 by ext i; exact (hj ⟨i⟩).elim]
          simpa only [zero_smul] using amp_smul M (0 : ℝ) Z
        have hPSD : (amp M W).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
            (referenceAction_nonneg M (CStarMatrix.ofMatrix W)
              (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hW.posSemidef.nonneg)))
        have hEnergy := energy_nonneg (amp M W) X t hPSD ht
        rw [hZero]
        simpa only [inverseTest, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
          mul_zero, zero_sub] using (neg_nonpos.mpr hEnergy).trans hd
    let G := fun s : ℝ => inverseTest (amp N Z + s • amp N (1 : Matrix (R × a) (R × a) ℂ))
      (amp N V) X t
    have hG : Continuous G := continuous_inverseTest (by fun_prop) continuous_const X t
    have hLim : Tendsto G (𝓝[>] 0) (𝓝 (inverseTest (amp N Z) (amp N V) X t)) := by
      simpa only [G, zero_smul, add_zero] using
        (hG.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hLim
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [G, amp_add_smul] using hOutput s hs
  have hUpper : ∀ x ∈ inverseTestValues (amp N Z) (amp N V) t, x ≤ d := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨X, rfl⟩
    · exact hd
    · exact hTest X
  exact ⟨⟨d, hUpper⟩, csSup_le ⟨0, Set.mem_insert _ _⟩ hUpper⟩

/-- Uniform contraction for the original channel on the finite arithmetic
inverse domain, including singular input and output bases. -/
def VariationalArithmeticBound (N : QuantumChannel a b) (c : ℝ) : Prop :=
  ∀ {R : Type u} [Fintype R] [DecidableEq R]
    (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ), Z.PosSemidef →
    partialTraceRight V = 0 → t ∈ Set.Icc 0 1 → BddAbove (inverseTestValues Z V t) →
    BddAbove (inverseTestValues (amp N Z) (amp N V) t) ∧
      variationalInverse (amp N Z) (amp N V) t ≤ c * variationalInverse Z V t

private lemma depolarizedInverse_le_variational (N : QuantumChannel a b) (δ : Weight)
    (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ) (hZ : Z.PosDef)
    (hV : partialTraceRight V = 0) (ht : t ∈ Set.Icc 0 1)
    (hFin : BddAbove (inverseTestValues (amp N Z) (amp N V) t)) :
    q (amp ((depolarizingChannel b δ).comp N) Z)
        (amp ((depolarizingChannel b δ).comp N) V) t ≤
      (1 - (δ : ℝ)) * variationalInverse (amp N Z) (amp N V) t := by
  let M := (depolarizingChannel b δ).comp N
  let T := amp N Z
  let U := amp N V
  let s : ℝ := 1 - (δ : ℝ)
  have hs : 0 ≤ s := sub_nonneg.mpr δ.2.2.le
  have hOut : 0 ≤ variationalInverse T U t := le_csSup hFin (Set.mem_insert _ _)
  have hPtr : partialTraceRight U = 0 := (ptr_amp N V).trans hV
  have hU : replacementMatrix U = 0 := by
    simp only [replacementMatrix, hPtr, Matrix.zero_kronecker]
  have hVδ : amp M V = s • U := by rw [amp_depolarized, hU, smul_zero, add_zero]
  change q (amp M Z) (amp M V) t ≤ s * variationalInverse T U t
  by_cases hj : Nonempty (R × a)
  · have : Nonempty a := Nonempty.map Prod.snd hj
    have : Nonempty b := density_nonempty (N.mapState (uniformState a))
    have hFaithful := amp_posDef M (depolarized_posDef N δ) Z hZ
    let X := inverseMatrix (amp M Z) (amp M V) t
    have hTest : inverseTest T U X t ≤ variationalInverse T U t :=
      le_csSup hFin (Set.mem_insert_of_mem _ (Set.mem_range_self X))
    have hT : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
        (referenceAction_nonneg N (CStarMatrix.ofMatrix Z)
          (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hZ.posSemidef.nonneg)))
    have hK : (replacementMatrix T).PosSemidef :=
      (partialTraceRight_posSemidef hT).kronecker ((Matrix.PosSemidef.one (n := b)).smul
        (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card b)) : 0 ≤ (Fintype.card b : ℝ)⁻¹))
    have he := energy_nonneg (replacementMatrix T) X t hK ht
    rw [← inverseTest_inverseMatrix (amp M Z) (amp M V) t hFaithful ht]
    change inverseTest (amp M Z) (amp M V) X t ≤ s * variationalInverse T U t
    rw [hVδ, show amp M Z = s • T + (δ : ℝ) • replacementMatrix T from amp_depolarized N δ Z]
    unfold inverseTest at hTest ⊢
    rw [energy_linear_base, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    nlinarith only [mul_le_mul_of_nonneg_left hTest hs, mul_nonneg δ.2.1.le he]
  · have hz : V = 0 := by ext i; exact (hj ⟨i⟩).elim
    have hu : U = 0 := by
      rw [show U = amp N V from rfl, hz]
      simpa only [zero_smul] using amp_smul N (0 : ℝ) Z
    rw [hVδ, hu, smul_zero, q_eq_trace, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re]
    simpa only [hu] using mul_nonneg hs hOut

/-- The common complete and conditional entropy coefficient is also the
sharp bound for the actual arithmetic inverse metric on its finite domain. -/
theorem isLeast_variationalArithmeticBound (N : QuantumChannel a b) :
    IsLeast {c : ℝ | c ∈ Set.Icc 0 1 ∧ VariationalArithmeticBound N c}
      (completeCoefficient N) := by
  refine ⟨⟨completeCoefficient_bounds N, variationalInverse_channel_contraction N⟩, ?_⟩
  intro c hc
  apply (isLeast_depolarizedArithmeticBound N).2
  refine ⟨hc.1, ?_⟩
  intro δ R _ _ Z V t hZ hV ht
  obtain ⟨hFin, hEq⟩ := variationalInverse_eq_q Z V t hZ ht
  obtain ⟨hOut, hBound⟩ := hc.2 Z V t hZ.posSemidef hV ht hFin
  have hNonneg : 0 ≤ variationalInverse (amp N Z) (amp N V) t :=
    le_csSup hOut (Set.mem_insert _ _)
  calc
    _ ≤ (1 - (δ : ℝ)) * variationalInverse (amp N Z) (amp N V) t :=
      depolarizedInverse_le_variational N δ Z V t hZ hV ht hOut
    _ ≤ 1 * variationalInverse (amp N Z) (amp N V) t :=
      mul_le_mul_of_nonneg_right (sub_le_self _ δ.2.1.le) hNonneg
    _ ≤ c * q Z V t := by simpa only [one_mul, hEq] using hBound

/-- Actual output variational ratios over faithful correlated input bases and
complex directions in the partial-trace kernel. -/
def variationalMetricRatios (N : QuantumChannel a b) (t : ℝ) : Set ℝ :=
  {x | ∃ (R : Type u) (fR : Fintype R) (eR : DecidableEq R),
    letI := fR
    letI := eR
    ∃ Z V : Matrix (R × a) (R × a) ℂ, Z.PosDef ∧ partialTraceRight V = 0 ∧
      0 < q Z V t ∧ x = variationalInverse (amp N Z) (amp N V) t / q Z V t}

def variationalMetricCoefficient (N : QuantumChannel a b) (t : ℝ) : ℝ :=
  sSup (insert 0 (variationalMetricRatios N t))

private lemma variationalMetricRatios_bounds (N : QuantumChannel a b) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) :
    insert 0 (variationalMetricRatios N t) ⊆ Set.Icc 0 (completeCoefficient N) := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨R, fR, eR, Z, V, hZ, hV, hq, rfl⟩
  · exact ⟨le_rfl, (completeCoefficient_bounds N).1⟩
  · let _ := fR
    let _ := eR
    obtain ⟨hFin, hEq⟩ := variationalInverse_eq_q Z V t hZ ht
    obtain ⟨hOut, hBound⟩ := variationalInverse_channel_contraction N Z V t hZ.posSemidef hV ht hFin
    exact ⟨div_nonneg (le_csSup hOut (Set.mem_insert _ _)) hq.le,
      (div_le_iff₀ hq).mpr (hEq ▸ hBound)⟩

theorem variationalMetricCoefficient_bounds (N : QuantumChannel a b) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) :
    variationalMetricCoefficient N t ∈ Set.Icc 0 (completeCoefficient N) := by
  have hBound := variationalMetricRatios_bounds N t ht
  exact ⟨le_csSup ⟨_, fun _ hx => (hBound hx).2⟩ (Set.mem_insert _ _),
    csSup_le ⟨0, Set.mem_insert _ _⟩ fun _ hx => (hBound hx).2⟩

private lemma depolarized_endpointBound_variationalMetricCoefficient
    (N : QuantumChannel a b) (δ : Weight) :
    EndpointBound ((depolarizingChannel b δ).comp N) (variationalMetricCoefficient N 0) := by
  intro R fR eR Z V hZ hV
  let M := (depolarizingChannel b δ).comp N
  have ht : (0 : ℝ) ∈ Set.Icc 0 1 := by simp
  rcases (q_nonneg Z V 0 hZ ht).eq_or_lt with hq | hq
  · have hZero := direction_eq_zero_of_q_eq_zero Z V 0 hZ ht hq.symm
    have hAmp : amp M V = 0 := by
      rw [hZero]
      simpa only [zero_smul] using amp_smul M (0 : ℝ) Z
    change q (amp M Z) (amp M V) 0 ≤ _
    simp only [hAmp, ← hq, q_eq_trace, Matrix.conjTranspose_zero, Matrix.zero_mul,
      Matrix.trace_zero, Complex.zero_re, mul_zero, le_rfl]
  · have hFin := (variationalInverse_eq_q Z V 0 hZ ht).1
    have hOut := (variationalInverse_channel_contraction N Z V 0 hZ.posSemidef hV ht hFin).1
    have hBdd : BddAbove (insert 0 (variationalMetricRatios N 0)) :=
      ⟨_, fun _ hx => (variationalMetricRatios_bounds N 0 ht hx).2⟩
    have hRatio : variationalInverse (amp N Z) (amp N V) 0 / q Z V 0 ∈
        variationalMetricRatios N 0 := ⟨R, fR, eR, Z, V, hZ, hV, hq, rfl⟩
    calc
      _ ≤ (1 - (δ : ℝ)) * variationalInverse (amp N Z) (amp N V) 0 :=
        depolarizedInverse_le_variational N δ Z V 0 hZ hV ht hOut
      _ ≤ variationalInverse (amp N Z) (amp N V) 0 := by
        have hNonneg : 0 ≤ variationalInverse (amp N Z) (amp N V) 0 :=
          le_csSup hOut (Set.mem_insert _ _)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (sub_le_self 1 δ.2.1.le) hNonneg
      _ ≤ variationalMetricCoefficient N 0 * q Z V 0 :=
        (div_le_iff₀ hq).mp (le_csSup hBdd (Set.mem_insert_of_mem _ hRatio))

/-- The left endpoint attains the common entropy coefficient and the
supremum of the actual metric coefficients over the closed interval. -/
theorem variationalMetricCoefficient_chain (N : QuantumChannel a b) :
    variationalMetricCoefficient N 0 = completeCoefficient N ∧
    completeCoefficient N = conditionalCoefficient N ∧
    conditionalCoefficient N = sSup (variationalMetricCoefficient N '' Set.Icc 0 1) := by
  have ht : (0 : ℝ) ∈ Set.Icc 0 1 := by simp
  have hMetric := variationalMetricCoefficient_bounds N 0 ht
  have hEntropy := conditionalCoefficient_eq_completeCoefficient N
  have hReverse : conditionalCoefficient N ≤ variationalMetricCoefficient N 0 := by
    have hc : variationalMetricCoefficient N 0 ∈ Set.Icc 0 1 :=
      ⟨hMetric.1, hMetric.2.trans (completeCoefficient_bounds N).2⟩
    apply csSup_le ⟨0, Set.mem_insert _ _⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨R, fR, eR, ρ, σ, hSupp, hpos, rfl⟩
    · exact hc.1
    · let _ := fR
      let _ := eR
      exact (div_le_iff₀ hpos).mpr (supported_conditional_relativeEntropy_contraction N _ hc
        (depolarized_endpointBound_variationalMetricCoefficient N) ρ σ hSupp)
  have hZero := le_antisymm hMetric.2 (hEntropy ▸ hReverse)
  have hMem : variationalMetricCoefficient N 0 ∈ variationalMetricCoefficient N '' Set.Icc 0 1 :=
    ⟨0, ht, rfl⟩
  have hUpper : ∀ x ∈ variationalMetricCoefficient N '' Set.Icc 0 1, x ≤ completeCoefficient N := by
    rintro _ ⟨t, ht, rfl⟩
    exact (variationalMetricCoefficient_bounds N t ht).2
  refine ⟨hZero, hEntropy.symm, ?_⟩
  rw [hEntropy]
  apply le_antisymm _ (csSup_le ⟨_, hMem⟩ hUpper)
  rw [← hZero]
  exact le_csSup ⟨_, hUpper⟩ hMem

#print axioms act_depolarizingChannel
#print axioms supported_conditional_relativeEntropy_contraction_of_faithful_output
#print axioms supported_conditional_relativeEntropy_contraction
#print axioms depolarized_endpointBound_completeCoefficient
#print axioms conditionalCoefficient_eq_completeCoefficient
#print axioms isLeast_depolarizedArithmeticBound
#print axioms variationalInverse_eq_q
#print axioms variationalInverse_channel_contraction
#print axioms isLeast_variationalArithmeticBound
#print axioms variationalMetricCoefficient_bounds
#print axioms variationalMetricCoefficient_chain
end D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
