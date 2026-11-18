/- GID: D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiChannelSupportedExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Depolarized endpoint bounds control the supported conditional Umegaki deficit. -/

import D5.S3.Quantum.Divergence.UmegakiConditionalBKM
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
open D5.S3.Quantum.Divergence.UmegakiKernelContraction
open D5.S3.Quantum.Divergence.UmegakiConditionalBKM
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

#print axioms act_depolarizingChannel
#print axioms supported_conditional_relativeEntropy_contraction_of_faithful_output
#print axioms supported_conditional_relativeEntropy_contraction
end D5.S3.Quantum.Divergence.UmegakiChannelSupportedExtension
