/- GID: D5/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/DiagonalDiscord/DiagonalDiscordMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local channels preserving classical–quantum states cannot increase diagonal discord. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.Information.PartialTrace.Isometries
import D5.S3.Quantum.Measurement.Auric.CoordinatePinching
import D5.S3.Quantum.ProcessReconstruction.ReconstructionChannels
import D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Quantum.Recovery.QubitActualResidualGeometry

/-!
# Finite-dimensional monotonicity of diagonal discord

Liu–Takagi–Lloyd, *Diagonal quantum discord*, DOI 10.1088/1751-8121/ab0774,
§3.2.2, p. 9 (arXiv:1708.09076v2, §III.B.2, p. 6) state Conjecture 1 for a
measured qubit. Their Corollary 6 (arXiv v2, §III.B.2(b), p. 8) proves
monotonicity under local discord-nongenerating channels for measured dimension
greater than two in Section III.B's setting of a nondegenerate measured
marginal. The results here prove monotonicity for every local CPTP channel
preserving classical–quantum states, including degenerate measured marginals.
The comparison exhibits minimizing eigenbases at both the input and the output.
Specializing it to `a = Fin 2` gives the inequality of Conjecture 1.

The image of an eligible input pinching has the same marginal as the actual
output. Any basis making that image classical–quantum is therefore eligible
for the output. The fixed-pinching Pythagorean decomposition uses Gour, Marvian
and Spekkens (arXiv:0901.0943v2, Theorem 3 and its proof, pp. 3–4,
Eqs. (9)–(13), especially Eq. (12) for the trace-log equality). The Lean proof
handles support inclusion for singular states. The decomposition and channel
data processing give the pointwise bound with its nonnegative residual.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity

open scoped BigOperators CStarAlgebra ComplexOrder Kronecker _root_.Matrix MatrixOrder
open _root_.Matrix
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance (partialTrace_isometries)
open D5.S3.Quantum.Measurement.Auric.CoordinatePinching
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality (partialTraceRight_sum)
open D5.S3.Quantum.Recovery.QubitResidualRounding (tensorLeft)

private abbrev mat {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : Matrix n n ℂ :=
  CStarMatrix.ofMatrix.symm ρ.1

section Pinching

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}

/-- Discarding the outcome of a complete projective measurement. -/
def pinch (p : CompletePVM n k) (ρ : DensityState n) : DensityState n :=
  (pinchingChannel p).mapState ρ

private theorem pinch_matrix (p : CompletePVM n k) (ρ : DensityState n) :
    mat (pinch p ρ) = unreadState p.proj (mat ρ) := by
  exact pinchingChannel_apply p (mat ρ)

private theorem recordMeasurement (p : CompletePVM n k) : IsRecordMeasurement p.proj :=
  ⟨fun j => by simpa only [Matrix.star_eq_conjTranspose] using (p.hermitian j).eq,
    p.idempotent, p.orthogonal, p.complete⟩

private theorem pinch_fixed_iff (p : CompletePVM n k) (ρ : DensityState n) :
    pinch p ρ = ρ ↔ unreadState p.proj (mat ρ) = mat ρ := by
  constructor
  · intro h
    rw [← pinch_matrix, h]
  · intro h
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    exact (pinch_matrix p ρ).trans h

private theorem pinch_idempotent (p : CompletePVM n k) (ρ : DensityState n) :
    pinch p (pinch p ρ) = pinch p ρ := by
  apply (pinch_fixed_iff p (pinch p ρ)).2
  rw [pinch_matrix]
  exact unreadState_idempotent (recordMeasurement p) (mat ρ)

omit [DecidableEq n] in
private theorem compression_form (P X : Matrix n n ℂ) (hP : Pᴴ = P) (x : n → ℂ) :
    star x ⬝ᵥ ((P * X * P) *ᵥ x) =
      star (P *ᵥ x) ⬝ᵥ (X *ᵥ (P *ᵥ x)) := by
  calc
    _ = star x ⬝ᵥ ((Pᴴ * X * P) *ᵥ x) := by rw [hP]
    _ = _ := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec,
        Matrix.vecMul_conjTranspose, star_star]

/-- Pinching contains the support of the input, even at singular states. -/
theorem supportContained_pinch (p : CompletePVM n k) (ρ : DensityState n) :
    SupportContained ρ (pinch p ρ) := by
  intro x hx
  change mat (pinch p ρ) *ᵥ x = 0 at hx
  change mat ρ *ᵥ x = 0
  rw [pinch_matrix] at hx
  have hρ := density_posSemidef ρ
  have hsum : (∑ j, star (p.proj j *ᵥ x) ⬝ᵥ (mat ρ *ᵥ (p.proj j *ᵥ x))) = 0 := by
    have h := congrArg (fun y : n → ℂ => star x ⬝ᵥ y) hx
    simp only [unreadState, Matrix.sum_mulVec, dotProduct_sum, dotProduct_zero] at h
    simpa only [fun j => compression_form (p.proj j) (mat ρ) (p.hermitian j).eq x] using h
  have hzero (j : Fin k) : mat ρ *ᵥ (p.proj j *ᵥ x) = 0 := by
    apply hρ.dotProduct_mulVec_zero_iff.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => hρ.dotProduct_mulVec_nonneg (p.proj i *ᵥ x))).mp
      hsum j (Finset.mem_univ j)
  calc
    mat ρ *ᵥ x = mat ρ *ᵥ ((∑ j, p.proj j) *ᵥ x) := by
      rw [p.complete, Matrix.one_mulVec]
    _ = 0 := by simp only [Matrix.sum_mulVec, Matrix.mulVec_sum, hzero, Finset.sum_const_zero]

private theorem unread_fixed_iff_commute (p : CompletePVM n k) (X : Matrix n n ℂ) :
    unreadState p.proj X = X ↔ ∀ j, Commute X (p.proj j) := by
  classical
  constructor
  · intro h j
    have hoff := (unreadState_fixed_iff (recordMeasurement p) X).mp h
    change X * p.proj j = p.proj j * X
    calc
      _ = ∑ i, p.proj i * X * p.proj j := by
        rw [← Matrix.sum_mul, ← Matrix.sum_mul, p.complete, Matrix.one_mul]
      _ = p.proj j * X * p.proj j := by
        refine Finset.sum_eq_single j (fun i _ hij => hoff i j hij) (by simp)
      _ = ∑ i, p.proj j * X * p.proj i := by
        symm
        refine Finset.sum_eq_single j (fun i _ hij => hoff j i hij.symm) (by simp)
      _ = _ := by rw [← Matrix.mul_sum, p.complete, Matrix.mul_one]
  · intro h
    unfold unreadState
    calc
      _ = ∑ j, X * p.proj j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← (h j).eq, Matrix.mul_assoc, p.idempotent]
      _ = _ := by rw [← Matrix.mul_sum, p.complete, Matrix.mul_one]

private theorem trace_log_fixed (p : CompletePVM n k) (ρ τ : DensityState n)
    (hτ : pinch p τ = τ) :
    Matrix.trace ((pinch p ρ).1 * CFC.log τ.1) =
      Matrix.trace (ρ.1 * CFC.log τ.1) := by
  let L := CStarMatrix.ofMatrix.symm (CFC.log τ.1)
  have hcomm := (unread_fixed_iff_commute p (mat τ)).1 ((pinch_fixed_iff p τ).1 hτ)
  have hL : unreadState p.proj L = L := by
    apply (unread_fixed_iff_commute p L).2
    intro j
    have h : Commute τ.1 (CStarMatrix.ofMatrix (p.proj j)) := by
      change mat τ * p.proj j = p.proj j * mat τ
      exact (hcomm j).eq
    let _ : ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    have hlog := (h.cfc_real Real.log).eq
    change L * p.proj j = p.proj j * L at hlog
    exact hlog
  change Matrix.trace (mat (pinch p ρ) * L) = Matrix.trace (mat ρ * L)
  rw [pinch_matrix, trace_pinching p, hL]

/-- The actual entropy gain is the supported finite trace-log divergence. -/
theorem finiteTraceLogRelativeEntropy_pinch (p : CompletePVM n k) (ρ : DensityState n) :
    finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      vonNeumannEntropy (pinch p ρ) - vonNeumannEntropy ρ := by
  have hsplit : finiteTraceLogRelativeEntropy ρ (pinch p ρ) =
      -vonNeumannEntropy ρ - (Matrix.trace (ρ.1 * CFC.log (pinch p ρ).1)).re :=
    quantum_relative_entropy_eq_neg_entropy_sub_cross ρ (pinch p ρ)
  rw [hsplit, ← trace_log_fixed p ρ (pinch p ρ) (pinch_idempotent p ρ)]
  unfold vonNeumannEntropy
  ring

private theorem supported_channel_dpi
    {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m] [Nonempty n]
    (Φ : QuantumChannel n m) {ρ τ : DensityState n} (h : SupportContained ρ τ) :
    SupportContained (Φ.mapState ρ) (Φ.mapState τ) ∧
      finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState τ) ≤
        finiteTraceLogRelativeEntropy ρ τ := by
  have hd := extended_quantum_relative_entropy_channel_dpi Φ ρ τ
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support h] at hd
  have hout : SupportContained (Φ.mapState ρ) (Φ.mapState τ) := by
    apply (extendedQuantumRelativeEntropy_ne_top_iff _ _).1
    intro ht
    rw [ht] at hd
    exact WithTop.coe_ne_top (top_le_iff.mp hd)
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hout] at hd
  exact ⟨hout, WithTop.coe_le_coe.mp hd⟩

/-- Supported Pythagoras for a projective pinching and a fixed reference.
The third support witness follows by applying DPI to the pinching itself. -/
theorem extendedQuantumRelativeEntropy_pinch_pythagoras [Nonempty n]
    (p : CompletePVM n k) (ρ τ : DensityState n)
    (hτ : pinch p τ = τ) (h : SupportContained ρ τ) :
    extendedQuantumRelativeEntropy ρ τ =
      extendedQuantumRelativeEntropy ρ (pinch p ρ) +
        extendedQuantumRelativeEntropy (pinch p ρ) τ := by
  have hout : SupportContained (pinch p ρ) (pinch p τ) :=
    (supported_channel_dpi (pinchingChannel p) h).1
  rw [hτ] at hout
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support h,
    extendedQuantumRelativeEntropy_eq_coe_of_support (supportContained_pinch p ρ),
    extendedQuantumRelativeEntropy_eq_coe_of_support hout, ← WithTop.coe_add]
  congr 1
  rw [finiteTraceLogRelativeEntropy_pinch]
  have split (σ : DensityState n) : finiteTraceLogRelativeEntropy σ τ =
      -vonNeumannEntropy σ - (Matrix.trace (σ.1 * CFC.log τ.1)).re :=
    quantum_relative_entropy_eq_neg_entropy_sub_cross σ τ
  rw [split ρ, split (pinch p ρ), trace_log_fixed p ρ τ hτ]
  ring

private theorem finiteTraceLogRelativeEntropy_nonneg [Nonempty n]
    {ρ τ : DensityState n} (h : SupportContained ρ τ) :
    0 ≤ finiteTraceLogRelativeEntropy ρ τ := by
  let discard : QuantumChannel n PUnit :=
    UnitaryReconstruction.discard (Equiv.prodPUnit n).symm
  have hstate : discard.mapState ρ = discard.mapState τ := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext ⟨⟩ ⟨⟩
    simpa [Matrix.trace, Matrix.diag] using
      (discard.mapState ρ).trace_eq_one.trans (discard.mapState τ).trace_eq_one.symm
  simpa only [hstate, finiteTraceLogRelativeEntropy_self] using
    (supported_channel_dpi discard h).2

end Pinching

section Local

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private def mapPVM {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {k : ℕ} (f : Matrix n n ℂ →⋆ₐ[ℂ] Matrix m m ℂ) (p : CompletePVM n k) :
    CompletePVM m k where
  proj j := f (p.proj j)
  hermitian j := by
    change star (f (p.proj j)) = f (p.proj j)
    rw [← map_star, Matrix.star_eq_conjTranspose, (p.hermitian j).eq]
  idempotent j := by rw [← map_mul, p.idempotent]
  orthogonal i j hij := by rw [← map_mul, p.orthogonal i j hij, map_zero]
  complete := by rw [← map_sum, p.complete, map_one]

private def basisPVM (U : Matrix.unitaryGroup a ℂ) : CompletePVM a (Fintype.card a) :=
  mapPVM (Unitary.conjStarAlgAut ℂ _ U).toStarAlgHom (coordinatePVM (Fintype.equivFin a))

/-- The rank-one A projectors in basis U, tensored with the identity on B. -/
def localPVM (U : Matrix.unitaryGroup a ℂ) : CompletePVM (a × b) (Fintype.card a) :=
  mapPVM (tensorLeft (A := a) (B := b)) (basisPVM U)

private theorem tensorLeft_kraus_normalized [Nonempty a] (Λ : QuantumChannel a a) :
    (∑ j, (tensorLeft (A := a) (B := b) ((actual_kraus_representation Λ).kraus j))ᴴ *
      tensorLeft (A := a) (B := b) ((actual_kraus_representation Λ).kraus j)) = 1 := by
  let M := actual_kraus_representation Λ
  let f := tensorLeft (A := a) (B := b)
  change (∑ j, (f (M.kraus j))ᴴ * f (M.kraus j)) = 1
  have hstar (j : Fin (Fintype.card a) × Fin (Fintype.card a)) :
      (f (M.kraus j))ᴴ = f ((M.kraus j)ᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose] using (map_star f (M.kraus j)).symm
  simp_rw [hstar, ← map_mul f]
  rw [← map_sum, M.hkraus, map_one]

/-- The channel Λ ⊗ id_B, obtained by tensoring each actual Kraus operator
of Λ with the identity on B. -/
def localChannel [Nonempty a] (Λ : QuantumChannel a a) :
    QuantumChannel (a × b) (a × b) :=
  (finite_kraus_quantum_channel
    (fun j => tensorLeft (A := a) (B := b) ((actual_kraus_representation Λ).kraus j))
    (tensorLeft_kraus_normalized (b := b) Λ)).choose

/-- The Kraus action on the entire joint matrix algebra. -/
theorem localChannel_apply [Nonempty a] (Λ : QuantumChannel a a)
    (X : Matrix (a × b) (a × b) ℂ) :
    let M := actual_kraus_representation Λ
    CStarMatrix.ofMatrix.symm
      ((localChannel (b := b) Λ).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ j, (M.kraus j ⊗ₖ (1 : Matrix b b ℂ)) * X *
        (M.kraus j ⊗ₖ (1 : Matrix b b ℂ))ᴴ :=
  (finite_kraus_quantum_channel
    (fun j => tensorLeft (A := a) (B := b) ((actual_kraus_representation Λ).kraus j))
    (tensorLeft_kraus_normalized (b := b) Λ)).choose_spec X

theorem marginalRight_localChannel [Nonempty a] (Λ : QuantumChannel a a)
    (ρ : DensityState (a × b)) :
    marginalRight ((localChannel Λ).mapState ρ) = Λ.mapState (marginalRight ρ) := by
  let T := localChannel (b := b) Λ
  let M := actual_kraus_representation Λ
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceRight (CStarMatrix.ofMatrix.symm
    (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix (mat ρ)))) =
    CStarMatrix.ofMatrix.symm (Λ.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (partialTraceRight (mat ρ))))
  rw [localChannel_apply Λ (mat ρ), M.haction (partialTraceRight (mat ρ)),
    partialTraceRight_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact partialTrace_isometries (M.kraus j) (1 : Matrix b b ℂ) (by simp) (mat ρ)

private theorem marginal_pinch_matrix (U : Matrix.unitaryGroup a ℂ)
    (ρ : DensityState (a × b)) :
    mat (marginalRight (pinch (localPVM U) ρ)) =
      unreadState (basisPVM U).proj (mat (marginalRight ρ)) := by
  change partialTraceRight (mat (pinch (localPVM U) ρ)) = _
  rw [pinch_matrix]
  unfold unreadState
  let p := basisPVM U
  let K := (localPVM (b := b) U).proj
  rw [partialTraceRight_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hp : (K j)ᴴ = K j := ((localPVM (b := b) U).hermitian j).eq
  calc
    partialTraceRight (K j * mat ρ * K j) =
        partialTraceRight (K j * mat ρ * (K j)ᴴ) := by rw [hp]
    _ = p.proj j * partialTraceRight (mat ρ) * (p.proj j)ᴴ :=
      partialTrace_isometries (p.proj j) (1 : Matrix b b ℂ) (by simp) (mat ρ)
    _ = p.proj j * partialTraceRight (mat ρ) * p.proj j := by rw [(p.hermitian j).eq]

/-- The actual A marginal is diagonal in U. Degenerate eigenspaces allow all
unitary choices within them. -/
def Eligible (ρ : DensityState (a × b)) (U : Matrix.unitaryGroup a ℂ) : Prop :=
  ((Unitary.conjStarAlgAut ℂ _ U).symm (mat (marginalRight ρ))).IsDiag

private theorem coordinateUnread_apply {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (c : n → Fin k) (X : Matrix n n ℂ) (i j : n) :
    unreadState (coordinatePVM c).proj X i j = if c i = c j then X i j else 0 := by
  classical
  simp only [unreadState, Matrix.sum_apply, coordinatePVM, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  by_cases hij : c i = c j
  · rw [ite_eq_left hij, Finset.sum_eq_single (c i)]
    · simp [hij]
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hid : c i = d
    · have hjd : c j ≠ d := fun he => hij (hid.trans he.symm)
      simp [hid, hjd]
    · simp [hid]

private theorem basisUnread_fixed_iff (U : Matrix.unitaryGroup a ℂ) (X : Matrix a a ℂ) :
    unreadState (basisPVM U).proj X = X ↔
      ((Unitary.conjStarAlgAut ℂ _ U).symm X).IsDiag := by
  let f := Unitary.conjStarAlgAut ℂ (Matrix a a ℂ) U
  let c := Fintype.equivFin a
  let Y := f.symm X
  have hmap : f.symm (unreadState (basisPVM U).proj X) =
      unreadState (coordinatePVM c).proj Y := by
    change f.symm (∑ j, f ((coordinatePVM c).proj j) * X * f ((coordinatePVM c).proj j)) = _
    simp only [unreadState, map_sum, map_mul, StarAlgEquiv.symm_apply_apply, Y]
  have he : unreadState (basisPVM U).proj X = X ↔
      unreadState (coordinatePVM c).proj Y = Y := by
    constructor
    · intro h
      exact hmap.symm.trans (congrArg f.symm h)
    · intro h
      exact f.symm.injective (hmap.trans h)
  rw [he]
  change unreadState (coordinatePVM c).proj Y = Y ↔ Y.IsDiag
  constructor
  · intro h i j hij
    have he := congrArg (fun M : Matrix a a ℂ => M i j) h
    rw [coordinateUnread_apply, ite_eq_right (fun e => hij (c.injective e))] at he
    exact he.symm
  · intro h
    ext i j
    rw [coordinateUnread_apply]
    by_cases hij : i = j
    · subst j
      simp
    · rw [ite_eq_right (fun e => hij (c.injective e)), h hij]

private theorem eligible_iff_marginal_pinch (ρ : DensityState (a × b))
    (U : Matrix.unitaryGroup a ℂ) :
    Eligible ρ U ↔ marginalRight (pinch (localPVM U) ρ) = marginalRight ρ := by
  have hval : Function.Injective (fun σ : DensityState a => mat σ) :=
    fun _ _ h => Subtype.ext (CStarMatrix.ofMatrix.symm.injective h)
  have he : mat (marginalRight (pinch (localPVM U) ρ)) = mat (marginalRight ρ) ↔
      Eligible ρ U :=
    (marginal_pinch_matrix U ρ ▸ basisUnread_fixed_iff U (mat (marginalRight ρ)))
  exact (hval.eq_iff.symm.trans he).symm

private theorem exists_eligible (ρ : DensityState (a × b)) :
    ∃ U : Matrix.unitaryGroup a ℂ, Eligible ρ U := by
  let X := mat (marginalRight ρ)
  let hX := (density_posSemidef (marginalRight ρ)).isHermitian
  refine ⟨hX.eigenvectorUnitary, ?_⟩
  change ((Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary).symm X).IsDiag
  let f := Unitary.conjStarAlgAut ℂ (Matrix a a ℂ) hX.eigenvectorUnitary
  have hdiag : f.symm X = Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) :=
    (congrArg (fun M : Matrix a a ℂ => f.symm M) hX.spectral_theorem).trans
      (f.symm_apply_apply _)
  change (f.symm X).IsDiag
  rw [hdiag]
  exact Matrix.isDiag_diagonal _

/-- A classical–quantum state is fixed by some rank-one A pinching.
The criterion `unreadState_fixed_iff` gives precisely the vanishing of
the off-diagonal A blocks. The diagonal blocks are PSD by compression. -/
def IsCQ (ρ : DensityState (a × b)) : Prop :=
  ∃ U : Matrix.unitaryGroup a ℂ, pinch (localPVM U) ρ = ρ

def PreservesCQ (T : QuantumChannel (a × b) (a × b)) : Prop :=
  ∀ σ, IsCQ σ → IsCQ (T.mapState σ)

/-- Entropy gain for one local basis. -/
def basisGain (ρ : DensityState (a × b)) (U : Matrix.unitaryGroup a ℂ) : ℝ :=
  vonNeumannEntropy (pinch (localPVM U) ρ) - vonNeumannEntropy ρ

/-- Diagonal discord using the infimum of all eligible entropy gains. -/
def diagonalDiscord (ρ : DensityState (a × b)) : ℝ :=
  sInf (basisGain ρ '' {U | Eligible ρ U})

private theorem basisGain_nonneg [Nonempty a] [Nonempty b]
    (ρ : DensityState (a × b)) (U : Matrix.unitaryGroup a ℂ) :
    0 ≤ basisGain ρ U := by
  unfold basisGain
  rw [← finiteTraceLogRelativeEntropy_pinch]
  exact finiteTraceLogRelativeEntropy_nonneg (supportContained_pinch _ _)

/-- For every eligible input U there is an eligible output V fixing the
processed CQ reference. Its entropy gain plus the remaining relative entropy
is bounded by the gain at U. -/
theorem pointwise_transfer [Nonempty a] [Nonempty b] (Λ : QuantumChannel a a)
    (hCQ : PreservesCQ (localChannel (b := b) Λ)) (ρ : DensityState (a × b))
    (U : Matrix.unitaryGroup a ℂ) (hU : Eligible ρ U) :
    let T := localChannel (b := b) Λ
    let R := T.mapState ρ
    let τ := T.mapState (pinch (localPVM U) ρ)
    ∃ V : Matrix.unitaryGroup a ℂ,
      Eligible R V ∧ pinch (localPVM V) τ = τ ∧
      SupportContained (pinch (localPVM V) R) τ ∧
      0 ≤ finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ∧
      basisGain R V + finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ≤
        basisGain ρ U := by
  dsimp only
  let T := localChannel (b := b) Λ
  let R := T.mapState ρ
  let τ := T.mapState (pinch (localPVM U) ρ)
  change ∃ V : Matrix.unitaryGroup a ℂ,
    Eligible R V ∧ pinch (localPVM V) τ = τ ∧
    SupportContained (pinch (localPVM V) R) τ ∧
    0 ≤ finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ∧
    basisGain R V + finiteTraceLogRelativeEntropy (pinch (localPVM V) R) τ ≤ basisGain ρ U
  obtain ⟨V, hV⟩ := hCQ (pinch (localPVM U) ρ) ⟨U, pinch_idempotent (localPVM U) ρ⟩
  change pinch (localPVM V) τ = τ at hV
  have hsame : marginalRight τ = marginalRight R := by
    dsimp only [τ, R, T]
    simp only [marginalRight_localChannel, (eligible_iff_marginal_pinch ρ U).1 hU]
    rfl
  have hVeligible : Eligible R V := by
    have h : Eligible τ V := (eligible_iff_marginal_pinch τ V).2 (congrArg marginalRight hV)
    unfold Eligible at h ⊢
    rw [hsame] at h
    exact h
  have hρ := supportContained_pinch (localPVM U) ρ
  obtain ⟨hR, hDPI⟩ := supported_channel_dpi T hρ
  change SupportContained R τ at hR
  have hQ : SupportContained (pinch (localPVM V) R) τ := by
    have hs : SupportContained (pinch (localPVM V) R) (pinch (localPVM V) τ) :=
      (supported_channel_dpi (pinchingChannel (localPVM V)) hR).1
    simpa only [hV] using hs
  have hsplit := extendedQuantumRelativeEntropy_pinch_pythagoras (localPVM V) R τ hV hR
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support hR,
    extendedQuantumRelativeEntropy_eq_coe_of_support (supportContained_pinch (localPVM V) R),
    extendedQuantumRelativeEntropy_eq_coe_of_support hQ, ← WithTop.coe_add] at hsplit
  have hsplitReal := WithTop.coe_injective hsplit
  refine ⟨V, hVeligible, hV, hQ, finiteTraceLogRelativeEntropy_nonneg hQ, ?_⟩
  change finiteTraceLogRelativeEntropy R τ ≤
    finiteTraceLogRelativeEntropy ρ (pinch (localPVM U) ρ) at hDPI
  rw [hsplitReal, finiteTraceLogRelativeEntropy_pinch (localPVM V) R,
    finiteTraceLogRelativeEntropy_pinch (localPVM U) ρ] at hDPI
  exact hDPI

/-- Finite-dimensional extension of Liu–Takagi–Lloyd Conjecture 1. -/
theorem diagonalDiscord_localChannel_mono [Nonempty a] [Nonempty b]
    (Λ : QuantumChannel a a) (hCQ : PreservesCQ (localChannel (b := b) Λ))
    (ρ : DensityState (a × b)) :
    diagonalDiscord ((localChannel Λ).mapState ρ) ≤ diagonalDiscord ρ := by
  let R := (localChannel (b := b) Λ).mapState ρ
  change diagonalDiscord R ≤ sInf (basisGain ρ '' {U | Eligible ρ U})
  obtain ⟨U₀, hU₀⟩ := exists_eligible ρ
  apply le_csInf (show (basisGain ρ '' {U | Eligible ρ U}).Nonempty from
    ⟨basisGain ρ U₀, U₀, hU₀, rfl⟩)
  rintro _ ⟨U, hU, rfl⟩
  obtain ⟨V, hV, _, _, hnonneg, hbound⟩ := pointwise_transfer Λ hCQ ρ U hU
  have hbdd : BddBelow (basisGain R '' {W | Eligible R W}) :=
    ⟨0, by rintro _ ⟨W, _, rfl⟩; exact basisGain_nonneg R W⟩
  calc
    diagonalDiscord R ≤ basisGain R V := csInf_le hbdd ⟨V, hV, rfl⟩
    _ ≤ basisGain ρ U := le_trans (le_add_of_nonneg_right hnonneg) hbound

private theorem isClosed_eligible (ρ : DensityState (a × b)) :
    IsClosed {U : Matrix.unitaryGroup a ℂ | Eligible ρ U} := by
  let X := mat (marginalRight ρ)
  have hU : Continuous (fun U : Matrix.unitaryGroup a ℂ => U.val) :=
    continuous_subtype_val
  have hconj : Continuous (fun U : Matrix.unitaryGroup a ℂ =>
      U.valᴴ * X * U.val) :=
    (hU.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hU
  have heq : {U : Matrix.unitaryGroup a ℂ | Eligible ρ U} =
      ⋂ i : a, ⋂ j : a, ⋂ (_ : i ≠ j), {U | (U.valᴴ * X * U.val) i j = 0} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (hconj.matrix_elem i j) continuous_const

private theorem continuous_pinch_matrix (ρ : DensityState (a × b)) :
    Continuous (fun U : Matrix.unitaryGroup a ℂ => mat (pinch (localPVM U) ρ)) := by
  have hU : Continuous (fun U : Matrix.unitaryGroup a ℂ => U.val) :=
    continuous_subtype_val
  have hproj (j : Fin (Fintype.card a)) :
      Continuous (fun U : Matrix.unitaryGroup a ℂ => (localPVM (b := b) U).proj j) := by
    let E := (coordinatePVM (Fintype.equivFin a)).proj j
    have h : Continuous (fun U : Matrix.unitaryGroup a ℂ => U.val * E * U.valᴴ) :=
      (hU.matrix_mul continuous_const).matrix_mul hU.matrix_conjTranspose
    change Continuous (fun U : Matrix.unitaryGroup a ℂ =>
      (U.val * E * U.valᴴ) ⊗ₖ (1 : Matrix b b ℂ))
    refine continuous_matrix fun i j => ?_
    exact (h.matrix_elem i.1 j.1).mul continuous_const
  simp only [pinch_matrix, unreadState]
  exact continuous_finsetSum _ fun j _ =>
    ((hproj j).matrix_mul continuous_const).matrix_mul (hproj j)

private theorem continuous_basisGain (ρ : DensityState (a × b)) :
    Continuous (basisGain ρ) := by
  open D5.S3.Quantum.Information.OrthogonalRecordEntropy in
  have hEntropy : Continuous (fun U : Matrix.unitaryGroup a ℂ =>
      vonNeumannEntropy (pinch (localPVM U) ρ)) := by
    let _ : ContinuousFunctionalCalculus ℝ (CStarMatrix (a × b) (a × b) ℂ) IsSelfAdjoint :=
      IsSelfAdjoint.instContinuousFunctionalCalculus
    have hmat : Continuous (fun U : Matrix.unitaryGroup a ℂ =>
        (pinch (localPVM U) ρ).1) :=
      (CStarMatrix.ofMatrixL (m := a × b) (n := a × b) (A := ℂ)).continuous.comp
        (continuous_pinch_matrix ρ)
    have hCfc := hmat.cfc_of_mem_nhdsSet (s := (Set.univ : Set ℝ)) Real.negMulLog
      Filter.univ_mem (fun U => IsSelfAdjoint.of_nonneg (pinch (localPVM U) ρ).nonnegative)
      Real.continuous_negMulLog.continuousOn
    have hTrace : Continuous (realTrace : CStarMatrix (a × b) (a × b) ℂ → ℝ) :=
      Complex.continuous_re.comp
        ((CStarMatrix.ofMatrixL (m := a × b) (n := a × b) (A := ℂ)).symm.continuous.matrix_trace)
    exact (hTrace.comp hCfc).congr fun U => (entropy_eq_trace_cfc (pinch (localPVM U) ρ)).symm
  exact hEntropy.sub continuous_const

/-- Every finite bipartite state has an eligible eigenbasis attaining the
    diagonal discord. The same basis minimizes the entropy gain over all
    choices in each degenerate eigenspace. -/
theorem diagonalDiscord_attained (ρ : DensityState (a × b)) :
    ∃ U : Matrix.unitaryGroup a ℂ, Eligible ρ U ∧
      IsMinOn (basisGain ρ) {V | Eligible ρ V} U ∧
      diagonalDiscord ρ = basisGain ρ U := by
  let _ : CompactSpace (Matrix.unitaryGroup a ℂ) :=
    D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.unitaryCompactSpace
  obtain ⟨U, hU, hmin⟩ := (isClosed_eligible ρ).isCompact.exists_isMinOn
    (exists_eligible ρ) (continuous_basisGain ρ).continuousOn
  have hbelow : ∀ x ∈ basisGain ρ '' {V | Eligible ρ V}, basisGain ρ U ≤ x := by
    rintro _ ⟨V, hV, rfl⟩
    exact hmin hV
  refine ⟨U, hU, hmin, le_antisymm ?_ ?_⟩
  · exact csInf_le ⟨_, hbelow⟩ ⟨U, hU, rfl⟩
  · exact le_csInf ⟨_, U, hU, rfl⟩ hbelow

/-- Conjecture 1 with the input and output optima expressed as attained
    minima, in arbitrary finite dimensions. -/
theorem diagonalDiscord_localChannel_mono_attained [Nonempty a] [Nonempty b]
    (Λ : QuantumChannel a a) (hCQ : PreservesCQ (localChannel (b := b) Λ))
    (ρ : DensityState (a × b)) :
    let R := (localChannel (b := b) Λ).mapState ρ
    ∃ U V : Matrix.unitaryGroup a ℂ,
      Eligible ρ U ∧ Eligible R V ∧
      IsMinOn (basisGain ρ) {W | Eligible ρ W} U ∧
      IsMinOn (basisGain R) {W | Eligible R W} V ∧
      basisGain R V ≤ basisGain ρ U := by
  dsimp only
  obtain ⟨U, hU, hUmin, hUeq⟩ := diagonalDiscord_attained ρ
  obtain ⟨V, hV, hVmin, hVeq⟩ := diagonalDiscord_attained ((localChannel Λ).mapState ρ)
  exact ⟨U, V, hU, hV, hUmin, hVmin,
    hVeq.symm.trans_le ((diagonalDiscord_localChannel_mono Λ hCQ ρ).trans_eq hUeq)⟩

end Local

end D5.S3.Quantum.Information.DiagonalDiscord.DiagonalDiscordMonotonicity
