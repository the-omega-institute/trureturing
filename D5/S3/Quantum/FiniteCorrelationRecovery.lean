/- GID: D5/S3/Quantum/FiniteCorrelationRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/FiniteCorrelationRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Centered contraction endpoints and finite-state support compression. -/
import D5.S3.Quantum.FixedPointProjection
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Weil.ZetaLinear.RankTrace

/-!
admission_basis: escape-witness
escape_witness: Endpoint.fixedDimensionOfCenteredCorrelation
Compactness attains centered correlation one. The maximizing vector and the
invariant vector give two independent fixed directions. Spectral support frames
then permit compression of singular marginals.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22403
-/

open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
section r2_gram_contraction
open scoped ENNReal NNReal
noncomputable section
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Gram
open D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
variable {E F A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A] [Nontrivial A] [NormOneClass A]
lemma gramContractionOfPositiveSimilarity
    (C : E →L[ℂ] F) (U : A →ₗ[ℂ] A)
    (hpos : ∀ X, 0 ≤ X → 0 ≤ U X)
    (σ : A) (hσ : IsStrictlyPositive σ) (hfix : U σ = σ)
    (e : E ≃ₗ[ℂ] A)
    (he : ∀ x : E, U (e x) = e (C.adjoint (C x))) : ‖C‖ ≤ 1 := by
  let G := C.adjoint.comp C
  have hG : IsSelfAdjoint G := by
    dsimp only [G]
    have hI : IsSelfAdjoint (1 : F →L[ℂ] F) := IsSelfAdjoint.one _
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
      ContinuousLinearMap.comp_id] using hI.adjoint_conj C
  have hb (z : ℂ) (hz : z ∈ spectrum ℂ G) : ‖z‖ ≤ 1 := by
    have hz' : z ∈ spectrum ℂ G.toLinearMap := by
      rwa [ContinuousLinearMap.spectrum_eq] at hz
    obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
    have hvU : Module.End.HasEigenvector U z (e v) := by
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · rw [he]
        change e (G v) = z • e v
        have hgv : G v = z • v := Module.End.mem_eigenspace_iff.mp hv.1
        rw [hgv, map_smul]
      · intro hzv
        apply hv.2
        simpa using congrArg e.symm hzv
    exact faithful_fixed_eigenvalue_norm_le_one U hpos σ hσ hfix z
      (Module.End.hasEigenvalue_of_hasEigenvector hvU)
  have hr : spectralRadius ℂ G ≤ 1 := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun z hz => ?_
    exact_mod_cast hb z hz
  have hGn : ‖G‖ ≤ 1 := by
    rw [G.spectralRadius_eq_nnnorm hG] at hr
    exact_mod_cast hr
  have hCsq : ‖C‖ ^ 2 ≤ 1 := by
    simpa only [G, ContinuousLinearMap.norm_adjoint_comp_self, pow_two] using hGn
  nlinarith [norm_nonneg C]
end D5.S3.Quantum.FiniteCorrelationRecovery.Gram
end
end r2_gram_contraction
section r2_contraction_endpoint
open Complex
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
private lemma adjointFixedOfNormEq
    (C : E →L[ℂ] F) (hC : ‖C‖ ≤ 1) (x : E) (hx : ‖C x‖ = ‖x‖) :
    C.adjoint (C x) = x := by
  have ha : ‖C.adjoint (C x)‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖C.adjoint‖ * ‖C x‖ := C.adjoint.le_opNorm _
      _ ≤ 1 * ‖x‖ := by rw [ContinuousLinearMap.adjoint.norm_map, hx]; gcongr
      _ = ‖x‖ := one_mul _
  have hi : RCLike.re (inner ℂ (C.adjoint (C x)) x) = ‖x‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq, hx]
  have hn : ‖C.adjoint (C x) - x‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hi]
    have hnonneg := sq_nonneg ‖C.adjoint (C x) - x‖
    rw [norm_sub_sq (𝕜 := ℂ), hi] at hnonneg
    nlinarith [norm_nonneg (C.adjoint (C x)), norm_nonneg x]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
end D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
end
end r2_contraction_endpoint
section r2_centered_endpoint
open Set Complex
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
def centeredUnit (e : E) : Set E := {x | ‖x‖ = 1 ∧ inner ℂ e x = 0}
private lemma centeredUnitCompact (e : E) : IsCompact (centeredUnit e) := by
  letI : ProperSpace E := FiniteDimensional.proper ℂ E
  have hs : IsCompact {x : E | ‖x‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using (isCompact_sphere (0 : E) (1 : ℝ))
  have hc : IsClosed {x : E | inner ℂ e x = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact hs.inter_right hc

def centeredCorrelationValues (C : E →L[ℂ] F) (e : E) (f : F) : Set ℝ :=
  (fun p : E × F => ‖inner ℂ (C p.1) p.2‖) '' (centeredUnit e ×ˢ centeredUnit f)
private lemma centeredCorrelationValuesLeOne
    (C : E →L[ℂ] F) (hC : ‖C‖ ≤ 1) (e : E) (f : F)
    (r : ℝ) (hr : r ∈ centeredCorrelationValues C e f) : r ≤ 1 := by
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩ := hr
  calc
    _ ≤ ‖C x‖ * ‖y‖ := norm_inner_le_norm (𝕜 := ℂ) (C x) y
    _ = ‖C x‖ := by rw [hy.1, mul_one]
    _ ≤ ‖C‖ * ‖x‖ := C.le_opNorm x
    _ ≤ 1 := by rw [hx.1, mul_one]; exact hC
private lemma sSupCenteredEqOneOfSubvalues
    (C : E →L[ℂ] F) (hC : ‖C‖ ≤ 1) (e : E) (f : F)
    (S : Set ℝ) (hS : S ⊆ centeredCorrelationValues C e f) (hs : sSup S = 1) :
    sSup (centeredCorrelationValues C e f) = 1 := by
  have hne : S.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, Real.sSup_empty] at hs
    norm_num at hs
  have ht : BddAbove (centeredCorrelationValues C e f) :=
    ⟨1, centeredCorrelationValuesLeOne C hC e f⟩
  apply le_antisymm
  · exact csSup_le (hne.mono hS) (centeredCorrelationValuesLeOne C hC e f)
  · rw [← hs]
    exact csSup_le_csSup ht hne hS
private lemma fixedVectorOfCorrelationSupOne [CompleteSpace E] [CompleteSpace F]
    (C : E →L[ℂ] F) (hC : ‖C‖ ≤ 1) (e : E) (f : F)
    (hmu : sSup (centeredCorrelationValues C e f) = 1) :
    ∃ x : E, ‖x‖ = 1 ∧ inner ℂ e x = 0 ∧ C.adjoint (C x) = x := by
  let S := centeredCorrelationValues C e f
  have hc : IsCompact S :=
    ((centeredUnitCompact e).prod (centeredUnitCompact f)).image
      ((C.continuous.comp continuous_fst).inner continuous_snd).norm
  have hne : S.Nonempty := by
    by_contra hn
    have hz : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change sSup S = 1 at hmu
    rw [hz, Real.sSup_empty] at hmu
    norm_num at hmu
  have hm : (1 : ℝ) ∈ S := by
    rw [← hmu]
    exact hc.sSup_mem hne
  obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, hxy⟩ := hm
  have hx1 : ‖x‖ = 1 := hx.1
  have hy1 : ‖y‖ = 1 := hy.1
  have hu : ‖C x‖ ≤ 1 := by
    calc
      _ ≤ ‖C‖ * ‖x‖ := C.le_opNorm x
      _ ≤ 1 := by rw [hx1, mul_one]; exact hC
  have hl : 1 ≤ ‖C x‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℂ) (C x) y
    simpa only [hxy, hy1, mul_one] using hh
  have heq : ‖C x‖ = ‖x‖ := (le_antisymm hu hl).trans hx1.symm
  exact ⟨x, hx1, hx.2, adjointFixedOfNormEq C hC x heq⟩
end D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
end
end r2_centered_endpoint
section r2_fixed_dimension_endpoint
open Complex
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [CompleteSpace E] [CompleteSpace F]
lemma fixedDimensionOfCenteredCorrelation
    (C : E →L[ℂ] F) (hC : ‖C‖ ≤ 1) (v : E) (f : F) (hv0 : v ≠ 0)
    (U : V →ₗ[ℂ] V) (e : E ≃ₗ[ℂ] V)
    (he : ∀ x : E, U (e x) = e (C.adjoint (C x)))
    (hv : U (e v) = e v)
    (S : Set ℝ) (hS : S ⊆ centeredCorrelationValues C v f) (hmu : sSup S = 1) :
    1 < Module.finrank ℂ U.fixedSubmodule := by
  have hfull := sSupCenteredEqOneOfSubvalues C hC v f S hS hmu
  obtain ⟨x, hx1, horth, hfix⟩ := fixedVectorOfCorrelationSupOne C hC v f hfull
  have hx0 : x ≠ 0 := by intro hz; simp [hz] at hx1
  let w : Fin 2 → E := ![v,x]
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [w] using hv0
    · simpa [w] using hx0
  have hwo : Pairwise (fun i j => inner ℂ (w i) (w j) = 0) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [w, inner_eq_zero_symm]
  have hli : LinearIndependent ℂ w := linearIndependent_of_ne_zero_of_inner_eq_zero hw0 hwo
  have hmap : LinearIndependent ℂ (fun i => e (w i)) := hli.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hfixed : ∀ i, U (e (w i)) = e (w i) := by
    intro i
    fin_cases i
    · exact hv
    · change U (e x) = e x
      rw [he, hfix]
  let z : Fin 2 → U.fixedSubmodule := fun i => ⟨e (w i), hfixed i⟩
  have hzli : LinearIndependent ℂ z :=
    LinearIndependent.of_comp U.fixedSubmodule.subtype hmap
  have hd := hzli.fintype_card_le_finrank
  norm_num at hd
  omega
end D5.S3.Quantum.FiniteCorrelationRecovery.Endpoint
end
end r2_fixed_dimension_endpoint
section r3_isometric_compression

open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Compression
variable {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
lemma pullPush (U : Matrix a c ℂ) (hU : Uᴴ * U = 1) (X : Matrix c c ℂ) :
    ((U)ᴴ * ((((U) * (X) * (U)ᴴ))) * (U)) = X := by
  calc
    _ = (Uᴴ * U) * X * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hU, Matrix.one_mul, Matrix.mul_one]
lemma pushMul (U : Matrix a c ℂ) (hU : Uᴴ * U = 1) (X Y : Matrix c c ℂ) :
    ((U) * (X) * (U)ᴴ) * ((U) * (Y) * (U)ᴴ) = ((U) * ((X * Y)) * (U)ᴴ) := by
  calc
    _ = U * X * (Uᴴ * U) * Y * Uᴴ := by simp only [Matrix.mul_assoc]
    _ = U * (X * Y) * Uᴴ := by rw [hU, Matrix.mul_one, Matrix.mul_assoc U X Y]
lemma pushHermitian (U : Matrix a c ℂ) (X : Matrix c c ℂ) (hX : X.IsHermitian) :
    (((U) * (X) * (U)ᴴ)).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose U hX
lemma pullHermitian (U : Matrix a c ℂ) (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    (((U)ᴴ * (X) * (U))).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul U hX
lemma pushTrace (U : Matrix a c ℂ) (hU : Uᴴ * U = 1) (X : Matrix c c ℂ) :
    (((U) * (X) * (U)ᴴ)).trace = X.trace := by
  rw [ Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
lemma tracePair (U : Matrix a c ℂ) (S : Matrix c c ℂ) (X : Matrix a a ℂ) :
    (((U) * (S) * (U)ᴴ) * X).trace = (S * ((U)ᴴ * (X) * (U))).trace := by
  simpa only [Fintype.sum_unique] using
    D5.S3.Quantum.FixedPointProjection.Kraus.rawPair (fun _ : Unit => U) S X
private lemma sqrtPush (U : Matrix a c ℂ) (hU : Uᴴ * U = 1)
    (S : Matrix c c ℂ) (hS : S.PosSemidef) :
    CFC.sqrt (((U) * (S) * (U)ᴴ)) = ((U) * ((CFC.sqrt S)) * (U)ᴴ) := by
  apply CFC.sqrt_unique
  · rw [pushMul U hU, CFC.sqrt_mul_sqrt_self S hS.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).mul_mul_conjTranspose_same U).nonneg
lemma gmPairCompress (U : Matrix a c ℂ) (hU : Uᴴ * U = 1)
    (S : Matrix c c ℂ) (hS : S.PosSemidef) (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    (Xᴴ * (CFC.sqrt ((((U) * (S) * (U)ᴴ))) * (X) * CFC.sqrt ((((U) * (S) * (U)ᴴ))))).trace =
      ((((U)ᴴ * (X) * (U)))ᴴ * (CFC.sqrt (S) * ((((U)ᴴ * (X) * (U)))) * CFC.sqrt (S))).trace := by
  rw [hX.eq, (pullHermitian U X hX).eq]
  rw [sqrtPush U hU S hS]
  have ht := Matrix.trace_mul_comm (X * U * CFC.sqrt S) (Uᴴ * X * U * CFC.sqrt S * Uᴴ)
  simpa only [Matrix.mul_assoc] using ht
end D5.S3.Quantum.FiniteCorrelationRecovery.Compression
end
end r3_isometric_compression
section r3_faithful_frame
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Compression
variable {a : Type} [Fintype a] [DecidableEq a]
structure FaithfulFrame (S : Matrix a a ℂ) where
  ι : Type
  [finiteIndex : Fintype ι]
  [decidableIndex : DecidableEq ι]
  U : Matrix a ι ℂ
  small : Matrix ι ι ℂ
  iso : Uᴴ * U = 1
  positive : small.PosDef
  reconstruct : ((U) * (small) * (U)ᴴ) = S
attribute [instance] FaithfulFrame.finiteIndex FaithfulFrame.decidableIndex
lemma existsFaithfulFrame (S : Matrix a a ℂ) (hS : S.PosSemidef) :
    Nonempty (FaithfulFrame S) := by
  classical
  let hH := hS.isHermitian
  let c : Type := {i : a // 0 < hH.eigenvalues i}
  let W : Matrix a a ℂ := hH.eigenvectorUnitary
  let U : Matrix a c ℂ := fun i j => W i j.val
  let D : Matrix c c ℂ := Matrix.diagonal (fun i => (hH.eigenvalues i.val : ℂ))
  have hW : Wᴴ * W = 1 := hH.eigenvectorUnitary.2.1
  refine ⟨⟨c, U, D, ?_, ?_, ?_⟩⟩
  · ext i j
    change (∑ k : a, star (W k i.val) * W k j.val) = if i = j then 1 else 0
    have hh := congrArg (fun M : Matrix a a ℂ => M i.val j.val) hW
    simpa only [U, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Subtype.val_inj] using hh
  · apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast i.property
  · have hs : S = W * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * Wᴴ := by
      simpa only [W, Unitary.conjStarAlgAut_apply, Function.comp_def,
        RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose] using hH.spectral_theorem
    apply Eq.trans ?_ hs.symm
    ext i j
    change (∑ k : c, (U * D) i k * Uᴴ k j) =
      ∑ k : a, (W * Matrix.diagonal (fun q => (hH.eigenvalues q : ℂ))) i k * Wᴴ k j
    simp only [D, Matrix.mul_diagonal]
    change (∑ k : c, W i k.val * (hH.eigenvalues k.val : ℂ) * star (W j k.val)) =
      ∑ k : a, W i k * (hH.eigenvalues k : ℂ) * star (W j k)
    symm
    apply Finset.sum_congr_set (s := {k : a | 0 < hH.eigenvalues k})
    · intro k hk
      rfl
    · intro k hk
      have hz : hH.eigenvalues k = 0 := le_antisymm (le_of_not_gt hk) (hS.eigenvalues_nonneg k)
      simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]
end D5.S3.Quantum.FiniteCorrelationRecovery.Compression
end
end r3_faithful_frame
section r3_tensor_compression
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Compression
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
open scoped Kronecker
lemma tensorIso (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]
lemma pullTensor (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (X : Matrix a a ℂ) (Y : Matrix b b ℂ) :
    (((U ⊗ₖ V))ᴴ * ((X ⊗ₖ Y)) * ((U ⊗ₖ V))) = ((U)ᴴ * (X) * (U)) ⊗ₖ ((V)ᴴ * (Y) * (V)) := by
  simp only [ Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
lemma marginalAPush (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (hV : Vᴴ * V = 1) (ρ : Matrix (c × d) (c × d) ℂ) :
    partialTraceRight ((((U ⊗ₖ V)) * (ρ) * ((U ⊗ₖ V))ᴴ)) = ((U) * ((partialTraceRight ρ)) * (U)ᴴ) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← Matrix.trace_mul_comm X, ← D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalLeft,
    Matrix.trace_mul_comm, tracePair, pullTensor]
  simp only [ Matrix.mul_one, hV]
  rw [Matrix.trace_mul_comm, D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalLeft, Matrix.trace_mul_comm]
  exact (tracePair U (partialTraceRight ρ) X).symm
lemma marginalBPush (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (hU : Uᴴ * U = 1) (ρ : Matrix (c × d) (c × d) ℂ) :
    partialTraceLeft ((((U ⊗ₖ V)) * (ρ) * ((U ⊗ₖ V))ᴴ)) = ((V) * ((partialTraceLeft ρ)) * (V)ᴴ) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  rw [← Matrix.trace_mul_comm Y, ← D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalRight,
    Matrix.trace_mul_comm, tracePair, pullTensor]
  simp only [ Matrix.mul_one, hU]
  rw [Matrix.trace_mul_comm, D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalRight, Matrix.trace_mul_comm]
  exact (tracePair V (partialTraceLeft ρ) Y).symm
end D5.S3.Quantum.FiniteCorrelationRecovery.Compression
end
end r3_tensor_compression
section r3_projection_support
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Compression
variable {n : Type} [Fintype n] [DecidableEq n]
private lemma psdProjectionAnnihilate (R : Matrix n n ℂ) (hR : R.PosSemidef)
    (Z : Matrix n n ℂ) (hZ : Z.IsHermitian) (hZZ : Z * Z = Z)
    (ht : (R * Z).trace = 0) : R * Z = 0 := by
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  have hZpos : Z.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (show 0 ≤ Z from (show IsStarProjection Z from ⟨hZZ,hZ⟩).nonneg)
  have ht' : ((R.submatrix e e) * (Z.submatrix e e)).trace = 0 := by
    rw [Matrix.submatrix_mul_equiv]
    change (∑ i : Fin (Fintype.card n), (R * Z) (e i) (e i)) = 0
    rw [e.sum_comp (fun i : n => (R * Z) i i)]
    exact ht
  have hh := D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity.zero_trace_mul_eq_zero
    (R.submatrix e e) (Z.submatrix e e) (hR.submatrix e) (hZpos.submatrix e) ht'
  rw [Matrix.submatrix_mul_equiv] at hh
  ext i j
  have he := congrArg (fun M : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℂ =>
    M (e.symm i) (e.symm j)) hh
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.zero_apply] using he

private lemma psdProjectionSupport (R : Matrix n n ℂ) (hR : R.PosSemidef)
    (P : Matrix n n ℂ) (hP : P.IsHermitian) (hPP : P * P = P)
    (ht : (R * P).trace = R.trace) : R * P = R ∧ P * R = R := by
  have hZ : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hZZ : (1 - P) * (1 - P) = 1 - P := by
    noncomm_ring [hPP]
  have htZ : (R * (1 - P)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ht, sub_self]
  have hz := psdProjectionAnnihilate R hR (1 - P) hZ hZZ htZ
  have hr : R * P = R := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hz
    exact (sub_eq_zero.mp hz).symm
  refine ⟨hr, ?_⟩
  have hh := congrArg Matrix.conjTranspose hr
  simpa only [Matrix.conjTranspose_mul, hR.isHermitian.eq, hP.eq] using hh
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
open scoped Kronecker
lemma jointSupportFrame (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef)
    (U : Matrix a c ℂ) (V : Matrix b d ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (S : Matrix c c ℂ) (T : Matrix d d ℂ)
    (hA : partialTraceRight ρ = ((U) * (S) * (U)ᴴ))
    (hB : partialTraceLeft ρ = ((V) * (T) * (V)ᴴ)) :
    (((U ⊗ₖ V)) * (((((U ⊗ₖ V))ᴴ * (ρ) * ((U ⊗ₖ V))))) * ((U ⊗ₖ V))ᴴ) = ρ := by
  let P := ((U) * ((1 : Matrix c c ℂ)) * (U)ᴴ)
  let Q := ((V) * ((1 : Matrix d d ℂ)) * (V)ᴴ)
  have hP : P.IsHermitian := pushHermitian U 1 Matrix.isHermitian_one
  have hQ : Q.IsHermitian := pushHermitian V 1 Matrix.isHermitian_one
  have hPP : P * P = P := by rw [pushMul U hU, Matrix.one_mul]
  have hQQ : Q * Q = Q := by rw [pushMul V hV, Matrix.one_mul]
  have hAP : partialTraceRight ρ * P = partialTraceRight ρ := by
    rw [hA, pushMul U hU, Matrix.mul_one]
  have hBQ : partialTraceLeft ρ * Q = partialTraceLeft ρ := by
    rw [hB, pushMul V hV, Matrix.mul_one]
  have hAt : (partialTraceRight ρ).trace = ρ.trace := trace_partialTraceRight ρ
  have hBt : (partialTraceLeft ρ).trace = ρ.trace := trace_partialTraceLeft ρ
  have hPj : (P ⊗ₖ (1 : Matrix b b ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hP.eq, Matrix.conjTranspose_one]
  have hQj : ((1 : Matrix a a ℂ) ⊗ₖ Q).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hQ.eq, Matrix.conjTranspose_one]
  have hpj : (P ⊗ₖ (1 : Matrix b b ℂ)) * (P ⊗ₖ (1 : Matrix b b ℂ)) =
      P ⊗ₖ (1 : Matrix b b ℂ) := by rw [← Matrix.mul_kronecker_mul, hPP, Matrix.one_mul]
  have hqj : ((1 : Matrix a a ℂ) ⊗ₖ Q) * ((1 : Matrix a a ℂ) ⊗ₖ Q) =
      (1 : Matrix a a ℂ) ⊗ₖ Q := by rw [← Matrix.mul_kronecker_mul, hQQ, Matrix.one_mul]
  have hp := psdProjectionSupport ρ hρ _ hPj hpj (by
    rw [Matrix.trace_mul_comm, D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalLeft, Matrix.trace_mul_comm, hAP, hAt])
  have hq := psdProjectionSupport ρ hρ _ hQj hqj (by
    rw [Matrix.trace_mul_comm, D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalRight, Matrix.trace_mul_comm, hBQ, hBt])
  have hprod : (P ⊗ₖ Q) = (P ⊗ₖ (1 : Matrix b b ℂ)) * ((1 : Matrix a a ℂ) ⊗ₖ Q) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hleft : (P ⊗ₖ Q) * ρ = ρ := by rw [hprod, Matrix.mul_assoc, hq.2, hp.2]
  have hright : ρ * (P ⊗ₖ Q) = ρ := by rw [hprod, ← Matrix.mul_assoc, hp.1, hq.1]
  have hKK : (U ⊗ₖ V) * (U ⊗ₖ V)ᴴ = P ⊗ₖ Q := by
    simp only [P, Q, Matrix.mul_one, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
  calc
    _ = ((U ⊗ₖ V) * (U ⊗ₖ V)ᴴ) * ρ * ((U ⊗ₖ V) * (U ⊗ₖ V)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = ρ := by rw [hKK, hleft, hright]
end D5.S3.Quantum.FiniteCorrelationRecovery.Compression
end
end r3_projection_support
section r2_am_upper
open Matrix MatrixOrder ComplexOrder
noncomputable section
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
variable {n : Type*} [Fintype n] [DecidableEq n]
private lemma amTrace (σ X : Matrix n n ℂ) (hX : X.IsHermitian) :
    (Xᴴ * ((1 / 2 : ℂ) • ((σ) * (X) + (X) * (σ)))).trace = (X * σ * X).trace := by
  rw [hX.eq]
  simp only [ Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    smul_add, Matrix.trace_add]
  have hcycle : (X * (σ * X)).trace = (X * (X * σ)).trace := by
    calc
      _ = ((X * σ) * X).trace := by rw [Matrix.mul_assoc]
      _ = ((X * X) * σ).trace := by rw [Matrix.trace_mul_cycle]
      _ = _ := by rw [Matrix.mul_assoc]
  have hcomm : (X * (X * σ)).trace = (X * σ * X).trace := by
    simpa [Matrix.mul_assoc] using (Matrix.trace_mul_comm X (X * σ))
  rw [hcycle, hcomm]
  ring_nf
private lemma stateCauchyUnit (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (A B : Matrix n n ℂ) (hA : (A * ρ * Aᴴ).trace = 1)
    (hB : (B * ρ * Bᴴ).trace = 1) : ‖(B * ρ * Aᴴ).trace‖ ≤ 1 := by
  letI : SeminormedAddCommGroup (Matrix n n ℂ) := ρ.toMatrixSeminormedAddCommGroup hρ
  letI : InnerProductSpace ℂ (Matrix n n ℂ) := ρ.toMatrixInnerProductSpace hρ
  have hn (D : Matrix n n ℂ) (hD : (D * ρ * Dᴴ).trace = 1) : ‖D‖ = 1 := by
    have hs : ‖D‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      change ((D * ρ * Dᴴ).trace).re = 1
      rw [hD]
      rfl
    nlinarith [norm_nonneg D]
  have hh := norm_inner_le_norm (𝕜 := ℂ) A B
  change ‖(B * ρ * Aᴴ).trace‖ ≤ ‖A‖ * ‖B‖ at hh
  simpa only [hn A hA, hn B hB, one_mul] using hh
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
lemma amCorrelationLeOne (ρ : Matrix (a × b) (a × b) ℂ) (hρ : ρ.PosSemidef)
    (X : Matrix a a ℂ) (Y : Matrix b b ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hx : (Xᴴ * ((1 / 2 : ℂ) • (((partialTraceRight ρ)) * (X) + (X) * ((partialTraceRight ρ))))).trace = 1)
    (hy : (Yᴴ * ((1 / 2 : ℂ) • (((partialTraceLeft ρ)) * (Y) + (Y) * ((partialTraceLeft ρ))))).trace = 1) :
    ‖(kroneckerMap (· * ·) X Yᴴ * ρ).trace‖ ≤ 1 := by
  let A := kroneckerMap (· * ·) X (1 : Matrix b b ℂ)
  let B := kroneckerMap (· * ·) (1 : Matrix a a ℂ) Y
  have hA : Aᴴ = A := by
    dsimp only [A]
    simpa only [hX.eq, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker X (1 : Matrix b b ℂ)
  have hB : Bᴴ = B := by
    dsimp only [B]
    simpa only [hY.eq, Matrix.conjTranspose_one] using
      Matrix.conjTranspose_kronecker (1 : Matrix a a ℂ) Y
  have hx' : (A * ρ * Aᴴ).trace = 1 := by
    rw [amTrace _ _ hX] at hx
    calc
      _ = (Aᴴ * ρ * A).trace := by rw [hA]
      _ = (Xᴴ * partialTraceRight ρ * X).trace := D5.S3.Quantum.FixedPointProjection.Marginal.localTrace ρ X
      _ = 1 := by simpa only [hX.eq] using hx
  have hy' : (B * ρ * Bᴴ).trace = 1 := by
    rw [hB, Matrix.trace_mul_cycle]
    change (kroneckerMap (· * ·) (1 : Matrix a a ℂ) Y *
      kroneckerMap (· * ·) (1 : Matrix a a ℂ) Y * ρ).trace = 1
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, D5.S3.Quantum.FixedPointProjection.Marginal.traceLocalRight]
    rw [← Matrix.trace_mul_cycle Y (partialTraceLeft ρ) Y]
    rwa [amTrace _ _ hY] at hy
  have hh := stateCauchyUnit ρ hρ A B hx' hy'
  rw [hA, Matrix.trace_mul_cycle] at hh
  change ‖(A * B * ρ).trace‖ ≤ 1 at hh
  have hab : A * B = kroneckerMap (· * ·) X Y := by
    dsimp only [A,B]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  simpa only [hab, hY.eq] using hh
end D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
end
end r2_am_upper
section generic_am
noncomputable section
section r3_am_witness
open Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma projectionProbability (σ P : Matrix n n ℂ) (hσ : σ.PosDef) (hσ1 : σ.trace = 1)
    (hP : P.IsHermitian) (hPP : P * P = P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ (σ * P).trace = (p : ℂ) := by
  have hproj : IsStarProjection P := ⟨hPP, hP⟩
  have htr := RHLinalg.trace_mul_nonneg_of_posSemidef hσ.posSemidef
    (Matrix.nonneg_iff_posSemidef.mp hproj.nonneg)
  have hc := RHLinalg.trace_mul_nonneg_of_posSemidef hσ.posSemidef
    (Matrix.nonneg_iff_posSemidef.mp hproj.one_sub.nonneg)
  have hn : (σ * P).trace ≠ 0 := by
    intro hz
    exact hP0 (D5.S3.Quantum.FixedPointProjection.Faithful.faithfulTraceZero σ P hσ
      (Matrix.nonneg_iff_posSemidef.mp hproj.nonneg) hz)
  have hcn : (σ * (1 - P)).trace ≠ 0 := by
    intro hz
    have hz' := D5.S3.Quantum.FixedPointProjection.Faithful.faithfulTraceZero σ (1 - P) hσ
      (Matrix.nonneg_iff_posSemidef.mp hproj.one_sub.nonneg) hz
    exact hP1 (sub_eq_zero.mp hz').symm
  have hs : (σ * (1 - P)).trace = 1 - (σ * P).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hσ1]
  have hpr : 0 ≤ (σ * P).trace.re := htr
  have hcr : 0 ≤ (σ * (1 - P)).trace.re := hc
  have hpi : (σ * P).trace.im = 0 := by
    have hh : star (σ * P).trace = (σ * P).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hσ.isHermitian.eq, hP.eq, Matrix.trace_mul_comm]
    have hi := congrArg Complex.im hh
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  refine ⟨(σ * P).trace.re, ?_, ?_, ?_⟩
  · apply lt_of_le_of_ne hpr
    intro hz
    apply hn
    apply Complex.ext <;> simp_all
  · rw [hs] at hcr hcn
    change 0 ≤ 1 - (σ * P).trace.re at hcr
    apply lt_of_le_of_ne (sub_nonneg.mp hcr)
    intro hz
    apply hcn
    apply Complex.ext <;> simp_all
  · apply Complex.ext <;> simp_all
end D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
open Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
variable {n : Type*} [Fintype n] [DecidableEq n]
def binaryObservable (P : Matrix n n ℂ) (p : ℝ) : Matrix n n ℂ :=
  ((Real.sqrt (p * (1 - p)) : ℂ)⁻¹) • (P - (p : ℂ) • 1)
lemma binaryObservableHermitian (P : Matrix n n ℂ) (hP : P.IsHermitian) (p : ℝ) :
    (binaryObservable P p).IsHermitian := by
  apply (hP.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))).smul
  simp [IsSelfAdjoint]
lemma binaryObservableCentered (σ P : Matrix n n ℂ) (p : ℝ)
    (hσ : σ.trace = 1) (hp : (σ * P).trace = (p : ℂ)) :
    (σ * binaryObservable P p).trace = 0 := by
  simp [binaryObservable, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul,
    Matrix.trace_sub, hσ, hp]
private lemma centeredProjectionVariance (σ P : Matrix n n ℂ) (p : ℝ)
    (hσ : σ.trace = 1) (hp : (σ * P).trace = (p : ℂ)) (hPP : P * P = P) :
    ((P - (p : ℂ) • 1) * σ * (P - (p : ℂ) • 1)).trace = ((p * (1-p) : ℝ) : ℂ) := by
  have hcycle : (P * σ * P).trace = (p : ℂ) := by
    rw [Matrix.trace_mul_cycle, hPP, Matrix.trace_mul_comm, hp]
  have hcomm : (P * σ).trace = (p : ℂ) := by rw [Matrix.trace_mul_comm, hp]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    hcycle, hcomm, hp, hσ, smul_eq_mul]
  push_cast
  ring
lemma binaryObservableAmUnit (σ P : Matrix n n ℂ) (hP : P.IsHermitian)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hσ : σ.trace = 1)
    (hp : (σ * P).trace = (p : ℂ)) (hPP : P * P = P) :
    ((binaryObservable P p)ᴴ * ((1 / 2 : ℂ) • ((σ) * ((binaryObservable P p)) + ((binaryObservable P p)) * (σ)))).trace = 1 := by
  rw [amTrace _ _ (binaryObservableHermitian P hP p)]
  have hv := centeredProjectionVariance σ P p hσ hp hPP
  have hd : 0 < p * (1-p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hs : (Real.sqrt (p * (1-p)) : ℂ) ^ 2 = ((p * (1-p) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hd)]
  have hs0 : (Real.sqrt (p * (1-p)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hd)
  simp only [binaryObservable, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_smul, smul_eq_mul, hv]
  rw [← hs]
  field_simp
end D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
open Matrix MatrixOrder ComplexOrder
namespace D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
def traceCorrelation (ρ : Matrix (a × b) (a × b) ℂ) :
    Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ →ₗ[ℂ] ℂ :=
  (Matrix.kroneckerBilinear (R := ℂ)).compr₂
    ((Matrix.traceLinearMap (a × b) ℂ ℂ).comp (LinearMap.mulRight ℂ ρ))
lemma sharedBinaryCorrelation (ρ : Matrix (a × b) (a × b) ℂ)
    (P : Matrix a a ℂ) (Q : Matrix b b ℂ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hPP : traceCorrelation ρ P Q = (p : ℂ))
    (hP : traceCorrelation ρ P 1 = (p : ℂ))
    (hQ : traceCorrelation ρ 1 Q = (p : ℂ))
    (h1 : traceCorrelation ρ 1 1 = 1) :
    traceCorrelation ρ (binaryObservable P p) (binaryObservable Q p) = 1 := by
  have hd : 0 < p * (1-p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hs : (Real.sqrt (p * (1-p)) : ℂ) ^ 2 = ((p * (1-p) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hd)]
  have hs0 : (Real.sqrt (p * (1-p)) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hd)
  simp only [binaryObservable, map_smul, map_sub, LinearMap.smul_apply,
    LinearMap.sub_apply, hPP, hP, hQ, h1, smul_eq_mul]
  field_simp
  push_cast at hs
  linear_combination -hs
end D5.S3.Quantum.FiniteCorrelationRecovery.Arithmetic
end r3_am_witness
end
end generic_am
