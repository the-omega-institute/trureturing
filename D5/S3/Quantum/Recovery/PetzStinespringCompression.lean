import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Divergence.UmegakiKernelContraction
import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import Mathlib.Tactic.Abel

/-!
# Stinespring compression for ordinary Petz recovery

This is the finite algebraic step in the CPTP argument of
`ordinary-petz-local-uniform-audit.txt`. The spectral formulas include the
zero block of a rectangular dilation and use the pseudoinverse on the
retained marginal. The ordinary partial-trace formula is spelled out in
`ordinaryPetz_embed` using the same operators as the private
`PetzPhysicalAmplitude.ordinaryPetz` draft.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

namespace PetzStinespringCompression

open Matrix
open scoped BigOperators ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality (channel_kraus_stinespring)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (partialTraceRight_embed_mul partialTraceRight_mul_embed)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
  (actual_kraus_representation actual_kraus_trace_pair krausAdjoint)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
  (spectralSupport spectralInverseSqrt)
open D5.S3.Quantum.Lieb.PositiveMapJensen (cfc_intertwining)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport (spectral_sqrt_normalization)

section Rectangular

variable {a : Type u} {m : Type v}
  [Fintype a] [DecidableEq a] [Fintype m] [DecidableEq m]

/-- The embedded operator agrees with the input on the isometric image.
The scalar at zero accounts for the entire orthogonal complement. -/
theorem cfc_isometric_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f (V * X * Vᴴ) =
      V * cfc f X * Vᴴ + f 0 • (1 - V * Vᴴ) := by
  let Y := V * X * Vᴴ
  let D : Matrix m m ℂ := 1 - V * Vᴴ
  have hY : Y.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose V hX
  have hYV : Y * V = V * X := by
    change (V * X * Vᴴ) * V = V * X
    rw [Matrix.mul_assoc (V * X) Vᴴ V, hV, Matrix.mul_one]
  have hYD : Y * D = D * (0 : Matrix m m ℂ) := by
    change Y * (1 - V * Vᴴ) = D * 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc Y V Vᴴ,
      hYV, Matrix.mul_zero, sub_self]
  have hFV : cfc f Y * V = V * cfc f X :=
    cfc_intertwining Y X hY hX V hYV f
  have hFD : cfc f Y * D = f 0 • D := by
    simpa only [cfc_apply_zero, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.mul_one] using
      (cfc_intertwining Y (0 : Matrix m m ℂ) hY Matrix.isHermitian_zero D hYD f)
  have hsplit : V * Vᴴ + D = 1 := by
    dsimp [D]
    abel
  change cfc f Y = V * cfc f X * Vᴴ + f 0 • D
  calc
    cfc f Y = cfc f Y * (V * Vᴴ + D) := by rw [hsplit, Matrix.mul_one]
    _ = (cfc f Y * V) * Vᴴ + cfc f Y * D := by
      rw [Matrix.mul_add, Matrix.mul_assoc (cfc f Y) V Vᴴ]
    _ = _ := by rw [hFV, hFD]

/-- Every nonzero spectral projection is transported by the rectangular isometry. -/
theorem nonzero_spectralProjection_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.IsHermitian) {t : ℝ} (ht : t ≠ 0) :
    cfc (fun x : ℝ => if x = t then 1 else 0) (V * X * Vᴴ) =
      V * cfc (fun x : ℝ => if x = t then 1 else 0) X * Vᴴ := by
  simpa only [if_neg (Ne.symm ht), zero_smul, add_zero] using
    (cfc_isometric_embed V hV hX (fun x : ℝ => if x = t then 1 else 0))

/-- The support of each embedded state is the input support transported by `V`.
This applies to both states even when the input supports differ. -/
theorem spectralSupport_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.IsHermitian) :
    spectralSupport (V * X * Vᴴ) = V * spectralSupport X * Vᴴ := by
  simpa only [spectralSupport, eq_self_iff_true, ite_true, zero_smul, add_zero] using
    (cfc_isometric_embed V hV hX (fun x : ℝ => if x = 0 then 0 else 1))

/-- The zero spectral projection consists of the transported input kernel and
the complement of the isometry's range. -/
theorem kernelProjection_embed (V : Matrix m a ℂ) (hV : Vᴴ * V = 1)
    {X : Matrix a a ℂ} (hX : X.IsHermitian) :
    1 - spectralSupport (V * X * Vᴴ) =
      V * (1 - spectralSupport X) * Vᴴ + (1 - V * Vᴴ) := by
  rw [spectralSupport_embed V hV hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  abel

private theorem spectralSupport_of_posDef {X : Matrix a a ℂ} (hX : X.PosDef) :
    spectralSupport X = 1 := by
  unfold spectralSupport
  calc
    _ = cfc (fun _ : ℝ => 1) X := by
      apply cfc_congr
      intro x hx
      rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact if_neg (ne_of_gt (hX.eigenvalues_pos i))
    _ = 1 := cfc_const_one ℝ X hX.isHermitian.isSelfAdjoint

end Rectangular

section PartialTrace

variable {a b e : Type u}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype e] [DecidableEq e]

/-- The compression of the dilated reference by the tensor lift of the
retained kernel projection is PSD and has trace zero. This forces the
image of the input support into the tensor lift of the marginal support. -/
theorem range_support_le_marginal_support
    (V : Matrix (b × e) a ℂ) {σ : Matrix a a ℂ} (hσ : σ.PosSemidef) :
    (spectralSupport (partialTraceRight (V * σ * Vᴴ)) ⊗ₖ (1 : Matrix e e ℂ)) *
        (V * spectralSupport σ) = V * spectralSupport σ := by
  let Y := V * σ * Vᴴ
  let q := partialTraceRight Y
  let K := 1 - spectralSupport q
  let L := K ⊗ₖ (1 : Matrix e e ℂ)
  let T := L * V
  have hq : q.PosSemidef := partialTraceRight_posSemidef (hσ.mul_mul_conjTranspose_same V)
  have hNorm := spectral_sqrt_normalization q hq
  dsimp only at hNorm
  obtain ⟨_, _, hP, _, _, _, hPq, _⟩ := hNorm
  have hKq : K * q = 0 := by
    change (1 - spectralSupport q) * q = 0
    rw [Matrix.sub_mul, Matrix.one_mul, hPq, sub_self]
  have hK : Kᴴ = K := by
    simp only [K, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP]
  have hL : Lᴴ = L := by
    simp only [L, Matrix.conjTranspose_kronecker, hK, Matrix.conjTranspose_one]
  have hBlock : T * σ * Tᴴ = L * Y * L := by
    simp only [T, Y, Matrix.conjTranspose_mul, hL, Matrix.mul_assoc]
  have hTrace : (T * σ * Tᴴ).trace = 0 := by
    rw [hBlock, ← trace_partialTraceRight (L * Y * L)]
    change (partialTraceRight
      ((K ⊗ₖ (1 : Matrix e e ℂ)) * Y * (K ⊗ₖ (1 : Matrix e e ℂ)))).trace = 0
    rw [partialTraceRight_mul_embed, partialTraceRight_embed_mul]
    change (K * q * K).trace = 0
    rw [hKq, Matrix.zero_mul, Matrix.trace_zero]
  have hZero : T * σ * Tᴴ = 0 :=
    (hσ.mul_mul_conjTranspose_same T).trace_eq_zero_iff.mp hTrace
  let R := CFC.sqrt σ
  have hR : Rᴴ = R := (CFC.sqrt_nonneg σ).posSemidef.isHermitian.eq
  have hRR : R * R = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hGram : (T * R) * (T * R)ᴴ = T * σ * Tᴴ := by
    rw [Matrix.conjTranspose_mul, hR, ← hRR]
    simp only [Matrix.mul_assoc]
  have hTR : T * R = 0 := Matrix.self_mul_conjTranspose_eq_zero.mp (hGram.trans hZero)
  have hTσ : T * σ = 0 := by rw [← hRR, ← Matrix.mul_assoc, hTR, Matrix.zero_mul]
  have hTP : T * spectralSupport σ = 0 := by
    have h := cfc_intertwining (0 : Matrix (b × e) (b × e) ℂ) σ
      Matrix.isHermitian_zero hσ.isHermitian T (by rw [Matrix.zero_mul, hTσ])
      (fun x : ℝ => if x = 0 then 0 else 1)
    simpa only [spectralSupport, cfc_apply_zero, eq_self_iff_true, ite_true, map_zero,
      Matrix.zero_mul] using h.symm
  have hL' : L = 1 - (spectralSupport q ⊗ₖ (1 : Matrix e e ℂ)) := by
    dsimp [L, K]
    rw [← Matrix.one_kronecker_one (m := b) (n := e) (α := ℂ)]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ : 1
    simp only [Matrix.sub_apply, Matrix.kronecker_apply, _root_.sub_mul]
  change (spectralSupport q ⊗ₖ (1 : Matrix e e ℂ)) * (V * spectralSupport σ) =
    V * spectralSupport σ
  have h := hTP
  change (L * V) * spectralSupport σ = 0 at h
  rw [Matrix.mul_assoc, hL', Matrix.sub_mul, Matrix.one_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- On the restricted input carrier, positive definiteness makes the
whole isometric range lie in the retained support tensored with the environment. -/
theorem faithful_range_le_marginal_support
    (V : Matrix (b × e) a ℂ) {σ : Matrix a a ℂ} (hσ : σ.PosDef) :
    (spectralSupport (partialTraceRight (V * σ * Vᴴ)) ⊗ₖ (1 : Matrix e e ℂ)) * V = V := by
  simpa only [spectralSupport_of_posDef hσ, Matrix.mul_one] using
    (range_support_le_marginal_support V hσ.posSemidef)

end PartialTrace

section Channel

variable {a b e : Type u}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype e] [DecidableEq e]

/-- Reindex the existing environment-first Stinespring matrix by swapping
its product row coordinates. The right partial trace is the actual channel. -/
theorem exists_retainedFirst_stinespring (Φ : QuantumChannel a b) :
    ∃ V : Matrix (b × (b × a)) a ℂ, Vᴴ * V = 1 ∧
      ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X := by
  obtain ⟨W, hW, hAction⟩ := channel_kraus_stinespring.2 Φ
  let swap : b × (b × a) ≃ (b × a) × b := Equiv.prodComm b (b × a)
  let V := W.submatrix swap id
  refine ⟨V, ?_, ?_⟩
  · change (W.submatrix swap id)ᴴ * W.submatrix swap id = _
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv Wᴴ W id swap id,
      Matrix.submatrix_id_id, hW]
  · intro X
    change partialTraceLeft (W * X * Wᴴ) = act Φ X
    exact hAction X

/-- A dilation of the actual channel sends the support of the reference
into the output support tensored with the environment. On a faithful input
carrier the input support factor is the identity. -/
theorem exists_supported_stinespring (Φ : QuantumChannel a b)
    {σ : Matrix a a ℂ} (hσ : σ.PosSemidef) :
    ∃ V : Matrix (b × (b × a)) a ℂ, Vᴴ * V = 1 ∧
      (∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X) ∧
      (spectralSupport (act Φ σ) ⊗ₖ (1 : Matrix (b × a) (b × a) ℂ)) *
        (V * spectralSupport σ) = V * spectralSupport σ := by
  obtain ⟨V, hV, hAction⟩ := exists_retainedFirst_stinespring Φ
  refine ⟨V, hV, hAction, ?_⟩
  rw [← hAction σ]
  exact range_support_le_marginal_support V hσ

/-- The adjoint of the actual channel is the diagonal tensor lift compressed
by any dilation realizing that channel. Matrix units separate the trace pairing. -/
theorem compress_lift_eq_krausAdjoint (Φ : QuantumChannel a b)
    (V : Matrix (b × e) a ℂ)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X)
    (Y : Matrix b b ℂ) :
    Vᴴ * (Y ⊗ₖ (1 : Matrix e e ℂ)) * V =
      krausAdjoint (actual_kraus_representation Φ).kraus Y := by
  let L := Y ⊗ₖ (1 : Matrix e e ℂ)
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  change (X * (Vᴴ * L * V)).trace =
    (X * krausAdjoint (actual_kraus_representation Φ).kraus Y).trace
  calc
    _ = ((V * X * Vᴴ) * L).trace := by
      rw [← Matrix.mul_assoc X (Vᴴ * L) V, Matrix.trace_mul_comm (X * (Vᴴ * L)) V]
      simp only [Matrix.mul_assoc]
    _ = (partialTraceRight (V * X * Vᴴ) * Y).trace := by
      rw [← trace_partialTraceRight ((V * X * Vᴴ) * L)]
      simp only [L, partialTraceRight_mul_embed]
    _ = _ := by
      rw [hAction X]
      simpa only [act] using (actual_kraus_trace_pair Φ X Y).symm

/-- The ordinary partial-trace Petz output is exactly the isometric image of
the ordinary Petz output using the channel's actual Kraus adjoint. The
retained inverse square root is spectral and vanishes on the kernel. -/
theorem ordinaryPetz_embed (Φ : QuantumChannel a b)
    (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X)
    {σ : Matrix a a ℂ} (hσ : σ.IsHermitian) (p : Matrix b b ℂ) :
    let σV := V * σ * Vᴴ
    let W := spectralInverseSqrt (partialTraceRight σV)
    let Q := spectralInverseSqrt (act Φ σ)
    cfc Real.sqrt σV * ((W * p * W) ⊗ₖ (1 : Matrix e e ℂ)) * cfc Real.sqrt σV =
      V * (cfc Real.sqrt σ *
        krausAdjoint (actual_kraus_representation Φ).kraus (Q * p * Q) *
        cfc Real.sqrt σ) * Vᴴ := by
  dsimp only
  have hS : cfc Real.sqrt (V * σ * Vᴴ) = V * cfc Real.sqrt σ * Vᴴ := by
    simpa only [Real.sqrt_zero, zero_smul, add_zero] using
      (cfc_isometric_embed V hV hσ Real.sqrt)
  simp only [hAction σ, hS]
  let Q := spectralInverseSqrt (act Φ σ)
  let B := Q * p * Q
  let L := B ⊗ₖ (1 : Matrix e e ℂ)
  let S := cfc Real.sqrt σ
  change (V * S * Vᴴ) * L * (V * S * Vᴴ) =
    V * (S * krausAdjoint (actual_kraus_representation Φ).kraus B * S) * Vᴴ
  calc
    _ = V * (S * (Vᴴ * L * V) * S) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by
      change V * (S * (Vᴴ * (B ⊗ₖ (1 : Matrix e e ℂ)) * V) * S) * Vᴴ = _
      rw [compress_lift_eq_krausAdjoint Φ V hAction B]

/-- Compressing the physical partial-trace Petz output recovers the actual
channel formula, including when the output marginal is singular. -/
theorem ordinaryPetz_compress (Φ : QuantumChannel a b)
    (V : Matrix (b × e) a ℂ) (hV : Vᴴ * V = 1)
    (hAction : ∀ X : Matrix a a ℂ, partialTraceRight (V * X * Vᴴ) = act Φ X)
    {σ : Matrix a a ℂ} (hσ : σ.IsHermitian) (p : Matrix b b ℂ) :
    let σV := V * σ * Vᴴ
    let W := spectralInverseSqrt (partialTraceRight σV)
    let Q := spectralInverseSqrt (act Φ σ)
    Vᴴ * (cfc Real.sqrt σV * ((W * p * W) ⊗ₖ (1 : Matrix e e ℂ)) *
      cfc Real.sqrt σV) * V =
      cfc Real.sqrt σ *
        krausAdjoint (actual_kraus_representation Φ).kraus (Q * p * Q) *
        cfc Real.sqrt σ := by
  dsimp only
  rw [ordinaryPetz_embed Φ V hV hAction hσ p]
  let Q := spectralInverseSqrt (act Φ σ)
  let P := cfc Real.sqrt σ *
    krausAdjoint (actual_kraus_representation Φ).kraus (Q * p * Q) *
    cfc Real.sqrt σ
  change Vᴴ * (V * P * Vᴴ) * V = P
  calc
    _ = (Vᴴ * V) * P * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = P := by rw [hV, Matrix.one_mul, Matrix.mul_one]

end Channel

end PetzStinespringCompression
