/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStickRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStickRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A binary channel refutes complete hockey-stick monotonicity and orthogonal reduction. -/

import D5.S3.Quantum.Divergence.FaithfulConditionalGap
import D5.S3.Quantum.Foundation.TraceNormTensorProduct
import D5.S3.Weil.ZetaLinear.RankTrace

/-! The complete contraction coefficient in Hirche–George–Nuradha–Wilde,
arXiv:2608.27171v1, Definition 2, Remark 6 and §9. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
namespace D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_add_le
  traceNorm_neg traceNorm_of_posSemidef trace_norm_jordan_mass)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (amp_mono)
open D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit
  (traceNorm_kronecker)
open D5.S3.Quantum.Divergence.FaithfulConditionalGap (positive_trace_contraction)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (trace_partialTraceRight)
open RHLinalg (rtrace rtrace_add rtrace_sub trace_mul_nonneg_of_posSemidef)

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem twice_posTrace (X : Matrix n n ℂ) (hX : X.IsHermitian) :
    2 * posTrace X = traceNorm X + rtrace X := by
  have h := congrArg rtrace (CFC.posPart_sub_negPart X hX)
  rw [rtrace_sub] at h
  have ht := trace_norm_jordan_mass X hX
  change traceNorm X = rtrace X⁺ + rtrace X⁻ at ht
  change 2 * rtrace X⁺ = traceNorm X + rtrace X
  linarith

private theorem posTrace_mono {X Y : Matrix n n ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (hXY : X ≤ Y) : posTrace X ≤ posTrace Y := by
  have ht := traceNorm_add_le Y (X - Y)
  rw [add_comm Y, sub_add_cancel, ← neg_sub Y, traceNorm_neg] at ht
  have hmass := congrArg Complex.re
    (traceNorm_of_posSemidef (sub_nonneg.mpr hXY).posSemidef)
  change traceNorm (Y - X) = rtrace (Y - X) at hmass
  rw [hmass, rtrace_sub] at ht
  linarith [twice_posTrace X hX, twice_posTrace Y hY]

theorem effect_le_posTrace {X M : Matrix n n ℂ} (hX : X.IsHermitian)
    (hM : 0 ≤ M) (hI : M ≤ 1) : rtrace (M * X) ≤ posTrace X := by
  have h₁ := trace_mul_nonneg_of_posSemidef
    (sub_nonneg.mpr hI).posSemidef (CFC.posPart_nonneg X).posSemidef
  have h₂ := trace_mul_nonneg_of_posSemidef
    hM.posSemidef (CFC.negPart_nonneg X).posSemidef
  change 0 ≤ rtrace ((1 - M) * X⁺) at h₁
  change 0 ≤ rtrace (M * X⁻) at h₂
  rw [sub_mul, one_mul, rtrace_sub] at h₁
  have he := congrArg (fun Z => rtrace (M * Z)) (CFC.posPart_sub_negPart X hX)
  change rtrace (M * (X⁺ - X⁻)) = rtrace (M * X) at he
  rw [mul_sub, rtrace_sub] at he
  change rtrace (M * X) ≤ rtrace X⁺
  linarith

/-- Ratios from equal-reference-marginal state pairs, with optional orthogonality. -/
def completeRatios {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : Set ℝ :=
  {x | ∃ (R : Type) (fR : Fintype R) (dR : DecidableEq R),
    letI := fR
    letI := dR
    ∃ ρ σ : Matrix (R × A) (R × A) ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧
      ptr ρ = ptr σ ∧ (orth = true → ρ * σ = 0) ∧ 0 < E γ ρ σ ∧
      x = E γ (amp N ρ) (amp N σ) / E γ ρ σ}

/-- The complete coefficient, with zero included to cover an empty ratio set. -/
def completeCoefficient {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) : ℝ :=
  sSup (insert 0 (completeRatios N γ orth))

theorem amp_psd {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) {X : Matrix (R × A) (R × A) ℂ}
    (hX : X.PosSemidef) : (amp N X).PosSemidef := by
  have hm := amp_mono N hX.nonneg
  have hzero : amp N (0 : Matrix (R × A) (R × A) ℂ) = 0 := by
    simpa only [zero_smul] using amp_smul N 0 X
  rw [hzero] at hm
  exact hm.posSemidef

theorem E_contract {A B R : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]
    (N : QuantumChannel A B) (γ : ℝ) {ρ σ : Matrix (R × A) (R × A) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) : E γ (amp N ρ) (amp N σ) ≤ E γ ρ σ := by
  let f : Matrix (R × A) (R × A) ℂ →ₗ[ℂ] Matrix (R × B) (R × B) ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((D5.S3.Quantum.Foundation.FiniteDiamondDistance.referenceLinear N).comp
        CStarMatrix.ofMatrixₗ.toLinearMap)
  have ht (X : Matrix (R × A) (R × A) ℂ) : (amp N X).trace = X.trace := by
    rw [← trace_partialTraceRight (amp N X)]
    change (ptr (amp N X)).trace = X.trace
    rw [ptr_amp]
    exact trace_partialTraceRight X
  have hn := positive_trace_contraction f
    (fun X hX => (amp_psd N (X := X) hX.posSemidef).nonneg) ht
    (ρ - γ • σ) (hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ)))
  change traceNorm (amp N (ρ - γ • σ)) ≤ traceNorm (ρ - γ • σ) at hn
  have htr := congrArg Complex.re (ht (ρ - γ • σ))
  have hu := twice_posTrace (amp N ρ - γ • amp N σ)
    ((amp_psd N hρ).isHermitian.sub ((amp_psd N hσ).isHermitian.smul
      (IsSelfAdjoint.all γ)))
  have hv := twice_posTrace (ρ - γ • σ)
    (hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ)))
  rw [amp_sub_smul] at hn htr
  change rtrace (amp N ρ - γ • amp N σ) = rtrace (ρ - γ • σ) at htr
  unfold E
  linarith

theorem ratios_bounded {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B) (γ : ℝ) (orth : Bool) :
    BddAbove (insert 0 (completeRatios N γ orth)) := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · rcases hx with ⟨R, fR, dR, ρ, σ, hρ, _, hσ, _, _, _, hd, rfl⟩
    letI := fR
    letI := dR
    exact (div_le_one hd).mpr (E_contract N γ hρ hσ)

private def ray {n : Type*} (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

private theorem ray_psd {n : Type*} [Finite n] (v : n → ℂ) : (ray v).PosSemidef :=
  posSemidef_vecMulVec_self_star v

private def e₀ : Fin 2 → ℂ := ![1, 0]
private def e₁ : Fin 2 → ℂ := ![0, 1]
private def b : Fin 2 → ℂ := ![4 / 5, 3 / 5]

private def kraus (a : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then vecMulVec e₀ e₀ else vecMulVec b e₁

private theorem kraus_complete : (∑ a, (kraus a)ᴴ * kraus a) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [kraus, e₀, e₁, b, Matrix.one_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, map_ofNat, map_div₀]

/-- Measures in the computational basis and prepares the rays of (1,0) and (4/5,3/5). -/
def channel : QuantumChannel (Fin 2) (Fin 2) :=
  Classical.choose (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    kraus kraus_complete)

private theorem channel_action (X : Matrix (Fin 2) (Fin 2) ℂ) :
    act channel X = X 0 0 • ray e₀ + X 1 1 • ray b := by
  have h := Classical.choose_spec
    (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
      kraus kraus_complete) X
  change act channel X = _ at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ray, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, kraus] <;>
    norm_num [e₀, e₁, b, Matrix.vecMulVec_apply, Pi.star_apply, map_ofNat, map_div₀] <;> ring

private def diagonalBlock {R : Type*} (a : Fin 2) (X : Matrix (R × Fin 2) (R × Fin 2) ℂ) :
    Matrix R R ℂ := X.submatrix (fun r => (r, a)) (fun r => (r, a))

private theorem amplify {R : Type*} [Fintype R] [DecidableEq R]
    (X : Matrix (R × Fin 2) (R × Fin 2) ℂ) :
    amp channel X = (diagonalBlock 0 X ⊗ₖ ray e₀) + (diagonalBlock 1 X ⊗ₖ ray b) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [amp_entry]
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M a c)
    (channel_action (fun x y => X (i,x) (j,y)))

private def cq {R : Type*} (X Y : Matrix R R ℂ) : Matrix (R × Fin 2) (R × Fin 2) ℂ :=
  (X ⊗ₖ ray e₀) + (Y ⊗ₖ ray e₁)

private theorem cq_psd {R : Type*} [Finite R]
    {X Y : Matrix R R ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (cq X Y).PosSemidef :=
  (hX.kronecker (ray_psd e₀)).add (hY.kronecker (ray_psd e₁))

private theorem cq_entry {R : Type*} (X Y : Matrix R R ℂ) (i j : R) (a c : Fin 2) :
    cq X Y (i, a) (j, c) = if a = 0 ∧ c = 0 then X i j
      else if a = 1 ∧ c = 1 then Y i j else 0 := by
  fin_cases a <;> fin_cases c <;>
    simp only [cq, Matrix.add_apply, Matrix.kroneckerMap_apply, ray, Matrix.vecMulVec_apply] <;>
    norm_num [e₀, e₁, Pi.star_apply]

private theorem cq_trace {R : Type*} [Fintype R] (X Y : Matrix R R ℂ) :
    (cq X Y).trace = X.trace + Y.trace := by
  unfold cq
  rw [Matrix.trace_add, Matrix.trace_kronecker, Matrix.trace_kronecker]
  simp only [ray, trace_vecMulVec]
  norm_num [e₀, e₁, dotProduct, Fin.sum_univ_two, Pi.star_apply]

private theorem cq_posTrace {R : Type*} [Fintype R] [DecidableEq R]
    {X Y : Matrix R R ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    posTrace (cq X Y) = posTrace X + posTrace Y := by
  have hP := cq_psd (CFC.posPart_nonneg X).posSemidef (CFC.posPart_nonneg Y).posSemidef
  have hQ := cq_psd (CFC.negPart_nonneg X).posSemidef (CFC.negPart_nonneg Y).posSemidef
  have hpq : cq X⁺ Y⁺ * cq X⁻ Y⁻ = 0 := by
    unfold cq
    simp only [Matrix.add_mul, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul]
    have h01 : ray e₀ * ray e₁ = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [ray, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply] <;>
        norm_num [e₀, e₁, Pi.star_apply]
    have h10 : ray e₁ * ray e₀ = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp only [ray, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply] <;>
        norm_num [e₀, e₁, Pi.star_apply]
    simp [h01, h10, CFC.posPart_mul_negPart]
  have hdecomp : cq X Y = cq X⁺ Y⁺ - cq X⁻ Y⁻ := by
    ext ⟨i,a⟩ ⟨j,c⟩
    simp only [Matrix.sub_apply, cq_entry]
    split_ifs
    · exact congrFun (congrFun (CFC.posPart_sub_negPart X hX).symm i) j
    · exact congrFun (congrFun (CFC.posPart_sub_negPart Y hY).symm i) j
    · simp
  unfold posTrace
  rw [(CFC.posPart_negPart_unique hdecomp hpq hP.nonneg hQ.nonneg).1]
  change rtrace (cq X⁺ Y⁺) = rtrace X⁺ + rtrace Y⁺
  unfold rtrace
  rw [cq_trace, map_add]

private theorem cq_ptr {R : Type*} [Fintype R] [DecidableEq R] (X Y : Matrix R R ℂ) :
    ptr (cq X Y) = X + Y := by
  ext i j
  change (∑ a : Fin 2, cq X Y (i,a) (j,a)) = X i j + Y i j
  norm_num [Fin.sum_univ_two, cq_entry]

private theorem output_contrast_norm : traceNorm (ray e₀ - ray b) = (6 / 5 : ℝ) := by
  let K := ray e₀ - ray b
  have hsq : Kᴴ * K = (9 / 25 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.sub_apply, ray, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.smul_apply] <;>
      norm_num [e₀, b, Matrix.one_apply, Complex.real_smul, map_sub, map_mul, map_div₀,
        map_ofNat]
  let S : Matrix (Fin 2) (Fin 2) ℂ := (3 / 5 : ℝ) • 1
  have hs : S * S = Kᴴ * K := by
    rw [hsq]
    simp only [S, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    norm_num
  have hp : 0 ≤ S := Matrix.PosSemidef.nonneg
    (Matrix.PosSemidef.one.smul (show (0 : ℝ) ≤ 3 / 5 by norm_num))
  change (Matrix.trace (CFC.sqrt (Kᴴ * K))).re = _
  rw [CFC.sqrt_unique hs hp]
  norm_num [S, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul]

private theorem posTrace_contrast {R : Type} [Fintype R] [DecidableEq R]
    (X : Matrix (R × Fin 2) (R × Fin 2) ℂ) (hX : X.IsHermitian) (ht : X.trace = 0)
    (hptr : ptr X = 0) :
    posTrace (amp channel X) ≤ (3 / 5 : ℝ) * posTrace X := by
  let D := diagonalBlock 0 X
  have hD : D.IsHermitian := hX.submatrix _
  have hblocks : diagonalBlock 1 X = -D := by
    ext i j
    have h := congrFun (congrFun hptr i) j
    change (∑ a : Fin 2, X (i,a) (j,a)) = 0 at h
    rw [Fin.sum_univ_two] at h
    exact eq_neg_of_add_eq_zero_right h
  have ho : amp channel X = D ⊗ₖ (ray e₀ - ray b) := by
    rw [amplify, hblocks]
    ext ⟨i,a⟩ ⟨j,c⟩
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.kronecker_apply, Matrix.sub_apply]
    ring
  have hneg : posTrace (-D) = rtrace D⁻ := by
    change rtrace ((-D)⁺) = _
    rw [CFC.posPart_neg]
  have hd : posTrace (cq D (-D)) = traceNorm D := by
    rw [cq_posTrace hD hD.neg, hneg]
    exact (trace_norm_jordan_mass _ hD).symm
  have hpinch : D5.S3.Quantum.Divergence.FaithfulConditionalGap.pinch X = cq D (-D) := by
    ext ⟨i,a⟩ ⟨j,c⟩
    rw [D5.S3.Quantum.Divergence.FaithfulConditionalGap.pinch_entry, cq_entry, ← hblocks]
    fin_cases a <;> fin_cases c <;> simp [D, diagonalBlock]
  have hnorm := D5.S3.Quantum.Divergence.FaithfulConditionalGap.pinch_contract X
  rw [hpinch] at hnorm
  have hC : (cq D (-D)).IsHermitian := by
    rw [Matrix.IsHermitian, cq, Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_kronecker, hD.eq, hD.neg.eq, (ray_psd e₀).isHermitian.eq,
      (ray_psd e₁).isHermitian.eq]
  have htrC : rtrace (cq D (-D)) = 0 := by
    unfold rtrace
    simp [cq_trace]
  have htrX : rtrace X = 0 := by simp [rtrace, ht]
  have htrO : rtrace (amp channel X) = 0 := by
    have h := trace_partialTraceRight (amp channel X)
    change (ptr (amp channel X)).trace = (amp channel X).trace at h
    rw [ptr_amp, hptr, Matrix.trace_zero] at h
    simp [rtrace, ← h]
  have hO : (amp channel X).IsHermitian := by
    rw [ho]
    exact show (D ⊗ₖ (ray e₀ - ray b))ᴴ = _ by
      rw [Matrix.conjTranspose_kronecker, hD.eq,
        ((ray_psd e₀).isHermitian.sub (ray_psd b).isHermitian).eq]
  have hnO : traceNorm (amp channel X) = (6 / 5 : ℝ) * traceNorm D := by
    rw [ho, traceNorm_kronecker, output_contrast_norm, mul_comm]
  linarith [twice_posTrace X hX, twice_posTrace (cq D (-D)) hC,
    twice_posTrace (amp channel X) hO]

private theorem endpoint_pair {R : Type} [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (R × Fin 2) (R × Fin 2) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρt : ρ.trace = 1)
    (hσt : σ.trace = 1) (hm : ptr ρ = ptr σ) :
    E 1 (amp channel ρ) (amp channel σ) ≤ (3 / 5 : ℝ) * E 1 ρ σ := by
  have ht : (ρ - σ).trace = 0 := by simp [Matrix.trace_sub, hρt, hσt]
  have hp : ptr (ρ - σ) = 0 := by
    simpa only [one_smul, hm, sub_self] using ptr_sub_smul 1 ρ σ
  have he := posTrace_contrast (ρ - σ) (hρ.isHermitian.sub hσ.isHermitian) ht hp
  have ha : amp channel (ρ - σ) = amp channel ρ - amp channel σ := by
    simpa only [one_smul] using amp_sub_smul channel 1 ρ σ
  simpa only [E, one_smul, ha] using he

private theorem orthogonal_input {R : Type*} [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (R × Fin 2) (R × Fin 2) ℂ} (hρ : ρ.PosSemidef)
    (hρt : ρ.trace = 1) (hσ : σ.PosSemidef) (ho : ρ * σ = 0)
    {γ : ℝ} (hγ : 0 ≤ γ) : E γ ρ σ = 1 := by
  have he := CFC.posPart_negPart_unique (a := ρ - γ • σ) (b := ρ) (c := γ • σ)
    rfl (by rw [Matrix.mul_smul, ho, smul_zero]) hρ.nonneg (hσ.smul hγ).nonneg
  change rtrace ((ρ - γ • σ)⁺) = 1
  simp [he.1, rtrace, hρt]

private theorem orthogonal_pair {R : Type} [Fintype R] [DecidableEq R]
    {ρ σ : Matrix (R × Fin 2) (R × Fin 2) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρt : ρ.trace = 1)
    (hσt : σ.trace = 1) (hm : ptr ρ = ptr σ) (ho : ρ * σ = 0)
    {γ : ℝ} (hγ : 1 ≤ γ) :
    E γ (amp channel ρ) (amp channel σ) ≤ (3 / 5 : ℝ) := by
  have hn := amp_psd channel hσ
  have hp := amp_psd channel hρ
  have hle : amp channel ρ - γ • amp channel σ ≤ amp channel ρ - amp channel σ := by
    apply sub_le_sub_left
    have h := (hn.smul (sub_nonneg.mpr hγ)).nonneg
    rwa [sub_smul, one_smul, sub_nonneg] at h
  have h := posTrace_mono (hp.isHermitian.sub (hn.isHermitian.smul (IsSelfAdjoint.all γ)))
    (hp.isHermitian.sub hn.isHermitian) hle
  have ht := endpoint_pair hρ hσ hρt hσt hm
  rw [orthogonal_input hρ hρt hσ ho zero_le_one, mul_one] at ht
  exact h.trans (by simpa only [E, one_smul] using ht)

private theorem endpoint_upper : completeCoefficient channel 1 false ≤ 3 / 5 := by
  apply csSup_le (by simp)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · rcases hx with ⟨R, fR, dR, ρ, σ, hρ, hρt, hσ, hσt, hm, _, hd, rfl⟩
    letI := fR
    letI := dR
    exact (div_le_iff₀ hd).mpr (endpoint_pair hρ hσ hρt hσt hm)

private theorem orthogonal_upper {γ : ℝ} (hγ : 1 ≤ γ) :
    completeCoefficient channel γ true ≤ 3 / 5 := by
  apply csSup_le (by simp)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · rcases hx with ⟨R, fR, dR, ρ, σ, hρ, hρt, hσ, hσt, hm, ho, _, rfl⟩
    letI := fR
    letI := dR
    rw [orthogonal_input hρ hρt hσ (ho rfl) (zero_le_one.trans hγ), div_one]
    exact orthogonal_pair hρ hσ hρt hσt hm (ho rfl) hγ

private def ρ₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 131 : ℝ) • (ray e₀ + (2 : ℝ) • ray ![1, -8])

private def σ₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 262 : ℝ) • ((2 : ℝ) • ray ![1, -8] + (64 : ℝ) • ray e₁)

private def σ₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  (4 / 262 : ℝ) • ray ![1, -4]

private def ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := cq ρ₀ 0
private def σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := cq σ₀ σ₁

private theorem witness_states :
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧ ptr ρ = ptr σ := by
  refine ⟨cq_psd (((ray_psd _).add ((ray_psd _).smul (by norm_num))).smul (by norm_num))
    Matrix.PosSemidef.zero, ?_,
    cq_psd ((((ray_psd _).smul (by norm_num)).add
        ((ray_psd _).smul (by norm_num))).smul (by norm_num))
      ((ray_psd _).smul (by norm_num)), ?_, ?_⟩
  · rw [ρ, cq_trace]
    simp only [ρ₀, Matrix.trace_smul, Matrix.trace_add, ray, trace_vecMulVec]
    norm_num [e₀, dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.real_smul, map_ofNat]
  · rw [σ, cq_trace]
    simp only [σ₀, σ₁, Matrix.trace_smul, Matrix.trace_add, ray, trace_vecMulVec]
    norm_num [e₁, dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.real_smul, map_ofNat]
  · rw [ρ, σ, cq_ptr, cq_ptr]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ρ₀, σ₀, σ₁, ray, e₀, e₁, Matrix.add_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, map_ofNat]

private def positiveBlock : Matrix (Fin 2) (Fin 2) ℂ := (1 / 131 : ℝ) • ray e₀
private def negativeBlock : Matrix (Fin 2) (Fin 2) ℂ := (64 / 131 : ℝ) • ray e₁
private def secondNegativeBlock : Matrix (Fin 2) (Fin 2) ℂ :=
  (4 / 131 : ℝ) • ray ![1, -4]

private theorem witness_decomp :
    ρ - (2 : ℝ) • σ = cq (positiveBlock - negativeBlock) (-secondNegativeBlock) := by
  ext ⟨i,a⟩ ⟨j,c⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases c <;>
    norm_num [ρ, σ, ρ₀, σ₀, σ₁, positiveBlock, negativeBlock, secondNegativeBlock,
      cq_entry, ray, e₀, e₁,
      Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, map_ofNat]

private theorem witness_input : E 2 ρ σ = 1 / 131 := by
  have hP : positiveBlock.PosSemidef := (ray_psd _).smul (by norm_num)
  have hQ : negativeBlock.PosSemidef := (ray_psd _).smul (by norm_num)
  have hB : secondNegativeBlock.PosSemidef := (ray_psd _).smul (by norm_num)
  have hz : positiveBlock * negativeBlock = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [positiveBlock, negativeBlock, ray, e₀, e₁, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, Fin.sum_univ_two, map_ofNat]
  unfold E
  rw [witness_decomp, cq_posTrace (hP.isHermitian.sub hQ.isHermitian) hB.isHermitian.neg]
  change rtrace ((positiveBlock - negativeBlock)⁺) + rtrace ((-secondNegativeBlock)⁺) = _
  rw [(CFC.posPart_negPart_unique rfl hz hP.nonneg hQ.nonneg).1,
    (CFC.posPart_eq_zero_iff _).mpr (neg_nonpos.mpr hB.nonneg)]
  simp only [positiveBlock, rtrace, Matrix.trace_smul, ray, trace_vecMulVec]
  norm_num [e₀, dotProduct, Pi.star_apply, Complex.real_smul, Fin.sum_univ_two]

private def detector : Fin 2 × Fin 2 → ℂ :=
  fun (i, a) => ![![3, 0], ![0, 1]] i a

private def effect : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 10 : ℝ) • ray detector

private theorem effect_bounds : 0 ≤ effect ∧ effect ≤ 1 := by
  have hp : effect.PosSemidef := (ray_psd _).smul (by norm_num)
  have hi : IsIdempotentElem effect := by
    change effect * effect = effect
    unfold effect ray
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec]
    have hd : star detector ⬝ᵥ detector = (10 : ℂ) := by
      norm_num [detector, dotProduct, Pi.star_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, map_ofNat]
    rw [hd, Matrix.vecMulVec_smul]
    ext i j
    norm_num [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  have hproj : IsStarProjection effect := ⟨hi, hp.isHermitian⟩
  exact ⟨hp.nonneg, sub_nonneg.mp hproj.one_sub.nonneg⟩

set_option maxHeartbeats 1000000 in
-- The detector computation expands a fixed four-by-four rational matrix product.
private theorem witness_output : (9 / 10 : ℝ) * (1 / 131) ≤
    E 2 (amp channel ρ) (amp channel σ) := by
  let Z := amp channel ρ - (2 : ℝ) • amp channel σ
  have hZ : Z.IsHermitian := (amp_psd channel witness_states.1).isHermitian.sub
    ((amp_psd channel witness_states.2.2.1).isHermitian.smul (IsSelfAdjoint.all (2 : ℝ)))
  have hact : Z = ((positiveBlock - negativeBlock) ⊗ₖ ray e₀) +
      ((-secondNegativeBlock) ⊗ₖ ray b) := by
    dsimp only [Z]
    rw [← amp_sub_smul, witness_decomp, amplify]
    congr 2 <;> ext i j <;> simp [diagonalBlock, cq_entry]
  have hc : rtrace (effect * Z) = (9 / 10 : ℝ) * (1 / 131) := by
    rw [hact]
    norm_num [effect, detector, positiveBlock, negativeBlock, secondNegativeBlock,
      ray, e₀, e₁, b, rtrace,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply,
      Matrix.add_apply,
      Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Complex.real_smul, Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      map_ofNat, map_div₀]
  exact hc ▸ effect_le_posTrace hZ effect_bounds.1 effect_bounds.2

private theorem witness_lower : 9 / 10 ≤ completeCoefficient channel 2 false := by
  let x := E 2 (amp channel ρ) (amp channel σ) / E 2 ρ σ
  have hd : 0 < E 2 ρ σ := by rw [witness_input]; norm_num
  obtain ⟨hρ, hρt, hσ, hσt, hm⟩ := witness_states
  have hmemb : x ∈ completeRatios channel 2 false :=
    ⟨Fin 2, inferInstance, inferInstance, ρ, σ, hρ, hρt, hσ, hσt, hm,
      by simp, hd, rfl⟩
  calc
    (9 / 10 : ℝ) ≤ x := (le_div_iff₀ hd).mpr (witness_input ▸ witness_output)
    _ ≤ completeCoefficient channel 2 false :=
      le_csSup (ratios_bounded channel 2 false) (Set.mem_insert_of_mem _ hmemb)

/-- A single binary channel violates gamma monotonicity and orthogonal-input reduction. -/
theorem result :
    completeCoefficient channel 1 false ≤ 3 / 5 ∧
    (∀ γ : ℝ, 1 ≤ γ → completeCoefficient channel γ true ≤ 3 / 5) ∧
    9 / 10 ≤ completeCoefficient channel 2 false := by
  exact ⟨endpoint_upper, fun _ hγ => orthogonal_upper hγ, witness_lower⟩

/-- On this channel the complete coefficient violates both proposed restrictions. -/
theorem refutes_monotonicity_and_orthogonal_reduction :
    ¬ AntitoneOn (fun γ => completeCoefficient channel γ false) (Set.Ici 1) ∧
    completeCoefficient channel 2 true < completeCoefficient channel 2 false := by
  obtain ⟨hendpoint, horth, hwitness⟩ := result
  constructor
  · intro h
    have h21 := h (show (1 : ℝ) ∈ Set.Ici 1 by simp)
      (show (2 : ℝ) ∈ Set.Ici 1 by norm_num) (by norm_num)
    linarith
  · have h := horth 2 (by norm_num)
    linarith

#print axioms refutes_monotonicity_and_orthogonal_reduction

end D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
