/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/BellCenteredConditionalTraceGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/BellCenteredConditionalTraceGap
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Exact Bell-centered conditional trace gaps and zero under output domination. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport

/-! The normalized Bell-pencil witness for the conditional trace gap.
The reference is enlarged by one point, carrying the entire padding state. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap

open _root_.Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (density_posSemidef partialTraceRight trace_partialTraceRight)
open UnitaryReconstruction.LiuWildChoiObstruction
  (bell bell_norm outer pairMatrix)

open private dsum dsum_psd dsum_mul posTrace_dsum posTrace_reindex
  posTrace_smul posTrace_psd posTrace_neg_psd
  act_zero act_smul act_state amp_state from
  D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open private bell_marginal from D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
open RHLinalg (rtrace rtrace_sub)

private def padEquiv (R A : Type*) : Option R × A ≃ (R × A) ⊕ A :=
  (((Equiv.optionEquivSumPUnit.{0} R).prodCongr (Equiv.refl A)).trans
    (Equiv.sumProdDistrib R PUnit A)).trans
      (Equiv.sumCongr (Equiv.refl (R × A)) (Equiv.uniqueProd A PUnit))

section Padding

variable {R A B : Type*} [Fintype R] [DecidableEq R]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The blocks on the `some` and `none` reference sectors, respectively. -/
private def pad (X : Matrix (R × A) (R × A) ℂ) (Y : Matrix A A ℂ) :
    Matrix (Option R × A) (Option R × A) ℂ :=
  (dsum X Y).reindex (padEquiv R A).symm (padEquiv R A).symm

private theorem pad_psd {X : Matrix (R × A) (R × A) ℂ} {Y : Matrix A A ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (pad X Y).PosSemidef := by
  exact (dsum_psd hX hY).submatrix (padEquiv R A)

private theorem trace_pad (X : Matrix (R × A) (R × A) ℂ) (Y : Matrix A A ℂ) :
    (pad X Y).trace = X.trace + Y.trace := by
  unfold pad
  rw [trace_reindex]
  simp [dsum, Matrix.trace, Fintype.sum_sum_type]

private theorem pad_mul (X X' : Matrix (R × A) (R × A) ℂ)
    (Y Y' : Matrix A A ℂ) :
    pad X Y * pad X' Y' = pad (X * X') (Y * Y') := by
  unfold pad
  change (Matrix.reindexRingEquiv ℂ (padEquiv R A).symm) (dsum X Y) *
    (Matrix.reindexRingEquiv ℂ (padEquiv R A).symm) (dsum X' Y') = _
  rw [← (Matrix.reindexRingEquiv ℂ (padEquiv R A).symm).map_mul, dsum_mul]
  rfl

private theorem pad_sub (X X' : Matrix (R × A) (R × A) ℂ)
    (Y Y' : Matrix A A ℂ) :
    pad X Y - pad X' Y' = pad (X - X') (Y - Y') := by
  have h : dsum X Y - dsum X' Y' = dsum (X - X') (Y - Y') := by
    unfold dsum
    simp only [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add,
      neg_zero, add_zero]
  exact congrArg (fun M : Matrix ((R × A) ⊕ A) ((R × A) ⊕ A) ℂ =>
    M.reindex (padEquiv R A).symm (padEquiv R A).symm) h

private theorem posTrace_pad {X : Matrix (R × A) (R × A) ℂ} {Y : Matrix A A ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    posTrace (pad X Y) = posTrace X + posTrace Y := by
  have hXY : (dsum X Y).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hX (by simp) hY
  unfold pad
  rw [posTrace_reindex (padEquiv R A).symm hXY, posTrace_dsum hX hY]

private theorem amp_pad (N : QuantumChannel A B)
    (X : Matrix (R × A) (R × A) ℂ) (Y : Matrix A A ℂ) :
    amp N (pad X Y) = pad (amp N X) (act N Y) := by
  ext ⟨r, b⟩ ⟨s, d⟩
  rw [amp_entry]
  cases r <;> cases s
  · rfl
  · change act N (0 : Matrix A A ℂ) b d = 0
    exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
  · change act N (0 : Matrix A A ℂ) b d = 0
    exact congrArg (fun M : Matrix B B ℂ => M b d) (act_zero N)
  · rfl

private def referencePad (M : Matrix R R ℂ) (t : ℂ) : Matrix (Option R) (Option R) ℂ :=
  let e := (Equiv.optionEquivSumPUnit.{0} R).symm
  (dsum M (t • (1 : Matrix PUnit.{1} PUnit.{1} ℂ))).reindex e e

private theorem ptr_pad (X : Matrix (R × A) (R × A) ℂ) (Y : Matrix A A ℂ) :
    ptr (pad X Y) = referencePad (ptr X) Y.trace := by
  ext r s
  cases r <;> cases s
  · change (∑ a : A, Y a a) = (Y.trace • (1 : Matrix PUnit.{1} PUnit.{1} ℂ))
      PUnit.unit PUnit.unit
    simp [Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, smul_eq_mul]
  · change (∑ _ : A, (0 : ℂ)) = 0
    simp
  · change (∑ _ : A, (0 : ℂ)) = 0
    simp
  · rfl

private theorem posTrace_referencePad_neg {M : Matrix R R ℂ} (hM : M.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    posTrace (referencePad M (-(t : ℂ))) = rtrace M := by
  let U : Matrix PUnit.{1} PUnit.{1} ℂ := 1
  have hU : (t • U).PosSemidef := (Matrix.PosSemidef.one (n := PUnit.{1})).smul ht
  have htU : (-(t : ℂ)) • U = -(t • U) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.neg_apply, Complex.real_smul, smul_eq_mul]
  change posTrace ((dsum M ((-(t : ℂ)) • U)).reindex
    (Equiv.optionEquivSumPUnit.{0} R).symm (Equiv.optionEquivSumPUnit.{0} R).symm) = _
  rw [htU]
  have hsum : (dsum M (-(t • U))).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hM.isHermitian (by simp) hU.isHermitian.neg
  rw [posTrace_reindex _ hsum, posTrace_dsum hM.isHermitian hU.isHermitian.neg,
    posTrace_neg_psd hU, posTrace_psd hM, add_zero]
  rfl

end Padding

private theorem E_one_swap_of_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (h : (X - Y).IsHermitian) (ht : X.trace = Y.trace) :
    E 1 X Y = posTrace (Y - X) := by
  have hj := congrArg rtrace (CFC.posPart_sub_negPart (X - Y) h)
  change rtrace ((X - Y)⁺ - (X - Y)⁻) = rtrace (X - Y) at hj
  rw [rtrace_sub, ← CFC.posPart_neg, neg_sub] at hj
  have hz : rtrace (X - Y) = 0 := by simp [rtrace, Matrix.trace_sub, ht]
  unfold E
  rw [one_smul]
  exact sub_eq_zero.mp (hj.trans hz)

/-- The Bell projector in the reference-first product basis, normalized when `A` is nonempty. -/
def bellProjector (A : Type*) [Fintype A] [DecidableEq A] :
    Matrix (A × A) (A × A) ℂ :=
  outer (bell A)

/-- The normalized Bell-centered pair with one reference padding block.
The reference contribution is recorded explicitly and is preserved by the channel. -/
theorem bell_padded_gap {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (N : QuantumChannel A B)
    (ω : DensityState A) (ε : ℝ)
    (hε : 0 < ε) (hεD : ε ≤ (Fintype.card A : ℝ) ^ 2 - 1) :
    let d : ℝ := Fintype.card A
    let D : ℝ := d ^ 2 - 1
    let P := bellProjector A
    let C := 1 - P
    let ρ := D⁻¹ • pad C (0 : Matrix A A ℂ)
    let σ := D⁻¹ • pad (ε • P) ((D - ε) • pairMatrix ω)
    Fintype.card (Option A) = Fintype.card A + 1 ∧
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ σ.PosSemidef ∧ σ.trace = 1 ∧ ρ * σ = 0 ∧
      E 1 (ptr ρ) (ptr σ) = (D - ε) / D ∧
      gap 1 ρ σ = ε / D ∧ 0 < gap 1 ρ σ ∧
      gap 1 (amp N ρ) (amp N σ) = posTrace (ε • amp N P - amp N C) / D ∧
      gap 1 (amp N ρ) (amp N σ) / gap 1 ρ σ =
        posTrace (ε • amp N P - amp N C) / ε ∧
      (gap 1 (amp N ρ) (amp N σ) = 0 ↔ ε • amp N P ≤ amp N C) ∧
      (gap 1 (amp N ρ) (amp N σ) / gap 1 ρ σ = 0 ↔ ε • amp N P ≤ amp N C) := by
  intro d D P C ρ σ
  let c : ℝ := D⁻¹
  let t : ℝ := D - ε
  let H := C - ε • P
  let W := pairMatrix ω
  have hD : 0 < D := hε.trans_le hεD
  have hd : 2 ≤ Fintype.card A := by
    by_contra! hd
    have hd₁ : d ≤ 1 := by
      change (Fintype.card A : ℝ) ≤ 1
      exact_mod_cast (show Fintype.card A ≤ 1 by omega)
    have hsq : d ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd₁ 2
    change 0 < d ^ 2 - 1 at hD
    linarith
  have hdpos : 0 < d := by
    change (0 : ℝ) < (Fintype.card A : ℝ)
    exact_mod_cast (show 0 < Fintype.card A by omega)
  change ε ≤ d ^ 2 - 1 at hεD
  have ht : 0 ≤ t := sub_nonneg.mpr hεD
  have hc : 0 ≤ c := (inv_pos.mpr hD).le
  let _ : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have hPn : star (bell A) ⬝ᵥ bell A = 1 := bell_norm
  have hP : P.PosSemidef := Matrix.posSemidef_vecMulVec_self_star (bell A)
  have hP₂ : P * P = P := by
    change outer (bell A) * outer (bell A) = outer (bell A)
    simp only [outer, Matrix.vecMulVec_mul_vecMulVec, hPn, one_smul]
  have hPt : P.trace = 1 := by
    change (outer (bell A)).trace = 1
    rw [outer, Matrix.trace_vecMulVec, dotProduct_comm, hPn]
  have hC : C.PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self C
    have hGram : C.conjTranspose * C = C := by
      change (1 - P).conjTranspose * (1 - P) = 1 - P
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isHermitian.eq,
        sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hP₂, sub_self, sub_zero]
    rwa [hGram] at h
  have hCt : C.trace = (D : ℂ) := by
    change ((1 : Matrix (A × A) (A × A) ℂ) - P).trace = (D : ℂ)
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_prod, hPt]
    simp [D, d, pow_two]
  have hW : W.PosSemidef := density_posSemidef ω
  have hWt : W.trace = 1 := ω.2.2
  have hρ : ρ.PosSemidef := (pad_psd hC Matrix.PosSemidef.zero).smul hc
  have hσ : σ.PosSemidef := (pad_psd (hP.smul hε.le) (hW.smul ht)).smul hc
  have hnormalize : c * D = 1 := inv_mul_cancel₀ hD.ne'
  have hsplit : ε + t = D := by
    change ε + (D - ε) = D
    ring
  have hρt : ρ.trace = 1 := by
    change (c • pad C (0 : Matrix A A ℂ)).trace = 1
    simp only [Matrix.trace_smul, trace_pad, hCt, Matrix.trace_zero, add_zero,
      Complex.real_smul, ← Complex.ofReal_mul, hnormalize, Complex.ofReal_one]
  have hσt : σ.trace = 1 := by
    change (c • pad (ε • P) (t • W)).trace = 1
    simp only [Matrix.trace_smul, trace_pad, hPt, hWt, Complex.real_smul, mul_one,
      ← Complex.ofReal_add, hsplit, ← Complex.ofReal_mul, hnormalize, Complex.ofReal_one]
  have horth : ρ * σ = 0 := by
    have hCP : C * P = 0 := by
      change (1 - P) * P = 0
      rw [sub_mul, Matrix.one_mul, hP₂, sub_self]
    have hCεP : C * (ε • P) = 0 := by rw [Matrix.mul_smul, hCP, smul_zero]
    change (c • pad C (0 : Matrix A A ℂ)) * (c • pad (ε • P) (t • W)) = 0
    rw [Matrix.smul_mul, Matrix.mul_smul, pad_mul, hCεP, Matrix.zero_mul]
    simp [pad, dsum, Matrix.reindex_apply]
  have hsub : ρ - σ = c • pad H (-(t • W)) := by
    change c • pad C 0 - c • pad (ε • P) (t • W) = _
    rw [← smul_sub, pad_sub, zero_sub]
  have hHtrace : H.trace = (t : ℂ) := by
    change (C - ε • P).trace = (t : ℂ)
    rw [Matrix.trace_sub, Matrix.trace_smul, hCt, hPt, Complex.real_smul,
      mul_one, ← Complex.ofReal_sub]
  have hptrOne : ptr (1 : Matrix (A × A) (A × A) ℂ) = d • (1 : Matrix A A ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ptr, partialTraceRight, Matrix.smul_apply, Complex.real_smul, d]
    · simp [ptr, partialTraceRight, Matrix.smul_apply, Prod.mk.injEq, hij]
  have hptrP : ptr P = d⁻¹ • (1 : Matrix A A ℂ) := by
    have hbell : ptr P = (Fintype.card A : ℂ)⁻¹ • (1 : Matrix A A ℂ) := bell_marginal
    rw [hbell]
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, d]
  have hptrC : ptr C = (d - d⁻¹) • (1 : Matrix A A ℂ) := by
    change ptr ((1 : Matrix (A × A) (A × A) ℂ) - P) = _
    rw [show ptr ((1 : Matrix (A × A) (A × A) ℂ) - P) =
      ptr (1 : Matrix (A × A) (A × A) ℂ) - ptr P by
        simpa only [one_smul] using ptr_sub_smul 1 (1 : Matrix (A × A) (A × A) ℂ) P,
      hptrOne, hptrP, sub_smul]
  have hptrH : (ptr H).PosSemidef := by
    have hs : ptr H = (d - (1 + ε) * d⁻¹) • (1 : Matrix A A ℂ) := by
      change ptr (C - ε • P) = _
      rw [ptr_sub_smul, hptrC, hptrP, smul_smul, ← sub_smul]
      congr 1
      ring
    have hcoef : 0 ≤ d - (1 + ε) * d⁻¹ := by
      rw [← div_eq_mul_inv]
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hdpos).2
      nlinarith
    rw [hs]
    exact Matrix.PosSemidef.one.smul hcoef
  have hbase : E 1 (ptr ρ) (ptr σ) = t / D := by
    have hptrsub : ptr (ρ - σ) = ptr ρ - ptr σ := by
      simpa only [one_smul] using ptr_sub_smul 1 ρ σ
    have htracePad : (-(t • W)).trace = -(t : ℂ) := by
      rw [Matrix.trace_neg, Matrix.trace_smul, hWt, Complex.real_smul, mul_one]
    unfold E
    rw [one_smul, ← hptrsub, hsub,
      show ptr (c • pad H (-(t • W))) = c • ptr (pad H (-(t • W))) from
        partialTraceRight_smul c _,
      posTrace_smul c hc, ptr_pad, htracePad, posTrace_referencePad_neg hptrH t ht]
    have hrt : rtrace (ptr H) = t := by
      change (partialTraceRight H).trace.re = t
      rw [trace_partialTraceRight, hHtrace, Complex.ofReal_re]
    rw [hrt, div_eq_mul_inv]
    exact mul_comm c t
  have hEin : E 1 ρ σ = 1 := by
    have hp :=
      (CFC.posPart_negPart_unique (a := ρ - σ) (b := ρ) (c := σ)
        rfl horth hρ.nonneg hσ.nonneg).1
    change rtrace ((ρ - (1 : ℝ) • σ)⁺) = 1
    rw [one_smul, hp]
    change ρ.trace.re = 1
    rw [hρt, Complex.one_re]
  have hin : gap 1 ρ σ = ε / D := by
    rw [gap, hEin, hbase]
    apply (eq_div_iff hD.ne').2
    calc
      (1 - t / D) * D = D - t := by rw [sub_mul, one_mul, div_mul_cancel₀ _ hD.ne']
      _ = ε := by
        dsimp only [t]
        ring
  have hswap : σ - ρ = c • pad (ε • P - C) (t • W) := by
    change c • pad (ε • P) (t • W) - c • pad C 0 = _
    rw [← smul_sub, pad_sub, sub_zero]
  have hPN := amp_psd N hP
  have hCN := amp_psd N hC
  have hK : (ε • amp N P - amp N C).IsHermitian :=
    (hPN.smul hε.le).isHermitian.sub hCN.isHermitian
  have hWN := act_state N (X := W) ⟨hW, hWt⟩
  have hσρout : amp N σ - amp N ρ =
      c • pad (ε • amp N P - amp N C) (t • act N W) := by
    rw [← (show amp N (σ - ρ) = amp N σ - amp N ρ by
      simpa only [one_smul] using amp_sub_smul N 1 σ ρ), hswap, amp_smul, amp_pad, act_smul]
    rw [(show amp N (ε • P - C) = amp N (ε • P) - amp N C by
      simpa only [one_smul] using amp_sub_smul N 1 (ε • P) C), amp_smul]
  have hEout : E 1 (amp N ρ) (amp N σ) =
      posTrace (ε • amp N P - amp N C) / D + t / D := by
    have hρN := amp_state N (X := ρ) ⟨hρ, hρt⟩
    have hσN := amp_state N (X := σ) ⟨hσ, hσt⟩
    rw [E_one_swap_of_trace_eq (hρN.1.isHermitian.sub hσN.1.isHermitian)
      (hρN.2.trans hσN.2.symm), hσρout, posTrace_smul c hc,
      posTrace_pad hK (hWN.1.smul ht).isHermitian,
      posTrace_smul t ht, posTrace_psd hWN.1]
    have htW : rtrace (act N W) = 1 := by
      change (act N W).trace.re = 1
      rw [hWN.2, Complex.one_re]
    change c * (posTrace (ε • amp N P - amp N C) + t * rtrace (act N W)) = _
    rw [htW, mul_one]
    simp only [div_eq_mul_inv, c]
    ring
  have hout : gap 1 (amp N ρ) (amp N σ) = posTrace (ε • amp N P - amp N C) / D := by
    rw [gap, ptr_amp, ptr_amp, hEout, hbase, add_sub_cancel_right]
  have hin_pos : 0 < gap 1 ρ σ := hin ▸ div_pos hε hD
  have hratio : gap 1 (amp N ρ) (amp N σ) / gap 1 ρ σ =
      posTrace (ε • amp N P - amp N C) / ε := by
    rw [hout, hin, div_div_div_cancel_right₀ hD.ne']
  let K := ε • amp N P - amp N C
  have hKpsd : K⁺.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg K)
  have htrace : posTrace K = 0 ↔ K⁺ = 0 := by
    constructor
    · intro h
      have hi := (Complex.nonneg_iff.mp hKpsd.trace_nonneg).2
      exact hKpsd.trace_eq_zero_iff.mp (Complex.ext h hi.symm)
    · intro h
      change (K⁺).trace.re = 0
      rw [h, Matrix.trace_zero, Complex.zero_re]
  have hzero : posTrace K = 0 ↔ ε • amp N P ≤ amp N C := by
    rw [htrace, CFC.posPart_eq_zero_iff K hK]
    exact sub_nonpos
  refine ⟨Fintype.card_option, hρ, hρt, hσ, hσt, horth, hbase, hin, hin_pos, hout, hratio, ?_, ?_⟩
  · rw [hout, div_eq_zero_iff]
    simpa only [hD.ne', or_false] using hzero
  · rw [hratio, div_eq_zero_iff]
    simpa only [hε.ne', or_false] using hzero

#print axioms bell_padded_gap

end D5.S3.Quantum.Divergence.ConditionalExpansion.BellCenteredConditionalTraceGap
