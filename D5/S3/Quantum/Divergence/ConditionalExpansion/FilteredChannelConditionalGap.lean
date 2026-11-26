/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/FilteredChannelConditionalGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite CPTP filter preserves a uniform fraction of the conditional trace gap. -/

import D5.S3.Quantum.Divergence.ConditionalExpansion.DerivativeFreeHarmonicCongruence
import D5.S3.Quantum.Divergence.UmegakiKernelContraction

/-! A finite channel obtained by filtering a normalized tensor extension, and its
conditional trace-gap bounds over all finite references. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FilteredChannelConditionalGap

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open DerivativeFreeHarmonicCongruence
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (partialTraceRight_embed_mul partialTraceRight_posDef)
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open RHLinalg (rtrace rtrace_add rtrace_sub trace_mul_nonneg_of_posSemidef)

universe u
variable {S R A E : Type u}
  [Fintype S] [DecidableEq S] [Fintype R] [DecidableEq R]
  [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]

private theorem rt_smul {n : Type*} [Fintype n] (a : ℝ) (M : Matrix n n ℂ) :
    rtrace (a • M) = a * rtrace M := by
  change (Matrix.trace (a • M)).re = a * M.trace.re
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private theorem rt_mul_comm {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    rtrace (X * Y) = rtrace (Y * X) :=
  congrArg Complex.re (Matrix.trace_mul_comm X Y)

private theorem rt_embed (X : Matrix S S ℂ) (Y : Matrix (S × E) (S × E) ℂ) :
    rtrace ((X ⊗ₖ (1 : Matrix E E ℂ)) * Y) =
      rtrace (X * partialTraceRight Y) := by
  unfold rtrace
  rw [← trace_partialTraceRight, partialTraceRight_embed_mul]

private theorem psd_B (Z Q : Matrix S S ℂ) (hQ : Q.IsHermitian) :
    (harmonicB Z Q).PosSemidef := by
  have hp := (CFC.posPart_nonneg Z).posSemidef.conjTranspose_mul_mul_same Q
  have hm := (CFC.negPart_nonneg Z).posSemidef.conjTranspose_mul_mul_same (1 - Q)
  simpa only [harmonicB, hQ.eq, (Matrix.isHermitian_one.sub hQ).eq] using hp.add hm

private theorem rt_B (Z Q : Matrix S S ℂ) (hZ : Z.IsHermitian) (hh : Q * Q = Q) :
    rtrace (harmonicB Z Q) = harmonicDelta Z Q := by
  have hcomp : (1 - Q) * (1 - Q) = 1 - Q := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hh, sub_self, sub_zero]
  have hcycle (P X : Matrix S S ℂ) (hP : P * P = P) :
      rtrace (P * X * P) = rtrace (P * X) := by
    rw [rt_mul_comm (P * X) P, ← mul_assoc, hP]
  have hdecomp := congrArg (fun X => rtrace (Q * X)) (CFC.posPart_sub_negPart Z hZ)
  change rtrace (Q * (Z⁺ - Z⁻)) = rtrace (Q * Z) at hdecomp
  rw [mul_sub, rtrace_sub] at hdecomp
  unfold harmonicB harmonicDelta
  change rtrace (Q * Z⁺ * Q + (1 - Q) * Z⁻ * (1 - Q)) =
    rtrace ((-Z)⁺) + rtrace (Q * Z)
  rw [CFC.posPart_neg, rtrace_add, hcycle Q _ hh, hcycle (1-Q) _ hcomp,
    sub_mul, Matrix.one_mul, rtrace_sub]
  linarith

private theorem tensor_parts (Z : Matrix S S ℂ) (hZ : Z.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) :
    (a • (Z ⊗ₖ (1 : Matrix E E ℂ)))⁺ = a • (Z⁺ ⊗ₖ (1 : Matrix E E ℂ)) ∧
    (a • (Z ⊗ₖ (1 : Matrix E E ℂ)))⁻ = a • (Z⁻ ⊗ₖ (1 : Matrix E E ℂ)) := by
  apply CFC.posPart_negPart_unique
  · rw [← smul_sub]
    have h := congrArg (fun M : Matrix S S ℂ => M ⊗ₖ (1 : Matrix E E ℂ))
      (CFC.posPart_sub_negPart Z hZ)
    have ht : (Z⁺ - Z⁻) ⊗ₖ (1 : Matrix E E ℂ) =
        Z⁺ ⊗ₖ (1 : Matrix E E ℂ) - Z⁻ ⊗ₖ (1 : Matrix E E ℂ) := by
      ext i j
      simp [Matrix.kronecker, Matrix.kroneckerMap, sub_mul]
    rw [ht] at h
    rw [h]
  · rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
      CFC.posPart_mul_negPart, Matrix.zero_kronecker, smul_zero, smul_zero]
  · exact smul_nonneg ha ((CFC.posPart_nonneg Z).posSemidef.kronecker
      Matrix.PosSemidef.one).nonneg
  · exact smul_nonneg ha ((CFC.negPart_nonneg Z).posSemidef.kronecker
      Matrix.PosSemidef.one).nonneg

private theorem tensor_B (Z P : Matrix S S ℂ) (hZ : Z.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) :
    harmonicB (a • (Z ⊗ₖ (1 : Matrix E E ℂ))) (P ⊗ₖ (1 : Matrix E E ℂ)) =
      a • (harmonicB Z P ⊗ₖ (1 : Matrix E E ℂ)) := by
  have hp := tensor_parts (E := E) Z hZ a ha
  have hc : (1 : Matrix (S × E) (S × E) ℂ) - P ⊗ₖ (1 : Matrix E E ℂ) =
      (1-P) ⊗ₖ (1 : Matrix E E ℂ) := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp [Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply, Prod.mk.injEq]
    split <;> split <;> simp_all
  simp only [harmonicB, hp.1, hp.2, hc, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, ← smul_add, ← Matrix.add_kronecker]

private theorem rt_tensor (Z : Matrix S S ℂ) [Nonempty E] :
    rtrace (((Fintype.card E : ℝ)⁻¹) • (Z ⊗ₖ (1 : Matrix E E ℂ))) = rtrace Z := by
  have hn : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [rt_smul]
  unfold rtrace
  rw [Matrix.trace_kronecker, Matrix.trace_one]
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  field_simp

/-- Tensoring with a normalized identity and filtering with a positive definite
matrix preserves at least the reciprocal inverse-marginal bound of the sector gap. -/
private theorem tensor_filtered_sector_bound [Nonempty E]
    (Z P : Matrix S S ℂ) (W : Matrix (S × E) (S × E) ℂ)
    (hZ : Z.IsHermitian) (hP : P.IsHermitian) (hPP : P * P = P)
    (hW : W.PosDef) (hcomm : Commute W (P ⊗ₖ (1 : Matrix E E ℂ)))
    (k : ℝ) (hk : 0 < k)
    (hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight W = 1)
    (hinv : (Fintype.card E : ℝ)⁻¹ • partialTraceRight W⁻¹ ≤ k • (1 : Matrix S S ℂ)) :
    let X := (Fintype.card E : ℝ)⁻¹ • (Z ⊗ₖ (1 : Matrix E E ℂ))
    posTrace (-(CFC.sqrt W * X * CFC.sqrt W)) + rtrace (P * Z) ≥
      k⁻¹ * harmonicDelta Z P := by
  let a := (Fintype.card E : ℝ)⁻¹
  let X := a • (Z ⊗ₖ (1 : Matrix E E ℂ))
  let Q := P ⊗ₖ (1 : Matrix E E ℂ)
  let B := harmonicB Z P
  let T := CFC.sqrt W
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hXh : X.IsHermitian := by
    apply Matrix.IsHermitian.smul _ (IsSelfAdjoint.all a)
    change (Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = Z ⊗ₖ (1 : Matrix E E ℂ)
    rw [Matrix.conjTranspose_kronecker, hZ.eq, Matrix.conjTranspose_one]
  have hQh : Q.IsHermitian := by
    change (P ⊗ₖ (1 : Matrix E E ℂ))ᴴ = _
    rw [Matrix.conjTranspose_kronecker, hP.eq, Matrix.conjTranspose_one]
  have hQQ : Q * Q = Q := by
    dsimp only [Q]
    rw [← Matrix.mul_kronecker_mul, hPP, Matrix.one_mul]
  have hBQ : harmonicB X Q = a • (B ⊗ₖ (1 : Matrix E E ℂ)) :=
    tensor_B Z P hZ a ha
  have hδ : harmonicDelta X Q = harmonicDelta Z P := by
    rw [← rt_B X Q hXh hQQ, hBQ, rt_tensor, rt_B Z P hZ hPP]
  have hden : rtrace (W⁻¹ * harmonicB X Q) ≤ k * harmonicDelta Z P := by
    rw [hBQ, Matrix.mul_smul, rt_smul, rt_mul_comm W⁻¹, rt_embed]
    have hp : 0 ≤ rtrace (B * (k • (1 : Matrix S S ℂ) - a • partialTraceRight W⁻¹)) :=
      trace_mul_nonneg_of_posSemidef (psd_B Z P hP) (sub_nonneg.mpr hinv).posSemidef
    rw [mul_sub, rtrace_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      rt_smul, rt_smul, rt_B Z P hZ hPP] at hp
    linarith
  have hTQ : Commute T Q := by
    change Commute (CFC.sqrt W) Q
    rw [CFC.sqrt_eq_real_sqrt W hW.posSemidef.nonneg]
    exact hcomm.cfcₙ_real Real.sqrt
  have hTT : T * T = W := CFC.sqrt_mul_sqrt_self W hW.posSemidef.nonneg
  have htrace : rtrace (Q * (T * X * T)) = rtrace (P * Z) := by
    calc
      _ = rtrace (T * (Q * (T * X))) := by
        rw [← mul_assoc Q (T * X) T, rt_mul_comm]
      _ = rtrace (Q * (W * X)) := by
        rw [← mul_assoc T Q, hTQ.eq, mul_assoc, ← mul_assoc T T, hTT]
      _ = rtrace (W * (Q * X)) := by
        rw [← mul_assoc, ← hcomm.eq, mul_assoc]
      _ = rtrace (P * Z) := by
        dsimp only [X, Q]
        rw [Matrix.mul_smul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
          Matrix.mul_smul, rt_smul, rt_mul_comm W, rt_embed, ← rt_smul,
          ← Matrix.mul_smul, hnorm, Matrix.mul_one]
  have hb := derivative_free_harmonic_congruence W X Q hW hXh hQh hQQ hcomm k⁻¹
  unfold harmonicValue at hb
  rw [hδ, htrace] at hb
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg k⁻¹)
  have he : k⁻¹ ^ 2 * (k * harmonicDelta Z P) = k⁻¹ * harmonicDelta Z P := by
    field_simp
  rw [he] at hmul
  change k⁻¹ * harmonicDelta Z P ≤ posTrace (-(T * X * T)) + rtrace (P * Z)
  linarith

private theorem spectral_positive_projection {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℂ) (hT : T.IsHermitian) :
    ∃ P : Matrix n n ℂ, P.IsHermitian ∧ P * P = P ∧ P * T = T⁺ := by
  classical
  let d : n → ℂ := fun i => if 0 < hT.eigenvalues i then 1 else 0
  let U : Matrix n n ℂ := ↑hT.eigenvectorUnitary
  let D := Matrix.diagonal d
  let P := U * D * Uᴴ
  have hU : Uᴴ * U = 1 := hT.eigenvectorUnitary.2.1
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    by_cases hi : 0 < hT.eigenvalues i <;> simp [d, hi]
  have hDD : D * D = D := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : 0 < hT.eigenvalues i <;> simp [d, hi]
  have hTdiag : T = U * Matrix.diagonal (Complex.ofReal ∘ hT.eigenvalues) * Uᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U,
      RCLike.ofReal_eq_complex_ofReal] using hT.spectral_theorem
  have hTpos : T⁺ = U * Matrix.diagonal
      (Complex.ofReal ∘ (fun x : ℝ => x⁺) ∘ hT.eigenvalues) * Uᴴ := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp), hT.cfc_eq]
    rfl
  have hDiag : D * Matrix.diagonal (Complex.ofReal ∘ hT.eigenvalues) =
      Matrix.diagonal (Complex.ofReal ∘ (fun x : ℝ => x⁺) ∘ hT.eigenvalues) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : 0 < hT.eigenvalues i
    · simp [Function.comp_apply, d, hi, posPart_eq_self.mpr hi.le]
    · simp [Function.comp_apply, d, hi, posPart_eq_zero.mpr (le_of_not_gt hi)]
  refine ⟨P, (hD.mul_mul_conjTranspose_same U).isHermitian, ?_, ?_⟩
  · dsimp only [P]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul, ← Matrix.mul_assoc D D, hDD]
  · rw [hTpos]
    conv_lhs => rw [hTdiag]
    simp only [P, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    rw [← Matrix.mul_assoc D, hDiag]

private theorem ptr_hermitian (Z : Matrix (R × A) (R × A) ℂ)
    (hZ : Z.IsHermitian) : (ptr Z).IsHermitian := by
  change (partialTraceRight Z)ᴴ = partialTraceRight Z
  ext r s
  simp only [Matrix.conjTranspose_apply, partialTraceRight, star_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun M : Matrix (R × A) (R × A) ℂ => M (r,a) (s,a)) hZ.eq

private theorem negative_sector (Z : Matrix (R × A) (R × A) ℂ) (hZ : Z.IsHermitian) :
    ∃ P : Matrix R R ℂ, P.IsHermitian ∧ P * P = P ∧
      rtrace ((P ⊗ₖ (1 : Matrix A A ℂ)) * Z) = -posTrace (-ptr Z) := by
  obtain ⟨P, hP, hPP, hp⟩ :=
    spectral_positive_projection (-ptr Z) (ptr_hermitian Z hZ).neg
  refine ⟨P, hP, hPP, ?_⟩
  have h := congrArg rtrace hp
  change rtrace (P * (-ptr Z)) = posTrace (-ptr Z) at h
  simp only [mul_neg, rtrace, Matrix.trace_neg, map_neg] at h
  change rtrace ((P ⊗ₖ (1 : Matrix A A ℂ)) * Z) = _
  unfold rtrace
  rw [← trace_partialTraceRight, partialTraceRight_embed_mul]
  change rtrace (P * ptr Z) = _
  change -rtrace (P * ptr Z) = posTrace (-ptr Z) at h
  linarith

private theorem posTrace_reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : n ≃ m) (X : Matrix n n ℂ)
    (hX : X.IsHermitian) :
    posTrace (X.reindex e e) = posTrace X := by
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  have hp : (F X)⁺ = F X⁺ := by
    apply (CFC.posPart_negPart_unique (b := F X⁺) (c := F X⁻) ?_ ?_ ?_ ?_).1
    · rw [← map_sub, CFC.posPart_sub_negPart X hX]
    · rw [← map_mul, CFC.posPart_mul_negPart, map_zero]
    · exact ((CFC.posPart_nonneg X).posSemidef.submatrix e.symm).nonneg
    · exact ((CFC.negPart_nonneg X).posSemidef.submatrix e.symm).nonneg
  change rtrace (F X)⁺ = rtrace X⁺
  rw [hp]
  exact congrArg Complex.re (trace_reindex e X⁺)

/-- Actual filtered action with environment initialized to its normalized identity. -/
def filterAction (G : Matrix (A × E) (A × E) ℂ) (Z : Matrix A A ℂ) :
    Matrix (A × E) (A × E) ℂ :=
  CFC.sqrt G * ((Fintype.card E : ℝ)⁻¹ • (Z ⊗ₖ (1 : Matrix E E ℂ))) * CFC.sqrt G

private theorem amp_filterAction (G : Matrix (A × E) (A × E) ℂ)
    (N : QuantumChannel A (A × E)) (hN : ∀ Z, act N Z = filterAction G Z)
    (Z : Matrix (R × A) (R × A) ℂ) :
    amp N Z =
      ((1 : Matrix R R ℂ) ⊗ₖ CFC.sqrt G) *
        ((Fintype.card E : ℝ)⁻¹ •
          ((Z ⊗ₖ (1 : Matrix E E ℂ)).reindex (Equiv.prodAssoc R A E) (Equiv.prodAssoc R A E))) *
        ((1 : Matrix R R ℂ) ⊗ₖ CFC.sqrt G) := by
  let T := CFC.sqrt G
  let M := (Fintype.card E : ℝ)⁻¹ •
    ((Z ⊗ₖ (1 : Matrix E E ℂ)).reindex (Equiv.prodAssoc R A E) (Equiv.prodAssoc R A E))
  let U := (1 : Matrix R R ℂ) ⊗ₖ T
  have hleft (r s : R) (b d : A × E) :
      (U * M) (r,b) (s,d) = ∑ j : A × E, T b j * M (r,j) (s,d) := by
    simp [U, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_irrel]
  have hright (r s : R) (b d : A × E) :
      (U * M * U) (r,b) (s,d) =
        ∑ j : A × E, (U * M) (r,b) (s,j) * T j d := by
    change (∑ j : R × (A × E), (U * M) (r,b) j * U j (s,d)) = _
    simp [U, Fintype.sum_prod_type, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_irrel]
  ext ⟨r,b⟩ ⟨s,d⟩
  change amp N Z (r,b) (s,d) = (U * M * U) (r,b) (s,d)
  rw [amp_entry, hN, hright]
  simp_rw [hleft]
  unfold filterAction
  simp only [Matrix.mul_apply]
  rfl

private theorem ptr_reassociated (G : Matrix (A × E) (A × E) ℂ) :
    partialTraceRight
      (((1 : Matrix R R ℂ) ⊗ₖ G).reindex (Equiv.prodAssoc R A E).symm
        (Equiv.prodAssoc R A E).symm) =
      (1 : Matrix R R ℂ) ⊗ₖ partialTraceRight G := by
  ext ⟨r,a⟩ ⟨s,b⟩
  simp [partialTraceRight, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply, Matrix.one_apply]

/-- Uniform conditional trace-gap bound for the actual filtered action of a channel.
The hypothesis on the inverse marginal is in the Loewner order. -/
theorem filtered_channel_conditional_trace_gap [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (k : ℝ) (hk : 0 < k)
    (hinv : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹ ≤ k • (1 : Matrix A A ℂ))
    (N : QuantumChannel A (A × E)) (hN : ∀ X, act N X = filterAction G X)
    (Z : Matrix (R × A) (R × A) ℂ) (hZ : Z.IsHermitian) :
    k⁻¹ * (posTrace (-Z) - posTrace (-ptr Z)) ≤
      posTrace (-amp N Z) - posTrace (-ptr Z) := by
  obtain ⟨q, hq, hqq, hqtr⟩ := negative_sector Z hZ
  let P := q ⊗ₖ (1 : Matrix A A ℂ)
  let e := Equiv.prodAssoc R A E
  let F := Matrix.reindexAlgEquiv ℂ ℂ e
  let W := F.symm ((1 : Matrix R R ℂ) ⊗ₖ G)
  let T := F.symm ((1 : Matrix R R ℂ) ⊗ₖ CFC.sqrt G)
  let a := (Fintype.card E : ℝ)⁻¹
  let X := a • (Z ⊗ₖ (1 : Matrix E E ℂ))
  have hW : W.PosDef :=
    (Matrix.PosDef.one.kronecker hG).submatrix e.injective
  have hP : P.IsHermitian := by
    change (q ⊗ₖ (1 : Matrix A A ℂ))ᴴ = _
    rw [Matrix.conjTranspose_kronecker, hq.eq, Matrix.conjTranspose_one]
  have hPP : P * P = P := by
    dsimp only [P]
    rw [← Matrix.mul_kronecker_mul, hqq, Matrix.one_mul]
  have hcomm : Commute W (P ⊗ₖ (1 : Matrix E E ℂ)) := by
    change W * (P ⊗ₖ (1 : Matrix E E ℂ)) = _ * W
    apply F.injective
    have hQ : F (P ⊗ₖ (1 : Matrix E E ℂ)) =
        q ⊗ₖ (1 : Matrix (A × E) (A × E) ℂ) := by
      change (P ⊗ₖ (1 : Matrix E E ℂ)).reindex e e = _
      dsimp only [P, e]
      rw [Matrix.kronecker_assoc, Matrix.one_kronecker_one]
    simp only [map_mul, hQ, W, AlgEquiv.apply_symm_apply, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
  have hWnorm : a • partialTraceRight W = 1 := by
    change a • partialTraceRight
      (((1 : Matrix R R ℂ) ⊗ₖ G).reindex e.symm e.symm) = 1
    rw [ptr_reassociated, ← Matrix.kronecker_smul, hnorm, Matrix.one_kronecker_one]
  have hWinv : W⁻¹ = F.symm ((1 : Matrix R R ℂ) ⊗ₖ G⁻¹) := by
    change (((1 : Matrix R R ℂ) ⊗ₖ G).reindex e.symm e.symm)⁻¹ = _
    rw [Matrix.inv_reindex, Matrix.inv_kronecker, inv_one]
    rfl
  have hWbound : a • partialTraceRight W⁻¹ ≤ k • (1 : Matrix (R × A) (R × A) ℂ) := by
    rw [hWinv]
    change a • partialTraceRight
      (((1 : Matrix R R ℂ) ⊗ₖ G⁻¹).reindex e.symm e.symm) ≤ _
    rw [ptr_reassociated, ← Matrix.kronecker_smul]
    have hI : (1 : Matrix R R ℂ).PosSemidef := Matrix.PosSemidef.one
    have hp := hI.kronecker (sub_nonneg.mpr hinv).posSemidef
    apply sub_nonneg.mp
    convert hp.nonneg using 1
    rw [show (1 : Matrix R R ℂ) ⊗ₖ
        (k • (1 : Matrix A A ℂ) - a • partialTraceRight G⁻¹) =
        (1 : Matrix R R ℂ) ⊗ₖ (k • (1 : Matrix A A ℂ)) -
          (1 : Matrix R R ℂ) ⊗ₖ (a • partialTraceRight G⁻¹) by
        ext i j
        simp [Matrix.kronecker_apply, mul_sub]]
    simp only [Matrix.kronecker_smul, Matrix.one_kronecker_one]
  have hT : T.PosSemidef :=
    (Matrix.PosSemidef.one.kronecker (CFC.sqrt_nonneg G).posSemidef).submatrix e
  have hTT : T * T = W := by
    dsimp only [T, W]
    rw [← map_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg]
  have hsqrt : CFC.sqrt W = T := CFC.sqrt_unique hTT hT.nonneg
  have hY : (T * X * T).IsHermitian := by
    have hX : X.IsHermitian := by
      apply Matrix.IsHermitian.smul _ (IsSelfAdjoint.all a)
      change (Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = _
      rw [Matrix.conjTranspose_kronecker, hZ.eq, Matrix.conjTranspose_one]
    simpa only [hT.isHermitian.eq] using Matrix.isHermitian_conjTranspose_mul_mul T hX
  have ha : amp N Z = F (T * X * T) := by
    rw [amp_filterAction G N hN]
    simp only [map_mul, T, AlgEquiv.apply_symm_apply, X]
    congr 2
  have hn : posTrace (-amp N Z) = posTrace (-(T * X * T)) := by
    rw [ha, ← map_neg]
    exact posTrace_reindex e _ hY.neg
  have hb := tensor_filtered_sector_bound Z P W hZ hP hPP hW hcomm
    k hk hWnorm hWbound
  change posTrace (-(CFC.sqrt W * X * CFC.sqrt W)) + rtrace (P * Z) ≥
    k⁻¹ * harmonicDelta Z P at hb
  rw [hsqrt, ← hn] at hb
  change rtrace (P * Z) = _ at hqtr
  rw [hqtr, harmonicDelta, hqtr] at hb
  linarith

private def injection (e : E) : Matrix (A × E) A ℂ :=
  fun i j => if i = (j,e) then 1 else 0

private theorem injection_compress (e : E) (G : Matrix (A × E) (A × E) ℂ) :
    (injection (A := A) e)ᴴ * G * injection (A := A) e =
      G.submatrix (fun x => (x,e)) (fun x => (x,e)) := by
  ext i j
  simp [injection, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, Fintype.sum_prod_type, Prod.mk.injEq, ite_mul, mul_ite]

private theorem injection_expand (Z : Matrix A A ℂ) :
    (∑ e : E, injection (A := A) e * Z * (injection (A := A) e)ᴴ) =
      Z ⊗ₖ (1 : Matrix E E ℂ) := by
  ext ⟨i,f⟩ ⟨j,g⟩
  simp [injection, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Prod.mk.injEq, ite_mul, mul_ite]
  by_cases h : f = g
  · subst g
    simp [ite_and]
  · simp [ite_and, h, Ne.symm h]

/-- The filter is a genuine trace-preserving completely positive channel. -/
theorem exists_filtered_channel [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1) :
    ∃ N : QuantumChannel A (A × E), ∀ Z, act N Z = filterAction G Z := by
  let a := (Fintype.card E : ℝ)⁻¹
  let b := Real.sqrt a
  let T := CFC.sqrt G
  let K : E → Matrix (A × E) A ℂ := fun e => b • (T * injection (A := A) e)
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hb : b * b = a := Real.mul_self_sqrt ha
  have hT : T.IsHermitian := (CFC.sqrt_nonneg G).posSemidef.isHermitian
  have hTT : T * T = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hc (e : E) : (K e)ᴴ = b • ((injection (A := A) e)ᴴ * T) := by
    simp only [K, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hT.eq, star_trivial]
  have hcomp (e : E) : (K e)ᴴ * K e =
      a • G.submatrix (fun x => (x,e)) (fun x => (x,e)) := by
    rw [hc]
    dsimp only [K]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hb]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc T T, hTT, ← Matrix.mul_assoc, injection_compress]
  have hsum : (∑ e, (K e)ᴴ * K e) = 1 := by
    simp only [hcomp, ← Finset.smul_sum]
    have hp : (∑ e : E, G.submatrix (fun x => (x,e)) (fun x => (x,e))) =
        partialTraceRight G := by
      ext i j
      simp [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]
    rw [hp, hnorm]
  obtain ⟨N, hN⟩ := finite_kraus_quantum_channel K hsum
  refine ⟨N, fun Z => ?_⟩
  change CStarMatrix.ofMatrix.symm (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix Z)) = _
  rw [hN]
  have hterm (e : E) : K e * Z * (K e)ᴴ =
      a • (T * (injection (A := A) e * Z * (injection (A := A) e)ᴴ) * T) := by
    rw [hc]
    dsimp only [K]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hb, Matrix.mul_assoc]
  simp only [hterm, ← Finset.smul_sum]
  simp only [← Matrix.mul_sum, ← Matrix.sum_mul, injection_expand, filterAction,
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- Equation (25) with the operator norm of the normalized inverse marginal.
All finite reference types and all Hermitian matrices are quantified. -/
theorem filtered_channel_norm_trace_gap [Nonempty A] [Nonempty E]
    (G : Matrix (A × E) (A × E) ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel A (A × E)) (hN : ∀ X, act N X = filterAction G X)
    (Z : Matrix (R × A) (R × A) ℂ) (hZ : Z.IsHermitian) :
    ‖((Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹)‖⁻¹ *
        (posTrace (-Z) - posTrace (-ptr Z)) ≤
      posTrace (-amp N Z) - posTrace (-ptr Z) := by
  let L := (Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹
  have ha : 0 < (Fintype.card E : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hL : L.PosDef := (partialTraceRight_posDef _ hG.inv).smul ha
  have hL0 : L ≠ 0 := by
    intro hz
    have ht := hL.trace_pos
    rw [hz, Matrix.trace_zero] at ht
    exact (lt_irrefl 0 ht)
  have hbound : L ≤ ‖L‖ • (1 : Matrix A A ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact IsSelfAdjoint.le_algebraMap_norm_self L hL.isHermitian
  exact filtered_channel_conditional_trace_gap G hG hnorm ‖L‖
    (norm_pos_iff.mpr hL0) hbound N hN Z hZ

/-- Every admissible conditional hockey-stick ratio of the filtered channel
is bounded below by the reciprocal operator norm of its inverse marginal. -/
theorem filtered_channel_ratio_lower_bound
    {a e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (G : Matrix (a × e) (a × e) ℂ) (hG : G.PosDef)
    (hnorm : (Fintype.card e : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel a (a × e)) (hN : ∀ X, act N X = filterAction G X)
    (γ : ℝ) (orth : Bool) {x : ℝ} (hx : x ∈ ratios N γ orth) :
    ‖((Fintype.card e : ℝ)⁻¹ • partialTraceRight G⁻¹)‖⁻¹ ≤ x := by
  obtain ⟨r, fr, dr, ρ, σ, hρ, _, hσ, _, _, hd, rfl⟩ := hx
  letI := fr
  letI := dr
  let Z := ρ - γ • σ
  have hZ : Z.IsHermitian := hρ.isHermitian.sub (hσ.isHermitian.smul (IsSelfAdjoint.all γ))
  have h := filtered_channel_norm_trace_gap G hG hnorm N hN (-Z) hZ.neg
  have hamp : amp N (-Z) = -amp N Z := by
    simpa only [neg_one_smul] using amp_smul N (-1) Z
  have hptr : ptr (-Z) = -ptr Z := by
    change partialTraceRight (-Z) = -partialTraceRight Z
    simpa only [neg_one_smul] using
      (partialTraceRight_smul (-1 : ℝ) Z)
  simp only [hamp, hptr, neg_neg] at h
  apply (le_div_iff₀ hd).mpr
  unfold gap E
  rw [ptr_amp, ptr_amp]
  dsimp only [Z] at h
  rw [amp_sub_smul, ptr_sub_smul] at h
  exact h

end FilteredChannelConditionalGap
