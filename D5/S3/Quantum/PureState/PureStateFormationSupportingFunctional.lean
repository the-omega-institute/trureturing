/- GID: D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional
   generality: I
   mirror-B: D5/B/S3/Quantum/PureState/PureStateFormationSupportingFunctional
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entanglement of formation has a supporting affine functional at every pure state. -/

import D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation
import D5.S3.Quantum.Matrix.CartesianVariance

/-! A supporting affine functional for the finite-dimensional entanglement of formation.
The entropy uses the natural logarithm, with the logarithm set to zero at zero.
Finite pure ensembles and their costs use `MoreauYosidaFormationSelectiveLoccRefutation`.
Its `E_F` takes values in `ENNReal`: the lower bound is expressed through `ENNReal.ofReal`.
The value of the functional at the pure state is also identified with its real marginal entropy,
so the equality does not lose the sign information discarded by `ENNReal.ofReal`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.PureState.PureStateFormationSupportingFunctional

open _root_.Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation

/-- Every normalized bipartite pure state admits a Hermitian supporting functional for `E_F`.
The first equality gives its real value; the second identifies this value with `E_F`.
The last inequality ranges over all density states, using the nonnegative extended-real codomain.
-/
def claim : Prop := ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
  ∀ (ψ : Fin a × Fin b → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1),
  ∃ W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
    W.IsHermitian ∧
    (W * rankOneDensity ψ).trace.re =
      vonNeumannEntropy (marginalRight (pureDensityState ψ hψ)) ∧
    E_F (pureDensityState ψ hψ) = ENNReal.ofReal (W * rankOneDensity ψ).trace.re ∧
    ∀ σ : DensityState (Fin a × Fin b),
      ENNReal.ofReal (W * CStarMatrix.ofMatrix.symm σ.val).trace.re ≤ E_F σ

private theorem entropy_scalar_lower (r t c : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (ht1 : t ≤ 1) (hc : 0 ≤ c) (hcr : 0 < r → 1 ≤ c * r) :
    -t * Real.log r - (t - r) - c * (t - r) ^ 2 ≤ Real.negMulLog t := by
  by_cases hr0 : r = 0
  · subst r
    have he := Real.negMulLog_nonneg ht ht1
    simp only [Real.log_zero, mul_zero, sub_zero, zero_sub]
    nlinarith [mul_nonneg hc (sq_nonneg t)]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases ht0 : t = 0
  · subst t
    simp only [Real.negMulLog_zero, neg_zero, zero_mul, zero_sub, neg_sq]
    nlinarith [mul_le_mul_of_nonneg_left (hcr hrp) hr]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos htp hrp)) ht
  rw [Real.log_div ht0 hr0] at hl
  have hmul : t * (t / r - 1) = (t - r) + (t - r) ^ 2 / r := by
    field_simp
    ring
  rw [hmul] at hl
  have hi : r⁻¹ ≤ c := (inv_le_iff_one_le_mul₀ hrp).mpr (hcr hrp)
  have hsq := mul_le_mul_of_nonneg_right hi (sq_nonneg (t - r))
  simp only [Real.negMulLog_def]
  rw [div_eq_mul_inv] at hl
  nlinarith

private theorem trace_spectral_pair {n : Type*} [Fintype n] [DecidableEq n]
    {R T : Matrix n n ℂ} (hR : R.IsHermitian) (hT : T.IsHermitian) (f : ℝ → ℝ) :
    (RHLinalg.specMap hR f * T).trace.re =
      ∑ i, ∑ j, f (hR.eigenvalues i) *
        RHLinalg.normSqMatrix
          (star (hR.eigenvectorUnitary : Matrix n n ℂ) *
            (hT.eigenvectorUnitary : Matrix n n ℂ)) i j * hT.eigenvalues j := by
  let U : Matrix n n ℂ := hR.eigenvectorUnitary
  let V : Matrix n n ℂ := hT.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (fun i => (f (hR.eigenvalues i) : ℂ))
  let E : Matrix n n ℂ := diagonal (fun j => (hT.eigenvalues j : ℂ))
  let O := star U * V
  have he : (RHLinalg.specMap hR f * T).trace = (D * O * E * star O).trace := by
    change (U * D * star U * T).trace = _
    conv_lhs => rw [hT.spectral_theorem]
    change (U * D * star U * (V * E * star V)).trace = _
    calc
      _ = (U * (D * star U * V * E * star V)).trace := by congr 1; noncomm_ring
      _ = ((D * star U * V * E * star V) * U).trace := Matrix.trace_mul_comm _ _
      _ = _ := by
        dsimp only [O]
        rw [star_mul, star_star]
        congr 1
        noncomm_ring
  rw [he]
  change (∑ i, (D * O * E * star O) i i).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  change ((f (hR.eigenvalues i) : ℂ) * O i j * hT.eigenvalues j * star (O i j)).re = _
  rw [show (f (hR.eigenvalues i) : ℂ) * O i j * hT.eigenvalues j * star (O i j) =
    ((f (hR.eigenvalues i) * hT.eigenvalues j : ℝ) : ℂ) *
      (O i j * star (O i j)) by push_cast; ring]
  rw [show star (O i j) = starRingEnd ℂ (O i j) from rfl, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    RHLinalg.normSqMatrix, Matrix.of_apply, Complex.normSq_eq_norm_sq]
  dsimp only [O, U, V]
  ring

private theorem entropy_matrix_lower {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : DensityState n) : ∃ c : ℝ, 0 ≤ c ∧
      ∀ τ : DensityState n,
        -(RHLinalg.specMap (density_posSemidef ρ).isHermitian Real.log *
          CStarMatrix.ofMatrix.symm τ.val).trace.re -
          c * RHLinalg.frobSq
            (CStarMatrix.ofMatrix.symm τ.val - CStarMatrix.ofMatrix.symm ρ.val) ≤
        vonNeumannEntropy τ := by
  let R := CStarMatrix.ofMatrix.symm ρ.val
  let hR := (density_posSemidef ρ).isHermitian
  let r := hR.eigenvalues
  let c := ∑ i, (r i)⁻¹
  have hr (i : n) : 0 ≤ r i := (density_posSemidef ρ).eigenvalues_nonneg i
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hr i)
  have hcr (i : n) (hi : 0 < r i) : 1 ≤ c * r i := by
    have hs : (r i)⁻¹ ≤ c :=
      Finset.single_le_sum (fun j _ => inv_nonneg.mpr (hr j)) (Finset.mem_univ i)
    have hm := mul_le_mul_of_nonneg_right hs (hr i)
    rwa [inv_mul_cancel₀ hi.ne'] at hm
  refine ⟨c, hc, ?_⟩
  intro τ
  let T := CStarMatrix.ofMatrix.symm τ.val
  let hT := (density_posSemidef τ).isHermitian
  let t := hT.eigenvalues
  let O : Matrix n n ℂ := star (hR.eigenvectorUnitary : Matrix n n ℂ) *
    (hT.eigenvectorUnitary : Matrix n n ℂ)
  let w := RHLinalg.normSqMatrix O
  have hw : w ∈ doublyStochastic ℝ n :=
    RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
      (mul_mem (Unitary.star_mem hR.eigenvectorUnitary.property) hT.eigenvectorUnitary.property)
  have ht (j : n) : 0 ≤ t j := (density_posSemidef τ).eigenvalues_nonneg j
  have hrs : ∑ i, r i = 1 := by
    have he := RHLinalg.rtrace_eq_sum_eigenvalues hR
    have htr : R.trace = 1 := ρ.property.2
    change RCLike.re R.trace = ∑ i, r i at he
    rw [htr] at he
    simpa only [RCLike.one_re] using he.symm
  have hts : ∑ j, t j = 1 := by
    have he := RHLinalg.rtrace_eq_sum_eigenvalues hT
    have htr : T.trace = 1 := τ.property.2
    change RCLike.re T.trace = ∑ j, t j at he
    rw [htr] at he
    simpa only [RCLike.one_re] using he.symm
  have ht1 (j : n) : t j ≤ 1 := by
    rw [← hts]
    exact Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ j)
  have hrow (f : n → ℝ) : ∑ i, ∑ j, w i j * f i = ∑ i, f i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hw, one_mul]
  have hcol (f : n → ℝ) : ∑ i, ∑ j, w i j * f j = ∑ j, f j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hw, one_mul]
  have hcross : (R * T).trace.re = ∑ i, ∑ j, w i j * (r i * t j) := by
    change RCLike.re (R * T).trace = _
    rw [RHLinalg.re_trace_mul_eq_eigenvalue_bilinear hR hT]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change r i * w i j * t j = _
    ring
  have hquad : ∑ i, ∑ j, w i j * (t j - r i) ^ 2 = RHLinalg.frobSq (T - R) := by
    have hex := RHLinalg.frobSq_add_hermitian hT hR.neg
    have hneg : RHLinalg.frobSq (-R) = RHLinalg.frobSq R := by
      simp only [RHLinalg.frobSq, Matrix.conjTranspose_neg, neg_mul_neg]
    rw [← sub_eq_add_neg, hneg, Matrix.mul_neg, Matrix.trace_neg, map_neg,
      Matrix.trace_mul_comm T R] at hex
    rw [RCLike.re_to_complex] at hex
    rw [RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hT,
      RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hR, hcross] at hex
    calc
      _ = (∑ i, ∑ j, w i j * (t j) ^ 2) -
          2 * (∑ i, ∑ j, w i j * (r i * t j)) +
          (∑ i, ∑ j, w i j * (r i) ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hcol, hrow]; linarith [hex]
  have hlog : (RHLinalg.specMap hR Real.log * T).trace.re =
      ∑ i, ∑ j, w i j * (t j * Real.log (r i)) := by
    rw [trace_spectral_pair hR hT]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change Real.log (r i) * w i j * t j = _
    ring
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left
        (entropy_scalar_lower (r i) (t j) c (hr i) (ht j) (ht1 j) hc (hcr i))
        (nonneg_of_mem_doublyStochastic hw (i := i) (j := j))
  have he : ∑ i, ∑ j, w i j *
      (-t j * Real.log (r i) - (t j - r i) - c * (t j - r i) ^ 2) =
      -(RHLinalg.specMap hR Real.log * T).trace.re - c * RHLinalg.frobSq (T - R) := by
    calc
      _ = -(∑ i, ∑ j, w i j * (t j * Real.log (r i))) -
          ((∑ i, ∑ j, w i j * t j) - (∑ i, ∑ j, w i j * r i)) -
          c * (∑ i, ∑ j, w i j * (t j - r i) ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [← hlog, hcol, hrow, hts, hrs, hquad]; ring
  rw [he, hcol] at hs
  exact hs.trans_eq (entropy_eq_sum τ).symm

private theorem partial_trace_hs_bound {a b : ℕ}
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    RHLinalg.frobSq (partialTraceRight X) ≤ (b : ℝ) * RHLinalg.frobSq X := by
  have hentry (i j : Fin a) : Complex.normSq (∑ k, X (j, k) (i, k)) ≤
      (b : ℝ) * ∑ k, Complex.normSq (X (j, k) (i, k)) := by
    have hre := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun k : Fin b => (X (j, k) (i, k)).re)
    have him := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun k : Fin b => (X (j, k) (i, k)).im)
    simpa only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
      Finset.sum_add_distrib, mul_add, Finset.card_univ, Fintype.card_fin, pow_two]
      using add_le_add hre him
  rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
  change (∑ i, ∑ j, Complex.normSq (∑ k, X (j, k) (i, k))) ≤ _
  calc
    _ ≤ ∑ i, ∑ j, (b : ℝ) * ∑ k, Complex.normSq (X (j, k) (i, k)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = (b : ℝ) * ∑ i, ∑ k, ∑ j, Complex.normSq (X (j, k) (i, k)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ ≤ (b : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l, Complex.normSq (X (j, l) (i, k)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg b)
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum (f := fun l => Complex.normSq (X (j, l) (i, k)))
        (fun l _ => Complex.normSq_nonneg _)
        (Finset.mem_univ k)
    _ = _ := by
      congr 1
      simp [RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type,
        Complex.normSq_apply]

private theorem lifted_trace_pair {a b : ℕ} (L : Matrix (Fin a) (Fin a) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (Matrix.kronecker L (1 : Matrix (Fin b) (Fin b) ℂ) * X).trace =
      (L * partialTraceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply,
    partialTraceRight,
    Finset.mul_sum, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (k : Fin b) (j : Fin a) => L i j * X (j, k) (i, k))

private theorem pure_support_bound {a b : ℕ}
    (ψ : Fin a × Fin b → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∃ W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      W.IsHermitian ∧
      (W * rankOneDensity ψ).trace.re =
        vonNeumannEntropy (marginalRight (pureDensityState ψ hψ)) ∧
      ∀ (φ : Fin a × Fin b → ℂ) (hφ : star φ ⬝ᵥ φ = 1),
        (W * rankOneDensity φ).trace.re ≤
          vonNeumannEntropy (marginalRight (pureDensityState φ hφ)) := by
  let ρ := marginalRight (pureDensityState ψ hψ)
  let R := CStarMatrix.ofMatrix.symm ρ.val
  let hR := (density_posSemidef ρ).isHermitian
  let L := RHLinalg.specMap hR Real.log
  let P := rankOneDensity ψ
  obtain ⟨c, hc, hbound⟩ := entropy_matrix_lower ρ
  let K : ℝ := 2 * b * c
  let W := -Matrix.kronecker L (1 : Matrix (Fin b) (Fin b) ℂ) -
    (K : ℂ) • (1 - P)
  have hP : P.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star ψ).isHermitian
  have hPid : P * P = P := (pure_state_handshake ψ hψ 0).1
  have hPtr : P.trace = 1 := (pureDensityState ψ hψ).property.2
  have hL : L.IsHermitian := RHLinalg.specMap_isHermitian hR Real.log
  have hW : W.IsHermitian :=
    (isHermitian_kronecker hL isHermitian_one).neg.sub
      ((isHermitian_one.sub hP).smul (by simp [IsSelfAdjoint]))
  have hself : -(L * R).trace.re = vonNeumannEntropy ρ := by
    have hLR : L * R = RHLinalg.specMap hR (Real.log * id) := by
      rw [RHLinalg.specMap_mul, RHLinalg.specMap_id]
    rw [hLR]
    have ht := RHLinalg.rtrace_specMap hR (Real.log * id)
    change (RHLinalg.specMap hR (Real.log * id)).trace.re = _ at ht
    rw [ht, entropy_eq_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply, id_eq, Real.negMulLog_def]
    ring
  have htrace (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.trace = 1) :
      (W * X).trace.re = -(L * partialTraceRight X).trace.re -
        K * (1 - (P * X).trace.re) := by
    dsimp only [W]
    rw [sub_mul, neg_mul, Matrix.smul_mul, sub_mul, one_mul,
      Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_sub,
      lifted_trace_pair, hX]
    simp only [Complex.sub_re, Complex.neg_re, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.one_re]
  refine ⟨W, hW, ?_, ?_⟩
  · rw [htrace P hPtr, hPid, hPtr, Complex.one_re]
    change -(L * R).trace.re - K * (1 - 1) = _
    rw [sub_self, mul_zero, sub_zero]
    exact hself
  · intro φ hφ
    let Q := rankOneDensity φ
    have hQ : Q.IsHermitian := (Matrix.posSemidef_vecMulVec_self_star φ).isHermitian
    have hQid : Q * Q = Q := (pure_state_handshake φ hφ 0).1
    have hQtr : Q.trace = 1 := (pureDensityState φ hφ).property.2
    have hPQ : RHLinalg.frobSq (Q - P) = 2 * (1 - (P * Q).trace.re) := by
      have he := RHLinalg.frobSq_add_hermitian hQ hP.neg
      have hn : RHLinalg.frobSq (-P) = RHLinalg.frobSq P := by
        simp only [RHLinalg.frobSq, Matrix.conjTranspose_neg, neg_mul_neg]
      rw [← sub_eq_add_neg, hn, Matrix.mul_neg, Matrix.trace_neg,
        map_neg, Matrix.trace_mul_comm Q P] at he
      have hpure : RHLinalg.frobSq P = 1 := by
        rw [RHLinalg.frobSq, hP.eq, hPid, hPtr, RCLike.one_re]
      have hqpure : RHLinalg.frobSq Q = 1 := by
        rw [RHLinalg.frobSq, hQ.eq, hQid, hQtr, RCLike.one_re]
      rw [hpure, hqpure] at he
      rw [RCLike.re_to_complex] at he
      linarith
    have hdiff : partialTraceRight Q - R = partialTraceRight (Q - P) := by
      ext i j
      change (∑ k, Q (i, k) (j, k)) - (∑ k, P (i, k) (j, k)) =
        ∑ k, (Q (i, k) (j, k) - P (i, k) (j, k))
      rw [Finset.sum_sub_distrib]
    have hh := mul_le_mul_of_nonneg_left (partial_trace_hs_bound (Q - P)) hc
    rw [hPQ] at hh
    have hm := hbound (marginalRight (pureDensityState φ hφ))
    change -(L * partialTraceRight Q).trace.re -
      c * RHLinalg.frobSq (partialTraceRight Q - R) ≤ _ at hm
    rw [hdiff] at hm
    rw [htrace Q hQtr]
    dsimp only [K]
    exact (sub_le_sub_left (hh.trans_eq (by ring)) _).trans hm

/-- The entanglement of formation has a supporting affine functional at every pure state. -/
theorem result : claim := by
  intro a b _ _ ψ hψ
  obtain ⟨W, hW, heq, hpure⟩ := pure_support_bound ψ hψ
  have hunit (M : Pure a b) :
      star (fun x : Fin a × Fin b => M.val x.1 x.2) ⬝ᵥ
        (fun x : Fin a × Fin b => M.val x.1 x.2) = 1 := by
    simpa [dotProduct, Fintype.sum_prod_type, Complex.mul_conj, mul_comm, mass]
      using congrArg (fun r : ℝ => (r : ℂ)) M.property
  have hroof (σ : DensityState (Fin a × Fin b)) :
      ENNReal.ofReal (W * CStarMatrix.ofMatrix.symm σ.val).trace.re ≤ E_F σ := by
    apply le_iInf
    intro N
    apply le_iInf
    intro e
    apply ENNReal.ofReal_le_ofReal
    have havg : (W * CStarMatrix.ofMatrix.symm σ.val).trace.re =
        ∑ i, e.p i * (W * rankOneDensity
          (fun x : Fin a × Fin b => (e.ψ i).val x.1 x.2)).trace.re := by
      rw [← e.average, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_smul, Matrix.trace_smul]
      simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    rw [havg]
    unfold cost
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (e.p_nonneg i)
    exact hpure (fun x => (e.ψ i).val x.1 x.2) (hunit (e.ψ i))
  let M : Pure a b := ⟨fun i j => ψ (i, j), by
    have h := congrArg Complex.re hψ
    simpa [dotProduct, Fintype.sum_prod_type, mass, Complex.star_def,
      Complex.mul_re, Complex.normSq_apply] using h⟩
  let e : Ensemble 1 (pureDensityState ψ hψ) :=
    { p := fun _ => 1
      p_nonneg := fun _ => zero_le_one
      p_sum := by simp
      ψ := fun _ => M
      average := by
        rw [Fin.sum_univ_one, Complex.ofReal_one, one_smul]
        rfl }
  have hcost : cost e = vonNeumannEntropy (marginalRight (pureDensityState ψ hψ)) := by
    change (∑ _ : Fin 1, (1 : ℝ) *
      vonNeumannEntropy (marginalRight (pureDensityState ψ hψ))) = _
    rw [Fin.sum_univ_one, one_mul]
  have hupper : E_F (pureDensityState ψ hψ) ≤
      ENNReal.ofReal (W * rankOneDensity ψ).trace.re := by
    calc
      E_F (pureDensityState ψ hψ) ≤ ENNReal.ofReal (cost e) :=
        iInf_le_of_le 1 (iInf_le_of_le e le_rfl)
      _ = ENNReal.ofReal (W * rankOneDensity ψ).trace.re := by rw [hcost, heq]
  exact ⟨W, hW, heq, le_antisymm hupper (hroof (pureDensityState ψ hψ)), hroof⟩

#print axioms result

end D5.S3.Quantum.PureState.PureStateFormationSupportingFunctional
