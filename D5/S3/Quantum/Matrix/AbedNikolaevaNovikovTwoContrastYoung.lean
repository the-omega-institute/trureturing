/- GID: D5/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/AbedNikolaevaNovikovTwoContrastYoung
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact two-contrast Young envelope in every positive even matrix dimension. -/

/-
admission_basis: open-problem-resolution (#22727; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23032.
Direct frozen dependencies (declaration identities from the existing report):
The scoped report is refreshed in Stage B before freezing.
  D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef
    Lean name: RHLinalg.trace_mul_nonneg_of_posSemidef
    statement_id: sha256:d0be9623184a0aa6b2753f04a89d828122fe7292de10124c81506a795f6decf6
  D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    statement_id: sha256:accd04d85421c0847456ddb52626f272e79ea98e568dcf9dfeddc5035a1f2013
  D5/S3/Quantum/Matrix/AlternativeMeanLinearization.diagonal_real_spectrum (private owner)
    statement_id: sha256:37a7087536fd497ffdbec51f763b6a1e7ebb508fe77c11ba0f54e36fff6d093e
Dependency labels: F1 = trace positivity above; F2 = equal-Gram unitary above; F3 = diagonal spectrum above.
Per-declaration proof_shape, direct frozen dependencies and consumers:
  contrast: proof_shape: not-applicable(definition); escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: blockDiag_contrast, envelope_attained, prescribed_gram_orbit_bound, values, values_upper_bound
  values: proof_shape: not-applicable(definition); escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: claim, result, values_upper_bound
  claim: proof_shape: not-applicable(definition); escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: result (type)
  trace_interval_comparison: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F1;
    consumers: unitary_trace_interval_comparison
  envelope_denominator_pos: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained, prescribed_gram_orbit_bound
  contrast_coefficient_identity: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained, prescribed_gram_orbit_bound
  exists_polar_abs: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F2;
    consumers: gram_is_unitary_conjugate, weighted_young_polar
  gram_is_unitary_conjugate: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F2;
    consumers: values_upper_bound
  weighted_young_polar: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F2, F1;
    consumers: values_upper_bound
  spectrum_interval: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: prescribed_gram_orbit_bound, square_spectral_bounds
  posDef_spectral_min: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: prescribed_gram_orbit_bound
  square_spectral_bounds: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: prescribed_gram_orbit_bound
  unitary_trace_interval_comparison: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F1;
    consumers: prescribed_gram_orbit_bound
  prescribed_gram_orbit_bound: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F1;
    consumers: values_upper_bound
  values_upper_bound: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F2, F1;
    consumers: result
  blockDiag: proof_shape: not-applicable(definition); escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: blockDiag_contrast, blockDiag_diagonal, blockDiag_mul, blockDiag_nonneg, blockDiag_posdef, blockDiag_trace, envelope_attained
  blockDiag_diagonal: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: blockDiag_contrast, blockDiag_mul, blockDiag_nonneg, blockDiag_posdef, blockDiag_trace
  blockDiag_mul: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained
  blockDiag_trace: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained
  blockDiag_nonneg: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained
  blockDiag_posdef: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: none;
    consumers: envelope_attained
  blockDiag_contrast: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F3;
    consumers: envelope_attained
  envelope_attained: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F3;
    consumers: result
  result: proof_shape: bind-only; escape_witness: none;
    direct_frozen_dependencies: F2, F1, F3;
    consumers: #22727 nominated endpoint
The contrast and value-set formulas retain the expressions of #22727.
The modulus is Mathlib CFC.abs, and diagonal spectra reuse the existing owner.
-/


import D5.S3.Weil.ZetaLinear.RankTrace
import D5.S3.Quantum.Algebra.GramUnitaryExtension
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

open _root_.Matrix
open scoped ComplexOrder MatrixOrder

/-- The source's OMC(T) = (max σ(T) - min σ(T))/(max σ(T) + min σ(T)).
Only nonzero positive semidefinite matrices are used in the claim. -/
def contrast {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (sSup (spectrum ℝ T) - sInf (spectrum ℝ T)) /
    (sSup (spectrum ℝ T) + sInf (spectrum ℝ T))

/-- Item 8's set of relative violations. Mathlib's CFC.abs is the modulus
sqrt(Xᴴ * X); φρ(X) is literally (ρ * X).trace. Real parts select the real
values of φ on positive semidefinite matrices. The source imposes no trace-one
normalization on ρ. -/
def values (n : ℕ) (δ δ' : ℝ) : Set ℝ :=
  {v | ∃ (ρ A B : Matrix (Fin n) (Fin n) ℂ),
    ρ.PosDef ∧ A ≠ 0 ∧ B ≠ 0 ∧
    contrast ρ = δ ∧ contrast (CFC.abs A) = δ' ∧ contrast (CFC.abs B) = δ' ∧
    0 < ((ρ * (Aᴴ * A)).trace.re + (ρ * (Bᴴ * B)).trace.re) / 2 ∧
    v = ((ρ * CFC.abs (A * Bᴴ)).trace.re -
          ((ρ * (Aᴴ * A)).trace.re + (ρ * (Bᴴ * B)).trace.re) / 2) /
        (((ρ * (Aᴴ * A)).trace.re + (ρ * (Bᴴ * B)).trace.re) / 2)}

/-- Conjecture 11.1, final clause: Proposition 5.22 is the item-8 two-contrast
envelope in every positive even dimension, including δ'=0 and δ'=1.
Nonemptiness and boundedness explicitly give the real supremum its intended
meaning; neither is an extra hypothesis. -/
def claim : Prop :=
  ∀ (r : ℕ), 1 ≤ r →
    ∀ (δ : ℝ), 0 ≤ δ → δ < 1 →
      ∀ (δ' : ℝ), 0 ≤ δ' → δ' ≤ 1 →
        (values (2 * r) δ δ').Nonempty ∧
        BddAbove (values (2 * r) δ δ') ∧
        sSup (values (2 * r) δ δ') = 4 * δ * δ' / (1 + δ' ^ 2 - 2 * δ * δ')

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private diagonal_real_spectrum from D5.S3.Quantum.Matrix.AlternativeMeanLinearization

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sharp trace comparison, needing only a shared trace and spectral intervals. -/
private theorem trace_interval_comparison
    (R H K : Matrix ι ι ℂ) (m M u v : ℝ)
    (hm : 0 ≤ m) (hM : 0 ≤ M) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hRlo : m • (1 : Matrix ι ι ℂ) ≤ R)
    (hRhi : R ≤ M • (1 : Matrix ι ι ℂ))
    (hHlo : u • (1 : Matrix ι ι ℂ) ≤ H)
    (hHhi : H ≤ v • (1 : Matrix ι ι ℂ))
    (hKlo : u • (1 : Matrix ι ι ℂ) ≤ K)
    (hKhi : K ≤ v • (1 : Matrix ι ι ℂ))
    (htr : K.trace.re = H.trace.re) :
    (M * u + m * v) * (R * K).trace.re ≤
      (M * v + m * u) * (R * H).trace.re := by
  have g1 := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hRlo) (Matrix.le_iff.mp hKhi)
  have g2 := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hRhi) (Matrix.le_iff.mp hKlo)
  have g3 := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hRlo) (Matrix.le_iff.mp hHlo)
  have g4 := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hRhi) (Matrix.le_iff.mp hHhi)
  simp only [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_smul,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
    map_sub, RCLike.smul_re] at g1 g2 g3 g4
  have htr' : RCLike.re K.trace = RCLike.re H.trace := htr
  rw [htr'] at g1 g2
  change (M*u+m*v) * RCLike.re (R*K).trace ≤ (M*v+m*u) * RCLike.re (R*H).trace
  have a := mul_nonneg (mul_nonneg hM hu) g1
  have b := mul_nonneg (mul_nonneg hm hv) g2
  have c := mul_nonneg (mul_nonneg hM hv) g3
  have d := mul_nonneg (mul_nonneg hm hu) g4
  nlinarith only [a,b,c,d]

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

private theorem envelope_denominator_pos (δ η : ℝ) (hδ : δ < 1)
    (hη : 0 ≤ η) :
    0 < 1 + η ^ 2 - 2 * δ * η := by
  by_cases hz : η = 0
  · simp [hz]
  · have hp : 0 < η := lt_of_le_of_ne hη (Ne.symm hz)
    have h := mul_pos hp (sub_pos.mpr hδ)
    nlinarith only [sq_nonneg (1 - η), h]

private theorem contrast_coefficient_identity (m M a b δ η : ℝ)
    (hm : 0 < m) (hM : 0 < M) (ha : 0 ≤ a) (hb : 0 < b)
    (hδ : δ = (M - m) / (M + m)) (hη : η = (b - a) / (b + a)) :
    (M * b ^ 2 + m * a ^ 2) * (1 + η ^ 2 - 2 * δ * η) =
      (M * a ^ 2 + m * b ^ 2) * (1 + η ^ 2 + 2 * δ * η) := by
  rw [hδ, hη]
  field_simp [ne_of_gt (add_pos hM hm), ne_of_gt (add_pos_of_pos_of_nonneg hb ha)]
  <;> ring

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
variable {n : ℕ}

private theorem exists_polar_abs (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : unitaryGroup (Fin n) ℂ, A = U.val * CFC.abs A := by
  apply D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    A (CFC.abs A)
  simp only [(CFC.abs_nonneg A).posSemidef.isHermitian.eq, CFC.abs_mul_abs,
    Matrix.star_eq_conjTranspose]

private theorem gram_is_unitary_conjugate (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : unitaryGroup (Fin n) ℂ) :
    ∃ W : unitaryGroup (Fin n) ℂ,
      Q.valᴴ * (A * Aᴴ) * Q.val = W.val * (Aᴴ * A) * W.valᴴ := by
  obtain ⟨V, hV⟩ := exists_polar_abs A
  have hAbs : (CFC.abs A)ᴴ = CFC.abs A := (CFC.abs_nonneg A).posSemidef.isHermitian.eq
  have hGram : A * Aᴴ = V.val * (Aᴴ * A) * V.valᴴ := by
    calc
      A * Aᴴ = (V.val * CFC.abs A) * (V.val * CFC.abs A)ᴴ := congrArg (fun X => X * Xᴴ) hV
      _ = V.val * (CFC.abs A * CFC.abs A) * V.valᴴ := by
        rw [conjTranspose_mul, hAbs]
        noncomm_ring
      _ = V.val * (Aᴴ * A) * V.valᴴ := by
        rw [CFC.abs_mul_abs]
        rfl
  refine ⟨star Q * V, ?_⟩
  change Q.valᴴ * (A * Aᴴ) * Q.val =
    (Q.valᴴ * V.val) * (Aᴴ * A) * (Q.valᴴ * V.val)ᴴ
  rw [hGram, conjTranspose_mul, conjTranspose_conjTranspose]
  noncomm_ring

private theorem weighted_young_polar (R A B : Matrix (Fin n) (Fin n) ℂ)
    (hR : R.PosSemidef) :
    ∃ U : unitaryGroup (Fin n) ℂ,
      2 * (R * CFC.abs (A * Bᴴ)).trace.re ≤
        (R * (U.valᴴ * (A * Aᴴ) * U.val)).trace.re + (R * (B * Bᴴ)).trace.re := by
  obtain ⟨U, hU⟩ := exists_polar_abs (A * Bᴴ)
  have hc : U.valᴴ * (A * Bᴴ) = CFC.abs (A * Bᴴ) := by
    calc
      U.valᴴ * (A * Bᴴ) = U.valᴴ * (U.val * CFC.abs (A * Bᴴ)) :=
        congrArg (fun X => U.valᴴ * X) hU
      _ = CFC.abs (A * Bᴴ) := by
        simp only [← Matrix.mul_assoc, ← star_eq_conjTranspose, U.prop.1, Matrix.one_mul]
  have hcs : B * Aᴴ * U.val = CFC.abs (A * Bᴴ) := by
    have h := congrArg Matrix.conjTranspose hc
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose,
      (CFC.abs_nonneg (A * Bᴴ)).posSemidef.isHermitian.eq, Matrix.mul_assoc] using h
  let X := Aᴴ * U.val - Bᴴ
  have hsq : Xᴴ * X = U.valᴴ * (A * Aᴴ) * U.val + B * Bᴴ -
      CFC.abs (A * Bᴴ) - CFC.abs (A * Bᴴ) := by
    calc
      Xᴴ * X = U.valᴴ * (A * Aᴴ) * U.val + B * Bᴴ -
        U.valᴴ * (A * Bᴴ) - B * Aᴴ * U.val := by
        dsimp only [X]
        simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose]
        noncomm_ring
      _ = _ := by rw [hc, hcs]
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef hR
    (Matrix.posSemidef_conjTranspose_mul_self X)
  rw [hsq] at hp
  simp only [mul_add, mul_sub, Matrix.trace_add, Matrix.trace_sub, map_add, map_sub] at hp
  refine ⟨U, ?_⟩
  change 0 ≤ ((R * (U.valᴴ * (A * Aᴴ) * U.val)).trace.re +
    (R * (B * Bᴴ)).trace.re - (R * CFC.abs (A * Bᴴ)).trace.re -
    (R * CFC.abs (A * Bᴴ)).trace.re) at hp
  linarith only [hp]

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung


namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ} [Nonempty (Fin n)]

private theorem spectrum_interval (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : 0 ≤ T) (hne : T ≠ 0) :
    0 ≤ sInf (spectrum ℝ T) ∧ 0 < sSup (spectrum ℝ T) ∧
    sInf (spectrum ℝ T) ≤ sSup (spectrum ℝ T) ∧
    sInf (spectrum ℝ T) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ T ∧
    T ≤ sSup (spectrum ℝ T) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hs := hT.posSemidef.isHermitian.spectrum_real_eq_range_eigenvalues
  have hc : IsCompact (spectrum ℝ T) := by
    exact ContinuousFunctionalCalculus.isCompact_spectrum T
  have he : (spectrum ℝ T).Nonempty := by
    rw [hs]
    exact Set.range_nonempty _
  have hlo : sInf (spectrum ℝ T) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ T := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (algebraMap_le_iff_le_spectrum hT.isSelfAdjoint).mpr
        (fun x hx => csInf_le hc.bddBelow hx)
  have hhi : T ≤ sSup (spectrum ℝ T) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (le_algebraMap_iff_spectrum_le hT.isSelfAdjoint).mpr
        (fun x hx => le_csSup hc.bddAbove hx)
  have hmin : 0 ≤ sInf (spectrum ℝ T) := by
    obtain ⟨i, hi⟩ := hs ▸ hc.sInf_mem he
    rw [hs, ← hi]
    exact hT.posSemidef.eigenvalues_nonneg i
  have hmax : 0 < sSup (spectrum ℝ T) := by
    by_contra h
    have hz : T ≤ 0 := hhi.trans (by
      simpa only [zero_smul] using
        smul_le_smul_of_nonneg_right (le_of_not_gt h) (show (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1 from zero_le_one))
    exact hne (le_antisymm hz hT)
  exact ⟨hmin, hmax, csInf_le hc.bddBelow (hc.sSup_mem he), hlo, hhi⟩

private theorem posDef_spectral_min (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosDef) :
    0 < sInf (spectrum ℝ R) := by
  have hs := hR.isHermitian.spectrum_real_eq_range_eigenvalues
  have hc : IsCompact (spectrum ℝ R) := by
    exact ContinuousFunctionalCalculus.isCompact_spectrum R
  have he : (spectrum ℝ R).Nonempty := by
    rw [hs]
    exact Set.range_nonempty _
  obtain ⟨i, hi⟩ := hs ▸ hc.sInf_mem he
  rw [hs, ← hi]
  exact hR.eigenvalues_pos i

private theorem square_spectral_bounds (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : 0 ≤ T) (hne : T ≠ 0) :
    (sInf (spectrum ℝ T)) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ T * T ∧
    T * T ≤ (sSup (spectrum ℝ T)) ^ 2 • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨hmin, hmax, _, hlo, hhi⟩ := spectrum_interval T hT hne
  have hc : IsCompact (spectrum ℝ T) := by
    exact ContinuousFunctionalCalculus.isCompact_spectrum T
  constructor
  · rw [← sq, ← cfc_pow_id (R := ℝ) T 2 hT.isSelfAdjoint]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (algebraMap_le_cfc_iff (fun x : ℝ => x ^ 2)
        ((sInf (spectrum ℝ T)) ^ 2) T (by fun_prop) hT.isSelfAdjoint).mpr
        (fun x hx => pow_le_pow_left₀ hmin (csInf_le hc.bddBelow hx) 2)
  · rw [← sq, ← cfc_pow_id (R := ℝ) T 2 hT.isSelfAdjoint]
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (cfc_le_algebraMap_iff (fun x : ℝ => x ^ 2)
        ((sSup (spectrum ℝ T)) ^ 2) T (by fun_prop) hT.isSelfAdjoint).mpr
        (fun x hx => pow_le_pow_left₀
          (hmin.trans (csInf_le hc.bddBelow hx)) (le_csSup hc.bddAbove hx) 2)

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung


namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ} [Nonempty (Fin n)]

omit [Nonempty (Fin n)] in
private theorem unitary_trace_interval_comparison
    (R H : Matrix (Fin n) (Fin n) ℂ) (W : unitaryGroup (Fin n) ℂ)
    (m M u v : ℝ) (hm : 0 ≤ m) (hM : 0 ≤ M) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hRlo : m • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ R)
    (hRhi : R ≤ M • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hHlo : u • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ H)
    (hHhi : H ≤ v • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (M*u + m*v) * (R * (W.val * H * W.valᴴ)).trace.re ≤
      (M*v + m*u) * (R * H).trace.re := by
  have hlo := (Matrix.le_iff.mp hHlo).mul_mul_conjTranspose_same W.val
  have hhi := (Matrix.le_iff.mp hHhi).mul_mul_conjTranspose_same W.val
  have hKlo : u • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ W.val * H * W.valᴴ := by
    apply Matrix.le_iff.mpr
    simpa only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
      Matrix.mul_one, Matrix.one_mul, ← star_eq_conjTranspose, W.prop.2] using hlo
  have hKhi : W.val * H * W.valᴴ ≤ v • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    apply Matrix.le_iff.mpr
    simpa only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
      Matrix.mul_one, Matrix.one_mul, ← star_eq_conjTranspose, W.prop.2] using hhi
  apply trace_interval_comparison R H (W.val * H * W.valᴴ) m M u v hm hM hu hv
    hRlo hRhi hHlo hHhi hKlo hKhi
  rw [Matrix.trace_mul_cycle]
  simp only [← star_eq_conjTranspose, W.prop.1, Matrix.one_mul]

private theorem prescribed_gram_orbit_bound
    (R A : Matrix (Fin n) (Fin n) ℂ) (W : unitaryGroup (Fin n) ℂ)
    (δ η : ℝ) (hR : R.PosDef) (hA : A ≠ 0)
    (hδ : contrast R = δ) (hη : contrast (CFC.abs A) = η)
    (hd : δ < 1) (he : 0 ≤ η) (he1 : η ≤ 1) :
    (R * (W.val * (Aᴴ * A) * W.valᴴ)).trace.re ≤
      (1 + 4*δ*η/(1+η^2-2*δ*η)) * (R * (Aᴴ * A)).trace.re := by
  let m := sInf (spectrum ℝ R)
  let M := sSup (spectrum ℝ R)
  let a := sInf (spectrum ℝ (CFC.abs A))
  let b := sSup (spectrum ℝ (CFC.abs A))
  have hm : 0 < m := posDef_spectral_min R hR
  obtain ⟨_, hM, _, hRlo, hRhi⟩ :=
    spectrum_interval R hR.posSemidef.nonneg hR.isUnit.ne_zero
  have hAbsne : CFC.abs A ≠ 0 := by simpa only [ne_eq, CFC.abs_eq_zero_iff] using hA
  obtain ⟨ha, hb, _, _, _⟩ := spectrum_interval (CFC.abs A) (CFC.abs_nonneg A) hAbsne
  obtain ⟨hHlo, hHhi⟩ := square_spectral_bounds (CFC.abs A) (CFC.abs_nonneg A) hAbsne
  rw [CFC.abs_mul_abs] at hHlo hHhi
  have hc := unitary_trace_interval_comparison R (Aᴴ*A) W m M (a^2) (b^2)
    hm.le hM.le (sq_nonneg a) (sq_nonneg b) hRlo hRhi hHlo hHhi
  have hδ' : δ = (M-m)/(M+m) := hδ.symm
  have hη' : η = (b-a)/(b+a) := hη.symm
  have hi := contrast_coefficient_identity m M a b δ η hm hM ha hb hδ' hη'
  let D := 1+η^2-2*δ*η
  let q := M*a^2+m*b^2
  let p := M*b^2+m*a^2
  let C := 1+4*δ*η/D
  have hD : 0 < D := envelope_denominator_pos δ η hd he
  have hq : 0 < q := add_pos_of_nonneg_of_pos
    (mul_nonneg hM.le (sq_nonneg a)) (mul_pos hm (sq_pos_of_pos hb))
  have hi' : p*D = q*(D+4*δ*η) := by
    dsimp only [p,q,D]
    nlinarith only [hi]
  have hp : p = C*q := by
    change p = (1+4*δ*η/D)*q
    field_simp [hD.ne']
    nlinarith only [hi']
  change q * (R * (W.val * (Aᴴ * A) * W.valᴴ)).trace.re ≤ p * (R * (Aᴴ * A)).trace.re at hc
  change (R * (W.val * (Aᴴ * A) * W.valᴴ)).trace.re ≤ C * (R * (Aᴴ * A)).trace.re
  apply (mul_le_mul_iff_right₀ hq).mp
  calc
    q * (R * (W.val * (Aᴴ * A) * W.valᴴ)).trace.re ≤ p * (R * (Aᴴ * A)).trace.re := hc
    _ = q * (C * (R * (Aᴴ * A)).trace.re) := by rw [hp]; ring

private theorem values_upper_bound (δ η : ℝ) (hd : δ < 1)
    (he : 0 ≤ η) (he1 : η ≤ 1) :
    ∀ v ∈ values n δ η, v ≤ 4*δ*η/(1+η^2-2*δ*η) := by
  intro v hv
  obtain ⟨R,A,B,hR,hA,hB,hδ,hηA,hηB,hN,hv⟩ := hv
  obtain ⟨U,hYoung⟩ := weighted_young_polar R A B hR.posSemidef
  obtain ⟨WA,hWA⟩ := gram_is_unitary_conjugate A U
  obtain ⟨WB,hWB⟩ := gram_is_unitary_conjugate B (1 : unitaryGroup (Fin n) ℂ)
  have hAub := prescribed_gram_orbit_bound R A WA δ η hR hA hδ hηA hd he he1
  have hBub := prescribed_gram_orbit_bound R B WB δ η hR hB hδ hηB hd he he1
  rw [← hWA] at hAub
  have hBB : B*Bᴴ = WB.val*(Bᴴ*B)*WB.valᴴ := by simpa using hWB
  rw [← hBB] at hBub
  have hL : (R * CFC.abs (A*Bᴴ)).trace.re ≤
      (1+4*δ*η/(1+η^2-2*δ*η)) *
        (((R*(Aᴴ*A)).trace.re+(R*(Bᴴ*B)).trace.re)/2) := by
    nlinarith only [hYoung,hAub,hBub]
  rw [hv]
  apply (div_le_iff₀ hN).mpr
  nlinarith only [hL]

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung


namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private def blockDiag (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r))
    (a b : ℝ) : Matrix (Fin (2*r)) (Fin (2*r)) ℂ :=
  (fromBlocks ((a : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) 0 0
    ((b : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ))).submatrix e e

private theorem blockDiag_diagonal (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r)) (a b : ℝ) :
    blockDiag r e a b = diagonal
      (fun i => ((Sum.elim (fun _ : Fin r => a) (fun _ : Fin r => b) (e i) : ℝ) : ℂ)) := by
  simp only [blockDiag, Matrix.smul_one_eq_diagonal, Matrix.fromBlocks_diagonal,
    Matrix.submatrix_diagonal_equiv]
  congr 1 <;> funext i <;> dsimp only [Function.comp_def] <;> cases e i <;> rfl

private theorem blockDiag_mul (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r))
    (a b c d : ℝ) :
    blockDiag r e a b * blockDiag r e c d = blockDiag r e (a*c) (b*d) := by
  simp only [blockDiag_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  cases e i <;> simp

private theorem blockDiag_trace (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r)) (a b : ℝ) :
    (blockDiag r e a b).trace.re = (r : ℝ) * (a+b) := by
  rw [blockDiag_diagonal, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [e.sum_comp]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem blockDiag_nonneg (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ blockDiag r e a b := by
  rw [blockDiag_diagonal]
  apply Matrix.PosSemidef.nonneg
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  rcases h : e i with j | j
  · simpa only [h, Sum.elim_inl] using (Complex.zero_le_real.mpr ha)
  · simpa only [h, Sum.elim_inr] using (Complex.zero_le_real.mpr hb)

private theorem blockDiag_posdef (r : ℕ) (e : Fin (2*r) ≃ (Fin r ⊕ Fin r))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (blockDiag r e a b).PosDef := by
  rw [blockDiag_diagonal]
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  rcases h : e i with j | j
  · simpa only [h, Sum.elim_inl] using (Complex.zero_lt_real.mpr ha)
  · simpa only [h, Sum.elim_inr] using (Complex.zero_lt_real.mpr hb)

private theorem blockDiag_contrast (r : ℕ) [Nonempty (Fin r)]
    (e : Fin (2*r) ≃ (Fin r ⊕ Fin r)) (a b : ℝ) :
    contrast (blockDiag r e a b) = (max a b-min a b)/(max a b+min a b) := by
  rw [blockDiag_diagonal, contrast, diagonal_real_spectrum]
  have hr : Set.range (fun i => Sum.elim (fun _ : Fin r => a) (fun _ : Fin r => b) (e i)) =
      {a,b} := by
    change Set.range ((Sum.elim (fun _ : Fin r => a) (fun _ : Fin r => b)) ∘ e) = _
    simp only [EquivLike.range_comp, Set.Sum.elim_range, Set.range_const, Set.singleton_union]
  rw [hr, csSup_pair, csInf_pair]

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung

namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem envelope_attained (r : ℕ) (hr : 1 ≤ r)
    (δ η : ℝ) (hd0 : 0 ≤ δ) (hd1 : δ < 1) (he0 : 0 ≤ η) (he1 : η ≤ 1) :
    4*δ*η/(1+η^2-2*δ*η) ∈ values (2*r) δ η := by
  have hrpos : 0 < r := by exact Nat.zero_lt_of_lt hr
  letI : NeZero r := ⟨by omega⟩
  let e : Fin (2*r) ≃ (Fin r ⊕ Fin r) :=
    (finCongr (show 2*r=r+r by omega)).trans finSumFinEquiv.symm
  let k : ℝ := (1+δ)/(1-δ)
  let ell : ℝ := (1-η)/(1+η)
  have hkpos : 0 < k := div_pos (by linarith) (by linarith)
  have hk1 : 1 ≤ k := (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr (by linarith)
  have hell0 : 0 ≤ ell := div_nonneg (by linarith) (by linarith)
  have hell1 : ell ≤ 1 := (div_le_iff₀ (by linarith : 0 < 1+η)).mpr (by linarith)
  have hdcalc : (k-1)/(k+1) = δ := by
    dsimp only [k]
    field_simp [ne_of_gt (sub_pos.mpr hd1)]
    <;> ring
  have hecalc : (1-ell)/(1+ell) = η := by
    dsimp only [ell]
    field_simp [ne_of_gt (by linarith : 0 < 1+η)]
    <;> ring
  let R := blockDiag r e k 1
  let A : Matrix (Fin (2*r)) (Fin (2*r)) ℂ :=
    (fromBlocks (0 : Matrix (Fin r) (Fin r) ℂ) 1 ((ell : ℂ) • 1) 0).submatrix e e
  have hR : R.PosDef := blockDiag_posdef r e k 1 hkpos zero_lt_one
  have hGram : Aᴴ*A = blockDiag r e (ell^2) 1 := by
    simp [A,blockDiag, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    <;> simp only [← Complex.ofReal_mul, RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.coe_algebraMap]
  have hAntiGram : A*Aᴴ = blockDiag r e 1 (ell^2) := by
    simp [A,blockDiag, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    <;> simp only [← Complex.ofReal_mul, RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.coe_algebraMap]
  have hA : A ≠ 0 := by
    intro hz
    have h := congrArg (fun X : Matrix (Fin (2*r)) (Fin (2*r)) ℂ =>
      X (e.symm (Sum.inl 0)) (e.symm (Sum.inr 0))) hz
    simpa [A] using h
  have hAbs : CFC.abs A = blockDiag r e ell 1 := by
    unfold CFC.abs
    change CFC.sqrt (Aᴴ*A) = blockDiag r e ell 1
    rw [hGram]
    apply CFC.sqrt_unique ?_ (blockDiag_nonneg r e ell 1 hell0 zero_le_one)
    simpa only [pow_two, one_mul, mul_one] using blockDiag_mul r e ell 1 ell 1
  have hAbsProd : CFC.abs (A*Aᴴ) = blockDiag r e 1 (ell^2) := by
    rw [CFC.abs_of_nonneg _ (Matrix.posSemidef_self_mul_conjTranspose A).nonneg, hAntiGram]
  have hδ : contrast R = δ := by
    rw [blockDiag_contrast]
    simpa only [max_eq_left hk1, min_eq_right hk1] using hdcalc
  have hη : contrast (CFC.abs A) = η := by
    rw [hAbs, blockDiag_contrast]
    simpa only [max_eq_right hell1, min_eq_left hell1] using hecalc
  have hL : (R*CFC.abs (A*Aᴴ)).trace.re = (r:ℝ)*(k+ell^2) := by
    rw [hAbsProd, blockDiag_mul, blockDiag_trace]
    ring
  have hNval : ((R*(Aᴴ*A)).trace.re+(R*(Aᴴ*A)).trace.re)/2 =
      (r:ℝ)*(k*ell^2+1) := by
    rw [hGram,blockDiag_mul,blockDiag_trace]
    ring
  have hrR : 0 < (r:ℝ) := by exact_mod_cast hrpos
  have hbase : 0 < k*ell^2+1 := add_pos_of_nonneg_of_pos
    (mul_nonneg hkpos.le (sq_nonneg ell)) zero_lt_one
  have hN : 0 < ((R*(Aᴴ*A)).trace.re+(R*(Aᴴ*A)).trace.re)/2 := by
    rw [hNval]
    exact mul_pos hrR hbase
  refine ⟨R,A,A,hR,hA,hA,hδ,hη,hη,hN,?_⟩
  rw [hL,hNval]
  have hi := contrast_coefficient_identity 1 k ell 1 δ η
    zero_lt_one hkpos hell0 zero_lt_one hdcalc.symm hecalc.symm
  have hD := envelope_denominator_pos δ η hd1 he0
  have hratio : (k+ell^2-(k*ell^2+1))/(k*ell^2+1) =
      4*δ*η/(1+η^2-2*δ*η) := by
    apply (div_eq_div_iff hbase.ne' hD.ne').mpr
    nlinarith only [hi]
  rw [← mul_sub, mul_div_mul_left _ _ hrR.ne']
  exact hratio.symm

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung


namespace D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem result : claim := by
  intro r hr δ hd0 hd1 η he0 he1
  letI : NeZero (2*r) := ⟨by omega⟩
  have hatt := envelope_attained r hr δ η hd0 hd1 he0 he1
  have hu := values_upper_bound (n := 2*r) δ η hd1 he0 he1
  have hne : (values (2*r) δ η).Nonempty := ⟨_, hatt⟩
  have hbd : BddAbove (values (2*r) δ η) := ⟨_, hu⟩
  exact ⟨hne, hbd, le_antisymm (csSup_le hne hu) (le_csSup hbd hatt)⟩

end D5.S3.Quantum.Matrix.AbedNikolaevaNovikovTwoContrastYoung
