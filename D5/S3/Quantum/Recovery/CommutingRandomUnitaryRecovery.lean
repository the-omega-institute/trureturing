/- GID: D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unitary quasi-inversion for commuting random-unitary noise through dimension three. -/

import D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order

/-! Based on Li–Tam, Corollary 2(a), and Shahbeigi et al., Example 5 and Corollary 2.
See `Library/QuantumChannels/litam1994extremecorrelation.md` and
`Library/QuantumChannels/shahbeigietal2021quasiinversion.md`.

The eigenbasis construction adapts the normal-matrix argument in
`D5.S3.Quantum.BlockNorm.EssentiallyHermitian`, which credits the TauCeti
contributors (commit 7c8d7117e41432d613582fc600dcb0a3be7dba30).
Copyright (c) 2026 The TauCeti contributors. Licensed under Apache-2.0. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Elementwise
open Matrix Finset
open D5.S3.Quantum.Measurement.BasisMeasurementProjection (HermitianSpace)
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition (hermitian_space_finrank)
open D5.S3.Quantum.Recovery.BinaryRandomUnitaryChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)

noncomputable section

namespace D5.S3.Quantum.Recovery.CommutingRandomUnitaryRecovery

set_option maxHeartbeats 700000

/-- The complex correlation matrices are the positive semidefinite matrices of unit diagonal. -/
def correlationMatrices (d : ℕ) : Set (CodeMatrix d) :=
  {X | X.PosSemidef ∧ ∀ i, X i i = 1}

private theorem spectralFactor {d : ℕ} {X : CodeMatrix d} (hX : X.PosSemidef) :
    ∃ V : Matrix (Fin d) (Fin X.rank) ℂ, ∃ W : Matrix (Fin X.rank) (Fin d) ℂ,
      X = V * Vᴴ ∧ W * V = 1 := by
  classical
  let U : CodeMatrix d := hX.1.eigenvectorUnitary
  let eigenvalue := hX.1.eigenvalues
  let e : Fin X.rank ≃ {i // eigenvalue i ≠ 0} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hX.1.rank_eq_card_non_zero_eigs])
  let B : Fin X.rank → ℂ := fun j => (Real.sqrt (eigenvalue (e j).1) : ℝ)
  let Q : Matrix (Fin d) (Fin X.rank) ℂ := Matrix.of fun i j => U i (e j).1
  let V := Q * diagonal B
  let W := diagonal (fun j => (B j)⁻¹) * Qᴴ
  have hB (j : Fin X.rank) : B j ≠ 0 := by
    change (Real.sqrt (eigenvalue (e j).1) : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_ne_zero'.mpr
      (lt_of_le_of_ne (hX.eigenvalues_nonneg (e j).1) (e j).2.symm))
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hX.1.eigenvectorUnitary
  have hQ : Qᴴ * Q = 1 := by
    ext i j
    have h := congrArg (fun M : CodeMatrix d => M (e i).1 (e j).1) hU
    simpa only [Q, Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.one_apply,
      Subtype.val_inj, e.injective.eq_iff] using h
  refine ⟨V, W, ?_, ?_⟩
  · have hSpectral : X = U * diagonal (fun k => (eigenvalue k : ℂ)) * Uᴴ :=
      hX.1.spectral_theorem
    conv_lhs => rw [hSpectral]
    ext i j
    have ht (k : Fin X.rank) : B k * star (B k) = (eigenvalue (e k).1 : ℂ) := by
      simp only [B, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      exact congrArg Complex.ofReal (Real.mul_self_sqrt (hX.eigenvalues_nonneg (e k).1))
    let entry (k : Fin d) : ℂ := U i k * (eigenvalue k : ℂ) * star (U j k)
    have hv (a : Fin d) (k : Fin X.rank) : V a k = U a (e k).1 * B k :=
      mul_diagonal _ _ _ _
    calc
      _ = ∑ k, entry k := by
        rw [Matrix.mul_apply]
        simp only [Matrix.mul_diagonal, conjTranspose_apply, entry]
      _ = ∑ k : {k // eigenvalue k ≠ 0}, entry k.1 := by
        rw [← Finset.sum_subtype (univ.filter fun k => eigenvalue k ≠ 0)
          (fun k => by simp) entry]
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro k _ hk
        have hz : eigenvalue k = 0 := by simpa using hk
        simp [entry, hz]
      _ = ∑ k : Fin X.rank, entry (e k).1 := (e.sum_comp _).symm
      _ = (V * Vᴴ) i j := by
        rw [Matrix.mul_apply]
        apply sum_congr rfl
        intro k _
        rw [conjTranspose_apply, hv, hv, star_mul]
        dsimp [entry]
        rw [← ht]
        change U i (e k).1 * (B k * conj (B k)) * conj (U j (e k).1) = _
        ring
  · calc
      W * V = diagonal (fun j => (B j)⁻¹) * (Qᴴ * Q) * diagonal B := by
        simp only [W, V, Matrix.mul_assoc]
      _ = 1 := by simp [hQ, diagonal_mul_diagonal, hB, diagonal_one]

private theorem small_hermitian_perturbation {r : ℕ} {H : CodeMatrix r}
    (hH : H.IsHermitian) :
    ∃ t : ℝ, 0 < t ∧ ((1 : CodeMatrix r) + t • H).PosSemidef ∧
      ((1 : CodeMatrix r) - t • H).PosSemidef := by
  let U : CodeMatrix r := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let s : ℝ := 1 + ∑ i, |l i|
  have hs : 0 < s := by
    have := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin r))) (fun i _ => abs_nonneg (l i))
    dsimp [s]
    linarith
  have hb (i : Fin r) : |l i| ≤ s := by
    have := single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => abs_nonneg (l j))
      (mem_univ i)
    dsimp [s]
    linarith
  have hdiag (a : ℝ) (ha : |a| = s⁻¹) :
      (diagonal (fun i => ((1 + a * l i : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    have hm : |a * l i| ≤ 1 := by
      rw [abs_mul, ha, ← inv_mul_cancel₀ hs.ne']
      exact mul_le_mul_of_nonneg_left (hb i) (inv_nonneg.mpr hs.le)
    exact_mod_cast (show 0 ≤ 1 + a * l i by linarith [(abs_le.mp hm).1])
  have hp (a : ℝ) (ha : |a| = s⁻¹) : ((1 : CodeMatrix r) + a • H).PosSemidef := by
    have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    have he : H = U * diagonal (fun i => (l i : ℂ)) * Uᴴ := by
      exact hH.spectral_theorem
    have heq : (1 : CodeMatrix r) + a • H =
        U * diagonal (fun i => ((1 + a * l i : ℝ) : ℂ)) * Uᴴ := by
      have hd : diagonal (fun i => ((1 + a * l i : ℝ) : ℂ)) =
          1 + a • diagonal (fun i => (l i : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [diagonal_apply_eq, Complex.ofReal_add, Complex.ofReal_one,
            Complex.ofReal_mul, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
            Complex.real_smul]
        · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hu, ← he]
    rw [heq]
    exact (hdiag a ha).mul_mul_conjTranspose_same U
  refine ⟨s⁻¹, inv_pos.mpr hs, hp _ (abs_of_nonneg (inv_nonneg.mpr hs.le)), ?_⟩
  simpa only [neg_smul, sub_eq_add_neg] using hp (-s⁻¹)
    (by rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr hs.le)])

/-- Li–Tam's complex correlation-matrix rank bound (Corollary 2(a)). -/
theorem extreme_rank_sq_le {d : ℕ} {X : CodeMatrix d}
    (hX : X ∈ (correlationMatrices d).extremePoints ℝ) : X.rank ^ 2 ≤ d := by
  classical
  rcases spectralFactor hX.1.1 with ⟨V, W, hV, hW⟩
  let f : HermitianSpace X.rank →ₗ[ℝ] (Fin d → ℝ) :=
    { toFun := fun H i => (V * (H : CodeMatrix X.rank) * Vᴴ) i i |>.re
      map_add' := by
        intro A B
        funext i
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro a A
        funext i
        simp [Matrix.mul_smul, Matrix.smul_mul, Complex.real_smul] }
  by_contra! hdim
  have hn : ¬ Function.Injective f := by
    intro hf
    have h := LinearMap.finrank_le_finrank_of_injective hf
    rw [hermitian_space_finrank, Module.finrank_pi_fintype] at h
    exact (not_le_of_gt hdim) (by simpa using h)
  have ⟨H, hzero, hne⟩ : ∃ H, f H = 0 ∧ H ≠ 0 := by
    simpa only [injective_iff_map_eq_zero f, not_forall, not_imp, exists_prop] using hn
  let A : CodeMatrix X.rank := H
  have hA : A.IsHermitian := H.property
  let P := V * A * Vᴴ
  have hP : P.IsHermitian := by
    simp only [IsHermitian, P, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  have hpdiag (i : Fin d) : P i i = 0 := by
    apply Complex.ext
    · exact congrFun hzero i
    · have h := congrArg Complex.im (congrFun (congrFun hP.eq i) i)
      simp only [conjTranspose_apply, Complex.star_def, Complex.conj_im] at h
      rw [Complex.zero_im]
      linarith
  have hPne : P ≠ 0 := by
    intro hP0
    apply hne
    apply Subtype.ext
    have hwstar : Vᴴ * Wᴴ = 1 := by
      rw [← conjTranspose_mul, hW, conjTranspose_one]
    have he : W * P * Wᴴ = A := by
      calc
        _ = (W * V) * A * (Vᴴ * Wᴴ) := by simp only [P, Matrix.mul_assoc]
        _ = A := by rw [hW, hwstar, one_mul, mul_one]
    change A = 0
    simpa only [hP0, Matrix.mul_zero, Matrix.zero_mul] using he.symm
  obtain ⟨t, ht, hplus, hminus⟩ := small_hermitian_perturbation hA
  have hpos : (X + t • P).PosSemidef := by
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ← hV, P] using hplus.mul_mul_conjTranspose_same V
  have hneg : (X - t • P).PosSemidef := by
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ← hV, P] using hminus.mul_mul_conjTranspose_same V
  have he := hX.2 (x₁ := X + t • P) ⟨hpos, fun i => by simp [hpdiag, hX.1.2 i]⟩
    (x₂ := X - t • P) ⟨hneg, fun i => by simp [hpdiag, hX.1.2 i]⟩
    (show X ∈ openSegment ℝ (X + t • P) (X - t • P) from
      ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩)
  have hsmul : t • P = 0 := add_left_cancel (he.trans (add_zero X).symm)
  exact hPne ((smul_eq_zero.mp hsmul).resolve_left ht.ne')

private theorem correlation_compact (d : ℕ) : IsCompact (correlationMatrices d) := by
  have hc : IsClosed (correlationMatrices d) := by
    have he : correlationMatrices d =
        {X : CodeMatrix d | X.PosSemidef} ∩ ⋂ i : Fin d, {X | X i i = 1} := by
      ext X
      simp [correlationMatrices]
    rw [he]
    exact Matrix.posSemidef_is_closed.inter (isClosed_iInter fun i =>
      isClosed_eq ((continuous_apply i).comp (continuous_apply i)) continuous_const)
  refine (isCompact_closedBall (0 : CodeMatrix d) (d : ℝ)).of_isClosed_subset hc ?_
  intro X hX
  obtain ⟨V, _, hV, _⟩ := spectralFactor hX.1
  have hrow (i : Fin d) : ∑ j, Complex.normSq (V i j) = 1 := by
    have h := congrArg (fun M : CodeMatrix d => (M i i).re) hV
    simpa only [hX.2 i, Complex.one_re, Matrix.mul_apply, conjTranspose_apply,
      Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re] using h.symm
  have hbound (i : Fin d) (j : Fin X.rank) : ‖V i j‖ ≤ 1 := by
    have h := single_le_sum (fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (V i k))
      (mem_univ j)
    rw [hrow, Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (V i j)]
  rw [Metric.mem_closedBall, dist_zero_right, Matrix.norm_le_iff (Nat.cast_nonneg d)]
  intro i j
  rw [hV, mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin X.rank, (1 : ℝ) := sum_le_sum fun k _ => by
      rw [norm_mul, conjTranspose_apply, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hbound i k)).trans (hbound j k)
    _ ≤ (d : ℝ) := by simpa using (show (X.rank : ℝ) ≤ d by exact_mod_cast X.rank_le_height)

private theorem exists_extreme_max {d : ℕ} (f : CodeMatrix d →L[ℝ] ℝ) :
    ∃ X ∈ (correlationMatrices d).extremePoints ℝ,
      ∀ Y ∈ correlationMatrices d, f Y ≤ f X := by
  let C := correlationMatrices d
  have hC : IsCompact C := correlation_compact d
  have hne : C.Nonempty := ⟨1, PosSemidef.one, fun i => one_apply_eq i⟩
  obtain ⟨x, hx, hmax⟩ := hC.exists_isMaxOn hne f.continuous.continuousOn
  let F := {y ∈ C | f y = f x}
  have hF : IsCompact F := hC.inter_right (isClosed_eq f.continuous continuous_const)
  have he : IsExposed ℝ C F := by
    intro _
    refine ⟨f, Set.ext fun y => ?_⟩
    change (y ∈ C ∧ f y = f x) ↔ (y ∈ C ∧ ∀ z ∈ C, f z ≤ f y)
    constructor
    · rintro ⟨hy, hyx⟩
      exact ⟨hy, fun z hz => hyx ▸ hmax hz⟩
    · rintro ⟨hy, hymax⟩
      exact ⟨hy, (hmax hy).antisymm (hymax x hx)⟩
  let : LocallyConvexSpace ℝ (CodeMatrix d) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin d → Fin d → ℂ))
  obtain ⟨y, hy⟩ := hF.extremePoints_nonempty ⟨x, hx, rfl⟩
  refine ⟨y, he.isExtreme.extremePoints_subset_extremePoints hy, fun z hz => ?_⟩
  exact hy.1.2 ▸ hmax hz

/-- Every real linear functional on complex correlation matrices of size at most
three attains a maximum on a rank-one phase Gram matrix. -/
theorem phase_gram_max {d : ℕ} (hd : 0 < d) (hd3 : d ≤ 3)
    (f : CodeMatrix d →L[ℝ] ℝ) :
    ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) ∧
      ∀ X ∈ correlationMatrices d, f X ≤ f (vecMulVec z (star z)) := by
  obtain ⟨X, hX, hmax⟩ := exists_extreme_max f
  have hrle : X.rank ≤ 1 := by nlinarith [extreme_rank_sq_le hX]
  obtain ⟨V, _, hV, _⟩ := spectralFactor hX.1.1
  have hrne : X.rank ≠ 0 := by
    intro hr
    let : IsEmpty (Fin X.rank) := by rw [hr]; infer_instance
    let i : Fin d := ⟨0, hd⟩
    have h := congrArg (fun M : CodeMatrix d => M i i) hV
    simp [hX.1.2 i, Matrix.mul_apply] at h
  have hr : X.rank = 1 := by omega
  let j : Fin X.rank := ⟨0, by omega⟩
  have : Unique (Fin X.rank) := by rw [hr]; infer_instance
  let z : Fin d → ℂ := fun i => V i j
  have hgram : X = vecMulVec z (star z) := by
    rw [hV]
    ext a b
    have hj : (default : Fin X.rank) = j := Subsingleton.elim _ _
    simp [mul_apply, hj, z, vecMulVec_apply]
  refine ⟨z, fun i => ?_, fun Y hY => hgram ▸ hmax Y hY⟩
  have h := congrArg (fun M : CodeMatrix d => (M i i).re) hgram
  simp only [hX.1.2 i, Complex.one_re, vecMulVec_apply, Pi.star_apply, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (z i)]

private def weightedKraus {d : ℕ} {b : Type*} (w : b → ℝ)
    (U : b → unitaryGroup (Fin d) ℂ) (a : b) : CodeMatrix d :=
  (Real.sqrt (w a) : ℂ) • (U a : CodeMatrix d)

private theorem weighted_complete {d : ℕ} {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ) :
    ∑ a, (weightedKraus w U a)ᴴ * weightedKraus w U a = 1 := by
  have h (a : b) : (weightedKraus w U a)ᴴ * weightedKraus w U a =
      (w a : ℂ) • (1 : CodeMatrix d) := by
    simp only [weightedKraus, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (U a : CodeMatrix d)ᴴ * (U a : CodeMatrix d) = 1 from
      Unitary.coe_star_mul_self (U a)]
    rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (hw a)]
  simp only [h, ← Finset.sum_smul, ← Complex.ofReal_sum, hs, Complex.ofReal_one, one_smul]

/-- The actual CPTP mixture with any finite family of unitary branches and
nonnegative weights of total mass one. -/
def randomUnitaryChannel {d : ℕ} {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ) :
    CodeChannel d :=
  (finite_kraus_quantum_channel (weightedKraus w U) (weighted_complete hw hs U)).choose

private theorem randomUnitary_kraus_action {d : ℕ} {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ)
    (X : CodeMatrix d) :
    channelAction (randomUnitaryChannel hw hs U) X =
      ∑ a, weightedKraus w U a * X * (weightedKraus w U a)ᴴ :=
  (finite_kraus_quantum_channel (weightedKraus w U) (weighted_complete hw hs U)).choose_spec X

theorem randomUnitaryChannel_action {d : ℕ} {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ)
    (X : CodeMatrix d) :
    channelAction (randomUnitaryChannel hw hs U) X =
      ∑ a, (w a : ℂ) • channelAction (unitaryChannel (U a)) X := by
  rw [randomUnitary_kraus_action]
  apply sum_congr rfl
  intro a _
  simp only [unitaryChannel_action, weightedKraus, conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (hw a)]

/-- The canonical score of a finite unitary mixture is the weighted sum of the
squared traces of the branch-decoder products, with the canonical normalization. -/
theorem randomUnitary_score_kraus {d : ℕ} (hd : 0 < d)
    {b k : Type*} [Fintype b] [Fintype k] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ)
    (D : CodeChannel d) (K : k → CodeMatrix d)
    (hK : ∀ X, channelAction D X = ∑ a, K a * X * (K a)ᴴ) :
    recoveryScore (randomUnitaryChannel hw hs U) D =
      (d : ℝ)⁻¹ ^ 2 * ∑ j, ∑ a, w a * Complex.normSq (trace (K j * (U a : CodeMatrix d))) := by
  let L := weightedKraus w U
  have hcomp : channelAction (D.comp (randomUnitaryChannel hw hs U)) =
      MatrixMap.of_kraus (fun t : k × b => K t.1 * L t.2) (fun t : k × b => K t.1 * L t.2) := by
    apply LinearMap.ext
    intro X
    change channelAction D (channelAction (randomUnitaryChannel hw hs U) X) = _
    rw [hK, randomUnitary_kraus_action]
    simp only [L, Matrix.mul_sum, Matrix.sum_mul, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  unfold recoveryScore
  rw [hcomp, canonical_overlap_kraus _ hd, Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro a _
  simp only [L, weightedKraus, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (hw a)]

private def gramObjective {d : ℕ} {b : Type*} [Fintype b] (w : b → ℝ)
    (u : b → Fin d → ℂ) : CodeMatrix d →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun X => ∑ a, w a * ∑ i, ∑ j, (u a i * X i j * conj (u a j)).re
        map_add' := by
          intro X Y
          simp only [Matrix.add_apply, mul_add, add_mul, Complex.add_re, Finset.sum_add_distrib]
        map_smul' := by
          intro c X
          simp only [Matrix.smul_apply, Complex.real_smul, RingHom.id_apply, smul_eq_mul]
          have h (a : b) (i j : Fin d) :
              (u a i * ((c : ℂ) * X i j) * conj (u a j)).re =
                c * (u a i * X i j * conj (u a j)).re := by
            rw [← Complex.re_ofReal_mul]
            congr 1
            ring
          simp_rw [h, ← Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum]
          apply sum_congr rfl
          intro a _
          ring }
    cont := by fun_prop }

private theorem objective_outer {d : ℕ} {b : Type*} [Fintype b] (w : b → ℝ)
    (u : b → Fin d → ℂ) (z : Fin d → ℂ) :
    gramObjective w u (vecMulVec z (star z)) =
      ∑ a, w a * Complex.normSq (∑ i, z i * u a i) := by
  change ∑ a, w a * ∑ i, ∑ j, (u a i * (z i * conj (z j)) * conj (u a j)).re = _
  apply sum_congr rfl
  intro a _
  congr 1
  simp_rw [← Complex.re_sum]
  have hn (q : ℂ) : (q * conj q).re = Complex.normSq q := by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [← hn, map_sum, Finset.sum_mul]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  ring

private theorem diagonal_mass_le {d : ℕ} {k : Type*} [Fintype k] (L : k → CodeMatrix d)
    (hL : ∑ b, (L b)ᴴ * L b = 1) (j : Fin d) :
    ∑ b, Complex.normSq (L b j j) ≤ 1 := by
  have h := congrArg (fun X : CodeMatrix d => (X j j).re) hL
  simp only [Matrix.sum_apply, Complex.re_sum, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re] at h
  rw [← h]
  exact sum_le_sum fun b _ =>
    single_le_sum (fun i _ => Complex.normSq_nonneg (L b i j)) (mem_univ j)

private theorem complete_gram {d : ℕ} {b k : Type*} [Fintype b] [Fintype k]
    {w : b → ℝ} (hw : ∀ a, 0 ≤ w a) (u : b → Fin d → ℂ)
    (z : k → Fin d → ℂ) (hz : ∀ i, ∑ j, Complex.normSq (z j i) ≤ 1) :
    ∃ X ∈ correlationMatrices d,
      (∑ j, ∑ a, w a * Complex.normSq (∑ i, z j i * u a i)) ≤ gramObjective w u X := by
  classical
  let G := ∑ j, vecMulVec (z j) (star (z j))
  let m : Fin d → ℝ := fun i => 1 - ∑ j, Complex.normSq (z j i)
  let c (i : Fin d) : Fin d → ℂ := Pi.single i (Real.sqrt (m i) : ℂ)
  let E := ∑ i, vecMulVec (c i) (star (c i))
  have hm (i) : 0 ≤ m i := sub_nonneg.mpr (hz i)
  have hc (i : Fin d) : (vecMulVec (c i) (star (c i))) i i = (m i : ℂ) := by
    simp only [vecMulVec_apply, c, Pi.single_eq_same, Pi.star_apply, Complex.star_def,
      Complex.mul_conj, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (hm i)]
  refine ⟨G + E, ⟨(posSemidef_sum _ (fun j _ => posSemidef_vecMulVec_self_star (z j))).add
    (posSemidef_sum _ (fun i _ => posSemidef_vecMulVec_self_star (c i))), fun i => ?_⟩, ?_⟩
  · have hE : E i i = (m i : ℂ) := by
      rw [show E i i = ∑ j, (vecMulVec (c j) (star (c j))) i i from Matrix.sum_apply _ _ _ _]
      rw [Fintype.sum_eq_single i, hc]
      intro j hj
      simp [c, vecMulVec_apply, Pi.single_eq_of_ne (Ne.symm hj)]
    simp only [Matrix.add_apply, hE, G, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply,
      Complex.star_def, Complex.mul_conj, ← Complex.ofReal_sum, m, Complex.ofReal_sub,
      Complex.ofReal_one, add_sub_cancel]
  · rw [map_add]
    have hG : gramObjective w u G =
        ∑ j, ∑ a, w a * Complex.normSq (∑ i, z j i * u a i) := by
      simp only [G, map_sum, objective_outer]
    rw [hG]
    exact le_add_of_nonneg_right (by
      simp only [E, map_sum, objective_outer]
      exact sum_nonneg fun i _ => sum_nonneg fun a _ => mul_nonneg (hw a) (Complex.normSq_nonneg _))

private def changeBasis {d : ℕ} (S : unitaryGroup (Fin d) ℂ) (K : CodeMatrix d) :
    CodeMatrix d := (S : CodeMatrix d)ᴴ * K * (S : CodeMatrix d)

private theorem changeBasis_complete {d : ℕ} {k : Type*} [Fintype k]
    (S : unitaryGroup (Fin d) ℂ) (K : k → CodeMatrix d)
    (hK : ∑ a, (K a)ᴴ * K a = 1) :
    ∑ a, (changeBasis S (K a))ᴴ * changeBasis S (K a) = 1 := by
  have hS : (S : CodeMatrix d) * (S : CodeMatrix d)ᴴ = 1 := Unitary.coe_mul_star_self S
  have hS' : (S : CodeMatrix d)ᴴ * (S : CodeMatrix d) = 1 := Unitary.coe_star_mul_self S
  calc
    _ = ∑ a, (S : CodeMatrix d)ᴴ * ((K a)ᴴ * K a) * (S : CodeMatrix d) := by
      apply sum_congr rfl
      intro a _
      simp only [changeBasis, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        _ = (S : CodeMatrix d)ᴴ * (K a)ᴴ *
            ((S : CodeMatrix d) * (S : CodeMatrix d)ᴴ) * K a * (S : CodeMatrix d) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by simp only [hS, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.sum_mul, ← Matrix.mul_sum, hK, Matrix.mul_one, hS']

private theorem trace_changeBasis {d : ℕ} (S T : unitaryGroup (Fin d) ℂ) (K : CodeMatrix d) :
    trace (K * ((S * T * star S : unitaryGroup (Fin d) ℂ) : CodeMatrix d)) =
      trace (changeBasis S K * (T : CodeMatrix d)) := by
  simp only [Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose, changeBasis]
  rw [← Matrix.mul_assoc K, Matrix.trace_mul_comm _ ((S : CodeMatrix d)ᴴ)]
  simp only [Matrix.mul_assoc]

/-- For a finite mixture with a supplied simultaneous unitary eigenbasis, the
canonical recovery score in positive dimension at most three is maximized by
a unitary decoder diagonal in that basis. -/
theorem unitary_optimal_of_eigenbasis {d : ℕ} (hd : 0 < d) (hd3 : d ≤ 3)
    {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ)
    (S : unitaryGroup (Fin d) ℂ) (u : b → Fin d → ℂ) (hu : ∀ a i, ‖u a i‖ = 1)
    (hU : ∀ a, star S * U a * S = diagonalUnitary (u a) (hu a)) :
    ∃ z : Fin d → ℂ, ∃ hz : ∀ i, ‖z i‖ = 1, ∀ D : CodeChannel d,
      recoveryScore (randomUnitaryChannel hw hs U) D ≤
        recoveryScore (randomUnitaryChannel hw hs U)
          (unitaryChannel (S * diagonalUnitary z hz * star S)) := by
  let f := gramObjective w u
  obtain ⟨z, hz, hmax⟩ := phase_gram_max hd hd3 f
  refine ⟨z, hz, fun D => ?_⟩
  let K := actual_kraus_representation D
  let Z := S * diagonalUnitary z hz * star S
  let L := changeBasis S ∘ K.kraus
  have hL : ∑ j, (L j)ᴴ * L j = 1 := changeBasis_complete S K.kraus K.hkraus
  have htrace (A : CodeMatrix d) (a : b) : trace (A * (U a : CodeMatrix d)) =
      ∑ i, changeBasis S A i i * u a i := by
    have he : S * diagonalUnitary (u a) (hu a) * star S = U a := by
      rw [← hU a]
      simp only [Unitary.star_eq_inv]
      group
    rw [← he, trace_changeBasis]
    simp only [diagonalUnitary, trace, Matrix.diag, Matrix.mul_diagonal]
  have hZ : changeBasis S (Z : CodeMatrix d) = diagonal z := by
    have he : star S * Z * S = diagonalUnitary z hz := by
      dsimp [Z]
      simp only [Unitary.star_eq_inv]
      group
    exact congrArg Subtype.val he
  have hscore := randomUnitary_score_kraus hd hw hs U (unitaryChannel Z)
    (fun _ : Unit => (Z : CodeMatrix d)) (by
      intro X
      simp only [unitaryChannel_action, Fintype.sum_unique])
  change recoveryScore (randomUnitaryChannel hw hs U) D ≤
    recoveryScore (randomUnitaryChannel hw hs U) (unitaryChannel Z)
  rw [randomUnitary_score_kraus hd hw hs U D K.kraus K.haction, hscore]
  simp only [Fintype.sum_unique, htrace, hZ, diagonal_apply_eq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  obtain ⟨X, hX, hdom⟩ := complete_gram hw u (fun j i => L j i i) (diagonal_mass_le L hL)
  exact hdom.trans ((hmax X hX).trans_eq (objective_outer w u z))

/-- Every finite diagonal random-unitary mixture in dimension one, two or
three has a diagonal unitary decoder optimal among all deterministic CPTP decoders. -/
theorem diagonal_unitary_optimal {d : ℕ} (hd : 0 < d) (hd3 : d ≤ 3)
    {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (u : b → Fin d → ℂ) (hu : ∀ a i, ‖u a i‖ = 1) :
    ∃ z : Fin d → ℂ, ∃ hz : ∀ i, ‖z i‖ = 1, ∀ D : CodeChannel d,
      recoveryScore (randomUnitaryChannel hw hs (fun a => diagonalUnitary (u a) (hu a))) D ≤
        recoveryScore (randomUnitaryChannel hw hs (fun a => diagonalUnitary (u a) (hu a)))
          (unitaryChannel (diagonalUnitary z hz)) := by
  simpa using unitary_optimal_of_eigenbasis hd hd3 hw hs
    (fun a => diagonalUnitary (u a) (hu a)) 1 u hu (by simp)

open Module Module.End ComplexStarModule in
/-- A pairwise commuting family of unitaries has a simultaneous unitary
eigenbasis. Its real and imaginary parts share orthogonal joint eigenspaces. -/
theorem simultaneous_unitary_eigenbasis {d : ℕ} {b : Type*}
    (U : b → unitaryGroup (Fin d) ℂ) (hU : ∀ a c, Commute (U a) (U c)) :
    ∃ S : unitaryGroup (Fin d) ℂ, ∃ u : b → Fin d → ℂ,
      ∃ hu : ∀ a i, ‖u a i‖ = 1, ∀ a, star S * U a * S = diagonalUnitary (u a) (hu a) := by
  classical
  let E := EuclideanSpace ℂ (Fin d)
  let T (a : b) : E →ₗ[ℂ] E := toEuclideanLin (U a : CodeMatrix d)
  have hstar (a : b) : star (T a) = toEuclideanLin (↑(star (U a)) : CodeMatrix d) := by
    rw [LinearMap.star_eq_adjoint, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      toEuclideanLin_conjTranspose_eq_adjoint]
  have hmap {V W : unitaryGroup (Fin d) ℂ} (h : Commute V W) :
      Commute (toEuclideanLin (V : CodeMatrix d)) (toEuclideanLin (W : CodeMatrix d)) :=
    (h.map (unitaryGroup (Fin d) ℂ).subtype).map (toLpLinAlgEquiv 2)
  have hc (a c : b) : Commute (T a) (T c) := hmap (hU a c)
  have hcs (a c : b) : Commute (T a) (star (T c)) := by
    rw [hstar]
    exact hmap (by simpa only [Unitary.star_eq_inv] using (hU a c).inv_right)
  have hsc (a c : b) : Commute (star (T a)) (T c) := (hcs c a).symm
  have hss (a c : b) : Commute (star (T a)) (star (T c)) := by
    rw [hstar, hstar]
    exact hmap (by simpa only [Unitary.star_eq_inv] using (hU a c).inv_left.inv_right)
  have hparts (A B : E →ₗ[ℂ] E) (h : Commute A B) (hs : Commute A (star B)) :
      Commute A (ℜ B : E →ₗ[ℂ] E) ∧ Commute A (ℑ B : E →ₗ[ℂ] E) := by
    rw [realPart_apply_coe, imaginaryPart_apply_coe]
    exact ⟨(h.add_right hs).smul_right _, ((h.sub_right hs).smul_right _).smul_right _⟩
  let F : b ⊕ b → E →ₗ[ℂ] E :=
    Sum.elim (fun a => (ℜ (T a) : E →ₗ[ℂ] E)) (fun a => (ℑ (T a) : E →ₗ[ℂ] E))
  have hs (a : b ⊕ b) : (F a).IsSymmetric := by
    cases a
    · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (ℜ (T _)).2
    · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr (ℑ (T _)).2
  have hp : Pairwise (fun a c => Commute (F a) (F c)) := by
    intro a c _
    cases a <;> cases c
    · exact (hparts _ _ (hparts _ _ (hc _ _) (hcs _ _)).1.symm
        (hparts _ _ (hsc _ _) (hss _ _)).1.symm).1.symm
    · exact (hparts _ _ (hparts _ _ (hc _ _) (hcs _ _)).2.symm
        (hparts _ _ (hsc _ _) (hss _ _)).2.symm).1.symm
    · exact (hparts _ _ (hparts _ _ (hc _ _) (hcs _ _)).1.symm
        (hparts _ _ (hsc _ _) (hss _ _)).1.symm).2.symm
    · exact (hparts _ _ (hparts _ _ (hc _ _) (hcs _ _)).2.symm
        (hparts _ _ (hsc _ _) (hss _ _)).2.symm).2.symm
  let V (χ : b ⊕ b → ℂ) : Submodule ℂ E := ⨅ a, eigenspace (F a) (χ a)
  have hV : DirectSum.IsInternal V :=
    LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hs hp
  have hO := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hs
  let J := {χ // V χ ≠ ⊥}
  let _ : Fintype J := hV.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hVJ : DirectSum.IsInternal fun χ : J => V χ := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hOJ := hO.comp (Subtype.val_injective (p := fun χ => V χ ≠ ⊥))
  have hd : finrank ℂ E = d := by simp [E]
  let B := hVJ.subordinateOrthonormalBasis hd hOJ
  let χ (i : Fin d) := (hVJ.subordinateOrthonormalBasisIndex hd i hOJ).1
  let u (a : b) (i : Fin d) := χ i (Sum.inl a) + Complex.I * χ i (Sum.inr a)
  have hB (a : b) (i : Fin d) : T a (B i) = u a i • B i := by
    have hm : B i ∈ V (χ i) := hVJ.subordinateOrthonormalBasis_subordinate hd i hOJ
    have hr := mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hm) (Sum.inl a))
    have hi := mem_eigenspace_iff.mp (((Submodule.mem_iInf _).mp hm) (Sum.inr a))
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart (T a)]
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    change F (Sum.inl a) (B i) + Complex.I • F (Sum.inr a) (B i) = _
    rw [hr, hi, smul_smul, ← add_smul]
  let s := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
  let S : unitaryGroup (Fin d) ℂ := ⟨s.toMatrix B.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary B⟩
  have hsinv : (star S : CodeMatrix d) = B.toBasis.toMatrix s := by
    change star (s.toMatrix B.toBasis) = _
    rw [← Matrix.mul_one (star _), ← s.toMatrix_mul_toMatrix_flip B.toBasis, ← Matrix.mul_assoc,
      (mem_unitaryGroup_iff'.mp S.property), Matrix.one_mul]
  have hdiag (a : b) : ((star S * U a * S : unitaryGroup (Fin d) ℂ) : CodeMatrix d) =
      diagonal (u a) := by
    have ha : (U a : CodeMatrix d) = LinearMap.toMatrix s s (T a) := by
      rw [show T a = toEuclideanLin (U a : CodeMatrix d) from rfl,
        toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
    change ((star S : CodeMatrix d) * (U a : CodeMatrix d) * s.toMatrix B.toBasis) = _
    rw [hsinv, ha, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
    ext i j
    by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, hB, h]
  have hu (a : b) (i : Fin d) : ‖u a i‖ = 1 := by
    have hgram := Unitary.coe_star_mul_self (star S * U a * S)
    rw [Matrix.star_eq_conjTranspose, hdiag, diagonal_conjTranspose, diagonal_mul_diagonal] at hgram
    have h := congrArg (fun A : CodeMatrix d => (A i i).re) hgram
    simp only [diagonal_apply_eq, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re, Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (u a i)]
  exact ⟨S, u, hu, fun a => Subtype.ext (hdiag a)⟩

/-- Every finite, pairwise commuting random-unitary mixture in positive dimension
at most three has a unitary decoder that maximizes the canonical recovery score. -/
theorem commuting_unitary_optimal {d : ℕ} (hd : 0 < d) (hd3 : d ≤ 3)
    {b : Type*} [Fintype b] {w : b → ℝ}
    (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (U : b → unitaryGroup (Fin d) ℂ)
    (hU : ∀ a c, Commute (U a) (U c)) :
    ∃ Z : unitaryGroup (Fin d) ℂ, ∀ D : CodeChannel d,
      recoveryScore (randomUnitaryChannel hw hs U) D ≤
        recoveryScore (randomUnitaryChannel hw hs U) (unitaryChannel Z) := by
  obtain ⟨S, u, hu, hS⟩ := simultaneous_unitary_eigenbasis U hU
  obtain ⟨z, hz, hopt⟩ := unitary_optimal_of_eigenbasis hd hd3 hw hs U S u hu hS
  exact ⟨S * diagonalUnitary z hz * star S, hopt⟩

#print axioms extreme_rank_sq_le
#print axioms phase_gram_max
#print axioms randomUnitaryChannel_action
#print axioms randomUnitary_score_kraus
#print axioms unitary_optimal_of_eigenbasis
#print axioms diagonal_unitary_optimal
#print axioms simultaneous_unitary_eigenbasis
#print axioms commuting_unitary_optimal

end D5.S3.Quantum.Recovery.CommutingRandomUnitaryRecovery
