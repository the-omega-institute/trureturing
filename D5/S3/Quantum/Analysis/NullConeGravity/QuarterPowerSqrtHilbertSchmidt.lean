/- GID: D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp square-root perturbation, bounded congruence and compact coercivity. -/

import D5.S3.Quantum.Analysis.TraceClass.FiniteCompression
import D5.S3.Quantum.Analysis.TraceClass.GeneralProduct
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic.NoncommRing
/-! Stage 3A of #34535. Sharp square-root bounds under quarter-power perturbations. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder InnerProductSpace Topology Polynomial NNReal
open ContinuousLinearMap HilbertSchmidt Filter

namespace D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt

variable {H K G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
/-- The positive fourth root obtained by taking two square roots. -/
abbrev quarterRoot (A : H →L[ℂ] H) := CFC.sqrt (CFC.sqrt A)
/-- Rectangular congruence of a bounded operator. -/
def adjointCongr (C : K →L[ℂ] H) (A : H →L[ℂ] H) : K →L[ℂ] K :=
  C.adjoint ∘L A ∘L C
/-- The squared Hilbert–Schmidt norm in a chosen Hilbert basis. -/
def hsSq (A : H →L[ℂ] H) (_hA : IsHilbertSchmidt A) : ℝ :=
  ∑' i, ‖A ((exists_hilbertBasis ℂ H).choose_spec.choose i)‖ ^ 2
private theorem hsSq_eq {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    {w : Set H} (b : HilbertBasis w ℂ H) : hsSq A hA = ∑' i, ‖A (b i)‖ ^ 2 := by
  exact (hasSum_norm_sq_apply_of_basis _ b
    (summable_norm_sq_apply_of_hilbertBasis _ _ hA)).tsum_eq.symm
private theorem hsSq_nonneg {A : H →L[ℂ] H} (hA : IsHilbertSchmidt A) : 0 ≤ hsSq A hA :=
  tsum_nonneg fun _ => sq_nonneg _
/-- A norm domination factors through the closed range of the dominating map. -/
theorem exists_bounded_factor (L : K →L[ℂ] H) (D : K →L[ℂ] K) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x, ‖L x‖ ≤ c * ‖D x‖) :
    ∃ Z : K →L[ℂ] H, ‖Z‖ ≤ c ∧ L = Z ∘L D := by
  let U := (LinearMap.range D.toLinearMap).topologicalClosure
  let : CompleteSpace U := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let e := D.toLinearMap.codRestrict U fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  have hd (y : U) : y ∈ closure (Set.range e) := by
    rw [closure_subtype, ← Set.range_comp]
    exact y.property
  let E := L.toLinearMap.extendOfNorm e
  refine ⟨E ∘L U.orthogonalProjectionOnto, opNorm_le_bound _ hc fun x => ?_, ?_⟩
  · exact (E.le_opNorm _).trans <| mul_le_mul (LinearMap.opNorm_extendOfNorm_le hd hc h)
      (U.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _) hc
  · ext x
    change L x = E (U.orthogonalProjectionOnto (D x))
    rw [show D x = (e x : K) from rfl, U.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact (LinearMap.extendOfNorm_eq hd ⟨c, h⟩ x).symm
private theorem rectangular_sum_adjoint {u : Set K} {v : Set H}
    (b : HilbertBasis u ℂ K) (d : HilbertBasis v ℂ H) (S : K →L[ℂ] H)
    (hb : Summable fun i => ‖S (b i)‖ ^ 2) :
    HasSum (fun j => ‖S.adjoint (d j)‖ ^ 2) (∑' i, ‖S (b i)‖ ^ 2) := by
  let f : u → v → ℝ := fun i j => ‖⟪d j, S (b i)⟫_ℂ‖ ^ 2
  have hr (i : u) : HasSum (f i) (‖S (b i)‖ ^ 2) := hasSum_norm_sq_inner_basis d _
  have hc (j : v) : HasSum (fun i => f i j) (‖S.adjoint (d j)‖ ^ 2) := by
    convert hasSum_norm_sq_inner_basis b (S.adjoint (d j)) using 2
    simp only [f, ← adjoint_inner_left, ← inner_conj_symm (b _) (S.adjoint (d j)),
      RCLike.norm_conj]
  have hrows : (fun i => ∑' j, f i j) = fun i => ‖S (b i)‖ ^ 2 :=
    funext fun i => (hr i).tsum_eq
  have hf : Summable (Function.uncurry f) := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun i => (hr i).summable, by rw [hrows]; exact hb⟩
  have hflip : Summable (Function.uncurry fun j i => f i j) :=
    (Equiv.prodComm v u).summable_iff.mpr hf
  have he : (∑' p : v × u, f p.2 p.1) = ∑' i, ‖S (b i)‖ ^ 2 := by
    calc
      _ = ∑' p : u × v, f p.1 p.2 := (Equiv.prodComm v u).tsum_eq _
      _ = ∑' i, ∑' j, f i j := hf.tsum_prod
      _ = _ := congrArg tsum hrows
  exact he ▸ hflip.hasSum.prod_fiberwise hc
omit [CompleteSpace H] [CompleteSpace K] in
private theorem left_square_sum {ι : Type*} (b : ι → K) (S : K →L[ℂ] H)
    (L : H →L[ℂ] G) (h : Summable fun i => ‖S (b i)‖ ^ 2) :
    Summable (fun i => ‖(L ∘L S) (b i)‖ ^ 2) ∧
      (∑' i, ‖(L ∘L S) (b i)‖ ^ 2) ≤ ‖L‖ ^ 2 * ∑' i, ‖S (b i)‖ ^ 2 := by
  have hb (i : ι) : ‖(L ∘L S) (b i)‖ ^ 2 ≤ ‖L‖ ^ 2 * ‖S (b i)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) _
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb (h.mul_left (‖L‖ ^ 2))
  exact ⟨hs, (hs.tsum_le_tsum hb (h.mul_left _)).trans_eq (tsum_mul_left)⟩
/-- Rectangular congruence is bounded on the Hilbert–Schmidt ideal. -/
theorem adjointCongr_hsSq_le (Z : K →L[ℂ] H) {W : H →L[ℂ] H}
    (hW : IsHilbertSchmidt W) :
    ∃ h : IsHilbertSchmidt (adjointCongr Z W),
      hsSq (adjointCongr Z W) h ≤ ‖Z‖ ^ 4 * hsSq W hW := by
  obtain ⟨u, b, _⟩ := exists_hilbertBasis ℂ K
  obtain ⟨v, d, _⟩ := exists_hilbertBasis ℂ H
  have ⟨hs, h₁⟩ := left_square_sum d W Z.adjoint
    (summable_norm_sq_apply_of_hilbertBasis v d hW)
  have ht := rectangular_sum_adjoint d b _ hs
  have ⟨hu, h₂⟩ := left_square_sum b _ Z.adjoint ht.summable
  have hv := rectangular_sum_adjoint b b _ hu
  have he : (Z.adjoint ∘L (Z.adjoint ∘L W).adjoint).adjoint = adjointCongr Z W := by
    simp [adjointCongr, comp_assoc]
  rw [he] at hv
  have h : IsHilbertSchmidt (adjointCongr Z W) := ⟨u, b, hv.summable⟩
  refine ⟨h, ?_⟩
  rw [hsSq_eq h b, hsSq_eq hW d, hv.tsum_eq]
  rw [ht.tsum_eq, adjoint.norm_map] at h₂
  rw [adjoint.norm_map] at h₁
  exact (h₂.trans (mul_le_mul_of_nonneg_left h₁ (sq_nonneg _))).trans_eq (by ring)
private theorem adjoint_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : A.adjoint = A :=
  (nonneg_iff_isPositive.mp hA).isSelfAdjoint
private theorem form_le {A B : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    A ≤ B ↔ ∀ x, A.reApplyInnerSelf x ≤ B.reApplyInnerSelf x := by
  rw [ContinuousLinearMap.le_def, isPositive_def']
  simp [hB.sub hA, reApplyInnerSelf, inner_sub_left, sub_nonneg]
omit [CompleteSpace H] in
private theorem form_smul (a : ℝ) (A : H →L[ℂ] H) (x : H) :
    (a • A).reApplyInnerSelf x = a * A.reApplyInnerSelf x := by
  simp [reApplyInnerSelf, inner_smul_left_eq_smul]
omit [CompleteSpace H] in
private theorem form_one (x : H) : (1 : H →L[ℂ] H).reApplyInnerSelf x = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x
private theorem form_sqrt (A : H →L[ℂ] H) (hA : 0 ≤ A) (x : H) :
    ‖CFC.sqrt A x‖ ^ 2 = A.reApplyInnerSelf x := by
  rw [apply_norm_sq_eq_inner_adjoint_left, adjoint_nonneg (CFC.sqrt_nonneg A)]
  exact congrArg (fun S : H →L[ℂ] H => S.reApplyInnerSelf x) (CFC.sqrt_mul_sqrt_self A hA)
private theorem congr_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) (C : K →L[ℂ] H) :
    0 ≤ adjointCongr C A :=
  nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp hA).adjoint_conj C)
private theorem congr_sub (C : K →L[ℂ] H) (B A : H →L[ℂ] H) :
    adjointCongr C (B - A) = adjointCongr C B - adjointCongr C A := by
  ext x
  simp [adjointCongr]
private theorem factor_congr {A M : H →L[ℂ] H} {N : K →L[ℂ] K}
    (hA : A.adjoint = A) (hN : N.adjoint = N) {C Z : K →L[ℂ] H}
    (h : A ∘L C = Z ∘L N) :
    adjointCongr C (A * M * A) = N * adjointCongr Z M * N := by
  have ht := congrArg adjoint h
  simp only [adjoint_comp, hA, hN] at ht
  ext x
  have hl (y : H) := DFunLike.congr_fun ht y
  have hr (y : K) := DFunLike.congr_fun h y
  simp only [comp_apply] at hl hr
  simp only [adjointCongr, comp_apply, mul_apply_eq_comp, hl, hr]
set_option maxHeartbeats 800000 in -- Elaborate the CFC order on two Hilbert spaces.
/-- Bounded congruence carries the quarter-power factorization with quantitative control. -/
theorem quarterPower_congruence {A B W : H →L[ℂ] H}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hW : IsHilbertSchmidt W)
    (hD : B - A = quarterRoot A * W * quarterRoot A) (C : K →L[ℂ] H) :
    let M := adjointCongr C A
    ∃ Z : K →L[ℂ] H, ‖Z‖ ^ 2 ≤ ‖C‖ ∧
      quarterRoot A ∘L C = Z ∘L quarterRoot M ∧
      adjointCongr C (B - A) = quarterRoot M * adjointCongr Z W * quarterRoot M ∧
      ∃ h : IsHilbertSchmidt (adjointCongr Z W),
        hsSq (adjointCongr Z W) h ≤ ‖C‖ ^ 2 * hsSq W hW := by
  let P := CFC.sqrt A
  let S := adjointCongr C P
  let M := adjointCongr C A
  have hP : 0 ≤ P := CFC.sqrt_nonneg A
  have hS : 0 ≤ S := congr_nonneg hP C
  have hM : 0 ≤ M := congr_nonneg hA C
  have hSsa : IsSelfAdjoint S := adjoint_nonneg hS
  have hMsa : IsSelfAdjoint M := adjoint_nonneg hM
  have hsq : S * S ≤ ‖C‖ ^ 2 • M := by
    have hss : IsSelfAdjoint (S * S) := by simp [IsSelfAdjoint, star_mul, hSsa.star_eq]
    apply (form_le hss ((IsSelfAdjoint.all (‖C‖ ^ 2)).smul hMsa)).mpr
    intro x
    have h₁ : ‖S x‖ ^ 2 = (S * S).reApplyInnerSelf x := by
      rw [apply_norm_sq_eq_inner_adjoint_left, adjoint_nonneg hS]
      rfl
    have h₂ : ‖P (C x)‖ ^ 2 = M.reApplyInnerSelf x := by
      rw [form_sqrt A hA]
      simp [M, adjointCongr, reApplyInnerSelf, ← adjoint_inner_left]
    rw [← h₁, form_smul, ← h₂, ← mul_pow]
    simpa only [S, adjointCongr, comp_apply, adjoint.norm_map] using
      pow_le_pow_left₀ (norm_nonneg (S x)) (C.adjoint.le_opNorm (P (C x))) 2
  have hroot : S ≤ ‖C‖ • CFC.sqrt M := by
    have he : (‖C‖ • CFC.sqrt M) * (‖C‖ • CFC.sqrt M) = ‖C‖ ^ 2 • M := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_two, CFC.sqrt_mul_sqrt_self M hM]
    simpa only [CFC.sqrt_unique rfl hS, CFC.sqrt_unique he
      (smul_nonneg (norm_nonneg C) (CFC.sqrt_nonneg M))] using CFC.sqrt_le_sqrt _ _ hsq
  have hb (x : K) : ‖(quarterRoot A ∘L C) x‖ ≤ Real.sqrt ‖C‖ * ‖quarterRoot M x‖ := by
    have hr : IsSelfAdjoint (CFC.sqrt M) := adjoint_nonneg (CFC.sqrt_nonneg M)
    have hf := (form_le hSsa ((IsSelfAdjoint.all ‖C‖).smul hr)).mp hroot x
    have he : ‖(quarterRoot A ∘L C) x‖ ^ 2 = S.reApplyInnerSelf x := by
      rw [comp_apply, form_sqrt P hP]
      simp [S, adjointCongr, reApplyInnerSelf, ← adjoint_inner_left]
    rwa [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 2 ≠ 0),
      mul_pow, Real.sq_sqrt (norm_nonneg _), he, form_sqrt _ (CFC.sqrt_nonneg M),
      ← form_smul]
  obtain ⟨Z, hz, he⟩ := exists_bounded_factor (quarterRoot A ∘L C) (quarterRoot M)
    (Real.sqrt_nonneg _) hb
  have hz₂ : ‖Z‖ ^ 2 ≤ ‖C‖ := (pow_le_pow_left₀ (norm_nonneg _) hz 2).trans_eq
    (Real.sq_sqrt (norm_nonneg _))
  obtain ⟨h, hh⟩ := adjointCongr_hsSq_le Z hW
  refine ⟨Z, hz₂, he, ?_, h, hh.trans ?_⟩
  · rw [hD]
    exact factor_congr (adjoint_nonneg (CFC.sqrt_nonneg _))
      (adjoint_nonneg (CFC.sqrt_nonneg _)) he
  · rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hz₂ _) (hsSq_nonneg hW)

section Finite
variable [FiniteDimensional ℂ H]
private theorem finite_hs (T : H →L[ℂ] H) : IsHilbertSchmidt T := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  exact ⟨w, b, Summable.of_finite⟩
private def tr (T : H →L[ℂ] H) : ℝ := (LinearMap.trace ℂ H T.toLinearMap).re
omit [CompleteSpace H] [FiniteDimensional ℂ H] in
private theorem tr_cycle (X Y : H →L[ℂ] H) : tr (X * Y) = tr (Y * X) :=
  congrArg Complex.re (LinearMap.trace_mul_comm ℂ X.toLinearMap Y.toLinearMap)
omit [CompleteSpace H] [FiniteDimensional ℂ H] in
private theorem tr_sub (X Y : H →L[ℂ] H) : tr (X - Y) = tr X - tr Y := by
  simp [tr]
private theorem hsSq_trace (T : H →L[ℂ] H) (h : IsHilbertSchmidt T) :
    hsSq T h = tr (T.adjoint * T) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  rw [hsSq_eq h b, tr, trace_eq_sum_inner_hilbertBasis_of_finiteDimensional _ b, tsum_fintype,
    tsum_fintype, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => T.apply_norm_sq_eq_inner_adjoint_right (b i)
omit [CompleteSpace H] [FiniteDimensional ℂ H] in
private theorem tr_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (T : H →L[ℂ] H) : tr T = ∑ i, (⟪b i, T (b i)⟫_ℂ).re := by
  rw [tr, LinearMap.trace_eq_sum_inner _ b]
  exact map_sum Complex.reAddGroupHom _ _
private theorem scalar_estimate {r p k : ℝ} (hr : 0 ≤ r) (hp : 0 < p)
    (hpk : 1 ≤ p * k) : 3 * r ^ 2 ≤ (r ^ 2 * k) ^ 2 + 2 * (r * p) := by
  have h₁ := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hpk 2
  have h₂ : 0 ≤ r * (r - p) ^ 2 * (r + 2 * p) := by positivity
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left _ (show 0 < p ^ 2 by positivity)
  calc
    _ = r ^ 4 * ((p * k) ^ 2 - 1) + r * (r - p) ^ 2 * (r + 2 * p) := by ring
    _ ≥ 0 := add_nonneg (mul_nonneg (by positivity) (by linarith)) h₂
set_option maxHeartbeats 1200000 in -- Trace expansion uses the CFC and spectral instances.
private theorem finite_unit_estimate {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hunit : IsUnit A) (hW : IsHilbertSchmidt W)
    (hD : B - A = quarterRoot A * W * quarterRoot A) :
    hsSq (CFC.sqrt B - CFC.sqrt A) (finite_hs _) ≤ hsSq W hW := by
  let P := CFC.sqrt A
  let Q := CFC.sqrt B
  have hP : IsSelfAdjoint P := adjoint_nonneg (CFC.sqrt_nonneg A)
  have hQ : IsSelfAdjoint Q := adjoint_nonneg (CFC.sqrt_nonneg B)
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff P (CFC.sqrt_nonneg A)).2
    ((CFC.isUnit_sqrt_iff A hA).2 hunit)
  let R : H →L[ℂ] H := u
  let S : H →L[ℂ] H := ↑u⁻¹
  have hR : IsSelfAdjoint R := by
    rw [show R = CFC.sqrt P from hu]
    exact adjoint_nonneg (CFC.sqrt_nonneg P)
  have hS : IsSelfAdjoint S := by
    have hu' : IsSelfAdjoint u := Units.ext hR.star_eq
    exact congrArg Units.val hu'.inv.star_eq
  have hRS : R * S = 1 := u.val_inv
  have hSR : S * R = 1 := u.inv_val
  have hRP : R * R = P := by rw [show R = quarterRoot A from hu]; exact CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
  have hPA : P * P = A := CFC.sqrt_mul_sqrt_self A hA
  have hQB : Q * Q = B := CFC.sqrt_mul_sqrt_self B hB
  let V := Q * S
  let X := star V * V
  let U := V * star V
  have hV : star V = S * Q := by simp [V, hS.star_eq, hQ.star_eq]
  have hW' : W = X - P := by
    have he : B - A = R * W * R := by simpa only [show R = quarterRoot A from hu] using hD
    have ha : S * A * S = P := by
      rw [← hPA, ← hRP]
      simp only [mul_assoc, hRS, mul_one]
      simp only [← mul_assoc, hSR, one_mul]
    calc
      W = S * (R * W * R) * S := by
        calc
          W = (S * R) * W * (R * S) := by rw [hSR, hRS, one_mul, mul_one]
          _ = _ := by noncomm_ring
      _ = X - P := by
        rw [← he, mul_sub, sub_mul, ha, ← hQB]
        simp only [X, hV, V]
        noncomm_ring
  have hX : IsSelfAdjoint X := IsSelfAdjoint.star_mul_self V
  have hU : IsSelfAdjoint U := IsSelfAdjoint.mul_star_self V
  have hXP : tr (X * P) = tr B := by
    have he : X * P = S * (B * R) := by
      simp only [X, hV, V, ← hQB]
      calc
        _ = S * ((Q * Q) * (S * P)) := by noncomm_ring
        _ = _ := by rw [← hRP, show S * (R * R) = R by rw [← mul_assoc, hSR, one_mul]]
    rw [he, tr_cycle, mul_assoc, hRS, mul_one]
  have hXX : tr (X * X) = tr (U * U) := by
    change tr (star V * V * (star V * V)) = tr (V * star V * (V * star V))
    rw [mul_assoc (star V) V, tr_cycle]
    exact congrArg tr (by noncomm_ring)
  have hdiff : hsSq W hW - hsSq (Q - P) (finite_hs _) =
      tr (U * U) - 3 * tr B + 2 * tr (Q * P) := by
    rw [hsSq_trace, hsSq_trace, hW']
    change tr (star (X - P) * (X - P)) - tr (star (Q - P) * (Q - P)) = _
    simp only [star_sub, hX.star_eq, hP.star_eq, hQ.star_eq, sub_mul, mul_sub,
      tr_sub, hXX, hXP, hQB]
    rw [tr_cycle P X, tr_cycle P Q, hXP]
    ring
  let q := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg B)).toLinearMap
  let b := q.isSymmetric.eigenvectorBasis rfl
  let r := q.isSymmetric.eigenvalues rfl
  have he (j) : Q (b j) = (r j : ℂ) • b j :=
    q.isSymmetric.apply_eigenvectorBasis rfl j
  have hj (j) : ‖b j‖ = 1 := b.orthonormal.1 j
  have hcol (j) : 3 * (⟪b j, B (b j)⟫_ℂ).re ≤
      (⟪b j, (U * U) (b j)⟫_ℂ).re + 2 * (⟪b j, (Q * P) (b j)⟫_ℂ).re := by
    let x := b j
    let p := ‖R x‖ ^ 2
    let k := ‖S x‖ ^ 2
    have hx : ‖x‖ = 1 := hj j
    have hp : 0 < p := by
      have hn : R x ≠ 0 := fun hz => by
        have e := DFunLike.congr_fun hSR x
        simp [hz] at e
        simp [← e] at hx
      exact pow_pos (norm_pos_iff.mpr hn) _
    have hpk : 1 ≤ p * k := by
      have hi : ⟪R x, S x⟫_ℂ = ⟪x, x⟫_ℂ := by
        rw [← adjoint_inner_right, show R.adjoint = R from hR]
        exact congrArg (fun y : H => ⟪x, y⟫_ℂ) (DFunLike.congr_fun hRS x)
      have hh := norm_inner_le_norm (𝕜 := ℂ) (R x) (S x)
      rw [hi, inner_self_eq_norm_sq_to_K] at hh
      have hh' : 1 ≤ ‖R x‖ * ‖S x‖ := by simpa [hx] using hh
      simpa only [p, k, mul_pow, one_pow] using pow_le_pow_left₀ zero_le_one hh' 2
    have hqx : Q x = (r j : ℂ) • x := he j
    have hb : (⟪x, B x⟫_ℂ).re = r j ^ 2 := by
      have hh := Q.apply_norm_sq_eq_inner_adjoint_right x
      rw [show Q.adjoint = Q from hQ] at hh
      rw [← hQB, show (⟪x, (Q * Q) x⟫_ℂ).re = ‖Q x‖ ^ 2 from hh.symm, hqx]
      simp [norm_smul, hx]
    have hqp : (⟪x, (Q * P) x⟫_ℂ).re = r j * p := by
      change (⟪x, Q (P x)⟫_ℂ).re = _
      rw [← adjoint_inner_left, show Q.adjoint = Q from hQ, hqx,
        inner_smul_left, Complex.conj_ofReal]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      congr 1
      dsimp only [p]
      rw [apply_norm_sq_eq_inner_adjoint_right, show R.adjoint = R from hR]
      exact congrArg (fun T : H →L[ℂ] H => (⟪x, T x⟫_ℂ).re) hRP.symm
    have hv : ‖V.adjoint x‖ ^ 2 = r j ^ 2 * k := by
      change ‖(star V) x‖ ^ 2 = _
      rw [hV, mul_apply_eq_comp, hqx, map_smul, norm_smul, mul_pow]
      simp [k]
    have hdiag : (⟪x, U x⟫_ℂ).re = r j ^ 2 * k := by
      rw [← hv, apply_norm_sq_eq_inner_adjoint_right, adjoint_adjoint]
      rfl
    have hnorm : (r j ^ 2 * k) ^ 2 ≤ ‖U x‖ ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← hdiag]
      exact (Complex.re_le_norm _).trans (by simpa [hx] using norm_inner_le_norm (𝕜 := ℂ) x (U x))
    have huu := U.apply_norm_sq_eq_inner_adjoint_right x
    rw [show U.adjoint = U from hU] at huu
    change 3 * (⟪x, B x⟫_ℂ).re ≤ (⟪x, (U * U) x⟫_ℂ).re + 2 * (⟪x, (Q * P) x⟫_ℂ).re
    rw [hb, hqp, show (⟪x, (U * U) x⟫_ℂ).re = ‖U x‖ ^ 2 from huu.symm]
    exact (scalar_estimate (q.nonneg_eigenvalues rfl j) hp hpk).trans (add_le_add_left hnorm _)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcol j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← tr_basis b, ← tr_basis b, ← tr_basis b] at hsum
  linarith
end Finite

omit [CompleteSpace H] in
private theorem strong_apply {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H}
    {S : H →L[ℂ] H} {R : ℝ} (hR : ∀ i, ‖T i‖ ≤ R)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x)))
    {y : ι → H} {x : H} (hy : Tendsto y l (𝓝 x)) :
    Tendsto (fun i => T i (y i)) l (𝓝 (S x)) := by
  have h₀ := tendsto_iff_norm_sub_tendsto_zero.mp hy
  have hv : Tendsto (fun i => T i (y i - x)) l (𝓝 0) :=
    squeeze_zero_norm (fun i => ((T i).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hR i) (norm_nonneg _))) (by simpa using h₀.const_mul R)
  simpa only [map_sub, sub_add_cancel, zero_add] using hv.add (hT x)
private theorem strong_sqrt {ι : Type*} {l : Filter ι} {T : ι → H →L[ℂ] H}
    {S : H →L[ℂ] H} {R : ℝ} (hR : ∀ i, ‖T i‖ ≤ R) (hSnorm : ‖S‖ ≤ R)
    (hTpos : ∀ i, 0 ≤ T i) (hS : 0 ≤ S)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => CFC.sqrt (T i) x) l (𝓝 (CFC.sqrt S x)) := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    have : ∀ i, CFC.sqrt (T i) x = CFC.sqrt S x := fun _ => Subsingleton.elim _ _
    simpa only [this] using (tendsto_const_nhds (x := CFC.sqrt S x) (f := l))
  | inr h =>
    have hpow (n : ℕ) : Tendsto (fun i => (T i ^ n) x) l (𝓝 ((S ^ n) x)) := by
      induction n with
      | zero => simp [tendsto_const_nhds]
      | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using strong_apply hR hT ih
    have hpoly (q : ℝ[X]) : Tendsto (fun i => (Polynomial.aeval (T i) q) x) l
        (𝓝 ((Polynomial.aeval S q) x)) := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simpa only [map_add, add_apply] using hp.add hq
      | monomial n a =>
        simpa only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
          smul_mul_assoc, one_mul, smul_apply] using (hpow n).const_smul a
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ := ε / (4 * (‖x‖ + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 R Real.sqrt
      Real.continuous_sqrt.continuousOn δ hδ
    have happrox (A : H →L[ℂ] H) (ha : 0 ≤ A) (hn : ‖A‖ ≤ R) :
        ‖Polynomial.aeval A q - CFC.sqrt A‖ ≤ δ := by
      have hsa : IsSelfAdjoint A := adjoint_nonneg ha
      rw [CFC.sqrt_eq_real_sqrt A ha, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn Real.sqrt_zero,
        ← cfc_polynomial q A hsa, ← cfc_sub q.eval Real.sqrt A]
      apply norm_cfc_le hδ.le
      intro t ht
      have ht₀ := spectrum_nonneg_of_nonneg ha ht
      have htR := (spectrum.norm_le_norm_of_mem ht).trans hn
      exact (hq t ⟨ht₀, by simpa [Real.norm_eq_abs, abs_of_nonneg ht₀] using htR⟩).le
    have hb (A : H →L[ℂ] H) (ha : 0 ≤ A) (hn : ‖A‖ ≤ R) :
        dist ((Polynomial.aeval A q) x) (CFC.sqrt A x) ≤ ε / 4 := by
      rw [dist_eq_norm, ← sub_apply]
      refine ((Polynomial.aeval A q - CFC.sqrt A).le_opNorm x).trans
        ((mul_le_mul_of_nonneg_right (happrox A ha hn) (norm_nonneg _)).trans ?_)
      calc
        δ * ‖x‖ ≤ δ * (‖x‖ + 1) := by gcongr; linarith
        _ = ε / 4 := by dsimp [δ]; field_simp
    filter_upwards [Metric.tendsto_nhds.mp (hpoly q) (ε / 2) (by positivity)] with i hi
    have h₁ := dist_triangle (CFC.sqrt (T i) x) ((Polynomial.aeval (T i) q) x) (CFC.sqrt S x)
    have h₂ := dist_triangle ((Polynomial.aeval (T i) q) x) ((Polynomial.aeval S q) x) (CFC.sqrt S x)
    have h₃ := hb (T i) (hTpos i) (hR i)
    have h₄ := hb S hS hSnorm
    rw [dist_comm] at h₃
    linarith

private theorem shift_unit (A : H →L[ℂ] H) (hA : 0 ≤ A) (ε : ℝ≥0) (hε : 0 < ε) :
    IsUnit (A + (ε : ℝ) • 1) := by
  apply isUnit_of_forall_le_norm_inner_map _ hε
  intro x
  have h : 0 ≤ A.reApplyInnerSelf x := (nonneg_iff_isPositive.mp hA).re_inner_nonneg_left x
  calc
    _ ≤ (A + (ε : ℝ) • 1).reApplyInnerSelf x := by
      rw [show (A + (ε : ℝ) • 1).reApplyInnerSelf x = A.reApplyInnerSelf x +
        ((ε : ℝ) • (1 : H →L[ℂ] H)).reApplyInnerSelf x by simp [reApplyInnerSelf, inner_add_left]]
      rw [form_smul, form_one]
      linarith
    _ ≤ _ := Complex.re_le_norm _
private theorem shift_factor {A E W : H →L[ℂ] H} (h : A ≤ E) (hW : IsHilbertSchmidt W) :
    ∃ Z : H →L[ℂ] H, quarterRoot A * W * quarterRoot A =
      quarterRoot E * adjointCongr Z W * quarterRoot E ∧
      ∃ hZ : IsHilbertSchmidt (adjointCongr Z W), hsSq (adjointCongr Z W) hZ ≤ hsSq W hW := by
  have ha := CFC.sqrt_nonneg A
  have he := CFC.sqrt_nonneg E
  have hs := (form_le (adjoint_nonneg ha) (adjoint_nonneg he)).mp (CFC.sqrt_le_sqrt A E h)
  obtain ⟨Z, hz, hf⟩ := exists_bounded_factor (quarterRoot A) (quarterRoot E) zero_le_one
    (fun x => by simpa only [one_mul, form_sqrt _ ha, form_sqrt _ he] using
      (pow_le_pow_iff_left₀ (norm_nonneg (quarterRoot A x)) (norm_nonneg (quarterRoot E x))
        (by decide : 2 ≠ 0)).mp (by simpa only [form_sqrt _ ha, form_sqrt _ he] using hs x))
  obtain ⟨hw, hle⟩ := adjointCongr_hsSq_le Z hW
  refine ⟨Z, ?_, hw, hle.trans ?_⟩
  · have hh := factor_congr (adjoint_nonneg (CFC.sqrt_nonneg (CFC.sqrt A)))
      (adjoint_nonneg (CFC.sqrt_nonneg (CFC.sqrt E))) (C := (1 : H →L[ℂ] H)) (M := W)
      (by simpa only [one_def, comp_id] using hf)
    simpa only [adjointCongr, one_def, adjoint_id, comp_id, id_comp] using hh
  · simpa using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz 4) (hsSq_nonneg hW)

set_option maxHeartbeats 1200000 in -- Elaborate the finite regularization and limit.
/-- The sharp constant-one estimate on any finite-dimensional complex Hilbert space. -/
theorem finite_quarterPower_sqrt_hsSq_le [FiniteDimensional ℂ H]
    {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : IsHilbertSchmidt W)
    (hD : B - A = quarterRoot A * W * quarterRoot A) :
    ∃ hΔ : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A),
      hsSq (CFC.sqrt B - CFC.sqrt A) hΔ ≤ hsSq W hW := by
  let ε (n : ℕ) : ℝ≥0 := ⟨1 / (n + 1 : ℝ), by positivity⟩
  have hε (n : ℕ) : 0 < ε n := by change 0 < 1 / (n + 1 : ℝ); positivity
  have hεle (n : ℕ) : (ε n : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let shift (S : H →L[ℂ] H) (n : ℕ) := S + (ε n : ℝ) • 1
  have hmono (S : H →L[ℂ] H) (n : ℕ) : S ≤ shift S n :=
    le_add_of_nonneg_right (smul_nonneg (ε n).coe_nonneg zero_le_one)
  have hpos (S : H →L[ℂ] H) (hS : 0 ≤ S) (n : ℕ) : 0 ≤ shift S n := hS.trans (hmono S n)
  have hlim (S : H →L[ℂ] H) (hS : 0 ≤ S) (x : H) :
      Tendsto (fun n => CFC.sqrt (shift S n) x) atTop (𝓝 (CFC.sqrt S x)) := by
    apply strong_sqrt (R := ‖S‖ + 1) _ (by linarith) (hpos S hS) hS _ x
    · intro n
      apply (norm_add_le _ _).trans
      gcongr
      rw [norm_smul, Real.norm_of_nonneg (ε n).coe_nonneg]
      have hone : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := opNorm_le_bound _ zero_le_one (by simp [one_def])
      simpa using mul_le_mul (hεle n) hone (norm_nonneg _) zero_le_one
    · intro y
      have ht : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [shift] using (tendsto_const_nhds (x := S y)).add (ht.smul_const y)
  have hbound (n : ℕ) : hsSq (CFC.sqrt (shift B n) - CFC.sqrt (shift A n)) (finite_hs _) ≤
      hsSq W hW := by
    obtain ⟨Z, hf, hz, hle⟩ := shift_factor (hmono A n) hW
    have he : shift B n - shift A n = quarterRoot (shift A n) * adjointCongr Z W *
        quarterRoot (shift A n) := by
      dsimp only [shift]
      rw [add_sub_add_right_eq_sub, hD, hf]
    exact (finite_unit_estimate (hpos A hA n) (hpos B hB n)
      (shift_unit A hA _ (hε n)) hz he).trans hle
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let : Finite w := b.orthonormal.linearIndependent.finite
  let : Fintype w := Fintype.ofFinite w
  refine ⟨finite_hs _, ?_⟩
  rw [hsSq_eq _ b, tsum_fintype]
  have hsum := tendsto_finsetSum (s := Finset.univ) (fun i : w => fun _ =>
    (((hlim B hB (b i)).sub (hlim A hA (b i))).norm.pow 2))
  apply le_of_tendsto' hsum
  intro n
  have hn := hbound n
  rw [hsSq_eq (finite_hs _) b, tsum_fintype] at hn
  simpa only [sub_apply] using hn
/-- The scalar pair (A=1, B=0) attains the sharp squared bound. -/
theorem quarterPower_sqrt_sharp :
    let A : ℂ →L[ℂ] ℂ := 1
    let B : ℂ →L[ℂ] ℂ := 0
    let W : ℂ →L[ℂ] ℂ := -1
    0 ≤ A ∧ 0 ≤ B ∧ B - A = quarterRoot A * W * quarterRoot A ∧
      ∃ (hW : IsHilbertSchmidt W) (hΔ : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A)),
        hsSq (CFC.sqrt B - CFC.sqrt A) hΔ = 1 ∧ hsSq W hW = 1 := by
  dsimp only
  have hW : IsHilbertSchmidt (-1 : ℂ →L[ℂ] ℂ) := finite_hs _
  have h : hsSq (-1 : ℂ →L[ℂ] ℂ) hW = 1 := by
    rw [hsSq_trace]
    simp [tr, adjoint_one]
  refine ⟨zero_le_one, le_rfl, by simp [quarterRoot], hW, finite_hs _, ?_, h⟩
  simpa only [CFC.sqrt_zero, CFC.sqrt_one, zero_sub] using h

omit [CompleteSpace H] in
private theorem finite_projection_tendsto {w : Set H} (b : HilbertBasis w ℂ H) (x : H) :
    Tendsto (fun F : Finset w => (TraceClassCompression.finiteSpan b F).starProjection x)
      atTop (𝓝 x) := by
  let y (F : Finset w) := ∑ i ∈ F, b.repr x i • b i
  have hy : Tendsto y atTop (𝓝 x) := b.hasSum_repr x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_iff_norm_sub_tendsto_zero.mp hy)
  intro F
  let U := TraceClassCompression.finiteSpan b F
  have hm : y F ∈ U := Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, hi, rfl⟩)
  rw [norm_sub_rev, ← dist_eq_norm, U.dist_starProjection_eq_infDist, ← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem hm
set_option maxHeartbeats 800000 in -- Elaborate CFC on the subspace and ambient space.
private theorem sqrt_compression (U : Submodule ℂ H) [CompleteSpace U]
    (A : H →L[ℂ] H) (hA : 0 ≤ A) :
    CFC.sqrt (U.starProjection * A * U.starProjection) =
      adjointCongr U.subtypeL.adjoint (CFC.sqrt (adjointCongr U.subtypeL A)) := by
  let i := U.subtypeL
  have hi : i.adjoint ∘L i = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change U.subtypeL.adjoint (U.subtypeL x) = x
    rw [U.adjoint_subtypeL]
    exact U.orthogonalProjectionOnto_mem_subspace_eq_self x
  have hp : U.starProjection = i ∘L i.adjoint := by
    change U.starProjection = U.subtypeL ∘L U.subtypeL.adjoint
    rw [U.adjoint_subtypeL]
    rfl
  let S := CFC.sqrt (adjointCongr i A)
  have hS : S * S = adjointCongr i A := CFC.sqrt_mul_sqrt_self _ (congr_nonneg hA i)
  change CFC.sqrt (U.starProjection * A * U.starProjection) = adjointCongr i.adjoint S
  apply CFC.sqrt_unique _ (congr_nonneg (CFC.sqrt_nonneg (adjointCongr i A)) i.adjoint)
  simp only [adjointCongr, adjoint_adjoint, mul_def, hp]
  change (i ∘L S ∘L i.adjoint) ∘L (i ∘L S ∘L i.adjoint) = _
  have he : (i ∘L S ∘L i.adjoint) ∘L (i ∘L S ∘L i.adjoint) =
      i ∘L (S * S) ∘L i.adjoint := by
    have h (x : U) : i.adjoint (i x) = x := DFunLike.congr_fun hi x
    ext x
    simp [comp_apply, h]
  rw [he, hS]
  simp only [adjointCongr, comp_assoc]
private theorem conjugate_contraction {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    {C : K →L[ℂ] H} (hC : ‖C‖ ≤ 1) :
    ∃ h : IsHilbertSchmidt (adjointCongr C S), hsSq (adjointCongr C S) h ≤ hsSq S hS := by
  obtain ⟨h, hh⟩ := adjointCongr_hsSq_le C hS
  exact ⟨h, hh.trans (by simpa using
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hC 4) (hsSq_nonneg hS))⟩

set_option maxHeartbeats 1200000 in -- Elaborate the varying finite subspaces and their CFCs.
/-- The sharp constant-one estimate on an arbitrary complex Hilbert space. -/
theorem quarterPower_sqrt_hsSq_le {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : IsHilbertSchmidt W) (hD : B - A = quarterRoot A * W * quarterRoot A) :
    ∃ hΔ : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A),
      hsSq (CFC.sqrt B - CFC.sqrt A) hΔ ≤ hsSq W hW := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let U := TraceClassCompression.finiteSpan b
  let P (F : Finset w) := (U F).starProjection
  let D := CFC.sqrt B - CFC.sqrt A
  let d (F : Finset w) := CFC.sqrt (P F * B * P F) - CFC.sqrt (P F * A * P F)
  have hbound (F : Finset w) : ∃ hd : IsHilbertSchmidt (d F), hsSq (d F) hd ≤ hsSq W hW := by
    let i := (U F).subtypeL
    have hi : ‖i‖ ≤ 1 := (U F).norm_subtypeL_le
    obtain ⟨Z, _, _, hf, hw, hle⟩ := quarterPower_congruence hA hB hW hD i
    rw [congr_sub] at hf
    obtain ⟨hd, hh⟩ := finite_quarterPower_sqrt_hsSq_le (congr_nonneg hA i)
      (congr_nonneg hB i) hw hf
    obtain ⟨ho, hho⟩ := conjugate_contraction hd (C := i.adjoint) (by simpa using hi)
    have he : d F = adjointCongr i.adjoint
        (CFC.sqrt (adjointCongr i B) - CFC.sqrt (adjointCongr i A)) := by
      change CFC.sqrt ((U F).starProjection * B * (U F).starProjection) -
        CFC.sqrt ((U F).starProjection * A * (U F).starProjection) = _
      rw [sqrt_compression _ B hB, sqrt_compression _ A hA, ← congr_sub]
    rw [he]
    have hc : ‖i‖ ^ 2 * hsSq W hW ≤ hsSq W hW := by
      simpa using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg i) hi 2) (hsSq_nonneg hW)
    exact ⟨ho, hho.trans (hh.trans (hle.trans hc))⟩
  have hs (S : H →L[ℂ] H) (hS : 0 ≤ S) (x : H) :
      Tendsto (fun F => CFC.sqrt (P F * S * P F) x) atTop (𝓝 (CFC.sqrt S x)) := by
    apply strong_sqrt (R := ‖S‖) (T := fun F => P F * S * P F) _ le_rfl _ hS _ x
    · intro F
      have hp := (U F).starProjection_norm_le
      calc
        ‖P F * S * P F‖ ≤ (‖P F‖ * ‖S‖) * ‖P F‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ ‖S‖ := by
          simpa using mul_le_mul (mul_le_mul_of_nonneg_right hp (norm_nonneg S)) hp (norm_nonneg _) (by positivity : 0 ≤ 1 * ‖S‖)
    · intro F
      exact (congr_nonneg hS (P F)).trans_eq (by
        rw [adjointCongr, show (P F).adjoint = P F from isSelfAdjoint_starProjection (U F)]
        rfl)
    · intro y
      exact strong_apply (fun F => (U F).starProjection_norm_le)
        (T := P) (S := (1 : H →L[ℂ] H)) (finite_projection_tendsto b)
        (S.continuous.continuousAt.tendsto.comp (finite_projection_tendsto b y))
  have hlim (x : H) : Tendsto (fun F => d F x) atTop (𝓝 (D x)) :=
    (hs B hB x).sub (hs A hA x)
  have hfinite (E : Finset w) : ∑ j ∈ E, ‖D (b j)‖ ^ 2 ≤ hsSq W hW := by
    apply le_of_tendsto' (tendsto_finsetSum (s := E) fun j _ => (hlim (b j)).norm.pow 2)
    intro F
    obtain ⟨h, hh⟩ := hbound F
    rw [hsSq_eq h b] at hh
    exact ((summable_norm_sq_apply_of_hilbertBasis w b h).sum_le_tsum E
      (fun _ _ => sq_nonneg _)).trans hh
  have hd : IsHilbertSchmidt D := ⟨w, b, summable_of_sum_le (fun _ => sq_nonneg _) hfinite⟩
  exact ⟨hd, (hsSq_eq hd b).trans_le (Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite)⟩
/-- The norm estimate with sharp constant one and its (sqrt 2) consequence. -/
theorem quarterPower_sqrt_hsNorm_le {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : IsHilbertSchmidt W) (hD : B - A = quarterRoot A * W * quarterRoot A) :
    ∃ hΔ : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A),
      Real.sqrt (hsSq (CFC.sqrt B - CFC.sqrt A) hΔ) ≤ Real.sqrt (hsSq W hW) ∧
      Real.sqrt (hsSq (CFC.sqrt B - CFC.sqrt A) hΔ) ≤ Real.sqrt 2 * Real.sqrt (hsSq W hW) := by
  obtain ⟨h, hh⟩ := quarterPower_sqrt_hsSq_le hA hB hW hD
  have hnorm := Real.sqrt_le_sqrt hh
  refine ⟨h, hnorm, hnorm.trans ?_⟩
  simpa using mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num))
    (Real.sqrt_nonneg (hsSq W hW))
/-- The square of the root difference is trace class. -/
theorem quarterPower_sqrt_sq_isTraceClass {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : IsHilbertSchmidt W) (hD : B - A = quarterRoot A * W * quarterRoot A) :
    IsTraceClass ((CFC.sqrt B - CFC.sqrt A) * (CFC.sqrt B - CFC.sqrt A)) := by
  obtain ⟨h, _⟩ := quarterPower_sqrt_hsSq_le hA hB hW hD
  exact isTraceClass_mul_of_isHilbertSchmidt h h
/-- The square-root estimate after an arbitrary bounded congruence. -/
theorem quarterPower_congruence_sqrt_hsSq_le {A B W : H →L[ℂ] H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hW : IsHilbertSchmidt W) (hD : B - A = quarterRoot A * W * quarterRoot A) (C : K →L[ℂ] H) :
    ∃ h : IsHilbertSchmidt (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A)),
      hsSq _ h ≤ ‖C‖ ^ 2 * hsSq W hW := by
  obtain ⟨Z, _, _, hf, hw, hle⟩ := quarterPower_congruence hA hB hW hD C
  rw [congr_sub] at hf
  obtain ⟨h, hh⟩ := quarterPower_sqrt_hsSq_le (congr_nonneg hA C) (congr_nonneg hB C) hw hf
  exact ⟨h, hh.trans hle⟩

set_option maxHeartbeats 1000000 in -- Elaborate the order and CFC on bounded endomorphisms.
/-- Compact perturbations of the identity are coercive under the two signed order bounds. -/
theorem compact_add_one_coercive {T J : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hTsa : IsSelfAdjoint T) (_hJsa : IsSelfAdjoint J) (hJ : J.ker = ⊥)
    (hp : 0 ≤ 1 + T + J) (hm : 0 ≤ 1 + T - J) :
    (1 + T : H →L[ℂ] H).ker = ⊥ ∧
      ∃ c : ℝ, 0 < c ∧ c • (1 : H →L[ℂ] H) ≤ 1 + T := by
  let N : H →L[ℂ] H := 1 + T
  have hNsa : IsSelfAdjoint N := (IsSelfAdjoint.one _).add hTsa
  have hforms (x : H) :
      (N + J).reApplyInnerSelf x = N.reApplyInnerSelf x + J.reApplyInnerSelf x ∧
      (N - J).reApplyInnerSelf x = N.reApplyInnerSelf x - J.reApplyInnerSelf x := by
    simp [reApplyInnerSelf, inner_add_left, inner_sub_left]
  have hN : 0 ≤ N := by
    apply nonneg_iff_isPositive.mpr (isPositive_def'.mpr ⟨hNsa, fun x => ?_⟩)
    have ha := (nonneg_iff_isPositive.mp hp).re_inner_nonneg_left x
    have hb := (nonneg_iff_isPositive.mp hm).re_inner_nonneg_left x
    change 0 ≤ (N + J).reApplyInnerSelf x at ha
    change 0 ≤ (N - J).reApplyInnerSelf x at hb
    rw [(hforms x).1] at ha
    rw [(hforms x).2] at hb
    linarith
  have hker : N.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : N x = 0 := hx
    have hzero : N.reApplyInnerSelf x = 0 := by simp [reApplyInnerSelf, hx']
    have ha := form_sqrt (N + J) hp x
    have hb := form_sqrt (N - J) hm x
    rw [(hforms x).1, hzero] at ha
    rw [(hforms x).2, hzero] at hb
    have hz : CFC.sqrt (N + J) x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖CFC.sqrt (N - J) x‖]
    have hj : J x = 0 := by
      have hh := DFunLike.congr_fun (CFC.sqrt_mul_sqrt_self (N + J) hp) x
      simpa [mul_apply_eq_comp, hz, hx'] using hh.symm
    exact hJ ▸ (show x ∈ J.ker from hj)
  have heig : ¬ Module.End.HasEigenvalue T.toLinearMap (-1) := by
    intro he
    obtain ⟨x, hx, hne⟩ := (Submodule.ne_bot_iff _).mp (Module.End.hasEigenvalue_iff.mp he)
    have hh : T x = (-1 : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx
    have hmem : x ∈ N.ker := show (1 + T) x = 0 by simp [hh]
    rw [hker, Submodule.mem_bot] at hmem
    exact hne hmem
  have hl : ∃ K, AntilipschitzWith K N := by
    simpa [N, sub_eq_add_neg, add_comm] using hT.antilipschitz_of_not_hasEigenvalue
      (show (-1 : ℂ) ≠ 0 by norm_num) heig
  obtain ⟨d, hd, hnorm⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp hl
  let R := ‖N‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hupper : N ≤ R • (1 : H →L[ℂ] H) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (IsSelfAdjoint.le_algebraMap_norm_self N hNsa).trans
      (algebraMap_mono _ (show ‖N‖ ≤ R from le_add_of_nonneg_right zero_le_one))
  have hquad : N * N ≤ R • N := by
    have hh := CFC.conjSqrt_monotone (c := N) hupper
    have hc : CFC.sqrt N * N * CFC.sqrt N = N * N := by
      set P := CFC.sqrt N
      have hP : P * P = N := CFC.sqrt_mul_sqrt_self N hN
      rw [← hP]
      noncomm_ring
    simpa only [CFC.conjSqrt_apply, hc, mul_smul_comm, mul_one, smul_mul_assoc,
      CFC.sqrt_mul_sqrt_self N hN] using hh
  refine ⟨hker, d ^ 2 / R, by positivity, ?_⟩
  apply (form_le ((IsSelfAdjoint.all (d ^ 2 / R)).smul (IsSelfAdjoint.one _)) hNsa).mpr
  intro x
  have hsa : IsSelfAdjoint (N * N) := by simp [IsSelfAdjoint, star_mul, hNsa.star_eq]
  have hq := (form_le hsa ((IsSelfAdjoint.all R).smul hNsa)).mp hquad x
  have hh := N.apply_norm_sq_eq_inner_adjoint_left x
  rw [show N.adjoint = N from hNsa] at hh
  change ‖N x‖ ^ 2 = (N * N).reApplyInnerSelf x at hh
  have hn := pow_le_pow_left₀ (mul_nonneg hd.le (norm_nonneg x)) (hnorm x) 2
  rw [mul_pow, hh] at hn
  rw [form_smul] at hq ⊢
  rw [form_one, div_mul_eq_mul_div, div_le_iff₀ hR]
  linarith
/-- A Hilbert–Schmidt perturbation satisfies the same coercivity criterion. -/
theorem hilbertSchmidt_add_one_coercive {T J : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hTsa : IsSelfAdjoint T) (hJsa : IsSelfAdjoint J) (hJ : J.ker = ⊥)
    (hp : 0 ≤ 1 + T + J) (hm : 0 ≤ 1 + T - J) :
    (1 + T : H →L[ℂ] H).ker = ⊥ ∧
      ∃ c : ℝ, 0 < c ∧ c • (1 : H →L[ℂ] H) ≤ 1 + T :=
  compact_add_one_coercive (isCompactOperator_of_isHilbertSchmidt hT) hTsa hJsa hJ hp hm

end D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
