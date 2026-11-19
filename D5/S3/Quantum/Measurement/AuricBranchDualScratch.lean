import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Weighted branch-score bound used in the AURIC flagged projective-distance argument,
Lemma 3.2 and equation (3) of the five-level optimality proof. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

namespace D5.S3.Quantum.Measurement.AuricBranchDual

variable {e h j : Type*} [Fintype e] [Fintype h]

private theorem hilbertSchmidt_cauchySchwarz (A B : Matrix h e ℂ) :
    ‖(Aᴴ * B).trace‖ ^ 2 ≤ (Aᴴ * A).trace.re * (Bᴴ * B).trace.re := by
  let a : EuclideanSpace ℂ (e × h) := WithLp.toLp 2 A.vec
  let b : EuclideanSpace ℂ (e × h) := WithLp.toLp 2 B.vec
  have hcs := inner_mul_inner_self_le (𝕜 := ℂ) a b
  rw [norm_inner_symm b a, ← pow_two] at hcs
  simp only [EuclideanSpace.inner_eq_star_dotProduct, a, b,
    RCLike.re_eq_complex_re] at hcs
  simpa only [dotProduct_comm B.vec (star A.vec), dotProduct_comm A.vec (star A.vec),
    dotProduct_comm B.vec (star B.vec),
    Matrix.star_vec_dotProduct_vec, RCLike.re_eq_complex_re] using hcs

private theorem weightedGram_trace (A : Matrix h e ℂ) (R : Matrix e e ℂ)
    (hR : R.IsHermitian) :
    ((A * R)ᴴ * (A * R)).trace = (R * R * (Aᴴ * A)).trace := by
  rw [Matrix.conjTranspose_mul, hR.eq,
    ← Matrix.mul_assoc (R * Aᴴ) A R, Matrix.trace_mul_cycle (R * Aᴴ) A R,
    ← Matrix.mul_assoc R R Aᴴ, Matrix.mul_assoc (R * R) Aᴴ A]

/-- Hilbert–Schmidt Cauchy–Schwarz with a positive definite right weight. -/
theorem weighted_trace_pairing_le [DecidableEq e] (L K : Matrix h e ℂ)
    (Y : Matrix e e ℂ) (hY : Y.PosDef) :
    ‖(Lᴴ * K).trace‖ ^ 2 ≤ (Y⁻¹ * (Lᴴ * L)).trace.re * (Y * (Kᴴ * K)).trace.re := by
  let R := CFC.sqrt Y
  have hR : R.PosDef := hY.isStrictlyPositive.sqrt.posDef
  have hRR : R * R = Y := CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hcross : ((L * R⁻¹)ᴴ * (K * R)).trace = (Lᴴ * K).trace := by
    rw [Matrix.conjTranspose_mul, hR.inv.isHermitian.eq,
      ← Matrix.mul_assoc (R⁻¹ * Lᴴ) K R, Matrix.trace_mul_cycle (R⁻¹ * Lᴴ) K R,
      ← Matrix.mul_assoc R R⁻¹ Lᴴ, Matrix.mul_nonsing_inv R hRdet, Matrix.one_mul]
  have hInvSq : R⁻¹ * R⁻¹ = Y⁻¹ := by rw [← Matrix.mul_inv_rev, hRR]
  have hcs := hilbertSchmidt_cauchySchwarz (L * R⁻¹) (K * R)
  rw [hcross, weightedGram_trace L _ hR.inv.isHermitian,
    weightedGram_trace K _ hR.isHermitian, hInvSq, hRR] at hcs
  exact hcs

variable [Fintype j] {κ : j → Type*} [∀ f, Fintype (κ f)]

/-- The sum of terminal trace-pairing scores for a complete flagged Kraus family on a branch. -/
theorem weighted_kraus_branch_score_le [DecidableEq e]
    (L : j → Matrix h e ℂ) (K : ∀ f, κ f → Matrix h e ℂ)
    (hK : (∑ f, ∑ l, (K f l)ᴴ * K f l) = 1)
    (Y : Matrix e e ℂ) (hY : Y.PosDef)
    (hL : ∀ f, (Y⁻¹ * ((L f)ᴴ * L f)).trace.re ≤ 1) :
    (∑ f, ∑ l, ‖((L f)ᴴ * K f l).trace‖ ^ 2) ≤ Y.trace.re := by
  calc
    _ ≤ ∑ f, ∑ l, (Y * ((K f l)ᴴ * K f l)).trace.re := by
      refine Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun l _ => ?_
      let R := CFC.sqrt Y
      have hR : R.PosDef := hY.isStrictlyPositive.sqrt.posDef
      have hRR : R * R = Y := CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg
      have hnonneg : 0 ≤ (Y * ((K f l)ᴴ * K f l)).trace.re := by
        rw [← hRR, ← weightedGram_trace _ R hR.isHermitian]
        exact Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg |>.1
      exact (weighted_trace_pairing_le (L f) (K f l) Y hY).trans
        (mul_le_of_le_one_left hnonneg (hL f))
    _ = Y.trace.re := by
      simp_rw [← Complex.reCLM_apply, ← map_sum, ← Matrix.trace_sum,
        ← Matrix.mul_sum, hK, Matrix.mul_one]

/-- Restriction of square terminal Kraus operators and tests to the
column space of an isometric frame for the first projective outcome. -/
theorem weighted_projective_branch_score_le [DecidableEq e]
    (W : Matrix h e ℂ) (hW : Wᴴ * W = 1)
    (D : j → Matrix h h ℂ) (K : ∀ f, κ f → Matrix h h ℂ)
    (hSupport : ∀ f l, K f l * (W * Wᴴ) = K f l)
    (hK : (∑ f, ∑ l, (K f l)ᴴ * K f l) = W * Wᴴ)
    (Y : Matrix e e ℂ) (hY : Y.PosDef)
    (hD : ∀ f, (Y⁻¹ * ((D f * W)ᴴ * (D f * W))).trace.re ≤ 1) :
    (∑ f, ∑ l, ‖((D f)ᴴ * K f l).trace‖ ^ 2) ≤ Y.trace.re := by
  have hRestricted : (∑ f, ∑ l, (K f l * W)ᴴ * (K f l * W)) = 1 := by
    have hGram (f : j) (l : κ f) :
        (K f l * W)ᴴ * (K f l * W) = Wᴴ * (((K f l)ᴴ * K f l) * W) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [hGram, ← Matrix.mul_sum, ← Matrix.sum_mul]
    simp [hK, Matrix.mul_assoc, hW]
  have hpair (f : j) (l : κ f) :
      ((D f * W)ᴴ * (K f l * W)).trace = ((D f)ᴴ * K f l).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.trace_mul_cycle Wᴴ (D f)ᴴ (K f l * W),
      Matrix.mul_assoc (K f l) W Wᴴ, hSupport,
      Matrix.trace_mul_comm (K f l) (D f)ᴴ]
  simpa only [hpair] using
    weighted_kraus_branch_score_le (fun f => D f * W) (fun f l => K f l * W)
      hRestricted Y hY hD

variable [DecidableEq e]

/-- Evaluation of the flagged Choi matrices against the vectorized tests. -/
def flaggedChoiScore (L : j → Matrix h e ℂ) (Φ : j → MatrixMap e h ℂ) : ℝ :=
  ∑ f, (star (L f).transpose.vec ⬝ᵥ ((Φ f).choi_matrix *ᵥ (L f).transpose.vec)).re

omit [DecidableEq e] in
private theorem choi_rankOne_pairing (L K : Matrix h e ℂ) :
    (star L.transpose.vec ⬝ᵥ
      (Matrix.vecMulVec K.transpose.vec (star K.transpose.vec) *ᵥ L.transpose.vec)).re =
      ‖(Lᴴ * K).trace‖ ^ 2 := by
  have hswap : star L.transpose.vec ⬝ᵥ K.transpose.vec = star L.vec ⬝ᵥ K.vec := by
    simp only [dotProduct, Pi.star_apply, Matrix.vec,
      Matrix.transpose_apply]
    exact Fintype.sum_equiv (Equiv.prodComm h e) _ _ (fun _ => rfl)
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul,
    star_dotProduct (v := K.transpose.vec) (w := L.transpose.vec), hswap,
    Matrix.star_vec_dotProduct_vec]
  simpa only [Complex.star_def, Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
    (congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := (Lᴴ * K).trace))).symm

/-- The Choi score is exactly the sum of squared trace pairings for any
choice of finite Kraus representation of each flag. -/
theorem flaggedChoiScore_of_kraus (L : j → Matrix h e ℂ)
    (K : ∀ f, κ f → Matrix h e ℂ) :
    flaggedChoiScore L (fun f => MatrixMap.of_kraus (K f) (K f)) =
      ∑ f, ∑ l, ‖((L f)ᴴ * K f l).trace‖ ^ 2 := by
  classical
  unfold flaggedChoiScore
  apply Finset.sum_congr rfl
  intro f _
  rw [MatrixMap.choi_of_kraus, Matrix.sum_mulVec, dotProduct_sum]
  rw [← Complex.reCLM_apply, map_sum]
  exact Finset.sum_congr rfl fun l _ => choi_rankOne_pairing (L f) (K f l)

/-- Weighted score bound directly on the flagged CP maps. The sum of the
maps is trace preserving, expressing completeness within this first outcome. -/
theorem weighted_cp_branch_score_le
    (L : j → Matrix h e ℂ) (Φ : j → MatrixMap e h ℂ)
    (hCP : ∀ f, (Φ f).IsCompletelyPositive)
    (hTP : (∑ f, Φ f).IsTracePreserving)
    (Y : Matrix e e ℂ) (hY : Y.PosDef)
    (hL : ∀ f, (Y⁻¹ * ((L f)ᴴ * L f)).trace.re ≤ 1) :
    flaggedChoiScore L Φ ≤ Y.trace.re := by
  classical
  choose K hK using fun f => (hCP f).exists_kraus
  have hComplete : (∑ f, ∑ l, (K f l)ᴴ * K f l) = 1 := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    have htrace (f : j) (l : h × e) :
        (K f l * X * (K f l)ᴴ).trace = ((K f l)ᴴ * K f l * X).trace :=
      Matrix.trace_mul_cycle _ _ _
    have h := hTP X
    simp only [LinearMap.sum_apply, hK, MatrixMap.of_kraus, LinearMap.coe_mk,
      AddHom.coe_mk, Matrix.trace_sum, htrace] at h
    simpa only [Finset.sum_mul, Matrix.trace_sum, Matrix.one_mul] using h
  have hΦ : Φ = fun f => MatrixMap.of_kraus (K f) (K f) := funext hK
  rw [hΦ, flaggedChoiScore_of_kraus]
  exact weighted_kraus_branch_score_le L K hComplete Y hY hL


section Regularized

open Filter Set
open scoped Topology Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real trace of the positive matrix square root. -/
def rootTrace (B : Matrix n n ℂ) : ℝ := (CFC.sqrt B).trace.re

/-- The pointwise variational inequality for the trace of the positive square root. -/
private theorem rootTrace_support {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    2 * (rootTrace B - rootTrace A) ≤ (((CFC.sqrt A)⁻¹) * (B - A)).trace.re := by
  let R := CFC.sqrt A
  let S := CFC.sqrt B
  have hR : R.PosDef := hA.isStrictlyPositive.sqrt.posDef
  have hS : S.PosDef := hB.isStrictlyPositive.sqrt.posDef
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hRi := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hSR : (R⁻¹ * (S * R)).trace = S.trace := by
    rw [Matrix.trace_mul_cycle' R⁻¹ S R, ← Matrix.mul_assoc R R⁻¹ S,
      Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit),
      Matrix.one_mul]
  have hnon := RHLinalg.trace_mul_nonneg_of_posSemidef hR.inv.posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self (S - R))
  have hstar : (S - R)ᴴ = S - R := by
    rw [Matrix.conjTranspose_sub, hS.isHermitian.eq, hR.isHermitian.eq]
  have hexpand : R⁻¹ * ((S - R)ᴴ * (S - R)) = R⁻¹ * B - R⁻¹ * (S * R) - S + R := by
    rw [hstar]
    calc
      _ = R⁻¹ * (S * S) - R⁻¹ * (S * R) - R⁻¹ * (R * S) + R⁻¹ * (R * R) := by
        noncomm_ring
      _ = _ := by
        rw [hSS, ← Matrix.mul_assoc R⁻¹ R S, ← Matrix.mul_assoc R⁻¹ R R, hRi,
          Matrix.one_mul, Matrix.one_mul]
  simp only [hexpand, Matrix.trace_sub, Matrix.trace_add, RCLike.re_eq_complex_re,
    Complex.sub_re, Complex.add_re, hSR] at hnon
  change 2 * (S.trace.re - R.trace.re) ≤ (R⁻¹ * (B - A)).trace.re
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, ← hRR,
    ← Matrix.mul_assoc, hRi, Matrix.one_mul]
  linarith

private theorem rootTrace_continuousOn :
    ContinuousOn (rootTrace (n := n)) {B | B.PosSemidef} := by
  intro B hB
  have hs := (CFC.continuousOn_sqrt (A := Matrix n n ℂ)).continuousWithinAt
    (show 0 ≤ B from (show B.PosSemidef from hB).nonneg)
  exact (Complex.continuous_re.comp continuous_id.matrix_trace).continuousAt.comp_continuousWithinAt
    (hs.mono fun A hA => (show A.PosSemidef from hA).nonneg)

omit [Fintype n] [DecidableEq n] in
private theorem mixture_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (t • A + (1 - t) • B).PosDef := by
  rcases ht.1.eq_or_lt with ht0 | ht0
  · simpa [← ht0] using hB
  · exact (hA.smul ht0).add_posSemidef (hB.posSemidef.smul (sub_nonneg.mpr ht.2))

private theorem inverseRoot_continuousOn :
    ContinuousOn (fun A : Matrix n n ℂ => (CFC.sqrt A)⁻¹) {A | A.PosDef} := by
  intro A hA
  have hR : (CFC.sqrt A).PosDef := (show A.PosDef from hA).isStrictlyPositive.sqrt.posDef
  have hinv : ContinuousAt (fun R : Matrix n n ℂ => R⁻¹) (CFC.sqrt A) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit))
  have hroot := (CFC.continuousOn_sqrt (A := Matrix n n ℂ)).continuousWithinAt
    (show 0 ≤ A from (show A.PosDef from hA).posSemidef.nonneg)
  exact hinv.comp_continuousWithinAt
    (hroot.mono fun X hX => (show X.PosDef from hX).posSemidef.nonneg)

private theorem endpoint_trace_le {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hmax : ∀ t ∈ Icc (0 : ℝ) 1, rootTrace (t • A + (1 - t) • B) ≤ rootTrace B) :
    (((CFC.sqrt B)⁻¹) * A).trace.re ≤ rootTrace B := by
  let M (t : ℝ) := t • A + (1 - t) • B
  have hM : Continuous M := by fun_prop
  have hM0 : M 0 = B := by simp [M]
  have hPD (t : ℝ) (ht : t ∈ Icc 0 1) : (M t).PosDef :=
    mixture_posDef hA hB ht
  let g (t : ℝ) : ℝ := (((CFC.sqrt (M t))⁻¹) * (A - B)).trace.re
  have hg : ContinuousOn g (Icc 0 1) := by
    have h := inverseRoot_continuousOn.comp hM.continuousOn hPD
    exact (Complex.continuous_re.comp continuous_id.matrix_trace).comp_continuousOn
      (h.mul continuousOn_const)
  have hle : g 0 ≤ 0 := by
    have : NeBot (𝓝[Ioo (0 : ℝ) 1] (0 : ℝ)) := left_nhdsWithin_Ioo_neBot zero_lt_one
    apply le_of_tendsto ((hg 0 (left_mem_Icc.mpr zero_le_one)).mono Ioo_subset_Icc_self).tendsto
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' := Ioo_subset_Icc_self ht
    have hs := rootTrace_support (hPD t ht') hB
    have hd : B - M t = (-t) • (A - B) := by
      dsimp [M]
      module
    rw [hd, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hs
    have hdiff : 0 ≤ 2 * (rootTrace B - rootTrace (M t)) := by
      linarith [hmax t ht']
    have hnon : 0 ≤ (-t) * g t := hdiff.trans hs
    exact nonpos_of_mul_nonneg_right hnon (neg_neg_of_pos ht.1)
  dsimp [g] at hle
  rw [hM0, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hle
  have hR : (CFC.sqrt B).PosDef := hB.isStrictlyPositive.sqrt.posDef
  have he : ((CFC.sqrt B)⁻¹ * B).trace.re = rootTrace B := by
    let R := CFC.sqrt B
    have hRR : R * R = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
    change (R⁻¹ * B).trace.re = R.trace.re
    rw [← hRR, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit), Matrix.one_mul]
  linarith

/-- A maximum of the regularized two-test mixture gives the feasible, universally
applicable weight `Y = (Tr √B) • √B`. Its trace is the square of the attained maximum. -/
theorem exists_regularized_dual_weight [Nonempty n]
    (A : Fin 2 → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    let M : ℝ → Matrix n n ℂ := fun t => t • (A 0 + ε • 1) + (1 - t) • (A 1 + ε • 1)
    ∃ t ∈ Icc (0 : ℝ) 1, IsMaxOn (fun s => rootTrace (M s)) (Icc 0 1) t ∧
      let Y := rootTrace (M t) • CFC.sqrt (M t)
      Y.PosDef ∧ (∀ i, (Y⁻¹ * A i).trace.re ≤ 1) ∧ Y.trace.re = rootTrace (M t) ^ 2 := by
  dsimp only
  let C (i : Fin 2) := A i + ε • (1 : Matrix n n ℂ)
  let M (t : ℝ) := t • C 0 + (1 - t) • C 1
  change ∃ t ∈ Icc (0 : ℝ) 1, IsMaxOn (fun s => rootTrace (M s)) (Icc 0 1) t ∧
    let Y := rootTrace (M t) • CFC.sqrt (M t)
    Y.PosDef ∧ (∀ i, (Y⁻¹ * A i).trace.re ≤ 1) ∧ Y.trace.re = rootTrace (M t) ^ 2
  have hC (i : Fin 2) : (C i).PosDef :=
    Matrix.PosDef.posSemidef_add (hA i) (Matrix.PosDef.one.smul hε)
  have hPD (s : ℝ) (hs : s ∈ Icc 0 1) : (M s).PosDef := mixture_posDef (hC 0) (hC 1) hs
  have hM : Continuous M := by fun_prop
  have hcont := rootTrace_continuousOn.comp hM.continuousOn
    (show MapsTo M (Icc 0 1) {B | B.PosSemidef} from fun s hs => (hPD s hs).posSemidef)
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont
  refine ⟨t, ht, hmax, ?_⟩
  let R := CFC.sqrt (M t)
  let f := rootTrace (M t)
  have hR : R.PosDef := (hPD t ht).isStrictlyPositive.sqrt.posDef
  have hf : 0 < f := Complex.pos_iff.mp hR.trace_pos |>.1
  change (f • R).PosDef ∧ (∀ i, ((f • R)⁻¹ * A i).trace.re ≤ 1) ∧
    (f • R).trace.re = f ^ 2
  have hEndpoints (i : Fin 2) : (R⁻¹ * C i).trace.re ≤ f := by
    apply endpoint_trace_le (hC i) (hPD t ht)
    intro s hs
    let endpoint : ℝ := if i = 0 then 1 else 0
    have hendpoint : endpoint ∈ Icc (0 : ℝ) 1 := by
      by_cases hi : i = 0 <;> simp [endpoint, hi]
    let p : ℝ := s * endpoint + (1 - s) * t
    have hp : p ∈ Icc 0 1 := by
      exact convex_Icc (0 : ℝ) 1 hendpoint ht hs.1 (sub_nonneg.mpr hs.2) (by ring)
    have he : s • C i + (1 - s) • M t = M p := by
      fin_cases i <;> simp only [p, endpoint, M, Fin.isValue] <;>
        norm_num <;> module
    rw [he]
    exact hmax hp
  refine ⟨hR.smul hf, fun i => ?_, ?_⟩
  · have htest : (R⁻¹ * A i).trace.re ≤ f := by
      have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hR.inv.posSemidef
        ((Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef).smul hε.le)
      have hi := hEndpoints i
      simp only [C, Matrix.mul_add, Matrix.trace_add, Complex.add_re] at hi
      exact le_trans (le_add_of_nonneg_right hn) hi
    let u : ℂˣ := Units.mk0 (f : ℂ) (by exact_mod_cast hf.ne')
    have hInv : (f • R)⁻¹ = f⁻¹ • R⁻¹ := by
      have hu := Matrix.inv_smul' R u ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
      change (((u : ℂ) • R)⁻¹) = ((↑u⁻¹ : ℂ) • R⁻¹) at hu
      change ((((f : ℂ) • R))⁻¹) = (((f⁻¹ : ℝ) : ℂ) • R⁻¹)
      simpa only [u, Units.val_mk0, Units.val_inv_eq_inv_val, Complex.ofReal_inv] using hu
    rw [hInv, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left htest (inv_nonneg.mpr hf.le)).trans_eq
      (inv_mul_cancel₀ hf.ne')
  · rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, pow_two]
    rfl


/-- Equation (3) for a complete two-flag CP branch. The parameter realizes the
unregularized maximum, including when the compression at that parameter is singular. -/
theorem two_flag_cp_branch_score_le
    (L : Fin 2 → Matrix h e ℂ) (Φ : Fin 2 → MatrixMap e h ℂ)
    (hCP : ∀ i, (Φ i).IsCompletelyPositive)
    (hTP : (∑ i, Φ i).IsTracePreserving) :
    let A (i : Fin 2) := (L i)ᴴ * L i
    let M (t : ℝ) := t • A 0 + (1 - t) • A 1
    ∃ t ∈ Icc (0 : ℝ) 1, IsMaxOn (fun s => rootTrace (M s)) (Icc 0 1) t ∧
      flaggedChoiScore L Φ ≤ rootTrace (M t) ^ 2 := by
  dsimp only
  let A (i : Fin 2) := (L i)ᴴ * L i
  let M (t : ℝ) := t • A 0 + (1 - t) • A 1
  change ∃ t ∈ Icc (0 : ℝ) 1, IsMaxOn (fun s => rootTrace (M s)) (Icc 0 1) t ∧
    flaggedChoiScore L Φ ≤ rootTrace (M t) ^ 2
  have hA (i : Fin 2) : (A i).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  let interval : Set ℝ := Icc 0 1
  let N (p : ℝ × ℝ) := M p.1 + p.2 • (1 : Matrix e e ℂ)
  have hM : Continuous M := by fun_prop
  have hN : Continuous N := by fun_prop
  have hMpos : MapsTo M interval {B | B.PosSemidef} := by
    intro s hs
    exact ((hA 0).smul hs.1).add ((hA 1).smul (sub_nonneg.mpr hs.2))
  have hNpos : MapsTo N (interval ×ˢ interval) {B | B.PosSemidef} := by
    intro p hp
    exact (show (M p.1).PosSemidef from hMpos hp.1).add
      (Matrix.PosSemidef.one.smul hp.2.1)
  have hcont := rootTrace_continuousOn.comp hM.continuousOn hMpos
  have hcompact : IsCompact interval := isCompact_Icc
  obtain ⟨t, ht, hmax⟩ := hcompact.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont
  refine ⟨t, ht, hmax, ?_⟩
  by_cases hne : Nonempty e
  swap
  · let : IsEmpty e := not_nonempty_iff.mp hne
    simpa [flaggedChoiScore, dotProduct] using (sq_nonneg (rootTrace (M t)))
  have hUniform := Metric.uniformContinuousOn_iff.mp
    ((hcompact.prod hcompact).uniformContinuousOn_of_continuous
      (rootTrace_continuousOn.comp hN.continuousOn hNpos))
  have hbound (η : ℝ) (hη : 0 < η) : flaggedChoiScore L Φ ≤ (rootTrace (M t) + η) ^ 2 := by
    obtain ⟨δ, hδ, hClose⟩ := hUniform η hη
    let ε : ℝ := min (δ / 2) 1
    have hε : 0 < ε := lt_min (by linarith) one_pos
    have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
    have hε1 : ε ∈ interval := ⟨hε.le, min_le_right _ _⟩
    obtain ⟨s, hs, _, hY, hFeasible, hTrace⟩ := exists_regularized_dual_weight A hA ε hε
    have hEq : s • (A 0 + ε • 1) + (1 - s) • (A 1 + ε • 1) = N (s, ε) := by
      dsimp [N, M]
      module
    have hWeighted := weighted_cp_branch_score_le L Φ hCP hTP _ hY hFeasible
    rw [hTrace] at hWeighted
    change flaggedChoiScore L Φ ≤
      rootTrace (s • (A 0 + ε • 1) + (1 - s) • (A 1 + ε • 1)) ^ 2 at hWeighted
    rw [hEq] at hWeighted
    have hdist : dist (s, ε) (s, 0) < δ := by
      simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hε.le] using And.intro hδ hεδ
    have hd := hClose (s, ε) ⟨hs, hε1⟩ (s, 0) ⟨hs, left_mem_Icc.mpr zero_le_one⟩ hdist
    have hdiff : rootTrace (N (s, ε)) - rootTrace (M s) < η := by
      have hd' : |rootTrace (N (s, ε)) - rootTrace (N (s, 0))| < η := by
        simpa only [Function.comp_apply, Real.dist_eq] using hd
      have he : N (s, 0) = M s := by simp [N]
      rw [he] at hd'
      exact (abs_lt.mp hd').2
    have hroot : 0 ≤ rootTrace (N (s, ε)) :=
      Complex.nonneg_iff.mp (CFC.sqrt_nonneg (N (s, ε))).posSemidef.trace_nonneg |>.1
    have hle : rootTrace (N (s, ε)) ≤ rootTrace (M t) + η := by
      have hsmax : rootTrace (M s) ≤ rootTrace (M t) := hmax hs
      linarith
    exact hWeighted.trans (pow_le_pow_left₀ hroot hle 2)
  have hlim : Tendsto (fun η : ℝ => (rootTrace (M t) + η) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (rootTrace (M t) ^ 2)) := by
    have hc : Continuous (fun η : ℝ => (rootTrace (M t) + η) ^ 2) := by fun_prop
    simpa only [add_zero] using (hc.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)).tendsto
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with η hη using hbound η hη

end Regularized

#print axioms exists_regularized_dual_weight
#print axioms two_flag_cp_branch_score_le
#print axioms weighted_trace_pairing_le
#print axioms weighted_kraus_branch_score_le
#print axioms weighted_projective_branch_score_le
#print axioms flaggedChoiScore_of_kraus
#print axioms weighted_cp_branch_score_le

end D5.S3.Quantum.Measurement.AuricBranchDual
