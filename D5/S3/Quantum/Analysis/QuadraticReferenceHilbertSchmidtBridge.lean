/- GID: D5/S3/Quantum/Analysis/QuadraticReferenceHilbertSchmidtBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/QuadraticReferenceHilbertSchmidtBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite concrete quadratic moment constructs the genuine inverse-square-root HS extension and controls the original trace. -/

import D5.S3.Quantum.Analysis.TraceClass.GeneralProduct
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder InnerProductSpace ENNReal
open HilbertSchmidt
noncomputable section
namespace D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The concrete extended quadratic column moment, before applying `toReal`. -/
def quadraticMoment {w : Set H} (e : HilbertBasis w ℂ H) (s : w → ℝ)
    (ρ : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i : w, ENNReal.ofReal (‖ρ (e i)‖ ^ 2 / s i)

/-- The analytic trace of the original bounded product. -/
def rightTrace (T B : H →L[ℂ] H) (hT : IsTraceClass T) : ℂ :=
  trace (T * B) (by simpa using isTraceClass_mul_mul (A := 1) (B := B) hT)

/-- The actual inverse of the positive square root, with its actual range domain. -/
def invSqrt (σ : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  LinearPMap.inverse ((CFC.sqrt σ).toLinearMap.toPMap ⊤)

private theorem exists_hilbertSchmidt_of_square_summable_columns
    {w : Set H} (e : HilbertBasis w ℂ H) (v : w → H)
    (hv : Summable (fun i : w => ‖v i‖ ^ 2)) :
    ∃ A : H →L[ℂ] H,
      (∀ i, A (e i) = v i) ∧ IsHilbertSchmidt A ∧
      (∑' i : w, ‖A (e i)‖ ^ 2) = ∑' i : w, ‖v i‖ ^ 2 ∧
      ‖A‖ ≤ Real.sqrt (∑' i : w, ‖v i‖ ^ 2) := by
  exact HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns e v hv

private theorem sqrt_apply_eigenvector (σ : H →L[ℂ] H) (hσ : 0 ≤ σ)
    (x : H) (s : ℝ) (hs : 0 < s) (he : σ x = (s : ℂ) • x) :
    CFC.sqrt σ x = (Real.sqrt s : ℂ) • x := by
  let S := CFC.sqrt σ
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hc2 : c ^ 2 = s := Real.sq_sqrt hs.le
  have hsq : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ
  let y := S x - (c : ℂ) • x
  have hcancel : S y + (c : ℂ) • y = 0 := by
    dsimp only [y]
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    have hxx : S (S x) = (s : ℂ) • x := by
      rw [← mul_apply_eq_comp, hsq, he]
    rw [hxx]
    have hcc : (c : ℂ) * (c : ℂ) = (s : ℂ) := by exact_mod_cast (by simpa only [pow_two] using hc2 : c * c = s)
    rw [hcc]
    module
  have hy : S y = -(c : ℂ) • y := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hcancel
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive (f := S)).mp (CFC.sqrt_nonneg σ)
  have hval : ⟪y, S y⟫_ℂ = (-(c * ‖y‖ ^ 2) : ℝ) := by
    rw [hy, inner_smul_right, inner_self_eq_norm_sq_to_K]
    push_cast
    rw [neg_mul]
    rfl
  have hreal : 0 ≤ -(c * ‖y‖ ^ 2) := by
    have hp := hpos.re_inner_nonneg_right y
    change 0 ≤ (⟪y, S y⟫_ℂ).re at hp
    simpa only [hval, Complex.ofReal_re] using hp
  have hynorm : ‖y‖ = 0 := by
    have hm : c * ‖y‖ ^ 2 = 0 := le_antisymm
      (neg_nonneg.mp hreal) (mul_nonneg hc.le (sq_nonneg _))
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hm).resolve_left hc.ne')
  exact sub_eq_zero.mp (norm_eq_zero.mp hynorm)

private theorem eq_of_basis_columns {w : Set H} (e : HilbertBasis w ℂ H)
    (A B : H →L[ℂ] H) (h : ∀ i, A (e i) = B (e i)) : A = B := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span)
  rintro _ ⟨i, rfl⟩
  exact h i

private theorem inverse_sqrt_domain_and_extension {w : Set H}
    (e : HilbertBasis w ℂ H) (σ ρ A : H →L[ℂ] H) (hσ : 0 ≤ σ)
    (s : w → ℝ) (hs : ∀ i, 0 < s i)
    (he : ∀ i, σ (e i) = (s i : ℂ) • e i)
    (hA : A * CFC.sqrt σ = ρ) :
    Dense ((invSqrt σ).domain : Set H) ∧
      ∀ x : (invSqrt σ).domain, A (x : H) = ρ (invSqrt σ x) := by
  classical
  let S := CFC.sqrt σ
  let f := S.toLinearMap.toPMap ⊤
  have hSe (i : w) : S (e i) = (Real.sqrt (s i) : ℂ) • e i :=
    sqrt_apply_eigenvector σ hσ (e i) (s i) (hs i) (he i)
  have hSsa : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.isSelfAdjoint_iff').mp (CFC.sqrt_nonneg σ).isSelfAdjoint
  have hinj : Function.Injective S := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    change S x = 0 at hx
    apply e.repr.injective
    apply lp.ext
    funext i
    simp only [HilbertBasis.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
    have hi := S.adjoint_inner_left x (e i)
    rw [hSsa, hSe i, hx, inner_zero_right, inner_smul_left] at hi
    have hne : (Real.sqrt (s i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hs i)).ne'
    simpa using (mul_eq_zero.mp hi).resolve_left (by simpa using hne)
  have hker : f.ker = ⊥ := by
    rw [LinearPMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    change S (x : H) = 0 at hx
    exact hinj (hx.trans (map_zero S).symm)
  have hdom : (invSqrt σ).domain = LinearMap.range f.toFun := LinearPMap.inverse_domain
  have hmem (i : w) : e i ∈ (invSqrt σ).domain := by
    rw [hdom, LinearMap.mem_range]
    refine ⟨⟨(((Real.sqrt (s i))⁻¹ : ℝ) : ℂ) • e i, Submodule.mem_top⟩, ?_⟩
    change S ((((Real.sqrt (s i))⁻¹ : ℝ) : ℂ) • e i) = e i
    rw [map_smul, hSe, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (hs i)).ne', Complex.ofReal_one, one_smul]
  have hspan : Submodule.span ℂ (Set.range e) ≤ (invSqrt σ).domain :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  constructor
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply top_unique
    rw [← e.dense_span]
    exact Submodule.topologicalClosure_mono hspan
  · intro x
    have hx : (x : H) ∈ LinearMap.range f.toFun := by rw [← hdom]; exact x.2
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    have hi : invSqrt σ x = (y : H) := by
      change f.inverse x = (y : H)
      exact LinearPMap.inverse_apply_eq hker hy
    rw [hi]
    have hxy : S (y : H) = (x : H) := hy
    rw [← hxy, ← mul_apply_eq_comp, hA]


private theorem trace_transfer_of_columns {w : Set H}
    (e : HilbertBasis w ℂ H) (ρ σ A : H →L[ℂ] H)
    (hρtc : IsTraceClass ρ) (hσtc : IsTraceClass σ) (hρpos : 0 ≤ ρ) (hσpos : 0 ≤ σ)
    (s : w → ℝ) (hs : ∀ i, 0 < s i)
    (he : ∀ i, σ (e i) = (s i : ℂ) • e i)
    (hAe : ∀ i, A (e i) = (((Real.sqrt (s i))⁻¹ : ℝ) : ℂ) • ρ (e i))
    (hAhs : IsHilbertSchmidt A)
    (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    ‖rightTrace ρ B hρtc‖ ^ 2 ≤
      (∑' i : w, ‖A (e i)‖ ^ 2) * (rightTrace σ (B ^ 2) hσtc).re := by
  let S := CFC.sqrt σ
  let C := B * S
  have hSe (i : w) : S (e i) = (Real.sqrt (s i) : ℂ) • e i :=
    sqrt_apply_eigenvector σ hσpos (e i) (s i) (hs i) (he i)
  have hS : IsHilbertSchmidt S := by
    have h := isHilbertSchmidt_sqrt_abs_of_isTraceClass hσtc
    simpa only [CFC.abs_of_nonneg σ hσpos] using h
  have hC : IsHilbertSchmidt C := isHilbertSchmidt_mul_left hS
  have ha : Summable (fun i : w => ‖A (e i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w e hAhs
  have hc : Summable (fun i : w => ‖C (e i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w e hC
  have hp : Summable (fun i : w => ‖A (e i)‖ * ‖C (e i)‖) :=
    summable_norm_mul_of_square_sums _ _ ha hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hi : Summable (fun i : w => ‖⟪A (e i), C (e i)⟫_ℂ‖) :=
    hp.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_inner_le_norm _ _)
  have hρsa : ContinuousLinearMap.adjoint ρ = ρ :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hρpos.isSelfAdjoint
  have hσsa : ContinuousLinearMap.adjoint σ = σ :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hσpos.isSelfAdjoint
  have hBsa : ContinuousLinearMap.adjoint B = B :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hB
  have hpair (i : w) : ⟪A (e i), C (e i)⟫_ℂ = ⟪e i, (ρ * B) (e i)⟫_ℂ := by
    have hsqrt : Real.sqrt (s i) ≠ 0 := (Real.sqrt_pos.mpr (hs i)).ne'
    dsimp only [C]
    rw [hAe, mul_apply_eq_comp, hSe, map_smul, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hsqrt,
      Complex.ofReal_one, one_mul, ← ρ.adjoint_inner_right, hρsa, mul_apply_eq_comp]
  have htrace : rightTrace ρ B hρtc = ∑' i : w, ⟪A (e i), C (e i)⟫_ℂ := by
    unfold rightTrace
    rw [trace_eq_of_hilbertBasis _ e]
    exact tsum_congr fun i => (hpair i).symm
  have hsecond (i : w) : ⟪e i, (σ * B ^ 2) (e i)⟫_ℂ =
      (‖C (e i)‖ ^ 2 : ℝ) := by
    have hdiag : ⟪e i, (σ * B ^ 2) (e i)⟫_ℂ =
        (s i : ℂ) * ⟪B (e i), B (e i)⟫_ℂ := by
      rw [mul_apply_eq_comp, ← hσsa, σ.adjoint_inner_right, he, inner_smul_left,
        Complex.conj_ofReal, pow_two, mul_apply_eq_comp, ← hBsa, B.adjoint_inner_right]
      rw [hBsa]
    rw [hdiag, inner_self_eq_norm_sq_to_K]
    have hnorm : ‖C (e i)‖ ^ 2 = s i * ‖B (e i)‖ ^ 2 := by
      dsimp only [C]
      rw [mul_apply_eq_comp, hSe, map_smul, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (hs i).le]
    rw [hnorm]
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  have hmoment : (rightTrace σ (B ^ 2) hσtc).re = ∑' i : w, ‖C (e i)‖ ^ 2 := by
    unfold rightTrace
    rw [trace_eq_of_hilbertBasis _ e]
    simp_rw [hsecond]
    rw [← Complex.ofReal_tsum (fun i : w => ‖C (e i)‖ ^ 2), Complex.ofReal_re]
  have hbound : ‖rightTrace ρ B hρtc‖ ≤
      Real.sqrt (∑' i : w, ‖A (e i)‖ ^ 2) * Real.sqrt (∑' i : w, ‖C (e i)‖ ^ 2) := by
    rw [htrace]
    exact (norm_tsum_le_tsum_norm hi).trans
      ((hi.tsum_le_tsum (fun _ => norm_inner_le_norm _ _) hp).trans
        (tsum_mul_le_sqrt_mul_sqrt ha hc (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)))
  rw [hmoment]
  calc
    ‖rightTrace ρ B hρtc‖ ^ 2 ≤
        (Real.sqrt (∑' i : w, ‖A (e i)‖ ^ 2) *
          Real.sqrt (∑' i : w, ‖C (e i)‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = (∑' i : w, ‖A (e i)‖ ^ 2) * (∑' i : w, ‖C (e i)‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _),
        Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _)]

/-- A finite concrete quadratic moment constructs one bounded Hilbert–Schmidt extension
of the original inverse-square-root product on its entire actual dense domain, and
controls the analytic trace of every original bounded self-adjoint observable. -/
theorem quadratic_reference_hilbertSchmidt_bridge
    {w : Set H} (e : HilbertBasis w ℂ H) (ρ σ : H →L[ℂ] H)
    (hρtc : IsTraceClass ρ) (hσtc : IsTraceClass σ)
    (hρpos : 0 ≤ ρ) (hσpos : 0 ≤ σ)
    (s : w → ℝ) (hs : ∀ i, 0 < s i)
    (hσe : ∀ i, σ (e i) = (s i : ℂ) • e i)
    (hQ : quadraticMoment e s ρ ≠ ⊤) :
    ∃ A : H →L[ℂ] H,
      IsHilbertSchmidt A ∧
      (∀ i, A (e i) = (((Real.sqrt (s i))⁻¹ : ℝ) : ℂ) • ρ (e i)) ∧
      (∑' i : w, ‖A (e i)‖ ^ 2) = (quadraticMoment e s ρ).toReal ∧
      A * CFC.sqrt σ = ρ ∧
      Dense ((invSqrt σ).domain : Set H) ∧
      (∀ x : (invSqrt σ).domain, A (x : H) = ρ (invSqrt σ x)) ∧
      (∀ B : H →L[ℂ] H, IsSelfAdjoint B →
        ‖rightTrace ρ B hρtc‖ ^ 2 ≤
          (quadraticMoment e s ρ).toReal * (rightTrace σ (B ^ 2) hσtc).re) := by
  let v : w → H := fun i => (((Real.sqrt (s i))⁻¹ : ℝ) : ℂ) • ρ (e i)
  have hvnorm (i : w) : ‖v i‖ ^ 2 = ‖ρ (e i)‖ ^ 2 / s i := by
    dsimp only [v]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow,
      inv_pow, Real.sq_sqrt (hs i).le]
    simp only [div_eq_mul_inv, mul_comm]
  have hqreal : (quadraticMoment e s ρ).toReal = ∑' i : w, ‖v i‖ ^ 2 := by
    unfold quadraticMoment
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    apply tsum_congr
    intro i
    rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (hs i).le), hvnorm]
  have hv : Summable (fun i : w => ‖v i‖ ^ 2) := by
    have h := ENNReal.summable_toReal hQ
    change Summable (fun i : w => (ENNReal.ofReal (‖ρ (e i)‖ ^ 2 / s i)).toReal) at h
    simpa only [← hvnorm, ENNReal.toReal_ofReal (sq_nonneg _)] using h
  obtain ⟨A, hAe, hAhs, hAsum, _⟩ := exists_hilbertSchmidt_of_square_summable_columns e v hv
  have hprod : A * CFC.sqrt σ = ρ := by
    apply eq_of_basis_columns e
    intro i
    rw [mul_apply_eq_comp, sqrt_apply_eigenvector σ hσpos (e i) (s i) (hs i) (hσe i),
      map_smul, hAe]
    dsimp only [v]
    rw [smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr (hs i)).ne', Complex.ofReal_one, one_smul]
  obtain ⟨hdense, hext⟩ := inverse_sqrt_domain_and_extension e σ ρ A hσpos s hs hσe hprod
  have hsum : (∑' i : w, ‖A (e i)‖ ^ 2) = (quadraticMoment e s ρ).toReal :=
    hAsum.trans hqreal.symm
  refine ⟨A, hAhs, hAe, hsum, hprod, hdense, hext, ?_⟩
  intro B hB
  rw [← hsum]
  exact trace_transfer_of_columns e ρ σ A hρtc hσtc hρpos hσpos s hs hσe hAe hAhs B hB

#print axioms quadratic_reference_hilbertSchmidt_bridge

end D5.S3.Quantum.Analysis.QuadraticReferenceHilbertSchmidtBridge
