/- GID: D5/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/ClosedTraceFinitenessBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-class dimension bounds, cycle variance bounds, and closed-trace counterexamples. -/

import D5.S3.Quantum.Analysis.TraceClass.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Closed-Trace Finiteness Boundaries and Cycle-Rearrangement Obstructions

Motivated by Chandrasekaran (arXiv:2611.34924v1, Section 5.2 Eqs. 5.30–5.38, 5.44–5.46,
Appendix D.2 Eq. D.25, and Appendix E Eq. E.12), this module establishes both the positive
operator-theoretic finiteness theorems and the exact obstructions separating open-amplitude
convergence from closed-trace convergence:

1. **Positive trace-class dimension bounds**: If `W ≥ 0` is trace-class on a complex Hilbert
   space `H` and obeys a uniform lower bound `c ‖x‖² ≤ Re ⟪x, W x⟫` (`c > 0`), then `H` is
   finite-dimensional with `finrank ℂ H ≤ (trace W).re / c`. The same sharp bound holds for
   the range of any star projection `p` on which a positive trace-class operator `C` satisfies
   `c ‖x‖² ≤ Re ⟪x, C x⟫` (covering spectral sublevels of finite-trace Euclidean cylinders).
2. **Positive cycle-union area-variance bound** (Eq. D.25): On any finite union of `r`-cycles
   with at most a `1/r` fraction of basis vectors outside an area band of half-width `Δs` and
   positive weights `c ≤ w i ≤ 1`, the weighted variance is at most `Δs² + sMax² / (r * c)`.
3. **Closed-trace rearrangement sign-flip counterexample** (exact boundary of Eq. 5.38): On the
   infinite-dimensional orthonormal basis `ℕ` of `ℓ²(ℕ)` with `C_b = 1`, bounded area
   `s(2m) = 0, s(2m+1) = 1`, pair-flip boost observable `O = -σ_x ⊗ σ_x`, and `X = Δ_η O - 1`,
   two exhaustive increasing nets of finite-rank cuts—the symmetric pair net `symCut N` and an
   explicit order-`r` cycle-bijection net `cycCut r N` (`r ≥ 5`)—both exhaust `ℕ` (strong
   convergence `P_N ↑ 1`), yet yield `Z(symCut N) = 2N → +∞` while
   `Z(cycCut r N) = (4 - r)N ≤ -N → -∞`.
4. **Disjoint joint-cut unconditional summability equivalence** (exact boundary of Eqs. 5.44–5.45):
   For `w : ℕ → ℝ≥0` and any non-degenerate probability distribution `v` on a finite set `α` with
   event `I` of probability `p ∈ (0, 1)`, the joint-cut summand `f(i, a) = w i * v a * (1_I(a) - p)`
   always has zero inner sum `∑ a, f(i, a) = 0`, yet `Summable f ↔ Summable w` with exact fiber
   L¹ norm `∑ a, |f(i, a)| = 2 * p * (1 - p) * w i`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace D5.S3.Quantum.Analysis.NullConeGravity.ClosedTraceFinitenessBoundary

section PositiveTraceClassBounds

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive trace-class operator uniformly bounded below by `c > 0` forces the Hilbert space
to be finite-dimensional with sharp dimension bound `finrank ℂ H ≤ (trace W).re / c`. -/
theorem finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound
    {W : H →L[ℂ] H} (hW_nn : 0 ≤ W) (hW_tc : IsTraceClass W)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : H, c * ‖x‖ ^ 2 ≤ (⟪x, W x⟫_ℂ).re) :
    FiniteDimensional ℂ H ∧ (Module.finrank ℂ H : ℝ) ≤ (trace W hW_tc).re / c := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hdiag : Summable (fun i : w => (⟪b i, W (b i)⟫_ℂ).re) := by
    have habs := summable_inner_abs_of_hilbertBasis hW_tc b
    rwa [CFC.abs_of_nonneg W hW_nn] at habs
  have hterm : ∀ i : w, c ≤ (⟪b i, W (b i)⟫_ℂ).re := by
    intro i
    have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
    have h := hlow (b i)
    simpa [hnorm] using h
  have hconst : Summable (fun _ : w => c) :=
    Summable.of_nonneg_of_le (fun _ => hc.le) hterm hdiag
  let : Finite w := Finite.of_summable_const hc hconst
  let : Fintype w := Fintype.ofFinite w
  have hfd : FiniteDimensional ℂ H := b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hfinrank : Module.finrank ℂ H = Fintype.card w :=
    Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis
  have htrace_eq : (trace W hW_tc).re = ∑ i : w, (⟪b i, W (b i)⟫_ℂ).re := by
    rw [trace_eq_of_hilbertBasis_of_nonneg hW_nn hW_tc b, tsum_fintype, Complex.re_sum]
  have hsum_le : (Fintype.card w : ℝ) * c ≤ ∑ i : w, (⟪b i, W (b i)⟫_ℂ).re := by
    calc
      (Fintype.card w : ℝ) * c = ∑ _i : w, c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i : w, (⟪b i, W (b i)⟫_ℂ).re := Finset.sum_le_sum fun i _ => hterm i
  refine ⟨hfd, ?_⟩
  rw [hfinrank, htrace_eq]
  exact (le_div_iff₀ hc).mpr hsum_le

/-- Spectral-sublevel dimension bound: if `C ≥ 0` is trace-class on `H` and satisfies a uniform
lower bound `c ‖x‖² ≤ Re ⟪x, C x⟫` (`c > 0`) on the range of a star projection `p`, then
`range p` is finite-dimensional with `finrank ℂ (range p) ≤ (trace C).re / c`. -/
theorem finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound
    {p C : H →L[ℂ] H} (hp : IsStarProjection p)
    (hC_nn : 0 ≤ C) (hC_tc : IsTraceClass C)
    {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : H, x ∈ LinearMap.range p.toLinearMap → c * ‖x‖ ^ 2 ≤ (⟪x, C x⟫_ℂ).re) :
    FiniteDimensional ℂ (LinearMap.range p.toLinearMap) ∧
      (Module.finrank ℂ (LinearMap.range p.toLinearMap) : ℝ) ≤ (trace C hC_tc).re / c := by
  let W : Submodule ℂ H := LinearMap.range p.toLinearMap
  let : CompleteSpace W := by
    change CompleteSpace p.range
    exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      hp.isIdempotentElem).completeSpace_coe
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ W
  have hbOrtho : Orthonormal ℂ (fun i : w => (b i : H)) :=
    b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  have hbInj : Function.Injective (fun i : w => (b i : H)) :=
    hbOrtho.linearIndependent.injective
  let s : Set H := Set.range (fun i : w => (b i : H))
  have hsOrtho : Orthonormal ℂ ((↑) : s → H) := hbOrtho.toSubtypeRange
  obtain ⟨wH, bH, hsH, hbH⟩ := hsOrtho.exists_hilbertBasis_extension
  let : DecidableEq wH := Classical.decEq _
  have hdiag : Summable (fun j : wH => (⟪bH j, C (bH j)⟫_ℂ).re) := by
    have habs := summable_inner_abs_of_hilbertBasis hC_tc bH
    rwa [CFC.abs_of_nonneg C hC_nn] at habs
  have hinner_sq : ∀ j : wH, ⟪bH j, C (bH j)⟫_ℂ = ((‖CFC.sqrt C (bH j)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    let S : H →L[ℂ] H := CFC.sqrt C
    have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg C)
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hSS : S * S = C := CFC.sqrt_mul_sqrt_self C hC_nn
    have hinner : ⟪bH j, C (bH j)⟫_ℂ = ⟪S (bH j), S (bH j)⟫_ℂ := by
      rw [← hSS]
      show ⟪bH j, (S * S) (bH j)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.adjoint_inner_left S (S (bH j)) (bH j), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hdiag_nn : ∀ j : wH, 0 ≤ (⟪bH j, C (bH j)⟫_ℂ).re := by
    intro j
    rw [hinner_sq j, Complex.ofReal_re]
    exact sq_nonneg _
  let g : w → wH := fun i => ⟨(b i : H), hsH ⟨i, rfl⟩⟩
  have hgInj : Function.Injective g := by
    intro i₁ i₂ hij
    apply hbInj
    exact congrArg (fun z : wH => (z : H)) hij
  have hg_val : ∀ i : w, bH (g i) = (b i : H) := fun i => by
    rw [hbH]
  have hterm : ∀ i : w, c ≤ (⟪bH (g i), C (bH (g i))⟫_ℂ).re := by
    intro i
    rw [hg_val i]
    have hnorm : ‖(b i : H)‖ = 1 := hbOrtho.1 i
    have h := hlow (b i : H) (b i).property
    simpa [hnorm] using h
  have hcomp : Summable (fun i : w => (⟪bH (g i), C (bH (g i))⟫_ℂ).re) :=
    hdiag.comp_injective hgInj
  have hconst : Summable (fun _ : w => c) :=
    Summable.of_nonneg_of_le (fun _ => hc.le) hterm hcomp
  let : Finite w := Finite.of_summable_const hc hconst
  let : Fintype w := Fintype.ofFinite w
  have hfd : FiniteDimensional ℂ W := b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hfinrank : Module.finrank ℂ W = Fintype.card w :=
    Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis
  have htrace_re : (trace C hC_tc).re = ∑' j : wH, (⟪bH j, C (bH j)⟫_ℂ).re := by
    rw [trace_eq_of_hilbertBasis_of_nonneg hC_nn hC_tc bH]
    simp_rw [hinner_sq, Complex.ofReal_re]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hsum_le : (Fintype.card w : ℝ) * c ≤ ∑' j : wH, (⟪bH j, C (bH j)⟫_ℂ).re := by
    let T : Finset wH := Finset.univ.image g
    have hcard_eq : ∑ i : w, (⟪bH (g i), C (bH (g i))⟫_ℂ).re =
        ∑ j ∈ T, (⟪bH j, C (bH j)⟫_ℂ).re := by
      rw [Finset.sum_image (fun a _ b _ h => hgInj h)]
    calc
      (Fintype.card w : ℝ) * c = ∑ _i : w, c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ i : w, (⟪bH (g i), C (bH (g i))⟫_ℂ).re := Finset.sum_le_sum fun i _ => hterm i
      _ = ∑ j ∈ T, (⟪bH j, C (bH j)⟫_ℂ).re := hcard_eq
      _ ≤ ∑' j : wH, (⟪bH j, C (bH j)⟫_ℂ).re := hdiag.sum_le_tsum T (fun j _ => hdiag_nn j)
  refine ⟨hfd, ?_⟩
  change (Module.finrank ℂ W : ℝ) ≤ (trace C hC_tc).re / c
  rw [hfinrank, htrace_re]
  exact (le_div_iff₀ hc).mpr hsum_le

end PositiveTraceClassBounds

section CycleVarianceBound

variable {ι : Type*} [DecidableEq ι]

/-- Positive cycle-union area-variance bound (Chandrasekaran, arXiv:2611.34924v1, Eq. D.25):
if weights satisfy `c ≤ w i ≤ 1` (`0 < c`), values inside `I ⊆ s` lie within `Δs` of `s₀`,
values outside `I` lie within `sMax` of `s₀`, and at most a `1/r` fraction of states in `s`
lie outside `I`, then the weighted mean squared deviation is at most `Δs² + sMax² / (r * c)`. -/
theorem cycle_union_area_variance_bound (s I : Finset ι) (hIs : I ⊆ s) (hs : s.Nonempty)
    (w val : ι → ℝ) (c s₀ Δs sMax : ℝ) (r : ℕ)
    (hc : 0 < c) (_hΔs : 0 ≤ Δs) (_hsMax : 0 ≤ sMax) (hr : 0 < r)
    (hw_lo : ∀ i ∈ s, c ≤ w i) (hw_hi : ∀ i ∈ s, w i ≤ 1)
    (hI_dev : ∀ i ∈ I, |val i - s₀| ≤ Δs)
    (hout_dev : ∀ i ∈ s \ I, |val i - s₀| ≤ sMax)
    (hfrac : ((s \ I).card : ℝ) * (r : ℝ) ≤ (s.card : ℝ)) :
    (∑ i ∈ s, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) ≤
      Δs ^ 2 + sMax ^ 2 / ((r : ℝ) * c) := by
  have hsum_lo : (s.card : ℝ) * c ≤ ∑ i ∈ s, w i := by
    calc
      (s.card : ℝ) * c = ∑ _i ∈ s, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum hw_lo
  have hcard_pos : (0 : ℝ) < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  have hW_pos : 0 < ∑ i ∈ s, w i := lt_of_lt_of_le (mul_pos hcard_pos hc) hsum_lo
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hsplit :
      ∑ i ∈ s, w i * (val i - s₀) ^ 2 =
        (∑ i ∈ I, w i * (val i - s₀) ^ 2) + (∑ i ∈ s \ I, w i * (val i - s₀) ^ 2) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIs]
  have hI_bound :
      ∑ i ∈ I, w i * (val i - s₀) ^ 2 ≤ (∑ i ∈ s, w i) * Δs ^ 2 := by
    calc
      ∑ i ∈ I, w i * (val i - s₀) ^ 2
          ≤ ∑ i ∈ I, w i * Δs ^ 2 := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hw_nn : 0 ≤ w i := le_trans hc.le (hw_lo i (hIs hi))
            have hsq : (val i - s₀) ^ 2 ≤ Δs ^ 2 := by
              rw [← sq_abs (val i - s₀)]
              exact pow_le_pow_left₀ (abs_nonneg _) (hI_dev i hi) 2
            exact mul_le_mul_of_nonneg_left hsq hw_nn
      _ = (∑ i ∈ I, w i) * Δs ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (∑ i ∈ s, w i) * Δs ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact Finset.sum_le_sum_of_subset_of_nonneg hIs
              fun i hi _ => le_trans hc.le (hw_lo i hi)
  have hout_bound :
      ∑ i ∈ s \ I, w i * (val i - s₀) ^ 2 ≤ ((s \ I).card : ℝ) * sMax ^ 2 := by
    calc
      ∑ i ∈ s \ I, w i * (val i - s₀) ^ 2
          ≤ ∑ _i ∈ s \ I, sMax ^ 2 := by
            refine Finset.sum_le_sum fun i hi => ?_
            have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
            have hw_nn : 0 ≤ w i := le_trans hc.le (hw_lo i his)
            have hsq : (val i - s₀) ^ 2 ≤ sMax ^ 2 := by
              rw [← sq_abs (val i - s₀)]
              exact pow_le_pow_left₀ (abs_nonneg _) (hout_dev i hi) 2
            calc
              w i * (val i - s₀) ^ 2 ≤ w i * sMax ^ 2 := mul_le_mul_of_nonneg_left hsq hw_nn
              _ ≤ 1 * sMax ^ 2 := mul_le_mul_of_nonneg_right (hw_hi i his) (sq_nonneg _)
              _ = sMax ^ 2 := one_mul _
      _ = ((s \ I).card : ℝ) * sMax ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsecond :
      ((s \ I).card : ℝ) * sMax ^ 2 / (∑ i ∈ s, w i) ≤ sMax ^ 2 / ((r : ℝ) * c) := by
    rw [div_le_div_iff₀ hW_pos (mul_pos hr_pos hc)]
    calc
      ((s \ I).card : ℝ) * sMax ^ 2 * ((r : ℝ) * c)
          = (((s \ I).card : ℝ) * (r : ℝ)) * (c * sMax ^ 2) := by ring
      _ ≤ (s.card : ℝ) * (c * sMax ^ 2) :=
            mul_le_mul_of_nonneg_right hfrac (mul_nonneg hc.le (sq_nonneg _))
      _ = sMax ^ 2 * ((s.card : ℝ) * c) := by ring
      _ ≤ sMax ^ 2 * (∑ i ∈ s, w i) := mul_le_mul_of_nonneg_left hsum_lo (sq_nonneg _)
  calc
    (∑ i ∈ s, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i)
        = (∑ i ∈ I, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) +
            (∑ i ∈ s \ I, w i * (val i - s₀) ^ 2) / (∑ i ∈ s, w i) := by
          rw [hsplit, add_div]
    _ ≤ ((∑ i ∈ s, w i) * Δs ^ 2) / (∑ i ∈ s, w i) +
          (((s \ I).card : ℝ) * sMax ^ 2) / (∑ i ∈ s, w i) :=
          add_le_add (div_le_div_of_nonneg_right hI_bound hW_pos.le)
            (div_le_div_of_nonneg_right hout_bound hW_pos.le)
    _ ≤ Δs ^ 2 + sMax ^ 2 / ((r : ℝ) * c) := by
          have hcancel : (∑ i ∈ s, w i) * Δs ^ 2 / (∑ i ∈ s, w i) = Δs ^ 2 := by
            field_simp [hW_pos.ne']
          rw [hcancel]
          linarith

end CycleVarianceBound

section ClosedTraceRearrangementCounterexample

/-- Area eigenvalue on the orthonormal basis `ℕ` of `ℓ²(ℕ)`: `0` on even indices, `1` on odd
indices (bounded in `[0, 1]`). -/
def toyArea (n : ℕ) : ℝ :=
  if n % 2 = 0 then 0 else 1

/-- Matrix element `⟨i, i* | Δ_η (-σ_x ⊗ σ_x) | j, j*⟩` of the boost difference `Δ_η O` on the
pair-flip two-sided observable at boost phase `(-1)^{toyArea}` (`δ_η = 2`). -/
def pairFlipBoostKernel (i j : ℕ) : ℝ :=
  if i / 2 = j / 2 ∧ i ≠ j then 2 else 0

/-- Matrix element of the subtracted observable `X = Δ_η O - (δ_η / 2) I = Δ_η O - I`. -/
def subtractedKernel (i j : ℕ) : ℝ :=
  pairFlipBoostKernel i j - (if i = j then 1 else 0)

/-- Finite-rank closed-cut amplitude `Z_F[X] = ∑_{i, j ∈ F} ⟨i, i* | X | j, j*⟩` on a finite set
`F` of basis indices (matching Chandrasekaran Eq. 5.31 & 5.38 at `C_b = 1`). -/
def cutAmplitudeX (F : Finset ℕ) : ℝ :=
  ∑ i ∈ F, ∑ j ∈ F, subtractedKernel i j

/-- Symmetric pair cutoff `F_sym(N) = {0, 1, ..., 2N - 1}` keeping the first `N` matched pairs. -/
def symCut (N : ℕ) : Finset ℕ :=
  Finset.range (2 * N)

/-- The `n`-th cycle of length `r ≥ 2` in the cycle partition of `ℕ`: one odd element `2n + 1`
(outside `I = {0}`) paired with `r - 1` even elements `2((r - 1)n + k)` (inside `I`). -/
def cycleElement (r n : ℕ) (k : Fin r) : ℕ :=
  if k.val = 0 then 2 * n + 1 else 2 * ((r - 1) * n + (k.val - 1))

/-- Explicit order-`r` cycle permutation `V_r : ℕ ≃ ℕ` matching Chandrasekaran Fig. 29:
every orbit has exact size `r`, contains exactly one odd basis vector (`toyArea = 1`) and
`r - 1` even basis vectors (`toyArea = 0`). -/
def cycleBlockEquiv (r : ℕ) (hr : 2 ≤ r) : (ℕ × Fin r) ≃ ℕ where
  toFun p := cycleElement r p.1 p.2
  invFun m :=
    if m % 2 = 1 then
      (m / 2, ⟨0, by omega⟩)
    else
      ((m / 2) / (r - 1), ⟨(m / 2) % (r - 1) + 1, by
        have hpos : 0 < r - 1 := by omega
        have hlt := Nat.mod_lt (m / 2) hpos
        omega⟩)
  left_inv := by
    rintro ⟨n, ⟨k, hk⟩⟩
    unfold cycleElement
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte]
      have hmod : (2 * n + 1) % 2 = 1 := by omega
      have hdiv : (2 * n + 1) / 2 = n := by omega
      simp [hmod, hdiv]
    · simp only [hk0, ↓reduceIte]
      have hmod : (2 * ((r - 1) * n + (k - 1))) % 2 = 0 := by omega
      have hmod_ne : ¬ ((2 * ((r - 1) * n + (k - 1))) % 2 = 1) := by omega
      have hdiv2 : (2 * ((r - 1) * n + (k - 1))) / 2 = (r - 1) * n + (k - 1) := by omega
      have hpos : 0 < r - 1 := by omega
      have hkm : k - 1 < r - 1 := by omega
      have hq : ((r - 1) * n + (k - 1)) / (r - 1) = n := by
        rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hkm, add_zero]
      have hrem : ((r - 1) * n + (k - 1)) % (r - 1) = k - 1 := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hkm]
      simp only [hmod_ne, ↓reduceIte, hdiv2, hq, hrem]
      ext
      · rfl
      · dsimp
        omega
  right_inv := by
    intro m
    by_cases hm : m % 2 = 1
    · simp only [hm, ↓reduceIte, cycleElement]
      omega
    · have hm0 : m % 2 = 0 := by omega
      simp only [hm, ↓reduceIte, cycleElement]
      have hpos : 0 < r - 1 := by omega
      have hne : ¬ ((m / 2) % (r - 1) + 1 = 0) := by omega
      simp only [hne, ↓reduceIte, Nat.add_sub_cancel]
      have hdm := Nat.div_add_mod (m / 2) (r - 1)
      omega

/-- The cycle shift permutation `V_r : ℕ ≃ ℕ` of exact order `r`. -/
def cycleShiftPerm (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℕ :=
  letI : NeZero r := ⟨by omega⟩
  ((cycleBlockEquiv r hr).symm.trans
    ((Equiv.refl ℕ).prodCongr (Equiv.addRight (1 : Fin r)))).trans
    (cycleBlockEquiv r hr)

/-- The union of the first `N` complete `r`-cycles of `cycleShiftPerm r`. -/
def cycCut (r : ℕ) (hr : 2 ≤ r) (N : ℕ) : Finset ℕ :=
  ((Finset.range N) ×ˢ (Finset.univ : Finset (Fin r))).map (cycleBlockEquiv r hr).toEmbedding

/-- Helper: exact evaluation of `cutAmplitudeX F` via complete pairs in `F`. -/
private lemma cutAmplitudeX_eq_pair_count (F : Finset ℕ) :
    cutAmplitudeX F =
      4 * (((F.filter (fun m => m % 2 = 1 ∧ m - 1 ∈ F)).card : ℝ)) - (F.card : ℝ) := by
  unfold cutAmplitudeX subtractedKernel pairFlipBoostKernel
  have hsplit :
      ∑ i ∈ F, ∑ j ∈ F, ((if i / 2 = j / 2 ∧ i ≠ j then (2 : ℝ) else 0) -
          (if i = j then 1 else 0)) =
        (∑ i ∈ F, ∑ j ∈ F, if i / 2 = j / 2 ∧ i ≠ j then (2 : ℝ) else 0) -
          (∑ i ∈ F, ∑ j ∈ F, if i = j then (1 : ℝ) else 0) := by
    simp_rw [Finset.sum_sub_distrib]
  rw [hsplit]
  have hdiag : (∑ i ∈ F, ∑ j ∈ F, if i = j then (1 : ℝ) else 0) = (F.card : ℝ) := by
    have h1 : ∀ i ∈ F, (∑ j ∈ F, if i = j then (1 : ℝ) else 0) = 1 := fun i hi => by
      simp [hi]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hdiag]
  congr 1
  -- For each i ∈ F, the unique partner j with i / 2 = j / 2 ∧ i ≠ j is i + 1 (if even) or i - 1 (if odd).
  have hinner : ∀ i ∈ F,
      (∑ j ∈ F, if i / 2 = j / 2 ∧ i ≠ j then (2 : ℝ) else 0) =
        if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then 2 else 0 := by
    intro i _
    let partner : ℕ := if i % 2 = 0 then i + 1 else i - 1
    have hiff : ∀ j : ℕ, (i / 2 = j / 2 ∧ i ≠ j) ↔ j = partner := by
      intro j
      dsimp [partner]
      split_ifs with hev <;> omega
    simp_rw [hiff]
    rw [Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl hinner]
  -- Split F into odd and even elements; each matched pair contributes 2 from its even element and 2 from its odd element.
  let Fodd := F.filter (fun m => m % 2 = 1 ∧ m - 1 ∈ F)
  let Feven := F.filter (fun m => m % 2 = 0 ∧ m + 1 ∈ F)
  have hbij : Feven.card = Fodd.card := by
    refine Finset.card_bij (fun m _ => m + 1) ?_ ?_ ?_
    · intro m hm
      simp only [Feven, Fodd, Finset.mem_filter] at hm ⊢
      refine ⟨hm.2.2, by omega, ?_⟩
      simpa using hm.1
    · intro a _ b _ h
      omega
    · intro m hm
      simp only [Feven, Fodd, Finset.mem_filter] at hm ⊢
      refine ⟨m - 1, ⟨hm.2.2, by omega, ?_⟩, by omega⟩
      have : m - 1 + 1 = m := by omega
      rw [this]
      exact hm.1
  have hdisj : Disjoint Feven Fodd := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Feven, Fodd, Finset.mem_filter] at hm1 hm2
    omega
  have hsub : Feven ∪ Fodd ⊆ F := by
    intro m hm
    rcases Finset.mem_union.mp hm with h | h <;> exact (Finset.mem_filter.mp h).1
  have hzero : ∀ i ∈ F \ (Feven ∪ Fodd),
      (if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) = 0 := by
    intro i hi
    have hiF : i ∈ F := (Finset.mem_sdiff.mp hi).1
    have hnot : i ∉ Feven ∪ Fodd := (Finset.mem_sdiff.mp hi).2
    by_cases hev : i % 2 = 0
    · have hnot' : i + 1 ∉ F := by
        intro hmem
        exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiF, hev, hmem⟩))
      simp [hev, hnot']
    · have hodd : i % 2 = 1 := by omega
      have hnot' : i - 1 ∉ F := by
        intro hmem
        exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiF, hodd, hmem⟩))
      simp [hev, hnot']
  have hsum_split :
      (∑ i ∈ F, if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) =
        (∑ i ∈ Feven ∪ Fodd, if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) +
        (∑ i ∈ F \ (Feven ∪ Fodd), if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
  rw [hsum_split, Finset.sum_eq_zero hzero, add_zero, Finset.sum_union hdisj]
  have hE : (∑ i ∈ Feven, if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) =
      2 * (Feven.card : ℝ) := by
    have h1 : ∀ i ∈ Feven,
        (if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) = 2 := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      simp [h.1, h.2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    ring
  have hO : (∑ i ∈ Fodd, if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) =
      2 * (Fodd.card : ℝ) := by
    have h1 : ∀ i ∈ Fodd,
        (if (if i % 2 = 0 then i + 1 else i - 1) ∈ F then (2 : ℝ) else 0) = 2 := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      have hne : ¬ (i % 2 = 0) := by omega
      simp [hne, h.2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hE, hO, hbij]
  ring

/-- Exact closed-trace rearrangement sign-flip counterexample (boundary of Chandrasekaran
arXiv:2611.34924v1, Section 5.2 Eq. 5.38): on the infinite basis `ℕ` (`C_b = 1`, `0 ≤ toyArea ≤ 1`),
for every cycle length `r ≥ 5`:
1. `cycleShiftPerm r` has exact order `r` (`V^[r] = id`), and every `cycCut r N` is `V`-invariant;
2. Both `symCut N` and `cycCut r N` exhaust `ℕ` (strong convergence `P_N ↑ 1`);
3. For every `N ≥ 1`, `cutAmplitudeX (symCut N) = 2 * N > 0` (diverging to `+∞`), whereas
   `cutAmplitudeX (cycCut r N) = (4 - r) * N ≤ -N < 0` (diverging to `-∞`). -/
theorem cycle_rearrangement_sign_flip (r : ℕ) (hr : 5 ≤ r) :
    let hr2 : 2 ≤ r := by omega
    (∀ m : ℕ, (cycleShiftPerm r hr2)^[r] m = m) ∧
    (∀ N : ℕ, ∀ m ∈ cycCut r hr2 N, cycleShiftPerm r hr2 m ∈ cycCut r hr2 N) ∧
    (∀ m : ℕ, ∃ N : ℕ, m ∈ symCut N) ∧
    (∀ m : ℕ, ∃ N : ℕ, m ∈ cycCut r hr2 N) ∧
    (∀ N : ℕ, cutAmplitudeX (symCut N) = 2 * (N : ℝ)) ∧
    (∀ N : ℕ, cutAmplitudeX (cycCut r hr2 N) = (4 - (r : ℝ)) * (N : ℝ)) := by
  intro hr2
  let : NeZero r := ⟨by omega⟩
  have hstep : ∀ n : ℕ, ∀ k : Fin r,
      cycleShiftPerm r hr2 (cycleBlockEquiv r hr2 (n, k)) =
        cycleBlockEquiv r hr2 (n, k + (1 : Fin r)) := by
    intro n k
    unfold cycleShiftPerm
    simp
  have hiter : ∀ t : ℕ, ∀ n : ℕ, ∀ k : Fin r,
      (cycleShiftPerm r hr2)^[t] (cycleBlockEquiv r hr2 (n, k)) =
        cycleBlockEquiv r hr2 (n, k + Fin.ofNat r t) := by
    intro t
    induction t with
    | zero =>
      intro n k
      simp
    | succ t ih =>
      intro n k
      rw [Function.iterate_succ_apply', ih n k, hstep n (k + Fin.ofNat r t)]
      congr 2
      have hsucc : Fin.ofNat r (t + 1) = Fin.ofNat r t + (1 : Fin r) := by
        apply Fin.ext
        change (t + 1) % r = (t % r + 1 % r) % r
        rw [Nat.add_mod]
      rw [hsucc, add_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) V^[r] = id
    intro m
    let p := (cycleBlockEquiv r hr2).symm m
    have hm : m = cycleBlockEquiv r hr2 (p.1, p.2) := by
      simp [p]
    conv_lhs => rw [hm]
    rw [hiter r p.1 p.2]
    have hzero : Fin.ofNat r r = (0 : Fin r) := by
      apply Fin.ext
      change r % r = 0
      exact Nat.mod_self r
    rw [hzero, add_zero]
    exact hm.symm
  · -- (2) Each cycCut r N is V-invariant
    intro N m hm
    unfold cycCut at hm ⊢
    rw [Finset.mem_map] at hm ⊢
    rcases hm with ⟨⟨n, k⟩, hnk, rfl⟩
    refine ⟨(n, k + (1 : Fin r)), ?_, ?_⟩
    · rw [Finset.mem_product] at hnk ⊢
      exact ⟨hnk.1, Finset.mem_univ _⟩
    · exact (hstep n k).symm
  · -- (3) symCut exhausts ℕ
    intro m
    refine ⟨m + 1, ?_⟩
    unfold symCut
    rw [Finset.mem_range]
    omega
  · -- (4) cycCut exhausts ℕ
    intro m
    let p := (cycleBlockEquiv r hr2).symm m
    refine ⟨p.1 + 1, ?_⟩
    unfold cycCut
    rw [Finset.mem_map]
    refine ⟨p, ?_, by simp [p]⟩
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), Finset.mem_univ _⟩
  · -- (5) cutAmplitudeX (symCut N) = 2N
    intro N
    rw [cutAmplitudeX_eq_pair_count]
    have hcard : (symCut N).card = 2 * N := Finset.card_range (2 * N)
    have hfilt : ((symCut N).filter (fun m => m % 2 = 1 ∧ m - 1 ∈ symCut N)).card = N := by
      suffices h :
          ((symCut N).filter (fun m => m % 2 = 1 ∧ m - 1 ∈ symCut N)).card =
            (Finset.range N).card by
        simpa [Finset.card_range] using h
      refine Finset.card_bij (fun m _ => m / 2) ?_ ?_ ?_
      · intro m hm
        simp only [symCut, Finset.mem_filter, Finset.mem_range] at hm ⊢
        omega
      · intro a ha b hb hab
        simp only [symCut, Finset.mem_filter, Finset.mem_range] at ha hb
        omega
      · intro n hn
        rw [Finset.mem_range] at hn
        refine ⟨2 * n + 1, ?_, by omega⟩
        simp only [symCut, Finset.mem_filter, Finset.mem_range]
        omega
    rw [hcard, hfilt]
    push_cast
    ring
  · -- (6) cutAmplitudeX (cycCut r N) = (4 - r) N
    intro N
    rw [cutAmplitudeX_eq_pair_count]
    have hcard : (cycCut r hr2 N).card = r * N := by
      unfold cycCut
      rw [Finset.card_map, Finset.card_product, Finset.card_range, Finset.card_univ,
        Fintype.card_fin]
      ring
    have hfilt : ((cycCut r hr2 N).filter (fun m => m % 2 = 1 ∧ m - 1 ∈ cycCut r hr2 N)).card = N := by
      suffices h :
          ((cycCut r hr2 N).filter (fun m => m % 2 = 1 ∧ m - 1 ∈ cycCut r hr2 N)).card =
            (Finset.range N).card by
        simpa [Finset.card_range] using h
      refine Finset.card_bij (fun m _ => m / 2) ?_ ?_ ?_
      · intro m hm
        obtain ⟨hm_mem, hm_odd, _⟩ := Finset.mem_filter.mp hm
        unfold cycCut at hm_mem
        rw [Finset.mem_map] at hm_mem
        rcases hm_mem with ⟨⟨n, k⟩, hnk, rfl⟩
        rw [Finset.mem_product, Finset.mem_range] at hnk
        rw [Finset.mem_range]
        change cycleElement r n k % 2 = 1 at hm_odd
        change cycleElement r n k / 2 < N
        unfold cycleElement at hm_odd ⊢
        by_cases hk0 : k.val = 0
        · simp only [hk0, ↓reduceIte] at hm_odd ⊢
          omega
        · simp only [hk0, ↓reduceIte] at hm_odd
          omega
      · intro a ha b hb hab
        simp only [Finset.mem_filter] at ha hb
        omega
      · intro n hn
        rw [Finset.mem_range] at hn
        refine ⟨2 * n + 1, ?_, by omega⟩
        rw [Finset.mem_filter]
        refine ⟨?_, by omega, ?_⟩
        · unfold cycCut
          rw [Finset.mem_map]
          refine ⟨(n, ⟨0, by omega⟩), ?_, ?_⟩
          · rw [Finset.mem_product]
            exact ⟨Finset.mem_range.mpr hn, Finset.mem_univ _⟩
          · simp [cycleBlockEquiv, cycleElement]
        · -- 2n ∈ cycCut r N because n = (r - 1) * q + rem with q = n / (r - 1) ≤ n < N
          have hsub : 2 * n + 1 - 1 = 2 * n := by omega
          rw [hsub]
          unfold cycCut
          rw [Finset.mem_map]
          have hpos : 0 < r - 1 := by omega
          let q : ℕ := n / (r - 1)
          let rem : ℕ := n % (r - 1)
          have hq_lt : q < N := lt_of_le_of_lt (Nat.div_le_self n (r - 1)) hn
          have hrem_lt : rem < r - 1 := Nat.mod_lt n hpos
          refine ⟨(q, ⟨rem + 1, by omega⟩), ?_, ?_⟩
          · rw [Finset.mem_product]
            exact ⟨Finset.mem_range.mpr hq_lt, Finset.mem_univ _⟩
          · simp only [Equiv.coe_toEmbedding, cycleBlockEquiv, Equiv.coe_fn_mk, cycleElement]
            have hne : ¬ (rem + 1 = 0) := by omega
            simp only [hne, ↓reduceIte, Nat.add_sub_cancel]
            have hdm : (r - 1) * q + rem = n := Nat.div_add_mod n (r - 1)
            omega
    rw [hcard, hfilt]
    push_cast
    ring

end ClosedTraceRearrangementCounterexample

section DisjointJointCutBoundary

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Disjoint joint-cut summand in Chandrasekaran (arXiv:2611.34924v1, Eqs. 5.44–5.45):
`f(i, a) = w i * v a * (1_I(a) - p)`. -/
def jointCutTerm (w : ℕ → ℝ) (v : α → ℝ) (I : Finset α) (x : ℕ × α) : ℝ :=
  w x.1 * v x.2 * ((if x.2 ∈ I then (1 : ℝ) else 0) - ∑ a ∈ I, v a)

/-- Exact settlement of Chandrasekaran Eqs. 5.44–5.45:
for any nonnegative sequence `w : ℕ → ℝ` and any non-degenerate probability distribution `v` on
a finite set `α` with event `I` of probability `p ∈ (0, 1)`:
1. Every fiber sum vanishes (`∑ a, jointCutTerm w v I (i, a) = 0`), so the iterated sum is
   identically zero regardless of whether `w` is summable;
2. The fiber L¹ norm is exactly `2 * p * (1 - p) * w i`;
3. Unconditional summability of `jointCutTerm w v I` over `ℕ × α` holds if and only if
   `Summable w` already holds. -/
theorem disjoint_joint_cut_summable_iff (w : ℕ → ℝ) (v : α → ℝ) (I : Finset α)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ a, 0 ≤ v a) (hv_sum : ∑ a : α, v a = 1)
    (hp_pos : 0 < ∑ a ∈ I, v a) (hp_lt : ∑ a ∈ I, v a < 1) :
    let p := ∑ a ∈ I, v a
    (∀ i : ℕ, ∑ a : α, jointCutTerm w v I (i, a) = 0) ∧
    (∀ i : ℕ, ∑ a : α, |jointCutTerm w v I (i, a)| = 2 * p * (1 - p) * w i) ∧
    (Summable (jointCutTerm w v I) ↔ Summable w) := by
  intro p
  have hfiber_zero : ∀ i : ℕ, ∑ a : α, jointCutTerm w v I (i, a) = 0 := by
    intro i
    unfold jointCutTerm
    have h1 :
        ∑ a : α, w i * v a * ((if a ∈ I then (1 : ℝ) else 0) - p) =
          w i * ((∑ a : α, if a ∈ I then v a else 0) - p * (∑ a : α, v a)) := by
      have hexp : ∀ a : α,
          w i * v a * ((if a ∈ I then (1 : ℝ) else 0) - p) =
            w i * (if a ∈ I then v a else 0) - (w i * p) * v a := by
        intro a
        by_cases ha : a ∈ I <;> simp [ha] <;> ring
      simp_rw [hexp, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [h1, hv_sum, mul_one]
    have hI : (∑ a : α, if a ∈ I then v a else 0) = p := by
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun a : α => a ∈ I) = I := by
        ext a
        simp
      rw [hf]
    rw [hI, sub_self, mul_zero]
  have hfiber_abs : ∀ i : ℕ, ∑ a : α, |jointCutTerm w v I (i, a)| = 2 * p * (1 - p) * w i := by
    intro i
    unfold jointCutTerm
    have hsplit :
        ∑ a : α, |w i * v a * ((if a ∈ I then (1 : ℝ) else 0) - p)| =
          (∑ a ∈ I, |w i * v a * (1 - p)|) + (∑ a ∈ Finset.univ \ I, |w i * v a * (0 - p)|) := by
      have hunion : (Finset.univ : Finset α) = I ∪ (Finset.univ \ I) := by
        ext a
        by_cases ha : a ∈ I <;> simp [ha]
      conv_lhs => rw [hunion]
      rw [Finset.sum_union Finset.disjoint_sdiff]
      congr 1
      · refine Finset.sum_congr rfl fun a ha => by simp [ha]
      · refine Finset.sum_congr rfl fun a ha => ?_
        have hna : a ∉ I := (Finset.mem_sdiff.mp ha).2
        simp [hna]
    rw [hsplit]
    have h1 : ∑ a ∈ I, |w i * v a * (1 - p)| = w i * (1 - p) * p := by
      have heq : ∀ a ∈ I, |w i * v a * (1 - p)| = (w i * (1 - p)) * v a := by
        intro a _
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (hw i) (hv a)) (sub_nonneg.mpr hp_lt.le))]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    have hcomp_sum : ∑ a ∈ Finset.univ \ I, v a = 1 - p := by
      have hunion : I ∪ (Finset.univ \ I) = Finset.univ := by
        ext a
        by_cases ha : a ∈ I <;> simp [ha]
      have htot : (∑ a ∈ I, v a) + (∑ a ∈ Finset.univ \ I, v a) = 1 := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, hunion, hv_sum]
      linarith
    have h2 : ∑ a ∈ Finset.univ \ I, |w i * v a * (0 - p)| = w i * p * (1 - p) := by
      have heq : ∀ a ∈ Finset.univ \ I, |w i * v a * (0 - p)| = (w i * p) * v a := by
        intro a _
        have hneg : w i * v a * (0 - p) = -(w i * v a * p) := by ring
        rw [hneg, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg (hw i) (hv a)) hp_pos.le)]
        ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, hcomp_sum]
    rw [h1, h2]
    ring
  refine ⟨hfiber_zero, hfiber_abs, ?_⟩
  have hc_pos : 0 < 2 * p * (1 - p) := mul_pos (mul_pos zero_lt_two hp_pos) (sub_pos.mpr hp_lt)
  constructor
  · intro hsum
    have habs : Summable (fun x : ℕ × α => |jointCutTerm w v I x|) := hsum.abs
    have hslice : ∀ a : α, Summable (fun i : ℕ => |jointCutTerm w v I (i, a)|) := fun a =>
      habs.comp_injective (fun _ _ h => congrArg Prod.fst h)
    have hsum_fin : Summable (fun i : ℕ => ∑ a : α, |jointCutTerm w v I (i, a)|) :=
      summable_sum fun a _ => hslice a
    have hscaled : Summable (fun i : ℕ => (2 * p * (1 - p)) * w i) :=
      hsum_fin.congr fun i => hfiber_abs i
    exact (summable_mul_left_iff hc_pos.ne').mp hscaled
  · intro hsum_w
    have hpiece : ∀ a : α,
        Summable (fun x : ℕ × α => if x.2 = a then |jointCutTerm w v I x| else 0) := by
      intro a
      have hslice : Summable (fun i : ℕ => |jointCutTerm w v I (i, a)|) := by
        have hdom : ∀ i : ℕ, |jointCutTerm w v I (i, a)| ≤ (2 * p * (1 - p)) * w i := by
          intro i
          rw [← hfiber_abs i]
          exact Finset.single_le_sum (f := fun b => |jointCutTerm w v I (i, b)|)
            (fun b _ => abs_nonneg _) (Finset.mem_univ a)
        exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hdom (hsum_w.mul_left _)
      have hinj : Function.Injective (fun i : ℕ => (i, a)) := fun _ _ h => congrArg Prod.fst h
      have hcomp : Summable ((fun x : ℕ × α => if x.2 = a then |jointCutTerm w v I x| else 0) ∘
          (fun i : ℕ => (i, a))) := by
        convert hslice using 1
        ext i
        simp
      refine (hinj.summable_iff ?_).mp hcomp
      intro x hx
      have hxa : x.2 ≠ a := fun h => hx ⟨x.1, Prod.ext rfl h.symm⟩
      simp [hxa]
    have habs : Summable (fun x : ℕ × α => |jointCutTerm w v I x|) := by
      have hsum_eq : (fun x : ℕ × α => |jointCutTerm w v I x|) =
          fun x => ∑ a : α, if x.2 = a then |jointCutTerm w v I x| else 0 := by
        ext x
        simp
      rw [hsum_eq]
      exact summable_sum fun a _ => hpiece a
    exact habs.of_abs

end DisjointJointCutBoundary

#print axioms finiteDimensional_and_finrank_le_of_isTraceClass_lower_bound
#print axioms finiteDimensional_and_finrank_range_le_of_isTraceClass_lower_bound
#print axioms cycle_union_area_variance_bound
#print axioms cycle_rearrangement_sign_flip
#print axioms disjoint_joint_cut_summable_iff

end D5.S3.Quantum.Analysis.NullConeGravity.ClosedTraceFinitenessBoundary
