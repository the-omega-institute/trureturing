/- GID: D5/S3/Quantum/Divergence/Qubit/SignedProfile
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/Qubit/SignedProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Squared overlaps determine the signed qubit positive-part trace. -/

import D5.S3.Observer.BornReduction
import D5.S3.Weil.ZetaLinear.HermitianPosPart
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The spectrum and overlap dependence of finite signed pure-qubit contrasts. -/

set_option autoImplicit false

noncomputable section

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.Qubit.SignedProfile

variable {ι : Type*}

/-- The signed contrast of pure qubit preparations. -/
def contrast [Fintype ι] (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, a i • vecMulVec (ψ i) (star (ψ i))

/-- Squared overlap of two preparations in the same family. -/
def overlap (ψ : ι → Fin 2 → ℂ) (i j : ι) : ℝ :=
  Complex.normSq (star (ψ i) ⬝ᵥ ψ j)

/-- Signed overlap discriminant, expressed using one term per unordered pair.
For unit preparations it is the squared spectral gap of the contrast. -/
def gapSq [Fintype ι] [LinearOrder ι] (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) : ℝ :=
  (∑ i, a i) ^ 2 - 4 * ∑ ij ∈ (univ : Finset (ι × ι)).filter (fun ij => ij.1 < ij.2),
    a ij.1 * a ij.2 * (1 - overlap ψ ij.1 ij.2)

private theorem contrast_hermitian [Fintype ι] (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) :
    (contrast a ψ).IsHermitian := by
  classical
  unfold contrast
  induction (univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (show (vecMulVec (ψ i) (star (ψ i))).IsHermitian by
      simp [IsHermitian, conjTranspose_vecMulVec]).smul
        (by simp [IsSelfAdjoint]) |>.add ih

private theorem contrast_trace [Fintype ι] (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    (contrast a ψ).trace = ((∑ i, a i : ℝ) : ℂ) := by
  rw [contrast, trace_sum, Complex.ofReal_sum]
  exact sum_congr rfl fun i _ => by
    rw [trace_smul, trace_vecMulVec, dotProduct_comm (ψ i), hψ i]
    simp [Complex.real_smul]

private theorem sum_eq_twice_pairs [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * ∑ ij ∈ (univ : Finset (ι × ι)).filter (fun ij => ij.1 < ij.2), f ij.1 ij.2 := by
  rw [sum_filter, Fintype.sum_prod_type]
  have hswap :
      (∑ i, ∑ j, if j < i then f i j else 0) =
        ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hsymm j i]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, ((if i < j then f i j else 0) +
        (if j < i then f i j else 0)) := by
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h, not_lt_of_ge h.le]
      · simp [hdiag]
      · simp [h, not_lt_of_ge h.le]
    _ = _ := by simp only [sum_add_distrib, hswap, two_mul]

private theorem trace_pair (u v : Fin 2 → ℂ) :
    (vecMulVec u (star u) * vecMulVec v (star v)).trace =
      (Complex.normSq (star u ⬝ᵥ v) : ℂ) := by
  rw [trace_mul_comm]
  simpa only [D5.S3.Observer.Conditioning.recordWeight,
    D5.S3.Quantum.FiniteDimensional.bornProbability, Complex.normSq_eq_norm_sq] using
    D5.S3.Observer.BornReduction.rank_one_pure_state_modulus_square_reduction
      (fun _ : Unit => vecMulVec u (star u)) (vecMulVec v (star v)) () u v rfl rfl

/-- The trace-square invariant of the contrast expands over all ordered overlaps. -/
private theorem trace_contrast_sq [Fintype ι] (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) :
    ((contrast a ψ * contrast a ψ).trace).re =
      ∑ i, ∑ j, a i * a j * overlap ψ i j := by
  simp only [contrast, Finset.sum_mul, Finset.mul_sum, trace_sum, Complex.re_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
    rw [smul_mul_assoc, mul_smul_comm, trace_smul, trace_smul, trace_mul_comm, trace_pair]
    simp only [overlap, Complex.real_smul, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring

/-- The signed overlap expansion computes the discriminant of the contrast. -/
theorem gapSq_eq_trace_det [Fintype ι] [LinearOrder ι]
    (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    gapSq a ψ = (∑ i, a i) ^ 2 - 4 * (contrast a ψ).det.re := by
  let A := contrast a ψ
  let S := ∑ i, a i
  have hsymm (i j : ι) : overlap ψ i j = overlap ψ j i := by
    have h := congrArg Complex.re
      (trace_mul_comm (vecMulVec (ψ i) (star (ψ i))) (vecMulVec (ψ j) (star (ψ j))))
    simpa only [trace_pair, Complex.ofReal_re, overlap] using h
  have hdiag (i : ι) : overlap ψ i i = 1 := by simp [overlap, hψ]
  have hpairs := sum_eq_twice_pairs (fun i j => a i * a j * (1 - overlap ψ i j))
    (fun i j => by rw [hsymm i j, mul_comm (a i) (a j)])
    (fun i => by rw [hdiag, sub_self, mul_zero])
  have hsum : (∑ i, ∑ j, a i * a j * (1 - overlap ψ i j)) =
      S ^ 2 - (A * A).trace.re := by
    simp only [mul_sub, mul_one, sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [trace_contrast_sq a ψ, pow_two]
  have htrace : A.trace.re = S := by rw [contrast_trace a ψ hψ, Complex.ofReal_re]
  have hinvariant : (A * A).trace.re = A.trace.re ^ 2 - 2 * A.det.re := by
    have h : (A * A).trace = A.trace ^ 2 - 2 * A.det := by
      simp [Matrix.trace, Matrix.mul_apply, det_fin_two, Fin.sum_univ_two]
      ring
    have him : A.trace.im = 0 := by rw [contrast_trace a ψ hψ, Complex.ofReal_im]
    simpa [pow_two, Complex.mul_re, him] using congrArg Complex.re h
  unfold gapSq
  change S ^ 2 - _ = S ^ 2 - 4 * A.det.re
  rw [hsum, hinvariant, htrace] at hpairs
  linarith only [hpairs]

private theorem positive_pair (x y : ℝ) :
    max x 0 + max y 0 = (x + y + max |x + y| |x - y|) / 2 := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · have hxy : |x - y| ≤ x + y := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [max_eq_left hx, max_eq_left hy, abs_of_nonneg (add_nonneg hx hy), max_eq_left hxy]
    ring
  · have hxy : |x + y| ≤ x - y := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [max_eq_left hx, max_eq_right hy, abs_of_nonneg (by linarith : 0 ≤ x - y),
      max_eq_right hxy]
    ring
  · have hxy : |x + y| ≤ -(x - y) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [max_eq_right hx, max_eq_left hy, abs_of_nonpos (by linarith : x - y ≤ 0),
      max_eq_right hxy]
    ring
  · have hxy : |x - y| ≤ -(x + y) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [max_eq_right hx, max_eq_right hy, abs_of_nonpos (add_nonpos hx hy), max_eq_left hxy]
    ring

/-- Positive-part trace for any finite signed ensemble of unit qubit preparations. -/
theorem trace_posPart_contrast [Fintype ι] [LinearOrder ι]
    (a : ι → ℝ) (ψ : ι → Fin 2 → ℂ) (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    (contrast a ψ)⁺.trace.re =
      ((∑ i, a i) + max |∑ i, a i| (Real.sqrt (gapSq a ψ))) / 2 := by
  let A := contrast a ψ
  have hA : A.IsHermitian := contrast_hermitian a ψ
  let eig := hA.eigenvalues
  have htrace : eig 0 + eig 1 = ∑ i, a i := by
    have h := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    simpa [eig, A, contrast_trace a ψ hψ, Fin.sum_univ_two] using h.symm
  have hdet : A.det.re = eig 0 * eig 1 := by
    simpa [eig, Fin.prod_univ_two, ← Complex.ofReal_mul] using
      congrArg Complex.re hA.det_eq_prod_eigenvalues
  have hgap : gapSq a ψ = (eig 0 - eig 1) ^ 2 := by
    rw [gapSq_eq_trace_det a ψ hψ, ← htrace, hdet]
    ring
  have hpos : A⁺ = RHLinalg.hermPosPart hA := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
    rfl
  have hspectral : A⁺.trace.re = max (eig 0) 0 + max (eig 1) 0 := by
    rw [hpos]
    exact (RHLinalg.rtrace_hermPosPart hA).trans (by rw [Fin.sum_univ_two]; rfl)
  change A⁺.trace.re = _
  rw [hspectral, positive_pair, hgap, Real.sqrt_sq_eq_abs, htrace]

/-- When every other overlap is fixed, the weighted change of the selected overlap
determines the exact change of the signed overlap discriminant. -/
private theorem gapSq_sub_of_pair [Fintype ι] [LinearOrder ι] (a : ι → ℝ)
    (ψ χ : ι → Fin 2 → ℂ) {i j : ι} (hij : i < j)
    (hfix : ∀ k l, k < l → (k, l) ≠ (i, j) → overlap ψ k l = overlap χ k l) :
    gapSq a χ - gapSq a ψ = 4 * (a i * a j) * (overlap χ i j - overlap ψ i j) := by
  unfold gapSq
  rw [sub_sub_sub_cancel_left, ← mul_sub, ← sum_sub_distrib]
  rw [Finset.sum_eq_single (i, j)]
  · ring
  · intro p hp hne
    rw [hfix p.1 p.2 (mem_filter.mp hp).2 hne, sub_self]
  · simp [hij]

/-- A nonnegative weighted change of the only changed overlap gives a weak increase in the
trace of the positive part for unit preparations.
This includes increasing the overlap for a nonnegative weight product and decreasing it
for a nonpositive weight product. -/
theorem trace_posPart_contrast_le_of_pair [Fintype ι] [LinearOrder ι] (a : ι → ℝ)
    (ψ χ : ι → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (hχ : ∀ i, star (χ i) ⬝ᵥ χ i = 1)
    {i j : ι} (hij : i < j)
    (hfix : ∀ k l, k < l → (k, l) ≠ (i, j) → overlap ψ k l = overlap χ k l)
    (hpair : 0 ≤ (a i * a j) * (overlap χ i j - overlap ψ i j)) :
    (contrast a ψ)⁺.trace.re ≤ (contrast a χ)⁺.trace.re := by
  have hg : gapSq a ψ ≤ gapSq a χ := by
    apply sub_nonneg.mp
    rw [gapSq_sub_of_pair a ψ χ hij hfix, mul_assoc]
    exact mul_nonneg (by norm_num) hpair
  rw [trace_posPart_contrast a ψ hψ, trace_posPart_contrast a χ hχ]
  exact div_le_div_of_nonneg_right
    (add_le_add_right (max_le_max_left _ (Real.sqrt_le_sqrt hg)) _) (by norm_num)

private theorem overlap_phase_lower (u v : Fin 2 → ℂ) :
    (‖u 0‖ * ‖v 0‖ - ‖u 1‖ * ‖v 1‖) ^ 2 ≤ Complex.normSq (star u ⬝ᵥ v) := by
  let x := star (u 0) * v 0
  let y := star (u 1) * v 1
  have h : |‖x‖ - ‖y‖| ≤ ‖x + y‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using abs_norm_sub_norm_le x (-y)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
  simpa [x, y, dotProduct, Fin.sum_univ_two, Complex.normSq_eq_norm_sq, norm_mul] using hsq

/-- In the chosen basis, the squared overlap is at least `sin (φ - θ) ^ 2`
for vectors with coordinate magnitudes `(cos θ, sin θ)` and `(sin φ, cos φ)`.
The displayed real vectors are unit and have squared overlap `sin (φ - θ) ^ 2`
for all angles. When all four prescribed magnitudes are nonnegative, as for
`θ, φ ∈ [0, π / 2]`, these vectors have the prescribed magnitudes and attain the bound. -/
theorem phase_minimum (θ φ : ℝ) :
    let u₀ : Fin 2 → ℂ := ![(Real.cos θ : ℂ), (Real.sin θ : ℂ)]
    let v₀ : Fin 2 → ℂ := ![(Real.sin φ : ℂ), -(Real.cos φ : ℂ)]
    (star u₀ ⬝ᵥ u₀ = 1 ∧ star v₀ ⬝ᵥ v₀ = 1) ∧
    Complex.normSq (star u₀ ⬝ᵥ v₀) = Real.sin (φ - θ) ^ 2 ∧
    ∀ (u v : Fin 2 → ℂ),
      ‖u 0‖ = Real.cos θ → ‖u 1‖ = Real.sin θ →
      ‖v 0‖ = Real.sin φ → ‖v 1‖ = Real.cos φ →
      Real.sin (φ - θ) ^ 2 ≤ Complex.normSq (star u ⬝ᵥ v) := by
  dsimp only
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h : (Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ : ℝ) = 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq θ]
    simpa only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal, map_neg, neg_mul_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_one] using
      congrArg Complex.ofReal h
  · have h : (Real.sin φ * Real.sin φ + Real.cos φ * Real.cos φ : ℝ) = 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq φ]
    simpa only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal, map_neg, neg_mul_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_one] using
      congrArg Complex.ofReal h
  · have h :
        star (![(Real.cos θ : ℂ), (Real.sin θ : ℂ)] : Fin 2 → ℂ) ⬝ᵥ
          ![(Real.sin φ : ℂ), -(Real.cos φ : ℂ)] = (Real.sin (φ - θ) : ℂ) := by
      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal, Real.sin_sub,
        Complex.ofReal_sub, Complex.ofReal_mul]
      ring
    rw [h, Complex.normSq_ofReal, pow_two]
  · intro u v hu₀ hu₁ hv₀ hv₁
    have h := overlap_phase_lower u v
    rw [hu₀, hu₁, hv₀, hv₁] at h
    rw [Real.sin_sub]
    convert h using 1
    ring

private theorem overlap_eq_except_outer_pair {ψ χ : Fin 3 → Fin 2 → ℂ}
    (h01 : overlap ψ 0 1 = overlap χ 0 1) (h12 : overlap ψ 1 2 = overlap χ 1 2)
    (k l : Fin 3) (hkl : k < l) (hne : (k, l) ≠ (0, 2)) :
    overlap ψ k l = overlap χ k l := by
  fin_cases k <;> fin_cases l
  all_goals
    first
    | exact h01
    | exact h12
    | exact (hne rfl).elim
    | exfalso
      revert hkl
      decide

/-- With the middle preparation fixed to `e₀ = (1, 0)`, the explicit opposite-phase
triple attains the maximum positive-part trace among unit triples with the prescribed
coordinate magnitudes and a nonpositive product of the outer weights. -/
theorem trace_posPart_contrast_isGreatest_opposite_phase (a : Fin 3 → ℝ) (θ φ : ℝ)
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (hφ : φ ∈ Set.Icc 0 (Real.pi / 2))
    (ha : a 0 * a 2 ≤ 0) :
    let e₀ : Fin 2 → ℂ := ![1, 0]
    let u₀ : Fin 2 → ℂ := ![(Real.cos θ : ℂ), (Real.sin θ : ℂ)]
    let v₀ : Fin 2 → ℂ := ![(Real.sin φ : ℂ), -(Real.cos φ : ℂ)]
    let ψ₀ : Fin 3 → Fin 2 → ℂ := ![u₀, e₀, v₀]
    let domain : Set (Fin 3 → Fin 2 → ℂ) := {ψ |
      ψ 1 = e₀ ∧ ‖ψ 0 0‖ = Real.cos θ ∧ ‖ψ 0 1‖ = Real.sin θ ∧
      ‖ψ 2 0‖ = Real.sin φ ∧ ‖ψ 2 1‖ = Real.cos φ ∧
      ∀ i, star (ψ i) ⬝ᵥ ψ i = 1}
    IsGreatest ((fun ψ => (contrast a ψ)⁺.trace.re) '' domain) (contrast a ψ₀)⁺.trace.re := by
  intro e₀ u₀ v₀ ψ₀ domain
  have hphase := phase_minimum θ φ
  have he₀ : star e₀ ⬝ᵥ e₀ = 1 := by simp [e₀, dotProduct, Fin.sum_univ_two]
  have hψ₀ : ∀ i, star (ψ₀ i) ⬝ᵥ ψ₀ i = 1 := by
    intro i
    fin_cases i
    · exact hphase.1.1
    · exact he₀
    · exact hphase.1.2
  have hsin (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (le_trans hx.2 (by linarith [Real.pi_pos]))
  have hcos (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨le_trans (by linarith [Real.pi_pos]) hx.1, hx.2⟩
  have hmem₀ : ψ₀ ∈ domain := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, hψ₀⟩
    · change ‖(Real.cos θ : ℂ)‖ = Real.cos θ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcos θ hθ)]
    · change ‖(Real.sin θ : ℂ)‖ = Real.sin θ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsin θ hθ)]
    · change ‖(Real.sin φ : ℂ)‖ = Real.sin φ
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hsin φ hφ)]
    · change ‖-(Real.cos φ : ℂ)‖ = Real.cos φ
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcos φ hφ)]
  refine ⟨⟨ψ₀, hmem₀, rfl⟩, ?_⟩
  rintro _ ⟨ψ, ⟨href, hu0, hu1, hv0, hv1, hψ⟩, rfl⟩
  have referenceOverlaps (χ : Fin 3 → Fin 2 → ℂ) (hχ : χ 1 = e₀) :
      overlap χ 0 1 = ‖χ 0 0‖ ^ 2 ∧ overlap χ 1 2 = ‖χ 2 0‖ ^ 2 := by
    constructor <;>
      simp [overlap, hχ, e₀, dotProduct, Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
  obtain ⟨href₀, hu0', _, hv0', _, _⟩ := hmem₀
  have h01 : overlap ψ 0 1 = overlap ψ₀ 0 1 := by
    rw [(referenceOverlaps ψ href).1, (referenceOverlaps ψ₀ href₀).1, hu0, hu0']
  have h12 : overlap ψ 1 2 = overlap ψ₀ 1 2 := by
    rw [(referenceOverlaps ψ href).2, (referenceOverlaps ψ₀ href₀).2, hv0, hv0']
  have h02 : overlap ψ₀ 0 2 ≤ overlap ψ 0 2 := by
    change Complex.normSq (star u₀ ⬝ᵥ v₀) ≤ Complex.normSq (star (ψ 0) ⬝ᵥ ψ 2)
    rw [hphase.2.1]
    exact hphase.2.2 _ _ hu0 hu1 hv0 hv1
  exact trace_posPart_contrast_le_of_pair a ψ ψ₀ hψ hψ₀ (i := 0) (j := 2) (by decide)
    (overlap_eq_except_outer_pair h01 h12)
    (mul_nonneg_of_nonpos_of_nonpos ha (sub_nonpos.mpr h02))

#print axioms gapSq_eq_trace_det
#print axioms trace_posPart_contrast
#print axioms trace_posPart_contrast_le_of_pair
#print axioms phase_minimum
#print axioms trace_posPart_contrast_isGreatest_opposite_phase

namespace Pairing

export _root_.D5.S3.Quantum.Divergence.Qubit.SignedProfile (trace_pair)

end Pairing

end D5.S3.Quantum.Divergence.Qubit.SignedProfile
