/- GID: D5/S3/Quantum/Matrix/ReflectedSpectralWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/ReflectedSpectralWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite time window suppresses off-diagonal terms in a signed spectral amplitude. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap
import Mathlib.Data.Fin.Rev
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! A finite window bound for spectra with real signed weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Matrix.ReflectedSpectralWindow

open scoped BigOperators
open MeasureTheory

private noncomputable def phase (freq t : ℝ) : ℂ := Complex.exp ((freq * t : ℝ) * Complex.I)

/-- The signed spectral amplitude at time t. -/
noncomputable def amplitude {ι : Type*} [Fintype ι] (freq c : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j, (c j : ℂ) * phase (freq j) t

private theorem pair_re (a b x y t : ℝ) :
    ((a : ℂ) * phase x t * star ((b : ℂ) * phase y t)).re =
      a * b * Real.cos ((x - y) * t) := by
  change ((a : ℂ) * phase x t * (starRingEnd ℂ) ((b : ℂ) * phase y t)).re = _
  have harg : (starRingEnd ℂ) ((y * t : ℝ) * Complex.I) =
      ((-(y * t) : ℝ) : ℂ) * Complex.I := by simp
  have hsum : ((x * t : ℝ) : ℂ) * Complex.I + ((-(y * t) : ℝ) : ℂ) * Complex.I =
      (((x - y) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  simp only [phase, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]
  rw [show (a : ℂ) * Complex.exp ((x * t : ℝ) * Complex.I) *
      ((b : ℂ) * Complex.exp ((-(y * t) : ℝ) * Complex.I)) =
      ((a * b : ℝ) : ℂ) * (Complex.exp ((x * t : ℝ) * Complex.I) *
        Complex.exp ((-(y * t) : ℝ) * Complex.I)) by push_cast; ring]
  rw [← Complex.exp_add, hsum, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem amplitude_energy {ι : Type*} [Fintype ι] (freq c : ι → ℝ) (t : ℝ) :
    ‖amplitude freq c t‖ ^ 2 = ∑ i, ∑ j, c i * c j * Real.cos ((freq i - freq j) * t) := by
  calc
    ‖amplitude freq c t‖ ^ 2 = (amplitude freq c t * (starRingEnd ℂ) (amplitude freq c t)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = ∑ i, ∑ j, c j * c i * Real.cos ((freq j - freq i) * t) := by
      simp only [amplitude, map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_congr rfl (fun i _ =>
        Finset.sum_congr rfl (fun j _ => pair_re (c j) (c i) (freq j) (freq i) t))
    _ = _ := Finset.sum_comm

private theorem cosine_window (τ ω : ℝ) (hω : ω ≠ 0) :
    |∫ t in (0 : ℝ)..τ, Real.cos (ω * t)| ≤ |ω|⁻¹ := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos hω, integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, abs_mul, abs_inv]
  exact mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _)) (Real.abs_sin_le_one _)

/-- Bound the integrated spectral interference by the actual off-diagonal weight. -/
theorem interference_bound {ι : Type*} [Fintype ι] (freq c : ι → ℝ)
    (τ δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |freq i - freq j|) :
    |(∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) - τ * ∑ i, (c i) ^ 2| ≤
      δ⁻¹ * ((∑ i, |c i|) ^ 2 - ∑ i, (c i) ^ 2) := by
  classical
  let kernel (i j : ι) := ∫ t in (0 : ℝ)..τ, Real.cos ((freq i - freq j) * t)
  let cross (i j : ι) := if i = j then 0 else c i * c j * kernel i j
  have kernel_diag (i : ι) : kernel i i = τ := by simp [kernel]
  have integral_energy :
      (∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) =
        ∑ i, ∑ j, c i * c j * kernel i j := by
    simp only [amplitude_energy]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul, kernel]
      · intro j _
        exact (by fun_prop : Continuous fun t : ℝ =>
          c i * c j * Real.cos ((freq i - freq j) * t)).intervalIntegrable _ _
    · intro i _
      exact (by fun_prop : Continuous fun t : ℝ =>
        ∑ j, c i * c j * Real.cos ((freq i - freq j) * t)).intervalIntegrable _ _
  have integral_split :
      ∑ i, ∑ j, c i * c j * kernel i j = τ * (∑ i, (c i) ^ 2) + ∑ i, ∑ j, cross i j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      ∑ j, c i * c j * kernel i j =
          ∑ j, ((if j = i then τ * (c i) ^ 2 else 0) + cross i j) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp [cross, kernel_diag]
          ring
        · simp [cross, h, Ne.symm h]
      _ = _ := by simp [Finset.sum_add_distrib]
  have cross_le (i j : ι) : |cross i j| ≤
      δ⁻¹ * (if i = j then 0 else |c i| * |c j|) := by
    by_cases h : i = j
    · simp [cross, h]
    · have hg := hgap i j h
      have hd : freq i - freq j ≠ 0 := by
        intro hzero
        rw [hzero, abs_zero] at hg
        linarith
      have hk : |kernel i j| ≤ δ⁻¹ :=
        (cosine_window τ _ hd).trans (inv_anti₀ hδ hg)
      rw [show cross i j = c i * c j * kernel i j by simp [cross, h],
        abs_mul, abs_mul, ite_eq_right h, mul_comm δ⁻¹]
      exact mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have cross_weight :
      (∑ i, ∑ j, if i = j then 0 else |c i| * |c j|) =
        (∑ i, |c i|) ^ 2 - ∑ i, (c i) ^ 2 := by
    rw [sq, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have diagonal : (∑ j : ι, if j = i then (c i) ^ 2 else 0) = (c i) ^ 2 := by simp
    rw [Finset.mul_sum, ← diagonal, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · subst j
      simp [← sq, sq_abs]
    · simp [h, Ne.symm h]
  rw [integral_energy, integral_split, add_comm, add_sub_cancel_right]
  calc
    |∑ i, ∑ j, cross i j| ≤ ∑ i, |∑ j, cross i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |cross i j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, δ⁻¹ * (if i = j then 0 else |c i| * |c j|) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cross_le i j
    _ = _ := by simp only [← Finset.mul_sum, cross_weight]

/-- With unit absolute weight, the averaged transition exceeds the stated threshold. -/
theorem average_lower_bound {ι : Type*} [Fintype ι] [Nonempty ι] (freq c : ι → ℝ)
    (hc : (∑ i, |c i|) = 1) (τ δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i j, i ≠ j → δ ≤ |freq i - freq j|)
    (hτ : (Fintype.card ι : ℝ) / (ε * δ) ≤ τ) :
    (1 - ε) / (Fintype.card ι : ℝ) <
      (∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2) / τ := by
  let n : ℝ := Fintype.card ι
  let diagonal : ℝ := ∑ i, (c i) ^ 2
  let total : ℝ := ∫ t in (0 : ℝ)..τ, ‖amplitude freq c t‖ ^ 2
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have ht : 0 < τ := (div_pos hn hεδ).trans_le hτ
  have hcauchy : 1 ≤ n * diagonal := by
    simpa [hc, sq_abs, n, diagonal] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |c i|))
  have hdiag : 1 / n ≤ diagonal := (div_le_iff₀ hn).2 (by simpa [mul_comm] using hcauchy)
  have hdiag_pos : 0 < diagonal := (div_pos one_pos hn).trans_le hdiag
  have herr := interference_bound freq c τ δ hδ hgap
  rw [hc, one_pow] at herr
  have hinterference : - (δ⁻¹ * (1 - diagonal)) ≤ total - τ * diagonal :=
    (abs_le.mp herr).1
  have hstrict : δ⁻¹ * (1 - diagonal) < δ⁻¹ := by
    calc
      _ < δ⁻¹ * 1 := mul_lt_mul_of_pos_left (by linarith) (inv_pos.mpr hδ)
      _ = _ := mul_one _
  have hwindow : δ⁻¹ ≤ τ * ε / n := by
    apply (le_div_iff₀ hn).2
    have h : n ≤ τ * (ε * δ) := (div_le_iff₀ hεδ).1 hτ
    rw [mul_comm δ⁻¹, ← div_eq_mul_inv]
    exact (div_le_iff₀ hδ).2 (by simpa [mul_assoc] using h)
  have main : τ * (1 / n) - τ * ε / n < total := by
    linarith [mul_le_mul_of_nonneg_left hdiag ht.le, hstrict.trans_le hwindow]
  change (1 - ε) / n < total / τ
  apply (lt_div_iff₀ ht).2
  calc
    (1 - ε) / n * τ = τ * (1 / n) - τ * ε / n := by ring
    _ < total := main

open _root_.Matrix WithLp

/-- A vector at one simple eigenvalue is a scalar multiple of the chosen real eigenvector. -/
private theorem simple_eigenvector_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues)
    (i : ι) (w : EuclideanSpace ℝ ι)
    (hw : A *ᵥ ofLp w = hA.eigenvalues i • ofLp w) :
    ∃ s : ℝ, w = s • hA.eigenvectorBasis i := by
  let basis := hA.eigenvectorBasis
  have vanish (j : ι) (hne : j ≠ i) : basis.repr w j = 0 := by
    have hpair : (ofLp (basis j)) ⬝ᵥ (A *ᵥ ofLp w) =
        (A *ᵥ ofLp (basis j)) ⬝ᵥ ofLp w := by
      rw [dotProduct_mulVec, ← vecMul_transpose, hA.isSymm.eq]
    change (ofLp (hA.eigenvectorBasis j)) ⬝ᵥ (A *ᵥ ofLp w) =
      (A *ᵥ ofLp (hA.eigenvectorBasis j)) ⬝ᵥ ofLp w at hpair
    rw [hw, hA.mulVec_eigenvectorBasis j, dotProduct_smul, smul_dotProduct] at hpair
    have eq : (hA.eigenvalues i - hA.eigenvalues j) *
        (ofLp (basis j) ⬝ᵥ ofLp w) = 0 := by
      rw [sub_mul, sub_eq_zero]
      exact hpair
    have hdot := (mul_eq_zero.mp eq).resolve_left (sub_ne_zero.mpr ((hinj.ne hne).symm))
    rw [basis.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simpa [dotProduct_comm] using hdot
  refine ⟨basis.repr w i, ?_⟩
  calc
    w = ∑ j, basis.repr w j • basis j := (basis.sum_repr w).symm
    _ = _ := Finset.sum_eq_single i (fun j _ hne => by rw [vanish j hne, zero_smul])
      (by simp)

/-- Reflection of coordinates preserves the absolute value of each eigenvector entry. -/
theorem reflected_entry_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (hinj : Function.Injective hA.eigenvalues)
    (ρ : ι ≃ ι) (hinv : Function.Involutive ρ)
    (hρ : ∀ x y, A (ρ x) (ρ y) = A x y) (i x : ι) :
    |ofLp (hA.eigenvectorBasis i) (ρ x)| = |ofLp (hA.eigenvectorBasis i) x| := by
  let v := ofLp (hA.eigenvectorBasis i)
  let w : EuclideanSpace ℝ ι := toLp 2 (v ∘ ρ)
  have hv : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have hw : A *ᵥ ofLp w = hA.eigenvalues i • ofLp w := by
    funext x
    calc
      (A *ᵥ ofLp w) x = ∑ y, A (ρ x) (ρ y) * v (ρ y) := by
        simp only [mulVec, dotProduct, w, Function.comp_apply, hρ]
      _ = (A *ᵥ v) (ρ x) := Equiv.sum_comp ρ (fun y => A (ρ x) y * v y)
      _ = (hA.eigenvalues i • ofLp w) x := by rw [hv]; rfl
  obtain ⟨s, hs⟩ := simple_eigenvector_span hA hinj i w hw
  have entry (q : ι) : v (ρ q) = s * v q := by
    simpa only [w, ofLp_toLp, Function.comp_apply, ofLp_smul, Pi.smul_apply, smul_eq_mul, v]
      using congrArg (fun f : EuclideanSpace ℝ ι => ofLp f q) hs
  have hrepeat : v x = s * (s * v x) := by
    rw [← entry x, ← entry (ρ x), hinv x]
  have hproduct : (1 - s * s) * v x = 0 := by linarith
  change |v (ρ x)| = |v x|
  rcases mul_eq_zero.mp hproduct with hs2 | hx
  · have habs : |s| = 1 := by
      rw [← sq, ← sq_abs] at hs2
      nlinarith [abs_nonneg s]
    rw [entry x, abs_mul, habs, one_mul]
  · rw [entry x, hx, mul_zero]

open scoped Matrix.Norms.L2Operator

/-- The time evolution of a real matrix after complexification. -/
noncomputable def evolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : _root_.Matrix ι ι ℝ) (t : ℝ) : _root_.Matrix ι ι ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • A.map Complex.ofReal)

/-- Expand the actual matrix exponential in the signed real endpoint weights. -/
private theorem evolution_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian) (t : ℝ) (x y : ι) :
    evolution A t y x =
      amplitude (fun j => -hA.eigenvalues j)
        (fun j => ofLp (hA.eigenvectorBasis j) y * ofLp (hA.eigenvectorBasis j) x) t := by
  classical
  let v (j : ι) : ι → ℝ := ofLp (hA.eigenvectorBasis j)
  let u (j : ι) : ι → ℂ := fun q => v j q
  have row_dot (q : ι) : (∑ j, v j q * v j x) = if q = x then 1 else 0 := by
    have hu := Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have hi := congrArg (fun M : _root_.Matrix ι ι ℝ => M q x) hu
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.one_apply, v] using hi
  have one_vec : (∑ j, (v j x : ℂ) • u j) = Pi.single x 1 := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, u]
    simp only [mul_comm ((v _ x : ℝ) : ℂ), ← Complex.ofReal_mul, ← Complex.ofReal_sum]
    rw [row_dot q]
    split_ifs <;> simp
  have cast_eigen (j : ι) : A.map Complex.ofReal *ᵥ u j =
      (hA.eigenvalues j : ℂ) • u j := by
    funext q
    have hj := congrFun (hA.mulVec_eigenvectorBasis j) q
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, u, smul_eq_mul] at *
    exact_mod_cast hj
  have time_eigen (j : ι) : evolution A t *ᵥ u j =
      phase (-hA.eigenvalues j) t • u j := by
    unfold evolution phase
    apply D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector
    rw [smul_mulVec, cast_eigen j, smul_smul]
    congr 1
    push_cast
    ring
  calc
    evolution A t y x = (evolution A t *ᵥ Pi.single x 1) y := by
      simp
    _ = (evolution A t *ᵥ (∑ j, (v j x : ℂ) • u j)) y := by rw [one_vec]
    _ = _ := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, time_eigen, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, amplitude, u]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring

/-- A real reflection preserves endpoint weights, giving a lower bound for
the actual averaged matrix-exponential transition. -/
theorem reflected_transition_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : _root_.Matrix ι ι ℝ} (hA : A.IsHermitian)
    (ρ : ι ≃ ι) (hinv : Function.Involutive ρ)
    (hρ : ∀ x y, A (ρ x) (ρ y) = A x y) (x : ι)
    (τ δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (hgap : ∀ i j, i ≠ j → δ ≤ |hA.eigenvalues i - hA.eigenvalues j|)
    (hτ : (Fintype.card ι : ℝ) / (ε * δ) ≤ τ) :
    (1 - ε) / (Fintype.card ι : ℝ) <
      (∫ t in (0 : ℝ)..τ, ‖evolution A t (ρ x) x‖ ^ 2) / τ := by
  let : Nonempty ι := ⟨x⟩
  have hinj : Function.Injective hA.eigenvalues := by
    intro i j hij
    by_contra hne
    have h := hgap i j hne
    rw [hij, sub_self, abs_zero] at h
    exact (not_le_of_gt hδ) h
  let c (j : ι) := ofLp (hA.eigenvectorBasis j) (ρ x) * ofLp (hA.eigenvectorBasis j) x
  have hc : ∑ j, |c j| = 1 := by
    simp only [c, abs_mul, fun j => reflected_entry_abs hA hinj ρ hinv hρ j x, ← sq, sq_abs]
    have h := congrArg (fun M : _root_.Matrix ι ι ℝ => M x x)
      (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, sq] using h
  have hf : ∀ i j, i ≠ j → δ ≤ |-hA.eigenvalues i - -hA.eigenvalues j| := by
    intro i j hne
    simpa only [sub_neg_eq_add, neg_add_eq_sub, abs_sub_comm] using hgap i j hne
  simp_rw [evolution_entry hA]
  exact average_lower_bound _ c hc τ δ ε hδ hε hf hτ

open CentralSqrtTwoDefectGap
open D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence (jacobiMatrix upperBand)

private theorem central_hermitian (n : ℕ) :
    (centralDefect (n + 1) (by omega)).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  unfold centralDefect jacobiMatrix
  simp [Matrix.IsSymm, Matrix.transpose_add, add_assoc, add_comm, add_left_comm]

private theorem central_reflection (n : ℕ) (i j : Fin (2 * (n + 1) - 1 + 1)) :
    centralDefect (n + 1) (by omega) i.rev j.rev =
      centralDefect (n + 1) (by omega) i j := by
  have hleft : i.rev.val + 1 = j.rev.val ↔ j.val + 1 = i.val := by
    simp only [Fin.val_rev]
    omega
  have hright : j.rev.val + 1 = i.rev.val ↔ i.val + 1 = j.val := by
    simp only [Fin.val_rev]
    omega
  have hedge (a b : Fin (2 * (n + 1) - 1 + 1)) (h : a.val + 1 = b.val) :
      centralEdges (n + 1) (by omega) b.rev = centralEdges (n + 1) (by omega) a := by
    unfold centralEdges
    have he : b.rev.val = n + 1 - 1 ↔ a.val = n + 1 - 1 := by
      simp only [Fin.val_rev]
      omega
    simp only [he]
  simp only [centralDefect, jacobiMatrix, Matrix.add_apply, Matrix.diagonal_zero,
    Matrix.zero_apply, zero_add, Matrix.transpose_apply, upperBand, hleft, hright]
  by_cases h : j.val + 1 = i.val
  · have hn : ¬ i.val + 1 = j.val := by omega
    simp [h, hn, hedge j i h]
  · by_cases hh : i.val + 1 = j.val
    · simp [h, hh, hedge i j hh]
    · simp [h, hh]

/-- The distances between all pairs of distinct indexed spectral entries. -/
noncomputable def spectralDifferences {ι : Type*} [Fintype ι] [DecidableEq ι]
    (freq : ι → ℝ) : Finset ℝ :=
  ((Finset.univ.product Finset.univ).filter (fun ij : ι × ι => ij.1 ≠ ij.2)).image
    (fun ij => |freq ij.1 - freq ij.2|)

private theorem spectralDifferences_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (freq : ι → ℝ) : (spectralDifferences freq).Nonempty := by
  obtain ⟨i, j, h⟩ := exists_pair_ne ι
  exact ⟨_, Finset.mem_image.mpr ⟨(i, j), by simp [h], rfl⟩⟩

/-- The minimum of the distances at distinct indices of a finite spectrum. -/
noncomputable def actualGap {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (freq : ι → ℝ) : ℝ :=
  (spectralDifferences freq).min' (spectralDifferences_nonempty freq)

/-- Finite-time endpoint average for the central square-root-two defect. -/
theorem central_defect_endpoint_average (n : ℕ)
    (freq : Fin (2 * (n + 1) - 1 + 1) → ℝ)
    (hfreq : Finset.univ.val.map freq =
      (centralDefect (n + 1) (by omega)).charpoly.roots)
    (τ ε : ℝ) (hε : 0 < ε) :
    letI : Nontrivial (Fin (2 * (n + 1) - 1 + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    let δ := actualGap freq
    0 < δ ∧ (4 * (n + 1 : ℝ) / (ε * δ) ≤ τ →
      (1 - ε) / (2 * (n + 1 : ℝ)) <
        (∫ t in (0 : ℝ)..τ,
          ‖evolution (centralDefect (n + 1) (by omega)) t (Fin.last _) 0‖ ^ 2) / τ) := by
  classical
  let : Nontrivial (Fin (2 * (n + 1) - 1 + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  intro δ
  let A := centralDefect (n + 1) (by omega)
  have hA : A.IsHermitian := central_hermitian n
  have hδ : 0 < δ := by
    have h := (spectralDifferences freq).min'_mem (spectralDifferences_nonempty freq)
    obtain ⟨⟨i, j⟩, hij, hg⟩ := Finset.mem_image.mp h
    have hne : i ≠ j := (Finset.mem_filter.mp hij).2
    change |freq i - freq j| = δ at hg
    rw [← hg]
    exact (by positivity :
      0 < (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3).trans_le
      (central_spectral_gap n freq hfreq i j hne)
  refine ⟨hδ, fun ht => ?_⟩
  have hchoice : Finset.univ.val.map hA.eigenvalues = A.charpoly.roots := by
    simpa using hA.roots_charpoly_eq_eigenvalues.symm
  have hgap (i j : Fin (2 * (n + 1) - 1 + 1)) (hij : i ≠ j) :
      δ ≤ |hA.eigenvalues i - hA.eigenvalues j| := by
    have exists_index (k) : ∃ l, freq l = hA.eigenvalues k := by
      have hm : hA.eigenvalues k ∈ A.charpoly.roots := by
        rw [← hchoice]
        exact Multiset.mem_map.mpr ⟨k, by simp, rfl⟩
      rw [← hfreq] at hm
      obtain ⟨l, _, hl⟩ := Multiset.mem_map.mp hm
      exact ⟨l, hl⟩
    obtain ⟨a, ha⟩ := exists_index i
    obtain ⟨b, hb⟩ := exists_index j
    have hn : a ≠ b := by
      intro hab
      have h := central_spectral_gap n hA.eigenvalues hchoice i j hij
      rw [← ha, ← hb, hab, sub_self, abs_zero] at h
      exact (not_le_of_gt (by positivity : 0 <
        (2 * Real.sqrt 2 / (1 + Real.sqrt 2) ^ 2) / (n + 1 : ℝ) ^ 3)) h
    rw [← ha, ← hb]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(a, b), by simp [hn], rfl⟩)
  have hcard : (Fintype.card (Fin (2 * (n + 1) - 1 + 1)) : ℝ) = 2 * (n + 1 : ℝ) := by
    rw [Fintype.card_fin, Nat.sub_add_cancel (by omega : 1 ≤ 2 * (n + 1))]
    push_cast
    ring
  have htime : (Fintype.card (Fin (2 * (n + 1) - 1 + 1)) : ℝ) / (ε * δ) ≤ τ := by
    rw [hcard]
    exact (div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : 2 * (n + 1 : ℝ) ≤ 4 * (n + 1 : ℝ))
      (mul_nonneg hε.le hδ.le)).trans ht
  have result := reflected_transition_average hA Fin.revPerm Fin.rev_rev
    (central_reflection n) 0 τ δ ε hδ hε hgap htime
  rwa [hcard, show Fin.revPerm (0 : Fin (2 * (n + 1) - 1 + 1)) = Fin.last _ from by
    apply Fin.ext
    simp] at result

end D5.S3.Quantum.Matrix.ReflectedSpectralWindow
