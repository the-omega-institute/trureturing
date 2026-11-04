/- GID: D5/S3/Analytic/Laplace/PositiveSpectralBudget
   generality: I
   mirror-B: D5/B/S3/Analytic/Laplace/PositiveSpectralBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Moments.ComplexMGF]
   utility: none
   digest: Positive Laplace boundary kernels satisfy same-sign and short-gap spectral budgets. -/

import D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import Mathlib.Probability.Moments.ComplexMGF

/-! Finite Gram inequalities for boundary limits of positive Laplace transforms. -/

namespace D5.S3.Analytic.Laplace.PositiveSpectralBudget

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ComplexConjugate ComplexOrder

noncomputable section

private lemma laplace_character (σ t y : ℝ) :
    Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (y : ℂ)) =
      (Real.exp (-σ * y) : ℂ) * Complex.exp (((-y * t : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma positive_laplace {μ : Measure ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hi : Integrable (fun y : ℝ => Real.exp (-σ * y)) μ) :
    D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t => (σ : ℂ) * complexMGF id μ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  let f : ℝ → ℝ → ℂ := fun y t =>
    (Real.exp (-σ * y) : ℂ) * Complex.exp (((-y * t : ℝ) : ℂ) * Complex.I)
  have hf : ∀ᵐ y ∂μ,
      D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite (f y) := by
    filter_upwards [] with y
    exact D5.S3.Analytic.Fourier.PositiveDefinite.Closure.smul
      (D5.S3.Analytic.Fourier.PositiveDefinite.Closure.character (-y)) (Real.exp_pos _).le
  have hint (t : ℝ) : Integrable (fun y => f y t) μ := by
    have hce : Integrable (fun y : ℝ =>
        Complex.exp (-((σ : ℂ) + (t : ℂ) * Complex.I) * (y : ℂ))) μ := by
      apply integrable_cexp_mul_of_re_mem_integrableExpSet (by fun_prop)
      change Integrable (fun y : ℝ => Real.exp ((-((σ : ℂ) + (t : ℂ) * Complex.I)).re * y)) μ
      simpa using hi
    simpa only [laplace_character, f] using hce
  have hp := D5.S3.Analytic.Fourier.PositiveDefinite.Closure.smul
    (D5.S3.Analytic.Fourier.PositiveDefinite.Closure.integral hf hint) hσ.le
  simpa only [complexMGF, id_eq, laplace_character, f] using hp

/-- A boundary limit at the opposite frequency exists and is the conjugate
of the given limit. -/
theorem boundary_limit_conjugate {μ : Measure ℝ} {t : ℝ} {z : ℂ}
    (h : Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + (t : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 z)) :
    Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (conj z)) := by
  have heq (σ : ℝ) : (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)) =
      conj ((σ : ℂ) * complexMGF id μ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    rw [complexMGF, complexMGF, ← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← Complex.exp_conj]
    congr 1
    simp only [id_eq, map_mul, map_neg, map_add, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring
  simpa only [Function.comp_def, heq] using (Complex.continuous_conj.tendsto z).comp h

/-- Boundary values of a positive Laplace transform form a nonnegative real
quadratic form whenever the limits at the finite pairwise differences exist. -/
theorem boundary_positive_definite {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    {L : ℝ → ℂ} {ι : Type*} [Fintype ι] (t : ι → ℝ) (a : ι → ℂ)
    (hL : ∀ j k, Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + ((t j - t k : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (L (t j - t k)))) :
    (0 : ℂ) ≤ ∑ j, ∑ k, a j * conj (a k) * L (t j - t k) := by
  classical
  have ht : Tendsto (fun σ : ℝ => ∑ j, ∑ k,
      a j * conj (a k) * ((σ : ℂ) *
        complexMGF id μ (-((σ : ℂ) + ((t j - t k : ℝ) : ℂ) * Complex.I))))
      (𝓝[>] 0) (𝓝 (∑ j, ∑ k, a j * conj (a k) * L (t j - t k))) := by
    apply tendsto_finsetSum
    intro j _
    exact tendsto_finsetSum _ (fun k _ => tendsto_const_nhds.mul (hL j k))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hm := ((positive_laplace hσ (hc σ hσ)) (Fintype.card ι)
    (fun j => -t (e.symm j))).submatrix e
  have H := hm.dotProduct_mulVec_nonneg (fun j => conj (a j))
  change (0 : ℂ) ≤ ∑ j, conj (conj (a j)) * ∑ k,
    ((σ : ℂ) * complexMGF id μ
      (-((σ : ℂ) + ((-t (e.symm (e k)) - -t (e.symm (e j)) : ℝ) : ℂ) * Complex.I))) *
      conj (a k) at H
  simp only [Equiv.symm_apply_apply, Complex.conj_conj, neg_sub_neg, Finset.mul_sum] at H
  convert H using 1
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma boundary_zero_nonnegative_of_limit {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    {z : ℂ} (hL : Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-(σ : ℂ))) (𝓝[>] 0) (𝓝 z)) :
    (0 : ℂ) ≤ z := by
  simpa using boundary_positive_definite hc (fun _ : Unit => (0 : ℝ))
    (L := fun _ => z) (fun _ => (1 : ℂ)) (fun _ _ => by simpa using hL)

private lemma augmented_nonnegative {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    {L : ℝ → ℂ} {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (hL : ∀ j k : Option ι, Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) +
        ((Option.elim j 0 t - Option.elim k 0 t : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (L (Option.elim j 0 t - Option.elim k 0 t))))
    (s : ℝ) (b : ι → ℂ) :
    (0 : ℂ) ≤ (s : ℂ)^2 * L 0 +
      (s : ℂ) * (∑ j : ι, (conj (b j) * L (-t j) + b j * L (t j))) +
      ∑ j, ∑ k, b j * conj (b k) * L (t j - t k) := by
  classical
  have H := boundary_positive_definite hc
    (fun j : Option ι => Option.elim j (0 : ℝ) t)
    (fun j : Option ι => Option.elim j (s : ℂ) b) hL
  convert H using 1
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, sub_self,
    zero_sub, sub_zero, Complex.conj_ofReal, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hs : (∑ j : ι, b j * ((s : ℂ) * L (t j))) =
      (s : ℂ) * ∑ j : ι, b j * L (t j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

/-- Distinct nonzero frequencies with real boundary values at most `-c`
have cardinality at most `4*L(0)^2/c^2`, assuming limits and nonpositive real
parts only at the pairwise differences of the family augmented by zero. -/
theorem same_sign_budget {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    {L : ℝ → ℂ} {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (hL : ∀ j k : Option ι, Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) +
        ((Option.elim j 0 t - Option.elim k 0 t : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (L (Option.elim j 0 t - Option.elim k 0 t))))
    (hneg : ∀ j k : Option ι, Option.elim j 0 t - Option.elim k 0 t ≠ 0 →
      (L (Option.elim j 0 t - Option.elim k 0 t)).re ≤ 0)
    (hinj : Function.Injective t)
    (hne : ∀ j, t j ≠ 0) {c : ℝ} (hcpos : 0 < c)
    (hvalues : ∀ j, (L (t j)).re ≤ -c) :
    (Fintype.card ι : ℝ) * c ^ 2 ≤ 4 * (L 0).re ^ 2 := by
  classical
  let k := (L 0).re
  let n : ℝ := Fintype.card ι
  have hk : 0 ≤ k := (boundary_zero_nonnegative_of_limit hc
    (by simpa using hL none none)).1
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hcross : (∑ j, ((L (-t j)).re + (L (t j)).re)) ≤ -n * c := by
    calc
      _ ≤ ∑ _j : ι, -c := by
        apply Finset.sum_le_sum
        intro j _
        have h1 : (L (-t j)).re ≤ 0 := by
          simpa using hneg none (some j) (by simpa using neg_ne_zero.mpr (hne j))
        have h2 := hvalues j
        linarith
      _ = _ := by simp [n]
  have hinner (j : ι) : (∑ u, (L (t j - t u)).re) ≤ k := by
    calc
      _ ≤ ∑ u, if u = j then k else 0 := by
        apply Finset.sum_le_sum
        intro u _
        by_cases h : u = j
        · subst u; simp [k]
        · rw [ite_eq_right h]
          exact hneg (some j) (some u) (sub_ne_zero.mpr (fun he => h (hinj he).symm))
      _ = _ := by simp
  have hdiag : (∑ j, ∑ u, (L (t j - t u)).re) ≤ n * k := by
    calc
      _ ≤ ∑ _j : ι, k := Finset.sum_le_sum (fun j _ => hinner j)
      _ = _ := by simp [n]
  have hpoly (s : ℝ) (hs : 0 ≤ s) : 0 ≤ s ^ 2 * k - s * n * c + n * k := by
    have H := (augmented_nonnegative hc t hL s (fun _ => (1 : ℂ))).1
    simp only [map_one, one_mul, mul_one, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow,
      Complex.re_sum, zero_mul, mul_zero, sub_zero] at H
    have hcross' := mul_le_mul_of_nonneg_left hcross hs
    change 0 ≤ _ at H
    dsimp [k] at *
    nlinarith
  by_cases hk0 : k = 0
  · have H := hpoly 1 (by norm_num)
    rw [hk0] at H
    have hn0 : n = 0 := by nlinarith
    change n * c ^ 2 ≤ 4 * k ^ 2
    rw [hn0, hk0]
    norm_num
  · have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have H := hpoly (2 * k / c) (by positivity)
    have H' := mul_nonneg H (sq_nonneg c)
    field_simp [hcpos.ne'] at H'
    change n * c ^ 2 ≤ 4 * k ^ 2
    nlinarith

/-- A gap about zero bounds the sum of squared boundary values in every
finite family whose pairwise distances are smaller than the gap, assuming
limits and gap vanishing only at differences of the family augmented by zero. -/
theorem gap_budget {μ : Measure ℝ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    {L : ℝ → ℂ} {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (hL : ∀ j k : Option ι, Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) +
        ((Option.elim j 0 t - Option.elim k 0 t : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 (L (Option.elim j 0 t - Option.elim k 0 t))))
    {δ : ℝ}
    (hgap : ∀ j k : Option ι, 0 < |Option.elim j 0 t - Option.elim k 0 t| →
      |Option.elim j 0 t - Option.elim k 0 t| < δ →
      L (Option.elim j 0 t - Option.elim k 0 t) = 0)
    (hinj : Function.Injective t)
    (hdiam : ∀ j k, |t j - t k| < δ) :
    (∑ j, ‖L (t j)‖ ^ 2) ≤ (L 0).re ^ 2 := by
  classical
  let k := (L 0).re
  let S : ℝ := ∑ j, ‖L (t j)‖ ^ 2
  have hzero : (0 : ℂ) ≤ L 0 :=
    boundary_zero_nonnegative_of_limit hc (by simpa using hL none none)
  have hkreal : (k : ℂ) = L 0 := by
    apply Complex.ext
    · rfl
    · exact hzero.2
  have hk : 0 ≤ k := hzero.1
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hconj (j : ι) : L (-t j) = conj (L (t j)) :=
    tendsto_nhds_unique (by simpa using hL none (some j))
      (boundary_limit_conjugate (by simpa using hL (some j) none))
  have hnorm (j : ι) : conj (L (t j)) * L (t j) = (‖L (t j)‖ ^ 2 : ℝ) := by
    simpa only [Complex.ofReal_pow] using Complex.conj_mul' (L (t j))
  have hterm (j : ι) : conj (-conj (L (t j))) * L (-t j) +
      (-conj (L (t j))) * L (t j) = (-2 : ℂ) * (‖L (t j)‖ ^ 2 : ℝ) := by
    rw [hconj j, map_neg, Complex.conj_conj]
    calc
      _ = (-2 : ℂ) * (conj (L (t j)) * L (t j)) := by ring
      _ = _ := by rw [hnorm]
  have hcross : (∑ j : ι, (conj (-conj (L (t j))) * L (-t j) +
      (-conj (L (t j))) * L (t j))) = (-2 * S : ℝ) := by
    simp_rw [hterm]
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, S]
  have hinner (j : ι) : (∑ u, (-conj (L (t j))) *
      conj (-conj (L (t u))) * L (t j - t u)) = (k : ℂ) * (‖L (t j)‖ ^ 2 : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp only [map_neg, Complex.conj_conj, sub_self, neg_mul_neg]
      rw [hnorm, ← hkreal]
      ring
    · intro u _ hne
      have hgap' : L (t j - t u) = 0 :=
        hgap (some j) (some u) (abs_pos.mpr (sub_ne_zero.mpr
          (fun he => hne (hinj he).symm))) (hdiam j u)
      simp [hgap']
    · simp
  have hpoly (s : ℝ) : 0 ≤ s ^ 2 * k - 2 * s * S + k * S := by
    have H := (augmented_nonnegative hc t hL s (fun j => -conj (L (t j)))).1
    rw [hcross] at H
    simp_rw [hinner] at H
    rw [← Finset.mul_sum, ← Complex.ofReal_sum] at H
    change 0 ≤ (((s : ℂ)^2 * L 0 +
      (s : ℂ) * (-2 * S : ℝ)) + (k : ℂ) * (∑ j, (‖L (t j)‖ ^ 2 : ℝ))).re at H
    rw [← hkreal] at H
    simpa [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_pow,
      ← Complex.ofReal_sum, S, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using H
  change S ≤ k ^ 2
  by_cases hk0 : k = 0
  · have H := hpoly 1
    rw [hk0] at H
    nlinarith
  · have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have H := hpoly k
    nlinarith

#print axioms boundary_limit_conjugate
#print axioms boundary_positive_definite
#print axioms same_sign_budget
#print axioms gap_budget

end
end D5.S3.Analytic.Laplace.PositiveSpectralBudget
