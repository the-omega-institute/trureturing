/- GID: D5/S3/Fourier/Concentration/CenteredDisjointPrincipal
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CenteredDisjointPrincipal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The centered principal contribution has an explicit even-degree coefficient remainder. -/

import D5.S3.Fourier.Concentration.CenteredDisjointCharacterBound

/-! A principal term and remainder for each overlap coefficient, and their signed sum. -/

open Finset PowerSeries
open scoped PowerSeries ComplexConjugate

noncomputable section

namespace D5.S3.Fourier.Concentration.CenteredDisjointPrincipal

open DisjointCharacterEnvelope DisjointCharacterRemainder CenteredDisjointCharacterBound

/-- The coefficient obtained by taking the constant term of every centered even factor. -/
def principalTerm {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) : ℂ :=
  (∏ j ∈ t, -a j) * (c - (∑ j ∈ t, a j)/2)^(d-t.card) / ((d-t.card).factorial : ℂ)

/-- The full real quadratic majorant of the centered residual coefficient. -/
def quadraticBound (u v : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ range (n/2+1), expTermNorm (u,n-2*m) * expTermNorm (v,m)

private theorem even_constant (a : ℂ) : constantCoeff (evenPart a) = 1 := by
  rw [evenPart, constantCoeff_expand, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp

private theorem quadratic_constant (v : ℝ) : constantCoeff (quadraticAxis v) = 1 := by
  rw [quadraticAxis, constantCoeff_expand, ← coeff_zero_eq_constantCoeff_apply,
    realAxis_coeff]
  simp

private theorem even_tail_majorized {J : Type*} (t : Finset J) (a : J → ℂ) (n : ℕ) :
    ‖coeff n ((∏ j ∈ t, evenPart (a j)) - 1)‖ ≤
      coeff n (quadraticAxis (∑ j ∈ t, ‖a j‖^2/24) - 1) := by
  have hprod : ‖coeff n (∏ j ∈ t, evenPart (a j))‖ ≤
      coeff n (quadraticAxis (∑ j ∈ t, ‖a j‖^2/24)) := by
    have h := centered_product_majorized t 0 a n
    have hr : realAxis 0 = 1 := by simp [realAxis]
    simpa only [axis_zero, norm_zero, hr, one_mul] using h
  by_cases hn : n = 0
  · subst n
    simp only [coeff_zero_eq_constantCoeff_apply, map_sub, map_prod, even_constant,
      prod_const_one, map_one, sub_self, norm_zero, quadratic_constant, le_refl]
  · simpa only [map_sub, coeff_one, ite_eq_right hn, sub_zero] using hprod

private theorem coefficient_error {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ)
    (hd : t.card ≤ d) :
    let n := d-t.card
    let u := c-(∑ j ∈ t, a j)/2
    let v := (∑ j ∈ t, ‖a j‖^2)/24
    ‖overlapCoefficient t c a d - principalTerm t c a d‖ ≤
      (∏ j ∈ t, ‖a j‖) * (quadraticBound ‖u‖ v n - expTermNorm (‖u‖,n)) := by
  classical
  intro n u v
  have hdifference : overlapCoefficient t c a d - principalTerm t c a d =
      (∏ j ∈ t, -a j) * coeff n (axis u * ((∏ j ∈ t, evenPart (a j)) - 1)) := by
    dsimp [overlapCoefficient, principalTerm, n, u]
    rw [centered_product, coeff_C_mul, coeff_X_pow_mul', ite_eq_left hd, mul_sub, map_sub,
      mul_one, axis_coeff]
    ring
  have h := coeff_mul_majorized (axis u) ((∏ j ∈ t, evenPart (a j)) - 1)
    (realAxis ‖u‖) (quadraticAxis (∑ j ∈ t, ‖a j‖^2/24) - 1)
    (fun m => by rw [axis_norm_coeff, realAxis_coeff]) (even_tail_majorized t a) n
  rw [← sum_div] at h
  simp only [mul_sub, map_sub, mul_one, quadratic_coefficient, realAxis_coeff] at h
  rw [hdifference, norm_mul, norm_prod]
  simp only [norm_neg]
  exact mul_le_mul_of_nonneg_left (by simpa [quadraticBound, expTermNorm, v, mul_sub] using h)
    (prod_nonneg fun _ _ => norm_nonneg _)

private theorem principal_norm {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) :
    ‖principalTerm t c a d‖ = (∏ j ∈ t, ‖a j‖) *
      expTermNorm (‖c - (∑ j ∈ t, a j)/2‖,d-t.card) := by
  simp only [principalTerm, norm_div, norm_mul, norm_prod, norm_neg, norm_pow,
    Complex.norm_natCast, expTermNorm]
  ring

/-- Retain the principal coefficient, and control the error in both amplitude and squared norm. -/
theorem centered_principal_remainder {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ)
    (hd : t.card ≤ d) :
    let n := d-t.card
    let u := c-(∑ j ∈ t, a j)/2
    let v := (∑ j ∈ t, ‖a j‖^2)/24
    let A := ∏ j ∈ t, ‖a j‖
    let readout := fun x : ℝ × ℝ × ℕ => quadraticBound x.1 x.2.1 x.2.2
    let H := readout (‖u‖,v,n)
    let h := expTermNorm (‖u‖,n)
    ‖overlapCoefficient t c a d - principalTerm t c a d‖ ≤ A*(H-h) ∧
    |‖overlapCoefficient t c a d‖^2 - ‖principalTerm t c a d‖^2| ≤ A^2*(H^2-h^2) := by
  classical
  intro n u v A readout H h
  have herror : ‖overlapCoefficient t c a d - principalTerm t c a d‖ ≤ A*(H-h) :=
    coefficient_error t c a d hd
  refine ⟨herror, ?_⟩
  have hp : ‖principalTerm t c a d‖ = A*h := principal_norm t c a d
  have hc : ‖overlapCoefficient t c a d‖ ≤ A*H := by
    simpa only [ite_eq_left hd, quadraticBound, A, H, readout, n, u, v] using
      (centered_overlap_bound t c a d)
  have hN : 0 ≤ A*(H-h) := (norm_nonneg _).trans herror
  calc
    _ = |‖overlapCoefficient t c a d‖ - ‖principalTerm t c a d‖| *
        (‖overlapCoefficient t c a d‖ + ‖principalTerm t c a d‖) := by
      rw [show ‖overlapCoefficient t c a d‖^2 - ‖principalTerm t c a d‖^2 =
          (‖overlapCoefficient t c a d‖ - ‖principalTerm t c a d‖) *
            (‖overlapCoefficient t c a d‖ + ‖principalTerm t c a d‖) by ring,
        abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ (A*(H-h)) * (A*H + A*h) := by
      apply mul_le_mul ((abs_norm_sub_norm_le _ _).trans herror) (add_le_add hc hp.le)
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) hN
    _ = _ := by ring

/-- The alternating sum of principal squared norms approximates the real mixed coefficient,
with error bounded by the sum of the centered squared remainders. -/
theorem mixed_centered_principal_error {J : Type*} (s : Finset J) (a : J → ℂ) (d : ℕ) :
    let c := ∑ j ∈ s, a j
    let admissible := s.powerset.filter (fun t => t.card ≤ d)
    let readout := fun x : ℝ × ℝ × ℕ => quadraticBound x.1 x.2.1 x.2.2
    let H := fun t => readout (‖c-(∑ j ∈ t, a j)/2‖,
      (∑ j ∈ t, ‖a j‖^2)/24, d-t.card)
    let h := fun t => expTermNorm (‖c-(∑ j ∈ t, a j)/2‖,d-t.card)
    |(coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re -
      ∑ t ∈ admissible, (-1 : ℝ)^t.card * ‖principalTerm t c a d‖^2| ≤
        ∑ t ∈ admissible, (∏ j ∈ t, ‖a j‖)^2 * (H t^2-h t^2) := by
  classical
  intro c admissible readout H h
  have hfull := congrArg Complex.re (signed_overlap_expansion s a d).1
  simp only [Complex.re_sum, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hfull
  change (coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re =
    ∑ t ∈ admissible, (-1 : ℝ)^t.card * ‖overlapCoefficient t c a d‖^2 at hfull
  rw [hfull, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_)
  have hd := (mem_filter.mp ht).2
  rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact (centered_principal_remainder t c a d hd).2

#print axioms centered_principal_remainder
#print axioms mixed_centered_principal_error

end D5.S3.Fourier.Concentration.CenteredDisjointPrincipal
