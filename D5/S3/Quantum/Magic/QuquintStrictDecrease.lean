/- GID: D5/S3/Quantum/Magic/QuquintStrictDecrease
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintStrictDecrease
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:d885ced9fe875f3ea62f898fd21397dffe54026cc171199a8466c3631684e761; result=D5/S3/Quantum/Magic/QuquintStrictDecrease.directional_decrease
   digest: Exact normalized change and strict mana decrease on constrained directions. -/

import D5.S3.Quantum.Magic.QuquintFiniteMaximum

noncomputable section
open Matrix Complex Filter
open scoped BigOperators Topology
open D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
open D5.S3.Quantum.Magic.QuquintFiniteMaximum

namespace D5.S3.Quantum.Magic.QuquintStrictDecrease

def normalizedPerturbation (v : tangent) (e : ℝ) : State :=
  ‖psi + e • (v : State)‖⁻¹ • (psi + e • (v : State))

private theorem wigner_real_smul (v : State) (c : ℝ) (q p : Fin 5) :
    wigner (c • v) q p = c ^ 2 * wigner v q p := by
  simp [wigner, mulVec_smul, dotProduct_smul, smul_dotProduct]
  ring

private theorem lOne_real_smul (v : State) (c : ℝ) :
    lOne (c • v) = c ^ 2 * lOne v := by
  simp only [lOne, wigner_real_smul, abs_mul, abs_sq, Finset.mul_sum]

private theorem psi_norm_sq : ‖psi‖ ^ 2 = 1 := by
  have hz : ‖zeta‖ = 1 := by simp [zeta, Complex.norm_exp]
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [psi, Fin.sum_univ_succ, norm_pow, hz,
    Complex.norm_real, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem perturbation_norm_sq (v : tangent) (e : ℝ) :
    ‖psi + e • (v : State)‖ ^ 2 = 1 + e ^ 2 * ‖(v : State)‖ ^ 2 := by
  have h : inner ℂ psi (e • (v : State)) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp [dotProduct_smul, v.property.1]
  rw [norm_add_sq (𝕜 := ℂ), h, psi_norm_sq]
  simp [norm_smul, mul_pow]

private theorem denominator_pos (v : tangent) (e : ℝ) :
    0 < 1 + e ^ 2 * ‖(v : State)‖ ^ 2 := by positivity

theorem normalized_wigner (v : tangent) (e : ℝ) (q p : Fin 5) :
    wigner (normalizedPerturbation v e) q p =
      (wigner psi q p + e * (2 * (star (WithLp.ofLp psi) ⬝ᵥ
        (phasePoint q p *ᵥ WithLp.ofLp (v : State))).re / 5) +
        e ^ 2 * wigner (v : State) q p) / (1 + e ^ 2 * ‖(v : State)‖ ^ 2) := by
  rw [normalizedPerturbation, wigner_real_smul, inv_pow, perturbation_norm_sq,
    wigner_expand, inv_mul_eq_div]

private theorem normalized_lOne (v : tangent) (e : ℝ) :
    lOne (normalizedPerturbation v e) =
      lOne (psi + e • (v : State)) / (1 + e ^ 2 * ‖(v : State)‖ ^ 2) := by
  rw [normalizedPerturbation, lOne_real_smul, inv_pow, perturbation_norm_sq]
  exact inv_mul_eq_div _ _

private theorem abs_polynomial_eventually (a b c : ℝ) (ha : a ≠ 0) :
    ∀ᶠ e : ℝ in 𝓝 0, |a + e * b + e ^ 2 * c| =
      |a| + e * ((SignType.sign a : ℝ) * b) +
        e ^ 2 * ((SignType.sign a : ℝ) * c) := by
  have hc : Continuous (fun e : ℝ => a + e * b + e ^ 2 * c) := by fun_prop
  have ht : Tendsto (fun e : ℝ => a + e * b + e ^ 2 * c) (𝓝 0) (𝓝 a) := by
    simpa using hc.continuousAt.tendsto (x := 0)
  rcases ha.lt_or_gt with h | h
  · filter_upwards [ht.eventually_lt_const h] with e he
    simp [abs_of_neg he, abs_of_neg h, sign_neg h]
    ring
  · filter_upwards [ht.eventually_const_lt h] with e he
    simp [abs_of_pos he, abs_of_pos h, sign_pos h]

private theorem absolute_expansion (v : tangent) :
    ∀ᶠ e : ℝ in 𝓝 0, ∀ qp : Fin 5 × Fin 5,
      |wigner (psi + e • (v : State)) qp.1 qp.2| =
        |wigner psi qp.1 qp.2| +
        e * ((SignType.sign (wigner psi qp.1 qp.2) : ℝ) *
          (2 * (star (WithLp.ofLp psi) ⬝ᵥ
            (phasePoint qp.1 qp.2 *ᵥ WithLp.ofLp (v : State))).re / 5)) +
        e ^ 2 * (if qp ∈ zeroPoints then |wigner (v : State) qp.1 qp.2|
          else (SignType.sign (wigner psi qp.1 qp.2) : ℝ) *
            wigner (v : State) qp.1 qp.2) := by
  classical
  apply eventually_all.mpr
  intro qp
  by_cases hz : wigner psi qp.1 qp.2 = 0
  · have hm : qp ∈ zeroPoints := by simp [zeroPoints, hz]
    have hv := v.property.2 qp hm
    exact Filter.Eventually.of_forall fun e => by
      simp [wigner_expand, hz, hm, hv, abs_mul]
  · have hm : qp ∉ zeroPoints := by simp [zeroPoints, hz]
    simpa only [wigner_expand, if_neg hm] using
      abs_polynomial_eventually (wigner psi qp.1 qp.2)
        (2 * (star (WithLp.ofLp psi) ⬝ᵥ
          (phasePoint qp.1 qp.2 *ᵥ WithLp.ofLp (v : State))).re / 5)
        (wigner (v : State) qp.1 qp.2) hz

private theorem lOne_expansion (v : tangent) :
    ∀ᶠ e : ℝ in 𝓝 0, lOne (psi + e • (v : State)) = lOne psi +
      e ^ 2 * (secondVariation (v : State) + lOne psi * ‖(v : State)‖ ^ 2) := by
  classical
  filter_upwards [absolute_expansion v] with e he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun qp _ => he qp)
  have hfirst : ∑ qp : Fin 5 × Fin 5,
      (SignType.sign (wigner psi qp.1 qp.2) : ℝ) *
        (2 * (star (WithLp.ofLp psi) ⬝ᵥ
          (phasePoint qp.1 qp.2 *ᵥ WithLp.ofLp (v : State))).re / 5) = 0 := by
    rw [Fintype.sum_prod_type]
    exact first_coefficient_zero v
  unfold lOne
  rw [← Fintype.sum_prod_type (fun qp : Fin 5 × Fin 5 =>
    |wigner (psi + e • (v : State)) qp.1 qp.2|)]
  rw [hsum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hfirst, mul_zero, add_zero]
  rw [Finset.sum_ite]
  have hz : Finset.univ.filter (fun qp => qp ∈ zeroPoints) = zeroPoints := by ext; simp
  have hn : Finset.univ.filter (fun qp => qp ∉ zeroPoints) =
      Finset.univ \ zeroPoints := by ext; simp
  rw [hz, hn]
  rw [Fintype.sum_prod_type]
  simp only [secondVariation, lOne]
  ring

theorem exact_change (v : tangent) :
    ∀ᶠ e : ℝ in 𝓝 0, lOne (normalizedPerturbation v e) - lOne psi =
      e ^ 2 * secondVariation (v : State) / (1 + e ^ 2 * ‖(v : State)‖ ^ 2) := by
  filter_upwards [lOne_expansion v] with e he
  rw [normalized_lOne, he]
  field_simp
  ring

private theorem lOne_positive_eventually (v : tangent) :
    ∀ᶠ e : ℝ in 𝓝 0, 0 < lOne (normalizedPerturbation v e) := by
  have hl : 0 < lOne psi := by rw [lOne_psi]; positivity
  have hc : Continuous (fun e : ℝ => lOne psi +
      e ^ 2 * (secondVariation (v : State) + lOne psi * ‖(v : State)‖ ^ 2)) := by
    fun_prop
  have ht := hc.continuousAt.tendsto (x := 0)
  have hp := ht.eventually_const_lt (by simpa using hl)
  filter_upwards [lOne_expansion v, hp] with e he hp
  rw [normalized_lOne, he]
  exact div_pos hp (denominator_pos v e)

theorem directional_decrease (v : tangent) (hv : v ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : ℝ, 0 < |e| → |e| < δ →
      lOne (normalizedPerturbation v e) - lOne psi =
        e ^ 2 * secondVariation (v : State) / (1 + e ^ 2 * ‖(v : State)‖ ^ 2) ∧
      lOne (normalizedPerturbation v e) < lOne psi ∧
      Real.log (lOne (normalizedPerturbation v e)) < Real.log (lOne psi) := by
  have hall := (exact_change v).and (lOne_positive_eventually v)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff_ball.mp hall
  refine ⟨δ, hδ, fun e he heδ => ?_⟩
  have hm := hd e (by simpa [Real.dist_eq] using heδ)
  have hneg : lOne (normalizedPerturbation v e) - lOne psi < 0 := by
    rw [hm.1]
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (by simpa using he.ne'))
        (second_variation_negative v hv)) (denominator_pos v e)
  have hlt := sub_neg.mp hneg
  exact ⟨hm.1, hlt, Real.log_lt_log hm.2 hlt⟩

#print axioms perturbation_norm_sq
#print axioms normalized_wigner
#print axioms exact_change
#print axioms directional_decrease

end D5.S3.Quantum.Magic.QuquintStrictDecrease
