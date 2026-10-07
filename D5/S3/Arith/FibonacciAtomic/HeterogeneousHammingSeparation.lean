/- GID: D5/S3/Arith/FibonacciAtomic/HeterogeneousHammingSeparation
   generality: firstGate
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/HeterogeneousHammingSeparation
   mirror-productExpectation: none(waiver:unbounded-symbolic-estimate)
   anchors: []
   utility: none
   digest: Sharp heterogeneous Hamming separation is strictly below squared separation. -/

import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.HeterogeneousHammingSeparation

open LiteralWindowEnd (Window first last)
open LegalPriorityTeacher (Input Roles)
open HeterogeneousTeacherSeparation
open scoped BigOperators

/-- Actual classification disagreement under the heterogeneous product law. -/
def hamming {n : ℕ} (μ : Laws n) (t u : Roles n) : ℝ :=
  productExpectation μ (fun w => if classValue t w = classValue u w then 0 else 1)

/-- Sharp classification separation over the complete heterogeneous class. -/
def eta (rho : ℝ) : ℝ := 4 * rho ^ 2 * (1 - 2 * rho) * (1 + 3 * rho)

/-- First-window law maximizing its high endpoint while preserving all five masses. -/
def tilted (rho : ℝ) : Window → ℝ
  | .high => 1 - 4 * rho
  | _ => rho

/-- A single attaining product law: tilted at position zero, extremal elsewhere. -/
def attainingLaw (n : ℕ) (rho : ℝ) : Laws n :=
  fun i => if i.val = 0 then tilted rho else extremal rho

set_option maxHeartbeats 4000000 in
-- The exact indicator calculation retains all five endpoint bits before factorization.
/-- A universal lower bound, attained by the first four windows with all other legal
position laws arbitrary, and a strict comparison with squared separation. -/
theorem result (n : ℕ) (hn : 4 ≤ n) (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    let t : Roles n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
      by change (0 : ℕ) < 1; omega, by change (1 : ℕ) < 2; omega⟩
    let u : Roles n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩,
      by change (0 : ℕ) < 1; omega, by change (1 : ℕ) < 3; omega⟩
    (∀ μ : Laws n, Admissible rho μ → ∀ v w : Roles n, v ≠ w →
      eta rho ≤ hamming μ v w) ∧
    (t ≠ u ∧ Admissible rho (attainingLaw n rho) ∧
      hamming (attainingLaw n rho) t u = eta rho ∧
      ∀ μ : Laws n, Admissible rho μ →
        (∀ i : Fin n, i.val < 4 → μ i = attainingLaw n rho i) →
        hamming μ t u = eta rho) ∧
    eta rho < gamma rho := by
  classical
  dsimp only
  have same_head (μ : Laws n) (hsum : ∀ i, ∑ a, μ i a = 1)
      (t u : Roles n) (hp : t.p = u.p) (hq : t.q = u.q) (hrs : t.r ≠ u.r) :
      hamming μ t u = (highMarginal μ t.q - highMarginal μ t.p * μ t.q .ends) *
        (lowMarginal μ t.r + lowMarginal μ u.r - 2 * lowMarginal μ t.r * lowMarginal μ u.r) := by
    have hpr := ne_of_lt (lt_trans t.pq t.qr)
    have hps : t.p ≠ u.r := by simpa [hp] using ne_of_lt (lt_trans u.pq u.qr)
    have hqs : t.q ≠ u.r := by simpa [hq] using ne_of_lt u.qr
    have point (w : Input n) :
        (if classValue t w = classValue u w then (0 : ℝ) else 1) =
          (highIndicator (w t.q) * lowIndicator (w t.r) + highIndicator (w t.q) * lowIndicator (w
              u.r) -
            2 * (highIndicator (w t.q) * lowIndicator (w t.r) * lowIndicator (w u.r))) -
          (highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) * lowIndicator
              (w t.r) +
            highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) * lowIndicator
                (w u.r) -
            2 * (highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) *
              lowIndicator (w t.r) * lowIndicator (w u.r))) := by
      rw [class_value_formula, class_value_formula]
      simp only [firstGate, ← hp, ← hq]
      rcases (endpoint_indicators_binary (w t.p)).1 with ha | ha <;>
        rcases (endpoint_indicators_binary (w t.q)).1 with hb | hb <;>
        rcases (endpoint_indicators_binary (w t.q)).2 with hc | hc <;>
        rcases (endpoint_indicators_binary (w t.r)).2 with hd | hd <;>
        rcases (endpoint_indicators_binary (w u.r)).2 with he | he <;>
        norm_num [ha, hb, hc, hd, he]
    have split : hamming μ t u =
        productExpectation μ (fun w => highIndicator (w t.q) * lowIndicator (w t.r) +
            highIndicator (w t.q) * lowIndicator (w u.r) -
          2 * (highIndicator (w t.q) * lowIndicator (w t.r) * lowIndicator (w u.r))) -
        productExpectation μ (fun w => highIndicator (w t.p) * (lowIndicator (w t.q) *
            highIndicator (w t.q)) * lowIndicator (w t.r) +
          highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) * lowIndicator (w
              u.r) -
          2 * (highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) *
              lowIndicator (w t.r) * lowIndicator (w u.r))) := by
      simp only [hamming, productExpectation, ← Finset.sum_sub_distrib, ← mul_sub]
      apply Finset.sum_congr rfl
      intro w _
      rw [point]
    have first := product_expectation_linear_combination (μ := μ) (fun w => highIndicator (w t.q)
        * lowIndicator (w t.r))
      (fun w => highIndicator (w t.q) * lowIndicator (w u.r))
      (fun w => highIndicator (w t.q) * lowIndicator (w t.r) * lowIndicator (w u.r)) 1 1 (-2)
    have second := product_expectation_linear_combination (μ := μ)
      (fun w => highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) *
          lowIndicator (w t.r))
      (fun w => highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) *
          lowIndicator (w u.r))
      (fun w => highIndicator (w t.p) * (lowIndicator (w t.q) * highIndicator (w t.q)) *
          lowIndicator (w t.r) * lowIndicator (w u.r))
      1 1 (-2)
    simp only [one_mul, neg_mul, sub_eq_add_neg] at first second split ⊢
    rw [split, first, second,
      product_expectation_two_positions hsum _ _ (ne_of_lt t.qr) highIndicator lowIndicator,
          product_expectation_two_positions hsum _ _ hqs highIndicator lowIndicator,
      product_expectation_three_positions hsum _ _ _ (ne_of_lt t.qr) hqs hrs highIndicator
          lowIndicator lowIndicator,
      product_expectation_three_positions hsum _ _ _ (ne_of_lt t.pq) hpr (ne_of_lt t.qr)
          highIndicator (fun a => lowIndicator a * highIndicator a) lowIndicator,
      product_expectation_three_positions hsum _ _ _ (ne_of_lt t.pq) hps hqs highIndicator (fun a
          => lowIndicator a * highIndicator a) lowIndicator,
      product_expectation_four_positions hsum _ _ _ _ (ne_of_lt t.pq) hpr hps (ne_of_lt t.qr) hqs
          hrs
        highIndicator (fun a => lowIndicator a * highIndicator a) lowIndicator lowIndicator]
    simp only [high_indicator_mean, low_indicator_mean, joint_endpoint_mean]
    ring
  have gap : eta rho < gamma rho := by
    have hpos : 0 < 4 * rho ^ 2 * (1 - 2 * rho) :=
      mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hr)) (by linarith)
    have h := mul_pos hpos (show 0 < 1 - 3 * rho by linarith)
    dsimp [eta, gamma]
    nlinarith
  have lower (μ : Laws n) (hμ : Admissible rho μ) (t u : Roles n) (htu : t ≠ u) :
      eta rho ≤ hamming μ t u := by
    have first_gate_sq_le_class_sq (w : Input n) :
        (firstGate t w - firstGate u w) ^ 2 ≤
          (if classValue t w = classValue u w then (0 : ℝ) else 1) := by
      rw [class_value_formula, class_value_formula]
      rcases first_gate_binary (w t.p) (w t.q) with ht | ht <;>
        rcases first_gate_binary (w u.p) (w u.q) with hu | hu <;>
        rcases first_gate_binary (w t.q) (w t.r) with hb | hb <;>
        rcases first_gate_binary (w u.q) (w u.r) with hc | hc <;>
        norm_num [firstGate, ht, hu, hb, hc]
    have gate_le : productExpectation μ (fun w => (firstGate t w - firstGate u w) ^ 2) ≤ hamming μ
        t u := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (first_gate_sq_le_class_sq w)
        (Finset.prod_nonneg (fun i _ => hr.le.trans (hμ.1 i (w i))))
    by_cases hp : t.p = u.p
    · by_cases hq : t.q = u.q
      · have hrs : t.r ≠ u.r := by
          intro he
          apply htu
          cases t
          cases u
          simp_all
        rw [same_head μ hμ.2 t u hp hq hrs]
        have hH := (endpoint_marginal_bounds rho μ hμ t.p).1.2
        have ht := hμ.1 t.q .ends
        have hz := hμ.1 t.q .high
        have joint_lower : rho * (1 + 3 * rho) ≤ highMarginal μ t.q - highMarginal μ t.p * μ t.q
            .ends := by
          have h1 := mul_le_mul_of_nonneg_left hH (hr.le.trans ht)
          have h2 := mul_le_mul_of_nonneg_left ht (show 0 ≤ 3 * rho by linarith)
          dsimp [highMarginal] at h1 ⊢
          nlinarith
        have hpsi := bernoulli_discrepancy_lower rho hr hr8 (lowMarginal μ t.r) (lowMarginal μ u.r)
          (endpoint_marginal_bounds rho μ hμ t.r).2 (endpoint_marginal_bounds rho μ hμ u.r).2
        have hpsi0 : 0 ≤ 4 * rho * (1 - 2 * rho) :=
          mul_nonneg (by linarith) (by linarith)
        have hj0 : 0 ≤ highMarginal μ t.q - highMarginal μ t.p * μ t.q .ends :=
          (mul_nonneg hr.le (by linarith)).trans joint_lower
        have hh := mul_le_mul joint_lower hpsi hpsi0 hj0
        dsimp [eta]
        nlinarith
      · exact gap.le.trans ((first_gate_discrepancy_lower rho hr hr8 μ hμ t u (Or.inr hq)).trans
          gate_le)
    · exact gap.le.trans ((first_gate_discrepancy_lower rho hr hr8 μ hμ t u (Or.inl hp)).trans
        gate_le)
  let t : Roles n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
    by change (0 : ℕ) < 1; omega, by change (1 : ℕ) < 2; omega⟩
  let u : Roles n := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩,
    by change (0 : ℕ) < 1; omega, by change (1 : ℕ) < 3; omega⟩
  have distinct : t ≠ u := by
    intro h
    have := congrArg (fun v : Roles n => v.r.val) h
    norm_num [t, u] at this
  have admissible : Admissible rho (attainingLaw n rho) := by
    constructor
    · intro i a
      by_cases hzero : i.val = 0
      · cases a <;> simp [attainingLaw, hzero, tilted] <;> linarith
      · cases a <;> simp [attainingLaw, hzero, extremal] <;> linarith
    · intro i
      by_cases hzero : i.val = 0 <;> simp [attainingLaw, hzero, tilted, extremal, Finset.univ,
          Fintype.elems] <;> ring
  have attained (μ : Laws n) (hμ : Admissible rho μ)
      (hfirst : ∀ i : Fin n, i.val < 4 → μ i = attainingLaw n rho i) :
      hamming μ t u = eta rho := by
    rw [same_head μ hμ.2 t u rfl rfl
      (by intro h; have := congrArg Fin.val h; norm_num [t, u] at this)]
    have hp := hfirst t.p (by norm_num [t])
    have hq := hfirst t.q (by norm_num [t])
    have hr' := hfirst t.r (by norm_num [t])
    have hs := hfirst u.r (by norm_num [u])
    simp only [highMarginal, lowMarginal, hp, hq, hr', hs]
    norm_num [attainingLaw, t, u, tilted, extremal, eta]
    ring
  exact ⟨lower, ⟨distinct, admissible, attained _ admissible (fun _ _ => rfl), attained⟩, gap⟩

end D5.S3.Arith.FibonacciAtomic.HeterogeneousHammingSeparation
