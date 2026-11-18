/- GID: D5/S3/Arith/CharacterSums/PascadiSingularValueEnvelope
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSingularValueEnvelope
   mirror-E: none(waiver:expanded-singular-value-envelope)
   anchors: []
   utility: none
   digest: Actual algebraic value pairs remain subpower in the expanded coordinate envelope. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalSingularPartners

/-! The prime used for modular relevance does not need to equal the real
parameter bounding number-field conjugates. Choosing the latter to be p squared
retains the existing uniform number-field divisor theorem in the larger range. -/

open Polynomial

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem squared_envelope_coefficients (p : ℝ) (hp : 18 ≤ p)
    (q : Coordinate) (base e : Endpoint)
    (hq : CoordinateBound p p q)
    (hb₁ : CoordinateBound p p base.1) (hb₂ : CoordinateBound p p base.2)
    (he₁ : CoordinateBound p p e.1) (he₂ : CoordinateBound p p e.2) :
    ∀ j, |((pencil q base e).coeff j : ℝ)| ≤ (p^2)^2 := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have h₁ := actual_pencil_coefficient_bounds p p q base e hq hb₁ hb₂ he₁ he₂
  have hbound : 18*p^3 ≤ (p^2)^2 := by
    have hh := mul_le_mul_of_nonneg_right hp (pow_nonneg hp0 3)
    nlinarith only [hh]
  intro j
  by_cases hj : j ≤ 3
  · interval_cases j
    · exact h₁.1.trans (by nlinarith only [hbound, pow_nonneg hp0 3])
    · exact h₁.2.1.trans (by nlinarith only [hbound])
    · exact h₁.2.2.1.trans (by nlinarith only [hbound])
    · exact h₁.2.2.2.trans (by nlinarith only [hbound, pow_nonneg hp0 3])
  · rw [coeff_eq_zero_of_natDegree_lt ((pencil_natDegree q base e).trans_lt (by omega))]
    simp only [Int.cast_zero, abs_zero]
    positivity

/-- Actual bounded-coordinate endpoint pairs with one relevant integer factor
have a field-uniform subpower value count. The envelope permits coordinates up
to p; the former condition 18 J1 cubed at most p squared is not required. -/
theorem actual_fixed_factor_value_pairs_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime], 18 ≤ (p : ℝ) →
      ∀ (q : Coordinate) (base : Endpoint) (S : Finset Endpoint) (e₀ : Endpoint),
      e₀ ∈ S → CoordinateBound p p q →
      CoordinateBound p p base.1 → CoordinateBound p p base.2 →
      (∀ e ∈ S, CoordinateBound p p e.1 ∧ CoordinateBound p p e.2) →
      pencil q base e₀ ≠ 0 →
      ∀ (F : ℤ[X]) [Fact (Irreducible (F.map (Int.castRingHom ℚ)))],
      F.IsPrimitive → F ∣ pencil q base e₀ → ∀ b : ℤ,
      ((F.eval b : ℤ) : ZMod p) = 0 →
      IsUnit (((endpointQ base).eval b : ℤ) : ZMod p) →
      IsUnit (((endpointQ base-endpointL q base*coordinateLinear q).eval b : ℤ) : ZMod p) →
      ((singularFactorValuePairs F q base S).card : ℝ) ≤ C*(p : ℝ)^ε := by
  obtain ⟨C, hC, hcount⟩ := fixed_factor_value_pairs_envelope (ε/2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro p _ hp q base S e₀ he₀ hq hb₁ hb₂ hS hP F _ hprim hF b hFb hQu hQZu
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hp1 : 1 ≤ (p : ℝ) := by linarith
  have hp2 : (p : ℝ) ≤ (p : ℝ)^2 := by nlinarith only [hp1]
  have hp16 : 16 ≤ (p : ℝ)^2 := by nlinarith only [hp]
  have hcoeff := integer_cubic_factor_coeff_bound ((p : ℝ)^2) (by linarith only [hp16])
    (pencil q base e₀) F hP (pencil_natDegree q base e₀) hF
    (squared_envelope_coefficients (p : ℝ) hp q base e₀ hq hb₁ hb₂
      (hS e₀ he₀).1 (hS e₀ he₀).2)
  have hdegree : F.natDegree ≤ 3 :=
    (natDegree_le_of_dvd hF hP).trans (pencil_natDegree q base e₀)
  have hc := actual_coefficient_bounds (p : ℝ) p q base hq hb₁ hb₂
  have h3 : 3*(p : ℝ) ≤ ((p : ℝ)^2)^2 := by
    have hh : (p : ℝ) ≤ (p : ℝ)^3 :=
      by simpa only [pow_one] using pow_le_pow_right₀ hp1 (by decide : 1 ≤ 3)
    have hpp : 3 ≤ (p : ℝ)^3 := by linarith only [hp, hh]
    have hh' := mul_le_mul_of_nonneg_right hpp hp0
    nlinarith only [hh']
  have hpp2 : 2 ≤ (p : ℝ)^2 := by nlinarith only [hp]
  have h2raw := mul_le_mul_of_nonneg_right hpp2 (sq_nonneg (p : ℝ))
  have h2 : 2*(p : ℝ)^2 ≤ ((p : ℝ)^2)^2 := by
    nlinarith only [h2raw]
  have hsquare : (p : ℝ)^2 ≤ ((p : ℝ)^2)^2 := by
    nlinarith only [h2, sq_nonneg (p : ℝ)]
  have hvalue := hcount p ((p : ℝ)^2) hp16 F hprim hdegree hcoeff b hFb
    q base S e₀ he₀ hF hQu hQZu
    (hc.1.trans h3) (hc.2.1.trans h3) (hc.2.2.1.trans hsquare)
    (hc.2.2.2.1.trans (by nlinarith only [h2])) (hc.2.2.2.2.trans hsquare) (by
      intro e he z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨((hS e he).1).1.trans hp2, ((hS e he).1).2.trans hp2⟩
      · exact ⟨((hS e he).2).1.trans hp2, ((hS e he).2).2.trans hp2⟩)
  have hpow : ((p : ℝ)^2)^(ε/2) = (p : ℝ)^ε := by
    rw [← Real.rpow_natCast_mul hp0 2 (ε/2)]
    congr 1
    ring
  simpa only [hpow] using hvalue

end

end D5.S3.Arith.CharacterSums.Original
