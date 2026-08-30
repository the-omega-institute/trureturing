/- GID: D5/S1/Recurrence/BilateralLiftClassification
   generality: I
   mirror-B: D5/B/S1/Recurrence/BilateralLiftClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Classify the two-line golden Fibonacci lift and its component scales. -/

import D5.S1.Recurrence.BilateralLiftUniqueness

/- Library-search audit trail (2026-08-30):
   * Current-tree name and body-shape searches found the frozen recurrence owner for the span,
     shift, Binet, minimal-carrier, and residual clauses, but no public theorem exposing both
     finrank two and unique componentwise scaling.
   * Pinned Mathlib supplies the golden scalar identities, Fibonacci recurrence basis,
     `Module.finrank_eq_card_basis`, and Binet formula. No exact bilateral classification was found.
   * The other pinned Lean packages contain no Fibonacci solution-space or golden-eigenline hit.
     `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence

/-- The complete bilateral Fibonacci lift has two golden eigendirections. Both Binet
coefficients are nonzero, its canonical carrier is the least shift-invariant carrier of the
Fibonacci weights and has dimension two, and every pair of sequences on the two eigenlines is
obtained by a unique pair of component scalars. The canonical weight pair and its exact
contracting residual are included as public clauses. -/
theorem bilateral_lift_classification :
    Module.finrank Real (Real.fibRec : LinearRecurrence Real).solSpace = 2 /\
      (Real.fibRec : LinearRecurrence Real).solSpace =
        Submodule.span Real {expandingSequence, contractingSequence} /\
      Real.goldenRatio = (1 + Real.sqrt 5) / 2 /\
      Real.goldenConj = -Real.goldenRatio⁻¹ /\
      (shift expandingSequence = Real.goldenRatio • expandingSequence /\
        shift contractingSequence = Real.goldenConj • contractingSequence) /\
      ((Real.sqrt 5)⁻¹ ≠ 0 /\ -(Real.sqrt 5)⁻¹ ≠ 0) /\
      (forall k : Nat, fibonacciWeight k =
        (expandingSequence k - contractingSequence k) / Real.sqrt 5) /\
      (fibonacciWeight ∈ Submodule.span Real {expandingSequence, contractingSequence} /\
        (forall u, u ∈ Submodule.span Real {expandingSequence, contractingSequence} ->
          shift u ∈ Submodule.span Real {expandingSequence, contractingSequence}) /\
        forall W : Submodule Real Seq, fibonacciWeight ∈ W ->
          (forall u, u ∈ W -> shift u ∈ W) ->
          Submodule.span Real {expandingSequence, contractingSequence} <= W) /\
      Module.finrank Real
        (Submodule.span Real {expandingSequence, contractingSequence}) = 2 /\
      (forall u v : Seq,
        shift u = Real.goldenRatio • u ->
        shift v = Real.goldenConj • v ->
        ExistsUnique fun scales : Real × Real =>
          u = scales.1 • expandingSequence /\
            v = scales.2 • contractingSequence) /\
      (forall k : Nat, (expandingSequence k, contractingSequence k) =
        (Real.goldenRatio ^ (k + 1), Real.goldenConj ^ (k + 1))) /\
      forall k : Nat,
        fibonacciWeight (k + 1) - Real.goldenRatio * fibonacciWeight k =
          Real.goldenConj ^ (k + 1) := by
  letI : FiniteDimensional Real
      (Real.fibRec : LinearRecurrence Real).solSpace :=
    (Real.fibRec : LinearRecurrence Real).basis.finiteDimensional_of_finite
  have solutionDimension :
      Module.finrank Real (Real.fibRec : LinearRecurrence Real).solSpace = 2 := by
    rw [Module.finrank_eq_card_basis (Real.fibRec : LinearRecurrence Real).basis]
    simp only [Fintype.card_fin]
    rfl
  have carrierDimension :
      Module.finrank Real
        (Submodule.span Real {expandingSequence, contractingSequence}) = 2 := by
    rw [<- fibonacci_solution_space_eq_span]
    exact solutionDimension
  have conjugateIdentity : Real.goldenConj = -Real.goldenRatio⁻¹ := by
    linarith [Real.inv_goldenRatio]
  have nonzeroCoefficients :
      (Real.sqrt 5)⁻¹ ≠ 0 /\ -(Real.sqrt 5)⁻¹ ≠ 0 := by
    have squareRootNonzero : Real.sqrt 5 ≠ 0 := by positivity
    simp [squareRootNonzero]
  have expandingClassification : forall u : Seq,
      shift u = Real.goldenRatio • u ->
      ExistsUnique fun scale : Real => u = scale • expandingSequence := by
    intro u eigenlaw
    refine ⟨u 0 * Real.goldenRatio⁻¹, ?_, ?_⟩
    · funext k
      simp only [Pi.smul_apply, smul_eq_mul]
      induction k with
      | zero =>
          rw [show expandingSequence 0 = Real.goldenRatio by simp [expandingSequence]]
          calc
            u 0 = u 0 * 1 := by simp
            _ = u 0 * (Real.goldenRatio⁻¹ * Real.goldenRatio) := by
              rw [inv_mul_cancel₀ Real.goldenRatio_ne_zero]
            _ = (u 0 * Real.goldenRatio⁻¹) * Real.goldenRatio := by ring
      | succ k ih =>
          have step : u (k + 1) = Real.goldenRatio * u k := by
            simpa [shift] using congr_fun eigenlaw k
          rw [step, ih]
          simp [expandingSequence, pow_succ]
          ring
    · intro scale representation
      have initial : u 0 = scale * Real.goldenRatio := by
        simpa [expandingSequence] using congr_fun representation 0
      calc
        scale = scale * 1 := by simp
        _ = scale * (Real.goldenRatio * Real.goldenRatio⁻¹) := by
          rw [mul_inv_cancel₀ Real.goldenRatio_ne_zero]
        _ = u 0 * Real.goldenRatio⁻¹ := by rw [initial]; ring
  have contractingClassification : forall v : Seq,
      shift v = Real.goldenConj • v ->
      ExistsUnique fun scale : Real => v = scale • contractingSequence := by
    intro v eigenlaw
    refine ⟨v 0 * Real.goldenConj⁻¹, ?_, ?_⟩
    · funext k
      simp only [Pi.smul_apply, smul_eq_mul]
      induction k with
      | zero =>
          rw [show contractingSequence 0 = Real.goldenConj by simp [contractingSequence]]
          calc
            v 0 = v 0 * 1 := by simp
            _ = v 0 * (Real.goldenConj⁻¹ * Real.goldenConj) := by
              rw [inv_mul_cancel₀ Real.goldenConj_ne_zero]
            _ = (v 0 * Real.goldenConj⁻¹) * Real.goldenConj := by ring
      | succ k ih =>
          have step : v (k + 1) = Real.goldenConj * v k := by
            simpa [shift] using congr_fun eigenlaw k
          rw [step, ih]
          simp [contractingSequence, pow_succ]
          ring
    · intro scale representation
      have initial : v 0 = scale * Real.goldenConj := by
        simpa [contractingSequence] using congr_fun representation 0
      calc
        scale = scale * 1 := by simp
        _ = scale * (Real.goldenConj * Real.goldenConj⁻¹) := by
          rw [mul_inv_cancel₀ Real.goldenConj_ne_zero]
        _ = v 0 * Real.goldenConj⁻¹ := by rw [initial]; ring
  have componentwiseUniqueness : forall u v : Seq,
      shift u = Real.goldenRatio • u ->
      shift v = Real.goldenConj • v ->
      ExistsUnique fun scales : Real × Real =>
        u = scales.1 • expandingSequence /\
          v = scales.2 • contractingSequence := by
    intro u v expandingEigenlaw contractingEigenlaw
    obtain ⟨a, ha, haUnique⟩ := expandingClassification u expandingEigenlaw
    obtain ⟨b, hb, hbUnique⟩ := contractingClassification v contractingEigenlaw
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    rintro ⟨a', b'⟩ ⟨ha', hb'⟩
    exact Prod.ext (haUnique a' ha') (hbUnique b' hb')
  have weightPair : forall k : Nat,
      (expandingSequence k, contractingSequence k) =
        (Real.goldenRatio ^ (k + 1), Real.goldenConj ^ (k + 1)) := by
    intro k
    rfl
  exact ⟨solutionDimension, fibonacci_solution_space_eq_span, rfl,
    conjugateIdentity, shift_golden_eigenvectors, nonzeroCoefficients,
    fibonacci_weight_binet, fibonacci_cyclic_span_minimal, carrierDimension,
    componentwiseUniqueness, weightPair, fibonacci_weight_residual⟩

#print axioms bilateral_lift_classification

end D5.S1.Recurrence
