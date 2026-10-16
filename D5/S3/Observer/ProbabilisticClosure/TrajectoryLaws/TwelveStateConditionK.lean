/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateConditionK
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationary arrival observations preserve the original output clock and exclude Condition K. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open MarkedPredictiveQuotient OriginalMarkedLaw OriginalLawTrimming PositiveRectangleMessages

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateConditionK
variable {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- The deterministic-state observation selector, with its structural zeros. -/
def observation (f : H → Bool) (x : Bool) : Matrix H H ℝ :=
  Matrix.diagonal (fun i => if f i = x then 1 else 0)

private theorem arrival_intertwine (K : Matrix H H ℝ) (f : H → Bool)
    (n : ℕ) (w : Fin n → Bool) :
    wordMatrix (fun x => K*observation f x) n w * K =
      K*wordMatrix (fun x => observation f x*K) n w := by
  induction n with
  | zero => simp [wordMatrix]
  | succ n ih =>
    simp only [wordMatrix,Matrix.mul_assoc]
    rw [ih]

/-- The exact stationary arrival-observation convention has the usual state-observation
cylinders on the same integer clock. Every irreducible presentation of the actual twelve-state
output law in this convention excludes every nonzero positive rectangular word product,
and hence excludes the finite Condition K hypothesis. -/
theorem actual_condition_k_boundary (θ : Presentation H) (K : Matrix H H ℝ) (f : H → Bool)
    (harr : ∀ x, θ.matrix x = K*observation f x)
    (hsame : visibleLaw θ = TwelveStatePresentation.visible)
    (hirr : ∀ i j : H, ∃ n : ℕ, 0 < (K^n) i j) :
    (∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
      (visibleLaw θ : Measure _).real (visibleCylinder t n w) =
        ∑ i, θ.initial i*futureMass (fun x => observation f x*K) i n w) ∧
    ∀ (n : ℕ) (w : Fin n → Bool),
      ¬ Nonempty (Rectangle (wordMatrix (fun x => K*observation f x) n w)) := by
  classical
  have hsum : θ.matrix false+θ.matrix true = K := by
    rw [harr false,harr true,← Matrix.mul_add]
    have hd : observation f false+observation f true = 1 := by
      ext i j
      simp only [observation,Matrix.diagonal_apply,Matrix.one_apply,Matrix.add_apply]
      by_cases h : i = j
      · subst j; cases hf : f i <;> simp [hf]
      · simp [h]
    rw [hd,Matrix.mul_one]
  have hrow : K *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    funext i
    change ∑ j, K i j*1 = 1
    simp only [mul_one]
    rw [← hsum]
    exact θ.stochastic i
  have hstat : θ.initial ᵥ* K = θ.initial := by
    rw [← hsum]
    exact funext θ.stationary
  have hm : θ.matrix = fun x => K*observation f x := funext harr
  constructor
  · intro t n w
    rw [(same_law_trimming θ).2.2.2.2.2.2.2.1 t n w,hm]
    have he := congrArg (fun A : Matrix H H ℝ => θ.initial ⬝ᵥ (A *ᵥ fun _ => (1:ℝ)))
      (arrival_intertwine K f n w)
    rw [← Matrix.mulVec_mulVec,hrow,← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec θ.initial K,hstat] at he
    simpa only [dotProduct,Matrix.mulVec,futureMass,mul_one] using he
  · intro n w
    rw [← hm]
    exact PositiveRectangleLaw.actual_irreducible_obstruction θ hsame
      (by simpa only [hsum] using hirr) n w

#print axioms actual_condition_k_boundary
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStateConditionK
