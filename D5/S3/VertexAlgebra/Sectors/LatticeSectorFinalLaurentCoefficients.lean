/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual left-nested canonical coefficients equal the original finite Laurent fiber. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorSameRLeftCovariance
import D5.S3.VertexAlgebra.FormalSeries.SupportedFinalRInjectivity
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentAction

/-! The actual canonical left-nested channel and the existing Laurent
coefficient expression have nested support and the same finite polynomial
action. Supported injectivity identifies them on every signed exponent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFinalLaurentCoefficients
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorChannelTransport
open LatticeSectorThreeFieldCommonSeries LatticeSectorFinalLaurentFiber
open LatticeSectorSameRLeftCovariance SupportedFinalRInjectivity ThreeFieldFinalCone
open UniformGradedLocalCorrelator UngradedLocalWordSeries
open SupportedThreeFieldCollision ThreeFieldFinalLaurentFiber
open ThreeFieldFinalLaurentAction
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators VertexOperator
noncomputable section

private theorem actual_nested_support (D : LatticeData) (α β γ δ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (w : Sector D δ) :
    NestedSupport (fun e => leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)) := by
  obtain ⟨U, hu⟩ := canonical_truncation D α β u v
  constructor
  · refine ⟨U.toNat, ?_⟩
    intro x y z hx
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    unfold leftNested
    rw [hu (-x - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
  · intro x
    obtain ⟨B, hb⟩ := canonical_truncation D (α + β) γ
      (canonical D α β u (-x - 1) v) t
    refine ⟨B.toNat, ?_⟩
    intro y z hy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    unfold leftNested
    rw [hb (-y - 1) (by omega)]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply]

private theorem old_expression_support {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) :
    NestedSupport (laurentCoefficient P k a) := by
  constructor
  · refine ⟨k, ?_⟩
    intro x y z hx
    apply old_zero_outside
    simp only [FinalCone, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    omega
  · intro x
    refine ⟨(x + 3 * k).toNat, ?_⟩
    intro y z hy
    apply old_zero_outside
    simp only [FinalCone, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    omega

/-- Unconditional actual K=the EXISTING laurentCoefficient, with all original
witnesses and all signed products. The new finite calculation discharges,
rather than assumes, the old expression's final R-action. -/
theorem actual_three_field_final_laurent_coefficients
    (D : LatticeData) (α β γ : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) :
    let c : Fin 3 → Charge D := ![α, β, γ]
    let states : Fin 3 → Oscillator D := ![u, v, t]
    ∃ k : ℕ,
      (∀ i j : Fin 3, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c states i)
          (labelledFields D c states j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 3 → ℕ,
        ∃ P : MvPowerSeries (Fin 3) (Oscillator D),
        (∀ (i : Fin 3) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ e : Exponent 3,
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 1 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 0 2 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 0 2)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 1 2 0)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 0 1)
            (fun i => e i - a i) = signedExtend P e ∧
          polynomialAction (clearingPolynomial 3 k) (nestedCanonical D c states δ w 2 1 0)
            (fun i => e i - a i) = signedExtend P e) ∧
        ∀ e : Exponent 3,
          leftNested D α β γ δ u v t w (e 0) (e 1) (e 2) =
            laurentCoefficient
              (MvPowerSeries.subst (triangularArguments (Oscillator D)) P) k a e := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_three_field_same_R_left_covariance D α β γ u v t
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, six, covariance⟩ := rest δ w
  let Pt := MvPowerSeries.subst (triangularArguments (Oscillator D)) P
  let K : Distribution 3 (Oscillator D) := fun e =>
    leftNested D α β γ δ u v t w (e 0) (e 1) (e 2)
  have equal : K = laurentCoefficient Pt k a := by
    apply finalR_injective k (a 0) (a 1) (a 2) K (laurentCoefficient Pt k a)
      (actual_nested_support D α β γ δ u v t w) (old_expression_support Pt k a)
    change polynomialAction (finalPolynomial k a) K =
      polynomialAction (finalPolynomial k a) (laurentCoefficient Pt k a)
    funext e
    exact (covariance e).trans (raw_R_action_transport Pt k a e).symm
  refine ⟨a, P, truncation, six, ?_⟩
  intro e
  exact congrFun equal e

#print actual_three_field_final_laurent_coefficients
#print axioms actual_three_field_final_laurent_coefficients
end
end D5.S3.VertexAlgebra.LatticeSectorFinalLaurentCoefficients
