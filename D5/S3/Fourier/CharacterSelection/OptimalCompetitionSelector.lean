/- GID: D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/OptimalCompetitionSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized orthogonal target projection eliminates every competing profile. -/

import D5.S3.Observer.CanonicalStrongestSeparatingObserver
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-09-02):
   * Repository searches found `canonical_strongest_separating_observer`, whose normalized
     residual and exact readout are applied below, and the related character-code duality theorem.
   * Pinned Mathlib supplies `Submodule.starProjection_minimal`, complementary projection,
     projection membership, and finite-dimensional closedness; those declarations are reused.
   * Loogle suggested the namespaced projection API. LeanSearch returned HTTP 404 and
     unauthenticated GitHub code search returned HTTP 401. No external dependency or duplicate
     theorem was added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.OptimalCompetitionSelector

open D5.S3.Observer.CanonicalStrongestSeparatingObserver

noncomputable section

/-- The source theorem's finite complex coefficient space `C^d`. -/
abbrev CharacterProfileSpace (d : Nat) := EuclideanSpace Complex (Fin d)

/-- A finite family of real-rational features with all five source-side analytic conditions. -/
structure FiniteRealRationalFeatureFamily (d : Nat) where
  features : Fin d -> RatFunc Real
  conjugation_equivariant : forall z j,
    RatFunc.eval (algebraMap Real Complex) (star z) (features j) =
      star (RatFunc.eval (algebraMap Real Complex) z (features j))
  even : forall z j,
    RatFunc.eval (algebraMap Real Complex) (-z) (features j) =
      RatFunc.eval (algebraMap Real Complex) z (features j)
  real_on_real_axis : forall x j,
    (RatFunc.eval (algebraMap Real Complex) (x : Complex) (features j)).im = 0
  poles_outside_critical_strip : forall j z,
    (RatFunc.denom (features j)).eval₂ (algebraMap Real Complex) z = 0 ->
      z.re < 0 ∨ 1 < z.re
  sufficient_real_decay : forall j ε, 0 < ε ->
    ∃ R : Real, 0 < R ∧ forall x : Real, R <= |x| ->
      ‖RatFunc.eval (algebraMap Real Complex) (x : Complex) (features j)‖ < ε

/-- Evaluation of the finite real-rational feature family in `C^d`. -/
noncomputable def featureProfile {d : Nat} (family : FiniteRealRationalFeatureFamily d)
    (z : Complex) : CharacterProfileSpace d :=
  WithLp.toLp 2 fun j => RatFunc.eval (algebraMap Real Complex) z (family.features j)

/-- The real Euclidean pairing forced by the source's real competitor span. -/
def profileDot {d : Nat} (left right : CharacterProfileSpace d) : Real :=
  inner Real left right

/-- The real span of the finitely many competing character profiles. -/
def competitorProfileSpace
    {d m : Nat} (family : FiniteRealRationalFeatureFamily d)
    (competitors : Fin m -> Complex) :
    Submodule Real (CharacterProfileSpace d) :=
  Submodule.span Real (Set.range fun j => featureProfile family (competitors j))

/-- The distance from the target profile to the competitor profile space. -/
def selectorMargin
    {d m : Nat} (family : FiniteRealRationalFeatureFamily d)
    (target : Complex) (competitors : Fin m -> Complex) : Real :=
  Metric.infDist (featureProfile family target) (competitorProfileSpace family competitors :
    Set (CharacterProfileSpace d))

/-- The target margin is the norm of the target's complementary orthogonal projection. -/
def IsOrthogonalProjectionProblem
    {d m : Nat} (family : FiniteRealRationalFeatureFamily d)
    (target : Complex) (competitors : Fin m -> Complex) : Prop :=
  selectorMargin family target competitors =
    ‖(competitorProfileSpace family competitors)ᗮ.starProjection
      (featureProfile family target)‖

private theorem infDist_eq_norm_complementary_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
    (space : Submodule Real H) [space.HasOrthogonalProjection] (x : H) :
    Metric.infDist x (space : Set H) = ‖spaceᗮ.starProjection x‖ := by
  rw [Metric.infDist_eq_iInf]
  simp_rw [dist_eq_norm]
  calc
    (⨅ y : space, ‖x - y‖) = ‖x - space.starProjection x‖ :=
      (space.starProjection_minimal x).symm
    _ = ‖spaceᗮ.starProjection x‖ := by
      rw [space.starProjection_orthogonal_val]

private theorem normalized_residual_exact_readout
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (space : ClosedSubmodule Real H) (x : H) (residualNeZero : residual space x ≠ 0) :
    abs (inner Real (normalizedResidual space x) x) = ‖residual space x‖ := by
  have canonical := canonical_strongest_separating_observer space x residualNeZero
  have greatestMembership := canonical.2.1.1
  change ∃ g : H, g ∈ spaceᗮ ∧ ‖g‖ ≤ 1 ∧
    ‖residual space x‖ = abs (inner Real g x) at greatestMembership
  rcases greatestMembership with ⟨g, gMem, gNorm, gValue⟩
  have gMax : abs (inner Real g x) = ‖residual space x‖ := gValue.symm
  rcases (canonical.2.2.1 g gMem gNorm).mp gMax with gEq | gEq
  · simpa [gEq] using gMax
  · rw [gEq, inner_neg_left, abs_neg] at gMax
    exact gMax

/-- OACTC 925.1: the normalized projection of the target profile onto the orthogonal complement
of the real competitor span is a unit selector. It annihilates every competing profile, has
absolute target response equal to the metric margin, and is exactly the displayed projection
formula. The public conclusion also records that the margin is an orthogonal-projection problem. -/
theorem optimal_competition_selector
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    let W := competitorProfileSpace family competitors
    let delta := selectorMargin family target competitors
    ∃ cStar : CharacterProfileSpace d,
      ‖cStar‖ = 1 ∧
      cStar ∈ Wᗮ ∧
      (∀ j : Fin m, profileDot cStar (featureProfile family (competitors j)) = 0) ∧
      abs (profileDot cStar (featureProfile family target)) = delta ∧
      cStar =
        ‖Wᗮ.starProjection (featureProfile family target)‖⁻¹ •
          Wᗮ.starProjection (featureProfile family target) ∧
      IsOrthogonalProjectionProblem family target competitors := by
  classical
  dsimp only
  let W := competitorProfileSpace family competitors
  let x := featureProfile family target
  have marginEq : selectorMargin family target competitors = ‖Wᗮ.starProjection x‖ := by
    exact infDist_eq_norm_complementary_projection W x
  have projectionNormPos : 0 < ‖Wᗮ.starProjection x‖ := by
    rw [← marginEq]
    exact positiveMargin
  have projectionNeZero : Wᗮ.starProjection x ≠ 0 := norm_pos_iff.mp projectionNormPos
  let closedW : ClosedSubmodule Real (CharacterProfileSpace d) :=
    ⟨W, W.closed_of_finiteDimensional⟩
  have residualEq : residual closedW x = Wᗮ.starProjection x := by
    change x - W.starProjection x = Wᗮ.starProjection x
    exact (W.starProjection_orthogonal_val x).symm
  have residualNeZero : residual closedW x ≠ 0 := by
    rw [residualEq]
    exact projectionNeZero
  let cStar := normalizedResidual closedW x
  have cStarFormula :
      cStar = ‖Wᗮ.starProjection x‖⁻¹ • Wᗮ.starProjection x := by
    simp only [cStar, normalizedResidual, residualEq]
  have cStarNorm : ‖cStar‖ = 1 := by
    rw [cStarFormula, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr projectionNormPos)]
    exact inv_mul_cancel₀ projectionNormPos.ne'
  have cStarMem : cStar ∈ Wᗮ := by
    rw [cStarFormula]
    exact Wᗮ.smul_mem _ (Submodule.starProjection_apply_mem Wᗮ x)
  have cStarReadout : abs (profileDot cStar x) = selectorMargin family target competitors := by
    have readout := normalized_residual_exact_readout closedW x residualNeZero
    rw [residualEq, ← marginEq] at readout
    exact readout
  have cStarAnnihilates :
      ∀ j : Fin m, profileDot cStar (featureProfile family (competitors j)) = 0 := by
    intro j
    change inner Real cStar (featureProfile family (competitors j)) = 0
    apply Submodule.inner_left_of_mem_orthogonal (K := W)
    · exact Submodule.subset_span (Set.mem_range_self j)
    · exact cStarMem
  refine ⟨cStar, cStarNorm, cStarMem, cStarAnnihilates, cStarReadout, ?_, ?_⟩
  · simpa only [x] using cStarFormula
  · exact marginEq

private theorem selector_unit_norm_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    ∃ cStar : CharacterProfileSpace d, ‖cStar‖ = 1 := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨cStar, cStarNorm, _⟩
  exact ⟨cStar, cStarNorm⟩

private theorem selector_orthogonal_membership_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    ∃ cStar : CharacterProfileSpace d,
      cStar ∈ (competitorProfileSpace family competitors)ᗮ := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨cStar, _, cStarMem, _⟩
  exact ⟨cStar, cStarMem⟩

private theorem selector_competitor_annihilation_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    ∃ cStar : CharacterProfileSpace d,
      ∀ j : Fin m, profileDot cStar (featureProfile family (competitors j)) = 0 := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨cStar, _, _, cStarAnnihilates, _⟩
  exact ⟨cStar, cStarAnnihilates⟩

private theorem selector_target_response_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    ∃ cStar : CharacterProfileSpace d,
      abs (profileDot cStar (featureProfile family target)) =
        selectorMargin family target competitors := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨cStar, _, _, _, cStarReadout, _⟩
  exact ⟨cStar, cStarReadout⟩

private theorem selector_formula_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    ∃ cStar : CharacterProfileSpace d,
      cStar =
        ‖(competitorProfileSpace family competitors)ᗮ.starProjection
          (featureProfile family target)‖⁻¹ •
        (competitorProfileSpace family competitors)ᗮ.starProjection
          (featureProfile family target) := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨cStar, _, _, _, _, cStarFormula, _⟩
  exact ⟨cStar, cStarFormula⟩

private theorem selector_projection_problem_check
    {d m : Nat}
    (family : FiniteRealRationalFeatureFamily d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin family target competitors) :
    IsOrthogonalProjectionProblem family target competitors := by
  have result := optimal_competition_selector family target competitors positiveMargin
  dsimp only at result
  rcases result with ⟨_, _, _, _, _, _, projectionProblem⟩
  exact projectionProblem

private noncomputable def zeroFeatureFamily (d : Nat) : FiniteRealRationalFeatureFamily d where
  features := fun _ => 0
  conjugation_equivariant := by simp
  even := by simp
  real_on_real_axis := by simp [RatFunc.eval]
  poles_outside_critical_strip := by simp
  sufficient_real_decay := by
    intro j ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    simpa [RatFunc.eval] using hε

-- Trivialization probe: an identically zero valid family cannot satisfy the positive margin.
example
    {d m : Nat} (target : Complex) (competitors : Fin m -> Complex) :
    ¬0 < selectorMargin (zeroFeatureFamily d) target competitors := by
  have profileZero : featureProfile (zeroFeatureFamily d) target = 0 := by
    ext j
    simp [featureProfile, zeroFeatureFamily, RatFunc.eval]
  rw [show selectorMargin (zeroFeatureFamily d) target competitors = 0 by
    unfold selectorMargin
    rw [profileZero]
    exact Metric.infDist_zero_of_mem (Submodule.zero_mem _)]
  exact lt_irrefl 0

#print axioms optimal_competition_selector

end

end D5.S3.Fourier.CharacterSelection.OptimalCompetitionSelector
