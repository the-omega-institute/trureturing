/- GID: D5/S3/Fourier/CharacterSelection/OptimalCompetitionSelector
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/OptimalCompetitionSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The normalized orthogonal target projection eliminates every competing profile. -/

import D5.S3.Observer.CanonicalStrongestSeparatingObserver
import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-- The real Euclidean pairing forced by the source's real competitor span. -/
def profileDot {d : Nat} (left right : CharacterProfileSpace d) : Real :=
  inner Real left right

/-- The real span of the finitely many competing character profiles. -/
def competitorProfileSpace
    {Z : Type*} {d m : Nat}
    (profile : Z -> CharacterProfileSpace d) (competitors : Fin m -> Z) :
    Submodule Real (CharacterProfileSpace d) :=
  Submodule.span Real (Set.range fun j => profile (competitors j))

/-- The distance from the target profile to the competitor profile space. -/
def selectorMargin
    {Z : Type*} {d m : Nat}
    (profile : Z -> CharacterProfileSpace d) (target : Z) (competitors : Fin m -> Z) : Real :=
  Metric.infDist (profile target) (competitorProfileSpace profile competitors :
    Set (CharacterProfileSpace d))

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
formula. -/
theorem optimal_competition_selector
    {d m : Nat}
    (profile : Complex -> CharacterProfileSpace d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin profile target competitors) :
    let W := competitorProfileSpace profile competitors
    let delta := selectorMargin profile target competitors
    ∃ cStar : CharacterProfileSpace d,
      ‖cStar‖ = 1 ∧
      cStar ∈ Wᗮ ∧
      (∀ j : Fin m, profileDot cStar (profile (competitors j)) = 0) ∧
      abs (profileDot cStar (profile target)) = delta ∧
      cStar =
        ‖Wᗮ.starProjection (profile target)‖⁻¹ •
          Wᗮ.starProjection (profile target) := by
  classical
  dsimp only
  let W := competitorProfileSpace profile competitors
  let x := profile target
  have marginEq : selectorMargin profile target competitors = ‖Wᗮ.starProjection x‖ := by
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
  have cStarReadout : abs (profileDot cStar x) = selectorMargin profile target competitors := by
    have readout := normalized_residual_exact_readout closedW x residualNeZero
    rw [residualEq, ← marginEq] at readout
    exact readout
  refine ⟨cStar, cStarNorm, cStarMem, ?_, cStarReadout, ?_⟩
  · intro j
    change inner Real cStar (profile (competitors j)) = 0
    apply Submodule.inner_left_of_mem_orthogonal (K := W)
    · exact Submodule.subset_span (Set.mem_range_self j)
    · exact cStarMem
  · simpa only [x] using cStarFormula

-- Reverse probe: the public proposition exposes a nonzero selector with nonzero target response.
example
    {d m : Nat}
    (profile : Complex -> CharacterProfileSpace d) (target : Complex)
    (competitors : Fin m -> Complex)
    (positiveMargin : 0 < selectorMargin profile target competitors) :
    ∃ cStar : CharacterProfileSpace d,
      cStar ≠ 0 ∧ profileDot cStar (profile target) ≠ 0 := by
  rcases optimal_competition_selector profile target competitors positiveMargin with
    ⟨cStar, cStarNorm, _, _, cStarReadout, _⟩
  refine ⟨cStar, ?_, ?_⟩
  · exact fun cStarZero => by simp [cStarZero] at cStarNorm
  · intro responseZero
    rw [responseZero, abs_zero] at cStarReadout
    linarith

-- Trivialization probe: an identically zero profile family cannot satisfy the positive margin.
example
    {d m : Nat} (target : Complex) (competitors : Fin m -> Complex) :
    ¬0 < selectorMargin (fun _ : Complex => (0 : CharacterProfileSpace d)) target competitors := by
  have zeroMem :
      (0 : CharacterProfileSpace d) ∈
        competitorProfileSpace (fun _ : Complex => 0) competitors := Submodule.zero_mem _
  rw [show selectorMargin (fun _ : Complex => 0) target competitors = 0 by
    exact Metric.infDist_zero_of_mem zeroMem]
  exact lt_irrefl 0

#print axioms optimal_competition_selector

end

end D5.S3.Fourier.CharacterSelection.OptimalCompetitionSelector
