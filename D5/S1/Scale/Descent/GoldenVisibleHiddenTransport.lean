/- GID: D5/S1/Scale/Descent/GoldenVisibleHiddenTransport
   generality: I
   mirror-B: D5/B/S1/Scale/Descent/GoldenVisibleHiddenTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden inflation expands the visible projection and contracts the hidden projection. -/

import Mathlib

/- Library-search audit trail (2026-08-28):
   * Current-tree searches for golden inflation, conjugate transport, visible
     and hidden projections, and the displayed geometric contraction found no
     exact D5 theorem on this real-module carrier.
   * `D5/S1/Phase/RenormalizationPayload` has only a two-coordinate surrogate,
     so it is not imported as the source construction.
   * Pinned Mathlib supplies the exact golden-ratio identities and geometric
     power convergence theorem used below; it has no theorem packaging the
     source's projection construction and all transport clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Scale.Descent.GoldenVisibleHiddenTransport

/-- An endomorphism whose square is five times the identity canonically splits
golden inflation into a visibly expanding eigendirection and a hidden,
sign-reversing contracting eigendirection. The contraction parameter is the
intrinsic conjugate magnitude, hence exactly `goldenRatio⁻¹ ^ n`. -/
theorem golden_visible_hidden_transport :
    ∀ (W : Type) [AddCommGroup W] [Module Real W]
      (J : W →ₗ[Real] W),
      J.comp J = (5 : Real) • (LinearMap.id : W →ₗ[Real] W) →
      let inflation : W →ₗ[Real] W :=
        (2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) + J)
      let visibleProjection : W →ₗ[Real] W :=
        (2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) +
          (Real.sqrt 5)⁻¹ • J)
      let hiddenProjection : W →ₗ[Real] W :=
        (2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) -
          (Real.sqrt 5)⁻¹ • J)
      let epsilon : Nat → Real := fun n => |Real.goldenConj| ^ n
      (∀ x, visibleProjection (inflation x) =
          Real.goldenRatio • visibleProjection x) ∧
        1 < Real.goldenRatio ∧
        (∀ x, hiddenProjection (inflation x) =
          Real.goldenConj • hiddenProjection x) ∧
        Real.goldenConj < 0 ∧
        |Real.goldenConj| = Real.goldenRatio⁻¹ ∧
        Real.goldenRatio⁻¹ < 1 ∧
        (∀ n, epsilon n = Real.goldenRatio⁻¹ ^ n) ∧
        Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
  intro W _ _ J hJ
  dsimp only
  have hsqrtNonzero : Real.sqrt 5 ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by norm_num)
  have hsqrtSquare : Real.sqrt 5 ^ 2 = (5 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hJpoint (x : W) : J (J x) = (5 : Real) • x := by
    have := DFunLike.congr_fun hJ x
    simpa using this
  have hVisible (x : W) :
      ((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) +
        (Real.sqrt 5)⁻¹ • J))
          (((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) + J)) x) =
        Real.goldenRatio •
          (((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) +
            (Real.sqrt 5)⁻¹ • J)) x) := by
    simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_smul, map_add]
    rw [hJpoint, Real.goldenRatio]
    match_scalars
    · field_simp [hsqrtNonzero]
      nlinarith [hsqrtSquare]
    · field_simp [hsqrtNonzero]
  have hHidden (x : W) :
      ((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) -
        (Real.sqrt 5)⁻¹ • J))
          (((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) + J)) x) =
        Real.goldenConj •
          (((2 : Real)⁻¹ • ((LinearMap.id : W →ₗ[Real] W) -
            (Real.sqrt 5)⁻¹ • J)) x) := by
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.id_apply, map_smul, map_add]
    rw [hJpoint, Real.goldenConj]
    match_scalars
    · field_simp [hsqrtNonzero]
      ring_nf
      nlinarith [hsqrtSquare]
    · field_simp [hsqrtNonzero]
      ring_nf
  have hAbs : |Real.goldenConj| = Real.goldenRatio⁻¹ := by
    rw [abs_of_neg Real.goldenConj_neg, Real.inv_goldenRatio]
  have hContraction : Real.goldenRatio⁻¹ < 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.neg_one_lt_goldenConj]
  refine ⟨hVisible, Real.one_lt_goldenRatio, hHidden,
    Real.goldenConj_neg, hAbs, hContraction, ?_, ?_⟩
  · intro n
    rw [hAbs]
  · rw [show (fun n : Nat => |Real.goldenConj| ^ n) =
      fun n : Nat => Real.goldenRatio⁻¹ ^ n by funext n; rw [hAbs]]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity) hContraction

#print axioms golden_visible_hidden_transport

end D5.S1.Scale.Descent.GoldenVisibleHiddenTransport
