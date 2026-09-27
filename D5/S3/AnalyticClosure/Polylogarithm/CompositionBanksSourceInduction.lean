/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionBanksSourceInduction
   generality: G
   mirror-B: none(waiver:private-implementation-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Private source-weight closure for the actual positive-composition branch. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBoundary
import D5.S3.AnalyticClosure.Polylogarithm.CompositionContinuation
import D5.S3.AnalyticClosure.Polylogarithm.CompositionSlit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter Metric Set Topology

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction

open D5.S3.AnalyticClosure.Polylogarithm
open CompositionBoundary CompositionContinuation

private def sourceWeight : List ℕ+ → ℕ := fun ks ↦
  List.sum (List.map (fun entry : ℕ+ ↦ (entry : ℕ)) ks)

private def admissibleRemainder : ℕ+ → List ℕ+ → Prop := fun first suffix ↦
  1 < (first : ℕ) ∧
    ∃ ρ C : ℝ, ∃ M : ℕ,
      0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
        ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
          ‖CompositionContinuation.continued (first :: suffix) (1 - w) -
              (CompositionBoundary.zeta first suffix : ℂ)‖ ≤
            C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M

private def suffixConstant : List ℕ+ → ℝ
  | [] => 1
  | first :: suffix => CompositionBoundary.zeta first suffix

private def leadingOneRemainder : ℕ → List ℕ+ → Prop := fun q suffix ↦
  (suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ 1 < (first : ℕ)) ∧
    ∃ ρ C : ℝ, ∃ M : ℕ, ∃ P : Polynomial ℝ,
      0 < ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
        P.natDegree = q ∧
        P.coeff q = suffixConstant suffix / q.factorial ∧
        ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
          ‖CompositionContinuation.continued
              (List.replicate q (1 : ℕ+) ++ suffix) (1 - w) -
              (P.map Complex.ofRealHom).eval (-Complex.log w)‖ ≤
            C * ‖w‖ * (1 + ‖-Complex.log w‖) ^ M

private theorem actual_upper_bank_atlas :
    ∃ B : List ℕ+ → ℝ → ℂ,
      (∀ (ks : List ℕ+) (x ε : ℝ),
        1 < x → 0 < ε →
        ∃ r : ℝ, 0 < r ∧ r < ε ∧
          ∃ extension : ℂ → ℂ,
            AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
              Set.EqOn extension (CompositionContinuation.continued ks)
                (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
              Tendsto (CompositionContinuation.continued ks)
                (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
                (𝓝 (extension (x : ℂ)))) ∧
      (∀ (ks : List ℕ+) (x r : ℝ) (extension : ℂ → ℂ),
        1 < x → 0 < r →
        AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) →
        Set.EqOn extension (CompositionContinuation.continued ks)
          (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, dist y x < δ →
          extension (y : ℂ) = B ks y) ∧
      ∀ (first : ℕ+) (suffix : List ℕ+) (hfirst : 1 < (first : ℕ)) (x ε : ℝ),
        1 < x → 0 < ε →
        ∃ r : ℝ, 0 < r ∧ r < ε ∧
          ∃ F G : ℂ → ℂ,
            AnalyticOnNhd ℂ F (Metric.ball (x : ℂ) r) ∧
            AnalyticOnNhd ℂ G (Metric.ball (x : ℂ) r) ∧
            Set.EqOn F (CompositionContinuation.continued (first :: suffix))
              (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Set.EqOn G (CompositionContinuation.continued
                (⟨(first : ℕ) - 1, by omega⟩ :: suffix))
              (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            ∀ z ∈ Metric.ball (x : ℂ) r, HasDerivAt F (G z / z) z := by
  classical
  obtain ⟨continued_nil, continued_analytic, _continued_source, leading_deriv,
      ordinary_deriv⟩ := CompositionSlit.result
  have actual_local_primitive_bridge : ∀
      (current actualRhs extendedRhs : ℂ → ℂ) (center y : ℂ) (r : ℝ),
      0 < r → y ∈ Metric.ball center r → y ∈ CompositionContinuation.omega →
      AnalyticOnNhd ℂ current CompositionContinuation.omega →
      AnalyticOnNhd ℂ extendedRhs (Metric.ball center r) →
      (∀ z ∈ CompositionContinuation.omega, z ∈ Metric.ball center r →
        HasDerivAt current (actualRhs z) z) →
      extendedRhs =ᶠ[𝓝 y] actualRhs →
      ∃ extension : ℂ → ℂ,
        AnalyticOnNhd ℂ extension (Metric.ball center r) ∧
          extension =ᶠ[𝓝 y] current ∧
          ∀ z ∈ Metric.ball center r, HasDerivAt extension (extendedRhs z) z := by
    intro current actualRhs extendedRhs center y r hr hy hyo hcurrent hextended
      hcurrentDeriv hrhs
    obtain ⟨extension, hextensionAt, hextensionDeriv⟩ :=
      hextended.differentiableOn.isExactOn_ball.with_val_at y (current y)
    have hextensionAnalytic : AnalyticOnNhd ℂ extension (Metric.ball center r) :=
      (show DifferentiableOn ℂ extension (Metric.ball center r) from
        fun z hz ↦ (hextensionDeriv z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
          Metric.isOpen_ball
    have hlocal : ∀ᶠ z : ℂ in 𝓝 y,
        z ∈ Metric.ball center r ∧ z ∈ CompositionContinuation.omega ∧
          extendedRhs z = actualRhs z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy,
        (Complex.isOpen_slitPlane.preimage (by fun_prop)).mem_nhds hyo, hrhs] with z hz hzo heq
      exact ⟨hz, hzo, heq⟩
    change {z : ℂ | z ∈ Metric.ball center r ∧
      z ∈ CompositionContinuation.omega ∧ extendedRhs z = actualRhs z} ∈ 𝓝 y at hlocal
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hlocal
    have heq : Set.EqOn extension current (Metric.ball y δ) :=
      Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball y δ).isPreconnected
        (fun z hz ↦ (hextensionDeriv z (hδsub hz).1).differentiableAt.differentiableWithinAt)
        (fun z hz ↦ (hcurrent z (hδsub hz).2.1).differentiableAt.differentiableWithinAt)
        (fun z hz ↦ by
          rw [(hextensionDeriv z (hδsub hz).1).deriv,
            (hcurrentDeriv z (hδsub hz).2.1 (hδsub hz).1).deriv, (hδsub hz).2.2])
        (Metric.mem_ball_self hδ) hextensionAt
    exact ⟨extension, hextensionAnalytic,
      Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ) heq, hextensionDeriv⟩
  have actual_leading_extension_step : ∀ (suffix : List ℕ+) (center y : ℂ) (r : ℝ)
      (predecessor : ℂ → ℂ),
      0 < r → y ∈ Metric.ball center r → y ∈ CompositionContinuation.omega →
      AnalyticOnNhd ℂ predecessor (Metric.ball center r) →
      predecessor =ᶠ[𝓝 y] CompositionContinuation.continued suffix →
      (∀ z ∈ Metric.ball center r, z ≠ 1) →
      ∃ extension : ℂ → ℂ,
        AnalyticOnNhd ℂ extension (Metric.ball center r) ∧
          extension =ᶠ[𝓝 y] CompositionContinuation.continued ((1 : ℕ+) :: suffix) ∧
          ∀ z ∈ Metric.ball center r,
            HasDerivAt extension (predecessor z / (1 - z)) z := by
    intro suffix center y r predecessor hr hy hyo hpredecessor hagree hne
    apply actual_local_primitive_bridge
      (CompositionContinuation.continued ((1 : ℕ+) :: suffix))
      (fun z ↦ CompositionContinuation.continued suffix z / (1 - z))
      (fun z ↦ predecessor z / (1 - z)) center y r hr hy hyo
      (continued_analytic _).1
    · exact hpredecessor.div (analyticOnNhd_const.sub analyticOnNhd_id) fun z hz hzero ↦
        hne z hz (sub_eq_zero.mp hzero).symm
    · intro z hz _
      exact leading_deriv suffix z hz
    · filter_upwards [hagree] with z hz
      rw [hz]
  have actual_ordinary_extension_step : ∀ (first : ℕ+) (suffix : List ℕ+)
      (hfirst : 1 < (first : ℕ)) (center y : ℂ) (r : ℝ) (predecessor : ℂ → ℂ),
      0 < r → y ∈ Metric.ball center r → y ∈ CompositionContinuation.omega →
      AnalyticOnNhd ℂ predecessor (Metric.ball center r) →
      predecessor =ᶠ[𝓝 y] CompositionContinuation.continued
        (⟨(first : ℕ) - 1, by omega⟩ :: suffix) →
      (∀ z ∈ Metric.ball center r, z ≠ 0) →
      ∃ extension : ℂ → ℂ,
        AnalyticOnNhd ℂ extension (Metric.ball center r) ∧
          extension =ᶠ[𝓝 y] CompositionContinuation.continued (first :: suffix) ∧
          ∀ z ∈ Metric.ball center r, HasDerivAt extension (predecessor z / z) z := by
    intro first suffix hfirst center y r predecessor hr hy hyo hpredecessor hagree hne
    apply actual_local_primitive_bridge
      (CompositionContinuation.continued (first :: suffix))
      (fun z ↦ CompositionContinuation.continued
        (⟨(first : ℕ) - 1, by omega⟩ :: suffix) z / z)
      (fun z ↦ predecessor z / z) center y r hr hy hyo
      (continued_analytic _).1
    · exact hpredecessor.div analyticOnNhd_id hne
    · intro z hz hzball
      simpa only [if_neg (hne z hzball)] using ordinary_deriv first suffix hfirst z hz
    · filter_upwards [hagree] with z hz
      rw [hz]
  have actual_upper_local_extension : ∀ (ks : List ℕ+) (x ε : ℝ),
      1 < x → 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        ∃ y : ℂ, y ∈ Metric.ball (x : ℂ) r ∧
          0 < y.im ∧
          y ∈ CompositionContinuation.omega ∧
          ∃ extension : ℂ → ℂ,
            AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
              extension =ᶠ[𝓝 y] CompositionContinuation.continued ks := by
    intro ks
    refine Nat.strong_induction_on (p := fun weight ↦ ∀ ks,
      sourceWeight ks = weight → ∀ (x ε : ℝ), 1 < x → 0 < ε →
        ∃ r : ℝ, 0 < r ∧ r < ε ∧
          ∃ y : ℂ, y ∈ Metric.ball (x : ℂ) r ∧ 0 < y.im ∧
            y ∈ CompositionContinuation.omega ∧
            ∃ extension : ℂ → ℂ,
              AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
                extension =ᶠ[𝓝 y] CompositionContinuation.continued ks)
      (sourceWeight ks) ?_ ks rfl
    intro weight ih ks hweight
    have ih : ∀ previous, sourceWeight previous < sourceWeight ks →
        ∀ (x ε : ℝ), 1 < x → 0 < ε →
          ∃ r : ℝ, 0 < r ∧ r < ε ∧
            ∃ y : ℂ, y ∈ Metric.ball (x : ℂ) r ∧ 0 < y.im ∧
              y ∈ CompositionContinuation.omega ∧
              ∃ extension : ℂ → ℂ,
                AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
                  extension =ᶠ[𝓝 y] CompositionContinuation.continued previous := by
      intro previous hprevious
      exact ih (sourceWeight previous) (by simpa only [hweight] using hprevious)
        previous rfl
    intro x ε hx hε
    cases ks with
    | nil =>
        let r := ε / 2
        let y : ℂ := (x : ℂ) + (r / 2 : ℝ) * I
        have hr : 0 < r := by dsimp [r]; linarith
        have hry : y ∈ Metric.ball (x : ℂ) r := by
          rw [Metric.mem_ball, dist_eq_norm]
          simp only [y, add_sub_cancel_left, norm_mul, norm_real, norm_I]
          rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
          linarith
        have hyo : y ∈ CompositionContinuation.omega := by
          change 1 - y ∈ Complex.slitPlane
          rw [Complex.mem_slitPlane_iff]
          right
          simp only [sub_im, one_im, zero_sub, ne_eq, neg_eq_zero]
          apply ne_of_gt
          simp only [y, add_im, ofReal_im, mul_im, ofReal_re, I_im]
          dsimp [r]
          linarith
        have hyim : 0 < y.im := by
          simp only [y, add_im, ofReal_im, mul_im, ofReal_re, I_im]
          dsimp [r]
          linarith
        refine ⟨r, hr, by dsimp [r]; linarith, y, hry, hyim, hyo,
          fun _ ↦ (1 : ℂ), analyticOnNhd_const, ?_⟩
        rw [continued_nil]
    | cons first suffix =>
        let δ : ℝ := min ε ((x - 1) / 2)
        have hδ : 0 < δ := by dsimp [δ]; positivity
        by_cases hfirst : (first : ℕ) = 1
        · have hfirst' : first = (1 : ℕ+) := Subtype.ext hfirst
          subst first
          obtain ⟨r, hr, hrδ, y, hy, hyim, hyo, predecessor, hpredecessor, hagree⟩ :=
            ih suffix (by simp [sourceWeight]) x δ hx hδ
          have hne : ∀ z ∈ Metric.ball (x : ℂ) r, z ≠ 1 := by
            intro z hz hzone
            subst z
            rw [Metric.mem_ball, dist_eq_norm] at hz
            have hrx : r < (x - 1) / 2 := hrδ.trans_le (min_le_right _ _)
            have hnorm : ‖(1 : ℂ) - (x : ℂ)‖ = x - 1 := by
              rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
                Real.norm_eq_abs, abs_of_neg (by linarith : 1 - x < 0)]
              linarith
            rw [hnorm] at hz
            linarith
          obtain ⟨extension, hextension, heq, _hextensionDeriv⟩ :=
            actual_leading_extension_step suffix (x : ℂ) y r predecessor hr hy hyo
              hpredecessor hagree hne
          exact ⟨r, hr, hrδ.trans_le (min_le_left _ _), y, hy, hyim, hyo,
            extension, hextension, heq⟩
        · have hfirstpos : 0 < (first : ℕ) := first.property
          have hfirstgt : 1 < (first : ℕ) := by omega
          let previous : ℕ+ := ⟨(first : ℕ) - 1, by omega⟩
          obtain ⟨r, hr, hrδ, y, hy, hyim, hyo, predecessor, hpredecessor, hagree⟩ :=
            ih (previous :: suffix) (by
              change ((first : ℕ) - 1) + sourceWeight suffix <
                (first : ℕ) + sourceWeight suffix
              omega)
              x δ hx hδ
          have hne : ∀ z ∈ Metric.ball (x : ℂ) r, z ≠ 0 := by
            intro z hz hz0
            subst z
            rw [Metric.mem_ball, dist_eq_norm] at hz
            have hrx : r < (x - 1) / 2 := hrδ.trans_le (min_le_right _ _)
            have hnorm : ‖(0 : ℂ) - (x : ℂ)‖ = x := by
              rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (by linarith : 0 < x)]
            rw [hnorm] at hz
            linarith
          obtain ⟨extension, hextension, heq, _hextensionDeriv⟩ :=
            actual_ordinary_extension_step first suffix hfirstgt (x : ℂ) y r predecessor
              hr hy hyo hpredecessor hagree hne
          exact ⟨r, hr, hrδ.trans_le (min_le_left _ _), y, hy, hyim, hyo,
            extension, hextension, heq⟩
  have actual_upper_local_extension_on_upper : ∀ (ks : List ℕ+) (x ε : ℝ),
      1 < x → 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        ∃ extension : ℂ → ℂ,
          AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
            Set.EqOn extension (CompositionContinuation.continued ks)
              (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) := by
    intro ks x ε hx hε
    obtain ⟨r, hr, hrε, y, hy, hyim, _hyo, extension, hextension, heq⟩ :=
      actual_upper_local_extension ks x ε hx hε
    have hcontinued : AnalyticOnNhd ℂ (CompositionContinuation.continued ks)
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
      (continued_analytic ks).1.mono fun z hz ↦ by
        change 1 - z ∈ Complex.slitPlane
        rw [Complex.mem_slitPlane_iff]
        right
        simp only [sub_im, one_im, zero_sub, neg_ne_zero]
        exact ne_of_gt hz.2
    have hpreconnected : IsPreconnected
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
      ((convex_ball (x : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    refine ⟨r, hr, hrε, extension, hextension, ?_⟩
    exact (hextension.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      hcontinued hpreconnected ⟨hy, hyim⟩ heq
  have actual_upper_extensions_unique_on_real_overlap : ∀ (target : ℂ → ℂ)
      (x₁ x₂ a r₁ r₂ : ℝ) (extension₁ extension₂ : ℂ → ℂ),
      (a : ℂ) ∈ Metric.ball (x₁ : ℂ) r₁ ∩ Metric.ball (x₂ : ℂ) r₂ →
      AnalyticOnNhd ℂ extension₁ (Metric.ball (x₁ : ℂ) r₁) →
      AnalyticOnNhd ℂ extension₂ (Metric.ball (x₂ : ℂ) r₂) →
      Set.EqOn extension₁ target
          (Metric.ball (x₁ : ℂ) r₁ ∩ {z : ℂ | 0 < z.im}) →
      Set.EqOn extension₂ target
          (Metric.ball (x₂ : ℂ) r₂ ∩ {z : ℂ | 0 < z.im}) →
      Set.EqOn extension₁ extension₂
        (Metric.ball (x₁ : ℂ) r₁ ∩ Metric.ball (x₂ : ℂ) r₂) := by
    intro target x₁ x₂ a r₁ r₂ extension₁ extension₂ ha hextension₁ hextension₂ heq₁ heq₂
    have ha₁ : dist (a : ℂ) (x₁ : ℂ) < r₁ := by
      simpa only [Metric.mem_ball] using ha.1
    have ha₂ : dist (a : ℂ) (x₂ : ℂ) < r₂ := by
      simpa only [Metric.mem_ball] using ha.2
    let δ : ℝ := min (r₁ - dist (a : ℂ) (x₁ : ℂ))
      (r₂ - dist (a : ℂ) (x₂ : ℂ)) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    let y : ℂ := (a : ℂ) + (δ : ℝ) * I
    have hya : dist y (a : ℂ) = δ := by
      rw [dist_eq_norm]
      simp only [y, add_sub_cancel_left, norm_mul, norm_real, norm_I]
      rw [Real.norm_eq_abs, abs_of_pos hδ, mul_one]
    have hy₁ : y ∈ Metric.ball (x₁ : ℂ) r₁ := by
      rw [Metric.mem_ball]
      calc
        dist y (x₁ : ℂ) ≤ dist y (a : ℂ) + dist (a : ℂ) (x₁ : ℂ) :=
          dist_triangle _ _ _
        _ = δ + dist (a : ℂ) (x₁ : ℂ) := by rw [hya]
        _ < r₁ := by
          have hδle : δ ≤ (r₁ - dist (a : ℂ) (x₁ : ℂ)) / 2 := by
            exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
          linarith
    have hy₂ : y ∈ Metric.ball (x₂ : ℂ) r₂ := by
      rw [Metric.mem_ball]
      calc
        dist y (x₂ : ℂ) ≤ dist y (a : ℂ) + dist (a : ℂ) (x₂ : ℂ) :=
          dist_triangle _ _ _
        _ = δ + dist (a : ℂ) (x₂ : ℂ) := by rw [hya]
        _ < r₂ := by
          have hδle : δ ≤ (r₂ - dist (a : ℂ) (x₂ : ℂ)) / 2 := by
            exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
          linarith
    have hyim : 0 < y.im := by
      simpa [y] using hδ
    have hopen : IsOpen
        ((Metric.ball (x₁ : ℂ) r₁ ∩ Metric.ball (x₂ : ℂ) r₂) ∩
          {z : ℂ | 0 < z.im}) :=
      (Metric.isOpen_ball.inter Metric.isOpen_ball).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have heventually : extension₁ =ᶠ[𝓝 y] extension₂ :=
      Filter.eventually_of_mem (hopen.mem_nhds ⟨⟨hy₁, hy₂⟩, hyim⟩)
        (fun z hz ↦ (heq₁ ⟨hz.1.1, hz.2⟩).trans (heq₂ ⟨hz.1.2, hz.2⟩).symm)
    exact (hextension₁.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (hextension₂.mono Set.inter_subset_right)
      ((convex_ball (x₁ : ℂ) r₁).inter (convex_ball (x₂ : ℂ) r₂)).isPreconnected
      ⟨hy₁, hy₂⟩ heventually
  have actual_upper_local_extension_with_limit : ∀ (ks : List ℕ+) (x ε : ℝ),
      1 < x → 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        ∃ extension : ℂ → ℂ,
          AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) ∧
            Set.EqOn extension (CompositionContinuation.continued ks)
              (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
            Tendsto (CompositionContinuation.continued ks)
              (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
              (𝓝 (extension (x : ℂ))) := by
    intro ks x ε hx hε
    obtain ⟨r, hr, hrε, extension, hextension, heq⟩ :=
      actual_upper_local_extension_on_upper ks x ε hx hε
    refine ⟨r, hr, hrε, extension, hextension, heq, ?_⟩
    have hextensionLimit : Tendsto extension
        (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
        (𝓝 (extension (x : ℂ))) :=
      (hextension (x : ℂ) (Metric.mem_ball_self hr)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    refine hextensionLimit.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact heq hz
  have actual_upper_bank_value_exists_unique : ∀ (ks : List ℕ+) (x : ℝ),
      1 < x →
      ∃ value : ℂ,
        (∃ r : ℝ, 0 < r ∧
          Tendsto (CompositionContinuation.continued ks)
            (𝓝[(Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im})] (x : ℂ))
            (𝓝 value)) ∧
        ∀ (r : ℝ) (extension : ℂ → ℂ),
          0 < r →
          AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) →
          Set.EqOn extension (CompositionContinuation.continued ks)
            (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) →
          extension (x : ℂ) = value := by
    intro ks x hx
    obtain ⟨referenceRadius, hreferenceRadius, _hreferenceSmall, reference,
        hreferenceAnalytic, hreferenceEq, hreferenceLimit⟩ :=
      actual_upper_local_extension_with_limit ks x 1 hx zero_lt_one
    refine ⟨reference (x : ℂ), ⟨referenceRadius, hreferenceRadius,
      hreferenceLimit⟩, ?_⟩
    intro r extension hr hextension heq
    have hpoint : (x : ℂ) ∈
        Metric.ball (x : ℂ) referenceRadius ∩ Metric.ball (x : ℂ) r :=
      ⟨Metric.mem_ball_self hreferenceRadius, Metric.mem_ball_self hr⟩
    have hunique := actual_upper_extensions_unique_on_real_overlap
      (CompositionContinuation.continued ks) x x x
      referenceRadius r reference extension hpoint hreferenceAnalytic hextension
      hreferenceEq heq
    exact (hunique hpoint).symm
  let actualUpperBank : List ℕ+ → ℝ → ℂ := fun ks x ↦
    if hx : 1 < x then Classical.choose (actual_upper_bank_value_exists_unique ks x hx)
    else 0
  have actual_upper_bank_local_trace : ∀ (ks : List ℕ+) (x r : ℝ)
      (extension : ℂ → ℂ),
      1 < x → 0 < r →
      AnalyticOnNhd ℂ extension (Metric.ball (x : ℂ) r) →
      Set.EqOn extension (CompositionContinuation.continued ks)
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, dist y x < δ →
        extension (y : ℂ) = actualUpperBank ks y := by
    intro ks x r extension hx hr hextension heq
    let δ : ℝ := min (r / 2) ((x - 1) / 2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have hyx : dist (y : ℂ) (x : ℂ) < r := by
      have hdist : dist (y : ℂ) (x : ℂ) = dist y x := by
        rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, Real.dist_eq]
      rw [hdist]
      exact hy.trans_le
        ((min_le_left (r / 2) ((x - 1) / 2)).trans (by linarith))
    have hyone : 1 < y := by
      rw [Real.dist_eq] at hy
      have hyabs : |y - x| < (x - 1) / 2 :=
        hy.trans_le (min_le_right (r / 2) ((x - 1) / 2))
      have hneg := neg_lt_of_abs_lt hyabs
      linarith
    let s : ℝ := r - dist (y : ℂ) (x : ℂ)
    have hs : 0 < s := by dsimp [s]; linarith
    have hsub : Metric.ball (y : ℂ) s ⊆ Metric.ball (x : ℂ) r := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      calc
        dist z (x : ℂ) ≤ dist z (y : ℂ) + dist (y : ℂ) (x : ℂ) := dist_triangle _ _ _
        _ < s + dist (y : ℂ) (x : ℂ) := by linarith
        _ = r := by simp [s]
    have heq' : Set.EqOn extension (CompositionContinuation.continued ks)
        (Metric.ball (y : ℂ) s ∩ {z : ℂ | 0 < z.im}) := by
      apply heq.mono
      rintro z ⟨hzball, hzim⟩
      exact ⟨hsub hzball, hzim⟩
    have hvalue := (Classical.choose_spec
      (actual_upper_bank_value_exists_unique ks y hyone)).2 s extension hs
      (hextension.mono hsub) heq'
    dsimp only [actualUpperBank]
    rw [dif_pos hyone]
    exact hvalue
  have actual_upper_ordinary_pair : ∀ (first : ℕ+) (suffix : List ℕ+)
      (hfirst : 1 < (first : ℕ)) (x ε : ℝ),
      1 < x → 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        ∃ F G : ℂ → ℂ,
          AnalyticOnNhd ℂ F (Metric.ball (x : ℂ) r) ∧
          AnalyticOnNhd ℂ G (Metric.ball (x : ℂ) r) ∧
          Set.EqOn F (CompositionContinuation.continued (first :: suffix))
            (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
          Set.EqOn G (CompositionContinuation.continued
              (⟨(first : ℕ) - 1, by omega⟩ :: suffix))
            (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
          ∀ z ∈ Metric.ball (x : ℂ) r, HasDerivAt F (G z / z) z := by
    intro first suffix hfirst x ε hx hε
    let δ : ℝ := min ε (x / 2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨r, hr, hrδ, G, hG, hGactual⟩ :=
      actual_upper_local_extension_on_upper
        (⟨(first : ℕ) - 1, by omega⟩ :: suffix) x δ hx hδ
    let y : ℂ := (x : ℂ) + (r / 2 : ℝ) * I
    have hy : y ∈ Metric.ball (x : ℂ) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [y, add_sub_cancel_left, norm_mul, norm_real, norm_I]
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
      linarith
    have hyim : 0 < y.im := by
      simp only [y, add_im, ofReal_im, mul_im, ofReal_re, I_im]
      linarith
    have hyo : y ∈ CompositionContinuation.omega := by
      change 1 - y ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      right
      simp only [sub_im, one_im, y, add_im, ofReal_im, mul_im, ofReal_re, I_im,
        zero_sub, neg_ne_zero]
      positivity
    have hGagree : G =ᶠ[𝓝 y] CompositionContinuation.continued
        (⟨(first : ℕ) - 1, by omega⟩ :: suffix) := by
      have hopen : IsOpen (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
        Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
      exact Filter.eventually_of_mem (hopen.mem_nhds ⟨hy, hyim⟩) hGactual
    have hne : ∀ z ∈ Metric.ball (x : ℂ) r, z ≠ 0 := by
      intro z hz hz0
      subst z
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hrx : r < x / 2 := hrδ.trans_le (min_le_right _ _)
      have hnorm : ‖(0 : ℂ) - (x : ℂ)‖ = x := by
        rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith : 0 < x)]
      rw [hnorm] at hz
      linarith
    obtain ⟨F, hF, hFagree, hFderiv⟩ := actual_ordinary_extension_step first suffix
      hfirst (x : ℂ) y r G hr hy hyo hG hGagree hne
    have hcontinued : AnalyticOnNhd ℂ
        (CompositionContinuation.continued (first :: suffix))
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
      (continued_analytic _).1.mono fun z hz ↦ by
        change 1 - z ∈ Complex.slitPlane
        rw [Complex.mem_slitPlane_iff]
        right
        simp only [sub_im, one_im, zero_sub, neg_ne_zero]
        exact ne_of_gt hz.2
    have hpreconnected : IsPreconnected
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
      ((convex_ball (x : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hFactual : Set.EqOn F (CompositionContinuation.continued (first :: suffix))
        (Metric.ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
      (hF.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
        hcontinued hpreconnected ⟨hy, hyim⟩ hFagree
    exact ⟨r, hr, hrδ.trans_le (min_le_left _ _), F, G, hF, hG,
      hFactual, hGactual, hFderiv⟩
  exact ⟨actualUpperBank, actual_upper_local_extension_with_limit,
    actual_upper_bank_local_trace, actual_upper_ordinary_pair⟩

private theorem composition_remainder_cases_of_controls
    (head : ℕ+) (tail : List ℕ+)
    (composition_continued_norm_bound : ∀ ks : List ℕ+,
      (∀ (first : ℕ+) (rest : List ℕ+),
        sourceWeight (first :: rest) ≤ sourceWeight ks → 1 < (first : ℕ) →
          admissibleRemainder first rest) →
      ∃ ρ D : ℝ, ∃ N : ℕ,
        0 < ρ ∧ ρ < 1 ∧ 0 ≤ D ∧
          ∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
            ‖CompositionContinuation.continued ks (1 - w)‖ ≤
              D * (1 + ‖-Complex.log w‖) ^ N)
    (ordinary_admissible_remainder_step : ∀ (first : ℕ+) (suffix : List ℕ+)
      (hfirst : 1 < (first : ℕ)) (ρ D : ℝ) (N : ℕ),
      0 < ρ → ρ < 1 → 0 ≤ D →
      (∀ w : ℂ, w ∈ Complex.slitPlane → 0 < ‖w‖ → ‖w‖ < ρ →
        ‖CompositionContinuation.continued
            (⟨(first : ℕ) - 1, by omega⟩ :: suffix) (1 - w)‖ ≤
          D * (1 + ‖-Complex.log w‖) ^ N) →
        admissibleRemainder first suffix)
    (leading_one_remainder_iterate : ∀ (q : ℕ) (suffix : List ℕ+),
      leadingOneRemainder 0 suffix → leadingOneRemainder q suffix)
    (split_leading_ones : ∀ ks : List ℕ+,
      ∃ q suffix, ks = List.replicate q (1 : ℕ+) ++ suffix ∧
        (suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ 1 < (first : ℕ))) :
    (1 < (head : ℕ) ∧ admissibleRemainder head tail) ∨
      ∃ q suffix,
        head = (1 : ℕ+) ∧ 1 ≤ q ∧
        head :: tail = List.replicate q (1 : ℕ+) ++ suffix ∧
        (suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ 1 < (first : ℕ)) ∧
        leadingOneRemainder q suffix := by
  have admissible_remainder_all : ∀ (first : ℕ+) (suffix : List ℕ+),
      1 < (first : ℕ) → admissibleRemainder first suffix := by
    let P : List ℕ+ → Prop := fun ks ↦
      ∀ (first : ℕ+) (suffix : List ℕ+), ks = first :: suffix →
        1 < (first : ℕ) → admissibleRemainder first suffix
    have hall : ∀ ks, P ks := by
      intro ks
      refine Nat.strong_induction_on (p := fun weight ↦ ∀ ks,
        sourceWeight ks = weight → P ks) (sourceWeight ks) ?_ ks rfl
      intro weight ih ks hweight
      have ih : ∀ previous, sourceWeight previous < sourceWeight ks → P previous := by
        intro previous hprevious
        exact ih (sourceWeight previous) (by simpa only [hweight] using hprevious)
          previous rfl
      intro first suffix hks hfirst
      subst ks
      let predecessor : List ℕ+ := ⟨(first : ℕ) - 1, by omega⟩ :: suffix
      have hpredecessor : sourceWeight predecessor < sourceWeight (first :: suffix) := by
        change ((first : ℕ) - 1) + sourceWeight suffix <
          (first : ℕ) + sourceWeight suffix
        omega
      have hadmissible : ∀ (next : ℕ+) (rest : List ℕ+),
          sourceWeight (next :: rest) ≤ sourceWeight predecessor →
          1 < (next : ℕ) → admissibleRemainder next rest := by
        intro next rest hweight hnext
        have hprevious := ih (next :: rest) (hweight.trans_lt hpredecessor)
        exact hprevious next rest rfl hnext
      obtain ⟨ρ, D, N, hρ0, hρ1, hD, hbound⟩ :=
        composition_continued_norm_bound predecessor hadmissible
      exact ordinary_admissible_remainder_step first suffix hfirst ρ D N
        hρ0 hρ1 hD (by simpa only [predecessor] using hbound)
    intro first suffix hfirst
    exact hall (first :: suffix) first suffix rfl hfirst
  have leading_one_remainder_all : ∀ (q : ℕ) (suffix : List ℕ+),
      (suffix = [] ∨ ∃ first rest, suffix = first :: rest ∧ 1 < (first : ℕ)) →
        leadingOneRemainder q suffix := by
    intro q suffix hsuffix
    apply leading_one_remainder_iterate q suffix
    have leading_one_remainder_zero : leadingOneRemainder 0 [] := by
      refine ⟨Or.inl rfl, (1 / 2 : ℝ), 0, 0, 1, by norm_num, by norm_num,
        by norm_num, by simp, ?_, ?_⟩
      · simp [suffixConstant]
      · intro w _hw _hw0 _hwrho
        rw [show List.replicate 0 (1 : ℕ+) ++ [] = [] by simp,
          (CompositionSlit.result).1]
        norm_num
    have leading_one_remainder_zero_of_admissible : ∀
        (first : ℕ+) (suffix : List ℕ+),
        admissibleRemainder first suffix → leadingOneRemainder 0 (first :: suffix) := by
      intro first suffix hadmissible
      rcases hadmissible with ⟨hfirst, ρ, C, M, hρ0, hρ1, hC, hbound⟩
      refine ⟨Or.inr ⟨first, suffix, rfl, hfirst⟩, ρ, C, M,
        Polynomial.C (CompositionBoundary.zeta first suffix), hρ0, hρ1, hC,
        by simp, by simp [suffixConstant], ?_⟩
      intro w hw hw0 hwrho
      simpa using hbound w hw hw0 hwrho
    rcases hsuffix with rfl | ⟨first, rest, rfl, hfirst⟩
    · exact leading_one_remainder_zero
    · exact leading_one_remainder_zero_of_admissible first rest
        (admissible_remainder_all first rest hfirst)
  by_cases hhead : 1 < (head : ℕ)
  · exact Or.inl ⟨hhead, admissible_remainder_all head tail hhead⟩
  · right
    obtain ⟨q, suffix, hsplit, hsuffix⟩ := split_leading_ones (head :: tail)
    have hheadOne : head = (1 : ℕ+) := by
      apply Subtype.ext
      apply Nat.le_antisymm (Nat.le_of_not_gt hhead)
      exact Nat.succ_le_iff.mpr head.property
    have hq : 1 ≤ q := by
      by_contra hq
      have hq0 : q = 0 := by omega
      subst q
      have hsuffixEq : suffix = head :: tail := by simpa using hsplit.symm
      rcases hsuffix with hsuffixNil | ⟨first, rest, hsuffixCons, hfirst⟩
      · exact (List.cons_ne_nil head tail (hsuffixEq.symm.trans hsuffixNil)).elim
      · have hheads : head = first :=
          (List.cons.inj (hsuffixEq.symm.trans hsuffixCons)).1
        apply hhead
        simpa [hheads] using hfirst
    exact ⟨q, suffix, hheadOne, hq, hsplit, hsuffix,
      leading_one_remainder_all q suffix hsuffix⟩

end D5.S3.AnalyticClosure.Polylogarithm.CompositionBanksSourceInduction
