import D5.S3.Geometry.PowerCone.ActualCurveChords

/-!
The actual arbitrary-LHSCB to Curve bridge, conditional only on the named
two horizontal dual endpoint families. All primal, minimization, radial,
symmetry, mixed, graph-derivative, and integral-primitive data are constructed.

Attribution: Rui-Jin Zhang, Wenhao Fu and Yu-Hong Dai, The optimal barrier
parameter of the three-dimensional power cone, arXiv:2611.06404v1,
Theorem 3.5, printed pp. 9--12. This is a known scalar theorem.

SOURCE ONLY: no Lean execution, kernel, required CI, official acceptance,
novelty, unconditional scalar lower bound or full vector optimum is claimed.
The separately developed dual implementation is not imported or read here.
-/

open Set
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier.Actual

variable {c ν : ℝ} {F : ScalarPoint → ℝ}
variable (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)

noncomputable def rho : ℝ := ν-1
noncomputable def scale : ℝ := Real.sqrt (ν-1)

theorem scale_spec : 1 ≤ scale (ν := ν) ∧ ν = scale (ν := ν)^2+1 := by
  have hν := parameter_two_actual hF
  have hρ : 0 ≤ ν-1 := by linarith
  have hs := Real.sq_sqrt hρ
  have hs0 := Real.sqrt_nonneg (ν-1)
  constructor
  · dsimp [scale]
    nlinarith
  · dsimp [scale]
    linarith

theorem rho_scale : rho (ν := ν) = scale (ν := ν)^2 := by
  dsimp [rho]
  linarith [(scale_spec hF).2]

/-- Concrete fields, not existence assumptions. `HorizontalDualEndpoints`
contains precisely strict pairing and the two actual dualQuadratic exclusions
at the projected envelope's horizontal endpoints; see its definition.
In particular no Curve/lower/optimality proposition is a hypothesis. -/
noncomputable def curve (hc : 0 < c) (hc1 : c < 1)
    (hd : HorizontalDualEndpoints hF) : Curve c (scale (ν := ν)) where
  p := p hF
  q := q hF
  k := k hF
  kp := kp hF
  zeta := zeta hF
  sigma := sigma hF
  q_pos := fun _ hr => q_pos hF hr
  k_pos := fun _ hr => k_pos hF hr
  k_deriv := fun _ hr => k_hasDerivAt hF hr
  sigma_deriv := fun _ hr => sigma_hasDerivAt hF hr
  horizontal := fun _ hr => horizontal_bounds hF hc hc1 hd hr
    (scale_spec hF).1 (scale_spec hF).2
  mixed := fun _ hr => beta_bound hF hr (scale_spec hF).1 (scale_spec hF).2
  vertical := fun _ hr => vertical_bounds hF hc hc1 hr
    (lt_of_lt_of_le zero_lt_one (scale_spec hF).1) (scale_spec hF).2

/-- Removes the F3 foundation from the sharp lower mechanism at source
level. The only mathematical premise beyond the original arbitrary barrier
is the explicitly named residual horizontal dual endpoint supplier.
This theorem includes c=1/2; parameter_two_actual also handles that endpoint
without duality. The original domain is coneInterior c, not a larger cone. -/
theorem parameter_lower_of_horizontal_dual (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hd : HorizontalDualEndpoints hF) : 3/(1+c) ≤ ν := by
  have hc1 : c < 1 := by linarith
  have hh := (curve hF hc hc1 hd).parameter_lower hc hc2 (scale_spec hF).1
  rwa [← (scale_spec hF).2] at hh

/-- The balanced endpoint is unconditional at source level. -/
theorem balanced_parameter_lower (hc : c = 1/2) : 3/(1+c) ≤ ν := by
  have hh := parameter_two_actual hF
  rw [hc]
  norm_num
  exact hh

/-- Exact original topological-domain version. Its named residual input is
computed using the original F, after rewriting only the domain and boundary
identities already proved by Topology. There is no enlarged-domain premise. -/
theorem actual_domain_parameter_lower (hc : 0 < c) (hc2 : c ≤ 1/2)
    (hF : IsLHSCB ν (interior (closedCone c : Set ScalarPoint))
      (frontier (closedCone c : Set ScalarPoint)) F)
    (hd : HorizontalDualEndpoints (by
      simpa only [← coneInterior_eq_interior hc.le (by linarith : c ≤ 1),
        ← coneBoundary_eq_frontier hc.le (by linarith : c ≤ 1)] using hF)) :
    3/(1+c) ≤ ν := by
  let h : IsLHSCB ν (coneInterior c) (coneBoundary c) F := by
    simpa only [← coneInterior_eq_interior hc.le (by linarith : c ≤ 1),
      ← coneBoundary_eq_frontier hc.le (by linarith : c ≤ 1)] using hF
  exact parameter_lower_of_horizontal_dual h hc hc2 hd

/-- A future dual supplier of exactly the two displayed endpoint families
will inhabit ScalarLowerClaim without any additional F3 theorem. This is a
conditional connection, not an inhabitant with the dual input omitted. -/
theorem scalarLowerClaim_of_horizontal_dual
    (dual : ∀ (c : ℝ), 0 < c → c < 1/2 → ∀ (ν : ℝ) (F : ScalarPoint → ℝ)
      (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F), HorizontalDualEndpoints hF) :
    ScalarLowerClaim := by
  intro c hc hc2 ν F hF
  by_cases he : c = 1/2
  · exact balanced_parameter_lower hF he
  · exact parameter_lower_of_horizontal_dual hF hc hc2
      (dual c hc (lt_of_le_of_ne hc2 he) ν F hF)

end D5.S3.Analytic.ConvexBarrier.Actual
