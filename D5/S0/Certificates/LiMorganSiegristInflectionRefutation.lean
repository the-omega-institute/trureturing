/- GID: D5/S0/Certificates/LiMorganSiegristInflectionRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/LiMorganSiegristInflectionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/LiMorganSiegristInflectionRefutation.claim; result=D5/S0/Certificates/LiMorganSiegristInflectionRefutation.result; claim=D5/S0/Certificates/LiMorganSiegristInflectionRefutation.claim
   digest: Refutes uniqueness of the fractional concavity transition. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18772; Refuted).
Direct frozen dependencies: none (pinned Mathlib only).
All twelve private theorems have proof_shape: bind-only and escape_witness: none.
Consumers: forcing_hypotheses -> result; integral_half_mul_pow -> monomial_integral;
monomial_integral -> forcing_integral; h_deriv -> h_iteratedDeriv;
h1_deriv -> h_iteratedDeriv; h_iteratedDeriv -> curvature_identity;
h2_polynomial -> curvature_identity; forcing_integral -> solution_closed_form;
solution_closed_form -> curvature_identity; curvature_identity -> two_distinct_zeros;
polynomial_signs -> two_distinct_zeros; two_distinct_zeros -> result.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The source expressions in #18772 define rlIntegral, solution, Hypotheses and claim.
The weak-solution interpretation of solution is the source's representation (7);
no fractional Sobolev equivalence is asserted here.
-/


import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false

namespace D5.S0.Certificates.LiMorganSiegristInflectionRefutation

open Real Set Filter Topology

/-- Definition 1.1: the left-sided Riemann–Liouville fractional integral on `[0, x]`,
`I^α u(x) = Γ(α)⁻¹ ∫₀ˣ (x − t)^(α−1) u(t) dt`. -/
noncomputable def rlIntegral (α : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Gamma α)⁻¹ * ∫ t in (0 : ℝ)..x, (x - t) ^ (α - 1) * u t

/-- The solution of `D^α F = f` in `(0, 1)`, `F(0) = F(1) = 0`, in the representation (7):
`u(x) = I^α f(x) + c x^(α−1)`, `c = −I^α f(1)`. -/
noncomputable def solution (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  rlIntegral α f x - rlIntegral α f 1 * x ^ (α - 1)

/-- The hypotheses of Theorem 5.2: `f ∈ C([0, 1]) ∩ C¹((0, 1])`, `f(1) = 0`, `f ≥ 0` on `[0, 1]`,
`f ≢ 0`, and `lim_{x → 0+} x^((3−α)/(2−α)) f′(x) = 0`. -/
def Hypotheses (α : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Icc 0 1) ∧ ContDiffOn ℝ 1 f (Ioc 0 1) ∧ f 1 = 0 ∧
    (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x) ∧ (∃ x ∈ Icc (0 : ℝ) 1, f x ≠ 0) ∧
    Tendsto (fun x => x ^ ((3 - α) / (2 - α)) * deriv f x) (𝓝[>] 0) (𝓝 0)

/-- Li–Morgan–Siegrist, Conjecture 6.1: "Let 1 < α < 2. Under the hypotheses of Theorem 5.2, the
second derivative F″ has exactly one zero in (0, 1). Moreover, F″ changes sign at this zero, so
that this point is the unique inflection point of F." -/
def claim : Prop :=
  ∀ α : ℝ, 1 < α → α < 2 → ∀ f : ℝ → ℝ, Hypotheses α f →
    ∃ ξ ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 (solution α f) ξ = 0 ∧
      (∀ η ∈ Ioo (0 : ℝ) 1, iteratedDeriv 2 (solution α f) η = 0 → η = ξ) ∧
      ∃ δ > 0, ∀ y z : ℝ, ξ - δ < y → y < ξ → ξ < z → z < ξ + δ →
        iteratedDeriv 2 (solution α f) y * iteratedDeriv 2 (solution α f) z < 0

end D5.S0.Certificates.LiMorganSiegristInflectionRefutation


namespace D5.S0.Certificates.LiMorganSiegristInflectionRefutation
open Real Set Filter Topology
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private noncomputable def forcing (x : ℝ) : ℝ := (1 - x) * (1 + 5 * x^12)

private theorem forcing_hypotheses : Hypotheses (3/2) forcing := by
  have hf : ContDiff ℝ ⊤ forcing := by unfold forcing; fun_prop
  refine ⟨hf.continuous.continuousOn, hf.of_le (by simp) |>.contDiffOn, ?_, ?_, ?_, ?_⟩
  · norm_num [forcing]
  · intro x hx
    exact mul_nonneg (sub_nonneg.mpr hx.2) (by positivity)
  · exact ⟨0, by norm_num, by norm_num [forcing]⟩
  · have hc : Continuous (fun x : ℝ => x^3 * deriv forcing x) := by
      exact (continuous_id.pow 3).mul (hf.continuous_deriv (by simp))
    have ht : Tendsto (fun x : ℝ => x^3 * deriv forcing x) (𝓝[>] 0) (𝓝 (0^3 * deriv forcing 0)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    convert ht using 1 <;> norm_num [Real.rpow_natCast]


private theorem integral_half_mul_pow (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∫ u in (0:ℝ)..x, u ^ (1/2:ℝ) * u^n) =
      x ^ (3/2:ℝ) * x^n / ((n:ℝ) + 3/2) := by
  calc
    _ = ∫ u in (0:ℝ)..x, u ^ ((1/2:ℝ) + (n:ℝ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hx.le] at hu
      exact (Real.rpow_add_natCast' hu.1 (by positivity)).symm
    _ = (x ^ ((1/2:ℝ) + (n:ℝ) + 1) - 0 ^ ((1/2:ℝ) + (n:ℝ) + 1)) /
        ((1/2:ℝ) + (n:ℝ) + 1) := integral_rpow (Or.inl (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))
    _ = _ := by
      rw [show (1/2:ℝ) + (n:ℝ) + 1 = 3/2 + (n:ℝ) by ring,
        Real.zero_rpow (by positivity), sub_zero, Real.rpow_add_natCast hx.ne']
      congr 1 <;> ring

private theorem monomial_integral (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∫ t in (0:ℝ)..x, (x-t) ^ (1/2:ℝ) * t^n) =
      (∑ k ∈ Finset.range (n+1), (-1:ℝ)^(n-k) * (n.choose k:ℝ) /
        ((n-k:ℕ)+ (3/2:ℝ))) * (x ^ (3/2:ℝ) * x^n) := by
  have changevar : (∫ t in (0:ℝ)..x, (x-t) ^ (1/2:ℝ) * t^n) =
      ∫ u in (0:ℝ)..x, u ^ (1/2:ℝ) * (x-u)^n := by
    have h := intervalIntegral.integral_comp_sub_left
      (a := (0:ℝ)) (b := x) (fun u : ℝ => u^(1/2:ℝ) * (x-u)^n) x
    simpa only [sub_sub_cancel, sub_self, sub_zero] using h
  rw [changevar]
  simp_rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  have rearr : ∀ u : ℝ,
      (∑ k ∈ Finset.range (n+1), u^(1/2:ℝ) * (x^k * (-u)^(n-k) * (n.choose k:ℝ))) =
      ∑ k ∈ Finset.range (n+1), ((-1:ℝ)^(n-k) * (n.choose k:ℝ) * x^k) *
        (u^(1/2:ℝ) * u^(n-k)) := by
    intro u
    apply Finset.sum_congr rfl
    intro k hk
    rw [neg_pow]
    ring
  simp_rw [rearr]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_half_mul_pow x hx]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hp : x^k * x^(n-k) = x^n := pow_mul_pow_sub x hkn
    calc
      _ = ((-1:ℝ)^(n-k)*(n.choose k:ℝ)/((n-k:ℕ)+(3/2:ℝ))) *
          x^(3/2:ℝ) * (x^k*x^(n-k)) := by ring
      _ = _ := by rw [hp]; ring
  · intro k hk
    exact (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/2)).mul
      (continuous_id.pow (n-k))).const_mul _).intervalIntegrable _ _


private noncomputable def h (x : ℝ) : ℝ :=
  (2/3:ℝ)*x^(3/2:ℝ) - (4/15:ℝ)*x^(5/2:ℝ) +
  (8388608/91265265:ℝ)*x^(27/2:ℝ) - (16777216/203591745:ℝ)*x^(29/2:ℝ) -
  (361280966/882230895:ℝ)*x^(1/2:ℝ)
private noncomputable def h1 (x : ℝ) : ℝ :=
  x^(1/2:ℝ) - (2/3:ℝ)*x^(3/2:ℝ) +
  (4194304/3380195:ℝ)*x^(25/2:ℝ) - (8388608/7020405:ℝ)*x^(27/2:ℝ) -
  (180640483/882230895:ℝ)*x^(-1/2:ℝ)
private noncomputable def h2 (x : ℝ) : ℝ :=
  (1/2:ℝ)*x^(-1/2:ℝ) - x^(1/2:ℝ) +
  (10485760/676039:ℝ)*x^(23/2:ℝ) - (4194304/260015:ℝ)*x^(25/2:ℝ) +
  (180640483/1764461790:ℝ)*x^(-3/2:ℝ)
private noncomputable def curvaturePolynomial (x : ℝ) : ℝ :=
  (180640483/1764461790:ℝ) + x/2 - x^2 +
  (10485760/676039:ℝ)*x^13 - (4194304/260015:ℝ)*x^14

private theorem h_deriv (x : ℝ) (hx : x ≠ 0) : HasDerivAt h (h1 x) x := by
  have hp (p : ℝ) := Real.hasDerivAt_rpow_const (p := p) (Or.inl hx)
  have hd := (hp (3/2)).const_mul (2/3)
  have hd := hd.sub ((hp (5/2)).const_mul (4/15))
  have hd := hd.add ((hp (27/2)).const_mul (8388608/91265265))
  have hd := hd.sub ((hp (29/2)).const_mul (16777216/203591745))
  have hd := hd.sub ((hp (1/2)).const_mul (361280966/882230895))
  convert hd using 1 <;> (first | rfl | (norm_num [h1] <;> ring))

private theorem h1_deriv (x : ℝ) (hx : x ≠ 0) : HasDerivAt h1 (h2 x) x := by
  have hp (p : ℝ) := Real.hasDerivAt_rpow_const (p := p) (Or.inl hx)
  have hd := (hp (1/2)).sub ((hp (3/2)).const_mul (2/3))
  have hd := hd.add ((hp (25/2)).const_mul (4194304/3380195))
  have hd := hd.sub ((hp (27/2)).const_mul (8388608/7020405))
  have hd := hd.sub ((hp (-1/2)).const_mul (180640483/882230895))
  convert hd using 1 <;> (first | rfl | (norm_num [h2] <;> ring))

private theorem h_iteratedDeriv (x : ℝ) (hx : x ≠ 0) :
    iteratedDeriv 2 h x = h2 x := by
  have he : deriv h =ᶠ[𝓝 x] h1 := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (h_deriv y hy).deriv
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    he.deriv_eq.trans (h1_deriv x hx).deriv

private theorem h2_polynomial (x : ℝ) (hx : 0 < x) :
    x^(3/2:ℝ) * h2 x = curvaturePolynomial x := by
  have hp (p : ℝ) : x^(3/2:ℝ)*x^p = x^((3/2:ℝ)+p) := (Real.rpow_add hx _ _).symm
  calc
    _ = (1/2:ℝ)*(x^(3/2:ℝ)*x^(-1/2:ℝ)) - (x^(3/2:ℝ)*x^(1/2:ℝ)) +
      (10485760/676039:ℝ)*(x^(3/2:ℝ)*x^(23/2:ℝ)) -
      (4194304/260015:ℝ)*(x^(3/2:ℝ)*x^(25/2:ℝ)) +
      (180640483/1764461790:ℝ)*(x^(3/2:ℝ)*x^(-3/2:ℝ)) := by unfold h2; ring
    _ = _ := by simp_rw [hp]; norm_num [curvaturePolynomial]; ring


private theorem forcing_integral (x : ℝ) (hx : 0 < x) :
    (∫ t in (0:ℝ)..x, (x-t)^(1/2:ℝ) * forcing t) =
      (2/3:ℝ)*x^(3/2:ℝ) - (4/15:ℝ)*x^(5/2:ℝ) +
      (8388608/91265265:ℝ)*x^(27/2:ℝ) - (16777216/203591745:ℝ)*x^(29/2:ℝ) := by
  have hi (n : ℕ) : IntervalIntegrable (fun t : ℝ => (x-t)^(1/2:ℝ)*t^n)
      MeasureTheory.volume 0 x := by
    exact (((continuous_const.sub continuous_id).rpow_const (by norm_num)).mul
      (continuous_id.pow n)).intervalIntegrable _ _
  have i0 := monomial_integral x hx 0
  have i1 := monomial_integral x hx 1
  have i12 := monomial_integral x hx 12
  have i13 := monomial_integral x hx 13
  norm_num [Finset.sum_range_succ, Nat.choose] at i0 i1 i12 i13
  have rp1 : x^(5/2:ℝ) = x^(3/2:ℝ)*x := by
    convert Real.rpow_add_natCast hx.ne' (3/2:ℝ) 1 using 1 <;> norm_num
  have rp12 : x^(27/2:ℝ) = x^(3/2:ℝ)*x^12 := by
    convert Real.rpow_add_natCast hx.ne' (3/2:ℝ) 12 using 1 <;> norm_num
  have rp13 : x^(29/2:ℝ) = x^(3/2:ℝ)*x^13 := by
    convert Real.rpow_add_natCast hx.ne' (3/2:ℝ) 13 using 1 <;> norm_num
  calc
    _ = ∫ t in (0:ℝ)..x, ((x-t)^(1/2:ℝ)*t^0 - (x-t)^(1/2:ℝ)*t^1 +
      5*((x-t)^(1/2:ℝ)*t^12) - 5*((x-t)^(1/2:ℝ)*t^13)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      unfold forcing
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (((hi 0).sub (hi 1)).add ((hi 12).const_mul 5))
          ((hi 13).const_mul 5),
        intervalIntegral.integral_add ((hi 0).sub (hi 1)) ((hi 12).const_mul 5),
        intervalIntegral.integral_sub (hi 0) (hi 1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [pow_zero, mul_one, pow_one]
      rw [i0, i1, i12, i13, rp1, rp12, rp13]
      ring

private theorem solution_closed_form (x : ℝ) (hx : 0 < x) :
    solution (3/2) forcing x = (Gamma (3/2))⁻¹ * h x := by
  unfold solution rlIntegral
  norm_num only [show (3/2:ℝ)-1=(1/2:ℝ) by norm_num]
  rw [forcing_integral x hx, forcing_integral 1 (by norm_num)]
  norm_num [h]
  ring

private theorem curvature_identity (x : ℝ) (hx : 0 < x) :
    x^(3/2:ℝ) * Gamma (3/2) * iteratedDeriv 2 (solution (3/2) forcing) x =
      curvaturePolynomial x := by
  have he : solution (3/2) forcing =ᶠ[𝓝 x] (fun y => (Gamma (3/2))⁻¹ * h y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact solution_closed_form y hy
  rw [he.iteratedDeriv_eq 2, iteratedDeriv_const_mul_field, h_iteratedDeriv x hx.ne']
  have hg : Gamma (3/2:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  calc
    _ = x^(3/2:ℝ) * h2 x := by field_simp
    _ = _ := h2_polynomial x hx

private theorem polynomial_signs :
    0 < curvaturePolynomial (7/10) ∧ curvaturePolynomial (3/4) < 0 ∧
      0 < curvaturePolynomial (4/5) := by
  norm_num [curvaturePolynomial]

private theorem two_distinct_zeros :
    ∃ a ∈ Ioo (0:ℝ) 1, ∃ b ∈ Ioo (0:ℝ) 1,
      a ≠ b ∧ iteratedDeriv 2 (solution (3/2) forcing) a = 0 ∧
        iteratedDeriv 2 (solution (3/2) forcing) b = 0 := by
  have hc : Continuous curvaturePolynomial := by unfold curvaturePolynomial; fun_prop
  obtain ⟨a, ha, hpa⟩ := intermediate_value_Ioo' (by norm_num : (7/10:ℝ) ≤ 3/4)
    hc.continuousOn ⟨polynomial_signs.2.1, polynomial_signs.1⟩
  obtain ⟨b, hb, hpb⟩ := intermediate_value_Ioo (by norm_num : (3/4:ℝ) ≤ 4/5)
    hc.continuousOn ⟨polynomial_signs.2.1, polynomial_signs.2.2⟩
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hg : Gamma (3/2:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  refine ⟨a, ⟨ha0, by linarith [ha.2]⟩, b, ⟨hb0, by linarith [hb.2]⟩, ?_, ?_, ?_⟩
  · linarith [ha.2, hb.1]
  · have hz := curvature_identity a ha0
    rw [hpa] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (Real.rpow_pos_of_pos ha0 _).ne' hg)
  · have hz := curvature_identity b hb0
    rw [hpb] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (Real.rpow_pos_of_pos hb0 _).ne' hg)

theorem result : ¬ D5.S0.Certificates.LiMorganSiegristInflectionRefutation.claim := by
  intro hc
  obtain ⟨ξ, hξ, hz, huniq, hsign⟩ := hc (3/2) (by norm_num) (by norm_num) forcing forcing_hypotheses
  obtain ⟨a, ha, b, hb, hne, hza, hzb⟩ := two_distinct_zeros
  exact hne ((huniq a ha hza).trans (huniq b hb hzb).symm)


end D5.S0.Certificates.LiMorganSiegristInflectionRefutation
