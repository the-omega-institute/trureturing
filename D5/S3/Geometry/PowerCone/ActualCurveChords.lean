import D5.S3.Analytic.ConvexBarrier.ActualMinimizerCurve

/-!
Actual horizontal and vertical endpoints, all primal quadratic inputs, and
the precise residual dual input. The vertical lower chords need only the
primal Dikin theorem: their normalized first derivative is zero. The dual
supplier is needed here only for the two projected horizontal lower chords.
Zhang--Fu--Dai, arXiv:2611.06404v1, Lemma 3.2 and Theorem 3.5.
Source only, with no kernel/CI/novelty claim.
-/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier.Actual

theorem quadrant_frontier_subset : frontier quadrant ⊆ quadrantBoundary := by
  rw [quadrant_eq_interior,quadrantBoundary_eq_frontier]
  exact frontier_interior_subset

theorem powerCone_frontier_subset {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    frontier (coneInterior c : Set ScalarPoint) ⊆ coneBoundary c := by
  rw [coneInterior_eq_interior hc.le hc1.le,coneBoundary_eq_frontier hc.le hc1.le]
  exact frontier_interior_subset

theorem boundary_posScale {c λ : ℝ} (hλ : 0 < λ) {x : ScalarPoint}
    (hx : x ∈ coneBoundary c) : λ • x ∈ coneBoundary c := by
  have hw : weight c (λ*x.1.1) (λ*x.1.2) = λ*weight c x.1.1 x.1.2 := by
    unfold weight
    rw [Real.mul_rpow hλ.le hx.1.1,Real.mul_rpow hλ.le hx.1.2.1]
    calc
      _ = (λ^c*λ^(1-c))*(x.1.1^c*x.1.2^(1-c)) := by ring
      _ = _ := by rw [← Real.rpow_add hλ,show c+(1-c) = (1 : ℝ) by ring,Real.rpow_one]
  constructor
  · change 0 ≤ λ*x.1.1 ∧ 0 ≤ λ*x.1.2 ∧ ‖λ*x.2‖ ≤ _
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos hλ,hw]
    exact ⟨mul_nonneg hλ.le hx.1.1,mul_nonneg hλ.le hx.1.2.1,
      mul_le_mul_of_nonneg_left hx.1.2.2 hλ.le⟩
  · intro hi
    change 0 < λ*x.1.1 ∧ 0 < λ*x.1.2 ∧ ‖λ*x.2‖ < _ at hi
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos hλ,hw] at hi
    exact hx.2 ⟨(mul_pos_iff_of_pos_left hλ).mp hi.1,
      (mul_pos_iff_of_pos_left hλ).mp hi.2.1,(mul_lt_mul_left hλ).mp hi.2.2⟩

variable {c ν : ℝ} {F : ScalarPoint → ℝ}
variable (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)

theorem horizontal_endpoints (r : ℝ) :
    basePoint r-r • horizontalDirection = ((0 : ℝ),1) ∧
      basePoint r+(1-r) • horizontalDirection = ((1 : ℝ),0) := by
  constructor <;> ext <;> simp [basePoint,horizontalDirection] <;> ring

theorem horizontal_boundary (r : ℝ) :
    basePoint r-r • horizontalDirection ∈ quadrantBoundary ∧
      basePoint r+(1-r) • horizontalDirection ∈ quadrantBoundary := by
  rw [(horizontal_endpoints r).1,(horizontal_endpoints r).2]
  constructor <;> constructor
  · exact ⟨le_rfl,zero_le_one⟩
  · intro h; exact (lt_irrefl (0 : ℝ)) h.1
  · exact ⟨zero_le_one,le_rfl⟩
  · intro h; exact (lt_irrefl (0 : ℝ)) h.2

theorem horizontal_a {r : ℝ} (hr : r ∈ J) :
    a ν (partialMinimum hF) (basePoint r) horizontalDirection = p hF r := by
  unfold a
  rw [partialMinimum_first hF (basePoint_mem hr)]
  exact (section_first hF (graphPoint_mem hF hr) ex).symm

/-- The projected envelope's actual projective Hessian is the same qhat.
This uses F1's actual Schur derivative, rather than assuming an envelope jet. -/
theorem horizontal_Q {r : ℝ} (hr : r ∈ J) :
    Q ν (partialMinimum hF) (basePoint r) horizontalDirection = qhat hF r := by
  unfold Q b
  rw [← diagonal_two quadrant_isOpen (basePoint_mem hr),partialMinimum_schur hF
    (basePoint_mem hr),horizontal_a hF hr,qhat_schur hF hr]
  dsimp only [m,k]
  rw [section_second hF (graphPoint_mem hF hr) ex ex,
    section_second hF (graphPoint_mem hF hr) ex ez,
    section_second hF (graphPoint_mem hF hr) ez ez]
  have hraw := minimizer_fiber_hessian_pos hF (basePoint_mem hr)
  change (_ - _^2/_)/ν - _ = _/ν - _ - (_/ν)^2/(_/ν)
  field_simp [(parameter_pos hF).ne',hraw.ne'] <;> ring

/-- Both actual primal inputs on the full projected quadrant. -/
theorem horizontal_primal (hc : 0 < c) (hc1 : c < 1) {r : ℝ} (hr : r ∈ J) :
    (∀ λ : ℝ, 0 < λ →
      1 ≤ primalQuadratic ν (1+p hF r*r) (qhat hF r*r^2) λ) ∧
    (∀ λ : ℝ, 0 < λ →
      1 ≤ primalQuadratic ν (1-p hF r*(1-r)) (qhat hF r*(1-r)^2) λ) := by
  let hbar := IsLHSCB.partialMinimum hc hc1 hF
  have he := horizontal_endpoints r
  have houtm : ∀ λ : ℝ, 0 < λ → λ • (basePoint r-r • horizontalDirection) ∉ quadrant := by
    intro λ hλ hi
    rw [he.1] at hi
    have hh := hi.1
    norm_num at hh
  have houtp : ∀ λ : ℝ, 0 < λ → λ • (basePoint r+(1-r) • horizontalDirection) ∉ quadrant := by
    intro λ hλ hi
    rw [he.2] at hi
    have hh := hi.2
    norm_num at hh
  obtain ⟨hm,hp⟩ := hbar.primal_chord_exclusions quadrant_frontier_subset
    (basePoint_mem hr) r (1-r) houtm houtp
  constructor
  · intro λ hλ
    have hh := primal_polynomial hbar (basePoint_mem hr) horizontalDirection (-r) λ
    simp only [neg_smul,add_neg_eq_sub,horizontal_a hF hr,horizontal_Q hF hr,
      mul_neg,sub_neg_eq_add,neg_sq] at hh
    rw [← hh]
    exact hm λ hλ
  · intro λ hλ
    rw [← horizontal_a hF hr,← horizontal_Q hF hr,
      ← primal_polynomial hbar (basePoint_mem hr)]
    exact hp λ hλ

theorem width_eq_weight (c r : ℝ) : width c r = weight c r (1-r) := rfl

theorem vertical_lengths_pos {r : ℝ} (hr : r ∈ J) :
    0 < width c r+zeta hF r ∧ 0 < width c r-zeta hF r := by
  have hz : |zeta hF r| < width c r := by
    simpa only [sectionPoint,graphPoint,Real.norm_eq_abs,width,weight] using
      (graphPoint_mem hF hr).2.2
  obtain ⟨hm,hp⟩ := abs_lt.mp hz
  constructor <;> linarith

theorem vertical_endpoints {r : ℝ} (hr : r ∈ J) :
    sectionPoint (graphPoint hF r)-(width c r+zeta hF r) • vertical =
        (basePoint r,-weight c r (1-r)) ∧
    sectionPoint (graphPoint hF r)+(width c r-zeta hF r) • vertical =
        (basePoint r,weight c r (1-r)) := by
  constructor <;> ext <;> simp [sectionPoint,graphPoint,basePoint,vertical,width,weight] <;> ring

theorem vertical_boundary {r : ℝ} (hr : r ∈ J) :
    sectionPoint (graphPoint hF r)-(width c r+zeta hF r) • vertical ∈ coneBoundary c ∧
    sectionPoint (graphPoint hF r)+(width c r-zeta hF r) • vertical ∈ coneBoundary c := by
  rw [(vertical_endpoints hF hr).1,(vertical_endpoints hF hr).2]
  exact scalar_fiber_endpoints_boundary (basePoint_mem hr)

theorem vertical_a {r : ℝ} (hr : r ∈ J) :
    a ν F (sectionPoint (graphPoint hF r)) vertical = 0 := by
  exact (section_first hF (graphPoint_mem hF hr) ez).symm.trans (section_stationary hF hr)

theorem vertical_Q {r : ℝ} (hr : r ∈ J) :
    Q ν F (sectionPoint (graphPoint hF r)) vertical = k hF r := by
  exact (section_metric_Q hF (graphPoint_mem hF hr) ez).symm.trans (k_metric hF hr)

/-- Both vertical primal inputs from original F on its original domain. -/
theorem vertical_primal (hc : 0 < c) (hc1 : c < 1) {r : ℝ} (hr : r ∈ J) :
    (∀ λ : ℝ, 0 < λ →
      1 ≤ primalQuadratic ν 1 (k hF r*(width c r+zeta hF r)^2) λ) ∧
    (∀ λ : ℝ, 0 < λ →
      1 ≤ primalQuadratic ν 1 (k hF r*(width c r-zeta hF r)^2) λ) := by
  obtain ⟨hbm,hbp⟩ := vertical_boundary hF hr
  obtain ⟨hm,hp⟩ := hF.primal_chord_exclusions (powerCone_frontier_subset hc hc1)
    (graphPoint_mem hF hr) (width c r+zeta hF r) (width c r-zeta hF r)
    (fun λ hλ => (boundary_posScale hλ hbm).2)
    (fun λ hλ => (boundary_posScale hλ hbp).2)
  constructor
  · intro λ hλ
    have he := primal_polynomial hF (graphPoint_mem hF hr) vertical
      (-(width c r+zeta hF r)) λ
    simp only [vertical_a hF hr,vertical_Q hF hr,zero_mul,sub_zero,neg_sq,
      neg_smul,add_neg_eq_sub] at he
    rw [← he]
    exact hm λ hλ
  · intro λ hλ
    have he := primal_polynomial hF (graphPoint_mem hF hr) vertical
      (width c r-zeta hF r) λ
    simp only [vertical_a hF hr,vertical_Q hF hr,zero_mul,sub_zero] at he
    rw [← he]
    exact hp λ hλ

theorem primal_vertical_lower {ν s k δ : ℝ} (hs : 0 < s) (hν : ν = s^2+1)
    (hk : 0 < k) (hδ : 0 < δ)
    (hp : ∀ λ : ℝ, 0 < λ → 1 ≤ primalQuadratic ν 1 (k*δ^2) λ) :
    1/s ≤ δ*Real.sqrt k := by
  have hQ : 0 < k*δ^2 := mul_pos hk (sq_pos_of_pos hδ)
  have hd : 0 < 1+k*δ^2 := by linarith
  have he : primalQuadratic ν 1 (k*δ^2) (1/(1+k*δ^2)) =
      ν*(k*δ^2)/(1+k*δ^2) := by
    unfold primalQuadratic
    field_simp [hd.ne'] <;> ring
  have hh := hp (1/(1+k*δ^2)) (by positivity)
  rw [he,le_div_iff₀ hd,hν] at hh
  have hsq : (1 : ℝ)^2 ≤ (s*δ*Real.sqrt k)^2 := by
    have heq : (s*δ*Real.sqrt k)^2 = s^2*δ^2*k := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hk.le]; ring
    rw [heq]
    nlinarith [hh]
  have h1 := le_of_sq_le_sq hsq (show 0 ≤ s*δ*Real.sqrt k by positivity)
  apply (div_le_iff₀ hs).mpr
  nlinarith [h1]

/-- The vertical field of Curve is fully primal, with no dual premise. -/
theorem vertical_bounds (hc : 0 < c) (hc1 : c < 1) {s r : ℝ}
    (hr : r ∈ J) (hs : 0 < s) (hν : ν = s^2+1) :
    1/s ≤ (width c r+zeta hF r)*Real.sqrt (k hF r) ∧
    1/s ≤ (width c r-zeta hF r)*Real.sqrt (k hF r) := by
  obtain ⟨hm,hp⟩ := vertical_primal hF hc hc1 hr
  obtain ⟨hδm,hδp⟩ := vertical_lengths_pos hF hr
  exact ⟨primal_vertical_lower hs hν (k_pos hF hr) hδm hm,
    primal_vertical_lower hs hν (k_pos hF hr) hδp hp⟩

section DualInterface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact residual dual endpoint input. For y=x+delta*h this is strict
pairing <-DF(x),y>/nu>0 and the squared dual Dikin exclusion on the
supporting ray, in the two-dimensional restriction span{x,h}.
`Q` and `a` are the actual normalized Frechet derivatives of this F.
No curve, mixed bound, primal exclusion or parameter lower bound is a field.
The inverse Hessian here is that of the restricted two-dimensional barrier;
no equality with an ambient inverse Hessian is presumed. -/
structure DualEndpoint (ν : ℝ) (F : E → ℝ) (x h : E) (δ : ℝ) : Prop where
  strict_pairing : 0 < 1-a ν F x h*δ
  exclusion : ∀ λ : ℝ, 0 < λ →
    1 ≤ dualQuadratic ν (1-a ν F x h*δ) (Q ν F x h*δ^2) λ

end DualInterface

/-- The only missing dual families are the actual envelope endpoints
(0,1) and (1,0), at x=(r,1-r), h=(1,-1), delta=-r and 1-r.
This is intentionally a named theorem parameter awaiting the separate
dual-conjugacy implementation. It asserts no part of the curve calculus. -/
def HorizontalDualEndpoints : Prop := ∀ r ∈ J,
  DualEndpoint ν (partialMinimum hF) (basePoint r) horizontalDirection (-r) ∧
  DualEndpoint ν (partialMinimum hF) (basePoint r) horizontalDirection (1-r)

theorem horizontal_bounds (hc : 0 < c) (hc1 : c < 1)
    (hd : HorizontalDualEndpoints hF) {s r : ℝ} (hr : r ∈ J)
    (hs : 1 ≤ s) (hν : ν = s^2+1) :
    (1/s ≤ ellMinus (p hF r) (q hF r) r ∧ ellMinus (p hF r) (q hF r) r ≤ s) ∧
    (1/s ≤ ellPlus (p hF r) (q hF r) r ∧ ellPlus (p hF r) (q hF r) r ≤ s) := by
  obtain ⟨hpm,hpp⟩ := horizontal_primal hF hc hc1 hr
  obtain ⟨hdm,hdp⟩ := hd r hr
  have hs0 : 0 < s := by linarith
  have hq0 := qhat_pos hF hr
  have hr0 := hr.1
  have hr1 := sub_pos.mpr hr.2
  have hρ : ν-1 = s^2 := by rw [hν]; ring
  have hAm : 0 < 1+p hF r*r := by
    simpa only [horizontal_a hF hr,mul_neg,sub_neg_eq_add] using hdm.strict_pairing
  have hAp : 0 < 1-p hF r*(1-r) := by
    simpa only [horizontal_a hF hr] using hdp.strict_pairing
  have hdm' : ∀ λ : ℝ, 0 < λ →
      1 ≤ dualQuadratic ν (1+p hF r*r) (qhat hF r*r^2) λ := by
    simpa only [horizontal_a hF hr,horizontal_Q hF hr,mul_neg,sub_neg_eq_add,neg_sq]
      using hdm.exclusion
  have hdp' : ∀ λ : ℝ, 0 < λ →
      1 ≤ dualQuadratic ν (1-p hF r*(1-r)) (qhat hF r*(1-r)^2) λ := by
    simpa only [horizontal_a hF hr,horizontal_Q hF hr] using hdp.exclusion
  obtain ⟨hmp,hmd,_⟩ := dikin_quadratic_consequences (parameter_pos hF) hAm
    (mul_pos hq0 (sq_pos_of_pos hr0)) hpm hdm'
  obtain ⟨hpp',hpd,_⟩ := dikin_quadratic_consequences (parameter_pos hF) hAp
    (mul_pos hq0 (sq_pos_of_pos hr1)) hpp hdp'
  have hm := normalized_chord_bounds hAm (mul_pos hq0 (sq_pos_of_pos hr0)) hs0
    (by simpa only [hρ] using hmp)
    (by simpa only [hρ] using hmd)
  have hp := normalized_chord_bounds hAp (mul_pos hq0 (sq_pos_of_pos hr1)) hs0
    (by simpa only [hρ] using hpp')
    (by simpa only [hρ] using hpd)
  have hsm : Real.sqrt (qhat hF r*r^2) = q hF r*r := by
    rw [Real.sqrt_mul hq0.le,Real.sqrt_sq_eq_abs,abs_of_pos hr0]; rfl
  have hsp : Real.sqrt (qhat hF r*(1-r)^2) = q hF r*(1-r) := by
    rw [Real.sqrt_mul hq0.le,Real.sqrt_sq_eq_abs,abs_of_pos hr1]; rfl
  have hem : (1+p hF r*r)/Real.sqrt (qhat hF r*r^2) = ellMinus (p hF r) (q hF r) r := by
    rw [hsm]
    unfold ellMinus
    field_simp [hr0.ne',(q_pos hF hr).ne'] <;> ring
  have hep : (1-p hF r*(1-r))/Real.sqrt (qhat hF r*(1-r)^2) =
      ellPlus (p hF r) (q hF r) r := by
    rw [hsp]
    unfold ellPlus
    field_simp [hr1.ne',(q_pos hF hr).ne'] <;> ring
  rw [hem] at hm
  rw [hep] at hp
  exact ⟨hm,hp⟩

end D5.S3.Analytic.ConvexBarrier.Actual
