import CFMPActualTiltedCoercivity293Transient
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
universe u294 v294
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (Incidence)
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths)
open CFMPActualGlobalEnergy259Transient (localRead)
open CFMPConvexCoercivity292Transient

namespace CFMPActualIncidenceCoercivity294Transient

/-- The local positive radial slope extends to a global affine lower bound;
the attained minimum controls the interior of the sphere. -/
theorem sphere_gap_global_linear (f : Lengths → ℝ) (hc : Continuous f)
    (hconv : ConvexOn ℝ Set.univ f) (a : Lengths) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ x ∈ Metric.sphere a r, f a < f x) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ x : Lengths, c*‖x‖-C ≤ f x := by
  obtain ⟨c,hcpos,hbound⟩ := convex_sphere_gap_linear f hc hconv a r hr hgap
  obtain ⟨m,hm⟩ := (convex_sphere_gap_coercive_minimum f hc hconv a r hr hgap).2
  refine ⟨c,hcpos,c*(‖a‖+r)-f m,?_⟩
  intro x
  have hnorm : ‖x‖ ≤ ‖x-a‖+‖a‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-a) a
  by_cases hx : r ≤ ‖x-a‖
  · have hfx := hbound x hx
    have hfa := hm a
    have hcr : 0 ≤ c*r := mul_nonneg hcpos.le hr.le
    have hmul := mul_le_mul_of_nonneg_left hnorm hcpos.le
    nlinarith
  · have hfx := hm x
    have hlt : ‖x-a‖ < r := lt_of_not_ge hx
    have hsmall := mul_le_mul_of_nonneg_left hlt.le hcpos.le
    have hmul := mul_le_mul_of_nonneg_left hnorm hcpos.le
    nlinarith

variable {T : Type u294} {E : Type v294}
  [Fintype T] [Fintype E] [DecidableEq E]

/-- Every observed global coordinate is bounded by one original local read.
The sum counts tetrahedra and retains repeated occurrence labels. -/
theorem incidence_norm_le_sum (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e) (p : E → ℝ) :
    ‖p‖ ≤ ∑ t : T, ‖localRead s t p‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
  intro e
  obtain ⟨t,q,hq⟩ := hobs e
  have hcoord : ‖p e‖ ≤ ‖localRead s t p‖ := by
    simpa only [localRead,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,hq]
      using norm_le_pi_norm (localRead s t p) q
  exact hcoord.trans (Finset.single_le_sum (fun t _ => norm_nonneg (localRead s t p))
    (Finset.mem_univ t))

/-- A common positive coefficient can be chosen without assuming T nonempty.
The reciprocal-sum choice is also valid when T is empty. -/
private theorem common_positive_coefficient (c : T → ℝ) (hc : ∀ t, 0 < c t) :
    ∃ d : ℝ, 0 < d ∧ ∀ t, d ≤ c t := by
  classical
  let S : ℝ := 1+∑ t : T, (c t)⁻¹
  have hS : 0 < S := by
    have hsum : 0 ≤ ∑ t : T, (c t)⁻¹ :=
      Finset.sum_nonneg (fun t _ => (inv_pos.mpr (hc t)).le)
    dsimp [S]
    linarith
  refine ⟨S⁻¹,inv_pos.mpr hS,?_⟩
  intro t
  have hinv : (c t)⁻¹ ≤ S := by
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset T)) => (inv_pos.mpr (hc j)).le)
      (Finset.mem_univ t)
    dsimp [S]
    linarith
  simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hc t)) hinv

/-- Local affine norm lower bounds combine through the actual incidence
when every global coordinate occurs. No compatibility of local minimizers
or injectivity of the occurrence labels is assumed. -/
theorem finite_incidence_linear_growth (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (f : T → Lengths → ℝ)
    (hgrow : ∀ t : T, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ,
      ∀ v : Lengths, c*‖v‖-C ≤ f t v) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ p : E → ℝ,
      c*‖p‖-C ≤ ∑ t : T, f t (localRead s t p) := by
  classical
  choose c hc C hlocal using hgrow
  obtain ⟨d,hd,hdc⟩ := common_positive_coefficient c hc
  refine ⟨d,hd,∑ t : T, C t,?_⟩
  intro p
  have hsum : (∑ t : T, (d*‖localRead s t p‖-C t)) ≤
      ∑ t : T, f t (localRead s t p) := by
    apply Finset.sum_le_sum
    intro t _
    have hsmall := mul_le_mul_of_nonneg_right (hdc t) (norm_nonneg (localRead s t p))
    exact (sub_le_sub_right hsmall (C t)).trans (hlocal t (localRead s t p))
  calc
    d*‖p‖-(∑ t : T, C t) ≤ d*(∑ t : T, ‖localRead s t p‖)-(∑ t : T, C t) :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left (incidence_norm_le_sum s hobs p) hd.le) _
    _ = ∑ t : T, (d*‖localRead s t p‖-C t) := by
      rw [Finset.sum_sub_distrib,Finset.mul_sum]
    _ ≤ _ := hsum

/-- A finite actual incidence sum of locally growing continuous terms is
coercive and attains a minimum. Empty T and E remain in scope. -/
theorem finite_incidence_coercive_minimum (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (f : T → Lengths → ℝ) (hc : ∀ t, Continuous (f t))
    (hgrow : ∀ t : T, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ,
      ∀ v : Lengths, c*‖v‖-C ≤ f t v) :
    Tendsto (fun p : E → ℝ => ∑ t : T, f t (localRead s t p))
      (cocompact (E → ℝ)) atTop ∧
    ∃ p : E → ℝ, ∀ q : E → ℝ,
      (∑ t : T, f t (localRead s t p)) ≤ ∑ t : T, f t (localRead s t q) := by
  classical
  obtain ⟨c,hcpos,C,hbound⟩ := finite_incidence_linear_growth s hobs f hgrow
  have hlim : Tendsto (fun p : E → ℝ => ∑ t : T, f t (localRead s t p))
      (cocompact (E → ℝ)) atTop := by
    apply tendsto_atTop.2
    intro B
    have he : ∀ᶠ p : E → ℝ in cocompact (E → ℝ), (B+C)/c ≤ ‖p‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [he] with p hp
    have hmul := (div_le_iff₀ hcpos).1 hp
    have hB : B ≤ c*‖p‖-C := by nlinarith
    exact hB.trans (hbound p)
  have hcont : Continuous (fun p : E → ℝ => ∑ t : T, f t (localRead s t p)) := by
    apply continuous_finsetSum
    intro t _
    exact (hc t).comp (localRead s t).continuous
  exact ⟨hlim,hcont.exists_forall_le hlim⟩

end CFMPActualIncidenceCoercivity294Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualIncidenceCoercivity294Transient.sphere_gap_global_linear,
      ``CFMPActualIncidenceCoercivity294Transient.incidence_norm_le_sum,
      ``CFMPActualIncidenceCoercivity294Transient.finite_incidence_linear_growth,
      ``CFMPActualIncidenceCoercivity294Transient.finite_incidence_coercive_minimum] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP294 actual finite incidence growth absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP294 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP294 CHECKED {name} axioms={axioms}"
