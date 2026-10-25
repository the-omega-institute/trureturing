import CFMPActualDegenerateSegment281Transient
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace CFMPFiniteExceptionMonotone282Transient

/-- Continuity allows finitely many exceptional derivative points when
propagating a nonnegative derivative across a closed real interval. -/
theorem image_le_of_nonneg_derivative_off_finset
    (S : Finset ℝ) (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hD : ∀ x ∈ Ioo a b, x ∉ S →
      ∃ d : ℝ, HasDerivAt f d x ∧ 0 ≤ d) : f a ≤ f b := by
  classical
  induction S using Finset.induction_on generalizing a b with
  | empty =>
    have hmono : MonotoneOn f (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hf
      · intro x hx
        have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
        obtain ⟨d,hd,_⟩ := hD x hx' (by simp)
        exact hd.differentiableAt.differentiableWithinAt
      · intro x hx
        have hx' : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
        obtain ⟨d,hd,hn⟩ := hD x hx' (by simp)
        rwa [hd.deriv]
    exact hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  | @insert c S hc ih =>
    by_cases hca : c ≤ a
    · apply ih a b hab hf
      intro x hx hxs
      exact hD x hx (by
        simp only [Finset.mem_insert,not_or]
        exact ⟨ne_of_gt (hca.trans_lt hx.1),hxs⟩)
    by_cases hbc : b ≤ c
    · apply ih a b hab hf
      intro x hx hxs
      exact hD x hx (by
        simp only [Finset.mem_insert,not_or]
        exact ⟨ne_of_lt (hx.2.trans_le hbc),hxs⟩)
    have hac : a < c := lt_of_not_ge hca
    have hcb : c < b := lt_of_not_ge hbc
    have hleft : f a ≤ f c := by
      apply ih a c hac.le (hf.mono (Icc_subset_Icc le_rfl hcb.le))
      intro x hx hxs
      exact hD x ⟨hx.1,hx.2.trans hcb⟩ (by
        simp only [Finset.mem_insert,not_or]
        exact ⟨ne_of_lt hx.2,hxs⟩)
    have hright : f c ≤ f b := by
      apply ih c b hcb.le (hf.mono (Icc_subset_Icc hac.le le_rfl))
      intro x hx hxs
      exact hD x ⟨hac.trans hx.1,hx.2⟩ (by
        simp only [Finset.mem_insert,not_or]
        exact ⟨ne_of_gt hx.1,hxs⟩)
    exact hleft.trans hright

theorem monotoneOn_of_nonneg_derivative_off_finite
    (S : Set ℝ) (hS : S.Finite) (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hD : ∀ x ∈ Ioo a b, x ∉ S →
      ∃ d : ℝ, HasDerivAt f d x ∧ 0 ≤ d) : MonotoneOn f (Icc a b) := by
  classical
  intro x hx y hy hxy
  apply image_le_of_nonneg_derivative_off_finset hS.toFinset f x y hxy
    (hf.mono (Icc_subset_Icc hx.1 hy.2))
  intro z hz hzs
  apply hD z ⟨hx.1.trans_lt hz.1,hz.2.trans_le hy.2⟩
  simpa only [Set.Finite.mem_toFinset] using hzs

end CFMPFiniteExceptionMonotone282Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPFiniteExceptionMonotone282Transient.monotoneOn_of_nonneg_derivative_off_finite
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP282 finite-exception monotonicity absent: {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP282 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP282 CHECKED {name} axioms={axioms}"
