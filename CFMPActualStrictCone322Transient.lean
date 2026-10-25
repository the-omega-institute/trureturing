import CFMPActualPrescribedCone295Transient
import CFMPOriginalStrictInverse310Transient

noncomputable section
universe u322 v322
set_option autoImplicit false
open Set
open scoped BigOperators ContDiff
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (Incidence star)
open CFMPOriginalCovolumeNeighborhood251Transient (Lengths RealizationFamily physicalCovolume)
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPGlobalGenuineCovolume256Transient (realizedFamily)
open CFMPActualZeroAngle288Transient (extendedDifferential)
open CFMPActualPrescribedCone295Transient
open CFMPOriginalStrictInverse310Transient (original_strict_angle_inverse)

namespace CFMPActualStrictCone322Transient

/-- Strict original local angle data supply the genuine local metrics used
by the physically calibrated variational construction. The resulting common
positive generalized lengths may still contain flat tetrahedra. -/
theorem exists_actual_positive_strict_cone
    {T : Type u322} {E : Type v322}
    [Fintype T] [Fintype E] [DecidableEq E]
    (s : Incidence T E)
    (hobs : ∀ e : E, ∃ t : T, ∃ q : Fin 6, s.edge t q = e)
    (α : T → Fin 6 → ℝ) (hα : ∀ t q, 0 < α t q)
    (hv0 : ∀ t, α t 0 + α t 1 + α t 2 < Real.pi)
    (hv1 : ∀ t, α t 0 + α t 5 + α t 4 < Real.pi)
    (hv2 : ∀ t, α t 1 + α t 5 + α t 3 < Real.pi)
    (hv3 : ∀ t, α t 2 + α t 4 + α t 3 < Real.pi)
    (k : E → ℝ)
    (hbudget : ∀ e, (∑ o ∈ star s e, α o.1 o.2) = k e) :
    ∃ F : Lengths → ℝ, ContDiff ℝ 1 F ∧ ConvexOn ℝ Set.univ F ∧
      (∀ b, HasFDerivAt F (extendedDifferential b) b) ∧
      (∀ G : RealizationFamily, realizedFamily G →
        Set.EqOn F (physicalCovolume G) {a | genuine a}) ∧
      ∃ p : E → ℝ, (∀ e : E, 0 < p e) ∧
        ∀ e : E, signedCone s p e = k e := by
  classical
  have hlocal : ∀ t : T, ∃ l : Lengths, genuine l ∧
      ∀ q, CFMPOriginalSixPairedAngles435Transient.sourceAngle l q = α t q := by
    intro t
    exact original_strict_angle_inverse (α t) (hα t) (hv0 t) (hv1 t) (hv2 t) (hv3 t)
  choose A hA hmatch using hlocal
  have htarget : ∀ e, realizedConeTarget s A e = k e := by
    intro e
    calc
      realizedConeTarget s A e = ∑ o ∈ star s e, α o.1 o.2 := by
        unfold realizedConeTarget
        apply Finset.sum_congr rfl
        intro o _
        change CFMPOriginalSixPairedAngles435Transient.sourceAngle (A o.1) o.2 = α o.1 o.2
        exact hmatch o.1 o.2
      _ = k e := hbudget e
  obtain ⟨F, hC, hconv, hder, hphysical, p, hp, hcone⟩ :=
    exists_actual_positive_realized_cone
      (CFMPRegularJacobian110Transient.regularPoint 1)
      (CFMPRegularJacobian110Transient.regular_genuine 1 (by norm_num))
      s hobs A hA
  exact ⟨F, hC, hconv, hder, hphysical, p, hp, fun e => (hcone e).trans (htarget e)⟩

end CFMPActualStrictCone322Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPActualStrictCone322Transient.exists_actual_positive_strict_cone
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP322 actual strict prescribed-cone theorem absent"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP322 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP322 CHECKED {name} axioms={axioms}"
