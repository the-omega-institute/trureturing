import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Metric.MetricACSpeed
/-! Source-bound whole-family audits for the metric speed and variation identity. -/

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal NNReal
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Original172
noncomputable section
universe u v
namespace Reg.D5.S3.Geometry.Metric.MetricACSpeed
namespace Metric
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ s => s) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ r t => r t + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
∀ {X : Type u} [MetricSpace X],
∀ {T : ℝ} (hT : 0 < T)
    (z : ℝ → X) (hz : AbsolutelyContinuousOnInterval z 0 T)
    (r : ℝ → ℝ) (hr0 : ∀ t, 0 ≤ r t)
    (hrm : AEStronglyMeasurable r (volume.restrict (Icc (0 : ℝ) T)))
    (hrlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (r t))),
    IntervalIntegrable r volume 0 T ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      deriv (variationOnFromTo z (Icc 0 T) 0) t = r t) ∧
    (∫⁻ t in Icc (0 : ℝ) T, ENNReal.ofReal (r t)) = eVariationOn z (Icc 0 T) ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      (∫ t in a..b, (R.readout () () r) t) = (eVariationOn z (Icc a b)).toReal) ∧
    (∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, a ≤ b →
      dist (z a) (z b) ≤ ∫ t in a..b, r t)

theorem bad_law : ¬ arena.{u}.Law bad := by
  intro h
  let z : ℝ → PUnit.{u+1} := fun _ => PUnit.unit
  have hz : AbsolutelyContinuousOnInterval z 0 1 :=
    (LipschitzWith.const PUnit.unit).lipschitzOnWith.absolutelyContinuousOnInterval
  have hr : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
        (𝓝[≠] (0 : ℝ)) (𝓝 ((fun _ : ℝ => 0) t)) := by
    exact Eventually.of_forall (fun t => by
      simpa only [z, dist_self, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
          (𝓝[≠] (0 : ℝ)) (𝓝 0)))
  have hs := h (T := 1) zero_lt_one z hz (fun _ => 0)
    (fun _ => le_rfl) aestronglyMeasurable_const hr
  have he := hs.2.2.2.1 0 (by simp) 1 (by simp) zero_le_one
  simp only [bad, realize, zero_add] at he
  have hv : eVariationOn z (Icc (0 : ℝ) 1) = 0 := by
    apply eVariationOn.constant_on
    intro a ha b hb
    exact Subsingleton.elim _ _
  rw [hv] at he
  norm_num at he

def evidence : Registration arena (type_of% (@Original172.metric_AC_speed_variation_bridge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨(@Original172.metric_AC_speed_variation_bridge), bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have h0 := congrFun h 0
    norm_num [actual, realize] at h0

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@Original172.metric_AC_speed_variation_bridge) (type_of% (realize signature (fun _ _ s => s) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Metric.MetricACSpeed.Metric.__information_unit,
  realizationName := `Reg.D5.S3.Geometry.Metric.MetricACSpeed.Metric.evidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ s => s) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Metric.MetricACSpeed,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "fn", "arg", "body", "fn"],
      stateBinder := 6,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }
#print axioms registration
end Metric

end Reg.D5.S3.Geometry.Metric.MetricACSpeed
