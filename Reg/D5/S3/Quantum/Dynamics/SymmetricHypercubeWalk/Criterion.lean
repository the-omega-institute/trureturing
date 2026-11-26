import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion
import Reg.Support.SingleDependentReadout

/-! The gap sequence in the common-limit criterion, with the collision clause fixed. -/

noncomputable section

namespace Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open HypercubeWalsh LeanInformationAudit Filter MeasureTheory Finset
open scoped Topology

abbrev Weights := ℕ → ℕ → ℝ
abbrev Parameters := Σ _ : Weights, ℕ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p d => delta d (rho d (p.1 d)) p.2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : Weights) (hw : ∀ d h, h ≤ d → 0 ≤ w d h)
      (ht : ∀ d, ∑ h ∈ range (d + 1), w d h = 1),
    (∃ π : ProbabilityMeasure HypercubeWeakLimit.UnitInterval,
      Tendsto (fun d => HypercubeExchangeable.radialLaw (continuousShellLaw w hw ht d))
        atTop (𝓝 π) ∧
      Tendsto (fun d => HypercubeExchangeable.radialLaw (discreteShellLaw w hw ht d))
        atTop (𝓝 π)) ↔
    (∀ k : ℕ, 0 < k → Tendsto (fun d => R.readout () ⟨w, k⟩ d) atTop (𝓝 0)) ∧
    (∀ k : ℕ, 0 < k → ∃ m : ℝ, Tendsto (fun d => collisions d (rho d (w d)) k) atTop (𝓝 m))

private def zeroWeights : Weights := fun _ h => if h = 0 then 1 else 0

private theorem zeroWeights_nonneg (d h : ℕ) (_ : h ≤ d) : 0 ≤ zeroWeights d h := by
  unfold zeroWeights
  split_ifs <;> norm_num

private theorem zeroWeights_total (d : ℕ) : ∑ h ∈ range (d + 1), zeroWeights d h = 1 := by
  simp [zeroWeights]

private theorem rho_zeroWeights (d k : ℕ) : rho d (zeroWeights d) k = 1 := by
  classical
  unfold rho
  rw [sum_eq_single 0]
  · simp [zeroWeights, krawtchouk]
  · intro h _ hh
    simp [zeroWeights, hh]
  · simp

private theorem common_zeroWeights :
    ∃ π : ProbabilityMeasure HypercubeWeakLimit.UnitInterval,
      Tendsto (fun d => HypercubeExchangeable.radialLaw
        (continuousShellLaw zeroWeights zeroWeights_nonneg zeroWeights_total d)) atTop (𝓝 π) ∧
      Tendsto (fun d => HypercubeExchangeable.radialLaw
        (discreteShellLaw zeroWeights zeroWeights_nonneg zeroWeights_total d)) atTop (𝓝 π) := by
  apply (exists_common_shell_weakLimit_iff zeroWeights zeroWeights_nonneg zeroWeights_total).2
  constructor
  · intro k _
    have hz (d : ℕ) : delta d (rho d (zeroWeights d)) k = 0 := by
      simp [delta, shellPairSum, shellGap, rho_zeroWeights]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · intro k _
    refine ⟨1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop k] with d hd
    have hsum : d - k + k = d := Nat.sub_add_cancel hd
    have hchoose (n : ℕ) : (∑ i ∈ range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    simp [collisions, shellPairSum, rho_zeroWeights, ← mul_sum, ← sum_mul,
      hchoose, ← pow_add, hsum]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlimit : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
    ((h zeroWeights zeroWeights_nonneg zeroWeights_total).1 common_zeroWeights).1 1 (by decide)
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hlimit
  norm_num at he

private def changingWeights : Weights :=
  fun d h => if d = 2 then (d.choose h : ℝ) / (2 : ℝ) ^ d else zeroWeights d h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨changingWeights, 1⟩, 1, 2, ?_⟩
  change delta 1 (rho 1 (changingWeights 1)) 1 ≠ delta 2 (rho 2 (changingWeights 2)) 1
  have hfirst : changingWeights 1 = zeroWeights 1 := by funext h; norm_num [changingWeights]
  rw [hfirst]
  simp only [delta, shellPairSum, shellGap, rho_zeroWeights, abs_one, lt_self_iff_false,
    and_false, ite_false, mul_zero, sum_const_zero]
  norm_num [changingWeights, rho, krawtchouk, sum_range_succ, Nat.choose]

def evidence : Registration arena (type_of% @exists_common_shell_weakLimit_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_common_shell_weakLimit_iff, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_common_shell_weakLimit_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion.unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "body", "body",
        "fn", "fn", "arg", "body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.Criterion
