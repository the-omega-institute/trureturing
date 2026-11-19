import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing
import D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
import Reg.Support.SingleDependentReadout

noncomputable section
open Set Filter Topology LeanInformationAudit
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing
open _root_.D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f g : ℝ → ℕ → ℝ} {P Q α β cα cβ dα dβ : ℝ},
    0 < P → 0 < Q → α < β →
    0 < cα → 0 < cβ → 0 < dα → 0 < dβ →
    Tendsto (fun n => f α n * P ^ n) atTop (𝓝 cα) →
    Tendsto (fun n => f β n * P ^ n) atTop (𝓝 cβ) →
    Tendsto (fun n => g α n * Q ^ n) atTop (𝓝 dα) →
    Tendsto (fun n => g β n * Q ^ n) atTop (𝓝 dβ) →
    Real.log (cα / dα) < Real.log (cβ / dβ) →
    (∀ u v : ℝ, u < v → ∀ N : ℕ, ∃ i j : ℕ,
      N ≤ i ∧ N ≤ j ∧ u < (i : ℝ) * Real.log P - (j : ℝ) * Real.log Q ∧
      (i : ℝ) * Real.log P - (j : ℝ) * Real.log Q < v) →
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ContinuousOn (fun κ => f κ i - g κ j) (Icc α β)) →
    ∀ M : ℕ, ∃ κ ∈ Ioo α β, ∃ i j : ℕ,
      M ≤ i ∧ M ≤ j ∧ 1 ≤ i ∧ 1 ≤ j ∧ R.readout () () (f κ i) (g κ j)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ℝ → ℕ → ℝ := fun κ n => (κ + 2) / (2 : ℝ) ^ n
  let g : ℝ → ℕ → ℝ := fun _ n => 1 / (3 : ℝ) ^ n
  have hf (κ : ℝ) : Tendsto (fun n => f κ n * (2 : ℝ) ^ n) atTop (𝓝 (κ + 2)) := by
    convert tendsto_const_nhds using 1
    funext n
    dsimp [f]
    exact div_mul_cancel₀ _ (pow_ne_zero n (by norm_num))
  have hg (κ : ℝ) : Tendsto (fun n => g κ n * (3 : ℝ) ^ n) atTop (𝓝 1) := by
    convert tendsto_const_nhds using 1
    funext n
    dsimp [g]
    exact div_mul_cancel₀ _ (pow_ne_zero n (by norm_num))
  have hlog : Real.log ((0 + 2) / (1 : ℝ)) < Real.log ((1 + 2) / (1 : ℝ)) := by
    norm_num only [zero_add, one_div, div_one]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  obtain ⟨κ, hκ, i, j, hi, hj, hi1, hj1, heq⟩ :=
    h (f := f) (g := g) (P := 2) (Q := 3) (α := 0) (β := 1)
      (cα := 0 + 2) (cβ := 1 + 2) (dα := 1) (dβ := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hf 0) (hf 1) (hg 0) (hg 1) hlog
      (fun u v huv N => prime_log_lattice_tail (p := 2) (q := 3)
        (by norm_num) (by norm_num) (by norm_num) huv N)
      (by intro i j _ _; dsimp [f, g]; fun_prop) 0
  exact heq

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have hh := congrFun heq 0
  norm_num [actual, realize] at hh

def source_registration : Registration arena (type_of% @collision_of_scaled_limits) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@collision_of_scaled_limits, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@collision_of_scaled_limits) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing.collision_of_scaled_limits.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCrossing
