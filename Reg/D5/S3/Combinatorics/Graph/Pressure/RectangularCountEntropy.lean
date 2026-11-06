import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy
import Reg.Support.DependentFamily

/-! The complete rectangular telescope, observing its source function. -/

open LeanInformationAudit Set Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Topology

namespace Reg.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ f => f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ r c => -((r : ℝ) * c)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (f : ℕ → ℕ → ℝ) (L : ℝ), 0 ≤ L →
    (∀ r c, f r c = f c r) →
    (∀ c, Subadditive (fun r => f r c)) →
    (∀ r c, 0 ≤ f r c ∧ f r c ≤ (r : ℝ) * c * L) →
    ∃ s : ℝ, 0 ≤ s ∧
      Tendsto (fun n : ℕ => r.readout () () f n n / (n : ℝ) ^ 2) atTop (𝓝 s)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, hs, ht⟩ := h (fun _ _ => 0) 0 (by norm_num)
    (by intros; rfl) (by intro c a b; simp) (by intros; simp)
  change Tendsto (fun n : ℕ => -((n : ℝ) * n) / (n : ℝ) ^ 2) atTop (𝓝 s) at ht
  have hb : Tendsto (fun n : ℕ => -((n : ℝ) * n) / (n : ℝ) ^ 2)
      atTop (𝓝 (-1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hn0]
    <;> ring
  have heq : s = -1 := tendsto_nhds_unique ht hb
  norm_num [heq] at hs

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun (r c : ℕ) => (r : ℝ) * c), ?_⟩
  change (fun (_ _ : ℕ) => (0 : ℝ)) ≠ (fun (r c : ℕ) => (r : ℝ) * c)
  intro h
  have h0 := congrFun (congrFun h 1) 1
  norm_num at h0

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy.square_log_limit)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy.square_log_limit,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy.square_log_limit)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy.square_log_limit.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg",
        "fn", "fn", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Pressure.RectangularCountEntropy
