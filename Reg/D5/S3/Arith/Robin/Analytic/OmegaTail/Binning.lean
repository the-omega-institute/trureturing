import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.OmegaTail.Binning
import Reg.Support.SingleDependentReadout

/-! Exact dependent family for finite entropy-preserving interval bins. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set MeasureTheory Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail.Binning

namespace Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Binning

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ m n => m < n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {g : ℝ → ℝ} {A B eta : ℝ}, 0 < A → A < B →
    ContinuousOn g (Icc A B) → (∀ u ∈ Icc A B, g u ∈ Ioo (0 : ℝ) 1) → 0 < eta →
    ∃ n : ℕ, R.readout () () 0 n ∧ ∃ a b r : Fin n → ℝ,
      (∀ j, 0 < a j ∧ a j < b j ∧ 0 < r j ∧ r j < b j - a j) ∧
      (Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) ∧
      (∑ j, r j) = (∫ u in Ioc A B, g u) ∧
      (∫ u in Ioc A B, binEntropy (g u)) ≤
        (∑ j, (b j - a j) * binEntropy (r j / (b j - a j))) ∧
      (∑ j, r j * log (b j)) ≤ (∫ u in Ioc A B, g u * log u) +
        eta * ∫ u in Ioc A B, g u

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, _⟩ := h (g := fun _ : ℝ => (1 / 2 : ℝ)) (A := 1) (B := 2)
    (eta := 1) (by norm_num) (by norm_num) continuousOn_const
    (by intro u hu; norm_num) (by norm_num)
  exact hn

def family : Registration arena (type_of% @compact_bins) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compact_bins, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), 1, ?_⟩
    intro he
    have hh : (1 : ℕ) < 1 := Eq.mp (congrFun he 1) (by norm_num : (0 : ℕ) < 1)
    exact (lt_irrefl 1) hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@compact_bins) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.OmegaTail.Binning.compact_bins.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Binning.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.OmegaTail.Binning
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Robin.Analytic.OmegaTail.Binning
