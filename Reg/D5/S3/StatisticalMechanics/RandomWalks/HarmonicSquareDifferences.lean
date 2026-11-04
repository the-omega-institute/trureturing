import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences
import Reg.Support.SingleDependentReadout

/-! The observed state and output are whole lattice functions in every dimension. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace Reg.D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun d => Lattice d → ℝ) (fun d => Lattice d → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- The original harmonic input remains in the premises and on the right.
Only the full function operand in the left-hand square is observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 0 < d → ∀ H : Lattice d → ℝ,
    Harmonic H → ∀ (k : ℕ) (x : Lattice d),
      ((laplacian d)^[k]) (square (R.readout () d H)) x =
        ((2 * (d : ℝ))⁻¹) ^ k *
          ∑ w : Word d k, (mixedDifference k w H x) ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : Harmonic (fun _ : Lattice 1 => (0 : ℝ)) := by
    change translationMean 1 0 = 0
    exact map_zero _
  have hh := h (d := 1) (by norm_num) (fun _ => 0) hzero 0 (fun _ => 0)
  norm_num [rejected, realize, square, mixedDifference] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h (fun _ => 0)
  norm_num [actual, realize] at hh

def evidence : Registration arena (type_of% (@harmonic_square_iterate)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨harmonic_square_iterate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- The selected operand is H in the left-hand `square H`; all six original
binders and the complete lattice function survive in the dependent arena. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@harmonic_square_iterate) (Realization signature) Unit Unit where
  unitName := `D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences.harmonic_square_iterate.__information_unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ H => H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.StatisticalMechanics.RandomWalks.HarmonicSquareDifferences
