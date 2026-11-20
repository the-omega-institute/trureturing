import D5.S3.Quantum.Dynamics.WeldedColumnEvolution
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The normalized indicator matrix is observed from the column assignment. -/

namespace Reg.D5.S3.Quantum.Dynamics.WeldedColumnEvolution

open _root_.D5.S3.Quantum.Dynamics.WeldedColumnEvolution
open _root_.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap (centralDefect)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.LeanInformationAudit
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

private abbrev signature : Signature where
  Params := Type u × ℕ
  State p := p.1 → Column p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 (Column p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ col => normalizedColumns col) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (col : V → Column d)
    (_hsize : ∀ j, (Finset.univ.filter (fun v => col v = j)).card = 2 ^ columnDepth d j)
    (_hdegree : ∀ v j,
      ((G.neighborFinset v).filter (fun w => col w = j)).card = columnDegree d (col v) j)
    (t : ℝ),
    let Q := R.readout () (V, d) col
    let H := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • G.adjMatrix ℂ
    let J := (centralDefect (d + 1) (by omega)).map Complex.ofReal
    let U := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
    let P := NormedSpace.exp ((-Complex.I * (t : ℂ)) • J)
    Qᴴ * Q = 1 ∧ U * Q = Q * P ∧
      ∀ x y, col x = 0 → col y = Fin.last _ → U y x = P (Fin.last _) 0

private abbrev Sample := ULift.{u} (Fin 6)

private def sampleColumn (v : Sample.{u}) : Column 1 :=
  if v.down.val = 0 then 0 else if v.down.val ≤ 2 then 1 else if v.down.val ≤ 4 then 2 else 3

private def sampleGraph : SimpleGraph Sample.{u} :=
  SimpleGraph.fromRel fun v w => (sampleColumn v).val + 1 = (sampleColumn w).val

private instance : DecidableRel (sampleGraph.{u}).Adj := fun v w =>
  decidable_of_iff
    (v ≠ w ∧ ((sampleColumn v).val + 1 = (sampleColumn w).val ∨
      (sampleColumn w).val + 1 = (sampleColumn v).val))
    (SimpleGraph.fromRel_adj _ _ _).symm

private theorem sample_size :
    ∀ j, (Finset.univ.filter (fun v : Sample.{u} => sampleColumn v = j)).card =
      2 ^ columnDepth 1 j := by decide

private theorem sample_degree :
    ∀ (v : Sample.{u}) j,
      ((sampleGraph.neighborFinset v).filter (fun w => sampleColumn w = j)).card =
        columnDegree 1 (sampleColumn v) j := by decide

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := (h 1 sampleGraph sampleColumn sample_size sample_degree 0).1
  change (0 : Matrix Sample.{u} (Column 1) ℂ)ᴴ * 0 = 1 at hz
  simpa using congrArg (fun M : Matrix (Column 1) (Column 1) ℂ => M 0 0) hz

private def evidence : Registration arena.{u} (type_of% @central_defect_column_evolution.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨central_defect_column_evolution, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(Sample.{u}, 1), sampleColumn, (fun _ => 3), ?_⟩
    intro he
    have hv := congrArg (fun M : Matrix Sample.{u} (Column 1) ℂ => M (ULift.up 0) 0) he
    norm_num [actual, realize, normalizedColumns, sampleColumn, columnDepth] at hv

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@central_defect_column_evolution.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Dynamics.WeldedColumnEvolution.central_defect_column_evolution
  realizationName := `Reg.D5.S3.Quantum.Dynamics.WeldedColumnEvolution.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ col => normalizedColumns col) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.WeldedColumnEvolution
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Dynamics.WeldedColumnEvolution
