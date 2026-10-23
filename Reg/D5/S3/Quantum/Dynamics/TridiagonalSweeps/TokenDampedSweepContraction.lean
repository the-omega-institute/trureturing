import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction
open Matrix Filter Topology

namespace Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction
noncomputable section

abbrev sweepSignature : Signature where
  Params := Σ m : ℕ, Σ _v : Fin (m + 1) → ℝ, ℝ
  State := fun p => Fin p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => ℕ → (Fin p.1 → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def sweepActual : Realization sweepSignature := realize sweepSignature
  (fun _ p u k => (Malpha p.1 p.2.1 p.2.2 ^ k).mulVec u) (fun e => nomatch e)

def sweepRejected : Realization sweepSignature := realize sweepSignature
  (fun _ _ _ _ _ => 1) (fun e => nomatch e)

abbrev sweepArena : Arena where
  signature := sweepSignature
  Law R := ∀ (m : ℕ), 1 ≤ m → ∀ (v : Fin (m + 1) → ℝ),
    (∀ j, 0 < v j) → ∀ α : ℝ, 0 < α → α < 1 →
      (∀ μ ∈ spectrum ℂ ((Malpha m v α).map (algebraMap ℝ ℂ)), ‖μ‖ < 1) ∧
      (∀ u : Fin m → ℝ, Tendsto (R.readout () ⟨m, v, α⟩ u) atTop (nhds 0))

theorem sweepRejectedLaw : ¬ sweepArena.Law sweepRejected := by
  intro h
  have ht := (h 1 (by norm_num) (fun _ => 1) (by intro j; norm_num)
    (1 / 2) (by norm_num) (by norm_num)).2 0
  have he : (fun _ : Fin 1 => (1 : ℝ)) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds ht
  have hh := congrFun he 0
  norm_num at hh

def sweepRecord : Registration sweepArena claim where
  actual := sweepActual
  bridge := Iff.rfl
  variation := ⟨result, sweepRejected, sweepRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sweepRejected, ?_, rfl, sweepRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, (fun _ => 1), (1 / 2)⟩, 0, (fun _ => 1), ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [sweepActual, realize] at hh

noncomputable def result_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction.result)
    (type_of% (realize.{0,0,0,0,0} sweepSignature
      (fun _ p u k => (Malpha p.1 p.2.1 p.2.2 ^ k).mulVec u) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction.result.__information_unit,
  realizationName := `Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction.sweepRecord,
  realizationSource := none,
  generated := false,
  arena := .source ⟨sweepArena⟩,
  objectArena := .source ⟨sweepArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source sweepArena ⟨sweepRecord⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} sweepSignature
    (fun _ p u k => (Malpha p.1 p.2.1 p.2.2 ^ k).mulVec u) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction,
    definition := some { owner := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction, name := `D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction.claim, path := #[] },
    coordinates := #[0, 2, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "fn", "arg"],
      stateBinder := 7, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sweepRecord
end
end Reg.D5.S3.Quantum.Dynamics.TridiagonalSweeps.TokenDampedSweepContraction
