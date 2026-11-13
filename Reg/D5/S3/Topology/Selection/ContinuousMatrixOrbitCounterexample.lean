import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample

/-! The source family retains every positive dimension and the complete
counterexample telescope. Its observation is the actual second matrix field
on the literal inverse-natural real subspace. -/

namespace Reg.D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample

open _root_.D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => X) Mat

def actual : Realization signature :=
  realize signature (fun _ n x => Z2 n x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law obs := ∀ (n : ℕ) (_hn : 1 ≤ n),
    IsCompact literalSet ∧ Nonempty X ∧ CompactSpace X ∧ T2Space X ∧ ZeroDimensionalSpace X ∧
    Continuous (Z1 n) ∧ Continuous ((obs.readout () n)) ∧
    (Z1 n origin = 0 ∧ (obs.readout () n) origin = 0) ∧
    (∀ k : ℕ, Z1 n (point k) = (radius k : ℂ) • (1 : Mat n) ∧
      (obs.readout () n) (point k) = ((-1 : ℂ) ^ (k + 1) * (radius k : ℂ)) • (1 : Mat n)) ∧
    (∀ k : ℕ, ∀ hk : 1 ≤ k,
      Z1 n (positivePoint k hk) = (1 / (k : ℂ)) • (1 : Mat n) ∧
      (obs.readout () n) (positivePoint k hk) = ((-1 : ℂ) ^ k / (k : ℂ)) • (1 : Mat n)) ∧
    (∀ N, IsClopen (finiteHead N) ∧ Continuous (approximant n N) ∧
      (∀ x, (approximant n N x).conjTranspose * approximant n N x = 1 ∧
        approximant n N x * (approximant n N x).conjTranspose = 1) ∧
      ∀ x, ‖(obs.readout () n) x - approximant n N x * Z1 n x‖ ≤ 2 / (N + 1 : ℝ)) ∧
    (∀ x, (Z1 n x).conjTranspose * Z1 n x = ((obs.readout () n) x).conjTranspose * (obs.readout () n) x) ∧
    (∀ x, 0 ≤ Z1 n x ∧ CFC.abs ((obs.readout () n) x) = Z1 n x) ∧
    (¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, (obs.readout () n) x = U x * CFC.abs ((obs.readout () n) x)) ∧
    ¬ ∃ U : X → Mat n, Continuous U ∧ ∀ x, (obs.readout () n) x = U x * Z1 n x

private theorem actual_law : arena.Law actual := proposition10_3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hno := h 1 (by omega)
  rcases hno with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hlast⟩
  apply hlast
  refine ⟨fun _ => 0, continuous_const, fun x => ?_⟩
  simp [rejected, realize]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, origin, point 0, ?_⟩
  change Z2 1 origin ≠ Z2 1 (point 0)
  have h := proposition10_3 1 (by omega)
  rcases h with ⟨_, _, _, _, _, _, _, ho, hp, _⟩
  rw [ho.2, (hp 0).2]
  intro heq
  have hv := congrArg (fun M : Mat 1 => M 0 0) heq
  norm_num [radius] at hv

def source_registration : Registration arena (type_of% @proposition10_3) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@proposition10_3) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample.proposition10_3.audit
  realizationName := `Reg.D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => Z2 n x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Topology.Selection.ContinuousMatrixOrbitCounterexample
