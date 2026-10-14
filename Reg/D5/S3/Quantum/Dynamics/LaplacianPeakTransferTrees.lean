import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
open _root_.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
open scoped Classical

@[reducible] def signature : Signature where
  Params := ℕ
  State n := SimpleGraph (Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := SimpleGraph (Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ T => T) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

/-- The complete claim, with the graph operand of IsTree as its sole readout. -/
@[reducible] def arena : Arena where
  signature := signature
  Law O := ∀ N : ℕ, ∃ n ≥ N, ∃ T : SimpleGraph (Fin n),
    (O.readout () n T).IsTree ∧
      (∀ m : ℕ, IsEmpty (T ≃g completeBipartiteGraph (Fin 1) (Fin m))) ∧
      ∃ u v, PeakTransfer T u v

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn, T, hT, _⟩ := h 2
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact SimpleGraph.not_connected_bot hT.connected

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, ⊥, ⊤, fun h => ?_⟩
  change (⊥ : SimpleGraph (Fin 2)) = ⊤ at h
  have h01 := congrArg (fun G : SimpleGraph (Fin 2) => G.Adj 0 1) h
  simp at h01

def registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.result)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ T => T) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.result
    "Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees/arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ T => T) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees,
    definition := some {
      owner := `D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees,
      name := `D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.claim, path := #[] },
    coordinates := #[1],
    readouts := #[{
      path := #["body", "arg", "body", "arg", "arg", "body", "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#check Reg.Support.DependentFamily.enrollment_1
#print axioms registration
#print axioms registration_1

namespace EigenDotZero
universe u_1
open Matrix

/-- Observe the vector operand in the orthogonality conclusion. -/
abbrev signature : Signature where
  Params := Type u_1
  State V := V → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := V → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u_1} :=
  realize signature (fun _ _ w => w) (fun e => nomatch e)

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

/-- All hypotheses retain their original operands; only the final vector is observed. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law O := ∀ {V : Type u_1} [Fintype V] [DecidableEq V] {A : Matrix V V ℝ}
    (hA : A.IsHermitian) (w : V → ℝ) (mu : ℝ)
    (_hw : A *ᵥ w = mu • w) (i : V) (_hi : hA.eigenvalues i ≠ mu),
      ⇑(hA.eigenvectorBasis i) ⬝ᵥ O.readout () V w = 0

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  let V := ULift.{u_1} (Fin 1)
  let hA : (0 : Matrix V V ℝ).IsHermitian := Matrix.isHermitian_zero
  let i : V := default
  have he := h hA 0 (hA.eigenvalues i + 1) (by simp) i (by linarith)
  have hz : (∑ j, hA.eigenvectorBasis i j) = 0 := by
    simpa only [rejected, realize, dotProduct, mul_one] using he
  have hn : (∑ j, hA.eigenvectorBasis i j ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have hs : (∑ j, hA.eigenvectorBasis i j) ^ 2 = ∑ j, hA.eigenvectorBasis i j ^ 2 := by
    simp only [Fintype.sum_unique]
  rw [← hs, hz] at hn
  norm_num at hn

theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro i
  refine ⟨ULift.{u_1} (Fin 1), 0, (fun _ => 1), ?_⟩
  intro h
  exact zero_ne_one (congrFun h (ULift.up 0))

def source_registration : Registration arena.{u_1} (type_of% (@eig_dot_zero.{u_1})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eig_dot_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@eig_dot_zero.{u_1}) (Realization signature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.EigenDotZero.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees.EigenDotZero.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end EigenDotZero
end
end Reg.D5.S3.Quantum.Dynamics.LaplacianPeakTransferTrees
