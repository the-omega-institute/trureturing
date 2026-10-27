import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import Reg.Support.DependentFamily

/-! Source-bound audit of the matrix entries of an identity amplification. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
open _root_.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev signature : Signature where
  Params := Σ _𝕜 : Type, Σ m : ℕ, Σ r : ℕ,
    Σ _a : Fin m × Fin r, Fin m × Fin r
  State p := Matrix (Fin p.2.1 × Fin p.2.2.1) (Fin p.2.1 × Fin p.2.2.1) p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p M =>
    M p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p M =>
    M p.2.2.2.2 p.2.2.2.1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {𝕜 : Type} [RCLike 𝕜] {n m : ℕ}
    (Phi : Matrix (Fin n) (Fin n) 𝕜 →ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜) (r : ℕ)
    (P : Matrix (Fin n × Fin r) (Fin n × Fin r) 𝕜) (a b : Fin m × Fin r),
    R.readout () ⟨𝕜, m, r, a, b⟩
      (MatrixMap.kron Phi (LinearMap.id : MatrixMap (Fin r) (Fin r) 𝕜) P) =
      Phi (fun i j => P (i, a.2) (j, b.2)) a.1 b.1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := @h ℂ inferInstance 2 2 LinearMap.id 1
    (Matrix.single (0, 0) (1, 0) 1) (0, 0) (1, 0)
  change MatrixMap.kron (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ)
    LinearMap.id (Matrix.single (0, 0) (1, 0) 1) (1, 0) (0, 0) = _ at hb
  rw [kron_id_apply] at hb
  norm_num [Matrix.single_apply, id] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨ℂ, 1, 1, (0, 0), (0, 0)⟩, 0, 1, ?_⟩
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

def source_registration : Registration arena (type_of% @kron_id_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kron_id_apply, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@kron_id_apply) (Realization signature) Unit Unit := {
  unitName := `IptPptSquaredEquivalence.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p M => M p.2.2.2.1 p.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
    definition := none
    coordinates := #[0, 3, 5, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
