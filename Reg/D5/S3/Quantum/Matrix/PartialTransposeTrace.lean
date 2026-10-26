-- UNCOMPILED source-only candidate; no registration verdict is asserted.
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Matrix.PartialTransposeTrace

namespace Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace.TraceDuality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open LeanInformationAudit _root_.Matrix
noncomputable section

/-- Types are genuine coordinates in Type 1; no Fintype dictionary is a coordinate. -/
abbrev signature : Signature.{1,0,0,0,0} where
  Params := Σ _A : Type, Type
  State p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2) (p.1 × p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => partialTranspose M) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
/-- Retain both original finite dictionaries and the entire trace equality. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B]
    (M : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ),
    _root_.dotProduct (star v) (_root_.Matrix.mulVec (O.readout () ⟨A,B⟩ M) v) =
      (M * partialTranspose (_root_.Matrix.vecMulVec v (star v))).trace
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (A := Fin 1) (B := Fin 1) (fun _ _ => 1) (fun _ => 1)
  change
    (Finset.univ.sum fun _i : Fin 1 × Fin 1 => star (1 : ℂ) *
      (Finset.univ.sum fun _j : Fin 1 × Fin 1 => (0 : ℂ) * (1 : ℂ))) =
    (Finset.univ.sum fun _i : Fin 1 × Fin 1 =>
      Finset.univ.sum fun _j : Fin 1 × Fin 1 =>
        (1 : ℂ) * ((1 : ℂ) * star (1 : ℂ))) at he
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ] at he
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Fin 1,Fin 1⟩, 0, (fun _ _ => 1), ?_⟩
  intro heq
  have he := congrFun (congrFun heq (0,0)) (0,0)
  norm_num [actual, realize, partialTranspose,
    _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose] at he
/-- The one-role/no-anchor argument at the actual higher-universe signature. -/
private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality, rejected, rejected_law⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

/-- Source-only candidate: compilation and compiled source-binding evidence are pending. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.PartialTransposeTrace.partial_transpose_trace_duality) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace.TraceDuality.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace.TraceDuality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => partialTranspose M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.PartialTransposeTrace
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.PartialTransposeTrace.TraceDuality
