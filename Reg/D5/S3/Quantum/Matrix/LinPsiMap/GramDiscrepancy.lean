import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy
import Reg.Support.SingleDependentReadout

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Matrix.LinGProperty
open _root_.D5.S3.Quantum.Matrix.LinPsiMap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy
namespace Bound
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (A X B : Matrix (Fin n) (Fin n) ℂ)
    (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hdisc : ((δ : ℂ) • 1 - (A + B - X - Xᴴ)).PosSemidef)
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (j : Fin (Fintype.card (Fin n))),
    R.readout () () (2 * singularValuesSorted X j)
      ((hAp.1.add hBp.1).eigenvalues₀ j + δ / 2)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact @h 1 0 0 0 (by simpa using (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ).PosSemidef))
    0 (by norm_num) (by simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero ⟨0, by simp⟩
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh
def family : Registration arena (type_of% @gram_discrepancy_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gram_discrepancy_bound, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gram_discrepancy_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.LinPsiMap.gram_discrepancy_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy.Bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bound
end Reg.D5.S3.Quantum.Matrix.LinPsiMap.GramDiscrepancy
