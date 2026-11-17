import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiArithmeticBKM

noncomputable section
open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
open _root_.D5.S3.Divergence.LogDerivTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiArithmeticBKM

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef),
    R.readout () ()
      ((Hᴴ * logDeriv Z H).trace.re)
      (∫ u in (0 : ℝ)..1, Complex.re (inner ℂ
        (HilbertSchmidtOperatorSpace.ofOp
          ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))
        ((hsArithmeticMap Z u).inverse
          (HilbertSchmidtOperatorSpace.ofOp
            ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H)))))

theorem source_equivalence :
    (∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z H : Matrix ι ι ℂ) (hZ : Z.PosDef),
      (Hᴴ * logDeriv Z H).trace.re =
        ∫ u in (0 : ℝ)..1, Complex.re (inner ℂ
          (HilbertSchmidtOperatorSpace.ofOp
            ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))
          ((hsArithmeticMap Z u).inverse
            (HilbertSchmidtOperatorSpace.ofOp
              ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) H))))) ↔ arena.{u}.Law actual := by rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (ι := ULift.{u} Unit) 1 0 Matrix.PosDef.one

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% @arithmetic_inverse_pairing_eq_logDeriv) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@arithmetic_inverse_pairing_eq_logDeriv, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arithmetic_inverse_pairing_eq_logDeriv)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiArithmeticBKM.arithmetic_inverse_pairing_eq_logDeriv.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiArithmeticBKM.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms arithmetic_inverse_pairing_eq_logDeriv
#print axioms source_equivalence
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
