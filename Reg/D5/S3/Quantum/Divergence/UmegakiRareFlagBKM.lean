import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM

noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM

universe u v

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f L => Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {iota : Type u} {kappa : Type v} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ) (V : Matrix iota kappa ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef),
    R.readout () ()
      (fun delta : ℝ =>
          (Matrix.trace
            ((Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
                (0 : Matrix kappa kappa ℂ)).conjTranspose *
              D5.S3.Divergence.LogDerivTrace.logDeriv
                (Matrix.fromBlocks Z 0 0 (delta • C))
                (Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
                  (0 : Matrix kappa kappa ℂ)))).re /
            (2 * Real.log (1 / delta)))
      ((Matrix.trace (Vᴴ * Z⁻¹ * V)).re)

theorem source_equivalence :
    (∀ {iota : Type u} {kappa : Type v} [Fintype iota] [DecidableEq iota]
      [Fintype kappa] [DecidableEq kappa]
      (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ) (V : Matrix iota kappa ℂ)
      (hZ : Z.PosDef) (hC : C.PosDef),
      Filter.Tendsto
        (fun delta : ℝ =>
          (Matrix.trace
            ((Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
                (0 : Matrix kappa kappa ℂ)).conjTranspose *
              D5.S3.Divergence.LogDerivTrace.logDeriv
                (Matrix.fromBlocks Z 0 0 (delta • C))
                (Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
                  (0 : Matrix kappa kappa ℂ)))).re /
            (2 * Real.log (1 / delta)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Matrix.trace (Vᴴ * Z⁻¹ * V)).re))) ↔ arena.{u, v}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hh := h (iota := ULift.{u} Unit) (kappa := ULift.{v} Unit)
    (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
    (1 : Matrix (ULift.{v} Unit) (ULift.{v} Unit) ℂ)
    0 (Matrix.PosDef.one) (Matrix.PosDef.one)
  exact hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hh := congrFun he 0
  have hz : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds
  have hnot : ¬ Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro ho
    have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ho
    norm_num at h01
  have hz' : actual.readout i () (fun _ => 0) 0 := by
    simpa [actual, realize] using hz
  apply hnot
  have ho' := hh ▸ hz'
  simpa [actual, realize] using ho'

def family : Registration arena.{u, v} (type_of% @rare_flag_logDeriv_limit) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@rare_flag_logDeriv_limit, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u, v}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rare_flag_logDeriv_limit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.rare_flag_logDeriv_limit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f L => Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
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

#print axioms rare_flag_logDeriv_limit
#print axioms source_equivalence
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
