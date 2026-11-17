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

namespace Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM

universe u v

open MeasureTheory

namespace PairKernelEval

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
    R.readout () () (∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (b + t))) (if a = b then 1 / a else (Real.log a - Real.log b) / (a - b))

theorem source_equivalence :
    (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b),
      (∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (b + t))) = (if a = b then 1 / a else (Real.log a - Real.log b) / (a - b))) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% @pair_kernel_eval) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@pair_kernel_eval, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pair_kernel_eval) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.pair_kernel_eval.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.PairKernelEval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_equivalence
#print axioms audit

end PairKernelEval

namespace TraceCrossSpectral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {iota : Type u} {kappa : Type v} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (V : Matrix iota kappa ℂ) (UZ : Matrix iota iota ℂ) (UC : Matrix kappa kappa ℂ)
    (da : iota → ℂ) (db : kappa → ℂ),
    R.readout () () (V * (UC * Matrix.diagonal db * UCᴴ) * Vᴴ *
        (UZ * Matrix.diagonal da * UZᴴ)).trace (∑ i, ∑ j, da i * db j * Complex.normSq ((UZᴴ * V * UC) i j))

theorem source_equivalence :
    (∀ {iota : Type u} {kappa : Type v} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (V : Matrix iota kappa ℂ) (UZ : Matrix iota iota ℂ) (UC : Matrix kappa kappa ℂ)
    (da : iota → ℂ) (db : kappa → ℂ),
      (V * (UC * Matrix.diagonal db * UCᴴ) * Vᴴ *
        (UZ * Matrix.diagonal da * UZᴴ)).trace = (∑ i, ∑ j, da i * db j * Complex.normSq ((UZᴴ * V * UC) i j))) ↔ arena.{u, v}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  exact h (iota := ULift.{u} Unit) (kappa := ULift.{v} Unit) 0 0 0 (fun _ => 0) (fun _ => 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u, v} (type_of% @trace_cross_spectral) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@trace_cross_spectral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u, v}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_cross_spectral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.trace_cross_spectral.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM.TraceCrossSpectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
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

#print axioms source_equivalence
#print axioms audit

end TraceCrossSpectral

end Reg.D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
