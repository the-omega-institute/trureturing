import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.UmegakiKernelContraction

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open _root_.D5.S3.Quantum.Divergence.UmegakiKernelContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction

universe u

abbrev Q := ULift.{u} Unit

def identityChannel : QuantumChannel Q.{u} Q.{u} where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (StarAlgEquiv.refl ℂ (CStarMatrix Q Q ℂ))
  trace_preserving _ := rfl

theorem identity_endpoint : EndpointBound identityChannel.{u} 1 := by
  intro R _ _ Z V _ _
  have h (W : Matrix (R × Q) (R × Q) ℂ) : amp identityChannel W = W := by
    ext ⟨r,i⟩ ⟨s,j⟩
    rw [amp_entry]
    rfl
  rw [h Z, h V, one_mul]

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Nonempty a] [Nonempty b] {R : Type u} [Fintype R] [DecidableEq R]
      (N : QuantumChannel a b) (c : ℝ) (hN : (act N 1).PosDef)
      (hc : c ∈ Set.Icc (0 : ℝ) 1) (hEnd : EndpointBound N c)
      (Z V : Matrix (R × a) (R × a) ℂ) (t : ℝ) (hZ : Z.PosDef)
      (hV : partialTraceRight V = 0) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (q (amp N Z) (amp N V) t) (c * q Z V t)

theorem source_equivalence :
    (type_of% @kernel_contraction.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 1 Matrix.PosDef.one (by simp) identity_endpoint
    1 0 0 Matrix.PosDef.one (by ext i j; simp [partialTraceRight]) (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [actual, realize] at hh

def family : Registration arena.{u} (type_of% @kernel_contraction.{u}) where
  actual := actual
  bridge := source_equivalence
  variation := ⟨@kernel_contraction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_contraction.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiKernelContraction.kernel_contraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Divergence.UmegakiConditionalKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel

universe u

private abbrev Q := ULift.{u} Unit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def eqActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem eqDependence : ObservationalDependence signature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [eqActual, realize] at hh

private def leActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private theorem leDependence : ObservationalDependence signature leActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  norm_num [leActual, realize] at hh

private abbrev traceArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z V : Matrix ι ι ℂ) (t : ℝ),
    F.readout () () (q Z V t) ((Vᴴ * inverseMatrix Z V t).trace.re)

private theorem traceEquivalence :
    (type_of% @q_eq_trace.{u}) ↔ traceArena.{u}.Law eqActual :=
  Iff.rfl

private theorem traceRejected : ¬ traceArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0

def traceFamily : Registration traceArena.{u}
    (type_of% @q_eq_trace.{u}) where
  actual := eqActual
  bridge := traceEquivalence
  variation := ⟨@q_eq_trace, rejected, traceRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    traceArena.{u}.Law eqActual rejected traceRejected
  dependence := eqDependence

def traceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_eq_trace.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q_eq_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.traceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena.{u}⟩
  objectArena := .source ⟨traceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena.{u} ⟨traceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
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

#print axioms traceAudit

private abbrev endpointArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z V : Matrix ι ι ℂ) (hZ : Z.PosDef),
    F.readout () () (q Z V 0) ((Vᴴ * Z⁻¹ * V).trace.re)

private theorem endpointEquivalence :
    (type_of% @q_zero_parameter.{u}) ↔ endpointArena.{u}.Law eqActual :=
  Iff.rfl

private theorem endpointRejected : ¬ endpointArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 Matrix.PosDef.one

def endpointFamily : Registration endpointArena.{u}
    (type_of% @q_zero_parameter.{u}) where
  actual := eqActual
  bridge := endpointEquivalence
  variation := ⟨@q_zero_parameter, rejected, endpointRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    endpointArena.{u}.Law eqActual rejected endpointRejected
  dependence := eqDependence

def endpointAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_zero_parameter.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q_zero_parameter.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.endpointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena.{u}⟩
  objectArena := .source ⟨endpointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena.{u} ⟨endpointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
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

#print axioms endpointAudit

private abbrev energyArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z V : Matrix ι ι ℂ) (t : ℝ)
      (hZ : Z.PosSemidef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (0) (energy Z V t)

private theorem energyEquivalence :
    (type_of% @energy_nonneg.{u}) ↔ energyArena.{u}.Law leActual :=
  Iff.rfl

private theorem energyRejected : ¬ energyArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0 (Matrix.PosDef.one.posSemidef) (by simp)

def energyFamily : Registration energyArena.{u}
    (type_of% @energy_nonneg.{u}) where
  actual := leActual
  bridge := energyEquivalence
  variation := ⟨@energy_nonneg, rejected, energyRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    energyArena.{u}.Law leActual rejected energyRejected
  dependence := leDependence

def energyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@energy_nonneg.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.energy_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.energyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena.{u}⟩
  objectArena := .source ⟨energyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena.{u} ⟨energyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms energyAudit

private abbrev inverseEnergyArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z V : Matrix ι ι ℂ) (t : ℝ)
      (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (q Z V t) (energy Z (inverseMatrix Z V t) t)

private theorem inverseEnergyEquivalence :
    (type_of% @q_eq_energy_inverse.{u}) ↔ inverseEnergyArena.{u}.Law eqActual :=
  Iff.rfl

private theorem inverseEnergyRejected : ¬ inverseEnergyArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0 Matrix.PosDef.one (by simp)

def inverseEnergyFamily : Registration inverseEnergyArena.{u}
    (type_of% @q_eq_energy_inverse.{u}) where
  actual := eqActual
  bridge := inverseEnergyEquivalence
  variation := ⟨@q_eq_energy_inverse, rejected, inverseEnergyRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    inverseEnergyArena.{u}.Law eqActual rejected inverseEnergyRejected
  dependence := eqDependence

def inverseEnergyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_eq_energy_inverse.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q_eq_energy_inverse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.inverseEnergyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨inverseEnergyArena.{u}⟩
  objectArena := .source ⟨inverseEnergyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source inverseEnergyArena.{u} ⟨inverseEnergyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms inverseEnergyAudit

private abbrev nonnegativeArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z V : Matrix ι ι ℂ) (t : ℝ)
      (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (0) (q Z V t)

private theorem nonnegativeEquivalence :
    (type_of% @q_nonneg.{u}) ↔ nonnegativeArena.{u}.Law leActual :=
  Iff.rfl

private theorem nonnegativeRejected : ¬ nonnegativeArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0 Matrix.PosDef.one (by simp)

def nonnegativeFamily : Registration nonnegativeArena.{u}
    (type_of% @q_nonneg.{u}) where
  actual := leActual
  bridge := nonnegativeEquivalence
  variation := ⟨@q_nonneg, rejected, nonnegativeRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    nonnegativeArena.{u}.Law leActual rejected nonnegativeRejected
  dependence := leDependence

def nonnegativeAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_nonneg.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.nonnegativeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨nonnegativeArena.{u}⟩
  objectArena := .source ⟨nonnegativeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nonnegativeArena.{u} ⟨nonnegativeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms nonnegativeAudit

private abbrev cauchyArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z X V : Matrix ι ι ℂ) (t : ℝ)
      (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (((Xᴴ * V).trace.re)^2) (energy Z X t * q Z V t)

private theorem cauchyEquivalence :
    (type_of% @weighted_cauchy.{u}) ↔ cauchyArena.{u}.Law leActual :=
  Iff.rfl

private theorem cauchyRejected : ¬ cauchyArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0 0 Matrix.PosDef.one (by simp)

def cauchyFamily : Registration cauchyArena.{u}
    (type_of% @weighted_cauchy.{u}) where
  actual := leActual
  bridge := cauchyEquivalence
  variation := ⟨@weighted_cauchy, rejected, cauchyRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    cauchyArena.{u}.Law leActual rejected cauchyRejected
  dependence := leDependence

def cauchyAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_cauchy.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.weighted_cauchy.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.cauchyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cauchyArena.{u}⟩
  objectArena := .source ⟨cauchyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cauchyArena.{u} ⟨cauchyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cauchyAudit

private abbrev subtractArena : Arena where
  signature := signature
  Law F := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      (Z H X : Matrix ι ι ℂ) (t : ℝ)
      (hZ : Z.PosDef) (ht : t ∈ Set.Icc (0 : ℝ) 1),
    F.readout () () (q Z (H - arithmetic Z X t) t) (q Z H t - 2 * (Xᴴ * H).trace.re + energy Z X t)

private theorem subtractEquivalence :
    (type_of% @q_sub_arithmetic.{u}) ↔ subtractArena.{u}.Law eqActual :=
  Iff.rfl

private theorem subtractRejected : ¬ subtractArena.{u}.Law rejected := by
  intro h
  exact h (ι := Q) 1 0 0 0 Matrix.PosDef.one (by simp)

def subtractFamily : Registration subtractArena.{u}
    (type_of% @q_sub_arithmetic.{u}) where
  actual := eqActual
  bridge := subtractEquivalence
  variation := ⟨@q_sub_arithmetic, rejected, subtractRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    subtractArena.{u}.Law eqActual rejected subtractRejected
  dependence := eqDependence

def subtractAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@q_sub_arithmetic.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiConditionalKernel.q_sub_arithmetic.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel.subtractFamily
  realizationSource := none
  generated := false
  arena := .source ⟨subtractArena.{u}⟩
  objectArena := .source ⟨subtractArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source subtractArena.{u} ⟨subtractFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms subtractAudit

end Reg.D5.S3.Quantum.Divergence.UmegakiConditionalKernel

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Divergence.UmegakiReferenceTransport
open scoped Kronecker
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open _root_.Reg.D5.S3.Quantum.Divergence.UmegakiKernelContraction (identityChannel)
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport

universe u

private abbrev Q := ULift.{u} Unit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℂ → Prop)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def eqActual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem eqDependence : ObservationalDependence signature eqActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh := congrFun he 0
  exact one_ne_zero (hh.mp rfl)

private abbrev embeddingArena : Arena where
  signature := signature
  Law F := ∀ {a R : Type u} [Fintype a] [DecidableEq a] [Fintype R] [DecidableEq R]
      (X : Matrix R R ℂ) (V : Matrix (R × a) (R × a) ℂ),
    F.readout () () (((X ⊗ₖ (1 : Matrix a a ℂ))ᴴ * V).trace) ((Xᴴ * partialTraceRight V).trace)

private theorem embeddingEquivalence :
    (type_of% @trace_embed_pair.{u}) ↔ embeddingArena.{u}.Law eqActual :=
  Iff.rfl

private theorem embeddingRejected : ¬ embeddingArena.{u}.Law rejected := by
  intro h
  exact h (a := Q) (R := Q) 0 0

def embeddingFamily : Registration embeddingArena.{u}
    (type_of% @trace_embed_pair.{u}) where
  actual := eqActual
  bridge := embeddingEquivalence
  variation := ⟨@trace_embed_pair, rejected, embeddingRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    embeddingArena.{u}.Law eqActual rejected embeddingRejected
  dependence := eqDependence

def embeddingAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@trace_embed_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.trace_embed_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.embeddingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨embeddingArena.{u}⟩
  objectArena := .source ⟨embeddingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source embeddingArena.{u} ⟨embeddingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms embeddingAudit

private abbrev traceAdjointArena : Arena where
  signature := signature
  Law F := ∀ {a b R : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype R] [DecidableEq R] [Nonempty a] [Nonempty b]
      (N : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ)
      (Z : Matrix (R × a) (R × a) ℂ),
    F.readout () () ((PhiR N Y * Z).trace) ((Y * amp N Z).trace)

private theorem traceAdjointEquivalence :
    (type_of% @PhiR_trace_pair.{u}) ↔ traceAdjointArena.{u}.Law eqActual :=
  Iff.rfl

private theorem traceAdjointRejected : ¬ traceAdjointArena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 0 0

def traceAdjointFamily : Registration traceAdjointArena.{u}
    (type_of% @PhiR_trace_pair.{u}) where
  actual := eqActual
  bridge := traceAdjointEquivalence
  variation := ⟨@PhiR_trace_pair, rejected, traceAdjointRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    traceAdjointArena.{u}.Law eqActual rejected traceAdjointRejected
  dependence := eqDependence

def traceAdjointAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PhiR_trace_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.PhiR_trace_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.traceAdjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceAdjointArena.{u}⟩
  objectArena := .source ⟨traceAdjointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceAdjointArena.{u} ⟨traceAdjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms traceAdjointAudit

private abbrev hilbertSchmidtAdjointArena : Arena where
  signature := signature
  Law F := ∀ {a b R : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      [Fintype R] [DecidableEq R] [Nonempty a] [Nonempty b]
      (N : QuantumChannel a b) (Y : Matrix (R × b) (R × b) ℂ)
      (Z : Matrix (R × a) (R × a) ℂ),
    F.readout () () (((PhiR N Y)ᴴ * Z).trace) ((Yᴴ * amp N Z).trace)

private theorem hilbertSchmidtAdjointEquivalence :
    (type_of% @PhiR_hs_pair.{u}) ↔ hilbertSchmidtAdjointArena.{u}.Law eqActual :=
  Iff.rfl

private theorem hilbertSchmidtAdjointRejected : ¬ hilbertSchmidtAdjointArena.{u}.Law rejected := by
  intro h
  exact h (R := Q) identityChannel 0 0

def hilbertSchmidtAdjointFamily : Registration hilbertSchmidtAdjointArena.{u}
    (type_of% @PhiR_hs_pair.{u}) where
  actual := eqActual
  bridge := hilbertSchmidtAdjointEquivalence
  variation := ⟨@PhiR_hs_pair, rejected, hilbertSchmidtAdjointRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hilbertSchmidtAdjointArena.{u}.Law eqActual rejected hilbertSchmidtAdjointRejected
  dependence := eqDependence

def hilbertSchmidtAdjointAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@PhiR_hs_pair.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.UmegakiReferenceTransport.PhiR_hs_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport.hilbertSchmidtAdjointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hilbertSchmidtAdjointArena.{u}⟩
  objectArena := .source ⟨hilbertSchmidtAdjointArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hilbertSchmidtAdjointArena.{u} ⟨hilbertSchmidtAdjointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.UmegakiKernelContraction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms hilbertSchmidtAdjointAudit

end Reg.D5.S3.Quantum.Divergence.UmegakiReferenceTransport
