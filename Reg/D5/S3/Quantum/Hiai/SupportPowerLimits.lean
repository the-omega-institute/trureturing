import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Hiai.SupportPowerLimits
import Reg.Support.DependentFamily

open LeanInformationAudit Matrix Filter Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Hiai.SupportPowerLimits
open _root_.D5.S3.Quantum.Hiai.InverseMeanVariational
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Hiai.SupportPowerLimits
local instance {d : Type u} [Fintype d] [DecidableEq d] :
    Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

namespace MatrixEquality
abbrev signature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix d d ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let d := ULift.{u} Unit
  refine ⟨d, 0, 1, ?_⟩
  intro h
  have hh : (1 : Matrix d d ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero hh
end MatrixEquality

namespace RectangularEquality
abbrev signature : Signature where
  Params := Σ _ : Type, Type
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.2 ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Fin 1, Fin 1⟩, 0, (fun _ _ => 1), ?_⟩
  intro h
  have hh : (fun _ _ : Fin 1 => (1 : ℂ)) = 0 := Eq.mp (congrFun h 0) rfl
  have hz := congrFun (congrFun hh 0) 0
  norm_num at hz
end RectangularEquality

namespace MatrixLimit
abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.2 → Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Filter p.2 → Filter (Matrix p.1 p.1 ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ f l m => Tendsto f l m) (fun e => nomatch e)
def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature.{u,v} actual := by
  classical
  intro i
  let d := ULift.{u} Unit
  let ι := ULift.{v} Unit
  refine ⟨⟨d, ι⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh : Tendsto (fun _ : ι => (1 : Matrix d d ℂ)) (pure ⟨()⟩) (pure 0) :=
    Eq.mp (congrArg (fun f => f (pure ⟨()⟩) (pure 0)) h) tendsto_const_pure
  simpa using hh
end MatrixLimit

namespace ShiftLimit
abbrev signature : Signature where
  Params := Type u
  State d := ℝ → Matrix d d ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Filter ℝ → Filter (Matrix d d ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ _ f l m => Tendsto f l m) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  let d := ULift.{u} Unit
  refine ⟨d, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh : Tendsto (fun _ : ℝ => (1 : Matrix d d ℂ)) (pure 0) (pure 0) :=
    Eq.mp (congrArg (fun f => f (pure 0) (pure 0)) h) tendsto_const_pure
  simpa using hh
end ShiftLimit

namespace TraceLimit
abbrev signature : Signature where
  Params := Type v
  State ι := ι → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Filter ι → Filter ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{v} :=
  realize signature (fun _ _ f l m => Tendsto f l m) (fun e => nomatch e)
def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  let ι := ULift.{v} Unit
  refine ⟨ι, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh : Tendsto (fun _ : ι => (1 : ℝ)) (pure ⟨()⟩) (pure 0) :=
    Eq.mp (congrArg (fun f => f (pure ⟨()⟩) (pure 0)) h) tendsto_const_pure
  simpa using hh
end TraceLimit

namespace cfc_eigenmatrix
open RectangularEquality
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (V : Matrix ι κ ℂ) (lam : κ → ℝ)
    (hAV : A * V = V * diagonal (fun i => (lam i : ℂ))) (f : ℝ → ℝ),
    R.readout () ⟨ι, κ⟩ (hA.cfc f * V) (V * diagonal (fun i => (f (lam i) : ℂ)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (ι := Fin 1) (κ := Fin 1) (A := 0) (by simp) 0 (fun _ => 0)
    (by simp) (fun _ => 0)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.cfc_eigenmatrix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.cfc_eigenmatrix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.cfc_eigenmatrix) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.cfc_eigenmatrix.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.cfc_eigenmatrix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end cfc_eigenmatrix

namespace support_rpow_shift_tendsto
open ShiftLimit
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) {q : ℝ} (hq : q ≠ 0),
    R.readout () d
      (fun ε : ℝ => cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q) A)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (A ^ q))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (A := 0) Matrix.PosSemidef.zero (q := 1) one_ne_zero
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.support_rpow_shift_tendsto.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.support_rpow_shift_tendsto.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.support_rpow_shift_tendsto.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.support_rpow_shift_tendsto.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.support_rpow_shift_tendsto.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end support_rpow_shift_tendsto

namespace kernel_projection_data
open MatrixEquality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℂ} (hA : A.PosSemidef)
    (hker : ∀ x : d → ℂ, A *ᵥ x = 0 → B *ᵥ x = 0),
    let Q := 1 - spectralSupport A
    R.readout () d Qᴴ Q ∧ Q * Q = Q ∧ Q.PosSemidef ∧ A * Q = 0 ∧ B * Q = 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h (d := ULift.{u} Unit) (A := 0) (B := 0) Matrix.PosSemidef.zero
    (fun _ _ => by simp)).1
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.kernel_projection_data.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.kernel_projection_data.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.kernel_projection_data.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.kernel_projection_data.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.kernel_projection_data.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end kernel_projection_data

namespace rpow_on_eigenmatrix
open MatrixEquality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {X V : Matrix d d ℂ} (hX : X.PosSemidef) (c q : ℝ)
    (hXV : X * V = c • V), R.readout () d (X ^ q * V) (c ^ q • V)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (X := 0) (V := 0) Matrix.PosSemidef.zero 0 1 (by simp)
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.rpow_on_eigenmatrix.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.rpow_on_eigenmatrix.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.rpow_on_eigenmatrix.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.rpow_on_eigenmatrix.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.rpow_on_eigenmatrix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end rpow_on_eigenmatrix

namespace shifted_rpow_formula
open MatrixEquality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) (q : ℝ),
    R.readout () d ((A + ε • (1 : Matrix d d ℂ)) ^ q)
      (cfc (fun x : ℝ => (x + ε) ^ q) A)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (A := 0) Matrix.PosSemidef.zero (ε := 1) zero_lt_one 1
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.shifted_rpow_formula.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.shifted_rpow_formula.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.shifted_rpow_formula.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.shifted_rpow_formula.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.shifted_rpow_formula.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end shifted_rpow_formula

namespace inverse_shift_split
open MatrixEquality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) (q : ℝ),
    R.readout () d ((A + ε • (1 : Matrix d d ℂ)) ^ q)
      (cfc (fun x : ℝ => if x = 0 then 0 else (x + ε) ^ q) A +
        ε ^ q • (1 - spectralSupport A))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (A := 0) Matrix.PosSemidef.zero (ε := 1) zero_lt_one 1
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.inverse_shift_split.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.inverse_shift_split.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.inverse_shift_split.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.inverse_shift_split.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.inverse_shift_split.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end inverse_shift_split

namespace tendsto_positive_rpow
open MatrixLimit
abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {ι : Type v} {l : Filter ι} {F : ι → Matrix d d ℂ} {M : Matrix d d ℂ} {q : ℝ}
    (hq : 0 < q) (hM : M.PosSemidef) (hF : ∀ᶠ i in l, (F i).PosSemidef)
    (hlim : Tendsto F l (𝓝 M)),
    R.readout () ⟨d, ι⟩ (fun i => F i ^ q) l (𝓝 (M ^ q))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (ι := ULift.{v} Unit) (l := pure ⟨()⟩)
    (F := fun _ => 0) (M := 0) (q := 1) zero_lt_one Matrix.PosSemidef.zero
    (.of_forall fun _ => Matrix.PosSemidef.zero) tendsto_const_nhds
def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_positive_rpow.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_positive_rpow.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_positive_rpow.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_positive_rpow.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_positive_rpow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tendsto_positive_rpow

namespace psd_nested_rpow
open MatrixEquality
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {A : Matrix d d ℂ} (hA : A.PosSemidef) (p q : ℝ),
    R.readout () d ((A ^ p) ^ q) (A ^ (p * q))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (A := 0) Matrix.PosSemidef.zero 1 1
def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.psd_nested_rpow.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.psd_nested_rpow.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.psd_nested_rpow.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.psd_nested_rpow.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.psd_nested_rpow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end psd_nested_rpow

namespace tendsto_tracePower
open TraceLimit
abbrev arena : Arena where
  signature := signature.{v}
  Law R := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {ι : Type v} {l : Filter ι} {F : ι → Matrix d d ℂ} {M : Matrix d d ℂ} {q : ℝ}
    (hq : 0 < q) (hM : M.PosSemidef) (hF : ∀ᶠ i in l, (F i).PosSemidef)
    (hlim : Tendsto F l (𝓝 M)),
    R.readout () ι (fun i => tracePower q (F i)) l (𝓝 (tracePower q M))
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (ι := ULift.{v} Unit) (l := pure ⟨()⟩)
    (F := fun _ => 0) (M := 0) (q := 1) zero_lt_one Matrix.PosSemidef.zero
    (.of_forall fun _ => Matrix.PosSemidef.zero) tendsto_const_nhds
def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_tracePower.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_tracePower.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_tracePower.{u,v}) (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_tracePower.unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.SupportPowerLimits.tendsto_tracePower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.SupportPowerLimits
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end tendsto_tracePower

end Reg.D5.S3.Quantum.Hiai.SupportPowerLimits
