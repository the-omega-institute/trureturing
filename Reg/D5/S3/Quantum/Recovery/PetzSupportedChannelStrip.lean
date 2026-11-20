import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts of the scalar supported-channel strip conclusions. -/

set_option autoImplicit false

noncomputable section

universe u v

open Matrix MeasureTheory LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open _root_.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
open PetzCothStripMode (lowerWeight)
open PetzExponentialBoundaryEvaluation (petzWeight)
open scoped BigOperators ComplexOrder MatrixOrder

namespace Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip

private def unitState (n : Type u) [Fintype n] [DecidableEq n] [Unique n] : DensityState n :=
  ⟨1, zero_le_one, by simp [Matrix.trace, Matrix.diag, CStarMatrix.one_apply_eq]⟩

private def unitChannel (a : Type u) (b : Type v)
    [Fintype a] [DecidableEq a] [Unique a]
    [Fintype b] [DecidableEq b] [Unique b] : QuantumChannel a b where
  toCompletelyPositiveMap := CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b))
  trace_preserving := by
    intro X
    change Matrix.trace (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique a b) X) = Matrix.trace X
    simp [Matrix.trace, Matrix.diag, CStarMatrix.reindexₐ_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    change X ((Equiv.ofUnique a b).symm default) ((Equiv.ofUnique a b).symm default) =
      X default default
    simp only [Subsingleton.elim ((Equiv.ofUnique a b).symm default) (default : a)]

private def unitModel : SupportedRelativeModularModel
    (unitChannel (ULift.{u} Unit) (ULift.{v} Unit)) (unitState _) (unitState _) :=
  supported_relative_modular_model _ _ _ (supportContained_refl _)

private theorem hasInputCoordinate
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) : Nonempty (M.data.J × M.data.I) := by
  classical
  by_contra h
  letI : IsEmpty (M.data.J × M.data.I) := ⟨fun i => h ⟨i⟩⟩
  have hn := M.normξ
  simp at hn

namespace Amplitude

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (z : ℂ) (i : M.data.J × M.data.I),
    R.readout () () (amplitude M.data z i)
      (Complex.exp ((Real.log (inputRatio M.data i) : ℂ) * z) *
        ((Real.sqrt (M.data.ri i.2) : ℂ) *
          (star (M.data.v i.1) ⬝ᵥ
            (M.data.Ψ (M.data.spectralX
              (modularPower (outputRatio M.data) (-z) *ᵥ M.data.η)) *ᵥ M.data.u i.2))))

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v} 0 (Classical.choice (hasInputCoordinate unitModel.{u,v}))

def family : Registration arena.{u,v} (type_of% @amplitude_coordinate.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@amplitude_coordinate.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@amplitude_coordinate.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.amplitude_coordinate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.Amplitude.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
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

end Amplitude

namespace UnrotatedAmplitude

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (i : M.data.J × M.data.I),
    R.readout () () (amplitude M.data ((1 / 2 : ℝ) : ℂ) i)
      ((Real.sqrt (M.data.sj i.1) : ℂ) *
        (star (M.data.v i.1) ⬝ᵥ
          (M.data.Ψ (spectralInverseSqrt M.data.Q * cfc Real.sqrt M.data.T) *ᵥ
            M.data.u i.2)))

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v} (Classical.choice (hasInputCoordinate unitModel.{u,v}))

def family : Registration arena.{u,v} (type_of% @amplitude_half_coordinate.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@amplitude_half_coordinate.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@amplitude_half_coordinate.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.amplitude_half_coordinate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.UnrotatedAmplitude.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UnrotatedAmplitude

namespace Overlap

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (D : SupportedRelativeModularData Φ ρ σ) (z : ℂ),
    R.readout () () (overlap D z) (star D.ξ ⬝ᵥ amplitude D z)

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v}.data 0

def family : Registration arena.{u,v} (type_of% @overlap_eq_pair.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@overlap_eq_pair.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@overlap_eq_pair.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.overlap_eq_pair.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.Overlap.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Overlap

namespace Normalization

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    R.readout () () (overlap M.data 0).re 1

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v}

def family : Registration arena.{u,v} (type_of% @overlap_zero_re.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@overlap_zero_re.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@overlap_zero_re.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.overlap_zero_re.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.Normalization.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization

namespace RealDerivative

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    R.readout () () (deriv (overlap M.data) 0).re
      (-(finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)))

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v}

def family : Registration arena.{u,v} (type_of% @deriv_overlap_zero_re.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deriv_overlap_zero_re.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deriv_overlap_zero_re.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.deriv_overlap_zero_re.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.RealDerivative.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RealDerivative

namespace Distance

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (r s : ℝ),
    let γ := amplitude M.data ((r : ℂ) + (s : ℂ) * Complex.I)
    R.readout () () (deficit M.data r s)
      ((∑ i, ‖M.data.ξ i - γ i‖ ^ 2) + (1 - ∑ i, ‖γ i‖ ^ 2))

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v} 0 0

def family : Registration arena.{u,v} (type_of% @deficit_eq_distance_add_defect.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deficit_eq_distance_add_defect.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deficit_eq_distance_add_defect.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.deficit_eq_distance_add_defect.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.Distance.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Distance

namespace LowerDeficit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ),
    R.readout () () 0 (deficit M.data 0 s)

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v} 0

def family : Registration arena.{u,v} (type_of% @lower_deficit_nonneg.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lower_deficit_nonneg.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lower_deficit_nonneg.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.lower_deficit_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.LowerDeficit.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LowerDeficit

namespace UpperDeficit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ) (s : ℝ),
    R.readout () () 0 (deficit M.data (1 / 2) s)

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact law unitModel.{u,v} 0

def family : Registration arena.{u,v} (type_of% @upper_deficit_nonneg.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@upper_deficit_nonneg.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@upper_deficit_nonneg.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.upper_deficit_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.UpperDeficit.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UpperDeficit

namespace BoundaryIntegral

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ),
    let D := (supported_relative_modular_model Φ ρ σ support).data
    Integrable (fun s => lowerWeight s * deficit D 0 s) ∧
      Integrable (fun s => petzWeight s * deficit D (1 / 2) s) ∧
      R.readout () ()
        ((∫ s, lowerWeight s * deficit D 0 s) + (∫ s, petzWeight s * deficit D (1 / 2) s))
        (finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ))

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  exact (law (unitChannel (ULift.{u} Unit) (ULift.{v} Unit)) (unitState _) (unitState _)
    (supportContained_refl _)).2.2

def family : Registration arena.{u,v} (type_of% @integral_supported_channel_strip.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_supported_channel_strip.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro heq
    have h := congrFun heq 0
    norm_num [actual, realize] at h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@integral_supported_channel_strip.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.integral_supported_channel_strip.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.BoundaryIntegral.family
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
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BoundaryIntegral

namespace ComplexDerivative

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x + 1 : ℝ) : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    {Φ : QuantumChannel a b} {ρ σ : DensityState a}
    (M : SupportedRelativeModularModel Φ ρ σ),
    HasDerivAt (overlap M.data)
      (R.readout () () (-(finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)))) 0

private theorem rejectedLaw : ¬ arena.{u,v}.Law rejected := by
  intro law
  have h := congrArg Complex.re
    ((hasDerivAt_overlap_zero unitModel.{u,v}).unique (law unitModel.{u,v}))
  simp only [rejected, realize, Complex.ofReal_re] at h
  linarith

def family : Registration arena.{u,v} (type_of% @hasDerivAt_overlap_zero.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_overlap_zero.{u,v}, rejected, rejectedLaw.{u,v}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    simpa [actual, realize] using congrArg Complex.re h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_overlap_zero.{u,v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.hasDerivAt_overlap_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip.ComplexDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ComplexDerivative

end Reg.D5.S3.Quantum.Recovery.PetzSupportedChannelStrip
