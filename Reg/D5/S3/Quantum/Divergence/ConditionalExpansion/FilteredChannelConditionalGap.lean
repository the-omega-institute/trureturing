import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

/-! Readouts for the gap comparisons, exact matrix action, and admissible ratio membership. -/

noncomputable section

universe u

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap

open _root_.FilteredChannelConditionalGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem normalized_one {i : Type*} [Unique i] [Fintype i] [DecidableEq i] :
    (Fintype.card i : ℝ)⁻¹ • partialTraceRight (1 : Matrix (i × i) (i × i) ℂ) = 1 := by
  ext x y
  simp [partialTraceRight, Matrix.one_apply]

private abbrev gapSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def gapActual : Realization gapSignature :=
  realize gapSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def gapRejected : Realization gapSignature :=
  realize gapSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev loewnerArena : Arena where
  signature := gapSignature
  Law r := ∀ {R A E : Type u}
    [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
    [Nonempty E] (G : Matrix (A × E) (A × E) ℂ) (_ : G.PosDef)
    (_ : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (k : ℝ) (_ : 0 < k)
    (_ : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹ ≤ k • (1 : Matrix A A ℂ))
    (N : QuantumChannel A (A × E)) (_ : ∀ X, act N X = filterAction G X)
    (Z : Matrix (R × A) (R × A) ℂ) (_ : Z.IsHermitian),
    r.readout () () (k⁻¹ * (posTrace (-Z) - posTrace (-ptr Z)))
      (posTrace (-amp N Z) - posTrace (-ptr Z))

private abbrev normArena : Arena where
  signature := gapSignature
  Law r := ∀ {R A E : Type u}
    [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
    [Nonempty A] [Nonempty E] (G : Matrix (A × E) (A × E) ℂ) (_ : G.PosDef)
    (_ : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel A (A × E)) (_ : ∀ X, act N X = filterAction G X)
    (Z : Matrix (R × A) (R × A) ℂ) (_ : Z.IsHermitian),
    r.readout () () (‖((Fintype.card E : ℝ)⁻¹ • partialTraceRight G⁻¹)‖⁻¹ *
      (posTrace (-Z) - posTrace (-ptr Z))) (posTrace (-amp N Z) - posTrace (-ptr Z))

private theorem loewner_rejected : ¬ loewnerArena.{u}.Law gapRejected := by
  intro h
  let i := ULift.{u} Unit
  obtain ⟨N, hN⟩ := exists_filtered_channel (A := i) (E := i) 1 PosDef.one normalized_one
  exact @h i i i _ _ _ _ _ _ _ 1 PosDef.one normalized_one 1 one_pos
    (by rw [inv_one, normalized_one, one_smul]) N hN 0 isHermitian_zero

private theorem norm_rejected : ¬ normArena.{u}.Law gapRejected := by
  intro h
  let i := ULift.{u} Unit
  obtain ⟨N, hN⟩ := exists_filtered_channel (A := i) (E := i) 1 PosDef.one normalized_one
  exact @h i i i _ _ _ _ _ _ _ _ 1 PosDef.one normalized_one N hN 0 isHermitian_zero

private theorem gap_dependence : ObservationalDependence gapSignature gapActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  norm_num [gapActual, realize] at h

def loewnerFamily : Registration loewnerArena.{u}
    (type_of% @filtered_channel_conditional_trace_gap.{u}) where
  actual := gapActual
  bridge := Iff.rfl
  variation := ⟨@filtered_channel_conditional_trace_gap.{u}, gapRejected, loewner_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    loewnerArena.Law gapActual gapRejected loewner_rejected
  dependence := gap_dependence

def normFamily : Registration normArena.{u}
    (type_of% @filtered_channel_norm_trace_gap.{u}) where
  actual := gapActual
  bridge := Iff.rfl
  variation := ⟨@filtered_channel_norm_trace_gap.{u}, gapRejected, norm_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    normArena.Law gapActual gapRejected norm_rejected
  dependence := gap_dependence

private abbrev MatrixParams := Σ _ : Type u, Type u

private abbrev OutputMatrix (p : MatrixParams.{u}) := Matrix (p.1 × p.2) (p.1 × p.2) ℂ

private abbrev actionSignature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature MatrixParams.{u} OutputMatrix
    (fun p => OutputMatrix p → Prop)

private def actionActual : Realization actionSignature.{u} :=
  realize actionSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def actionRejected : Realization actionSignature.{u} :=
  realize actionSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev actionArena : Arena where
  signature := actionSignature.{u}
  Law r := ∀ {A E : Type u} [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E]
    [Nonempty E] (G : Matrix (A × E) (A × E) ℂ) (_ : G.PosDef)
    (_ : (Fintype.card E : ℝ)⁻¹ • partialTraceRight G = 1),
    ∃ N : QuantumChannel A (A × E),
      ∀ Z, r.readout () ⟨A, E⟩ (act N Z) (filterAction G Z)

private theorem action_rejected : ¬ actionArena.{u}.Law actionRejected := by
  intro h
  let i := ULift.{u} Unit
  obtain ⟨_, hN⟩ := @h i i _ _ _ _ _ 1 PosDef.one normalized_one
  exact hN 0

private theorem action_dependence : ObservationalDependence actionSignature.{u} actionActual := by
  intro i
  let p : MatrixParams.{u} := ⟨ULift.{u} Unit, ULift.{u} Unit⟩
  let x : OutputMatrix p := fun _ _ => 0
  let y : OutputMatrix p := fun _ _ => 1
  refine ⟨p, x, y, ?_⟩
  intro h
  have he : y = x := Eq.mp (congrFun h x) rfl
  let j := (ULift.up (), ULift.up ())
  exact one_ne_zero (congrFun (congrFun he j) j)

def actionFamily : Registration actionArena.{u} (type_of% @exists_filtered_channel.{u}) where
  actual := actionActual
  bridge := Iff.rfl
  variation := ⟨@exists_filtered_channel.{u}, actionRejected, action_rejected⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    actionArena.Law actionActual actionRejected action_rejected
  dependence := action_dependence

private abbrev ratioSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ) (fun _ => ℝ → Prop)

private def ratioActual : Realization ratioSignature :=
  realize ratioSignature (fun _ _ s x => x ∈ s) (fun e => nomatch e)

private def ratioRejected : Realization ratioSignature :=
  realize ratioSignature (fun _ _ _ _ => True) (fun e => nomatch e)

private abbrev ratioArena : Arena where
  signature := ratioSignature
  Law r := ∀ {a e : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype e] [DecidableEq e] [Nonempty e]
    (G : Matrix (a × e) (a × e) ℂ) (_ : G.PosDef)
    (_ : (Fintype.card e : ℝ)⁻¹ • partialTraceRight G = 1)
    (N : QuantumChannel a (a × e)) (_ : ∀ X, act N X = filterAction G X)
    (γ : ℝ) (orth : Bool) {x : ℝ} (_ : r.readout () () (ratios N γ orth) x),
    ‖((Fintype.card e : ℝ)⁻¹ • partialTraceRight G⁻¹)‖⁻¹ ≤ x

private theorem ratio_rejected : ¬ ratioArena.Law ratioRejected := by
  intro h
  obtain ⟨N, hN⟩ := exists_filtered_channel (A := Unit) (E := Unit) 1 PosDef.one normalized_one
  have hle := h 1 PosDef.one normalized_one N hN 1 false (x := -1) trivial
  have hn := inv_nonneg.mpr (norm_nonneg
    ((Fintype.card Unit : ℝ)⁻¹ • partialTraceRight ((1 : Matrix (Unit × Unit) (Unit × Unit) ℂ)⁻¹)))
  linarith

private theorem ratio_dependence : ObservationalDependence ratioSignature ratioActual := by
  intro i
  refine ⟨(), ∅, Set.univ, ?_⟩
  intro h
  exact (Eq.mpr (congrFun h 0) (Set.mem_univ 0) : (0 : ℝ) ∈ (∅ : Set ℝ))

def ratioFamily : Registration ratioArena (type_of% @filtered_channel_ratio_lower_bound) where
  actual := ratioActual
  bridge := Iff.rfl
  variation := ⟨@filtered_channel_ratio_lower_bound, ratioRejected, ratio_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    ratioArena.Law ratioActual ratioRejected ratio_rejected
  dependence := ratio_dependence

def loewnerAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filtered_channel_conditional_trace_gap.{u}) (Realization gapSignature) Unit Unit where
  unitName :=
    `FilteredChannelConditionalGap.filtered_channel_conditional_trace_gap.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap.loewnerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨loewnerArena.{u}⟩
  objectArena := .source ⟨loewnerArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source loewnerArena.{u} ⟨loewnerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def normAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filtered_channel_norm_trace_gap.{u}) (Realization gapSignature) Unit Unit where
  unitName := `FilteredChannelConditionalGap.filtered_channel_norm_trace_gap.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap.normFamily
  realizationSource := none
  generated := false
  arena := .source ⟨normArena.{u}⟩
  objectArena := .source ⟨normArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source normArena.{u} ⟨normFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def actionAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_filtered_channel.{u}) (Realization actionSignature.{u}) Unit Unit where
  unitName := `FilteredChannelConditionalGap.exists_filtered_channel.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap.actionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨actionArena.{u}⟩
  objectArena := .source ⟨actionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source actionArena.{u} ⟨actionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize actionSignature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def ratioAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@filtered_channel_ratio_lower_bound) (Realization ratioSignature) Unit Unit where
  unitName := `FilteredChannelConditionalGap.filtered_channel_ratio_lower_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap.ratioFamily
  realizationSource := none
  generated := false
  arena := .source ⟨ratioArena⟩
  objectArena := .source ⟨ratioArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ratioArena ⟨ratioFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ratioSignature (fun _ _ s x => x ∈ s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredChannelConditionalGap
