import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension

/-! Source-bound readouts for the exact trace identities and the weighted packing bound. -/

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
open _root_.D5.S3.Quantum.Recovery.LocalCompression.SpectralTestLeakage
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.Quantum.Measurements.WeightedLabelRecordDilation
open _root_.Matrix LeanInformationAudit
open scoped Matrix ComplexOrder MatrixOrder CStarAlgebra

noncomputable section

universe u v x y

namespace SignTrace

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {κ : Type v} [Fintype B] [DecidableEq B] [Fintype κ]
    (K : κ → Matrix B B ℂ)
    (_hT : (MatrixMap.of_kraus K K).IsTracePreserving)
    {H : Matrix B B ℂ} (hH : H.IsHermitian),
    ∑ a, signLeakage hH (K a) =
      R.readout () () (positiveSpectralProjection hH * (H - MatrixMap.of_kraus K K H)).trace

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let B := ULift.{u} Empty
  let κ := ULift.{v} Empty
  let K : κ → Matrix B B ℂ := fun k => nomatch IsEmpty.false k
  have hT : (MatrixMap.of_kraus K K).IsTracePreserving := by intro X; simp [Matrix.trace]
  have hbad := h K hT (H := 0) isHermitian_zero
  norm_num [rejected, realize, κ] at hbad

def family : Registration arena.{u,v} (type_of% @sum_signLeakage_eq.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_signLeakage_eq.{u,v}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sum_signLeakage_eq.{u,v}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension.sum_signLeakage_eq.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignTrace

private abbrev OneBasis := ULift.{u} Unit
private abbrev OneLabel := ULift.{v} Unit

private def oneIsometry : Matrix (Fin 1 × Fin 1) (OneBasis.{u}) ℂ := fun _ _ => 1

private theorem oneIsometry_iso : oneIsometry.{u}ᴴ * oneIsometry.{u} = 1 := by
  ext b c
  rw [Subsingleton.elim c b]
  simp [oneIsometry, Matrix.mul_apply]

private def oneLabel : OneBasis.{u} → OneLabel.{v} := fun _ => ⟨()⟩

private theorem oneLabel_mass (j : OneLabel.{v}) :
    ∑ b, (if oneLabel.{u,v} b = j then (1 : ℝ) else 0) = 1 := by
  have h (b : OneBasis.{u}) : oneLabel.{u,v} b = j := Subsingleton.elim _ _
  simp [h]

private theorem oneLabel_loss (X : Matrix (OneBasis.{u}) (OneBasis.{u}) ℂ) :
    labelLeakage oneLabel.{u,v} (fun _ => 1) X = 0 := by
  have h (j : OneLabel.{v}) : labelProjection oneLabel.{u,v} j = 1 := by
    unfold labelProjection
    have hj (b : OneBasis.{u}) : oneLabel.{u,v} b = j := Subsingleton.elim _ _
    simp [hj]
  simp [labelLeakage, h]

private def oneDecoder : QuantumChannel (Fin 1) (OneBasis.{u}) where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (CStarMatrix.reindexₐ ℂ ℂ (Equiv.ofUnique (Fin 1) (OneBasis.{u})))
  trace_preserving X := by
    change (∑ i : OneBasis.{u}, X ((Equiv.ofUnique (Fin 1) (OneBasis.{u})).symm i)
      ((Equiv.ofUnique (Fin 1) (OneBasis.{u})).symm i)) = ∑ i : Fin 1, X i i
    exact (Equiv.ofUnique (Fin 1) (OneBasis.{u})).symm.sum_comp (fun i => X i i)

namespace LabelDeficit

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ r x => r * x) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B]
    [Fintype J] [DecidableEq J] {d e : ℕ} [Nonempty J] (label : B → J) (mass : B → ℝ)
    (_hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (_hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B),
    ∑ a, labelLeakage label mass (recordKraus V decoder a) =
      R.readout () () (Fintype.card J : ℝ) (1 - averageSuccess label
        (fun b => mass b / Fintype.card J) V (decoderEffect label decoder))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hbad := h oneLabel.{u,v} (fun _ => 1) oneLabel_mass oneIsometry oneIsometry_iso oneDecoder
  norm_num [oneLabel_loss, rejected, realize] at hbad

def family : Registration arena.{u,v} (type_of% @label_deficit_eq.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@label_deficit_eq.{u,v}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h₁ := congrFun h 1
    norm_num [actual, realize] at h₁

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@label_deficit_eq.{u,v}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension.label_deficit_eq.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r x => r * x) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LabelDeficit

private theorem basis_card_le {B : Type u} [Fintype B] [DecidableEq B] {d e : ℕ}
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) : Fintype.card B ≤ d * e := by
  have h := (Matrix.rank_mul_le_left Vᴴ V).trans (Matrix.rank_le_card_width Vᴴ)
  simpa [hV] using h

namespace PackingBound

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x - y) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} {I : Type x} {L : Type y}
    [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J] [Fintype I] [Fintype L]
    {d e : ℕ} [Nonempty J] (label : B → J) (mass : B → ℝ)
    (_hmass₀ : ∀ b, 0 ≤ mass b) (_hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (hV : Vᴴ * V = 1) (_he : 0 < e)
    (decoder : QuantumChannel (Fin d) B) (ρ : I → DensityState B) (c : L → I → ℝ)
    (w : L → ℝ) (_hw : ∀ l, 0 ≤ w l)
    (_hdom : ∀ X : Matrix B B ℂ, labelLeakage label mass X ≤
      ∑ l, w l * signedTestLeakage ρ (c l) X)
    (δ : ℝ) (_hδ : ∀ i, traceNorm (preparation ρ i -
      CStarMatrix.ofMatrix.symm (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix
        (MatrixMap.of_kraus (encoderSlice V) (encoderSlice V) (preparation ρ i))))) ≤ δ),
    (Fintype.card J : ℝ) *
      (R.readout () () 1 (optimalSuccess label (fun b => mass b / Fintype.card J)
        (basis_card_le V hV))) ≤ δ * ∑ l, w l * ((∑ i, |c l i|) / 2)

private theorem rejected_law : ¬ arena.{u,v,x,y}.Law rejected := by
  intro h
  let I := ULift.{x} Empty
  let L := ULift.{y} Empty
  have hdom (X : Matrix OneBasis.{u} OneBasis.{u} ℂ) :
      labelLeakage oneLabel.{u,v} (fun _ => 1) X ≤
        ∑ l : L, (0 : ℝ) * signedTestLeakage
          (fun i : I => nomatch IsEmpty.false i) (fun i => nomatch IsEmpty.false i) X := by
    simp [oneLabel_loss]
  have hbad := h oneLabel.{u,v} (fun _ => 1) (fun _ => zero_le_one) oneLabel_mass
    oneIsometry oneIsometry_iso (by decide) oneDecoder
    (fun i : I => nomatch IsEmpty.false i) (fun (_ : L) i => nomatch IsEmpty.false i)
    (fun _ => 0) (fun _ => le_rfl) hdom 0 (fun i => nomatch IsEmpty.false i)
  norm_num [rejected, realize] at hbad

def family : Registration arena.{u,v,x,y} (type_of% @signed_test_record_dimension.{u,v,x,y}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signed_test_record_dimension.{u,v,x,y}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h₁ := congrFun h 1
    norm_num [actual, realize] at h₁

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signed_test_record_dimension.{u,v,x,y}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension.signed_test_record_dimension.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,x,y}⟩
  objectArena := .source ⟨arena.{u,v,x,y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,x,y} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x - y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PackingBound


namespace MemoryTrace

private abbrev signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x - y) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type u} {J : Type v} [Fintype B] [DecidableEq B]
    [Fintype J] [DecidableEq J] {d e : ℕ} (label : B → J) (mass : B → ℝ)
    (_hmass₀ : ∀ b, 0 ≤ mass b) (_hmass : ∀ j, ∑ b, (if label b = j then mass b else 0) = 1)
    (V : Matrix (Fin d × Fin e) B ℂ) (_hV : Vᴴ * V = 1)
    (decoder : QuantumChannel (Fin d) B),
    R.readout () () (Fintype.card J : ℝ) d ≤ ∑ a, labelLeakage label mass (recordKraus V decoder a)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hbad := h oneLabel.{u,v} (fun _ => 1) (fun _ => zero_le_one) oneLabel_mass
    oneIsometry oneIsometry_iso oneDecoder
  norm_num [oneLabel_loss, rejected, realize] at hbad

def family : Registration arena.{u,v} (type_of% @label_count_sub_memory_le_deficit.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@label_count_sub_memory_le_deficit.{u,v}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have h₁ := congrFun h 1
    norm_num [actual, realize] at h₁

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@label_count_sub_memory_le_deficit.{u,v}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension.label_count_sub_memory_le_deficit.__information_unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x - y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MemoryTrace

end

end Reg.D5.S3.Quantum.Recovery.LocalCompression.SignedTestRecordDimension
