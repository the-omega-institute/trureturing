import D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
import Reg.Support.DependentFamily
import LeanInformationAudit.Syntax

open _root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
open _root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
universe u v w

@[reducible] def matrixSignature : Signature where
  Params := Type u
  State d := Matrix d d ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ d := Matrix d d ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization matrixSignature.{u} :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence matrixSignature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (ULift.up 0)) (ULift.up 0)
  exact zero_ne_one hentry


-- Entry calculations for the independently lifted singleton countermodels.
private theorem const_mul {a b c : Type*} [Fintype b] [Unique b] (x y : ℂ) :
    Matrix.of (fun (_ : a) (_ : b) => x) * Matrix.of (fun (_ : b) (_ : c) => y) =
      ((fun _ _ => x * y) : Matrix a c ℂ) := by
  ext i j
  change (∑ _ : b, x * y) = x * y
  simp

private theorem const_star {a b : Type*} (x : ℂ) :
    (fun (_ : a) (_ : b) => x)ᴴ = fun _ _ => star x := rfl

private theorem const_smul {a b : Type*} (x y : ℂ) :
    x • ((fun _ _ => y) : Matrix a b ℂ) = fun _ _ => x * y := rfl

private theorem zero_entries {a b : Type*} :
    (0 : Matrix a b ℂ) = fun _ _ => 0 := rfl

private theorem one_entries {a : Type*} [DecidableEq a] [Subsingleton a] :
    (1 : Matrix a a ℂ) = fun _ _ => 1 := by
  ext i j
  change (if i = j then (1 : ℂ) else 0) = 1
  simp [Subsingleton.elim i j]

private theorem const_sub {a b : Type*} (x y : ℂ) :
    ((fun _ _ => x) : Matrix a b ℂ) - (fun _ _ => y) = fun _ _ => x - y := rfl

private theorem const_add {a b : Type*} (x y : ℂ) :
    ((fun _ _ => x) : Matrix a b ℂ) + (fun _ _ => y) = fun _ _ => x + y := rfl

run_cmd do
  let root := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
  let rows ← (#[(`EncodingKrausGram.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram), (`EncodingKrausAction.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action), (`FullSyndromeDecoder.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder), (`GramSyndromeEncoder.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder), (`PositiveSyndromeEncoder.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder), (`LogicalActionOnEncoding.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding), (`LogicalRepresentationMul.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul), (`LogicalRepresentationOnCopy.arena, `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy) ]).mapM fun (arena, target) => do
    pure {
      objectArenaName := root ++ arena
      theoremName := target
      statementIdentity := LeanInformationAudit.theoremStatementIdentity (← Lean.getEnv) target
      registrationModuleName := root : LeanInformationAudit.SnapshotOccurrence }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := rows, source := rows, companionPrefix := some root }

namespace EncodingKrausGram

def arena : Arena where
  signature := matrixSignature.{u}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    (S : s → Matrix n d ℂ) (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ),
    (∑ j, (encodingKraus S B j)ᴴ * encodingKraus S B j) =
      Matrix.trace (r.readout () s B * Bᴴ) • (1 : Matrix d d ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS B
  exact encoding_kraus_gram S hS B

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, S, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem encoding_kraus_gram in arena
  readout via (realize matrixSignature.{u} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration

end EncodingKrausGram

namespace EncodingKrausAction

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ) (B : Matrix s s ℂ)
    (rho : Matrix d d ℂ),
    (∑ j, encodingKraus S B j * rho * (encodingKraus S B j)ᴴ) =
      syndromeEncoding S (B * Bᴴ) (r.readout () d rho)

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S B rho
  exact encoding_kraus_action.{u,v,w} S B rho

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S (fun _ _ => 1) (fun _ _ => 1)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem encoding_kraus_action in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration
end EncodingKrausAction

namespace FullSyndromeDecoder

def arena : Arena where
  signature := matrixSignature.{v}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (v : d),
    ∃ decoder : QuantumChannel n d,
      (∀ X : Matrix n n ℂ,
        CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (r.readout () n X))) =
        syndromeDecoding S X +
          Matrix.trace ((1 - codeSupport S) * X) • Matrix.single v v 1) ∧
      (∀ sigma : Matrix s s ℂ, Matrix.trace sigma = 1 → ∀ rho : Matrix d d ℂ,
        CStarMatrix.ofMatrix.symm
          (decoder.toCompletelyPositiveMap
            (CStarMatrix.ofMatrix (syndromeEncoding S sigma rho))) = rho)

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS v
  exact full_syndrome_decoder.{u,v,w} S hS v

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  obtain ⟨decoder, he, _⟩ := h S hS (ULift.up 0)
  have he := he (fun _ _ => 1)
  change decoder.toCompletelyPositiveMap 0 = _ at he
  rw [map_zero] at he
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress erw [Matrix.sub_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem full_syndrome_decoder in arena
  readout via (realize matrixSignature.{v} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 13 }] })
  escape continues (open)

#print axioms registration
end FullSyndromeDecoder

namespace GramSyndromeEncoder

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (B : Matrix s s ℂ)
    (hB : Matrix.trace (B * Bᴴ) = 1),
    ∃ encoder : QuantumChannel d n, ∀ rho : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (r.readout () d rho))) =
      syndromeEncoding S (B * Bᴴ) rho

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS B hB
  exact gram_syndrome_encoder.{u,v,w} S hS B hB

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  obtain ⟨encoder, he⟩ := h S hS 1 (by simp [Matrix.trace])
  have he := he (fun _ _ => 1)
  change encoder.toCompletelyPositiveMap 0 = _ at he
  rw [map_zero] at he
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem gram_syndrome_encoder in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 14 }] })
  escape continues (open)

#print axioms registration
end GramSyndromeEncoder

namespace PositiveSyndromeEncoder

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (sigma : Matrix s s ℂ)
    (hpos : sigma.PosSemidef) (htrace : Matrix.trace sigma = 1),
    ∃ encoder : QuantumChannel d n, ∀ rho : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (encoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (r.readout () d rho))) =
      syndromeEncoding S sigma rho

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS sigma hpos htrace
  exact positive_syndrome_encoder.{u,v,w} S hS sigma hpos htrace

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  obtain ⟨encoder, he⟩ := h S hS 1 Matrix.PosSemidef.one (by simp [Matrix.trace])
  have he := he (fun _ _ => 1)
  change encoder.toCompletelyPositiveMap 0 = _ at he
  rw [map_zero] at he
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem positive_syndrome_encoder in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 15 }] })
  escape continues (open)

#print axioms registration
end PositiveSyndromeEncoder

namespace LogicalActionOnEncoding

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A rho : Matrix d d ℂ) (sigma : Matrix s s ℂ),
    logicalRepresentation S A * syndromeEncoding S sigma rho =
      syndromeEncoding S sigma (A * r.readout () d rho)

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS A rho sigma
  exact logical_action_on_encoding.{u,v,w} S hS A rho sigma

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem logical_action_on_encoding in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 12 }] })
  escape continues (open)

#print axioms registration
end LogicalActionOnEncoding

namespace LogicalRepresentationMul

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A B : Matrix d d ℂ),
    logicalRepresentation S A * logicalRepresentation S B =
      logicalRepresentation S (r.readout () d A * B)

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS A B
  exact logical_representation_mul.{u,v,w} S hS A B

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1) (fun _ _ => 1)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem logical_representation_mul in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration
end LogicalRepresentationMul

namespace LogicalRepresentationOnCopy

def arena : Arena where
  signature := matrixSignature.{w}
  Law r := ∀ {s : Type u} {n : Type v} {d : Type w}
    [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (A : Matrix d d ℂ) (j : s),
    logicalRepresentation S A * S j = S j * r.readout () d A

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro s n d _ _ _ _ _ _ S hS A j
  exact logical_representation_on_copy.{u,v,w} S hS A j

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let S : ULift.{u} (Fin 1) → Matrix (ULift.{v} (Fin 1)) (ULift.{w} (Fin 1)) ℂ :=
    fun _ _ _ => 1
  have hS : OrthogonalSyndromes S := by
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [if_pos rfl]
    ext a b
    change (∑ _ : ULift.{v} (Fin 1), star (1 : ℂ) * 1) = if a = b then 1 else 0
    simp [Subsingleton.elim a b]
  have he := h S hS (fun _ _ => 1) (ULift.up 0)
  simp only [rejected, realize, Realization.readout, syndromeDecoding, syndromeEncoding,
    encodingKraus, logicalRepresentation, codeSupport, S, Fintype.sum_unique, const_star, const_mul, const_smul,
    zero_entries, one_entries, const_sub, const_add] at he
  have hentry := congrFun (congrFun he (ULift.up 0)) (ULift.up 0)
  norm_num [rejected, realize, encodingKraus, logicalRepresentation, syndromeEncoding,
    syndromeDecoding, codeSupport, S, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.smul_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.sum_apply, Pi.smul_apply, Pi.zero_apply] at hentry
  all_goals
    repeat' first
      | fail_if_no_progress erw [Matrix.mul_apply] at hentry
      | fail_if_no_progress erw [Matrix.conjTranspose_apply] at hentry
      | fail_if_no_progress erw [Matrix.smul_apply] at hentry
      | fail_if_no_progress erw [Matrix.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.one_apply] at hentry
      | fail_if_no_progress erw [Pi.zero_apply] at hentry
      | fail_if_no_progress erw [Matrix.diag_apply] at hentry
      | fail_if_no_progress simp only [Fintype.sum_unique, Matrix.trace, if_true, if_false] at hentry
    norm_num at hentry

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := dependence

set_option trace.InformationRegistration.check true in
register_information_theorem logical_representation_on_copy in arena
  readout via (realize matrixSignature.{w} (fun _ _ x => x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 11 }] })
  escape continues (open)

#print axioms registration
end LogicalRepresentationOnCopy


end Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
