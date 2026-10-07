import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

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

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram.{u_1, u_2, u_3}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} matrixSignature.{u_1} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "encoding_kraus_gram") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} matrixSignature.{u_1} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.anchorEnumeration }


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

noncomputable def registration_2.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "encoding_kraus_action") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.anchorEnumeration }


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

noncomputable def registration_3.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder.{u_1, u_2, u_3}) (type_of% (realize.{u_2 + 1, u_2, 0, u_2, 0} matrixSignature.{u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "full_syndrome_decoder") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_2 + 1, u_2, 0, u_2, 0} matrixSignature.{u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "fn", "arg", "arg", "arg", "arg"], stateBinder := 13, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.anchorEnumeration }


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

noncomputable def registration_4.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "gram_syndrome_encoder") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "arg", "arg"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.anchorEnumeration }


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

noncomputable def registration_5.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "positive_syndrome_encoder") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "arg", "arg"], stateBinder := 15, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.anchorEnumeration }


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

noncomputable def registration_6.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "logical_action_on_encoding") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.anchorEnumeration }


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

noncomputable def registration_7.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "logical_representation_mul") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.anchorEnumeration }


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

noncomputable def registration_8.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy.{u_1, u_2, u_3}) (type_of% (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "OrthogonalSyndromeChannel") "logical_representation_on_copy") "Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel/Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_3 + 1, u_3, 0, u_3, 0} matrixSignature.{u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, definition := none, coordinates := #[2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.observationFact0, `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.anchorEnumeration }


#print axioms registration
end LogicalRepresentationOnCopy


end Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel


noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_3 + 1, u_3, 0, u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [DecidableEq.{u_1 + 1} s] →
          [Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (B : Matrix.{u_1, u_1, 0} s s Complex) →
                      (rho : Matrix.{u_3, u_3, 0} d d Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3, 0, u_3,
                            0}
                          Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (B : Matrix.{u_1, u_1, 0} s s Complex) (rho : Matrix.{u_3, u_3, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d rho

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_action\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausAction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausAction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_gram\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [inst : DecidableEq.{u_1 + 1} s] →
          [inst_1 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [inst_4 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst inst_1 inst_4 S) →
                      (B : Matrix.{u_1, u_1, 0} s s Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1,
                            0}
                          Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_1} Unit.unit s :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (B : Matrix.{u_1, u_1, 0} s s Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_1}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_1} Unit.unit s B

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_gram\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"encoding_kraus_gram\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.encoding_kraus_gram, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"EncodingKrausGram\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.EncodingKrausGram.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"full_syndrome_decoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [inst : DecidableEq.{u_1 + 1} s] →
          [inst_1 : Fintype.{u_2} n] →
            [inst_2 : DecidableEq.{u_2 + 1} n] →
              [inst_3 : Fintype.{u_3} d] →
                [inst_4 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst inst_1 inst_4 S) →
                      (v : d) →
                        (decoder :
                            @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_3} n d inst_1 inst_2
                              inst_3 inst_4) →
                          (X : Matrix.{u_2, u_2, 0} n n Complex) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_2 + 1, u_2, 0,
                                u_2, 0}
                              Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_2} Unit.unit n :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (v : d)
    (decoder : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_3} n d inst_2 inst_3 inst_4 inst_5)
    (X : Matrix.{u_2, u_2, 0} n n Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_2}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_2} Unit.unit n X

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"full_syndrome_decoder\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .function, .argument, .body, .function, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"full_syndrome_decoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.full_syndrome_decoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3.descriptorFact.{u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"FullSyndromeDecoder\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.FullSyndromeDecoder.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"positive_syndrome_encoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [inst : Fintype.{u_1} s] →
        [inst_1 : DecidableEq.{u_1 + 1} s] →
          [inst_2 : Fintype.{u_2} n] →
            [inst_3 : DecidableEq.{u_2 + 1} n] →
              [inst_4 : Fintype.{u_3} d] →
                [inst_5 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst_1 inst_2 inst_5 S) →
                      (sigma : Matrix.{u_1, u_1, 0} s s Complex) →
                        (hpos :
                            @Matrix.PosSemidef.{u_1, 0} s Complex Complex.instRing Complex.partialOrder
                              Complex.instStarRing sigma) →
                          (htrace :
                              @Eq.{1} Complex (@Matrix.trace.{u_1, 0} s Complex inst Complex.instAddCommMonoid sigma)
                                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                            (encoder :
                                @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_3, u_2} d n inst_4 inst_5
                                  inst_2 inst_3) →
                              (rho : Matrix.{u_3, u_3, 0} d d Complex) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3,
                                    0, u_3, 0}
                                  Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (sigma : Matrix.{u_1, u_1, 0} s s Complex)
    (hpos : @Matrix.PosSemidef.{u_1, 0} s Complex Complex.instRing Complex.partialOrder Complex.instStarRing sigma)
    (htrace :
      @Eq.{1} Complex (@Matrix.trace.{u_1, 0} s Complex inst Complex.instAddCommMonoid sigma)
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (encoder : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_3, u_2} d n inst_4 inst_5 inst_2 inst_3)
    (rho : Matrix.{u_3, u_3, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d rho

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"positive_syndrome_encoder\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .function, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"positive_syndrome_encoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.positive_syndrome_encoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"PositiveSyndromeEncoder\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.PositiveSyndromeEncoder.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_on_copy\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [inst : DecidableEq.{u_1 + 1} s] →
          [inst_1 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [inst_4 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst inst_1 inst_4 S) →
                      (A : Matrix.{u_3, u_3, 0} d d Complex) →
                        (j : s) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3, 0,
                              u_3, 0}
                            Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (A : Matrix.{u_3, u_3, 0} d d Complex) (j : s) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d A

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_on_copy\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_on_copy\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_on_copy, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration_8\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationOnCopy\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration_8, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationOnCopy.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_mul\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [inst : DecidableEq.{u_1 + 1} s] →
          [inst_1 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [inst_4 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst inst_1 inst_4 S) →
                      (A B : Matrix.{u_3, u_3, 0} d d Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3, 0, u_3,
                            0}
                          Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (A B : Matrix.{u_3, u_3, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d A

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_mul\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_representation_mul\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_representation_mul, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration_7\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalRepresentationMul\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration_7, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalRepresentationMul.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_action_on_encoding\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [Fintype.{u_1} s] →
        [inst : DecidableEq.{u_1 + 1} s] →
          [inst_1 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              [Fintype.{u_3} d] →
                [inst_4 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst inst_1 inst_4 S) →
                      (A rho : Matrix.{u_3, u_3, 0} d d Complex) →
                        (sigma : Matrix.{u_1, u_1, 0} s s Complex) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3, 0,
                              u_3, 0}
                            Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (A rho : Matrix.{u_3, u_3, 0} d d Complex) (sigma : Matrix.{u_1, u_1, 0} s s Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d rho

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_action_on_encoding\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"logical_action_on_encoding\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.logical_action_on_encoding, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration_6\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"LogicalActionOnEncoding\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration_6, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.LogicalActionOnEncoding.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_3 + 1, u_3, 0, u_3, 0} (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.arena.) (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"gram_syndrome_encoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.observation0.{u_1, u_2, u_3} : {s : Type u_1} →
  {n : Type u_2} →
    {d : Type u_3} →
      [inst : Fintype.{u_1} s] →
        [inst_1 : DecidableEq.{u_1 + 1} s] →
          [inst_2 : Fintype.{u_2} n] →
            [inst_3 : DecidableEq.{u_2 + 1} n] →
              [inst_4 : Fintype.{u_3} d] →
                [inst_5 : DecidableEq.{u_3 + 1} d] →
                  (S : s → Matrix.{u_2, u_3, 0} n d Complex) →
                    (hS :
                        @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d
                          inst_1 inst_2 inst_5 S) →
                      (B : Matrix.{u_1, u_1, 0} s s Complex) →
                        (hB :
                            @Eq.{1} Complex
                              (@Matrix.trace.{u_1, 0} s Complex inst Complex.instAddCommMonoid
                                (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} s s Complex)
                                  (Matrix.{u_1, u_1, 0} s s Complex) (Matrix.{u_1, u_1, 0} s s Complex)
                                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} s s s Complex inst
                                    Complex.instMul Complex.instAddCommMonoid)
                                  B
                                  (@Matrix.conjTranspose.{0, u_1, u_1} s s Complex
                                    (@InvolutiveStar.toStar.{0} Complex
                                      (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                        (@AddCommMonoid.toAddMonoid.{0} Complex
                                          (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                  Complex.instNonUnitalCommRing)))))
                                        (@StarRing.toStarAddMonoid.{0} Complex
                                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                Complex.instNonUnitalCommRing)))
                                          Complex.instStarRing)))
                                    B)))
                              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                          (encoder :
                              @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_3, u_2} d n inst_4 inst_5
                                inst_2 inst_3) →
                            (rho : Matrix.{u_3, u_3, 0} d d Complex) →
                              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_3 + 1, u_3, 0,
                                  u_3, 0}
                                Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3} Unit.unit d :=
  fun {s : Type u_1} {n : Type u_2} {d : Type u_3} [Fintype.{u_1} s] [DecidableEq.{u_1 + 1} s] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} d] [DecidableEq.{u_3 + 1} d] (S : s → Matrix.{u_2, u_3, 0} n d Complex)
    (hS :
      @D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding.OrthogonalSyndromes.{u_1, u_2, u_3} s n d inst_1 inst_2 inst_5
        S)
    (B : Matrix.{u_1, u_1, 0} s s Complex)
    (hB :
      @Eq.{1} Complex
        (@Matrix.trace.{u_1, 0} s Complex inst Complex.instAddCommMonoid
          (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} s s Complex) (Matrix.{u_1, u_1, 0} s s Complex)
            (Matrix.{u_1, u_1, 0} s s Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} s s s Complex inst Complex.instMul
              Complex.instAddCommMonoid)
            B
            (@Matrix.conjTranspose.{0, u_1, u_1} s s Complex
              (@InvolutiveStar.toStar.{0} Complex
                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                  (@AddCommMonoid.toAddMonoid.{0} Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              B)))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (encoder : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_3, u_2} d n inst_4 inst_5 inst_2 inst_3)
    (rho : Matrix.{u_3, u_3, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_3 + 1, u_3, 0, u_3, 0}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.matrixSignature.{u_3}
    Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.actual.{u_3} Unit.unit d rho

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"gram_syndrome_encoder\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .function, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"gram_syndrome_encoder\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.gram_syndrome_encoder, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4.descriptorFact.{u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"OrthogonalSyndromeChannel\",\"GramSyndromeEncoder\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel, declaration := `Reg.D5.S3.Quantum.Recovery.OrthogonalSyndromeChannel.GramSyndromeEncoder.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
