import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.MatrixUnitDecoder
import Reg.Support.DependentFamily

open scoped Matrix BigOperators
open _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder

noncomputable section
universe u v

namespace Gram

abbrev signature : Signature where
  Params := (d : Type u) × Type v
  State := fun p => p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output := fun _ p => p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization signature.{u, v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u, v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d),
    (∑ b, (decoderKraus F v b)ᴴ * decoderKraus F v b) =
      unitSupport (r.readout () ⟨d, n⟩ F)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v
  exact decoder_kraus_gram F hmul hstar v

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  have hb := h F hm hs (ULift.up 0)
  have hg := decoder_kraus_gram F hm hs (ULift.up 0)
  change (∑ b, (decoderKraus F (ULift.up 0) b)ᴴ * decoderKraus F (ULift.up 0) b) =
    unitSupport (0 : d → d → Matrix n n ℂ) at hb
  rw [hg] at hb
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up 0) (ULift.up 0)) hb
  simpa [unitSupport, F] using he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩, 0,
      (fun _ _ _ _ => 1), ?_⟩
    intro h
    have he := congrArg (fun F => F (ULift.up 0) (ULift.up 0) (ULift.up 0) (ULift.up 0)) h
    exact zero_ne_one he

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "MatrixUnitDecoder") "decoder_kraus_gram") "Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder/Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.anchorEnumeration }


#print axioms registration

end Gram
namespace MatrixObservation

abbrev signature : Signature where
  Params := Type u
  State := fun n => Matrix n n ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output := fun _ n => Matrix n n ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; exact nomatch x⟩

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def zeroFamily : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def oneFamily : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} (Fin 1), 0, (fun _ _ => 1), ?_⟩
  intro h
  have he := congrArg (fun M => M (ULift.up 0) (ULift.up 0)) h
  exact zero_ne_one he

end MatrixObservation

namespace Pairing
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d)
    (X : Matrix n n ℂ) (i j : d),
    (∑ b, decoderKraus F v b * X * (decoderKraus F v b)ᴴ) i j =
      Matrix.trace (F j i * r.readout () n X)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v X i j
  exact decoder_trace_pairing F hmul hstar v X i j

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  have hb := h F hm hs (ULift.up 0) 1 (ULift.up 0) (ULift.up 0)
  have hg := decoder_trace_pairing F hm hs (ULift.up 0) 1 (ULift.up 0) (ULift.up 0)
  change _ = Matrix.trace (F (ULift.up 0) (ULift.up 0) * (0 : Matrix n n ℂ)) at hb
  rw [hg] at hb
  simpa [F, Matrix.trace] using hb

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_2.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing.{u_1, u_2}) (type_of% (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "MatrixUnitDecoder") "decoder_trace_pairing") "Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder/Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.observationFact0, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.anchorEnumeration }


#print axioms registration
end Pairing

namespace Multiplication
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (A B : Matrix d d ℂ),
    representedMatrix F A * representedMatrix F B =
      representedMatrix F (r.readout () d A * B)

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul A B
  exact represented_matrix_mul F hmul A B

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hb := h F hm 1 1
  have he := congrArg (fun M : Matrix n n ℂ => M (ULift.up 0) (ULift.up 0)) hb
  simp [zeroFamily, realize, representedMatrix, F, Matrix.zero_apply] at he
  exact one_ne_zero he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_3.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul.{u_1, u_2}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "MatrixUnitDecoder") "represented_matrix_mul") "Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder/Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.observationFact0, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.anchorEnumeration }


#print axioms registration
end Multiplication

namespace Channel
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d),
    ∃ decoder : QuantumChannel n d, ∀ X : Matrix n n ℂ, ∀ i j : d,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (r.readout () n X))) i j =
      Matrix.trace (F j i * X) +
        Matrix.trace ((1 - unitSupport F) * X) * (Matrix.single v v (1 : ℂ)) i j

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v
  exact matrix_unit_decoder_channel F hmul hstar v

theorem rejected_law : ¬ arena.{u, v}.Law zeroFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  obtain ⟨decoder, hd⟩ := h F hm hs (ULift.up 0)
  have he := hd 1 (ULift.up 0) (ULift.up 0)
  change decoder.toCompletelyPositiveMap 0 (ULift.up 0) (ULift.up 0) = _ at he
  simp [map_zero, F, unitSupport, Matrix.trace] at he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, zeroFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_4.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel.{u_1, u_2}) (type_of% (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "MatrixUnitDecoder") "matrix_unit_decoder_channel") "Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder/Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.observationFact0, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.anchorEnumeration }


#print axioms registration
end Channel

namespace Recovery
open MatrixObservation

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {d : Type u} {n : Type v} [Fintype d] [DecidableEq d]
    [Fintype n] [DecidableEq n]
    (F : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i) (v : d) (Q : Matrix n n ℂ)
    (hcomm : ∀ i j, Q * F i j = F i j * Q)
    (hsupport : unitSupport F * Q = Q) (htrace : Matrix.trace (F v v * Q) = 1),
    ∃ decoder : QuantumChannel n d, ∀ A : Matrix d d ℂ,
      CStarMatrix.ofMatrix.symm
        (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Q * representedMatrix F A))) =
          r.readout () d A

theorem actual_law : arena.{u, v}.Law actual := by
  intro d n _ _ _ _ F hmul hstar v Q hcomm hsupport htrace
  exact decoder_recovers_commutant_weight F hmul hstar v Q hcomm hsupport htrace

theorem rejected_law : ¬ arena.{u, v}.Law oneFamily := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let F : d → d → Matrix n n ℂ := fun _ _ => 1
  have hm : ∀ i j k l, F i j * F k l = if j = k then F i l else 0 := by
    intro i j k l
    simp [F, Subsingleton.elim j k]
  have hs : ∀ i j, (F i j)ᴴ = F j i := by intro i j; simp [F]
  obtain ⟨decoder, hd⟩ := h F hm hs (ULift.up 0) 1
    (by intro i j; simp) (by simp [unitSupport, F]) (by simp [F, Matrix.trace])
  have he := congrArg (fun M : Matrix d d ℂ => M (ULift.up 0) (ULift.up 0)) (hd 0)
  have hz : (1 : Matrix n n ℂ) * representedMatrix F 0 = 0 := by
    simp [representedMatrix]
  rw [hz] at he
  change decoder.toCompletelyPositiveMap 0 (ULift.up 0) (ULift.up 0) = 1 at he
  simp [map_zero] at he

def registration : Registration arena.{u, v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, oneFamily, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨oneFamily, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence

noncomputable def registration_5.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight.{u_1, u_2}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "MatrixUnitDecoder") "decoder_recovers_commutant_weight") "Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder/Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "arg"], stateBinder := 15, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }, { name := `trace.InformationRegistration.check, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.observationFact0, `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.anchorEnumeration }


#print axioms registration
end Recovery

end
end Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder


noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.arena.) (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"represented_matrix_mul\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} d] →
      [inst : DecidableEq.{u_1 + 1} d] →
        [inst_1 : Fintype.{u_2} n] →
          [DecidableEq.{u_2 + 1} n] →
            (F : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
              (hmul :
                  ∀ (i j k l : d),
                    @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                      (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                        (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_1
                          Complex.instMul Complex.instAddCommMonoid)
                        (F i j) (F k l))
                      (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k) (F i l)
                        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                (A B : Matrix.{u_1, u_1, 0} d d Complex) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
                    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_1} Unit.unit d :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (A B : Matrix.{u_1, u_1, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.actual.{u_1} Unit.unit d A

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"represented_matrix_mul\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"represented_matrix_mul\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.represented_matrix_mul, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Multiplication\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Multiplication.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.arena.) (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_recovers_commutant_weight\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [inst : Fintype.{u_1} d] →
      [inst_1 : DecidableEq.{u_1 + 1} d] →
        [inst_2 : Fintype.{u_2} n] →
          [inst_3 : DecidableEq.{u_2 + 1} n] →
            (F : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
              (hmul :
                  ∀ (i j k l : d),
                    @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                      (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                        (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                          Complex.instMul Complex.instAddCommMonoid)
                        (F i j) (F k l))
                      (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
                        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                (hstar :
                    ∀ (i j : d),
                      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                          (F i j))
                        (F j i)) →
                  (v : d) →
                    (Q : Matrix.{u_2, u_2, 0} n n Complex) →
                      (hcomm :
                          ∀ (i j : d),
                            @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                  Complex.instMul Complex.instAddCommMonoid)
                                Q (F i j))
                              (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                  Complex.instMul Complex.instAddCommMonoid)
                                (F i j) Q)) →
                        (hsupport :
                            @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                  Complex.instMul Complex.instAddCommMonoid)
                                (@D5.S3.Quantum.Recovery.MatrixUnitDecoder.unitSupport.{u_1, u_2} d n inst F) Q)
                              Q) →
                          (htrace :
                              @Eq.{1} Complex
                                (@Matrix.trace.{u_2, 0} n Complex inst_2 Complex.instAddCommMonoid
                                  (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                    (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex
                                      inst_2 Complex.instMul Complex.instAddCommMonoid)
                                    (F v v) Q))
                                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                            (decoder :
                                @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_1} n d inst_2 inst_3
                                  inst inst_1) →
                              (A : Matrix.{u_1, u_1, 0} d d Complex) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1,
                                    0, u_1, 0}
                                  Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_1}
                                  Unit.unit d :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F i j))
          (F j i))
    (v : d) (Q : Matrix.{u_2, u_2, 0} n n Complex)
    (hcomm :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            Q (F i j))
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) Q))
    (hsupport :
      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
        (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
          (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
            Complex.instAddCommMonoid)
          (@D5.S3.Quantum.Recovery.MatrixUnitDecoder.unitSupport.{u_1, u_2} d n inst F) Q)
        Q)
    (htrace :
      @Eq.{1} Complex
        (@Matrix.trace.{u_2, 0} n Complex inst_2 Complex.instAddCommMonoid
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F v v) Q))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (decoder : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_1} n d inst_2 inst_3 inst inst_1)
    (A : Matrix.{u_1, u_1, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.actual.{u_1} Unit.unit d A

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_recovers_commutant_weight\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_recovers_commutant_weight\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_recovers_commutant_weight, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration_5\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Recovery\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration_5, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Recovery.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0} (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.arena.) (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"matrix_unit_decoder_channel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [inst : Fintype.{u_1} d] →
      [inst_1 : DecidableEq.{u_1 + 1} d] →
        [inst_2 : Fintype.{u_2} n] →
          [inst_3 : DecidableEq.{u_2 + 1} n] →
            (F : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
              (hmul :
                  ∀ (i j k l : d),
                    @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                      (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                        (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                          Complex.instMul Complex.instAddCommMonoid)
                        (F i j) (F k l))
                      (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
                        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                (hstar :
                    ∀ (i j : d),
                      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                          (F i j))
                        (F j i)) →
                  (v : d) →
                    (decoder :
                        @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_1} n d inst_2 inst_3 inst
                          inst_1) →
                      (X : Matrix.{u_2, u_2, 0} n n Complex) →
                        (i j : d) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_2 + 1, u_2, 0,
                              u_2, 0}
                            Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_2} Unit.unit n :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F i j))
          (F j i))
    (v : d)
    (decoder : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_2, u_1} n d inst_2 inst_3 inst inst_1)
    (X : Matrix.{u_2, u_2, 0} n n Complex) (i j : d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_2}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.actual.{u_2} Unit.unit n X

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"matrix_unit_decoder_channel\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .body, .body, .function, .argument, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"matrix_unit_decoder_channel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.matrix_unit_decoder_channel, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4.descriptorFact.{u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Channel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Channel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0} (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.arena.) (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_trace_pairing\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} d] →
      [inst : DecidableEq.{u_1 + 1} d] →
        [inst_1 : Fintype.{u_2} n] →
          [DecidableEq.{u_2 + 1} n] →
            (F : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
              (hmul :
                  ∀ (i j k l : d),
                    @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                      (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                        (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_1
                          Complex.instMul Complex.instAddCommMonoid)
                        (F i j) (F k l))
                      (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k) (F i l)
                        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                (hstar :
                    ∀ (i j : d),
                      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                          (F i j))
                        (F j i)) →
                  (v : d) →
                    (X : Matrix.{u_2, u_2, 0} n n Complex) →
                      (i j : d) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_2 + 1, u_2, 0, u_2,
                            0}
                          Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_2} Unit.unit n :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F i j))
          (F j i))
    (v : d) (X : Matrix.{u_2, u_2, 0} n n Complex) (i j : d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.signature.{u_2}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.MatrixObservation.actual.{u_2} Unit.unit n X

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_trace_pairing\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_trace_pairing\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_trace_pairing, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2.descriptorFact.{u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Pairing\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Pairing.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2,
    0} (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.arena.) (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_kraus_gram\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} d] →
      [inst : DecidableEq.{u_1 + 1} d] →
        [inst_1 : Fintype.{u_2} n] →
          [DecidableEq.{u_2 + 1} n] →
            (F : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
              (hmul :
                  ∀ (i j k l : d),
                    @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                      (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                        (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_1
                          Complex.instMul Complex.instAddCommMonoid)
                        (F i j) (F k l))
                      (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k) (F i l)
                        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                          (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                (hstar :
                    ∀ (i j : d),
                      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                        (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                          (F i j))
                        (F j i)) →
                  (v : d) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1) (u_2 + 1),
                        max u_1 u_2, 0, max u_1 u_2, 0}
                      Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.signature.{u_1, u_2} Unit.unit
                      (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (d : Type u_1) => Type u_2) d n) :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F i j))
          (F j i))
    (v : d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        max u_1 u_2, 0}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.signature.{u_1, u_2}
    Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.actual.{u_1, u_2} Unit.unit
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (d : Type u_1) => Type u_2) d n) F

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_kraus_gram\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"decoder_kraus_gram\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `D5.S3.Quantum.Recovery.MatrixUnitDecoder.decoder_kraus_gram, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"MatrixUnitDecoder\",\"Gram\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder, declaration := `Reg.D5.S3.Quantum.Recovery.MatrixUnitDecoder.Gram.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
