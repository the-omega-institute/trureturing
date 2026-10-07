import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
universe u v w z

namespace Scalar
abbrev signature : Signature where
  Params := (_ : Type u) × Type v
  State p := p.2 → Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2 → Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ {d : Type u} {s : Type v} [Fintype d] [DecidableEq d] [Fintype s]
    (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X) (j₀ : d) (a : s),
      F a = R.readout () ⟨d, s⟩ F a j₀ j₀ • (1 : Matrix d d ℂ)

theorem actual_law : arena.{u,v}.Law actual := by
  exact @identity_kraus_scalar.{u,v}

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let s := ULift.{v} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  have hF : ∀ X : Matrix d d ℂ, (∑ _a : s, (1 : Matrix d d ℂ) * X * (1 : Matrix d d ℂ)ᴴ) = X := by
    intro X
    simp
  have hh := h (fun _ => 1) hF i j
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  norm_num [rejected, realize, signature] at he
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let d := ULift.{u} (Fin 1)
    let s := ULift.{v} (Fin 1)
    let i : d := ⟨0⟩
    let j : s := ⟨0⟩
    refine ⟨⟨d, s⟩, (0 : s → Matrix d d ℂ), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun F : s → Matrix d d ℂ => F j i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_1.{u_1, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar.{u_1, u_3}) (type_of% (realize.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0, max u_1 u_3, 0} signature.{u_1, u_3} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausLeftInverseNecessity") "identity_kraus_scalar") "Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity/Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_3}) ⟨(registration.{u_1, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0, max u_1 u_3, 0} signature.{u_1, u_3} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn", "fn"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar, part := .type, path := [], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.anchorEnumeration }

#print axioms registration
end Scalar

namespace Commute
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {d : Type u} {s : Type v} [Fintype d] [DecidableEq d] [Fintype s]
    (F : s → Matrix d d ℂ)
    (hF : ∀ X : Matrix d d ℂ, (∑ a, F a * X * (F a)ᴴ) = X) (a : s) (X : Matrix d d ℂ),
      F a * X = R.readout () d X * F a

theorem actual_law : arena.{u,v}.Law actual := by
  exact @identity_kraus_commute.{u,v}

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let s := ULift.{v} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  have hF : ∀ X : Matrix d d ℂ, (∑ _a : s, (1 : Matrix d d ℂ) * X * (1 : Matrix d d ℂ)ᴴ) = X := by
    intro X
    simp
  have hh := h (fun _ => 1) hF j 1
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  norm_num [rejected, realize, signature] at he
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_2.{u_1, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_commute.{u_1, u_3}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausLeftInverseNecessity") "identity_kraus_commute") "Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity/Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_3}) ⟨(registration.{u_1, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_commute, part := .type, path := [], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.anchorEnumeration }

#print axioms registration
end Commute

namespace Products
abbrev signature : Signature where
  Params := (_ : Type u) × (_ : Type v) × Type w
  State p := p.2.2 → Matrix p.2.1 p.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2.2 → Matrix p.2.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {d : Type u} {n : Type v} {s : Type w} {t : Type z}
    [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n] [Fintype s] [Fintype t]
    (E : s → Matrix n d ℂ) (A : t → Matrix d n ℂ)
    (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (j₀ : d) (a c : s),
    (R.readout () ⟨d, n, s⟩ E a)ᴴ * E c =
      (∑ b, star ((A b * E a) j₀ j₀) * ((A b * E c) j₀ j₀)) •
        (1 : Matrix d d ℂ)

theorem actual_law : arena.{u,v,w,z}.Law actual := by
  exact @left_inverse_error_products.{u,v,w,z}

theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let d := ULift.{u} (Fin 1)
  let n := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let t := ULift.{z} (Fin 1)
  let i : d := ⟨0⟩
  let j : s := ⟨0⟩
  let E : s → Matrix n d ℂ := fun _ _ _ => 1
  let A : t → Matrix d n ℂ := fun _ _ _ => 1
  have hA : (∑ b, (A b)ᴴ * A b) = 1 := by
    ext j k
    change (∑ _b : t, ∑ _i : d, star (1 : ℂ) * 1) = (1 : Matrix n n ℂ) j k
    simp [Matrix.one_apply, Subsingleton.elim j k]
  have hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X := by
    intro X
    ext j k
    change (∑ _b : t, ∑ _q : n, (∑ _p : n, (1 : ℂ) *
      (∑ _a : s, ∑ l : d, (∑ k : d, (1 : ℂ) * X k l) * star 1)) * star 1) = X j k
    simp [Fintype.sum_unique, Subsingleton.elim j (default : d),
      Subsingleton.elim k (default : d)]
    congr 1 <;> exact Subsingleton.elim _ _
  have hh := h E A hA hleft i j j
  have he := congrArg (fun M : Matrix d d ℂ => M i i) hh
  simp only [rejected, realize, signature, Pi.zero_apply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.zero_apply] at he
  norm_num [A, E, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_unique] at he
  change (∑ _ : n, star (0 : ℂ) * 1) =
    star (∑ _ : n, (1 : ℂ) * 1) * (∑ _ : n, (1 : ℂ) * 1) at he
  norm_num at he

def registration : Registration arena.{u,v,w,z} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let d := ULift.{u} (Fin 1)
    let n := ULift.{v} (Fin 1)
    let s := ULift.{w} (Fin 1)
    let i : d := ⟨0⟩
    let j : n := ⟨0⟩
    let k : s := ⟨0⟩
    refine ⟨⟨d, n, s⟩, (0 : s → Matrix n d ℂ), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun E : s → Matrix n d ℂ => E k j i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_3.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.left_inverse_error_products.{u_1, u_2, u_3, u_4}) (type_of% (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} signature.{u_1, u_2, u_3} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausLeftInverseNecessity") "left_inverse_error_products") "Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity/Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3, u_4})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3, u_4}) ⟨(registration.{u_1, u_2, u_3, u_4})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} signature.{u_1, u_2, u_3} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.left_inverse_error_products, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.anchorEnumeration }

#print axioms registration
end Products

end Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity


noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalObjectArenaOperand.{u_1, u_2, u_3, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalObjectArenaFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0, max u_1 u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalObjectArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0, max u_1 u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalObjectArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalObjectArenaOperand.{u_1, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalObjectArenaFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.sourceLaw.{u_1, u_2, u_3, u_4} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
    max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (max (u_1 + 1) (u_2 + 1))
          (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_3 + 1) (u_2 + 1)) (u_1 + 1),
        max (max u_3 u_2) u_1, 0, max (max u_3 u_2) u_1, 0}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.actual.{u_3, u_2, u_1})
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.sourceBridgeFact.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"left_inverse_error_products\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.left_inverse_error_products, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_3 + 1) (u_2 + 1)) (u_1 + 1),
      max (max u_3 u_2) u_1, 0, max (max u_3 u_2) u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.arena.{u_1, u_2, u_3, u_4}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.actual.{u_3, u_2, u_1})
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.observation0.{u_1, u_2, u_3, u_4} : {d : Type u_1} →
  {n : Type u_2} →
    {s : Type u_3} →
      {t : Type u_4} →
        [inst : Fintype.{u_1} d] →
          [DecidableEq.{u_1 + 1} d] →
            [inst_2 : Fintype.{u_2} n] →
              [inst_3 : DecidableEq.{u_2 + 1} n] →
                [inst_4 : Fintype.{u_3} s] →
                  [inst_5 : Fintype.{u_4} t] →
                    (E : s → Matrix.{u_2, u_1, 0} n d Complex) →
                      (A : t → Matrix.{u_1, u_2, 0} d n Complex) →
                        (hA :
                            @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@Finset.sum.{u_4, u_2} t (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.addCommMonoid.{0, u_2, u_2} n n Complex Complex.instAddCommMonoid)
                                (@Finset.univ.{u_4} t inst_5) fun (b : t) =>
                                @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_2} (Matrix.{u_2, u_1, 0} n d Complex)
                                  (Matrix.{u_1, u_2, 0} d n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_2} n d n Complex inst
                                    Complex.instMul Complex.instAddCommMonoid)
                                  (@Matrix.conjTranspose.{0, u_1, u_2} d n Complex
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
                                    (A b))
                                  (A b))
                              (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 1)
                                (@One.toOfNat1.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                  (@Matrix.one.{0, u_2} n Complex inst_3 Complex.instZero Complex.instOne)))) →
                          (hleft :
                              ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
                                @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
                                  (@Finset.sum.{u_4, u_1} t (Matrix.{u_1, u_1, 0} d d Complex)
                                    (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid)
                                    (@Finset.univ.{u_4} t inst_5) fun (b : t) =>
                                    @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_1} (Matrix.{u_1, u_2, 0} d n Complex)
                                      (Matrix.{u_2, u_1, 0} n d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_1} d n d Complex
                                        inst_2 Complex.instMul Complex.instAddCommMonoid)
                                      (@HMul.hMul.{max u_1 u_2, u_2, max u_1 u_2} (Matrix.{u_1, u_2, 0} d n Complex)
                                        (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_1, u_2, 0} d n Complex)
                                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_2} d n n Complex
                                          inst_2 Complex.instMul Complex.instAddCommMonoid)
                                        (A b)
                                        (@Finset.sum.{u_3, u_2} s (Matrix.{u_2, u_2, 0} n n Complex)
                                          (@Matrix.addCommMonoid.{0, u_2, u_2} n n Complex Complex.instAddCommMonoid)
                                          (@Finset.univ.{u_3} s inst_4) fun (a : s) =>
                                          @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_2} (Matrix.{u_2, u_1, 0} n d Complex)
                                            (Matrix.{u_1, u_2, 0} d n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_2} n d n
                                              Complex inst Complex.instMul Complex.instAddCommMonoid)
                                            (@HMul.hMul.{max u_1 u_2, u_1, max u_1 u_2}
                                              (Matrix.{u_2, u_1, 0} n d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                                              (Matrix.{u_2, u_1, 0} n d Complex)
                                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_1} n d d
                                                Complex inst Complex.instMul Complex.instAddCommMonoid)
                                              (E a) X)
                                            (@Matrix.conjTranspose.{0, u_2, u_1} n d Complex
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
                                              (E a))))
                                      (@Matrix.conjTranspose.{0, u_1, u_2} d n Complex
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
                                        (A b)))
                                  X) →
                            (j₀ : d) →
                              (a c : s) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max
                                      (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
                                    max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
                                  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.signature.{u_1, u_2,
                                    u_3}
                                  Unit.unit
                                  (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
                                    (fun (x : Type u_1) =>
                                      @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (x : Type u_2) => Type u_3)
                                    d (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (x : Type u_2) => Type u_3) n s)) :=
  fun {d : Type u_1} {n : Type u_2} {s : Type u_3} {t : Type u_4} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d]
    [Fintype.{u_2} n] [DecidableEq.{u_2 + 1} n] [Fintype.{u_3} s] [Fintype.{u_4} t]
    (E : s → Matrix.{u_2, u_1, 0} n d Complex) (A : t → Matrix.{u_1, u_2, 0} d n Complex)
    (hA :
      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
        (@Finset.sum.{u_4, u_2} t (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.addCommMonoid.{0, u_2, u_2} n n Complex Complex.instAddCommMonoid) (@Finset.univ.{u_4} t inst_5)
          fun (b : t) =>
          @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_2} (Matrix.{u_2, u_1, 0} n d Complex)
            (Matrix.{u_1, u_2, 0} d n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_2} n d n Complex inst Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_1, u_2} d n Complex
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
              (A b))
            (A b))
        (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 1)
          (@One.toOfNat1.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.one.{0, u_2} n Complex inst_3 Complex.instZero Complex.instOne))))
    (hleft :
      ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
        @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
          (@Finset.sum.{u_4, u_1} t (Matrix.{u_1, u_1, 0} d d Complex)
            (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_4} t inst_5)
            fun (b : t) =>
            @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_1} (Matrix.{u_1, u_2, 0} d n Complex)
              (Matrix.{u_2, u_1, 0} n d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_1} d n d Complex inst_2 Complex.instMul
                Complex.instAddCommMonoid)
              (@HMul.hMul.{max u_1 u_2, u_2, max u_1 u_2} (Matrix.{u_1, u_2, 0} d n Complex)
                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_1, u_2, 0} d n Complex)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_2} d n n Complex inst_2 Complex.instMul
                  Complex.instAddCommMonoid)
                (A b)
                (@Finset.sum.{u_3, u_2} s (Matrix.{u_2, u_2, 0} n n Complex)
                  (@Matrix.addCommMonoid.{0, u_2, u_2} n n Complex Complex.instAddCommMonoid)
                  (@Finset.univ.{u_3} s inst_4) fun (a : s) =>
                  @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_2} (Matrix.{u_2, u_1, 0} n d Complex)
                    (Matrix.{u_1, u_2, 0} d n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_2} n d n Complex inst Complex.instMul
                      Complex.instAddCommMonoid)
                    (@HMul.hMul.{max u_1 u_2, u_1, max u_1 u_2} (Matrix.{u_2, u_1, 0} n d Complex)
                      (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_2, u_1, 0} n d Complex)
                      (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_1, u_1} n d d Complex inst
                        Complex.instMul Complex.instAddCommMonoid)
                      (E a) X)
                    (@Matrix.conjTranspose.{0, u_2, u_1} n d Complex
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
                      (E a))))
              (@Matrix.conjTranspose.{0, u_1, u_2} d n Complex
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
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (A b)))
          X)
    (j₀ : d) (a c : s) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.signature.{u_1, u_2, u_3}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.actual.{u_3, u_2, u_1} Unit.unit
    (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
      (fun (x : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (x : Type u_2) => Type u_3) d
      (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (x : Type u_2) => Type u_3) n s))
    E

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.observationFact0.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"left_inverse_error_products\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.left_inverse_error_products, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument, .argument, .function], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.varyingLawInput.{u_1, u_2, u_3, u_4} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.canonicalArenaOperand.{u_1, u_2, u_3, u_4})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.varyingLaw.{u_1, u_2, u_3, u_4}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.statementExclusion.{u_1, u_2, u_3, u_4} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"left_inverse_error_products\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.left_inverse_error_products, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4}).actual (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration.{u_1, u_2, u_3, u_4}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3.descriptorFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Products\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Products.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.sourceLaw.{u_1, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0, max u_1 u_3,
    0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (u_1 + 1) (u_3 + 1), max u_1 u_3,
        0, max u_1 u_3, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_3 + 1) (u_1 + 1), max u_3 u_1, 0,
        max u_3 u_1, 0}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.actual.{u_3, u_1})
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.sourceBridgeFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_scalar\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0,
      max u_1 u_3, 0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_3 + 1) (u_1 + 1), max u_3 u_1, 0,
      max u_3 u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.arena.{u_1, u_3}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.actual.{u_3, u_1})
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.observation0.{u_1, u_3} : {d : Type u_1} →
  {s : Type u_3} →
    [inst : Fintype.{u_1} d] →
      [DecidableEq.{u_1 + 1} d] →
        [inst_2 : Fintype.{u_3} s] →
          (F : s → Matrix.{u_1, u_1, 0} d d Complex) →
            (hF :
                ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
                  @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
                    (@Finset.sum.{u_3, u_1} s (Matrix.{u_1, u_1, 0} d d Complex)
                      (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid)
                      (@Finset.univ.{u_3} s inst_2) fun (a : s) =>
                      @HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                        (Matrix.{u_1, u_1, 0} d d Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst
                          Complex.instMul Complex.instAddCommMonoid)
                        (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex)
                          (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst
                            Complex.instMul Complex.instAddCommMonoid)
                          (F a) X)
                        (@Matrix.conjTranspose.{0, u_1, u_1} d d Complex
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
                          (F a)))
                    X) →
              (j₀ : d) →
                (a : s) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1) (u_3 + 1),
                      max u_1 u_3, 0, max u_1 u_3, 0}
                    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.signature.{u_1, u_3} Unit.unit
                    (@Sigma.mk.{u_1 + 1, u_3 + 1} (Type u_1) (fun (x : Type u_1) => Type u_3) d s) :=
  fun {d : Type u_1} {s : Type u_3} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_3} s]
    (F : s → Matrix.{u_1, u_1, 0} d d Complex)
    (hF :
      ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
        @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
          (@Finset.sum.{u_3, u_1} s (Matrix.{u_1, u_1, 0} d d Complex)
            (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_3} s inst_2)
            fun (a : s) =>
            @HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
              (Matrix.{u_1, u_1, 0} d d Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst Complex.instMul
                Complex.instAddCommMonoid)
              (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                (Matrix.{u_1, u_1, 0} d d Complex)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst Complex.instMul
                  Complex.instAddCommMonoid)
                (F a) X)
              (@Matrix.conjTranspose.{0, u_1, u_1} d d Complex
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
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (F a)))
          X)
    (j₀ : d) (a : s) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_3 + 1), max u_1 u_3, 0,
        max u_1 u_3, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.signature.{u_1, u_3}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.actual.{u_3, u_1} Unit.unit
    (@Sigma.mk.{u_1 + 1, u_3 + 1} (Type u_1) (fun (x : Type u_1) => Type u_3) d s) F

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.observationFact0.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_scalar\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"function\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .function, .function, .function], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.varyingLawInput.{u_1, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.canonicalArenaOperand.{u_1, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.varyingLaw.{u_1, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.statementExclusion.{u_1, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_scalar\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_scalar, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3}).actual (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration.{u_1, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1.descriptorFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Scalar\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Scalar.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.sourceLaw.{u_1, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
      Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.actual.{u_1})
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.sourceBridgeFact.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_commute\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_commute, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.arena.{u_1, u_3}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.actual.{u_1})
  Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.observation0.{u_1, u_3} : {d : Type u_1} →
  {s : Type u_3} →
    [inst : Fintype.{u_1} d] →
      [DecidableEq.{u_1 + 1} d] →
        [inst_2 : Fintype.{u_3} s] →
          (F : s → Matrix.{u_1, u_1, 0} d d Complex) →
            (hF :
                ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
                  @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
                    (@Finset.sum.{u_3, u_1} s (Matrix.{u_1, u_1, 0} d d Complex)
                      (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid)
                      (@Finset.univ.{u_3} s inst_2) fun (a : s) =>
                      @HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                        (Matrix.{u_1, u_1, 0} d d Complex)
                        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst
                          Complex.instMul Complex.instAddCommMonoid)
                        (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex)
                          (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst
                            Complex.instMul Complex.instAddCommMonoid)
                          (F a) X)
                        (@Matrix.conjTranspose.{0, u_1, u_1} d d Complex
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
                          (F a)))
                    X) →
              (a : s) →
                (X : Matrix.{u_1, u_1, 0} d d Complex) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
                    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.signature.{u_1} Unit.unit d :=
  fun {d : Type u_1} {s : Type u_3} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Fintype.{u_3} s]
    (F : s → Matrix.{u_1, u_1, 0} d d Complex)
    (hF :
      ∀ (X : Matrix.{u_1, u_1, 0} d d Complex),
        @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} d d Complex)
          (@Finset.sum.{u_3, u_1} s (Matrix.{u_1, u_1, 0} d d Complex)
            (@Matrix.addCommMonoid.{0, u_1, u_1} d d Complex Complex.instAddCommMonoid) (@Finset.univ.{u_3} s inst_2)
            fun (a : s) =>
            @HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
              (Matrix.{u_1, u_1, 0} d d Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst Complex.instMul
                Complex.instAddCommMonoid)
              (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} d d Complex) (Matrix.{u_1, u_1, 0} d d Complex)
                (Matrix.{u_1, u_1, 0} d d Complex)
                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} d d d Complex inst Complex.instMul
                  Complex.instAddCommMonoid)
                (F a) X)
              (@Matrix.conjTranspose.{0, u_1, u_1} d d Complex
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
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                      Complex.instStarRing)))
                (F a)))
          X)
    (a : s) (X : Matrix.{u_1, u_1, 0} d d Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.actual.{u_1} Unit.unit d X

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.observationFact0.{u_1, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_commute\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_commute, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.varyingLawInput.{u_1, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.canonicalArenaOperand.{u_1, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.varyingLaw.{u_1, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.statementExclusion.{u_1, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"identity_kraus_commute\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.identity_kraus_commute, part := .type, path := [], levels := [(.param `u_1), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3}).actual (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration.{u_1, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausLeftInverseNecessity\",\"Commute\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity, declaration := `Reg.D5.S3.Quantum.Recovery.KrausLeftInverseNecessity.Commute.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
