import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PhaseHistoryBound
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound
open _root_.D5.S3.Quantum.Entanglement.PhaseHistoryBound
open _root_.D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators ComplexOrder
noncomputable section
universe u

namespace Moments
abbrev signature : Signature where
  Params := ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (n t : ℕ) → Matrix (Path n) Bit ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ), 0 < p → p < 1 → ∀ (φ : ℕ → ℝ),
    ∃ U : ℕ → Unitary (Bit × Bit),
      (∀ t i j k, U t (basis (false, i)) (j,k) = step p (φ t) (j,k) i) ∧
      (∀ n t i x, circuit U n t (blankState false n i) (register n x) =
        R.readout () p φ n t x i) ∧
      (∀ n t i x, ‖R.readout () p φ n t x i‖^2 =
        if head n x = i then pathMass p n x else 0) ∧
      (∀ n i, expectation p n i (fun _ => 1) = 1) ∧
      (∀ n i s, s ≤ n → expectation p n i (fun x => observed n x s) = mean p i s) ∧
      (∀ n i s t, s ≤ t → t ≤ n →
        expectation p n i (fun x => observed n x s * observed n x t) -
          mean p i s * mean p i t =
          (-p)^(t-s) * mean p i s * (1-mean p i s))

def actual : Realization signature :=
  realize signature (fun _ p φ => source p φ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ _ => 0) (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, _, _, hb, _⟩ := h (1/2) (by norm_num) (by norm_num) (fun _ => 0)
  have hf := hb 0 0 false false
  norm_num [rejected, realize, head, pathMass] at hf

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_source_moments, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1/2 : ℝ), (fun _ => 0), (fun _ => Real.pi), ?_⟩
    intro h
    have he := congrArg (fun f => f 1 0 (true, false) true) h
    norm_num [actual, realize, source, head, pathAmplitude, bit, memory,
      mul_comm Complex.I, Complex.exp_pi_mul_I] at he
end Moments

namespace Bound
abbrev signature : Signature where
  Params := (_ : ℝ) × ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℝ), 0 < p → p < 1 → ∀ (n : ℕ) (θ : ℝ) (φ δ : ℕ → ℝ),
    (∀ t < n, ∃ k : ℤ, θ - φ t = δ t + k * (2 * Real.pi)) →
    ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix Bit Bit ℂ) -
      (error p θ φ n (R.readout () ⟨p,n⟩ δ)).conjTranspose *
        error p θ φ n (R.readout () ⟨p,n⟩ δ)).PosSemidef ∧
    ∀ (J : Type u) [Fintype J] [DecidableEq J],
      ((historyConstant p * ∑ s : Fin n, δ s.val ^ 2 : ℝ) • (1 : Matrix (J × Bit) (J × Bit) ℂ) -
        (Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (R.readout () ⟨p,n⟩ δ))).conjTranspose *
        Matrix.kronecker (1 : Matrix J J ℂ) (error p θ φ n (R.readout () ⟨p,n⟩ δ))).PosSemidef

def actual : Realization signature :=
  realize signature (fun _ p δ => center p.1 δ p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Real.pi) (fun e => nomatch e)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (1/2) (by norm_num) (by norm_num) 0 0 (fun _ => 0) (fun _ => 0)
    (by intro t ht; omega)).1
  have hd := hh.diag_nonneg (i := false)
  norm_num [rejected, realize, error, source, head, pathAmplitude, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_bool, mul_comm Complex.I,
    Complex.exp_pi_mul_I] at hd

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨phase_history_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(1/2 : ℝ), 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change center (1/2) (fun _ => 0) 1 ≠ center (1/2) (fun _ => 1) 1
    norm_num [center]
end Bound

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments) (type_of% (realize.{0, 0, 0, 0, 0} Moments.signature (fun _ p φ => source p φ) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "PhaseHistoryBound") "actual_source_moments") "Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound/Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(Moments.arena)⟩,
  objectArena := .source ⟨(Moments.arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (Moments.arena) ⟨(Moments.registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} Moments.signature (fun _ p φ => source p φ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "body", "body", "body", "arg", "fn", "fn", "fn", "fn"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.anchorEnumeration }


#print axioms Moments.registration

noncomputable def registration_2.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} Bound.signature (fun _ p δ => center p.1 δ p.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "PhaseHistoryBound") "phase_history_bound") "Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound/Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(Bound.arena.{u_1})⟩,
  objectArena := .source ⟨(Bound.arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (Bound.arena.{u_1}) ⟨(Bound.registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} Bound.signature (fun _ p δ => center p.1 δ p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, definition := none, coordinates := #[0, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "fn", "arg", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.observationFact0, `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.anchorEnumeration }


#print axioms Bound.registration

end
end Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound


noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.arena
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.arena.) (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"phase_history_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.observation0 : (p : Real) →
  (hp : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p) →
    (hp1 : @LT.lt.{0} Real Real.instLT p (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (n : Nat) →
        (θ : Real) →
          (φ δ : Nat → Real) →
            (hlift :
                ∀ (t : Nat),
                  @LT.lt.{0} Nat instLTNat t n →
                    @Exists.{1} Int fun (k : Int) =>
                      @Eq.{1} Real (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) θ (φ t))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (δ t)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Int.cast.{0} Real Real.instIntCast k)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              Real.pi)))) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) p n) :=
  fun (p : Real)
    (hp : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p)
    (hp1 : @LT.lt.{0} Real Real.instLT p (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (n : Nat) (θ : Real) (φ δ : Nat → Real)
    (hlift :
      ∀ (t : Nat),
        @LT.lt.{0} Nat instLTNat t n →
          @Exists.{1} Int fun (k : Int) =>
            @Eq.{1} Real (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) θ (φ t))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (δ t)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Int.cast.{0} Real Real.instIntCast k)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    Real.pi)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.signature
    Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (x : Real) => Nat) p n) δ

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"phase_history_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument, .argument, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"phase_history_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).actual (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"Bound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.arena) (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).actual

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"actual_source_moments\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.observation0 : (p : Real) →
  (hp : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p) →
    (hp1 : @LT.lt.{0} Real Real.instLT p (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (φ : Nat → Real) →
        (U :
            Nat →
              @D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.Unitary.{0}
                (Prod.{0, 0} D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit
                  D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit)
                (@instFintypeProd.{0, 0} D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit
                  D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit Bool.fintype Bool.fintype)) →
          (n t : Nat) →
            (i : D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit) →
              (x : D5.S3.Quantum.Entanglement.PhaseHistoryBound.Path n) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.signature PUnit.unit.{1} p :=
  fun (p : Real)
    (hp : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p)
    (hp1 : @LT.lt.{0} Real Real.instLT p (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (φ : Nat → Real)
    (U :
      Nat →
        @D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.Unitary.{0}
          (Prod.{0, 0} D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit
            D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit)
          (@instFintypeProd.{0, 0} D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit
            D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit Bool.fintype Bool.fintype))
    (n t : Nat) (i : D5.S3.Quantum.Entanglement.PhaseHistoryBound.Bit)
    (x : D5.S3.Quantum.Entanglement.PhaseHistoryBound.Path n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.signature
    Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.actual PUnit.unit.{1} p φ

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"actual_source_moments\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"function\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments, part := .type, path := [.body, .body, .body, .body, .argument, .body, .argument, .function, .argument, .body, .body, .body, .body, .argument, .function, .function, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"actual_source_moments\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).actual (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).variation.1 (Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"PhaseHistoryBound\",\"Moments\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound, declaration := `Reg.D5.S3.Quantum.Entanglement.PhaseHistoryBound.Moments.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
