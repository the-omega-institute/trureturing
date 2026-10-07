import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Reg.Support.DependentFamily
import Mathlib.Algebra.BigOperators.Fin

open _root_.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond
open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond

abbrev signature : Signature where
  Params := Nat
  State q := CountMat q q
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := CountMat q q
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q C => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {q r' s : Nat} (C : CountMat q q)
    (leftClass : Fin q → Fin r') (rightClass : Fin q → Fin s)
    (leftRep : Fin r' → Fin q) (rightRep : Fin s → Fin q)
    (hleftRep : ∀ f, leftClass (leftRep f) = f)
    (hrightRep : ∀ h, rightClass (rightRep h) = h)
    (hcolumns : ∀ u v, leftClass u = leftClass v → ∀ i, C i u = C i v)
    (hrows : ∀ u v, rightClass u = rightClass v → ∀ k, C u k = C v k),
    ∃ D : CountMat s r',
      columnMembership leftClass * (r.readout () q C) * columnSelector leftRep =
        (columnMembership leftClass * rowMembership rightClass) * D ∧
      rowSelector rightRep * C * rowMembership rightClass =
        D * (columnMembership leftClass * rowMembership rightClass) ∧
      Nonempty (ExchangeChain ℕ
        (columnMembership leftClass * C * columnSelector leftRep)
        (rowSelector rightRep * C * rowMembership rightClass) 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let C : CountMat 1 1 := fun _ _ => 1
  let lc : Fin 1 → Fin 1 := fun _ => 0
  let rc : Fin 1 → Fin 1 := fun _ => 0
  let lr : Fin 1 → Fin 1 := fun _ => 0
  let rr : Fin 1 → Fin 1 := fun _ => 0
  have hh := h C lc rc lr rr
    (by intro f; exact (Fin.eq_zero f).symm) (by intro g; exact (Fin.eq_zero g).symm)
    (by intro u v huv i; simp [C])
    (by intro u v huv k; simp [C])
  obtain ⟨D, hleft, hright, _⟩ := hh
  have hl := congrFun (congrFun hleft 0) 0
  have hr := congrFun (congrFun hright 0) 0
  have hl' : 0 = D 0 0 := by
    simpa [rejected, realize, Matrix.mul_apply, Fin.sum_univ_succ,
      columnMembership, rowMembership, columnSelector, lc, rc, lr] using hl
  have hr' : 1 = D 0 0 := by
    calc
      1 = (rowSelector rr * C * rowMembership rc) 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
        rfl
      _ = (D * (columnMembership lc * rowMembership rc)) 0 0 := hr
      _ = D 0 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
        change D 0 0 * (1 * 1) = D 0 0
        exact Nat.mul_one _
  exact Nat.zero_ne_one (hl'.trans hr'.symm)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q r s C leftClass rightClass leftRep rightRep hleftRep hrightRep hcolumns hrows
    simpa [actual, realize] using
      first_response_diamond C leftClass rightClass leftRep rightRep hleftRep hrightRep hcolumns hrows,
    rejected, rejected_law⟩
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
  dependence := by
    intro i
    cases i
    let z : CountMat 1 1 := fun _ _ => 0
    let o : CountMat 1 1 := fun _ _ => 1
    refine ⟨(1 : Nat), z, o, ?_⟩
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [actual, realize, z, o] at hh

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.first_response_diamond) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ q C => C) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "FirstResponseDiamond") "first_response_diamond") "Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond/Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ q C => C) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.first_response_diamond, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
      Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.actual)
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"first_response_diamond\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.first_response_diamond, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.arena
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.actual)
  Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.observation0 : {q r s : Nat} →
  (C : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat q q) →
    (leftClass : Fin q → Fin r) →
      (rightClass : Fin q → Fin s) →
        (leftRep : Fin r → Fin q) →
          (rightRep : Fin s → Fin q) →
            (hleftRep : ∀ (f : Fin r), @Eq.{1} (Fin r) (leftClass (leftRep f)) f) →
              (hrightRep : ∀ (h : Fin s), @Eq.{1} (Fin s) (rightClass (rightRep h)) h) →
                (hcolumns :
                    ∀ (u v : Fin q),
                      @Eq.{1} (Fin r) (leftClass u) (leftClass v) → ∀ (i : Fin q), @Eq.{1} Nat (C i u) (C i v)) →
                  (hrows :
                      ∀ (u v : Fin q),
                        @Eq.{1} (Fin s) (rightClass u) (rightClass v) → ∀ (k : Fin q), @Eq.{1} Nat (C u k) (C v k)) →
                    (D : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat s r) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.signature PUnit.unit.{1} q :=
  fun {q r s : Nat} (C : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat q q) (leftClass : Fin q → Fin r)
    (rightClass : Fin q → Fin s) (leftRep : Fin r → Fin q) (rightRep : Fin s → Fin q)
    (hleftRep : ∀ (f : Fin r), @Eq.{1} (Fin r) (leftClass (leftRep f)) f)
    (hrightRep : ∀ (h : Fin s), @Eq.{1} (Fin s) (rightClass (rightRep h)) h)
    (hcolumns :
      ∀ (u v : Fin q), @Eq.{1} (Fin r) (leftClass u) (leftClass v) → ∀ (i : Fin q), @Eq.{1} Nat (C i u) (C i v))
    (hrows :
      ∀ (u v : Fin q), @Eq.{1} (Fin s) (rightClass u) (rightClass v) → ∀ (k : Fin q), @Eq.{1} Nat (C u k) (C v k))
    (D : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat s r) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.signature
    Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.actual PUnit.unit.{1} q C

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"first_response_diamond\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.first_response_diamond, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .function, .argument, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"first_response_diamond\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.first_response_diamond, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"FirstResponseDiamond\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond, declaration := `Reg.D5.S3.ConceptDynamics.Coding.FirstResponseDiamond.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
