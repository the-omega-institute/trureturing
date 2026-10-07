import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
import Reg.Support.DependentFamily
import Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ScalarCountMatrices
import Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.ResponseLaws

open _root_.D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open _root_.D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open _root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

def identityMatrix (q : ℕ) : CountMat q q := fun i j => if i = j then 1 else 0

theorem identity_edge {q : ℕ} {i j : Fin q}
    (a : Fin (identityMatrix q i j)) : i = j := by
  by_contra h
  have := a.isLt
  simp [identityMatrix, h] at this

def identityNumber {q : ℕ} (i : Fin q) : Fin (identityMatrix q i i) :=
  ⟨0, by simp [identityMatrix]⟩

def rightIdentityPath {q : ℕ} (M : CountMat q q) (i j : Fin q) :
    EdgePair M (identityMatrix q) i j ≃ FinitePath M 1 i j where
  toFun := fun ⟨t, a, b⟩ => by
    have h := identity_edge b
    subst t
    exact .cons a (.nil j)
  invFun := fun p => by
    cases p with
    | cons a tail =>
      cases tail
      exact ⟨j, a, identityNumber j⟩
  left_inv := by
    rintro ⟨t, a, b⟩
    have h := identity_edge b
    subst t
    have hb : b = identityNumber j := by
      apply Fin.ext
      have hb := b.isLt
      simp only [identityMatrix, if_pos rfl] at hb
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    subst b
    rfl
  right_inv := by
    intro p
    cases p with
    | cons a tail => cases tail; rfl

def leftIdentityPath {q : ℕ} (M : CountMat q q) (i j : Fin q) :
    EdgePair (identityMatrix q) M i j ≃ FinitePath M 1 i j where
  toFun := fun ⟨t, a, b⟩ => by
    have h := identity_edge a
    subst t
    exact .cons b (.nil j)
  invFun := fun p => by
    cases p with
    | cons a tail =>
      cases tail
      exact ⟨i, identityNumber i, a⟩
  left_inv := by
    rintro ⟨t, a, b⟩
    have h := identity_edge a
    subst t
    have ha : a = identityNumber i := by
      apply Fin.ext
      have ha := a.isLt
      simp only [identityMatrix, if_pos rfl] at ha
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ ha)
    subst a
    rfl
  right_inv := by
    intro p
    cases p with
    | cons a tail => cases tail; rfl

/-- The numbered lag-one certificate shared by all certificate audit clients. -/
def lagOneCertificate {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0)) :
    CompatibleCertificate M M M (identityMatrix q) 1 where
  positiveLag := Nat.zero_lt_one
  essentialA := essential
  essentialB := essential
  phi := fun _ _ => Equiv.refl _
  psiA := rightIdentityPath M
  psiB := leftIdentityPath M
  compatible := by
    intro i j z alpha r
    cases alpha with
    | cons a tail => cases tail; rfl

abbrev I2 : CountMat 2 2 := identityMatrix 2

def certificateU : CompatibleCertificate U U U (identityMatrix 1) 1 :=
  lagOneCertificate U ⟨fun _ => ⟨0, by simp [U]⟩, fun _ => ⟨0, by simp [U]⟩⟩

def certificateP2 : CompatibleCertificate P2 P2 P2 (identityMatrix 1) 1 :=
  lagOneCertificate P2 ⟨fun _ => ⟨0, by simp [P2]⟩, fun _ => ⟨0, by simp [P2]⟩⟩

def certificateI2 : CompatibleCertificate I2 I2 I2 (identityMatrix 2) 1 :=
  lagOneCertificate I2 ⟨fun i => ⟨i, by simp [I2, identityMatrix]⟩,
    fun i => ⟨i, by simp [I2, identityMatrix]⟩⟩

#print axioms lagOneCertificate

theorem lagOne_incoming {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0))
    (a r : Edge M) (h : a.target = r.source) :
    ((lagOneCertificate M essential).incomingLift a r h).val = a := rfl

theorem lagOne_outgoing {q : ℕ} (M : CountMat q q)
    (essential : (∀ i, ∃ j, M i j ≠ 0) ∧ (∀ j, ∃ i, M i j ≠ 0))
    (r b : Edge M) (h : r.target = b.source) :
    ((lagOneCertificate M essential).outgoingLift r b h).val = b := by
  cases r
  cases b
  cases h
  rfl

abbrev edgeSignature : Signature where
  Params := Σ n, Σ k, CountMat n k
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def edgeActual : Realization edgeSignature :=
  realize edgeSignature (fun _ _ r => r) (fun e => nomatch e)

namespace LeftForgetting

def bad : Realization edgeSignature :=
  realize edgeSignature (fun _ _ r => { r with number := Fin.rev r.number })
    (fun e => nomatch e)

def arena : Arena where
  signature := edgeSignature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    (∀ (a : Edge A) (r : Edge R) (h : a.target = r.source),
      (c.incomingSquare a r h).terminalR = rho.readout () ⟨n, k, R⟩ r) ∧
    (∀ (r : Edge R) (b : Edge B) (h : r.target = b.source),
      (c.outgoingSquare r b h).initialR = r) ∧
    (∀ {i j z} (alpha : FinitePath A m i j) (r : Fin (R j z)),
      (let lifted := c.liftIncomingPath alpha r
       (⟨i, lifted.1, lifted.2⟩ : Edge R)) =
      (let rs := (c.psiA i j).symm alpha
       (⟨i, rs.1, rs.2.1⟩ : Edge R)))

theorem actual_law : arena.Law edgeActual := by
  intro n k m A B R S c
  exact square_lifts_left_forgetting c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := (h certificateP2).1 ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ rfl
  have hn := congrArg (fun r : Edge P2 => r.number.val) he
  exact Nat.zero_ne_one hn

def registration : Registration arena (arena.Law edgeActual) where
  actual := edgeActual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2⟩, ⟨0, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
    intro h
    have := congrArg (fun r : Edge P2 => r.number.val) h
    exact Nat.zero_ne_one this

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting) (type_of% (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "square_lifts_left_forgetting") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} edgeSignature (fun _ _ r => r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.anchorEnumeration }


#print axioms registration

end LeftForgetting

def reverseNumbers {k : ℕ} {B : CountMat k k} :
    {d : ℕ} → {i j : Fin k} → FinitePath B d i j → FinitePath B d i j
  | _, _, _, .nil i => .nil i
  | _, _, _, .cons a tail => .cons (Fin.rev a) (reverseNumbers tail)

def onePathNumber {k : ℕ} {B : CountMat k k} {i j : Fin k}
    (p : FinitePath B 1 i j) : Fin (B i j) := by
  cases p with
  | cons a tail => cases tail; exact a

namespace RightForgetting

abbrev signature : Signature where
  Params := Σ k, Σ m, Σ B : CountMat k k, Σ _ : Fin k, Fin k
  State p := FinitePath p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := FinitePath p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ beta => beta) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ beta => reverseNumbers beta) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    ∀ {i : Fin n} {t z : Fin k} (r : Fin (R i t)) (beta : FinitePath B m t z),
      (let lifted := c.liftOutgoingPath r beta
       (⟨lifted.1, z, lifted.2.2⟩ : Edge R)) =
      (let sr := (c.psiB t z).symm (rho.readout () ⟨k, m, B, t, z⟩ beta)
       (⟨sr.1, z, sr.2.2⟩ : Edge R))

theorem actual_law : arena.Law actual := by
  intro n k m A B R S c
  exact square_lifts_right_forgetting c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  have he := h certificateP2 (i := 0) (t := 0) (z := 0) 0 (.cons 0 (.nil 0))
  have hn := congrArg (fun r : Edge P2 => r.number.val) he
  exact Nat.zero_ne_one hn

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1, P2, 0, 0⟩, .cons 0 (.nil 0), .cons 1 (.nil 0), ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg (fun p : FinitePath P2 1 0 0 =>
      (onePathNumber p).val) h)

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ beta => beta) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "square_lifts_right_forgetting") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ beta => beta) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[1, 2, 4, 9, 10], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "value", "arg"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.anchorEnumeration }


#print axioms registration

end RightForgetting

def loop (i : Fin 2) : Edge I2 := ⟨i, i, identityNumber i⟩

namespace SourceProjection

abbrev signature : Signature where
  Params := Σ n, Σ k, CountMat n k
  State p := Edge p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r.source) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ r =>
    ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le r.source.val) r.source.isLt⟩)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law rho := ∀ {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
    {R : CountMat n k} {S : CountMat k n} (c : CompatibleCertificate A B R S m),
    (∀ r : Edge R, ∃ sq : Square c, sq.initialR = r) ∧
    (∀ r : Edge R, ∃ sq : Square c, sq.terminalR = r) ∧
    Function.Surjective (fun r : Edge R => rho.readout () ⟨n, k, R⟩ r) ∧
    Function.Surjective (fun r : Edge R => r.target) ∧
    ((∀ u, ∃ v, c.squareMatrix u v ≠ 0) ∧
      (∀ v, ∃ u, c.squareMatrix u v ≠ 0))

theorem actual_law : arena.Law actual := by
  intro n k m A B R S c
  exact square_graph_essential_and_projections c

theorem rejected_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨r, hr⟩ := (h certificateI2).2.2.1 1
  exact Nat.zero_ne_one (congrArg Fin.val hr)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, bad, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨2, 2, I2⟩, loop 0, loop 1, ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ r => r.source) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "ConceptDynamics") "Coding") "CompatibleResponseForgetting") "CompatibleCertificate") "square_graph_essential_and_projections") "Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting/Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ r => r.source) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, definition := none, coordinates := #[0, 1, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "body"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.sourceBridgeFact, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.observationFact0, `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.anchorEnumeration }


#print axioms registration

end SourceProjection

end Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.actual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_graph_essential_and_projections\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.actual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            (r : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat
                  (fun (n : Nat) =>
                    @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                  n
                  (@Sigma.mk.{0, 0} Nat
                    (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R)) :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m)
    (r : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
      n (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R))
    r

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_graph_essential_and_projections\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\",\"body\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument, .argument, .body], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_graph_essential_and_projections\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_graph_essential_and_projections, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"SourceProjection\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.SourceProjection.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.actual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_right_forgetting\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.actual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            {i : Fin n} →
              {t z : Fin k} →
                (r : Fin (R i t)) →
                  (beta : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath k B m t z) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.signature
                      PUnit.unit.{1}
                      (@Sigma.mk.{0, 0} Nat
                        (fun (k : Nat) =>
                          @Sigma.{0, 0} Nat fun (m : Nat) =>
                            @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
                              fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
                              @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
                        k
                        (@Sigma.mk.{0, 0} Nat
                          (fun (m : Nat) =>
                            @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
                              fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
                              @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
                          m
                          (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
                            (fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
                              @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
                            B (@Sigma.mk.{0, 0} (Fin k) (fun (x : Fin k) => Fin k) t z)))) :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) {i : Fin n}
    {t z : Fin k} (r : Fin (R i t))
    (beta : @D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel.FinitePath k B m t z) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.signature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (k : Nat) =>
        @Sigma.{0, 0} Nat fun (m : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
            fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
            @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
      k
      (@Sigma.mk.{0, 0} Nat
        (fun (m : Nat) =>
          @Sigma.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
            fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
            @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
        m
        (@Sigma.mk.{0, 0} (D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k)
          (fun (B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k) =>
            @Sigma.{0, 0} (Fin k) fun (x : Fin k) => Fin k)
          B (@Sigma.mk.{0, 0} (Fin k) (fun (x : Fin k) => Fin k) t z))))
    beta

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_right_forgetting\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"letValue\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .letValue, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_right_forgetting\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_right_forgetting, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"RightForgetting\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.RightForgetting.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
      Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_left_forgetting\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.arena
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual)
  Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration)

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.observation0 : {n k m : Nat} →
  {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n} →
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k} →
      {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k} →
        {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n} →
          (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m) →
            (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A) →
              (r : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R) →
                (h :
                    @Eq.{1} (Fin n) (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a)
                      (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.source n k R r)) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} Nat
                      (fun (n : Nat) =>
                        @Sigma.{0, 0} Nat fun (k : Nat) =>
                          D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
                      n
                      (@Sigma.mk.{0, 0} Nat
                        (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R)) :=
  fun {n k m : Nat} {A : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n n}
    {B : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k k}
    {R : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k}
    {S : D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat k n}
    (c : @D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate n k A B R S m)
    (a : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n n A)
    (r : @D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge n k R)
    (h :
      @Eq.{1} (Fin n) (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.target n n A a)
        (@D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.Edge.source n k R r)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeSignature
    Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.edgeActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} Nat fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k)
      n (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap.CountMat n k) k R))
    r

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_left_forgetting\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"CompatibleCertificate\",\"square_lifts_left_forgetting\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.CompatibleCertificate.square_lifts_left_forgetting, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration).actual (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration).variation.2.choose (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration).variation.1 (Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Coding\",\"CompatibleResponseForgetting\",\"LeftForgetting\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting, declaration := `Reg.D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting.LeftForgetting.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
