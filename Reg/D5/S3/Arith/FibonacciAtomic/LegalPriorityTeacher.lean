import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher

abbrev auditSignature : Signature where
  Params := Σ n : ℕ, Σ _ : Roles n, Roles n
  State p := Input p.1
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 3
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization auditSignature :=
  realize auditSignature (fun i p x =>
    Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) i) (fun e => nomatch e)

def rejected (i : Fin 2) : Realization auditSignature :=
  realize auditSignature (fun j p x => if j = i then 2
    else Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) j) (fun e => nomatch e)

def arena : Arena where
  signature := auditSignature
  Law R := ∀ {n : ℕ} (t u : Roles n),
    (∀ x : Input n, Legal x → R.readout 0 ⟨n, t, u⟩ x = R.readout 1 ⟨n, t, u⟩ x) ↔
      signature t = signature u

theorem rejected_law (i : Fin 2) : ¬ arena.Law (rejected i) := by
  intro h
  let t : Roles 3 := ⟨0, 1, 2, by decide, by decide⟩
  have hz : Legal (fun _ : Fin 3 => Window.zero) := by
    simp [Legal, D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.flatten,
      D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.bits,
      D5.S3.Arith.ZeckendorfFutureKernel.legal, List.ofFn_succ]
  have he := (h t t).mpr rfl (fun _ => Window.zero) hz
  fin_cases i <;> norm_num [rejected, realize, teacher, gate, first, last] at he <;> cases he

def registration : Registration arena
    (∀ {n : ℕ} (t u : Roles n),
      (∀ x : Input n, Legal x → teacher t x = teacher u x) ↔ signature t = signature u) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun t u => result t u, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      change Fin 2 at i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hji
      change Fin 2 at j
      funext p x
      change Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) j =
        if j = i then (2 : Fin 3)
        else Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) j
      exact (if_neg hji).symm
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change Fin 2 at i
    let t : Roles 5 := ⟨0, 2, 4, by decide, by decide⟩
    refine ⟨⟨5, t, t⟩, (fun _ => Window.zero), probe 0 2, ?_⟩
    fin_cases i <;>
      change teacher t (fun _ => Window.zero) ≠ teacher t (probe 0 2) <;>
      decide +kernel

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result) (type_of% (realize auditSignature
      (fun i p x => Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) i)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.informationUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize auditSignature
    (fun i p x => Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) i)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observationFact1, `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.anchorEnumeration }

end Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.arena
    (∀ {n : Nat} (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n),
      Iff
        (∀ (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n),
          @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x →
            @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.teacher n t x)
              (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.teacher n u x))
        (@Eq.{1} (Prod.{0, 0} (Option.{0} (Prod.{0, 0} (Fin n) (Fin n))) (Option.{0} (Prod.{0, 0} (Fin n) (Fin n))))
          (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.signature n t)
          (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.signature n u)))
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.arena
  (∀ {n : Nat} (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n),
    Iff
      (∀ (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n),
        @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x →
          @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.teacher n t x)
            (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.teacher n u x))
      (@Eq.{1} (Prod.{0, 0} (Option.{0} (Prod.{0, 0} (Fin n) (Fin n))) (Option.{0} (Prod.{0, 0} (Fin n) (Fin n))))
        (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.signature n t)
        (@D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.signature n u)))
  Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) where
  values := [(fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
    (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
    (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observation0 : {n : Nat} →
  (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) →
    (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n) →
      @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.auditSignature
          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
              (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@Sigma.mk.{0, 0} Nat
            (fun (n : Nat) =>
              @Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
                fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
                D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
            n
            (@Sigma.mk.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
              (fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
                D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
              t u)) :=
  fun {n : Nat} (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
    (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n)
    (a : @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.auditSignature
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
          fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
          D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
      n
      (@Sigma.mk.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
        (fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
          D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
        t u))
    x

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result, part := .type, path := [.body, .body, .body, .function, .argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observation1 : {n : Nat} →
  (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) →
    (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n) →
      @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.auditSignature
          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
              (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Sigma.mk.{0, 0} Nat
            (fun (n : Nat) =>
              @Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
                fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
                D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
            n
            (@Sigma.mk.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
              (fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
                D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
              t u)) :=
  fun {n : Nat} (t u : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
    (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Input n)
    (a : @D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Legal n x) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.auditSignature
    Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@Sigma.mk.{0, 0} Nat
      (fun (n : Nat) =>
        @Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
          fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
          D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
      n
      (@Sigma.mk.{0, 0} (D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
        (fun (x : D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n) =>
          D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.Roles n)
        t u))
    x

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result, part := .type, path := [.body, .body, .body, .function, .argument, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"LegalPriorityTeacher\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
