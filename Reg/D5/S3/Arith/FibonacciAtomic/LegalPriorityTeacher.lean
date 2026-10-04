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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.result)
    (type_of% arena) (type_of% arena)
    (type_of% (realize auditSignature
      (fun i p x => Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) i)
      (fun e => nomatch e))) Unit Unit Unit Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.informationUnit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher.registration,
  realizationSource := none, generated := false,
  arena := ⟨arena⟩, objectArena := ⟨arena⟩, catalog := Lean.Name.anonymous,
  localNames := false, realization := .source arena ⟨registration⟩,
  readout := some (realize auditSignature
    (fun i p x => Fin.cases (teacher p.2.1 x) (fun _ => teacher p.2.2 x) i)
    (fun e => nomatch e)),
  variation := none, sensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher, definition := none,
    coordinates := #[0, 1, 2],
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg"],
      stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }] }

end Reg.D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
